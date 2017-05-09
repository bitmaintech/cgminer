/*
 * Copyright 2012-2013 Andrew Smith
 * Copyright 2013 Con Kolivas <kernel@kolivas.org>
 * Copyright 2013 Lingchao Xu <lingchao.xu@bitmaintech.com>
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the Free
 * Software Foundation; either version 3 of the License, or (at your option)
 * any later version.  See COPYING for more details.
 */

/*
 * Those code should be works fine with AntMiner U1 of Bmsc.
 * Operation:
 *   No detection implement.
 *   Input: 64B = 32B midstate + 20B fill bytes + last 12 bytes of block head.
 *   Return: send back 40bits immediately when Bmsc found a valid nonce.
 *           no query protocol implemented here, if no data send back in ~11.3
 *           seconds (full cover time on 32bit nonce range by 380MH/s speed)
 *           just send another work.
 * Notice:
 *   1. Bmsc will start calculate when you push a work to them, even they
 *      are busy.
 *   2. Bmsc will stop work when: a valid nonce has been found or 40 bits
 *      nonce range is completely calculated.
 */


#include <float.h>
#include <limits.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <strings.h>
#include <sys/time.h>
#include <unistd.h>

#include "config.h"

#ifdef WIN32
#include <windows.h>
#endif

#include "compat.h"
#include "miner.h"
#include "usbutils.h"

// The serial I/O speed - Linux uses a define 'B115200' in bits/termios.h
#define BMSC_IO_SPEED 115200

#define BMSC_NONCE_ARRAY_SIZE 6

// The size of a successful nonce read
#define BMSC_READ_SIZE 5

// Ensure the sizes are correct for the Serial read
#if (BMSC_READ_SIZE != 5)
#error BMSC_READ_SIZE must be 5
#endif
#define ASSERT1(condition) __maybe_unused static char sizeof_uint32_t_must_be_4[(condition)?1:-1]
ASSERT1(sizeof(uint32_t) == 4);

// TODO: USB? Different calculation? - see usbstats to work it out e.g. 1/2 of normal send time
//  or even use that number? 1/2
// #define BMSC_READ_TIME(baud) ((double)BMSC_READ_SIZE * (double)8.0 / (double)(baud))
// maybe 1ms?
#define BMSC_READ_TIME(baud) (0.001)

// USB ms timeout to wait - user specified timeouts are multiples of this
#define BMSC_WAIT_TIMEOUT 100
#define BMSC_CMR2_TIMEOUT 1
#define BMSC_READ_BUF_LEN 8192

// Defined in multiples of BMSC_WAIT_TIMEOUT
// Must of course be greater than BMSC_READ_COUNT_TIMING/BMSC_WAIT_TIMEOUT
// There's no need to have this bigger, since the overhead/latency of extra work
// is pretty small once you get beyond a 10s nonce range time and 10s also
// means that nothing slower than 429MH/s can go idle so most bmsc devices
// will always mine without idling
#define BMSC_READ_TIME_LIMIT_MAX 100

// In timing mode: Default starting value until an estimate can be obtained
// 5000 ms allows for up to a ~840MH/s device
#define BMSC_READ_COUNT_TIMING	5000
#define BMSC_READ_COUNT_MIN		BMSC_WAIT_TIMEOUT
#define SECTOMS(s)	((int)((s) * 1000))
// How many ms below the expected completion time to abort work
// extra in case the last read is delayed
#define BMSC_READ_REDUCE	((int)(BMSC_WAIT_TIMEOUT * 1.5))

// For a standard Bmsc (to 5 places)
// Since this rounds up a the last digit - it is a slight overestimate
// Thus the hash rate will be a VERY slight underestimate
// (by a lot less than the displayed accuracy)
// Minor inaccuracy of these numbers doesn't affect the work done,
// only the displayed MH/s
#define BMSC_REV3_HASH_TIME 0.0000000026316
#define LANCELOT_HASH_TIME 0.0000000025000
#define ASICMINERUSB_HASH_TIME 0.0000000029761
// TODO: What is it?
#define CAIRNSMORE1_HASH_TIME 0.0000000027000
// Per FPGA
#define CAIRNSMORE2_HASH_TIME 0.0000000066600
#define NANOSEC 1000000000.0

#define CAIRNSMORE2_INTS 4

// Bmsc doesn't send a completion message when it finishes
// the full nonce range, so to avoid being idle we must abort the
// work (by starting a new work item) shortly before it finishes
//
// Thus we need to estimate 2 things:
//	1) How many hashes were done if the work was aborted
//	2) How high can the timeout be before the Bmsc is idle,
//		to minimise the number of work items started
//	We set 2) to 'the calculated estimate' - BMSC_READ_REDUCE
//	to ensure the estimate ends before idle
//
// The simple calculation used is:
//	Tn = Total time in seconds to calculate n hashes
//	Hs = seconds per hash
//	Xn = number of hashes
//	W  = code/usb overhead per work
//
// Rough but reasonable estimate:
//	Tn = Hs * Xn + W	(of the form y = mx + b)
//
// Thus:
//	Line of best fit (using least squares)
//
//	Hs = (n*Sum(XiTi)-Sum(Xi)*Sum(Ti))/(n*Sum(Xi^2)-Sum(Xi)^2)
//	W = Sum(Ti)/n - (Hs*Sum(Xi))/n
//
// N.B. W is less when aborting work since we aren't waiting for the reply
//	to be transferred back (BMSC_READ_TIME)
//	Calculating the hashes aborted at n seconds is thus just n/Hs
//	(though this is still a slight overestimate due to code delays)
//

// Both below must be exceeded to complete a set of data
// Minimum how long after the first, the last data point must be
#define HISTORY_SEC 60
// Minimum how many points a single BMSC_HISTORY should have
#define MIN_DATA_COUNT 5
// The value MIN_DATA_COUNT used is doubled each history until it exceeds:
#define MAX_MIN_DATA_COUNT 100

static struct timeval history_sec = { HISTORY_SEC, 0 };

// Store the last INFO_HISTORY data sets
// [0] = current data, not yet ready to be included as an estimate
// Each new data set throws the last old set off the end thus
// keeping a ongoing average of recent data
#define INFO_HISTORY 10

#define BMSC_WORK_QUEUE_NUM 36

struct BMSC_HISTORY {
	struct timeval finish;
	double sumXiTi;
	double sumXi;
	double sumTi;
	double sumXi2;
	uint32_t values;
	uint32_t hash_count_min;
	uint32_t hash_count_max;
};

enum timing_mode { MODE_DEFAULT, MODE_SHORT, MODE_LONG, MODE_VALUE };

static const char *MODE_DEFAULT_STR = "default";
static const char *MODE_SHORT_STR = "short";
static const char *MODE_SHORT_STREQ = "short=";
static const char *MODE_LONG_STR = "long";
static const char *MODE_LONG_STREQ = "long=";
static const char *MODE_VALUE_STR = "value";
static const char *MODE_UNKNOWN_STR = "unknown";

struct BMSC_INFO {
	enum sub_ident ident;
	int intinfo;

	// time to calculate the golden_ob
	uint64_t golden_hashes;
	struct timeval golden_tv;

	struct BMSC_HISTORY history[INFO_HISTORY+1];
	uint32_t min_data_count;

	int timeout;

	// seconds per Hash
	double Hs;
	// ms til we abort
	int read_time;
	// ms limit for (short=/long=) read_time
	int read_time_limit;

	enum timing_mode timing_mode;
	bool do_bmsc_timing;

	bool start;

	double fullnonce;
	int count;
	double W;
	uint32_t values;
	uint64_t hash_count_range;

	// Determine the cost of history processing
	// (which will only affect W)
	uint64_t history_count;
	struct timeval history_time;

	// bmsc-options
	int baud;
	int work_division;
	int fpga_count;
	uint32_t nonce_mask;

	uint8_t cmr2_speed;
	bool speed_next_work;
	bool flash_next_work;

	struct work * work_queue[BMSC_WORK_QUEUE_NUM];
	int work_queue_index;

	unsigned char nonce_bin[BMSC_NONCE_ARRAY_SIZE][BMSC_READ_SIZE+1];
	int nonce_index;
};

#define BMSC_MIDSTATE_SIZE 32
#define BMSC_UNUSED_SIZE 15
#define BMSC_WORK_SIZE 12

#define BMSC_WORK_DATA_OFFSET 64

#define BMSC_CMR2_SPEED_FACTOR 2.5
#define BMSC_CMR2_SPEED_MIN_INT 100
#define BMSC_CMR2_SPEED_DEF_INT 180
#define BMSC_CMR2_SPEED_MAX_INT 220
#define CMR2_INT_TO_SPEED(_speed) ((uint8_t)((float)_speed / BMSC_CMR2_SPEED_FACTOR))
#define BMSC_CMR2_SPEED_MIN CMR2_INT_TO_SPEED(BMSC_CMR2_SPEED_MIN_INT)
#define BMSC_CMR2_SPEED_DEF CMR2_INT_TO_SPEED(BMSC_CMR2_SPEED_DEF_INT)
#define BMSC_CMR2_SPEED_MAX CMR2_INT_TO_SPEED(BMSC_CMR2_SPEED_MAX_INT)
#define BMSC_CMR2_SPEED_INC 1
#define BMSC_CMR2_SPEED_DEC -1
#define BMSC_CMR2_SPEED_FAIL -10

#define BMSC_CMR2_PREFIX ((uint8_t)0xB7)
#define BMSC_CMR2_CMD_SPEED ((uint8_t)0)
#define BMSC_CMR2_CMD_FLASH ((uint8_t)1)
#define BMSC_CMR2_DATA_FLASH_OFF ((uint8_t)0)
#define BMSC_CMR2_DATA_FLASH_ON ((uint8_t)1)
#define BMSC_CMR2_CHECK ((uint8_t)0x6D)

struct BMSC_WORK {
	uint8_t midstate[BMSC_MIDSTATE_SIZE];
	// These 4 bytes are for CMR2 bitstreams that handle MHz adjustment
	uint8_t check;
	uint8_t data;
	uint8_t cmd;
	uint8_t prefix;
	uint8_t unused[BMSC_UNUSED_SIZE];
	uint8_t workid;
	uint8_t work[BMSC_WORK_SIZE];
};

#define END_CONDITION 0x0000ffff

// Looking for options in --bmsc-timing and --bmsc-options:
//
// Code increments this each time we start to look at a device
// However, this means that if other devices are checked by
// the Bmsc code (e.g. Avalon only as at 20130517)
// they will count in the option offset
//
// This, however, is deterministic so that's OK
//
// If we were to increment after successfully finding an Bmsc
// that would be random since an Bmsc may fail and thus we'd
// not be able to predict the option order
//
// Devices are checked in the order libusb finds them which is ?
//
static int option_offset = -1;

unsigned char CRC5(unsigned char *ptr, unsigned char len)
{
    unsigned char i, j, k;
    unsigned char crc = 0x1f;

    unsigned char crcin[5] = {1, 1, 1, 1, 1};
    unsigned char crcout[5] = {1, 1, 1, 1, 1};
    unsigned char din = 0;

    j = 0x80;
    k = 0;
    for (i = 0; i < len; i++)
    {
    	if (*ptr & j) {
    		din = 1;
    	} else {
    		din = 0;
    	}
    	crcout[0] = crcin[4] ^ din;
    	crcout[1] = crcin[0];
    	crcout[2] = crcin[1] ^ crcin[4] ^ din;
    	crcout[3] = crcin[2];
    	crcout[4] = crcin[3];

        j = j >> 1;
        k++;
        if (k == 8)
        {
            j = 0x80;
            k = 0;
            ptr++;
        }
        memcpy(crcin, crcout, 5);
    }
    crc = 0;
    if(crcin[4]) {
    	crc |= 0x10;
    }
    if(crcin[3]) {
    	crc |= 0x08;
    }
    if(crcin[2]) {
    	crc |= 0x04;
    }
    if(crcin[1]) {
    	crc |= 0x02;
    }
    if(crcin[0]) {
    	crc |= 0x01;
    }
    return crc;
}

static void _transfer(struct cgpu_info *bmsc, uint8_t request_type, uint8_t bRequest, uint16_t wValue, uint16_t wIndex, uint32_t *data, int siz, enum usb_cmds cmd)
{
	int err;

	err = usb_transfer_data(bmsc, request_type, bRequest, wValue, wIndex, data, siz, cmd);

	applog(LOG_DEBUG, "%s: cgid %d %s got err %d",
			bmsc->drv->name, bmsc->cgminer_id,
			usb_cmdname(cmd), err);
}

#define transfer(bmsc, request_type, bRequest, wValue, wIndex, cmd) \
		_transfer(bmsc, request_type, bRequest, wValue, wIndex, NULL, 0, cmd)

static void bmsc_initialise(struct cgpu_info *bmsc, int baud)
{
	struct BMSC_INFO *info = (struct BMSC_INFO *)(bmsc->device_data);
	uint16_t wValue, wIndex;
	enum sub_ident ident;
	int interface;

	if (bmsc->usbinfo.nodev)
		return;

	interface = _usb_interface(bmsc, info->intinfo);
	ident = usb_ident(bmsc);

	switch (ident) {
		case IDENT_BLT:
		case IDENT_LLT:
		case IDENT_CMR1:
		case IDENT_CMR2:
			// Reset
			transfer(bmsc, FTDI_TYPE_OUT, FTDI_REQUEST_RESET, FTDI_VALUE_RESET,
				 interface, C_RESET);

			if (bmsc->usbinfo.nodev)
				return;

			// Latency
			_usb_ftdi_set_latency(bmsc, info->intinfo);

			if (bmsc->usbinfo.nodev)
				return;

			// Set data control
			transfer(bmsc, FTDI_TYPE_OUT, FTDI_REQUEST_DATA, FTDI_VALUE_DATA_BLT,
				 interface, C_SETDATA);

			if (bmsc->usbinfo.nodev)
				return;

			// default to BLT/LLT 115200
			wValue = FTDI_VALUE_BAUD_BLT;
			wIndex = FTDI_INDEX_BAUD_BLT;

			if (ident == IDENT_CMR1 || ident == IDENT_CMR2) {
				switch (baud) {
					case 115200:
						wValue = FTDI_VALUE_BAUD_CMR_115;
						wIndex = FTDI_INDEX_BAUD_CMR_115;
						break;
					case 57600:
						wValue = FTDI_VALUE_BAUD_CMR_57;
						wIndex = FTDI_INDEX_BAUD_CMR_57;
						break;
					default:
						quit(1, "bmsc_intialise() invalid baud (%d) for Cairnsmore1", baud);
						break;
				}
			}

			// Set the baud
			transfer(bmsc, FTDI_TYPE_OUT, FTDI_REQUEST_BAUD, wValue,
				 (wIndex & 0xff00) | interface, C_SETBAUD);

			if (bmsc->usbinfo.nodev)
				return;

			// Set Modem Control
			transfer(bmsc, FTDI_TYPE_OUT, FTDI_REQUEST_MODEM, FTDI_VALUE_MODEM,
				 interface, C_SETMODEM);

			if (bmsc->usbinfo.nodev)
				return;

			// Set Flow Control
			transfer(bmsc, FTDI_TYPE_OUT, FTDI_REQUEST_FLOW, FTDI_VALUE_FLOW,
				 interface, C_SETFLOW);

			if (bmsc->usbinfo.nodev)
				return;

			// Clear any sent data
			transfer(bmsc, FTDI_TYPE_OUT, FTDI_REQUEST_RESET, FTDI_VALUE_PURGE_TX,
				 interface, C_PURGETX);

			if (bmsc->usbinfo.nodev)
				return;

			// Clear any received data
			transfer(bmsc, FTDI_TYPE_OUT, FTDI_REQUEST_RESET, FTDI_VALUE_PURGE_RX,
				 interface, C_PURGERX);
			break;
		case IDENT_ICA:
			// Set Data Control
			transfer(bmsc, PL2303_CTRL_OUT, PL2303_REQUEST_CTRL, PL2303_VALUE_CTRL,
				 interface, C_SETDATA);

			if (bmsc->usbinfo.nodev)
				return;

			// Set Line Control
			uint32_t ica_data[2] = { PL2303_VALUE_LINE0, PL2303_VALUE_LINE1 };
			_transfer(bmsc, PL2303_CTRL_OUT, PL2303_REQUEST_LINE, PL2303_VALUE_LINE,
				 interface, &ica_data[0], PL2303_VALUE_LINE_SIZE, C_SETLINE);

			if (bmsc->usbinfo.nodev)
				return;

			// Vendor
			transfer(bmsc, PL2303_VENDOR_OUT, PL2303_REQUEST_VENDOR, PL2303_VALUE_VENDOR,
				 interface, C_VENDOR);
			break;
		case IDENT_AMU:
			// Enable the UART
			transfer(bmsc, CP210X_TYPE_OUT, CP210X_REQUEST_IFC_ENABLE,
				 CP210X_VALUE_UART_ENABLE,
				 interface, C_ENABLE_UART);

			if (bmsc->usbinfo.nodev)
				return;

			// Set data control
			transfer(bmsc, CP210X_TYPE_OUT, CP210X_REQUEST_DATA, CP210X_VALUE_DATA,
				 interface, C_SETDATA);

			if (bmsc->usbinfo.nodev)
				return;

			// Set the baud
			uint32_t data = CP210X_DATA_BAUD;
			_transfer(bmsc, CP210X_TYPE_OUT, CP210X_REQUEST_BAUD, 0,
				 interface, &data, sizeof(data), C_SETBAUD);
			break;
		default:
			quit(1, "bmsc_intialise() called with invalid %s cgid %i ident=%d",
				bmsc->drv->name, bmsc->cgminer_id, ident);
	}
}

#define BTM_NONCE_ERROR -1
#define BTM_NONCE_OK 0
#define BTM_NONCE_RESTART 1
#define BTM_NONCE_TIMEOUT 2

static int bmsc_get_nonce(struct cgpu_info *bmsc, unsigned char *buf, struct timeval *tv_start,
			    struct timeval *tv_finish, struct thr_info *thr, int read_time)
{
	struct BMSC_INFO *info = (struct BMSC_INFO *)(bmsc->device_data);
	int err, amt, rc;

	if (bmsc->usbinfo.nodev)
		return BTM_NONCE_ERROR;

	cgtime(tv_start);
	err = usb_read_ii_timeout_cancellable(bmsc, info->intinfo, (char *)buf,
					      BMSC_READ_SIZE, &amt, read_time,
					      C_GETRESULTS);
	cgtime(tv_finish);

	if (err < 0 && err != LIBUSB_ERROR_TIMEOUT) {
		applog(LOG_ERR, "%s%i: Comms error (rerr=%d amt=%d)", bmsc->drv->name,
		       bmsc->device_id, err, amt);
		dev_error(bmsc, REASON_DEV_COMMS_ERROR);
		return BTM_NONCE_ERROR;
	}

	if (amt >= BMSC_READ_SIZE)
		return BTM_NONCE_OK;

	rc = SECTOMS(tdiff(tv_finish, tv_start));
	if (thr && thr->work_restart) {
		applog(LOG_DEBUG, "Bmsc Read: Work restart at %d ms", rc);
		return BTM_NONCE_RESTART;
	}

	if (amt > 0)
		applog(LOG_DEBUG, "Bmsc Read: Timeout reading for %d ms", rc);
	else
		applog(LOG_DEBUG, "Bmsc Read: No data for %d ms", rc);
	return BTM_NONCE_TIMEOUT;
}

static const char *timing_mode_str(enum timing_mode timing_mode)
{
	switch(timing_mode) {
	case MODE_DEFAULT:
		return MODE_DEFAULT_STR;
	case MODE_SHORT:
		return MODE_SHORT_STR;
	case MODE_LONG:
		return MODE_LONG_STR;
	case MODE_VALUE:
		return MODE_VALUE_STR;
	default:
		return MODE_UNKNOWN_STR;
	}
}

static void set_timing_mode(int this_option_offset, struct cgpu_info *bmsc, float readtimeout)
{
	struct BMSC_INFO *info = (struct BMSC_INFO *)(bmsc->device_data);
	enum sub_ident ident;
	double Hs;
	char buf[BUFSIZ+1];
	char *ptr, *comma, *eq;
	size_t max;
	int i;

	ident = usb_ident(bmsc);
	switch (ident) {
		case IDENT_ICA:
			info->Hs = BMSC_REV3_HASH_TIME;
			break;
		case IDENT_BLT:
		case IDENT_LLT:
			info->Hs = LANCELOT_HASH_TIME;
			break;
		case IDENT_AMU:
			info->Hs = ASICMINERUSB_HASH_TIME;
			break;
		case IDENT_CMR1:
			info->Hs = CAIRNSMORE1_HASH_TIME;
			break;
		case IDENT_CMR2:
			info->Hs = CAIRNSMORE2_HASH_TIME;
			break;
		default:
			quit(1, "Bmsc get_options() called with invalid %s ident=%d",
				bmsc->drv->name, ident);
	}

	info->read_time = 0;
	info->read_time_limit = 0; // 0 = no limit

	info->fullnonce = info->Hs * (((double) 0xffffffff) + 1);
	info->read_time = (int)(readtimeout * BMSC_WAIT_TIMEOUT);

	if(info->read_time < 0)
		info->read_time = 1;

	info->timing_mode = MODE_DEFAULT;
	info->do_bmsc_timing = false;

	info->min_data_count = MIN_DATA_COUNT;

	// All values are in multiples of BMSC_WAIT_TIMEOUT
	info->read_time_limit *= BMSC_WAIT_TIMEOUT;

	applog(LOG_ERR, "%s%d Init: mode=%s read_time=%dms limit=%dms Hs=%e",
			bmsc->drv->name, bmsc->cgminer_id,
			timing_mode_str(info->timing_mode),
			info->read_time, info->read_time_limit, info->Hs);
}

static uint32_t mask(int work_division)
{
	uint32_t nonce_mask = 0x7fffffff;

	// yes we can calculate these, but this way it's easy to see what they are
	switch (work_division) {
	case 1:
		nonce_mask = 0xffffffff;
		break;
	case 2:
		nonce_mask = 0x7fffffff;
		break;
	case 4:
		nonce_mask = 0x3fffffff;
		break;
	case 8:
		nonce_mask = 0x1fffffff;
		break;
	default:
		quit(1, "Invalid2 bmsc-options for work_division (%d) must be 1, 2, 4 or 8", work_division);
	}

	return nonce_mask;
}

static void get_options(int this_option_offset, struct cgpu_info *bmsc, int *baud, float *readtimeout)
{
	char buf[BUFSIZ+1];
	char *ptr, *comma, *colon, *colon2;
	enum sub_ident ident;
	size_t max;
	int i, tmp;
	float tmpf;

	if (opt_bmsc_options == NULL)
		buf[0] = '\0';
	else {
		ptr = opt_bmsc_options;
		for (i = 0; i < this_option_offset; i++) {
			comma = strchr(ptr, ',');
			if (comma == NULL)
				break;
			ptr = comma + 1;
		}

		comma = strchr(ptr, ',');
		if (comma == NULL)
			max = strlen(ptr);
		else
			max = comma - ptr;

		if (max > BUFSIZ)
			max = BUFSIZ;
		strncpy(buf, ptr, max);
		buf[max] = '\0';
	}

	ident = usb_ident(bmsc);
	switch (ident) {
		case IDENT_ICA:
		case IDENT_BLT:
		case IDENT_LLT:
			*baud = BMSC_IO_SPEED;
			break;
		case IDENT_AMU:
			*baud = BMSC_IO_SPEED;
			break;
		case IDENT_CMR1:
			*baud = BMSC_IO_SPEED;
			break;
		case IDENT_CMR2:
			*baud = BMSC_IO_SPEED;
			break;
		default:
			quit(1, "Bmsc get_options() called with invalid %s ident=%d",
				bmsc->drv->name, ident);
	}

	if (*buf) {
		colon = strchr(buf, ':');
		if (colon)
			*(colon++) = '\0';

		if (*buf) {
			tmp = atoi(buf);
			switch (tmp) {
			case 115200:
				*baud = 115200;
				break;
			case 57600:
				*baud = 57600;
				break;
			default:
				quit(1, "Invalid bmsc-options for baud (%s) must be 115200 or 57600", buf);
			}
		}

		if (colon && *colon) {
			tmpf = atof(colon);
			if (tmpf > 0) {
				*readtimeout = tmpf;
			} else {
				quit(1, "Invalid bmsc-options for timeout (%s) must be > 0", colon);
			}
		}
	}
}

static void get_bandops(unsigned char * core_buf, int *corenum, char *coreenable, int *coresleep)
{
	char buf[512] = {0};
	char *colon, *colon2, * colon3;
	int i, len;

	if (opt_bmsc_bandops) {
		len = strlen(opt_bmsc_bandops);
		if(len <= 0 || len >= 512) {
			quit(1, "Invalid bmsc-bandops %s %d", opt_bmsc_bandops, len);
		}
		strcpy(buf, opt_bmsc_bandops);
		colon = strchr(buf, ':');
		if (colon)
			*(colon++) = '\0';

		if (*buf) {
			if(strlen(buf) > 8 || strlen(buf)%2 != 0 || strlen(buf)/2 == 0) {
				quit(1, "Invalid bitmain-options for core command, must be hex now: %s", buf);
			}
			memset(core_buf, 0, 4);
			if(!hex2bin(core_buf, buf, strlen(buf)/2)) {
				quit(1, "Invalid bitmain-options for core command, hex2bin error now: %s", buf);
			}
		}

		if (colon && *colon) {
			colon2 = strchr(colon, ':');
			if (colon2)
				*(colon2++) = '\0';

			if (*colon) {
				*corenum = atoi(colon);
				if(*corenum <= 0 || *corenum >= 256) {
					quit(1, "Invalid bitmain-bandops for asic core num, must %d be > 0 and < 256", *corenum);
				}
			}

			if(colon2 && *colon2) {
				colon3 = strchr(colon2, ':');
				if (colon3)
					*(colon3++) = '\0';

				if(*colon2) {
					strcpy(coreenable, colon2);
					if(strlen(coreenable) != *corenum) {
						quit(1, "Invalid bitmain-bandops for asic core enable, must be equal core num %d", *corenum);
					}
				}

				if (colon3 && *colon3) {
					*coresleep = atoi(colon3);
				}
			}
		}
	}
}

static struct cgpu_info *bmsc_detect_one(struct libusb_device *dev, struct usb_find_devices *found)
{
	int this_option_offset = ++option_offset;
	struct BMSC_INFO *info;
	struct timeval tv_start, tv_finish;

	// Block 171874 nonce = (0xa2870100) = 0x000187a2
	// N.B. golden_ob MUST take less time to calculate
	//	than the timeout set in bmsc_open()
	//	This one takes ~0.53ms on Rev3 Bmsc
	const char golden_ob[] =
		"4679ba4ec99876bf4bfe086082b40025"
		"4df6c356451471139a3afa71e48f544a"
		"00000000000000004000000000000000"
		"0000001f87320b1a1426674f2fa722ce";
	const char golden_ob1[] =
		"e1eb393a50f6ae97e306ea87c1c47eae"
		"1f9ad02d729d9f86bd48a213a4600144"
		"00000000000000004000000000000000"
		"0000001ffb0b0719aaf19752dd5e83a4";
	const char golden_ob2[] =
		"b65911ea2c4b0c52958cb408caebff32"
		"8dece4e6a002fe2693ba9906ffde7e8a"
		"00000000000000004000000000000000"
		"0000001f20dc1c190642455201756658";
	const char golden_ob3[] =
		"c99da189374bcc69a1134d6f4953addc"
		"7420499b132b7f8f999b0c71fe7efbf2"
		"00000000000000004000000000000000"
		"0000001f20dc1c198e4145526d74dee3";
	const char golden_ob4[] =
		"696af96144b6079c1b437fbc6e539e4d"
		"996d25b027ea9eefdfaf4eff6add6986"
		"00000000000000004000000000000000"
		"0000001f20dc1c19f84e4552ac86dc14";

	char bandops_ob[] =
		"00000000000000000000000000000000"
		"00000000000000000000000000000000"
		"00000000000000000000000000000000"
		"00000000000000000000000000000000";

	const char golden_nonce[] = "000187a2";
	const char golden_nonce1[] = "0345182b";
	const char golden_nonce2[] = "466b30a5";
	const char golden_nonce3[] = "857e65ee";
	const char golden_nonce4[] = "c6f70284";
	const uint32_t golden_nonce_val = 0x000187a2;
	unsigned char nonce_bin[BMSC_READ_SIZE];
	struct BMSC_WORK workdata;
	char *nonce_hex;
	int baud = 115200, work_division = 1, fpga_count = 1;
	float readtimeout = 1.0;
	struct cgpu_info *bmsc;
	int ret, err, amount, tries, i;
	bool ok;
	bool cmr2_ok[CAIRNSMORE2_INTS];
	int cmr2_count;

	unsigned char cmd_buf[4] = {0};
	unsigned char rdreg_buf[4] = {0};
	unsigned char reg_data[4] = {0};
	unsigned char voltage_data[2] = {0};

	unsigned char rebuf[BMSC_READ_BUF_LEN] = {0};
	int relen = 0;
	int realllen = 0;
	int nodata = 0;
	char msg[10240] = {0};
	int sendfreqstatus = 1;
	int k = 0;

	unsigned char core_cmd[4] = {0};
	int corenum = 0;
	char coreenable[256] = {0};
	int coresleep = 0;

	if (opt_bmsc_options == NULL)
		return NULL;

	if ((sizeof(workdata) << 1) != (sizeof(golden_ob) - 1))
		quithere(1, "Data and golden_ob sizes don't match");
	if ((sizeof(workdata) << 1) != (sizeof(bandops_ob) - 1))
			quithere(1, "Data and bandops_ob sizes don't match");

	bmsc = usb_alloc_cgpu(&bmsc_drv, 1);

	if (!usb_init(bmsc, dev, found))
		goto shin;

	get_options(this_option_offset, bmsc, &baud, &readtimeout);
	get_bandops(core_cmd, &corenum, coreenable, &coresleep);

	info = (struct BMSC_INFO *)calloc(1, sizeof(struct BMSC_INFO));
	if (unlikely(!info))
		quit(1, "Failed to malloc BMSC_INFO");
	bmsc->device_data = (void *)info;

	info->ident = usb_ident(bmsc);
	info->start = true;
	switch (info->ident) {
		case IDENT_ICA:
		case IDENT_BLT:
		case IDENT_LLT:
		case IDENT_AMU:
		case IDENT_CMR1:
			info->timeout = BMSC_WAIT_TIMEOUT;
			break;
		case IDENT_CMR2:
			if (found->intinfo_count != CAIRNSMORE2_INTS) {
				quithere(1, "CMR2 Interface count (%d) isn't expected: %d",
						found->intinfo_count,
						CAIRNSMORE2_INTS);
			}
			info->timeout = BMSC_CMR2_TIMEOUT;
			cmr2_count = 0;
			for (i = 0; i < CAIRNSMORE2_INTS; i++)
				cmr2_ok[i] = false;
			break;
		default:
			quit(1, "%s bmsc_detect_one() invalid %s ident=%d",
				bmsc->drv->dname, bmsc->drv->dname, info->ident);
	}
// For CMR2 test each USB Interface
cmr2_retry:
	tries = 2;
	ok = false;
	while (!ok && tries-- > 0) {
		bmsc_initialise(bmsc, baud);

		if(opt_bmsc_bootstart) {
			applog(LOG_ERR, "---------------------start bootstart----------------------");
			cmd_buf[0] = 0xbb;
			cmd_buf[1] = 0x00;
			cmd_buf[2] = 0x00;
			cmd_buf[3] = 0x00;  //0-7
			cmd_buf[3] = CRC5(cmd_buf, 27);
			cmd_buf[3] |= 0x80;

			cgsleep_ms(500);
			applog(LOG_ERR, "Send bootstart off %02x%02x%02x%02x", cmd_buf[0], cmd_buf[1], cmd_buf[2], cmd_buf[3]);
			err = usb_write(bmsc, (char * )cmd_buf, 4, &amount, C_SENDTESTWORK);
			if (err != LIBUSB_SUCCESS || amount != 4) {
				applog(LOG_ERR, "Write bootstart Comms error (werr=%d amount=%d)", err, amount);
				continue;
			}

			cmd_buf[0] = 0xbb;
			cmd_buf[1] = 0x08;
			cmd_buf[2] = 0x00;
			cmd_buf[3] = 0x00;  //0-7
			cmd_buf[3] = CRC5(cmd_buf, 27);
			cmd_buf[3] |= 0x80;

			cgsleep_ms(500);
			applog(LOG_ERR, "Send bootstart on  %02x%02x%02x%02x", cmd_buf[0], cmd_buf[1], cmd_buf[2], cmd_buf[3]);
			err = usb_write(bmsc, (char * )cmd_buf, 4, &amount, C_SENDTESTWORK);
			if (err != LIBUSB_SUCCESS || amount != 4) {
				applog(LOG_ERR, "Write bootstart Comms error (werr=%d amount=%d)", err, amount);
				continue;
			}
			applog(LOG_ERR, "Send bootstart ok");
		}

		if(opt_bmsc_voltage) {
			if(strlen(opt_bmsc_voltage) > 4 || strlen(opt_bmsc_voltage)%2 != 0 || strlen(opt_bmsc_voltage)/2 == 0) {
				quit(1, "Invalid options for voltage data, must be hex now: %s", opt_bmsc_voltage);
			}
			memset(voltage_data, 0, 2);
			if(!hex2bin(voltage_data, opt_bmsc_voltage, strlen(opt_bmsc_voltage)/2)) {
				quit(1, "Invalid options for voltage data, hex2bin error now: %s", opt_bmsc_voltage);
			}
			cmd_buf[0] = 0xaa;
			cmd_buf[1] = voltage_data[0];
			cmd_buf[1] &=0x0f;
			cmd_buf[1] |=0xb0;
			cmd_buf[2] = voltage_data[1];
			cmd_buf[3] = 0x00;  //0-7
			cmd_buf[3] = CRC5(cmd_buf, 4*8 - 5);
			cmd_buf[3] |= 0xc0;

			applog(LOG_ERR, "---------------------start voltage----------------------");
			cgsleep_ms(500);
			applog(LOG_ERR, "Send voltage %02x%02x%02x%02x", cmd_buf[0], cmd_buf[1], cmd_buf[2], cmd_buf[3]);
			err = usb_write(bmsc, (char * )cmd_buf, 4, &amount, C_SENDTESTWORK);
			if (err != LIBUSB_SUCCESS || amount != 4) {
				applog(LOG_ERR, "Write voltage Comms error (werr=%d amount=%d)", err, amount);
				continue;
			}
			applog(LOG_ERR, "Send voltage ok");
		}

		if (opt_bmsc_gray) {
			cmd_buf[0] = 3;
			cmd_buf[0] |= 0x80;
			cmd_buf[1] = 0; //16-23
			cmd_buf[2] = 0x80;  //8-15
			cmd_buf[3] = 0x80;  //0-7
			cmd_buf[3] = CRC5(cmd_buf, 27);
			cmd_buf[3] |= 0x80;

			applog(LOG_ERR, "-----------------start gray-------------------");
			cgsleep_ms(500);
			applog(LOG_ERR, "Send gray %02x%02x%02x%02x", cmd_buf[0], cmd_buf[1], cmd_buf[2], cmd_buf[3]);
			err = usb_write_ii(bmsc, info->intinfo, (char * )cmd_buf, 4, &amount, C_SENDWORK);
			if (err != LIBUSB_SUCCESS || amount != 4) {
				applog(LOG_ERR, "%s%i: Write freq Comms error (werr=%d amount=%d)", bmsc->drv->name, bmsc->device_id, err, amount);
				continue;
			}
			applog(LOG_DEBUG, "Send gray ok");
		}

		if (opt_bmsc_freq) {
			if (strcmp(opt_bmsc_freq, "0") != 0) {
				applog(LOG_DEBUG, "Device detect freq parameter=%s", opt_bmsc_freq);
				if (strlen(opt_bmsc_freq) > 8 || strlen(opt_bmsc_freq) % 2 != 0 || strlen(opt_bmsc_freq) / 2 == 0) {
					quit(1, "Invalid bmsc_freq for freq data, must be hex now: %s", opt_bmsc_freq);
				}
				memset(reg_data, 0, 4);
				if (!hex2bin(reg_data, opt_bmsc_freq, strlen(opt_bmsc_freq) / 2)) {
					quit(1, "Invalid bmsc_freq for freq data, hex2bin error now: %s", opt_bmsc_freq);
				}
				cmd_buf[0] = 2;
				cmd_buf[0] |= 0x80;
				cmd_buf[1] = reg_data[0]; //16-23
				cmd_buf[2] = reg_data[1];  //8-15
				cmd_buf[3] = 0;
				cmd_buf[3] = CRC5(cmd_buf, 27);
				applog(LOG_DEBUG, "Set_frequency cmd_buf[1]{%02x}cmd_buf[2]{%02x}", cmd_buf[1], cmd_buf[2]);

				rdreg_buf[0] = 4;
				rdreg_buf[0] |= 0x80;
				rdreg_buf[1] = 0; //16-23
				rdreg_buf[2] = 0x04;  //8-15
				rdreg_buf[3] = 0;
				rdreg_buf[3] = CRC5(rdreg_buf, 27);

				applog(LOG_ERR, "-----------------start freq-------------------");
				cgsleep_ms(500);

				applog(LOG_ERR, "Send frequency %02x%02x%02x%02x", cmd_buf[0], cmd_buf[1], cmd_buf[2], cmd_buf[3]);
				err = usb_write_ii(bmsc, info->intinfo, (char * )cmd_buf, 4, &amount, C_SENDWORK);
				if (err != LIBUSB_SUCCESS || amount != 4) {
					applog(LOG_ERR, "%s%i: Write freq Comms error (werr=%d amount=%d)", bmsc->drv->name, bmsc->device_id, err, amount);
					continue;
				}
				applog(LOG_DEBUG, "Send frequency ok");

				cgsleep_ms(500);

				applog(LOG_ERR, "Send freq getstatus %02x%02x%02x%02x", rdreg_buf[0], rdreg_buf[1], rdreg_buf[2], rdreg_buf[3]);

				for(i = 0; i < 10; i++) {
					usb_read_ii_timeout_cancellable(bmsc, info->intinfo, (char * )rebuf, BMSC_READ_SIZE, &relen, 100, C_GETRESULTS);
				}

				err = usb_write_ii(bmsc, info->intinfo, (char * )rdreg_buf, 4, &amount, C_SENDWORK);
				if (err != LIBUSB_SUCCESS || amount != 4) {
					applog(LOG_ERR, "%s%i: Write freq getstatus Comms error (werr=%d amount=%d)", bmsc->drv->name, bmsc->device_id, err, amount);
					continue;
				}
				applog(LOG_DEBUG, "Send freq getstatus ok");

				nodata = 0;
				realllen = 0;
				while (1) {
					relen = 0;
					err = usb_read_ii_timeout_cancellable(bmsc, info->intinfo, (char * )rebuf + realllen, BMSC_READ_SIZE, &relen, 200, C_GETRESULTS);
					if (err < 0 && err != LIBUSB_ERROR_TIMEOUT) {
						applog(LOG_ERR, "%s%i: Read freq Comms error (rerr=%d relen=%d)", bmsc->drv->name, bmsc->device_id, err, relen);
						break;
					} else if (err == LIBUSB_ERROR_TIMEOUT) {
						applog(LOG_DEBUG, "%s%i: Read freq Comms timeout (rerr=%d relen=%d)", bmsc->drv->name, bmsc->device_id, err, relen);

						nodata++;
						if (nodata > 5) {
							if (realllen <= 0) {
								if (sendfreqstatus) {
									sendfreqstatus = 0;
									applog(LOG_ERR, "Send freq getstatus %02x%02x%02x%02x", rdreg_buf[0], rdreg_buf[1], rdreg_buf[2], rdreg_buf[3]);
									usb_read_ii_timeout_cancellable(bmsc, info->intinfo, (char * )rebuf, BMSC_READ_SIZE, &relen, 200, C_GETRESULTS);
									err = usb_write_ii(bmsc, info->intinfo, (char * )rdreg_buf, 4, &amount, C_SENDWORK);
									if (err != LIBUSB_SUCCESS || amount != 4) {
										applog(LOG_ERR, "%s%i: Write freq getstatus Comms error (werr=%d amount=%d)", bmsc->drv->name, bmsc->device_id, err, amount);
										continue;
									}
									applog(LOG_DEBUG, "Send freq getstatus ok");
								} else {
									applog(LOG_ERR, "------recv freq getstatus no data finish------");
									break;
								}
							} else {
								applog(LOG_DEBUG, "Recv freq getstatus len=%d", realllen);
								for (i = 0; i < realllen; i += 5) {
									applog(LOG_ERR, "Recv %d freq getstatus=%02x%02x%02x%02x%02x", i / 5 + 1, rebuf[i], rebuf[i + 1], rebuf[i + 2], rebuf[i + 3], rebuf[i + 4]);
								}
								applog(LOG_ERR, "--------recv freq getstatus ok finish---------");
								break;
							}
						}
						continue;
					} else {
						nodata = 0;
						realllen += relen;
						for (i = 0; i < relen; i++) {
							sprintf(msg + i * 2, "%02x", rebuf[i]);
						}
						applog(LOG_DEBUG, "Read data(%d):%s", relen, msg);
					}
				}
			} else {
				applog(LOG_ERR, "Device detect freq 0 parameter");
			}
		}

		if (opt_bmsc_rdreg) {
			applog(LOG_DEBUG, "Device detect rdreg parameter=%s", opt_bmsc_rdreg);
			if (strlen(opt_bmsc_rdreg) > 8 || strlen(opt_bmsc_rdreg) % 2 != 0 || strlen(opt_bmsc_rdreg) / 2 == 0) {
				quit(1, "Invalid bmsc_rdreg for reg data, must be hex now: %s", opt_bmsc_rdreg);
			}
			memset(reg_data, 0, 4);
			if (!hex2bin(reg_data, opt_bmsc_rdreg, strlen(opt_bmsc_rdreg) / 2)) {
				quit(1, "Invalid bmsc_rdreg for reg data, hex2bin error now: %s", opt_bmsc_rdreg);
			}
			rdreg_buf[0] = 4;
			rdreg_buf[0] |= 0x80;
			rdreg_buf[1] = 0; //16-23
			rdreg_buf[2] = reg_data[0];  //8-15
			rdreg_buf[3] = 0;
			rdreg_buf[3] = CRC5(rdreg_buf, 27);
			applog(LOG_DEBUG, "Get_status rdreg_buf[1]{%02x}rdreg_buf[2]{%02x}", rdreg_buf[1], rdreg_buf[2]);

			applog(LOG_ERR, "-----------------start rdreg------------------");
			applog(LOG_ERR, "Send getstatus %02x%02x%02x%02x", rdreg_buf[0], rdreg_buf[1], rdreg_buf[2], rdreg_buf[3]);

			for(i = 0; i < 10; i++) {
				usb_read_ii_timeout_cancellable(bmsc, info->intinfo, (char * )rebuf, BMSC_READ_SIZE, &relen, 100, C_GETRESULTS);
			}

			err = usb_write_ii(bmsc, info->intinfo, (char * )rdreg_buf, 4, &amount, C_SENDWORK);
			if (err != LIBUSB_SUCCESS || amount != 4) {
				applog(LOG_ERR, "%s%i: Write rdreg Comms error (werr=%d amount=%d)", bmsc->drv->name, bmsc->device_id, err, amount);
				continue;
			}
			applog(LOG_DEBUG, "Send getstatus ok");

			nodata = 0;
			realllen = 0;
			while (1) {
				relen = 0;
				err = usb_read_ii_timeout_cancellable(bmsc, info->intinfo, (char * )rebuf + realllen, BMSC_READ_SIZE, &relen, 200, C_GETRESULTS);
				if (err < 0 && err != LIBUSB_ERROR_TIMEOUT) {
					applog(LOG_ERR, "%s%i: Read rdreg Comms error (rerr=%d relen=%d)", bmsc->drv->name, bmsc->device_id, err, relen);
					break;
				} else if (err == LIBUSB_ERROR_TIMEOUT) {
					applog(LOG_DEBUG, "%s%i: Read rdreg Comms timeout (rerr=%d relen=%d)", bmsc->drv->name, bmsc->device_id, err, relen);

					nodata++;
					if (nodata > 5) {
						applog(LOG_DEBUG, "Recv rdreg getstatus len=%d", realllen);
						for (i = 0; i < realllen; i += 5) {
							applog(LOG_ERR, "Recv %d rdreg getstatus=%02x%02x%02x%02x%02x", i / 5 + 1, rebuf[i], rebuf[i + 1], rebuf[i + 2], rebuf[i + 3], rebuf[i + 4]);
						}
						applog(LOG_ERR, "---------recv rdreg getstatus finish----------");
						break;
					}
					continue;
				} else {
					nodata = 0;
					realllen += relen;
					for (i = 0; i < relen; i++) {
						sprintf(msg + i * 2, "%02x", rebuf[i]);
					}
					applog(LOG_DEBUG, "Read data(%d):%s", relen, msg);
				}
			}
		}

		if (opt_bmsc_bandops) {
			unsigned char tmpbyte = 0;
			cmd_buf[0] = core_cmd[0];
			cmd_buf[1] = core_cmd[1];
			cmd_buf[2] = core_cmd[2];
			tmpbyte = core_cmd[3] & 0xE0;
			cmd_buf[3] = tmpbyte;
			cmd_buf[3] = CRC5(cmd_buf, 27);
			cmd_buf[3] |= tmpbyte;

			applog(LOG_ERR, "-----------------start bandops-------------------");
			applog(LOG_ERR, "SetBandOPS cmd:%02x%02x%02x%02x corenum:%d enable:%s sleep:%d", core_cmd[0], core_cmd[1], core_cmd[2], core_cmd[3], corenum, coreenable, coresleep);
			cgsleep_ms(500);
			applog(LOG_ERR, "Send bandops %02x%02x%02x%02x", cmd_buf[0], cmd_buf[1], cmd_buf[2], cmd_buf[3]);
			err = usb_write_ii(bmsc, info->intinfo, (char * )cmd_buf, 4, &amount, C_SENDWORK);
			if (err != LIBUSB_SUCCESS || amount != 4) {
				applog(LOG_ERR, "%s%i: Write BandOPS Comms error (werr=%d amount=%d)", bmsc->drv->name, bmsc->device_id, err, amount);
				continue;
			}
			applog(LOG_DEBUG, "Send bandops command ok");
			for(i = 0; i < corenum; i++) {
				if(coreenable[i] == '1') {
					bandops_ob[127] = '1';
				} else {
					bandops_ob[127] = '0';
				}
				amount = 0;
				hex2bin((void *)(&workdata), bandops_ob, sizeof(workdata));
				applog(LOG_ERR, "Send %d %s", i, bandops_ob);
				err = usb_write_ii(bmsc, info->intinfo, (char *)(&workdata), sizeof(workdata), &amount, C_SENDWORK);
				if (err != LIBUSB_SUCCESS || amount != sizeof(workdata)) {
					applog(LOG_ERR, "%d %s%i: Write BandOPS Enable Comms error (werr=%d amount=%d)", i, bmsc->drv->name, bmsc->device_id, err, amount);
					break;
				}
				if(coresleep > 0) {
					cgsleep_ms(coresleep);
				}
			}
			if(i >= corenum) {
				applog(LOG_DEBUG, "Send bandops core enable ok");
			} else {
				continue;
			}
		}
		cgsleep_ms(1000);

		applog(LOG_ERR, "-----------------start nonce------------------");
#if 0
		applog(LOG_ERR, "Bmsc send golden nonce");

		hex2bin((void *)(&workdata), golden_ob, sizeof(workdata));
		err = usb_write_ii(bmsc, info->intinfo, (char *)(&workdata), sizeof(workdata), &amount, C_SENDWORK);
		if (err != LIBUSB_SUCCESS || amount != sizeof(workdata))
			continue;

		memset(nonce_bin, 0, sizeof(nonce_bin));
		ret = bmsc_get_nonce(bmsc, nonce_bin, &tv_start, &tv_finish, NULL, 500);
		if (ret != BTM_NONCE_OK) {
			applog(LOG_ERR, "Bmsc recv golden nonce timeout");
			continue;
		}

		nonce_hex = bin2hex(nonce_bin, sizeof(nonce_bin));
		if (strncmp(nonce_hex, golden_nonce, 8) == 0)
			ok = true;
		else {
			applog(LOG_ERR, "Bmsc recv golden nonce %s != %s and retry", nonce_hex, golden_nonce);
			if (tries < 0 && info->ident != IDENT_CMR2) {
				applog(LOG_ERR, "Bmsc Detect: Test failed at %s: get %s, should: %s",
					bmsc->device_path, nonce_hex, golden_nonce);
			}
		}
		
		applog(LOG_ERR, "Bmsc recv golden nonce %s -- %s ", nonce_hex, golden_nonce);
#else
		applog(LOG_ERR, "Bmsc send golden nonce1");
		hex2bin((void *)(&workdata), golden_ob1, sizeof(workdata));
		err = usb_write_ii(bmsc, info->intinfo, (char *)(&workdata), sizeof(workdata), &amount, C_SENDWORK);
		if (err != LIBUSB_SUCCESS || amount != sizeof(workdata))
			continue;

		memset(nonce_bin, 0, sizeof(nonce_bin));
		ret = bmsc_get_nonce(bmsc, nonce_bin, &tv_start, &tv_finish, NULL, 500);
		if (ret != BTM_NONCE_OK) {
			applog(LOG_ERR, "Bmsc recv golden nonce timeout");
			continue;
		}

		nonce_hex = bin2hex(nonce_bin, sizeof(nonce_bin));
		if (strncmp(nonce_hex, golden_nonce1, 8) == 0)
			ok = true;		
		else {
			applog(LOG_ERR, "Bmsc recv golden nonce %s != %s and retry", nonce_hex, golden_nonce1);
			applog(LOG_ERR,"The first chip may not work,reconnrect the device will get better stats");
			cgsleep_ms(1000);
			if (tries < 0 && info->ident != IDENT_CMR2) {
				applog(LOG_ERR, "Bmsc Detect: Test failed at %s: get %s, should: %s",
					bmsc->device_path, nonce_hex, golden_nonce1);
			}
		}
		applog(LOG_ERR, "Bmsc recv golden nonce1 %s -- %s ", nonce_hex, golden_nonce1);

		applog(LOG_ERR, "Bmsc send golden nonce2");

		hex2bin((void *)(&workdata), golden_ob2, sizeof(workdata));
		err = usb_write_ii(bmsc, info->intinfo, (char *)(&workdata), sizeof(workdata), &amount, C_SENDWORK);
		if (err != LIBUSB_SUCCESS || amount != sizeof(workdata))
			continue;

		memset(nonce_bin, 0, sizeof(nonce_bin));
		ret = bmsc_get_nonce(bmsc, nonce_bin, &tv_start, &tv_finish, NULL, 500);
		if (ret != BTM_NONCE_OK) {
			applog(LOG_ERR, "Bmsc recv golden nonce timeout");
			continue;
		}

		nonce_hex = bin2hex(nonce_bin, sizeof(nonce_bin));
		if (strncmp(nonce_hex, golden_nonce2, 8) == 0)
			ok = true;		
		else {
			applog(LOG_ERR, "Bmsc recv golden nonce %s != %s and retry", nonce_hex, golden_nonce2);
			applog(LOG_ERR,"The second chip may not work,reconnrect the device will get better stats");
			cgsleep_ms(1000);
			if (tries < 0 && info->ident != IDENT_CMR2) {
				applog(LOG_ERR, "Bmsc Detect: Test failed at %s: get %s, should: %s",
					bmsc->device_path, nonce_hex, golden_nonce2);
			}
		}
		applog(LOG_ERR, "Bmsc recv golden nonce2 %s -- %s ", nonce_hex, golden_nonce2);
		applog(LOG_ERR, "Bmsc send golden nonce3");
		hex2bin((void *)(&workdata), golden_ob3, sizeof(workdata));
		err = usb_write_ii(bmsc, info->intinfo, (char *)(&workdata), sizeof(workdata), &amount, C_SENDWORK);
		if (err != LIBUSB_SUCCESS || amount != sizeof(workdata))
			continue;

		memset(nonce_bin, 0, sizeof(nonce_bin));
		ret = bmsc_get_nonce(bmsc, nonce_bin, &tv_start, &tv_finish, NULL, 500);
		if (ret != BTM_NONCE_OK) {
			applog(LOG_ERR, "Bmsc recv golden nonce timeout");
			continue;
		}

		nonce_hex = bin2hex(nonce_bin, sizeof(nonce_bin));
		if (strncmp(nonce_hex, golden_nonce3, 8) == 0)
			ok = true;		
		else {
			applog(LOG_ERR, "Bmsc recv golden nonce %s != %s and retry", nonce_hex, golden_nonce3);
			applog(LOG_ERR,"The third chip may not work,reconnrect the device will get better stats");
			cgsleep_ms(1000);
			if (tries < 0 && info->ident != IDENT_CMR2) {
				applog(LOG_ERR, "Bmsc Detect: Test failed at %s: get %s, should: %s",
					bmsc->device_path, nonce_hex, golden_nonce3);
			}
		}
		
		applog(LOG_ERR, "Bmsc recv golden nonce %s -- %s ", nonce_hex, golden_nonce3);		
		applog(LOG_ERR, "Bmsc send golden nonce4");

		hex2bin((void *)(&workdata), golden_ob4, sizeof(workdata));
		err = usb_write_ii(bmsc, info->intinfo, (char *)(&workdata), sizeof(workdata), &amount, C_SENDWORK);
		if (err != LIBUSB_SUCCESS || amount != sizeof(workdata))
			continue;

		memset(nonce_bin, 0, sizeof(nonce_bin));
		ret = bmsc_get_nonce(bmsc, nonce_bin, &tv_start, &tv_finish, NULL, 500);
		if (ret != BTM_NONCE_OK) {
			applog(LOG_ERR, "Bmsc recv golden nonce4 timeout");
			continue;
		}

		nonce_hex = bin2hex(nonce_bin, sizeof(nonce_bin));
		if (strncmp(nonce_hex, golden_nonce4, 8) == 0)
			ok = true;
		
		else {
			applog(LOG_ERR, "Bmsc recv golden nonce %s != %s and retry", nonce_hex, golden_nonce4);
			applog(LOG_ERR,"The fourth chip may not work,reconnrect the device will get better stats");
			cgsleep_ms(1000);
			if (tries < 0 && info->ident != IDENT_CMR2) {
				applog(LOG_ERR, "Bmsc Detect: Test failed at %s: get %s, should: %s",
					bmsc->device_path, nonce_hex, golden_nonce4);
			}
		}
		
		applog(LOG_ERR, "Bmsc recv golden nonce %s -- %s ", nonce_hex, golden_nonce4);
#endif
		free(nonce_hex);
	}

	if (!ok) {
		if (info->ident != IDENT_CMR2)
			goto unshin;

		if (info->intinfo < CAIRNSMORE2_INTS-1) {
			info->intinfo++;
			goto cmr2_retry;
		}
	} else {
		if (info->ident == IDENT_CMR2) {
			applog(LOG_DEBUG,
				"Bmsc Detect: "
				"Test succeeded at %s i%d: got %s",
					bmsc->device_path, info->intinfo, golden_nonce);

			cmr2_ok[info->intinfo] = true;
			cmr2_count++;
			if (info->intinfo < CAIRNSMORE2_INTS-1) {
				info->intinfo++;
				goto cmr2_retry;
			}
		}
	}

	if (info->ident == IDENT_CMR2) {
		if (cmr2_count == 0) {
			applog(LOG_ERR,
				"Bmsc Detect: Test failed at %s: for all %d CMR2 Interfaces",
				bmsc->device_path, CAIRNSMORE2_INTS);
			goto unshin;
		}

		// set the interface to the first one that succeeded
		for (i = 0; i < CAIRNSMORE2_INTS; i++)
			if (cmr2_ok[i]) {
				info->intinfo = i;
				break;
			}
	} else {
		applog(LOG_DEBUG,
			"Bmsc Detect: "
			"Test succeeded at %s: got %s",
				bmsc->device_path, golden_nonce);
	}

	/* We have a real Bmsc! */
	if (!add_cgpu(bmsc))
		goto unshin;

	update_usb_stats(bmsc);

	applog(LOG_INFO, "%s%d: Found at %s",
		bmsc->drv->name, bmsc->device_id, bmsc->device_path);

	if (info->ident == IDENT_CMR2) {
		applog(LOG_INFO, "%s%d: with %d Interface%s",
				bmsc->drv->name, bmsc->device_id,
				cmr2_count, cmr2_count > 1 ? "s" : "");

		// Assume 1 or 2 are running FPGA pairs
		if (cmr2_count < 3) {
			work_division = fpga_count = 2;
			info->Hs /= 2;
		}
	}

	applog(LOG_DEBUG, "%s%d: Init baud=%d work_division=%d fpga_count=%d readtimeout=%f",
		bmsc->drv->name, bmsc->device_id, baud, work_division, fpga_count, readtimeout);

	info->baud = baud;
	info->work_division = work_division;
	info->fpga_count = fpga_count;
	info->nonce_mask = mask(work_division);
	info->work_queue_index = 0;
	for(k = 0; k < BMSC_WORK_QUEUE_NUM; k++) {
		info->work_queue[k] = NULL;
	}

	info->golden_hashes = (golden_nonce_val & info->nonce_mask) * fpga_count;
	timersub(&tv_finish, &tv_start, &(info->golden_tv));

	set_timing_mode(this_option_offset, bmsc, readtimeout);

	if (info->ident == IDENT_CMR2) {
		int i;
		for (i = info->intinfo + 1; i < bmsc->usbdev->found->intinfo_count; i++) {
			struct cgpu_info *cgtmp;
			struct BMSC_INFO *intmp;

			if (!cmr2_ok[i])
				continue;

			cgtmp = usb_copy_cgpu(bmsc);
			if (!cgtmp) {
				applog(LOG_ERR, "%s%d: Init failed initinfo %d",
						bmsc->drv->name, bmsc->device_id, i);
				continue;
			}

			cgtmp->usbinfo.usbstat = USB_NOSTAT;

			intmp = (struct BMSC_INFO *)malloc(sizeof(struct BMSC_INFO));
			if (unlikely(!intmp))
				quit(1, "Failed2 to malloc BMSC_INFO");

			cgtmp->device_data = (void *)intmp;

			// Initialise everything to match
			memcpy(intmp, info, sizeof(struct BMSC_INFO));

			intmp->intinfo = i;

			bmsc_initialise(cgtmp, baud);

			if (!add_cgpu(cgtmp)) {
				usb_uninit(cgtmp);
				free(intmp);
				continue;
			}

			update_usb_stats(cgtmp);
		}
	}

	return bmsc;

unshin:

	usb_uninit(bmsc);
	free(info);
	bmsc->device_data = NULL;

shin:

	bmsc = usb_free_cgpu(bmsc);

	return NULL;
}

static void bmsc_detect(bool __maybe_unused hotplug)
{
	usb_detect(&bmsc_drv, bmsc_detect_one);
}

static bool bmsc_prepare(__maybe_unused struct thr_info *thr)
{
//	struct cgpu_info *bmsc = thr->cgpu;
	return true;
}

static void cmr2_command(struct cgpu_info *bmsc, uint8_t cmd, uint8_t data)
{
	struct BMSC_INFO *info = (struct BMSC_INFO *)(bmsc->device_data);
	struct BMSC_WORK workdata;
	int amount;

	memset((void *)(&workdata), 0, sizeof(workdata));

	workdata.prefix = BMSC_CMR2_PREFIX;
	workdata.cmd = cmd;
	workdata.data = data;
	workdata.check = workdata.data ^ workdata.cmd ^ workdata.prefix ^ BMSC_CMR2_CHECK;

	usb_write_ii(bmsc, info->intinfo, (char *)(&workdata), sizeof(workdata), &amount, C_SENDWORK);
}

static void cmr2_commands(struct cgpu_info *bmsc)
{
	struct BMSC_INFO *info = (struct BMSC_INFO *)(bmsc->device_data);

	if (info->speed_next_work) {
		info->speed_next_work = false;
		cmr2_command(bmsc, BMSC_CMR2_CMD_SPEED, info->cmr2_speed);
		return;
	}

	if (info->flash_next_work) {
		info->flash_next_work = false;
		cmr2_command(bmsc, BMSC_CMR2_CMD_FLASH, BMSC_CMR2_DATA_FLASH_ON);
		cgsleep_ms(250);
		cmr2_command(bmsc, BMSC_CMR2_CMD_FLASH, BMSC_CMR2_DATA_FLASH_OFF);
		cgsleep_ms(250);
		cmr2_command(bmsc, BMSC_CMR2_CMD_FLASH, BMSC_CMR2_DATA_FLASH_ON);
		cgsleep_ms(250);
		cmr2_command(bmsc, BMSC_CMR2_CMD_FLASH, BMSC_CMR2_DATA_FLASH_OFF);
		return;
	}
}

static int64_t bmsc_scanwork(struct thr_info *thr)
{
	struct cgpu_info *bmsc = thr->cgpu;
	struct BMSC_INFO *info = (struct BMSC_INFO *)(bmsc->device_data);
	int ret, err, amount;
	unsigned char nonce_bin[BMSC_READ_SIZE];
	struct BMSC_WORK workdata;
	char *ob_hex;
	uint32_t nonce;
	int64_t hash_count = 0;
	struct timeval tv_start, tv_finish, elapsed;
	struct timeval tv_history_start, tv_history_finish;
	double Ti, Xi;
	int curr_hw_errors, i;
	bool was_hw_error;
	struct work *work = NULL;
	struct work *worktmp = NULL;

	struct BMSC_HISTORY *history0, *history;
	int count;
	double Hs, W, fullnonce;
	int read_time;
	bool limited;
	int64_t estimate_hashes;
	uint32_t values;
	int64_t hash_count_range;
	unsigned char workid = 0;
	int submitfull = 0;
	bool submitnonceok = true;

	// Device is gone
	if (bmsc->usbinfo.nodev)
		return -1;

	elapsed.tv_sec = elapsed.tv_usec = 0;

retry:
	work = get_work(thr, thr->id);
	memset((void *)(&workdata), 0, sizeof(workdata));
	memcpy(&(workdata.midstate), work->midstate, BMSC_MIDSTATE_SIZE);
	memcpy(&(workdata.work), work->data + BMSC_WORK_DATA_OFFSET, BMSC_WORK_SIZE);
	rev((void *)(&(workdata.midstate)), BMSC_MIDSTATE_SIZE);
	rev((void *)(&(workdata.work)), BMSC_WORK_SIZE);

	if(work->midstate[BMSC_MIDSTATE_SIZE-1] == 0xaa)
		goto retry;
	workdata.workid = work->id;
	workid = work->id;
	workid = workid & 0x1F;

	// We only want results for the work we are about to send
	usb_buffer_clear(bmsc);

	if(info->work_queue[workid]) {
		free(info->work_queue[workid]);
		info->work_queue[workid] = NULL;
	}
	info->work_queue[workid] = copy_work(work);

	err = usb_write_ii(bmsc, info->intinfo, (char *)(&workdata), sizeof(workdata), &amount, C_SENDWORK);
	if (err < 0 || amount != sizeof(workdata)) {
		applog(LOG_ERR, "%s%i: Comms error (werr=%d amt=%d)", bmsc->drv->name, bmsc->device_id, err, amount);
		dev_error(bmsc, REASON_DEV_COMMS_ERROR);
		bmsc_initialise(bmsc, info->baud);
		goto out;
	}

	if (opt_debug) {
		ob_hex = bin2hex((void *)(&workdata), sizeof(workdata));
		applog(LOG_DEBUG, "%s%d: sent %s", bmsc->drv->name, bmsc->device_id, ob_hex);
		free(ob_hex);
	}

	/* Bmsc will return 4 bytes (BMSC_READ_SIZE) nonces or nothing */
	memset(nonce_bin, 0, sizeof(nonce_bin));
	ret = bmsc_get_nonce(bmsc, nonce_bin, &tv_start, &tv_finish, thr, info->read_time);
	if (ret == BTM_NONCE_ERROR)
		goto out;

	// aborted before becoming idle, get new work
	if (ret == BTM_NONCE_TIMEOUT || ret == BTM_NONCE_RESTART) {
		timersub(&tv_finish, &tv_start, &elapsed);

		// ONLY up to just when it aborted
		// We didn't read a reply so we don't subtract BMSC_READ_TIME
		estimate_hashes = ((double)(elapsed.tv_sec) + ((double)(elapsed.tv_usec))/((double)1000000)) / info->Hs;

		// If some Serial-USB delay allowed the full nonce range to
		// complete it can't have done more than a full nonce
		if (unlikely(estimate_hashes > 0xffffffff))
			estimate_hashes = 0xffffffff;

		applog(LOG_DEBUG, "%s%d: no nonce = 0x%08lX hashes (%ld.%06lds)", bmsc->drv->name, bmsc->device_id, (long unsigned int)estimate_hashes, elapsed.tv_sec, elapsed.tv_usec);

		hash_count = 0;
		goto out;
	}

	memcpy((char *)&nonce, nonce_bin, sizeof(nonce));
	nonce = htobe32(nonce);
	curr_hw_errors = bmsc->hw_errors;

	workid = nonce_bin[4];
	workid = workid & 0x1F;
	worktmp = info->work_queue[workid];
	if(info->start && workid == 0x1f){
		goto out;
	}else{
		info->start = false;
	}
	if(worktmp) {
		submitfull = 0;
		if(submit_nonce_1(thr, worktmp, nonce, &submitfull)) {
			submitnonceok = true;
			submit_nonce_2(worktmp);
		} else {
			if(submitfull) {
				submitnonceok = true;
			} else {
				submitnonceok = false;
			}
		}
		cg_logwork(worktmp, nonce_bin, submitnonceok);
	} else {
		applog(LOG_ERR, "%s%d: work %02x not find error", bmsc->drv->name, bmsc->device_id, workid);
	}

	was_hw_error = (curr_hw_errors > bmsc->hw_errors);

	hash_count = (nonce & info->nonce_mask);
	hash_count++;
	hash_count *= info->fpga_count;

	hash_count = 0xffffffff;

	if (opt_debug || info->do_bmsc_timing)
		timersub(&tv_finish, &tv_start, &elapsed);

	applog(LOG_DEBUG, "%s%d: nonce = 0x%08x = 0x%08lX hashes (%ld.%06lds)", bmsc->drv->name, bmsc->device_id, nonce, (long unsigned int)hash_count, elapsed.tv_sec, elapsed.tv_usec);

out:
	free_work(work);
	return hash_count;
}
/*
static int64_t bmsc_scanwork(struct thr_info *thr)
{
	struct cgpu_info *bmsc = thr->cgpu;
	struct BMSC_INFO *info = (struct BMSC_INFO *)(bmsc->device_data);
	int ret, err, amount;
	unsigned char nonce_bin[BMSC_READ_SIZE];
	struct BMSC_WORK workdata;
	char *ob_hex;
	uint32_t nonce;
	int64_t hash_count = 0;
	int64_t hash_done = 0;
	struct timeval tv_start, tv_finish, elapsed;
	struct timeval tv_history_start, tv_history_finish;
	double Ti, Xi;
	int curr_hw_errors;
	bool was_hw_error;
	struct work *work;

	struct BMSC_HISTORY *history0, *history;
	double Hs, W, fullnonce;
	bool limited;
	int64_t estimate_hashes;
	uint32_t values;
	int64_t hash_count_range;

	int i = 0, count = 0, nofullcount = 0, readalllen = 0, readlen = 0, read_time = 0, nofull = 0;
	bool nonceok = false;
	bool noncedup = false;

	char testbuf[256] = {0};
	char testtmp[256] = {0};
	int asicnum = 0;
	int k = 0;

	// Device is gone
	if (bmsc->usbinfo.nodev)
		return -1;

	elapsed.tv_sec = elapsed.tv_usec = 0;

	work = get_work(thr, thr->id);
	memset((void *)(&workdata), 0, sizeof(workdata));
	memcpy(&(workdata.midstate), work->midstate, BMSC_MIDSTATE_SIZE);
	memcpy(&(workdata.work), work->data + BMSC_WORK_DATA_OFFSET, BMSC_WORK_SIZE);
	rev((void *)(&(workdata.midstate)), BMSC_MIDSTATE_SIZE);
	rev((void *)(&(workdata.work)), BMSC_WORK_SIZE);

	applog(LOG_DEBUG, "bmsc_scanhash start ------------");

	readalllen = 0;
	readlen = 0;
	if(info->work_queue != NULL) {
		while (true) {
			if (bmsc->usbinfo.nodev)
				return -1;
			amount = 0;
			memset(nonce_bin, 0, sizeof(nonce_bin));
			err = usb_read_once_timeout(bmsc, (char *)nonce_bin+readlen, 5-readlen, &amount, BMSC_WAIT_TIMEOUT, C_GETRESULTS);
			if (err < 0 && err != LIBUSB_ERROR_TIMEOUT) {
				applog(LOG_ERR, "%s%i: Comms error (rerr=%d amt=%d)", bmsc->drv->name, bmsc->device_id, err, amount);
				dev_error(bmsc, REASON_DEV_COMMS_ERROR);
				return 0;
			}
			if (amount > 0) {
				readalllen += amount;
				readlen += amount;
				if (readlen >= 5) {
					nonceok = false;

					memcpy((char *) &nonce, nonce_bin, BMSC_READ_SIZE);
					noncedup = false;
					for(i = 0; i < BMSC_NONCE_ARRAY_SIZE; i++) {
						if(memcmp(nonce_bin, info->nonce_bin[i], BMSC_READ_SIZE) == 0) {
							noncedup = true;
							break;
						}
					}
					if (!noncedup) {
						if(info->nonce_index < 0 || info->nonce_index >= BMSC_NONCE_ARRAY_SIZE)
							info->nonce_index = 0;

						memcpy(info->nonce_bin[info->nonce_index], nonce_bin, BMSC_READ_SIZE);
						info->nonce_index++;

						nonce = htobe32(nonce);

						nofull = 0;
						if (submit_nonce_1(thr, info->work_queue, nonce, &nofull)) {
							applog(LOG_DEBUG, "Bmsc nonce(0x%08x) match old work", nonce);
							submit_nonce_2(info->work_queue);
							nonceok = true;
						} else {
							if(!nofull) {
								applog(LOG_DEBUG, "Bmsc nonce(0x%08x) not match old work", nonce);
								usb_buffer_clear(bmsc);
								inc_hw_errors(thr);
								break;
							} else {
								nofullcount++;
							}
						}
					} else {
						applog(LOG_DEBUG, "Bmsc nonce duplication");
					}

					if (nonceok) {
						count++;
						hash_count = (nonce & info->nonce_mask);
						hash_count++;
						hash_count *= info->fpga_count;
						hash_done += 0xffffffff;//hash_count;

						applog(LOG_DEBUG, "%s%d: nonce = 0x%08x = 0x%08lX hashes (%ld.%06lds)",
								bmsc->drv->name, bmsc->device_id, nonce, (long unsigned int )hash_count, elapsed.tv_sec, elapsed.tv_usec);
					}
					readlen = 0;
				}
			} else {
				//usb_buffer_clear(bmsc);
				applog(LOG_DEBUG, "bmsc_scanhash usb_read_once_timeout read time out");
				break;
			}
		}
	}

	err = usb_write(bmsc, (char *)(&workdata), sizeof(workdata), &amount, C_SENDWORK);
	if (err < 0 || amount != sizeof(workdata)) {
		applog(LOG_ERR, "%s%i: Comms error (werr=%d amt=%d)", bmsc->drv->name, bmsc->device_id, err, amount);
		dev_error(bmsc, REASON_DEV_COMMS_ERROR);
		bmsc_initialise(bmsc, info->baud);
		return 0;
	}

	if (opt_debug) {
		ob_hex = bin2hex((char *)&workdata, sizeof(workdata));
		applog(LOG_DEBUG, "%s%d: sent %s", bmsc->drv->name, bmsc->device_id, ob_hex);
		free(ob_hex);
	}

	cgtime(&tv_start);
	readlen = 0;
	while(true) {
		if (bmsc->usbinfo.nodev)
			return -1;
		amount = 0;
		memset(nonce_bin, 0, sizeof(nonce_bin));
		err = usb_read_once_timeout(bmsc, (char *)nonce_bin+readlen, 5-readlen, &amount, BMSC_WAIT_TIMEOUT, C_GETRESULTS);
		cgtime(&tv_finish);
		if (err < 0 && err != LIBUSB_ERROR_TIMEOUT) {
			applog(LOG_ERR, "%s%i: Comms error (rerr=%d amt=%d)", bmsc->drv->name, bmsc->device_id, err, amount);
			dev_error(bmsc, REASON_DEV_COMMS_ERROR);
			return 0;
		}
		if(amount > 0) {
			readalllen += amount;
			readlen += amount;
			if (readlen >= 5) {
				nonceok = false;

				memcpy((char *) &nonce, nonce_bin, BMSC_READ_SIZE);
				noncedup = false;
				for(i = 0; i < BMSC_NONCE_ARRAY_SIZE; i++) {
					if(memcmp(nonce_bin, info->nonce_bin[i], BMSC_READ_SIZE) == 0) {
						noncedup = true;
						break;
					}
				}
				if(!noncedup) {
					if(info->nonce_index < 0 || info->nonce_index >= BMSC_NONCE_ARRAY_SIZE)
						info->nonce_index = 0;

					memcpy(info->nonce_bin[info->nonce_index], nonce_bin, BMSC_READ_SIZE);
					info->nonce_index++;

					nonce = htobe32(nonce);
					nofull = 0;
					if (submit_nonce_1(thr, work, nonce, &nofull)) {
						applog(LOG_DEBUG, "Bmsc nonce(0x%08x) match current work", nonce);
						submit_nonce_2(work);
						nonceok = true;
					} else {
						if(!nofull) {
							if (info->work_queue != NULL) {
								nofull = 0;
								if (submit_nonce_1(thr, info->work_queue, nonce, &nofull)) {
									applog(LOG_DEBUG, "Bmsc nonce(0x%08x) match old work", nonce);
									submit_nonce_2(info->work_queue);
									nonceok = true;
								} else {
									if(!nofull) {
										applog(LOG_DEBUG, "Bmsc nonce(0x%08x) not match work", nonce);
										usb_buffer_clear(bmsc);
										inc_hw_errors(thr);
										break;
									} else {
										nofullcount++;
									}
								}
							} else {
								applog(LOG_DEBUG, "Bmsc nonce(0x%08x) no old work", nonce);
							}
						} else {
							nofullcount++;
						}
					}
				} else {
					applog(LOG_DEBUG, "Bmsc nonce duplication");
				}

				if(nonceok) {
					count++;
					hash_count = (nonce & info->nonce_mask);
					hash_count++;
					hash_count *= info->fpga_count;
					hash_done += 0xffffffff;//hash_count;

					applog(LOG_DEBUG, "%s%d: nonce = 0x%08x = 0x%08lX hashes (%ld.%06lds)",
					bmsc->drv->name, bmsc->device_id, nonce, (long unsigned int )hash_count, elapsed.tv_sec, elapsed.tv_usec);
				}
				readlen = 0;
			}
		} else {
			applog(LOG_DEBUG, "bmsc_scanhash usb_read_once_timeout read time out");
		}

		read_time = SECTOMS(tdiff(&tv_finish, &tv_start));
		if(read_time >= info->read_time) {
			if (readalllen > 0)
				applog(LOG_DEBUG, "Bmsc Read: Nonce ok:%d below:%d in %d ms", count, nofullcount, read_time);
			else
				applog(LOG_DEBUG, "Bmsc Read: No nonce work %d for %d ms", work->id, read_time);

			break;
		}
	}

	if(info->work_queue != NULL) {
		free_work(info->work_queue);
		info->work_queue = NULL;
	}

	info->work_queue = copy_work(work);

	applog(LOG_DEBUG, "bmsc_scanhash stop ------------");
out:
	free_work(work);
	return hash_count;
}*/

static struct api_data *bmsc_api_stats(struct cgpu_info *cgpu)
{
	struct api_data *root = NULL;
	struct BMSC_INFO *info = (struct BMSC_INFO *)(cgpu->device_data);

	// Warning, access to these is not locked - but we don't really
	// care since hashing performance is way more important than
	// locking access to displaying API debug 'stats'
	// If locking becomes an issue for any of them, use copy_data=true also
	root = api_add_int(root, "read_time", &(info->read_time), false);
	root = api_add_int(root, "read_time_limit", &(info->read_time_limit), false);
	root = api_add_double(root, "fullnonce", &(info->fullnonce), false);
	root = api_add_int(root, "count", &(info->count), false);
	root = api_add_hs(root, "Hs", &(info->Hs), false);
	root = api_add_double(root, "W", &(info->W), false);
	root = api_add_uint(root, "total_values", &(info->values), false);
	root = api_add_uint64(root, "range", &(info->hash_count_range), false);
	root = api_add_uint64(root, "history_count", &(info->history_count), false);
	root = api_add_timeval(root, "history_time", &(info->history_time), false);
	root = api_add_uint(root, "min_data_count", &(info->min_data_count), false);
	root = api_add_uint(root, "timing_values", &(info->history[0].values), false);
	root = api_add_const(root, "timing_mode", timing_mode_str(info->timing_mode), false);
	root = api_add_bool(root, "is_timing", &(info->do_bmsc_timing), false);
	root = api_add_int(root, "baud", &(info->baud), false);
	root = api_add_int(root, "work_division", &(info->work_division), false);
	root = api_add_int(root, "fpga_count", &(info->fpga_count), false);

	return root;
}

static void bmsc_statline_before(char *buf, size_t bufsiz, struct cgpu_info *cgpu)
{
	struct BMSC_INFO *info = (struct BMSC_INFO *)(cgpu->device_data);

	if (info->ident == IDENT_CMR2 && info->cmr2_speed > 0)
		tailsprintf(buf, bufsiz, "%5.1fMhz", (float)(info->cmr2_speed) * BMSC_CMR2_SPEED_FACTOR);
	else
		tailsprintf(buf, bufsiz, "       ");

	tailsprintf(buf, bufsiz, "        | ");
}

static void bmsc_shutdown(__maybe_unused struct thr_info *thr)
{
	// TODO: ?
}

static void bmsc_identify(struct cgpu_info *cgpu)
{
	struct BMSC_INFO *info = (struct BMSC_INFO *)(cgpu->device_data);

	if (info->ident == IDENT_CMR2)
		info->flash_next_work = true;
}

static char *bmsc_set(struct cgpu_info *cgpu, char *option, char *setting, char *replybuf)
{
	struct BMSC_INFO *info = (struct BMSC_INFO *)(cgpu->device_data);
	int val;

	if (info->ident != IDENT_CMR2) {
		strcpy(replybuf, "no set options available");
		return replybuf;
	}

	if (strcasecmp(option, "help") == 0) {
		sprintf(replybuf, "clock: range %d-%d",
				  BMSC_CMR2_SPEED_MIN_INT, BMSC_CMR2_SPEED_MAX_INT);
		return replybuf;
	}

	if (strcasecmp(option, "clock") == 0) {
		if (!setting || !*setting) {
			sprintf(replybuf, "missing clock setting");
			return replybuf;
		}

		val = atoi(setting);
		if (val < BMSC_CMR2_SPEED_MIN_INT || val > BMSC_CMR2_SPEED_MAX_INT) {
			sprintf(replybuf, "invalid clock: '%s' valid range %d-%d",
					  setting,
					  BMSC_CMR2_SPEED_MIN_INT,
					  BMSC_CMR2_SPEED_MAX_INT);
		}

		info->cmr2_speed = CMR2_INT_TO_SPEED(val);
		info->speed_next_work = true;

		return NULL;
	}

	sprintf(replybuf, "Unknown option: %s", option);
	return replybuf;
}

struct device_drv bmsc_drv = {
	.drv_id = DRIVER_bmsc,
	.dname = "Bitmain",
	.name = "BTM",
	.drv_detect = bmsc_detect,
	.hash_work = &hash_driver_work,
	.get_api_stats = bmsc_api_stats,
	.get_statline_before = bmsc_statline_before,
	.set_device = bmsc_set,
	.identify_device = bmsc_identify,
	.thread_prepare = bmsc_prepare,
	.scanwork = bmsc_scanwork,
	.thread_shutdown = bmsc_shutdown,
};
