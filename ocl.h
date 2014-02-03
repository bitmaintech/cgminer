#ifndef __OCL_H__
#define __OCL_H__

#include "config.h"

#include <stdbool.h>
#define MAXTHREADS (0xFFFFFFFEULL)
#define MAXBUFFERS (0x10)
#define BUFFERSIZE (sizeof(uint32_t) * MAXBUFFERS)
#define FOUND (0x0F)

#define SCRYPT_MAXBUFFERS (0x100)
#define SCRYPT_BUFFERSIZE (sizeof(uint32_t) * SCRYPT_MAXBUFFERS)
#define SCRYPT_FOUND (0xFF)

#ifdef HAVE_OPENCL
#ifdef __APPLE_CC__
#include <OpenCL/opencl.h>
#else
#include <CL/cl.h>
#endif

#include "miner.h"

typedef struct {
	cl_context context;
	cl_kernel kernel;
	cl_command_queue commandQueue;
	cl_program program;
	cl_mem outputBuffer;
#ifdef USE_SCRYPT
	cl_mem CLbuffer0;
	cl_mem padbuffer8;
	size_t padbufsize;
	void * cldata;
#endif
	bool hasBitAlign;
	bool hasOpenCL11plus;
	bool hasOpenCL12plus;
	bool goffset;
	cl_uint vwidth;
	size_t max_work_size;
	size_t wsize;
	enum cl_kernels chosen_kernel;
} _clState;

extern char *file_contents(const char *filename, int *length);
extern int clDevicesNum(void);
extern _clState *initCl(unsigned int gpu, char *name, size_t nameSize);

extern void precalc_hash(dev_blk_ctx *blk, uint32_t *state, uint32_t *data);
extern void postcalc_hash_async(struct thr_info *thr, struct work *work, uint32_t *res);

#endif /* HAVE_OPENCL */
#endif /* __OCL_H__ */
