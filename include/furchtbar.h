#ifndef __FURCHTBAR_H__
#define __FURCHTBAR_H__

#include <stdint.h>

extern void furchtbar_restrict(int cond);
extern void furchtbar_assert(int cond);

extern int64_t  furchtbar_nondet_i64(void);
extern uint64_t furchtbar_nondet_u64(void);
extern int32_t  furchtbar_nondet_i32(void);
extern uint32_t furchtbar_nondet_u32(void);
extern int16_t  furchtbar_nondet_i16(void);
extern uint16_t furchtbar_nondet_u16(void);
extern int8_t   furchtbar_nondet_i8(void);
extern uint8_t  furchtbar_nondet_u8(void);

extern void furchtbar_watch(int num,...);

#endif
