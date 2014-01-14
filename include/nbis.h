#ifndef __NBIS_H__
#define __NBIS_H__

#include <stdint.h>

extern void nbis_restrict(int cond);
extern void nbis_assert(int cond);

extern int64_t  nbis_nondet_i64(void) __attribute__((pure));
extern uint64_t nbis_nondet_u64(void) __attribute__((pure));
extern int32_t  nbis_nondet_i32(void) __attribute__((pure));
extern uint32_t nbis_nondet_u32(void) __attribute__((pure));
extern int16_t  nbis_nondet_i16(void) __attribute__((pure));
extern uint16_t nbis_nondet_u16(void) __attribute__((pure));
extern int8_t   nbis_nondet_i8(void) __attribute__((pure));
extern uint8_t  nbis_nondet_u8(void) __attribute__((pure));

extern int nbis_nondet_int(void) __attribute__((pure));

extern void nbis_watch(int num,...);

#endif
