#ifndef __NBIS_H__
#define __NBIS_H__

#include <stdint.h>

extern void nbis_restrict(int cond);
extern void nbis_assert(int cond);

extern int64_t  nbis_nondet_i64(void);
extern uint64_t nbis_nondet_u64(void);
extern int32_t  nbis_nondet_i32(void);
extern uint32_t nbis_nondet_u32(void);
extern int16_t  nbis_nondet_i16(void);
extern uint16_t nbis_nondet_u16(void);
extern int8_t   nbis_nondet_i8(void);
extern uint8_t  nbis_nondet_u8(void);

extern void nbis_watch(int num,...);

#endif
