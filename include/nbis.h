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
extern unsigned int nbis_nondet_uint(void) __attribute__((pure));
extern char nbis_nondet_char(void) __attribute__((pure));
extern unsigned char nbis_nondet_uchar(void) __attribute__((pure));
extern long nbis_nondet_long(void) __attribute__((pure));
extern unsigned long nbis_nondet_ulong(void) __attribute__((pure));
extern short nbis_nondet_short(void) __attribute__((pure));
extern unsigned short nbis_nondet_ushort(void) __attribute__((pure));

extern void nbis_watch(int num,...);

#endif
