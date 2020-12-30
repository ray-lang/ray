#ifndef _MEMORY_H
#define _MEMORY_H

#include <inttypes.h>
#include "raybool.h"
#include "structs.h"

void *ray_addrof(ray_object_t *obj);

// stdlib.RawPointer
void *ray_rawptr_addint(void*, intptr_t);
ray_bool_t ray_rawptr_eq(void*, void*);
ray_bool_t ray_rawptr_neq(void*, void*);
ray_bool_t ray_rawptr_is_nil(void*);
void *ray_rawptr_get(void**, intptr_t);
void ray_rawptr_set(void**, intptr_t, void*);
uint8_t ray_rawptr_get_byte(uint8_t*, intptr_t);
ray_object_t *ray_rawptr_get_bytes(uint8_t *self, uintptr_t count);
void ray_rawptr_set_byte(uint8_t *self, intptr_t offset, uint8_t byte);
void ray_rawptr_set_bytes(uint8_t *self, intptr_t offset, ray_object_t *byte_arr);
uintptr_t ray_rawptr_to_int(void*);
ray_object_t *ray_rawptr_hex(void *self);

#endif
