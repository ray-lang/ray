#ifndef _RAYINT_H
#define _RAYINT_H

#include <inttypes.h>
#include "structs.h"

void ray_int_deinit(const char *, ray_object_t*);

// Int
ray_object_t *ray_int_from_raw(intptr_t value);
intptr_t ray_int_to_raw(ray_object_t *obj);
ray_object_t *ray_int_to_string(ray_object_t *obj);
ray_object_t *ray_int_hex(ray_object_t *obj);

// Int8
ray_object_t *ray_int8_from_raw(int8_t value);
int8_t ray_int8_to_raw(ray_object_t *obj);
ray_object_t *ray_int8_to_string(ray_object_t *obj);
ray_object_t *ray_int8_hex(ray_object_t *obj);

// Int16
ray_object_t *ray_int16_from_raw(int16_t value);
int16_t ray_int16_to_raw(ray_object_t *obj);
ray_object_t *ray_int16_to_string(ray_object_t *obj);
ray_object_t *ray_int16_hex(ray_object_t *obj);

// Int32
ray_object_t *ray_int32_from_raw(int32_t value);
int32_t ray_int32_to_raw(ray_object_t *obj);
ray_object_t *ray_int32_to_string(ray_object_t *obj);
ray_object_t *ray_int32_hex(ray_object_t *obj);

// Int64
ray_object_t *ray_int64_from_raw(int64_t value);
int64_t ray_int64_to_raw(ray_object_t *obj);
ray_object_t *ray_int64_to_string(ray_object_t *obj);
ray_object_t *ray_int64_hex(ray_object_t *obj);

// UInt
ray_object_t *ray_uint_from_raw(uintptr_t value);
uintptr_t ray_uint_to_raw(ray_object_t *obj);
ray_object_t *ray_uint_to_string(ray_object_t *obj);
ray_object_t *ray_uint_hex(ray_object_t *obj);

// UInt8
ray_object_t *ray_uint8_from_raw(uint8_t value);
uint8_t ray_uint8_to_raw(ray_object_t *obj);
ray_object_t *ray_uint8_to_string(ray_object_t *obj);
ray_object_t *ray_uint8_hex(ray_object_t *obj);

// UInt16
ray_object_t *ray_uint16_from_raw(uint16_t value);
uint16_t ray_uint16_to_raw(ray_object_t *obj);
ray_object_t *ray_uint16_to_string(ray_object_t *obj);
ray_object_t *ray_uint16_hex(ray_object_t *obj);

// UInt32
ray_object_t *ray_uint32_from_raw(uint32_t value);
uint32_t ray_uint32_to_raw(ray_object_t *obj);
ray_object_t *ray_uint32_to_string(ray_object_t *obj);
ray_object_t *ray_uint32_hex(ray_object_t *obj);

// UInt64
ray_object_t *ray_uint64_from_raw(uint64_t value);
uint64_t ray_uint64_to_raw(ray_object_t *obj);
ray_object_t *ray_uint64_to_string(ray_object_t *obj);
ray_object_t *ray_uint64_hex(ray_object_t *obj);

#endif
