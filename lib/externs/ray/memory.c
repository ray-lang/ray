#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "gc.h"
#include "memory.h"
#include "rayarray.h"
#include "raybool.h"
#include "rayint.h"
#include "raystring.h"

void *ray_addrof(ray_object_t *obj) {
    if (ray_is_raw_type(obj->encoded_type)) {
        // unbox the raw value
        return obj->value;
    }
    // otherwise this is just a noop
    return obj;
}

/** stdlib.RawPointer **/

void *ray_rawptr_addint(void *self, intptr_t other) {
    return self + other;
}

ray_bool_t ray_rawptr_eq(void *self, void *other) {
    return self == other;
}

ray_bool_t ray_rawptr_neq(void *self, void *other) {
    return self != other;
}

ray_bool_t ray_rawptr_is_nil(void *self) {
    return self == 0;
}

void *ray_rawptr_get(void **self, intptr_t offset) {
    return self[offset];
}

void ray_rawptr_set(void **self, intptr_t offset, void *value) {
    self[offset] = value;
}

uint8_t ray_rawptr_get_byte(uint8_t *self, intptr_t offset) {
    return self[offset];
}

void ray_rawptr_set_byte(uint8_t *self, intptr_t offset, uint8_t byte) {
    self[offset] = byte;
}

ray_object_t *ray_rawptr_get_bytes(uint8_t *self, uintptr_t count) {
    ray_ty_path_t *path = __ray_array_path();
    char *enc_ti = ray_encode_ty_info(path, "stdlib.Array<UInt8>");
    ray_free_path(path);
    ray_object_t *arr = ray_array_new(count, enc_ti, 1);
    INCREF(arr); // need to incref otherwise it will be decrefed and freed after a set
    for (int i = 0; i < count; i++) {
        ray_object_t *b = ray_uint8_from_raw(self[i]);
        ray_array_set(arr, i, b);
    }
    return arr;
}

void ray_rawptr_set_bytes(uint8_t *self, intptr_t offset, ray_object_t *byte_arr) {
    INCREF(byte_arr);
    uintptr_t len = ray_array_len(byte_arr);
    uint8_t *ptr = self + offset;
    for (int i = 0; i < len; i++) {
        ray_object_t *b = ray_array_get(byte_arr, i);
        ptr[i] = ray_uint8_to_raw(b);
    }
    DECREF(byte_arr);
}

uintptr_t ray_rawptr_to_int(void *ptr) {
    return (uintptr_t)ptr;
}

ray_object_t *ray_rawptr_hex(void *self) {
    uintptr_t val = (uintptr_t)self;
    int length = snprintf(NULL, 0, "%lx", val); // length of the string
    char* str = malloc(length + 1); // malloc the string
    snprintf(str, length + 1, "%lx", val); // create the formatted string
    ray_object_t *str_obj = ray_string_from_raw("stdlib.String", str); // convert to ray object
    free(str); // free the str because we created a copy of str above
    return str_obj;
}
