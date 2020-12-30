#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "rayint.h"
#include "raystring.h"
#include "externs.h"

ray_ty_path_t *__ray_int_path(char *name) {
    ray_ty_path_t *path = malloc(sizeof(ray_ty_path_t));
    path->name = name;
    path->scope = malloc(sizeof(char*));
    path->scope[0] = 0; // no scope
    path->module = malloc(sizeof(char*)*2);
    path->module[0] = strdup("stdlib");
    path->module[1] = 0;
    path->has_impl = 0;
    path->is_static = 0;
    return path;
}

// NOTE: this can be used on an Int of any size
void ray_int_deinit(const char *_ti, ray_object_t *obj) {
    free(obj->value);
    ray_struct_free(obj);
}

/** Int **/

ray_object_t *ray_int_from_raw(intptr_t value) {
    // alloc the int value on the value on the heap
    intptr_t *value_ptr = malloc(sizeof(intptr_t));
    *value_ptr = value;

    // make type path for Int
    ray_ty_path_t *path = __ray_int_path("Int");

    // encode type info
    char *enc_ty_info = ray_encode_ty_info(path, "stdlib::Int");

    // make the struct
    return __ray_make_struct(value_ptr, enc_ty_info, ray_int_deinit);
}

intptr_t ray_int_to_raw(ray_object_t *obj) {
    return *(intptr_t*)obj->value;
}

ray_object_t *ray_int_to_string(ray_object_t *obj) {
    intptr_t val = *(intptr_t*)obj->value;
    int length = snprintf(NULL, 0, "%ld", val); // length of the string
    char* str = malloc(length + 1); // malloc the string
    snprintf(str, length + 1, "%ld", val); // create the formatted string
    ray_object_t *str_obj = ray_string_from_raw("stdlib::String", str); // convert to ray object
    free(str); // free the str because we created a copy of str above
    return str_obj;
}

ray_object_t *ray_int_hex(ray_object_t *obj) {
    intptr_t val = *(intptr_t*)obj->value;
    int length = snprintf(NULL, 0, "%lx", val); // length of the string
    char* str = malloc(length + 1); // malloc the string
    snprintf(str, length + 1, "%lx", val); // create the formatted string
    ray_object_t *str_obj = ray_string_from_raw("stdlib::String", str); // convert to ray object
    free(str); // free the str because we created a copy of str above
    return str_obj;
}

/** Int8 **/

ray_object_t *ray_int8_from_raw(int8_t value) {
    // alloc the int value on the value on the heap
    int8_t *value_ptr = malloc(sizeof(int8_t));
    *value_ptr = value;

    // make type path for Int8
    ray_ty_path_t *path = __ray_int_path("Int8");

    // encode type info
    char *enc_ty_info = ray_encode_ty_info(path, "stdlib::Int8");

    // make the struct
    return __ray_make_struct(value_ptr, enc_ty_info, ray_int_deinit);
}

int8_t ray_int8_to_raw(ray_object_t *obj) {
    return *(int8_t*)obj->value;
}

ray_object_t *ray_int8_to_string(ray_object_t *obj) {
    int8_t val = *(int8_t*)obj->value;
    int length = snprintf(NULL, 0, "%d", val); // length of the string
    char* str = malloc(length + 1); // malloc the string
    snprintf(str, length + 1, "%d", val); // create the formatted string
    ray_object_t *str_obj = ray_string_from_raw("stdlib::String", str); // convert to ray object
    free(str); // free the str because we created a copy of str above
    return str_obj;
}

ray_object_t *ray_int8_hex(ray_object_t *obj) {
    int8_t val = *(int8_t*)obj->value;
    int length = snprintf(NULL, 0, "%d", val); // length of the string
    char* str = malloc(length + 1); // malloc the string
    snprintf(str, length + 1, "%d", val); // create the formatted string
    ray_object_t *str_obj = ray_string_from_raw("stdlib::String", str); // convert to ray object
    free(str); // free the str because we created a copy of str above
    return str_obj;
}

/** Int16 **/

ray_object_t *ray_int16_from_raw(int16_t value) {
    // alloc the int value on the value on the heap
    int16_t *value_ptr = malloc(sizeof(int16_t));
    *value_ptr = value;

    // make type path for Int16
    ray_ty_path_t *path = __ray_int_path("Int16");

    // encode type info
    char *enc_ty_info = ray_encode_ty_info(path, "stdlib::Int16");

    // make the struct
    return __ray_make_struct(value_ptr, enc_ty_info, ray_int_deinit);
}

int16_t ray_int16_to_raw(ray_object_t *obj) {
    return *(int16_t*)obj->value;
}

ray_object_t *ray_int16_to_string(ray_object_t *obj) {
    int16_t val = *(int16_t*)obj->value;
    int length = snprintf(NULL, 0, "%d", val); // length of the string
    char* str = malloc(length + 1); // malloc the string
    snprintf(str, length + 1, "%d", val); // create the formatted string
    ray_object_t *str_obj = ray_string_from_raw("stdlib::String", str); // convert to ray object
    free(str); // free the str because we created a copy of str above
    return str_obj;
}

ray_object_t *ray_int16_hex(ray_object_t *obj) {
    int16_t val = *(int16_t*)obj->value;
    int length = snprintf(NULL, 0, "%d", val); // length of the string
    char* str = malloc(length + 1); // malloc the string
    snprintf(str, length + 1, "%d", val); // create the formatted string
    ray_object_t *str_obj = ray_string_from_raw("stdlib::String", str); // convert to ray object
    free(str); // free the str because we created a copy of str above
    return str_obj;
}

/** Int32 **/

ray_object_t *ray_int32_from_raw(int32_t value) {
    // alloc the int value on the value on the heap
    int32_t *value_ptr = malloc(sizeof(int32_t));
    *value_ptr = value;

    // make type path for Int32
    ray_ty_path_t *path = __ray_int_path("Int32");

    // encode type info
    char *enc_ty_info = ray_encode_ty_info(path, "stdlib::Int32");

    // make the struct
    return __ray_make_struct(value_ptr, enc_ty_info, ray_int_deinit);
}

int32_t ray_int32_to_raw(ray_object_t *obj) {
    return *(int32_t*)obj->value;
}

ray_object_t *ray_int32_to_string(ray_object_t *obj) {
    int32_t val = *(int32_t*)obj->value;
    int length = snprintf(NULL, 0, "%d", val); // length of the string
    char* str = malloc(length + 1); // malloc the string
    snprintf(str, length + 1, "%d", val); // create the formatted string
    ray_object_t *str_obj = ray_string_from_raw("stdlib::String", str); // convert to ray object
    free(str); // free the str because we created a copy of str above
    return str_obj;
}

ray_object_t *ray_int32_hex(ray_object_t *obj) {
    int32_t val = *(int32_t*)obj->value;
    int length = snprintf(NULL, 0, "%d", val); // length of the string
    char* str = malloc(length + 1); // malloc the string
    snprintf(str, length + 1, "%d", val); // create the formatted string
    ray_object_t *str_obj = ray_string_from_raw("stdlib::String", str); // convert to ray object
    free(str); // free the str because we created a copy of str above
    return str_obj;
}

/** Int64 **/

ray_object_t *ray_int64_from_raw(int64_t value) {
    // alloc the int value on the value on the heap
    int64_t *value_ptr = malloc(sizeof(int64_t));
    *value_ptr = value;

    // make type path for Int64
    ray_ty_path_t *path = __ray_int_path("Int64");

    // encode type info
    char *enc_ty_info = ray_encode_ty_info(path, "stdlib::Int64");

    // make the struct
    return __ray_make_struct(value_ptr, enc_ty_info, ray_int_deinit);
}

int64_t ray_int64_to_raw(ray_object_t *obj) {
    return *(int64_t*)obj->value;
}

ray_object_t *ray_int64_to_string(ray_object_t *obj) {
    int64_t val = *(int64_t*)obj->value;
    int length = snprintf(NULL, 0, "%lld", val); // length of the string
    char* str = malloc(length + 1); // malloc the string
    snprintf(str, length + 1, "%lld", val); // create the formatted string
    ray_object_t *str_obj = ray_string_from_raw("stdlib::String", str); // convert to ray object
    free(str); // free the str because we created a copy of str above
    return str_obj;
}

ray_object_t *ray_int64_hex(ray_object_t *obj) {
    int64_t val = *(int64_t*)obj->value;
    int length = snprintf(NULL, 0, "%llx", val); // length of the string
    char* str = malloc(length + 1); // malloc the string
    snprintf(str, length + 1, "%llx", val); // create the formatted string
    ray_object_t *str_obj = ray_string_from_raw("stdlib::String", str); // convert to ray object
    free(str); // free the str because we created a copy of str above
    return str_obj;
}

/** UInt **/

ray_object_t *ray_uint_from_raw(uintptr_t value) {
    // alloc the int value on the value on the heap
    uintptr_t *value_ptr = malloc(sizeof(uintptr_t));
    *value_ptr = value;

    // make type path for UInt
    ray_ty_path_t *path = __ray_int_path("UInt");

    // encode type info
    char *enc_ty_info = ray_encode_ty_info(path, "stdlib::UInt");

    // make the struct
    return __ray_make_struct(value_ptr, enc_ty_info, ray_int_deinit);
}

uintptr_t ray_uint_to_raw(ray_object_t *obj) {
    return *(uintptr_t*)obj->value;
}

ray_object_t *ray_uint_to_string(ray_object_t *obj) {
    uintptr_t val = *(uintptr_t*)obj->value;
    int length = snprintf(NULL, 0, "%lu", val); // length of the string
    char* str = malloc(length + 1); // malloc the string
    snprintf(str, length + 1, "%lu", val); // create the formatted string
    ray_object_t *str_obj = ray_string_from_raw("stdlib::String", str); // convert to ray object
    free(str); // free the str because we created a copy of str above
    return str_obj;
}

ray_object_t *ray_uint_hex(ray_object_t *obj) {
    uintptr_t val = *(uintptr_t*)obj->value;
    int length = snprintf(NULL, 0, "%lx", val); // length of the string
    char* str = malloc(length + 1); // malloc the string
    snprintf(str, length + 1, "%lx", val); // create the formatted string
    ray_object_t *str_obj = ray_string_from_raw("stdlib::String", str); // convert to ray object
    free(str); // free the str because we created a copy of str above
    return str_obj;
}

/** UInt8 **/

ray_object_t *ray_uint8_from_raw(uint8_t value) {
    // alloc the int value on the value on the heap
    uint8_t *value_ptr = malloc(sizeof(uint8_t));
    *value_ptr = value;

    // make type path for UInt8
    ray_ty_path_t *path = __ray_int_path("UInt8");

    // encode type info
    char *enc_ty_info = ray_encode_ty_info(path, "stdlib::UInt8");

    // make the struct
    return __ray_make_struct(value_ptr, enc_ty_info, ray_int_deinit);
}

uint8_t ray_uint8_to_raw(ray_object_t *obj) {
    return *(uint8_t*)obj->value;
}

ray_object_t *ray_uint8_to_string(ray_object_t *obj) {
    uint8_t val = *(uint8_t*)obj->value;
    int length = snprintf(NULL, 0, "%d", val); // length of the string
    char* str = malloc(length + 1); // malloc the string
    snprintf(str, length + 1, "%d", val); // create the formatted string
    ray_object_t *str_obj = ray_string_from_raw("stdlib::String", str); // convert to ray object
    free(str); // free the str because we created a copy of str above
    return str_obj;
}

ray_object_t *ray_uint8_hex(ray_object_t *obj) {
    uint8_t val = *(uint8_t*)obj->value;
    int length = snprintf(NULL, 0, "%d", val); // length of the string
    char* str = malloc(length + 1); // malloc the string
    snprintf(str, length + 1, "%d", val); // create the formatted string
    ray_object_t *str_obj = ray_string_from_raw("stdlib::String", str); // convert to ray object
    free(str); // free the str because we created a copy of str above
    return str_obj;
}

/** UInt16 **/

ray_object_t *ray_uint16_from_raw(uint16_t value) {
    // alloc the int value on the value on the heap
    uint16_t *value_ptr = malloc(sizeof(uint16_t));
    *value_ptr = value;

    // make type path for UInt16
    ray_ty_path_t *path = __ray_int_path("UInt16");

    // encode type info
    char *enc_ty_info = ray_encode_ty_info(path, "stdlib::UInt16");

    // make the struct
    return __ray_make_struct(value_ptr, enc_ty_info, ray_int_deinit);
}

uint16_t ray_uint16_to_raw(ray_object_t *obj) {
    return *(uint16_t*)obj->value;
}

ray_object_t *ray_uint16_to_string(ray_object_t *obj) {
    uint16_t val = *(uint16_t*)obj->value;
    int length = snprintf(NULL, 0, "%d", val); // length of the string
    char* str = malloc(length + 1); // malloc the string
    snprintf(str, length + 1, "%d", val); // create the formatted string
    ray_object_t *str_obj = ray_string_from_raw("stdlib::String", str); // convert to ray object
    free(str); // free the str because we created a copy of str above
    return str_obj;
}

ray_object_t *ray_uint16_hex(ray_object_t *obj) {
    uint16_t val = *(uint16_t*)obj->value;
    int length = snprintf(NULL, 0, "%d", val); // length of the string
    char* str = malloc(length + 1); // malloc the string
    snprintf(str, length + 1, "%d", val); // create the formatted string
    ray_object_t *str_obj = ray_string_from_raw("stdlib::String", str); // convert to ray object
    free(str); // free the str because we created a copy of str above
    return str_obj;
}

/** UInt32 **/

ray_object_t *ray_uint32_from_raw(uint32_t value) {
    // alloc the int value on the value on the heap
    uint32_t *value_ptr = malloc(sizeof(uint32_t));
    *value_ptr = value;

    // make type path for UInt32
    ray_ty_path_t *path = __ray_int_path("UInt32");

    // encode type info
    char *enc_ty_info = ray_encode_ty_info(path, "stdlib::UInt32");

    // make the struct
    return __ray_make_struct(value_ptr, enc_ty_info, ray_int_deinit);
}

uint32_t ray_uint32_to_raw(ray_object_t *obj) {
    return *(uint32_t*)obj->value;
}

ray_object_t *ray_uint32_to_string(ray_object_t *obj) {
    uint32_t val = *(uint32_t*)obj->value;
    int length = snprintf(NULL, 0, "%d", val); // length of the string
    char* str = malloc(length + 1); // malloc the string
    snprintf(str, length + 1, "%d", val); // create the formatted string
    ray_object_t *str_obj = ray_string_from_raw("stdlib::String", str); // convert to ray object
    free(str); // free the str because we created a copy of str above
    return str_obj;
}

ray_object_t *ray_uint32_hex(ray_object_t *obj) {
    uint32_t val = *(uint32_t*)obj->value;
    int length = snprintf(NULL, 0, "%d", val); // length of the string
    char* str = malloc(length + 1); // malloc the string
    snprintf(str, length + 1, "%d", val); // create the formatted string
    ray_object_t *str_obj = ray_string_from_raw("stdlib::String", str); // convert to ray object
    free(str); // free the str because we created a copy of str above
    return str_obj;
}

/** UInt64 **/

ray_object_t *ray_uint64_from_raw(uint64_t value) {
    // alloc the int value on the value on the heap
    uint64_t *value_ptr = malloc(sizeof(uint64_t));
    *value_ptr = value;

    // make type path for UInt64
    ray_ty_path_t *path = __ray_int_path("UInt64");

    // encode type info
    char *enc_ty_info = ray_encode_ty_info(path, "stdlib::UInt64");

    // make the struct
    return __ray_make_struct(value_ptr, enc_ty_info, ray_int_deinit);
}

uint64_t ray_uint64_to_raw(ray_object_t *obj) {
    return *(uint64_t*)obj->value;
}

ray_object_t *ray_uint64_to_string(ray_object_t *obj) {
    uint64_t val = *(uint64_t*)obj->value;
    int length = snprintf(NULL, 0, "%llu", val); // length of the string
    char* str = malloc(length + 1); // malloc the string
    snprintf(str, length + 1, "%llu", val); // create the formatted string
    ray_object_t *str_obj = ray_string_from_raw("stdlib::String", str); // convert to ray object
    free(str); // free the str because we created a copy of str above
    return str_obj;
}

ray_object_t *ray_uint64_hex(ray_object_t *obj) {
    uint64_t val = *(uint64_t*)obj->value;
    int length = snprintf(NULL, 0, "%llx", val); // length of the string
    char* str = malloc(length + 1); // malloc the string
    snprintf(str, length + 1, "%llx", val); // create the formatted string
    ray_object_t *str_obj = ray_string_from_raw("stdlib::String", str); // convert to ray object
    free(str); // free the str because we created a copy of str above
    return str_obj;
}

