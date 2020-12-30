#ifndef _RAYARRAY_H
#define _RAYARRAY_H

#include "raybool.h"
#include "structs.h"

ray_ty_path_t *__ray_array_path();

ray_object_t *ray_array_new(uintptr_t count, void *enc_ti, ray_bool_t is_raw);

ray_object_t *ray_array_init(const char *enc_ti);
void ray_array_deinit(const char *, ray_object_t *);
ray_object_t *ray_array_reserve(const char*, uintptr_t count);

uintptr_t ray_array_len(ray_object_t *arr);
ray_object_t *ray_array_get(ray_object_t *arr, intptr_t idx);
void ray_array_set(ray_object_t *arr, intptr_t idx, ray_object_t *value);
void ray_array_append(ray_object_t *arr, ray_object_t *value);

#endif
