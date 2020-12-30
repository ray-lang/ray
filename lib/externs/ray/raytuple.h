#ifndef _RAYTUPLE_H
#define _RAYTUPLE_H

#include <inttypes.h>
#include "structs.h"

typedef struct ray_tuple_t {
    uintptr_t len;
    ray_object_t **elements;
} ray_tuple_t;

ray_object_t *ray_tuple_init(const char *ti, uintptr_t count);
void ray_tuple_deinit(const char *_ti, ray_object_t *obj);
ray_object_t *ray_tuple_get(ray_object_t *obj, uint32_t idx);
void ray_tuple_set(ray_object_t *obj, uint32_t idx, ray_object_t * val);
ray_object_t *ray_tuple_len(ray_object_t *obj);
ray_object_t *ray_tuple_to_string(ray_object_t *obj);

#endif
