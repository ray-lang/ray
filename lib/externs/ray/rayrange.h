#ifndef _RAYRANGE_H
#define _RAYRANGE_H

#include "raybool.h"
#include "structs.h"

void ray_range_deinit(const char *_ti, ray_object_t *rng);
ray_object_t *ray_range_start(ray_object_t *rng);
ray_object_t *ray_range_end(ray_object_t *rng);
ray_bool_t ray_range_is_inclusive(ray_object_t *rng);

#endif
