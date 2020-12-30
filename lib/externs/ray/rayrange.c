#include <stdlib.h>
#include "gc.h"
#include "raybool.h"
#include "rayrange.h"

void ray_range_deinit(const char *_ti, ray_object_t *rng) {
    ray_object_t *start = ray_range_start(rng);
    ray_object_t *end = ray_range_end(rng);
    DECREF(start);
    DECREF(end);
    free(rng->value);
    ray_struct_free(rng);
}

ray_object_t *ray_range_start(ray_object_t *rng) {
    ray_object_t **ptr = (ray_object_t**)rng->value;
    return ptr[0];
}

ray_object_t *ray_range_end(ray_object_t *rng) {
    ray_object_t **ptr = (ray_object_t**)rng->value;
    return ptr[1];
}

ray_bool_t ray_range_is_inclusive(ray_object_t *rng) {
    uint8_t *ptr = (uint8_t*)rng->value + (2 * sizeof(ray_object_t*));
    return *ptr;
}
