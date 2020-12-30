#ifndef _RAYSTRING_H
#define _RAYSTRING_H

#include "structs.h"

extern void ray_string_deinit(const char *, ray_object_t *);
extern ray_object_t *ray_string_from_raw(const char *, char *);
extern char *ray_string_to_raw(ray_object_t *);
extern ray_object_t *ray_string_to_bytes(ray_object_t *);
extern intptr_t ray_string_len(ray_object_t *);

#endif
