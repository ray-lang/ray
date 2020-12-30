#ifndef _RAYDICT_H
#define _RAYDICT_H

#include "structs.h"

ray_object_t *ray_dict_get(ray_object_t *dict, ray_object_t *key);
void ray_dict_set(ray_object_t *dict, ray_object_t *key, ray_object_t *value);

#endif
