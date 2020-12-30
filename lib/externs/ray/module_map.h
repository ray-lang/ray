#ifndef _MODULE_MAP_H
#define _MODULE_MAP_H

#include <inttypes.h>
#include "structs.h"

typedef struct ray_modvar_t {
    uint32_t hash;
    void *value;
} ray_modvar_t;

typedef struct ray_mod_t {
    uint32_t hash;
    uint32_t varcount;
    ray_modvar_t **vars;
} ray_mod_t;

typedef struct ray_modmap_t {
    uint32_t size;
    ray_mod_t **modules;
} ray_modmap_t;

extern ray_modmap_t *__module_map;

ray_modmap_t *__ray_new_modmap(uint32_t size);
ray_mod_t *__ray_new_mod(uint32_t mod_hash, uint32_t varcount);
ray_modvar_t *__ray_new_modvar(uint32_t var_hash, void *value);
void *__ray_modvar(uint32_t mod_hash, uint32_t var_hash);

#endif
