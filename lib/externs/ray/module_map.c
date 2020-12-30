#include <stdlib.h>
#include <stdio.h>
#include "module_map.h"

ray_modmap_t *__ray_new_modmap(uint32_t size) {
    ray_modmap_t *modmap = malloc(sizeof(ray_modmap_t));
    modmap->size = size;
    modmap->modules = malloc(size * sizeof(ray_mod_t*));
    return modmap;
}

ray_mod_t *__ray_new_mod(uint32_t mod_hash, uint32_t varcount) {
    ray_mod_t *mod = malloc(sizeof(ray_mod_t));
    mod->hash = mod_hash;
    mod->varcount = varcount;
    mod->vars = malloc(varcount * sizeof(ray_modvar_t*));
    return mod;
}

ray_modvar_t *__ray_new_modvar(uint32_t var_hash, void *value) {
    ray_modvar_t *var = malloc(sizeof(ray_modvar_t));
    var->hash = var_hash;
    var->value = value;
    return var;
}

void *__ray_modvar(uint32_t mod_hash, uint32_t var_hash) {
    int size = __module_map->size;
    for (int i = 0; i < size; i++) {
        ray_mod_t *mod = __module_map->modules[i];
        if (mod_hash == mod->hash) {
            if (mod->varcount == 0) {
                // module has no variables
                break;
            }

            // found module, look through vars
            ray_modvar_t **vars = mod->vars;
            for (int j = 0; j <= mod->varcount; j++) {
                // skip one for the count
                ray_modvar_t *var = vars[j];
                if (var_hash == var->hash) {
                    return var->value;
                }
            }
        }
    }

    // TODO: Let callee handle this error case
    // fprintf(stderr, "Could not find variable with hash %#x in module %#x\n", var_hash, mod_hash);
    exit(-1);
}
