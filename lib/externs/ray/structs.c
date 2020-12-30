#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "externs.h"
#include "gc.h"
#include "hash.h"
#include "helpers.h"
#include "memory.h"
#include "rayint.h"
#include "raystring.h"
#include "structs.h"
#include "typeinfo.h"

ray_object_t *__ray_make_struct(void *value, const char *enc_ty_info, void (*deinit)(const char*, ray_object_t*)) {
    ray_object_t *obj = malloc(sizeof(ray_object_t));
    obj->value = value;
    obj->encoded_type = strdup(enc_ty_info);
    obj->refcount = 0;
    obj->deinit = deinit;
    return obj;
}

ray_object_t *ray_make_struct(void *value, const char *ti, void (*deinit)(const char*, ray_object_t*)) {
    ray_ty_pair_t *pair = ray_decode_ty_info(ti);
    ray_object_t *obj = __ray_make_struct(value, ti, deinit);
    ray_free_pair(pair);
    return obj;
}

void ray_struct_free(ray_object_t *obj) {
    free(obj->encoded_type);
    free(obj);
}

void ray_object_deinit(const char *ti, ray_object_t *obj) {
    // this is a "generic" deinit for boxed raw values
    free(obj->value);
    ray_struct_free(obj);
}

void __ray_make_struct_field(void *rawlist, const char *key, void *value, int field_idx) {
    uintptr_t key_idx = 2*field_idx;
    uintptr_t val_idx = 2*field_idx + 1;
    uint32_t *key_hash = malloc(sizeof(uint32_t));
    *key_hash = ray_hash(key);
    ray_rawlist_set(rawlist, key_idx, key_hash);
    ray_rawlist_set(rawlist, val_idx, value);
}

void *__ray_make_fields(ray_field_pair_t **fields, uintptr_t field_count) {
    // each element is a key-value pair
    void *rawlist = ray_rawlist_new(field_count * 2);

    for (int i = 0; i < field_count; i++) {
        ray_field_pair_t *pair = fields[i];
        __ray_make_struct_field(rawlist, pair->key, pair->value, i);
    }
    return rawlist;
}

void *__ray_get_struct_field(ray_object_t *obj, uint32_t field_hash) {
    void *fields = obj->value;
    uintptr_t len = ray_rawlist_len(fields);
    for (int i = 0; i < len; i++) {
        uint32_t **elptr = (uint32_t**)ray_rawlist_getelptr(fields, 2*i);
        if (elptr == 0) {
            return 0;
        }

        uint32_t h = **elptr;
        if (h == field_hash) {
            return ray_rawlist_getelptr(fields, 2*i + 1);
        }
    }
    return 0;
}

ray_object_t *ray_typestring(ray_object_t *obj) {
    ray_ty_pair_t *pair = ray_decode_ty_info(obj->encoded_type);
    ray_ty_path_t *ty_path = pair->path;
    char *mod = strjoin(ty_path->module, ".");
    char *scope = strjoin(ty_path->scope, ".");
    char *buf = calloc(1024, sizeof(char));
    sprintf(buf, "%s.%s.%s", mod, scope, ty_path->name);

    char *out = malloc(strlen(buf) * sizeof(char));
    strcpy(out, buf);

    free(buf);
    free(mod);
    free(scope);
    ray_free_pair(pair);

    ray_object_t *str = ray_string_from_raw("stdlib.String", out);
    free(out);
    return str;
}
