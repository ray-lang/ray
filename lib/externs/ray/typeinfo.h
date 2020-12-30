#ifndef _TYPEINFO_H
#define _TYPEINFO_H

#include <inttypes.h>
#include "raybool.h"

typedef struct ray_ty_path_t {
    char **module;
    char **scope;
    char *name;
    int has_impl;
    int is_static;
} ray_ty_path_t;

typedef struct ray_ty_pair_t {
    ray_ty_path_t *path;
    char *name;
} ray_ty_pair_t;

void ray_free_pair(ray_ty_pair_t *pair);
void ray_free_path(ray_ty_path_t *path);

ray_ty_pair_t *ray_decode_ty_info(const char *str);
char *ray_encode_ty_info(ray_ty_path_t *path, char *ty_name);

ray_ty_path_t *ray_decode_ty_path(const char *ty_info);
char *ray_encode_ty_path(ray_ty_path_t *ty_path);

ray_bool_t ray_is_raw_type(const char *enc_ti);

#endif
