#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "hash.h"
#include "helpers.h"
#include "raybool.h"
#include "typeinfo.h"

void ray_free_pair(ray_ty_pair_t *pair) {
    ray_free_path(pair->path);
    free(pair->name);
    free(pair);
}

void ray_free_path(ray_ty_path_t *path) {
    if (path->module != NULL) {
        char **m = path->module;
        while (*m != NULL) {
            free(*m);
            m++;
        }
        free(path->module);
    }

    if (path->scope != NULL) {
        char **s = path->scope;
        while (*s != NULL) {
            free(*s);
            s++;
        }
        free(path->scope);
    }

    free(path->name);
    free(path);
}

ray_ty_path_t *ray_decode_ty_path(const char *ty_info) {
    ray_ty_path_t *path = malloc(sizeof(ray_ty_path_t));
    char *enc_ty_path = strdup(ty_info);
    char *curr_str = enc_ty_path;
    char *module_parts = strsep(&curr_str, "#");
    char *scope_parts = strsep(&curr_str, "#");
    path->name = strdup(strsep(&curr_str, "#"));
    path->has_impl = strcmp(strsep(&curr_str, "#"), "1");
    path->is_static = strcmp(strsep(&curr_str, "#"), "1");
    path->module = get_parts(&module_parts, ".");
    path->scope = get_parts(&scope_parts, ".");
    free(enc_ty_path);
    return path;
}

ray_ty_pair_t *ray_decode_ty_info(const char *str) {
    char *s = strdup(str);
    char *curr = s;
    char *path_str = strsep(&curr, ";");
    char *ty_name = strsep(&curr, ";");

    ray_ty_pair_t *pair = malloc(sizeof(ray_ty_pair_t));
    pair->path = ray_decode_ty_path(path_str);
    pair->name = strdup(ty_name);

    free(s);
    return pair;
}

char *ray_encode_ty_path(ray_ty_path_t *ty_path) {
    char *mod = strjoin(ty_path->module, ".");
    char *scope = strjoin(ty_path->scope, ".");

    char *buf = calloc(1024, sizeof(char));
    sprintf(buf, "%s#%d#%s#%d#%s", mod, ty_path->has_impl, scope, ty_path->is_static, ty_path->name);

    char *out = malloc(strlen(buf)*sizeof(char));
    strcpy(out, buf);

    free(mod);
    free(scope);
    free(buf);
    return out;
}

char *ray_encode_ty_info(ray_ty_path_t *path, char *ty_name) {
    char *enc_ty_path = ray_encode_ty_path(path);
    char buf[1024];
    for (int i = 0; i < 1024; i++) {
        buf[i] = '\0';
    }
    sprintf(buf, "%s;%s", enc_ty_path, ty_name);
    char *out = malloc(strlen(buf)*sizeof(char));
    strcpy(out, buf);
    free(enc_ty_path);
    return out;
}

ray_bool_t ray_is_raw_type(const char *enc_ti) {
    ray_ty_pair_t *pair = ray_decode_ty_info(enc_ti);
    ray_bool_t is_raw =
        strncmp(pair->name, "Bool", 4) == 0 ||
        strncmp(pair->name, "Int8", 4) == 0 ||
        strncmp(pair->name, "Int16", 5) == 0 ||
        strncmp(pair->name, "Int32", 5) == 0 ||
        strncmp(pair->name, "Int64", 5) == 0 ||
        strncmp(pair->name, "UInt8", 4) == 0 ||
        strncmp(pair->name, "UInt16", 5) == 0 ||
        strncmp(pair->name, "UInt32", 5) == 0 ||
        strncmp(pair->name, "UInt64", 5) == 0 ||
        strncmp(pair->name, "RawString", 9) == 0 ||
        strncmp(pair->name, "RawArray", 8) == 0 ||
        strncmp(pair->name, "RawPointer", 10) == 0;
    ray_free_pair(pair);
    return is_raw;
}
