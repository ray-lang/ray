#ifndef _EXTERNS_H
#define _EXTERNS_H

#include "structs.h"

extern void *ray_rawlist_new(uintptr_t count);
extern void ray_rawlist_free(void *rawlist);
extern void **ray_rawlist_getelptr(void *rawlist, intptr_t idx);
extern uintptr_t ray_rawlist_len(void *rawlist);
extern void ray_rawlist_set(void* rawlist, intptr_t idx, void *value);

#endif
