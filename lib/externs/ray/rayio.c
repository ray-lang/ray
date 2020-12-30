#include <stdio.h>
#include <stdlib.h>
#include "hash.h"
#include "gc.h"
#include "rayint.h"
#include "rayio.h"
#include "raystring.h"

ray_object_t *ray_io_open(ray_object_t *path, ray_object_t *mode) {
    // incref the arguments
    INCREF(path, mode);

    // create a file object and get the raw file handle pointer
    ray_object_t *fobj = ray_file_init(path);
    FILE **fileptr = (FILE **)RAY_FIELD(fobj, "handle");

    // get the arguments to fopen and call it
    char *rawpath = ray_string_to_raw(path);
    char *rawmode = ray_string_to_raw(mode);
    *fileptr = fopen(rawpath, rawmode);

    // cleanup and decref arguments
    free(rawpath);
    free(rawmode);
    DECREF(path, mode);
    return fobj;
}

ray_object_t *ray_io_fputs(ray_object_t *fobj, ray_object_t *strobj) {
    // incref the arguments
    INCREF(fobj, strobj);

    // get the raw file handle
    FILE *fileptr = *(FILE **)RAY_FIELD(fobj, "handle");

    // convert the ray string to a c string and write it to the file
    char *rawstr = ray_string_to_raw(strobj);
    int count = fputs(rawstr, fileptr);

    // create the count object from the int
    ray_object_t *intobj = ray_int_from_raw(count);

    // cleanup and decref arguments
    free(rawstr);
    DECREF(fobj, strobj);
    return intobj;
}
