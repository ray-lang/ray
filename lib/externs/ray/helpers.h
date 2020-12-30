#ifndef _HELPERS_H
#define _HELPERS_H

char **get_parts(char **str, const char *delim);
char *strjoin(char **strings, const char *sep);
void ray_panic(const char *restrict fmt, ...);

#endif
