#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void print(const char* s) {
  for (const char* p = s; *p; ++p) {
    putchar(*p);
  }
}

void flush() { fflush(stdout); }

int64_t ord(const char* s) { return (int64_t)s[0]; }

const char* chr(int64_t c) {
  char* r = malloc(2);
  r[0] = c;
  r[1] = '\0';
  return r;
}

const char* getchar2() {
  int ch = getchar();
  return chr(ch);
}

int64_t size(const char* s) {
  const char* p = s;
  while (*p++)
    ;
  return p - s;
}

const char* substring(const char* s, int first, int n) {
  char* r = malloc(n + 1);
  memcpy(r, s + first, n);
  r[n] = '\0';
  return r;
}

const char* concat(const char* a, const char* b) {
  int sa = size(a);
  int sb = size(b);
  char* r = malloc(sa + sb + 1);
  memcpy(r, a, sa);
  memcpy(r + sa, b, sb);
  r[sa + sb] = '\0';
  return r;
}

int64_t not(int64_t x) { return x ? 0 : 1; }

void exit2(int64_t x) { exit(x); }