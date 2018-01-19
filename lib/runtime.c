#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef void (*destructor)(void*);

struct __attribute__((__packed__)) string {
  ssize_t ref_count_;
  destructor release_;
  char* data_;
};

struct __attribute__((__packed__)) array {
  ssize_t ref_count_;
  destructor release_;
  size_t* data_;
  size_t length_;
};

void increase_refcount(void* f) {
  if (f) {
    //printf("increase refcount %p\n", f);
    *(ssize_t*)f += 1;
  }
}

void decrease_refcount(void* f) {
  if (f) {
    *(ssize_t*)f -= 1;
    //printf("decrease refcount %p\n", f);
    if (*(ssize_t*)f <= 0) {
      intptr_t func = *(intptr_t*)(f + sizeof(ssize_t));
      ((destructor)func)(f);
    }
  }
}

void printInt(int n) { printf("%d\n", n); }

void printHex(int n) { printf("%x\n", n); }

void printString(struct string* str) {
  printf("%s\n", str ? str->data_ : "");
  decrease_refcount(str);
}

void error() {
  printf("runtime error\n");
  exit(0);
}

int readInt() {
  int n;
  scanf("%d\n", &n);
  return n;
}

void string_free(void* d) {
  struct string* r = (struct string*)d;
  free(r->data_);
  r->data_ = NULL;
  free(r);
  //printf("~string() %p\n", d);
}

struct string* string_new(const char* str) {
  struct string* r = malloc(sizeof(struct string));
  r->ref_count_ = 1;
  r->release_ = string_free;
  r->data_ = strdup(str);
  //printf("created string %p\n", r);
  return r;
}

void array_free(void* d) {
  struct array* r = (struct array*)d;
  free(r->data_);
  r->data_ = NULL;
  free(r);
  //printf("~array() %p\n", d);
}

void array_object_free(void* d) {
  struct array* r = (struct array*)d;
  for (size_t i = 0; i < r->length_; i++) {
    decrease_refcount((void*)(r->data_[i]));
  }
  free(r->data_);
  r->data_ = NULL;
  free(r);
  //printf("~array_object() %p\n", d);
}

struct array* array_new(size_t length) {
  struct array* r = malloc(sizeof(struct array));
  r->ref_count_ = 1;
  r->release_ = array_free;
  r->data_ = malloc(length * sizeof(size_t));
  r->length_ = length;
  memset(r->data_, 0, length * sizeof(size_t));
  return r;
}

struct array* array_object_new(size_t length) {
  struct array* r = array_new(length);
  r->release_ = array_object_free;
  return r;
}

void* array_get(struct array* array, size_t idx) {
  //decrease_refcount(array);
  //printf("gettingarray %p, %lu\n", array, array->ref_count_);
  return array->data_ + idx;
}

struct string* readString() {
  char* line;
  size_t n = 0;
  ssize_t result = getline(&line, &n, stdin);
  if (result <= 0)
    return NULL;
  else {
    if (line[result - 1] == '\n') line[result - 1] = '\0';
    struct string* result = string_new(line);
    free(line);
    return result;
  }
}

struct string* string_concatenate(struct string* str1, struct string* str2) {
  //printf("concatenating %p %p\n", str1, str2);
  struct string* ret;
  if (!str1 && !str2) {
    ret = NULL;
    goto cleanup;
  } else if (!str1) {
    ret = str2;
    goto cleanup;
  } else if (!str2) {
    ret = str1;
    goto cleanup;
  }
  char* result = malloc(strlen(str1->data_) + strlen(str2->data_) + 1);
  *result = 0;
  strcat(result, str1->data_);
  strcat(result, str2->data_);
  ret = string_new(result);
  free(result);

cleanup:
  decrease_refcount(str1);
  decrease_refcount(str2);
  return ret;
}
