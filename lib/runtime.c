#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_LENGTH 100

void printInt(int n) {
  printf("%d\n", n);
}

void printString(const char* str) {
  printf("%s\n", str);
}

void error() {
  printf("runtime error\n");
  exit(0);
}

int readInt() {
  int n;
  scanf("%d", &n);
  return n;
}

const char* readString() {
  char* result = malloc(MAX_LENGTH);
  scanf("%s", result);
  return result;
}

const char* concatenate(const char* str1, const char* str2) {
  char* result = malloc(strlen(str1) + strlen(str2) + 1);
  *result = 0;
  strcat(result, str1);
  strcat(result, str2);
  return result;
}
