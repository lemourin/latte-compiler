#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void printInt(int n) { printf("%d\n", n); }

void printHex(int n) { printf("%x\n", n); }

void printString(const char* str) { printf("%s\n", str ? str : ""); }

void error() {
  printf("runtime error\n");
  exit(0);
}

int readInt() {
  int n;
  scanf("%d\n", &n);
  return n;
}

const char* readString() {
  char* line;
  size_t n = 0;
  ssize_t result = getline(&line, &n, stdin);
  if (result <= 0)
    return NULL;
  else {
    if (line[result - 1] == '\n')
      line[result - 1] = '\0';
    return line;
  }
}

const char* concatenate(const char* str1, const char* str2) {
  if (!str1 && !str2)
    return NULL;
  else if (!str1)
    return str2;
  else if (!str2)
    return str1;
  char* result = malloc(strlen(str1) + strlen(str2) + 1);
  *result = 0;
  strcat(result, str1);
  strcat(result, str2);
  return result;
}
