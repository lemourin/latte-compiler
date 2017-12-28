#include <stdio.h>
#include <stdlib.h>

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
  return NULL;
}
