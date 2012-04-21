void f(int *A, int *B) {
  int i;
  for (i = 0; i < N - 1; i++) {
    A[i+1] = A[i] + B[i];
  }
}
