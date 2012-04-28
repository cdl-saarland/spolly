// A, B, C may alias
for (i = 0; i < 1024; i++) {
  A[i] = B[i] * C[i];
}
