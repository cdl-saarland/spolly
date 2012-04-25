for (i = 0; i < N; i++) {
  for (j = 0; j < N; j++) {
//   I1
    C[i*N+j] = 0;
    for (k = 0; k < N; k++) {
//      I2         I3         I4
      C[i*N+j] += A[i*N+k] * B[k*N+j];
    }
  }
}
