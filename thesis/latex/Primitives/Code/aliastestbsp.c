for (i = 0; i < N; i++) {
  for (j = 0; j < N; j++) {
//  I1
    C[i][j] = 0;
    for (k = 0; k < N; k++) {
//    I2         I3        I4
      C[i][j] += A[i][k] * B[k][j];
    }
  }
}
