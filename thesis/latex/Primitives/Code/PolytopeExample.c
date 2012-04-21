
void f(float A[1024][1024]) {
  int i,j;
  
  for (i = 1; i < 1024; i++) {
    for (j = 1; j < 1024; j++) {
      A[i][j] = A[i][j+1] * A[i][j - 1];
    }
  }
}
