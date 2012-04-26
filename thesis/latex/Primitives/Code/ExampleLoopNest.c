for (i = 1; i < 100; i++) 
  for (j = 1; j < 100; j++) 
    A[i][j] = A[i-1][j-1] 
              * B[i-1][j];
