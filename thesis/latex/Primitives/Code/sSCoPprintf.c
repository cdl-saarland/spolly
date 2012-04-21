for (i = 0; i < N; i ++) { 
  if (A[i] == 0) 
    printf("Unlikely error!");
  else 
    A[i] = 1024 / A[i] ;
}
