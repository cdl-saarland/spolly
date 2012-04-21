
for (i = 2; i < 1024; i++) {
  if (cond(i)) 
    A[i] += A[i-1] * A[i-2];
  else 
    A[i] -= A[i-1];
}
