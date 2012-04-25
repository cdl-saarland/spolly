#define N 1024

#ifdef I1
  #include "matmul1.c"
  #define ARGS  
  extern float A[N][N], B[N][N], C[N][N];
#endif
#ifdef I2
  #include "matmul2.c"
  #define ARGS A, B, C
  float A[N][N], B[N][N], C[N][N];
#endif
#ifdef I3
  #include "matmul3.c"
  #define ARGS &A, &B, &C
  float A[N * N], B[N * N], C[N * N];
#endif


void init_arrays(float A[N][N], float B[N][N], float C[N][N]) {
    int i, j;

    for (i=0; i<N; i++) {
        for (j=0; j<N; j++) {
            A[i][j] = (1+(i*j)%1024)/2.0;
            B[i][j] = (1+(i*j)%1024)/2.0;
            C[i][j] = 0;
        }
    }
}

double sum_array(float C[N][N]) {
    double sum = 0.0;
    int i, j;

    for (i=0; i<N; i++) {
        for (j=0; j<N; j++) {
          sum += C[i][j];
        }
    }

    return sum;
}

int main() {
    double sum;
    
    int i;
    for (i = 0; i < 10; i++) {
      init_arrays(A, B, C);
      matmul(ARGS);
      sum = sum_array(C);
     
      if (sum != 69920704991472.0)
        return 1;
    }

    return 0;
}
