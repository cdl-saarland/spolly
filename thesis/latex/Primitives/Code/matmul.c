#define N 1536

float A[N][N], B[N][N], C[N][N];

void init_arrays(float A[N][N], float B[N][N]) {
    int i, j;

    for (i=0; i<N; i++) {
        for (j=0; j<N; j++) {
            A[i][j] = (1+(i*j)%1024)/2.0;
            B[i][j] = (1+(i*j)%1024)/2.0;
        }
    }
}

void multiply_arrays(float A[N][N], float B[N][N], float C[N][N]) {
    int i, j, k;

    for(i=0; i<N; i++)  {
        for(j=0; j<N; j++)  {
            C[i][j] = 0;
            for(k=0; k<N; k++)
                C[i][j] = C[i][j] + A[i][k] * B[k][j];
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
    double sum_no_alias, sum_alias;

    init_arrays(A, B);
    multiply_arrays(A, B, C);
    sum_no_alias = sum_array(C);
     
    init_arrays(A, A);
    multiply_arrays(A, A, C);
    sum_alias = sum_array(C);

    return sum_no_alias != sum_alias;
}
