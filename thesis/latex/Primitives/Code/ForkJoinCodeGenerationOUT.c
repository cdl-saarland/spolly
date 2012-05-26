void f() {
  int i;
  for (i = Lb; i < Ub - N + 1;
       i += Str * N) {
    LoopNest(i + 0 * Str);
    ...
    LoopNest(i + N * Str);
  }
  // Remaining iterations
  for (int j = i; j < Ub; j += Str) {
    LoopNest(j);
  }
}
