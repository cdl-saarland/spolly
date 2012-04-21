void f() {
  int i;
  for (i = B; i < E - N + 1; i += S * N) {
    LoopNest(i + 0 * S);
    ...
    LoopNest(i + N * S);
  }
  // Remaining iterations
  for (int j = i; j < E; j += S) {
    LoopNest(j);
  }
}
