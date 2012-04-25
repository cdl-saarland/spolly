int c;

void f() {
  int i;
  int c_tmp = c;
  for (i = 0; i < 1024; i++) {
    if (c != c_tmp) 
      signalNonInvariancy();
    // function g may change c
    A[i] = g() + c; 
  }
}
