for (c1=-128;c1<=98;c1+=32) {
  for (c2=max(0,-32*floord(c1,32)-32);c2<=min(98,-c1+98);c2+=32) {
    for (c3=max(max(-98,c1),-c2-31);c3<=min(c1+31,-c2+98);c3++) {
      for (c4=max(c2,-c3);c4<=min(min(98,c2+31),-c3+98);c4++) {
        A[c3+c4+1][c4+1] = A[c3+c4][c4] * B[c3+c4][c4+1];
      }
    }
  }
}

