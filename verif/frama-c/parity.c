/*@
  requires \valid(t + (0 .. n)) ;
  requires 0 <= n;

  assigns t[0 .. n] ;
  ensures
    \forall integer j ; 0 <= j < n ==> t[j] == j % 2 ;
*/
void parity_reset(int *t, int n) {
  int i;
  /*@
    loop invariant 0 <= i <= n ;
    loop invariant
      \forall integer j ; 0 <= j < i ==>  t[j] == j %2 ;
    loop assigns i, t[0 .. n - 1] ;
    loop variant n-i ;
  */
  for (i = 0; i < n; i++) {
    t[i] = i % 2;
  }
}

