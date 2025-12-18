//We define the mathematical factorial as a recursive function.
//Because the program assumes n > 0, we define factorial only for positive naturals.
function fact(n: nat): nat
  //matches the method’s precondition:
  requires n > 0;
  //ensures termination of the recursive definition:
  decreases n;
{
  if n == 1 then 1 else n * fact(n - 1)
}


method ComputeFact(n : nat) returns (res : nat)
  requires n > 0;
  ensures res == fact(n);
 {
  res := 1;
  var i := 2;
  while (i <= n) 
    //The key idea of the loop is: After processing numbers 2 .. i-1, res equals (i-1)!.
    // So the invariant is:
    invariant res == fact(i - 1)
    //We also need bounds on i:
    invariant 2 <= i <= n + 1
    //The loop variant is:
    decreases n - i + 1
  {
    res := res * i;
    i := i + 1;
  }
 }
