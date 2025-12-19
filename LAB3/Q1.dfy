
/* 
Question 1a:
    Dafny gives the error "This postcondition might not hold on a return path."
    for the postcondition a > b.

    This error is given because when x == y, the else-branch will be entered
    and a and b will be assigned the same value, which breaks the postcondition.
*/


method M(x : int, y : int) returns (a : int, b : int) 
  ensures a > b
{
  if (x > y)
   {a:= x;
    b := y;}
  else
   {a := y; 
    b := x;}
}