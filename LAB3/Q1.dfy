
/* 
Question 1a:
    Dafny gives the error "This postcondition might not hold on a return path."
    for the postcondition a > b.

    This error is given because when x == y, the else-branch will be entered
    and a and b will be assigned the same value, which breaks the postcondition.
*/

/* 
Question 1b:
    Q: true
    S: if   x > y
       then a := x; b := y
       else a := y; b := x
    R: a > b

    B (guard)        :  x > y
    S1 (then-branch) : a := x; b := y
    S2 (else-branch) : a := y;   b := x
    R (postcondition): a > b

    For then-branch S1:
      S11: a := x
      S12: b := y

      Using sequential rule:
      wp(S1​1; S12​, R) = wp(S11​, wp(S12​, R))

      wp(a:=x; b:=y, a>b) = wp(a:=x, wp(b:=y, a>b))

      Inner wp:
      wp(b:=y, a>b)

      By the assignment rule:
      a>y

      So outer wp can be rewritten:
      wp(a:=x, a>y)

      By the assignment rule:
      x>y

      So,
      
      wp(S1, R) = x>y


    For else-branch:
      S21: a := y
      S22: b := x

      Using sequential rule:
      wp(S21​; S22​, R) = wp(S21​, wp(S22​, R))

      wp(a:=y; b:=x, a>b) = wp(a:=y, wp(b:=x, a>b))

      Inner wp:
        wp(b:=x, a>b)

        Assignment rule:
        a>x

      Outer wp rewritten:
         wp(a:=y, a>x)
      
        Assignment rule:
        y>x


      Whole statement:
        With:
          S1: a := x; b := y
          S2: a := y; b := x

      wp(if (x>y) then S1 else S2, a > b) =

      wp(S,R) = ( (x>y -> wp(S1,R)) ∧ (¬(x>y) -> wp(S2,R)) )
              = ( (x>y -> x>y)      ∧ (¬(x>y) -> (y>x))    )

	​    (x>y -> x>y) is trivially true, so the whole thing evaluates to
      wp(S,R) = ( ¬(x>y) -> y>x )

      with ¬(x>y) being the same as (x <= y)

      So,
      (x <= y) -> y>x

      With no precondition and therefore Q = true,
      Q -> wp(S,R) = true -> (x <= y) -> (y>x)

                   = (x <= y) -> (y>x)

      Counter example:

        With x = 1, y = 1
        (x <= y) = true
        (y>x)    = false

      So wp(S,R) fails and there is no precondition Q for which
      the implementation fulfills the postcondition a > b

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