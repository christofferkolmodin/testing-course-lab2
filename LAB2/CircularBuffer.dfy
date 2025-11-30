// class CircularMemory
// This class implements a cicular buffer with with 2 int typed pointers
class CircularMemory
{
  var cells : array<int>;
  var read_position : int;
  var write_position : int;
  var isFlipped : bool;

  constructor Init(cap : int) {...}
  predicate Valid() {...}

  method Read() returns (isSuccess : bool, content : int)
    modifies this
    requires Valid()
    ensures  Valid()
    ensures  isSuccess ==> ...
    ensures !isSuccess ==> ...

  {
    if(isFlipped)
    {
      ...
    }
    else // not flipped
    {
      ...
    }
  }

  method Write(input : int) returns (isSuccess : bool)
    modifies this
    requires Valid()
    ensures  Valid()
    ensures  isSuccess ==> ...
    ensures !isSuccess ==> ...
  {
    if(isFlipped)
    {
      ...
    }
    else // not flipped
    {
      ...
    }
  }


}
