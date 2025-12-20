// This class implements a cicular buffer with 2 int typed pointers
class CircularMemory
{
  var cells : array<int>;
  var read_position : int;
  var write_position : int;
  var isFlipped : bool;

  constructor Init(cap : int) 
    requires cap > 0
  {
    // Initialize array cells with 0s
    cells := new int[cap] (i => 0);
    read_position, write_position := 0, 0;
    isFlipped := false;
  }

  predicate Valid()
    reads this
  {
    // There is nothing to read or write to if length isnt > 0
    cells.Length > 0 &&
    // Read and write can only have in-bounds indices (0 to cells.length - 1)
    0 <= read_position < cells.Length &&
    0 <= write_position < cells.Length &&

    (!isFlipped ==> write_position >= read_position) &&
    ( isFlipped ==> write_position <= read_position)
  }

  // A predicate indicating no more Read available
  predicate isEmpty()
    reads this
  {
    // This condition indicates the read pointer has read all available data and "caught up" to the writer
    ((read_position == write_position) && !isFlipped)
  }

  // A predicate indicating no more Write should be allowed
  predicate isFull()
    reads this
  {
    // This condition indicates that the write pointer is about to "lap" the reader pointer
    // and no further writing should be allowed to prevent loss of data
    ((read_position == write_position) && isFlipped)
  }

  method Read() returns (isSuccess : bool, content : int)
    modifies this
    requires Valid()
    ensures  Valid()
    // When the read was successful, ensure the returned content is equal to
    // what was stored in the cell which was read
    ensures  isSuccess ==> (content == old(cells[read_position])) &&
                            write_position == old(write_position) &&
                            // Ensure new position is the expected one
                            (if old(read_position) == cells.Length - 1
                              then
                                read_position == 0
                              else
                                read_position == old(read_position) + 1)

    // If there is no data to read (buffer was empty), ensure the dummy value 0 was returned
    // and that the reading index remained unchanged
    ensures !isSuccess ==> (content == 0) &&
                            read_position == old(read_position) &&
                            write_position == old(write_position)

  {
    // The case when there is no data to read
    if ((read_position == write_position) && !isFlipped)
    {
      isSuccess := false;
      content := 0;
    }
    // There is data to read
    else
    {
      isSuccess := true;
      content := cells[read_position];

      // the case when read_position reached the end of the array and wraps to the beginning
      if (read_position == cells.Length - 1)
      {
        read_position := 0;
        isFlipped := !isFlipped;
      }
      else
      {
        read_position := read_position + 1;
      }
    }
  }


  method Write(input : int) returns (isSuccess : bool)
    // The write method modifies object fields but also the cells array
    modifies this, cells
    requires Valid()
    ensures  Valid()
    // Ensure the cells array itself was not reassigned by the write method
    ensures cells == old(cells)
    // When the write was successful, ensure the input value was stored
    // in the cell which was written to
    ensures  isSuccess ==> cells[old(write_position)] == input &&
                            read_position == old(read_position) &&
                            // Ensure new position is the expected one
                            (if old(write_position) == cells.Length - 1
                              then
                                write_position == 0
                              else
                                write_position == old(write_position) + 1)

    // If the write failed (the buffer was full), ensure the write index remained unchanged
    ensures !isSuccess ==> write_position == old(write_position)
    // read position should never be moved by Write 
    ensures read_position == old(read_position)
  {
    // The case when the buffer is full and writing would overwrite existing data
    if ((read_position == write_position) && isFlipped)
    {
      isSuccess := false;
    }
    else
    {
      isSuccess := true;

      cells[write_position] := input;

      // the case when write_position reached the end of the array and wraps to the beginning
      if (write_position == cells.Length - 1)
      {
        write_position := 0;
        isFlipped := !isFlipped;
      }
      else
      {
        write_position := write_position + 1;
      }
    }
  }

  // Question 3 for Lab 3
  method DoubleCapacity()
    modifies this
    requires Valid()
    ensures Valid()
    ensures cells.Length == 2 * old(cells.Length)
    ensures read_position == old(read_position)
    ensures write_position == old(write_position)
    ensures forall j : int :: 0 <= j < old(cells.Length) ==> cells[j] == old(cells[j])
    ensures forall j : int :: old(cells.Length) <= j < cells.Length ==> cells[j] == 0
    {
      
    var oldCells := cells;
    var oldLen := oldCells.Length;

    // Create a new temporary array with double the length of the old one
    var newCells := new int[2 * oldLen](k => 0);

    var i := 0;
    while (i < oldLen)
      invariant 0 <= i <= oldLen
      invariant newCells.Length == 2 * oldLen

      // Ensure positions and the flag is unchanged by the loop
      invariant read_position == old(read_position)
      invariant write_position == old(write_position)
      invariant isFlipped == old(isFlipped)

      // All cells which has already been copied (any cells before index i)
      // hold the same value in oldCells as in the newCells array
      invariant forall j:int :: 0 <= j < i ==> newCells[j] == oldCells[j]

      // All indices from i and onward are still just 0
      invariant forall j:int :: i <= j < newCells.Length ==> newCells[j] == 0

      // Ensures the loop will eventually terminate by verifying that oldLen - i
      // is smaller with each iteration
      decreases oldLen - i
      
      {
        // Copy elements from the old array to the new array
        newCells[i] := oldCells[i];
        i := i + 1;
      }

    // Assign the new double capacity array to cells
    cells := newCells;

  }


}
