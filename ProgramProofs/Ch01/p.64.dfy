method BadDouble(x: int) returns (d: int)
  ensures d == 2 * x + 100
{
    var y := BadDouble(x - 1);
    d := y + 200;
}