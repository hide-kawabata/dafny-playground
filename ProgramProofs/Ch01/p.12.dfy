method Triple(x: int) returns (r: int) 
    ensures r == 3 * x
{
        var y := 2 * x;
        r := x + y;
        assert r == 3 * x;
}

//method Caller() {
//    var t := Triple(18);
//    assert t < 100;
//}