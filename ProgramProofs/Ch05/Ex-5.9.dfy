function Mult(x: nat, y: nat): nat 
//    decreases x, y
    decreases x + y
{
    if y == 0 then 0 else x + Mult(x, y - 1)
}


// the proof may be simplified when you make the most use of the termination metric of Mult.

lemma {:induction false} MultCommutative(x: nat, y: nat)
    ensures Mult(x, y) == Mult(y, x)
{
    if x == 0 && y == 0 {
        calc {
            Mult(x, y); // LHS
        ==  0;
        ==  Mult(y, x); // RHS
        }
    } else if x == 0 && y > 0 {
        calc {
            Mult(0, y); // LHS
        ==  0 + Mult(0, y - 1); // def of Mult
        ==  { MultCommutative(0, y-1); }
            Mult(y - 1, 0);
        ==  0;
        ==  Mult(y, 0); // RHS
        }

    } else if x > 0 && y == 0 {
        calc {
            Mult(x, 0); // RHS
        ==  0;
        ==  Mult(x - 1, 0);
        ==  { MultCommutative(0, x - 1); }
            Mult(0, x - 1);
        ==  0 + Mult(0, x - 1);
        ==  Mult(0, x); // LHS
        }
    } else {
        calc {
            Mult(x, y); // LHS
        ==  x + Mult(x, y - 1); // def of Mult
        ==  { MultCommutative(x, y - 1); }
            x + Mult(y - 1, x);
        ==  x + y - 1 + Mult(y - 1, x - 1); // unfold Mult
        ==  { MultCommutative(x - 1, y - 1); }
            x + y - 1 + Mult(x - 1, y - 1);
        ==  y + Mult(x - 1, y); // fold mult
        ==  { MultCommutative(x - 1, y); }
            y + Mult(y, x - 1);
        ==  Mult(y, x); // def of Mult
        }
    }
}