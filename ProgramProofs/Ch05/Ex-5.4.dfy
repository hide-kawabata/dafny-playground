lemma a(x: int, y: int)
    ensures 5*x - 3*(y+x) == 2*x - 3*y
{
    calc {
        5*x - 3*(y+x);
    ==  5*x - 3*y - 3*x;
    ==  5*x - 3*x - 3*y;
    ==  (5-3)*x - 3*y;
        2*x - 3*y;
    }
}

lemma b(x: int, y: int)
    ensures 2*(x+4*y+7)-10 == 2*x+8*y+4
{
    calc {
        2*(x+4*y+7)-10;
    ==  2*x+2*4*y+2*7-10;
    ==  2*x+8*y+14-10;
    ==  2*x+8*y+4;
    }
}

lemma c(x: int)
    ensures 7*x + 5 < (x+3)*(x+4)
{
    calc {
        (x+3)*(x+4);
    ==  (x+3)*x + (x+3)*4;
    ==  x*x+3*x + 4*x+3*4;
    ==  x*x + (3+4)*x + 12;
    ==  x*x + 7*x + 12;
    >   x*x + 7*x + 5;
    >=  7*x + 5;
    }
}

lemma sample()
{
    // calc {
    //     true;
    // ==> 
    //     false;
    // }   

    assert true ==> false;
}


// assert (A==>B)&&(B==>C)