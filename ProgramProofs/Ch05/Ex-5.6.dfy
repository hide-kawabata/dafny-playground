function Ack(m: nat, n: nat): nat
  decreases m, n
{
  if m == 0 then
    n + 1
  else if n == 0 then
    Ack(m - 1, 1)
  else
    Ack(m - 1, Ack(m, n - 1))
}

lemma {:induction false} AckN2(n: nat)
    ensures Ack(1, n) == n + 2
{
    if n == 0 {
        calc {
            Ack(1, n);
            Ack(0, 1);
            1+1;
            n+2;
        }
    } else {
        calc {
            Ack(1, n);
            Ack(0, Ack(1, n-1));
            { AckN2(n-1); }
            Ack(0, (n-1)+2);
            Ack(0, n+1);
            (n+1)+1;
            n+2;
        }
    }
}

lemma {:induction false} AckN2'(n: nat)
    ensures Ack(1, n) == n + 2
{
    if n == 0 {
        calc {
            Ack(1, n);
            Ack(0, 1);
            1+1;
            n+2;
        }
    } else {
        calc {
            Ack(1, n);
            Ack(0, Ack(1, n-1));
            Ack(1, n-1) + 1;
            { AckN2'(n-1); }
            (n-1)+2 + 1;
            n+2;
        }
    }
}
