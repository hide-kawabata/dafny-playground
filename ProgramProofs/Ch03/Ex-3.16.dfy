// `StudyPlan` calls `Learn`: 40 - n > 40 - n, h
// `Learn` calls `StudyPlan`: 40 - n, h > 40 - (n + 1)
// `Learn` calls `Learn`: 40 - n, h > 40 - n, h - 1

method StudyPlan(n: nat)
  requires n <= 40
//  decreases 40 - n
  // decreases (40 - n)*2 + 1, 0
  decreases 40 - n, 1, 0
{
  if n == 40 {
    // done
  } else {
    var hours := RequiredStudyTime(n);
    Learn(n, hours);
  }
}

method Learn(n: nat, h: nat)
  requires n < 40
//  decreases 40 - n, h
  // decreases (40 - n)*2, h
  decreases 40 - n, 0, h
{
  if h == 0 {
    StudyPlan(n + 1);
  } else {
    Learn(n, h - 1);
  }
}

method RequiredStudyTime(c: nat) returns (hours: nat)