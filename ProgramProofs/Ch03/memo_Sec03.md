# Chapter 3: Recursion and Termination

## 3.0: The Endless Problem

Five programs that demonstrate the need for considering termination.
- Example 1: never terminates
  ```
  method BadDouble(x: int) return (d: int)
    ensures d == 2 * x
  {
    var y := BadDouble(x - 1);
    d := y + 2;
  }
  ```
- Example 2: there are cases that it terminates
  ```
  method PartialId(x: int) returns (y: int)
    ensures y == x
  {
    if x % 2 == 0 {
        y := x;
    } else {
        y := PartialId(x);
    }
  }
  ```
  This program is *partially correct* since every terminating call is correct. Note that the program of Example 1 is also partially correct (you can ensure anything).
    - WP[[S, Q]] = WLP[[S, Q]] && WP[[S, true]] (see Sec. 2.9.0)
- Example 3:
  ```
  method Squarish(x: int, guess: int) returns (y: int)
    ensures x * x == y
  {
    if 
    cases guess == x * x => // good guess!
      y := guess;
    case true =>
      y := Squarish(x, guess - 1);
    case true =>
      y := Squarish(x, guess + 1);
  }
  ```
- Example 4:
  ```
  method Impossible(x: int) returns (y: int)
    ensures y % 2 == 0 && y == 10 * x - 3
  {
    y := Impossible(x);
  }
  ```
- Example 5:
  ```
  function Dubious(): int {
    1 + Dubious()
  }
  ```
The most common way to avoid inconsistently defined functions is to prove that the functions terminate.

## 3.1 Avoiding Infinite Recursion

```
function Fib(n: nat): nat 
  decreases n
{
  if n < 2 then n else Fib(n - 2) + Fib(n - 1)
}
```
Let's decorate each activation record (called a *termination metric*).
- decoration for the caller: n
- decorations for the callees: n-2 and n-1
- Dafny checkes the *proof oblication* `n-2<n` and `n-1<n`.

```
function SeqSum(s: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |s|
  decreases hi - lo
{
  if lo == hi then 0 else s[lo] + SeqSum(s, lo + 1, hi)
}
```
- caller : hi - lo
- callee : hi - (lo + 1)
- Note: the termination metric of the caller must be non-negative.

## 3.2 Well-Founded Relations
* A binary relation `>` is well-founded when the following three conditions hold:
    1. `>` is irreflexive
    2. `>` is transitive
    3. `>` satisfies the *descending chain condition*; the relation has no infinite descending chain.

  A relation that satisfies the first two conditions is called a *strict partial order*.

* Dafny predefines x > y for each type of x and y:
    - `bool` : `x && !y`
        - i.e. `true > false`
    - `int` : `y < x && 0 <= x`
        - the greater one must be non-negative
    - `real` : `y <= x - 1.0 && 0.0 <= x`
    - `set<T>` : `y` is a proper subset of `x`
    - `seq<T>` : `y` is a consecutive proper sub-sequence of `x`
    - inductive datatypes : `y` is structurally included in `x`


## 3.3 Lexicographic Tuples

### 3.3.0 Remaining school work
```
method RequiredStudyTime(c: nat) returns (hours: nat)
```
```
method Study(n: nat, h: nat)
  decreases n, h
{
  if h != 0 {
    Study(n, h - 1);
  } else if n == 0 {
    // graduation
  } else {
    var hours := RequiredStudyTime(n - 1);
    Study(n - 1, hours);
  }
}
```
There are two recursive calls:
- n, h > n, h-1
- n, h > n-1, hours

### 3.3.1 Ackermann
```
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
```

### 3.3.2 Mutually recursive methods
"outer" computation and "inner" computation
```
method StudyPlan(n: nat)
  requires n <= 40
  decreases 40 - n
{
  if n == 40 {
    // done
  } else {
    var hours := RequiredStudyType(n);
    Learn(n, hours);
  }
}

method Learn(n: nat, h: nat)
  requires n < 40
  decreases 40 - n, h
{
  if h == 0 {
    StudyPlan(n + 1);
  } else {
    Learn(n, h - 1);
  }
}
```
- `StudyPlan` calls `Learn`: 40 - n > 40 - n, h
- `Learn` calls `StudyPlan`: 40 - n, h > 40 - (n + 1)
- `Learn` calls `Learn`: 40 - n, h > 40 - n, h - 1


### 3.3.3 Refactor a subcomputation

```
function ExpLess1(n: nat): nat {
    if n == 0 then 0 else 2 * ExpLess1(n - 1) + 1
}
```
Now we refactor it.
```
function ExpLess1(n: nat): nat {
    if n == 0 then0 else ExpLess2(n) + 1
}
function ExpLess2(n: nat): nat
    requires 1 <= n
{
    2 * ExpLess1(n - 1)

}
```
- ExpLess1 -> ExpLess2 : n > n ???
- ExpLess2 -> ExpLess1 : n > n - 1


## 3.4 Default `decreases` in Dafny

## 3.5 Summary

* Notes
- "Proving termination for functions ensures mathematical consistency, but there are ways to ensure mathematical consistency besides termination. For example, ACL2 safely admits tail-recursive functions, whether or not they terminate."