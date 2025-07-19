# 5 Lemmas and Proofs

The thinking and debugging you do when proving a lemma is the same as when proving programs correct. Therefore, practicing the skills of writing proofs gives you the chops to reason about more difficult programs. When you're comfortable writing proofs, you'll be able to think about the interesting aspects of your programs instead of spending your time wondering how to diagnose failed proof attempts.

## 5.0 Declaring a Lemma
```
function More(x: int): int {
    if x <= 0 then 1 else More(x - 2) + 3
}

lemma Increasing(x: int)
  ensures x < More(x)
```

## 5.1 Using a Lemma

```
method ExampleLemmaUse(a: int) {
    var b := More(a);
    var c := More(b);
    assert 2 <= c - a;
}
```

## 5.2 Proving a Lemma

```
lemma {:induction false} Increasing(x: int)
  ensures x < More(x)
{
  if x <= 0 {
  } else {
    Increasing(x-2); // this call gives us: x-2 < More(x-2)
  }
}
```

```
lemma {:induction false} Increasing1(x: int)
  ensures x < More(x)
{
  if 0 < x  {
    var y := x - 2;
    Increasing(y);
  }
}
```

## 5.3 Back to Basics

Step 1
```
lemma {:induction false} Increasing(x: int)
  ensures x < More(x)
{
  {{ true }}
  ?
  {{ x < More(x) >}}
}
```
Step 2
```
lemma {:induction false} Increasing(x: int)
  ensures x < More(x)
{
  {{ true }}
  if x <= 0 {
    {{ x <= 0 }}
    ?
    {{ x < More(x) }}
  } else {
    {{ x}}

  }
  {{ x < More(x) >}}
}
```