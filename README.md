

## EE 546 Final Project: Mathematical Cryptography

Textbook: <br />
*An Introduction to Mathematical Cryptography (Second Edition)* <br />
*by: Jeffrey Hoffstein Jill Pipher Joseph H. Silverman*<br />
[[link]](https://link-springer-com.offcampus.lib.washington.edu/book/10.1007/978-1-4939-1711-2)

Project by:<br />
Henry Do, Alexey Yermakov<br />
University of Washington<br />
Department of Electrical and Computer Engineering<br />
Winter 2025
<br />

## Introduction

Number theory is the "study of the properties of whole numbers" [[Wolfram Mathworld]](https://mathworld.wolfram.com/NumberTheory.html) (sometimes defined for integers). Cryptography is the "methodology of concealing the content of messages" (Chapter 1).

Number theory is important in modern cryptography due to certain functions/operations in number theory that are easy to compute in one direction, but hard to compute (break) in the other direction.

Examples:
-Discrete logarithm: For a^n mod p, if you know a and a^n mod p, it is difficult to find n. So if n was the "password" (private key) needed to decrypt a message, only the people who know n will know the contents of the message.

-Prime factorization: It's easy to compute the product of two primes, but factoring it back into primes is a difficult problem. So the primes can be used as the keys to encrypt a message.

Cryptography is extremely relevant to the future. One reason is that, at some point, quantum computers will likely break commonly used number theory functions (public key cryptography). Fields such as post-quantum cryptography aim to develop systems resistant against this.

## Overview

Primary contributions:<br />

- Integer Rings
- Proof that the Euclidean Algorithm converges in a finite number of steps (and an implementation of Extended Euclidean Algorithm)
- Multiplicative inverse of integers in a ring
- Chinese remainder theorem algorithm
- \+ Many more additional number theory proofs

## Integer Rings

**Definition of ring of integers modulo m**<br />
ℤ/mℤ = {0, 1, 2, . . ., *m* - 1}<br />
Addition and multiplication are defined as adding or multiplying elements of ℤ/mℤ, dividing them by *m*, and taking the remainder to obtain an element in ℤ/mℤ.<br />
In Lean, Mathlib uses the **Fin n** type, which is a type for a natural number *i* such that *0 ≤ i < n*. In fact, the ring of integers modulo m is called *ZMod m* in Mathlib and is *definitionally equal to* **Fin m** when *m > 0* and *ℤ* when *m = 0*.<br />
We do the same thing:


```hs
import EE546Project.IntRingModM
import EE546Project.Proofs

namespace Temp

-- Integer ring definition (following in the footsteps of Mathlib)
@[simp]
def IntRingModM :  → Type
  | 0 => ℤ
  | n + 1 => Fin (n + 1)

end Temp
```

Our contribution comes from proving *IntRingModM* is a *commutative ring* by using **CommRing.ofMinimalAxioms**. This is proven in Mathlib but is very gross.

```hs
namespace Temp

-- Register IntRingModM m for any m ∈ ℕ as a Commutative Ring
instance {m : ℕ} : CommRing (IntRingModM m) :=
  CommRing.ofMinimalAxioms
    IntRingModM.add_assoc
    IntRingModM.zero_add
    IntRingModM.neg_add_cancel
    IntRingModM.mul_assoc
    IntRingModM.mul_comm
    IntRingModM.one_mul
    IntRingModM.left_distrib

end Temp
```

We also registered addition and multiplication in Lean4 for the *IntRingModM m* definition so that we can use it naturally.

With this machinery, we can now use the **ring** tactic to prove nontrivial relationships:

```hs
-- Example showing how this works for any Commutative Ring
example (R : Type) [CommRing R] (a b : R) : (a + b) ** (a - b) = a^2 - b^2 := by
  ring -- no errors!

-- Example showing how this works for any IntRingModM m
example {m : ℕ} (a b : IntRingModM m) : (a + b) ** (a - b) = a^2 - b^2 := by
  ring -- no errors!
```


## Euclidean Algorithm

**Definition of divides**<br />
Let *a* and *b* be integers with *b* ≠ 0, we say *b* **divides** *a*, or that *a* **is divisible by** *b*, if there is an integer *c* such that *a* = *bc*. We write *b* | *a* to indicate that *b* divides *a*.

**Definition of division with remainder**<br />
Let *a* and *b* be positive integers. Then we say that *a* divided by *b* has quotient *q* and remainder *r* if *a* = *b* · *q* + *r* with 0 ≤ *r* < *b*. The values of *q* and *r* are uniquely determined by *a* and *b*.

**Definition of common divisor and greatest common divisor**<br />
A *common divisor* of two integers *a* and *b* is a positive integer *d* that divides both of them. The *greatest common divisor* of *a* and *b* is the largest positive integer *d* such that *d* | *a* and *d* | *b*. We denote this by *d* = gcd(*a*,*b*).

**Theorem 1.7** (The Euclidean Algorithm)<br />
Let *a* and *b* be positive integers with *a* ≥ *b*. The following algorithm computes gcd(*a*, *b*) in a finite number of steps.<br />
(1) Let *r0* = *a* and *r1* = *b*.<br />
(2) Set *i* = 1.<br />
(3) Divide *ri*−1 by *ri* to get a quotient qi and remainder *ri*+1, *ri*−1 = *ri* · qi + *ri*+1 with 0 ≤ *ri*+1 < *ri*.<br />
(4) If the remainder *ri*+1 = 0, then *ri* = gcd(*a*, *b*) and the algorithm terminates.<br />
(5) Otherwise, *ri*+1 > 0, so set *i* = *i* + 1 and go to Step 3.<br />

*Proof:*<br />
To prove this in Lean4 we just have to define a recursive function. In order to do so, we need to convince Lean that the function eventually terminates. We do this by using the `termination_by` and `decreasing_by` statements, supplying a proof of that the variable supplied in `termination_by` decreases with each iteration.

```hs
namespace Temp

def theorem1_7 (a b : Nat) : Nat :=
  if a = 0 then
    b
  else
    theorem1_7 (b % a) a
  termination_by a
  decreasing_by
    rename_i h
    simp_wf
    apply Nat.mod_lt _ (Nat.zero_lt_of_ne_zero _)
    assumption

end Temp
```

We can then use this to obtain our GCD for any given natural numbers

```hs
#eval theorem1_7 928 24 -- returns 8
```

**Theorem 1.11** (Extended Euclidean Algorithm)<br />
Let *a* and *b* be positive<br />
integers. Then the equation<br />
*au* + *bv* = gcd(*a*, *b*)<br />
always has a solution in integers *u* and *v*.

Intuition for why this works:
1. By definition, gcd(*a*,*b*), divides *a*, and divides *b*.<br />
2. Also, gcd(*a*,*b*) divides the sum of *a* and *b*.<br />
3. More generally, if gcd(*a*,*b*) divides a, then<br />
we must be able to say a × u = gcd(*a*,*b*)<br />
where m is some integer (same can be done for b).<br />
4. Therefore gcd(*a*,*b*) divides a linear integer<br />
combination of *a*,*b* i.e. *au* + *bv*.<br />

*Algorithm*:<br />
```text
1. Set u = 1, g = a, x = 0, and y = b
2. If y = 0, set v = (g − au)/b and return the values (g, u, v)
3. Divide g by y with remainder, g = qy + t, with 0 ≤ t < y
4. Set s = u − qx
5. Set u = x and g = y
6. Set x = s and y = t
7. Go To Step (2)
```

*Proof:*<br />
As before, we define a recursive function and prove that it terminates. This time we are dealing with many more variables internally, so we define a helper function to do the bulk of the work and only return what we're interested in: the GCD, *u*, and *v*.


```hs
namespace Temp

-- Helper for extended euclidean algorithm
def theorem1_11_h (a b: Nat) (u x: Int) (y g : Nat) : (Nat × Int × Int) :=
  if y = 0 then
    ⟨g, u, ((g-a**u)/b)⟩
  else
    let q := g / y
    let t := g % y
    let s := u - q ** x
    let u := x
    let g := y
    let x := s
    let y := t
    theorem1_11_h a b u x y g
  termination_by y
  decreasing_by
    rename_i g_old y_old x_old u_old hx_old
    refine Nat.mod_lt u_old (by exact Nat.zero_lt_of_ne_zero hx_old)

-- Extended Euclidean Algorithm
def theorem1_11 (a b : Nat) : (Nat × Int × Int) :=
  let u := 1
  let g := a
  let x := 0
  let y := b
  theorem1_11_h a b u x y g

end Temp
```

We can then use this to obtain our GCD for any given natural numbers

```hs
#eval theorem1_11 928 24 -- returns (8, -1, 39) as (gcd, u, v)
```

Extending these algorithms from natural numbers to integers is easy, just pass in the absolute value of the integers:

```hs
namespace Temp

-- GCD for integers
def gcd_int (a b : Int) :=
  theorem1_7 a.natAbs b.natAbs

end Temp

#eval gcd_int (928) (-24) -- returns 8
```


**Definition of relatively prime**<br />
Let *a* and *b* be integers. We say that *a* and *b* are relatively prime if gcd(*a*, *b*) = 1.

**Theorem 2.24** (Chinese Remainder Theorem)<br />
Let *m₁*, *m₂*, . . . , *mₖ* be a collection of pairwise relatively prime integers. This means that gcd(*mᵢ*, *mⱼ* ) = 1 for all *i* ≠ *j*. Let *a₁*, *a2*, . . . , *ak* be arbitrary integers. Then the system of simultaneous congruences *x* ≡ *a₁* (mod *m₁*), *x* ≡ *a₂* (mod *m₂*), . . . , *x* ≡ *aₖ* (mod *mₖ*) has a solution *x* = *c*. Further, if *x* = *c* and *x* = *c′* are both solutions, then *c* ≡ *c′* (mod *m₁m₂* · · · *mₖ*).

*Proof:*<br />
There are many ways to prove this. The textbook uses Proposition 1.13, but we were unable to use that to prove this. Instead, we used the Extended Euclidean algorithm for the case of *k=2* for a computational proof. In effect, we define the Chinese Remainder Theorem as an algorithm and compute it. Since it compiles in Lean4 without an error, we have a complete proof.

```hs
namespace Temp

def crt_euclid_2 (a₁ a₂ n₁ n₂: ℤ) : ℤ := by
  obtain ⟨_, m₁, m₂⟩ := ee_int n₁ n₂
  let x := a₁ ** m₂ ** n₂ + a₂ ** m₁ ** n₁
  exact x

end Temp

-- Calculate remainder
#eval crt_euclid_2 2 3 5 7 -- returns 17
```




## Miscellaneous Proofs

**Proposition 1.4**<br />
Let *a*, *b*, *c* ∈ *ℤ* be integers.<br />
(a) If *a* | *b* and *b* | *c*, then *a* | *c*.<br />
(b) If *a* | *b* and *b* | *a*, then *a* = ±*b*.<br />
(c) If *a* | *b* and *a* | *c*, then *a* | (*b* + *c*) and *a* | (*b* − *c*).<br />

**Proposition 1.13**<br />
Let m ≥ 1 be an integer.<br />
(a) If a1 ≡ a2 (mod m) and b1 ≡ b2 (mod m), then<br />
a1 ± b1 ≡ a2 ± b2 (mod m) and a1 · b1 ≡ a2 · b2 (mod m).<br />
(b) Let a be an integer. Then<br />
a · b ≡ 1 (mod m) for some integer b if and only if gcd(a, m)=1.<br />
Further, if a · b1 ≡ a · b2 ≡ 1 (mod m), then b1 ≡ b2 (mod m). We call b<br />
the (multiplicative) inverse of a modulo m.<br />

**Fast Powering Algorithm**<br />
g^A mod N can be computed efficiently by $ a_0^{A_0} a_1^{A_1} ... a_r^{A_r} mod N$
where $A_0$, $A_1$...$A_r$ are the coefficients of the binary expansion of A,
and $a_0 = g$, $a_1 = a_0^2$, $a_2 = a_1^2$ ... $a_r = g^2^r$

## Conclusion

Our goal was to get through the Chinese Remainder Theorem by building up to it in the book. We were able to prove the key theorems leading up to it, but were unable to apply the proof in the book directly. Despite this, we were able to prove a plethora of interesting results in number theory and learned a lot about how to use Lean to prove algorithms as well as theorems. We learned a lot about the principles and underlying mathematics surrounding modular arithmetic and number theory.

From this we learned that Mathlib is quite extensive and is useful when framing a problem around the existing theorems and definitions. However, if you start trying to prove something that is structured entirely differently than what is already in Mathlib, it becomes pretty useless.  It also makes it challenging to simplify these differently-structured proofs to the length of 2-3 lines commonly seen in Mathlib.

Fortunately, number theory is already pretty well implemented, with the primary theorems already formalized. However, these proofs are not easy to understand and often use some pretty advanced mathematical structures to achieve them. For instance, the Chinese Remainder Theorem uses Ideals to prove the theorem for several types of rings. (see *Ideal.quotientInfRingEquivPiQuotient*)

What's left to do is formalize the Chinese Remainder theorem using Proposition 1.13 just as how the book describes it.

