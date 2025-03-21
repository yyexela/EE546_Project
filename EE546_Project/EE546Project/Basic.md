

  An Introduction to Mathematical Cryptography
  (Second Edition)

  Jeffrey Hoffstein
  Jill Pipher
  Joseph H. Silverman

  Lean code created by

  Henry Do
  Alexey Yermakov

  Markdown generated using:
  ```bash
  python dm.py ./Basic.lean > Basic.md
  ```


```hs
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Tactic
import Mathlib.Data.Int.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Algebra.Ring.MinimalAxioms
open Classical
```

  Chapter 1: An Introduction to Cryptography

. Prop 1.4 Let a, b, c Γêê Z be integers.
(a) If a | b and b | c, then a | c.
```hs
theorem prop1_4_a {a b c : Γäñ} : a Γêú b ΓåÆ b Γêú c ΓåÆ a Γêú c := by
  intro h1 h2
  exact Int.dvd_trans h1 h2
```
 if ab=1, then a=1 OR a=-1
```hs
-- Not in book
theorem helper_lemma_1 {a b : Γäñ} : 1 = a * b ΓåÆ a = 1 Γê¿ a = -1 := by
  intro h
  exact Int.eq_one_or_neg_one_of_mul_eq_one (id (Eq.symm h))
```
 if ab=1, then a,b=1 OR a,b=-1
```hs
-- Not in book
theorem helper_lemma_2 {a b : Γäñ} : 1 = a * b ΓåÆ (a = 1 Γêº b = 1) Γê¿ (a = -1 Γêº b = -1) := by
  intro h1
  have h2 := helper_lemma_1 h1
  apply Or.elim h2
  . intro h3
    rw[h3] at h1
    simp at h1
    simp_all
  . intro h3
    rw[h3] at h1
    simp at h1
    simp_all

-- (b) If a | b and b | a, then a = ┬▒b.
```
classical not needed, but makes things easier
```hs
theorem prop1_4_b {a b : Γäñ} : a Γêú b ΓåÆ b Γêú a ΓåÆ a = b Γê¿ a = -b := by
  apply Or.elim (Classical.em (a < 0))
  . apply Or.elim (Classical.em (b < 0))
    . intro hb ha hab hba
      have ha : 0 Γëñ -a := by linarith
      have hb : 0 Γëñ -b := by linarith
      have hab : -a Γêú -b := by simp_all
      have hba : -b Γêú -a := by simp_all
      have h1 := Int.dvd_antisymm ha hb hab hba
      have : a = b := by linarith
      left
      exact this
    . intro hb ha hab hba
      have ha : 0 Γëñ -a := by linarith
      have hb : 0 Γëñ b := by linarith
      have hab : -a Γêú b := by simp_all
      have hba : b Γêú -a := by simp_all
      have h1 := Int.dvd_antisymm ha hb hab hba
      have : a = -b := by linarith
      right
      exact this
  . apply Or.elim (Classical.em (b < 0))
    . intro hb ha hab hba
      have ha : 0 Γëñ a := by linarith
      have hb : 0 Γëñ -b := by linarith
      have hab : a Γêú -b := by simp_all
      have hba : -b Γêú a := by simp_all
      have h1 := Int.dvd_antisymm ha hb hab hba
      have : a = -b := by linarith
      right
      exact this
    . intro hb ha hab hba
      have ha : 0 Γëñ a := by linarith
      have hb : 0 Γëñ b := by linarith
      have h1 := Int.dvd_antisymm ha hb hab hba
      have : a = b := by linarith
      left
      exact this

-- (c) If a | b and a | c, then a | (b + c) and a | (b ΓêÆ c).
theorem prop1_4_c {a b c: Γäñ } : a Γêú b ΓåÆ a Γêú c ΓåÆ a Γêú (b+c) Γêº a Γêú (b-c) := by
  intro h1 h2
  exact Γƒ¿ Int.dvd_add h1 h2, Int.dvd_sub h1 h2Γƒ⌐
```

How do you prove a recursive algorithm to converges in LΓêâΓêÇN?
1) Define the algorithm
2) Specify a decreasing value
3) Prove the value decreases each iteration

```hs
def factorial1 (a:Nat) : Nat :=
  if a = 0 then 1
  else
    a * factorial1 (a-1)
  termination_by a
  decreasing_by
    rename_i ha
    exact Nat.sub_one_lt ha

#eval factorial1 4

-- Of course, for this simple example LΓêâΓêÇN can infer that it terminates by the single argument a and it knows that a-1 < a pretty trivially....

def factorial2 (a:Nat) : Nat :=
  if a = 0 then 1
  else
    a * factorial2 (a-1)
  termination_by a

def factorial3 (a:Nat) : Nat :=
  if a = 0 then 1
  else
    a * factorial3 (a-1)

def factorial4 : Nat ΓåÆ Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial4 n
```

So, we return to wanting to prove that we can compute the GCD of two numbers in a finite number of steps, this is called the Euclidean Algorithm

```hs
-- GCD Euclidean Algorithm
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

#eval theorem1_7 93 6
```

There is a more computationally efficient definition for Euclidean's Algorithm that we can implement in lean as well:

Let a and b be positive integers. Then the equation
            au + bv = gcd(a, b)
always has a solution in integers u and v.

```hs
-- Helper for extended euclidean algorithm
def theorem1_11_h (a b: Nat) (u x: Int) (y g : Nat) : (Nat ├ù Int ├ù Int) :=
  if y = 0 then
    Γƒ¿g, u, ((g-a*u)/b)Γƒ⌐
  else
    let q := g / y
    let t := g % y
    let s := u - q * x
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
def theorem1_11 (a b : Nat) : (Nat ├ù Int ├ù Int) :=
  let u := 1
  let g := a
  let x := 0
  let y := b
  theorem1_11_h a b u x y g

#eval theorem1_11 93 6
```

For fun let's check how many times we recursed! Add a counter variable to both functions:

```hs
def gcd_slow_h (a b c : Nat) : Nat ├ù Nat :=
  if a = 0 then
    Γƒ¿b,cΓƒ⌐
  else
    gcd_slow_h (b % a) a (c+1)
  termination_by a
  decreasing_by
    rename_i h
    simp_wf
    apply Nat.mod_lt _ (Nat.zero_lt_of_ne_zero _)
    assumption

def gcd_slow (a b : Nat) : Nat ├ù Nat :=
  gcd_slow_h a b 0

-- Helper for extended euclidean algorithm
def gcd_fast_h (a b: Nat) (u x: Int) (y g c : Nat) : (Nat ├ù Int ├ù Int ├ù Nat) :=
  if y = 0 then
    Γƒ¿g, u, ((g-a*u)/b), cΓƒ⌐
  else
    let q := g / y
    let t := g % y
    let s := u - q * x
    let u := x
    let g := y
    let x := s
    let y := t
    gcd_fast_h a b u x y g c
  termination_by y
  decreasing_by
    rename_i g_old y_old x_old u_old hx_old
    refine Nat.mod_lt u_old (by exact Nat.zero_lt_of_ne_zero hx_old)

-- Extended Euclidean Algorithm
def gcd_fast (a b : Nat) : (Nat ├ù Int ├ù Int ├ù Nat) :=
  let u := 1
  let g := a
  let x := 0
  let y := b
  let c := 0
  gcd_fast_h a b u x y g c

#eval gcd_slow 93 6
#eval gcd_fast 93 6
```

What is the GCD of integers? It's just the GCD of their absolute values..

```hs
def gcd_int (a b : Int) :=
  (gcd_fast a.natAbs b.natAbs).1

#eval gcd_int (93) (6)
#eval gcd_int (93) (-6)
#eval gcd_int (-93) (6)
#eval gcd_int (-93) (-6)

-- Relatively Prime Definition
def rel_prime (a b : Nat) :=
  theorem1_7 a b = 1 -- theorem1_7: GCD

#eval theorem1_7 6 35

theorem rel_prime_ex1 : rel_prime 6 35 := by
  simp[rel_prime, theorem1_7]

#eval theorem1_7 5 35

theorem rel_prime_ex2 : ┬¼ rel_prime 5 35 := by
  simp[rel_prime, theorem1_7]

-- For fun: show that the first 100 numbers are relatively prime to 293 by raw computation using lists
def numbers : List Nat := List.range 101 |>.drop 1
def pairs : List (Nat ├ù Nat) := numbers.map (╬╗ n => (n,293))
def gcds : List Nat := pairs.map (╬╗ ab => theorem1_7 ab.1 ab.2)
def sub1 : List Nat := gcds.map (╬╗ gcd => gcd-1)
def sum := sub1.foldl (╬╗ acc x => acc + x) 0

#eval numbers
#eval pairs
#eval gcds
#eval sub1
#eval sum

-- Definition. Let m ΓëÑ 1 be an integer. We say that the integers a and b are
-- congruent modulo m if their difference a ΓêÆ b is divisible by m. We write
-- a Γëí b (mod m)
-- to indicate that a and b are congruent modulo m. The number m is called the
-- modulus.
def congru_mod (a b m: Γäñ) (h: m ΓëÑ 1) :=
  m Γêú (a-b)

-- Proposition 1.13. Let m ΓëÑ 1 be an integer.
-- (a) If a1 Γëí a2 (mod m) and b1 Γëí b2 (mod m), then
-- a1 ┬▒ b1 Γëí a2 ┬▒ b2 (mod m) and a1 ┬╖ b1 Γëí a2 ┬╖ b2 (mod m).
theorem prop1_13_a (a1 a2 b1 b2 m: Γäñ)
  (h: m ΓëÑ 1)
  (h2: congru_mod a1 a2 m h)
  (h3: congru_mod b1 b2 m h):
  ((congru_mod (a1 + b1) (a2 + b2) m h) Γêº (congru_mod (a1 - b1) (a2 - b2) m h)) Γêº (congru_mod (a1 * b1) (a2 * b2) m h) := by
    simp_all[congru_mod]
    apply And.intro
    . have prop14c := prop1_4_c h2 h3
      have commu_sum : a1 - a2 + (b1 - b2) = a1 + b1 - (a2 + b2) := by ring
      have commu_sum2 : a1 - a2 - (b1 - b2) = a1 - b1 - (a2 - b2) := by ring
      rw[commu_sum,commu_sum2] at prop14c
      exact prop14c
    . exact dvd_mul_sub_mul h2 h3
```
gcd(a,m) divides a*b - c*m (any linear combination of a,m)
```hs
theorem helper_1_13_b (a b c m: Γäñ): (Int.gcd a m) Γêú (a*b - c*m) := by sorry

-- Proposition 1.13. Let m ΓëÑ 1 be an integer.
-- (b) Let a be an integer. Then
-- a ┬╖ b Γëí 1 (mod m) for some integer b if and only if gcd(a, m)=1.

theorem eq_iff_modEq_nat (n : Γäò) {a b : Γäò} : (a : ZMod n) = b Γåö a Γëí b [MOD n] := by
  cases n
  ┬╖ simp [Nat.ModEq, Int.natCast_inj, Nat.mod_zero]
  ┬╖ rw [Fin.ext_iff, Nat.ModEq, \la val_natCast, \la  val_natCast]
    exact Iff.rfl

set_option diagnostics true
theorem prop1_13_b_1 (a b: Γäñ) (m: Γäò) (hm: m ΓëÑ 1) : ((a * b: ZMod m) = 1) Γåö (Int.gcd a b = 1) := by
  apply Iff.intro
  . intro hf
    rw[Int.gcd]
    rw[Nat.gcd]
    if a.natAbs = 0 then
      rename_i ha
      rw[ha]
      simp[Int.natAbs_zero] at ha
      simp[ha] at hf
      by_cases hm1 : m = 1
      . simp
        by_cases hb1 : b > 0
        . sorry
        . sorry
      . sorry
    else sorry
  . sorry

  #eval (1 : ZMod 1)

-- This works

theorem prop1_13_klavins {a b m: Γäñ} : a*b Γëí 1 [ZMOD m] ΓåÆ Int.gcd a m = 1 := by

  intro h
  apply Int.modEq_iff_add_fac.mp at h

  obtain Γƒ¿ k, hk Γƒ⌐ := h

  rw[ΓåInt.isCoprime_iff_gcd_eq_one]

  use b
  use k
  rw[hk]

  ring


-- Here's a helper for for another version of the proof below

theorem helperklavins {d a b : Γäñ} : dΓêúa ΓåÆ dΓêúb ΓåÆ ΓêÇ x y, d Γêú a*x + b*y := by

  intro ha hb x y

  simp[Int.dvd_def] at ha hb

  obtain Γƒ¿ k, hk Γƒ⌐ := ha
  obtain Γƒ¿ j, hj Γƒ⌐ := hb

  rw[hk,hj]

  have : d * k * x + d * j * y = d*(k*x+j*y) := by ring

  rw[this]

  exact Int.dvd_mul_right d (k * x + j * y)


theorem prop1_13_klavins_2 {a b m: Γäñ} : a*b Γëí 1 [ZMOD m] ΓåÆ gcd a m = 1 := by

  intro h

  have h' := Int.modEq_iff_add_fac.mp h

  obtain Γƒ¿ k, hk Γƒ⌐ := h'

  have g1 : (gcd a m) Γêú a := by exact gcd_dvd_left a m
  have g2 : (gcd a m) Γêú m := by exact gcd_dvd_right a m
  have g3 : (gcd a m) Γêú a * b + m * k := by apply helperklavins g1 g2

  rw[Γåhk] at g3 woo

  exact Int.eq_one_of_dvd_one (by exact Int.le.intro_sub (a.gcd m + 0) rfl) g3
   -- should be able to show g3 ΓåÆ gcd a m = 1

theorem prop_1_13_b_better {a b1 b2 m : Γäñ} : a * b1 Γëí 1 [ZMOD m] ΓåÆ a * b2 Γëí 1 [ZMOD m] ΓåÆ b1 Γëí b2 [ZMOD m] := by
  intro h1 h2
  sorry
  -- have b12: b1*(a*b2) Γëí b1*1 [ZMOD m] := by exact Int.ModEq.mul (by trivial) (h2)
  -- have eeee : b1*(a*b2) Γëí b1*a*b2 [ZMOD m] := by rw[mul_assoc]
  -- have b13: (b1*a)*b2 Γëí b1*1 [ZMOD m] := by exact Int.ModEq.trans (id (Int.ModEq.symm eeee)) b12
  -- have okk: b1*a Γëí a*b1 [ZMOD m] := by rw[mul_comm]
  -- have b1a: b1*a Γëí 1 [ZMOD m] := by exact Int.ModEq.trans okk h1
  -- have b15: (b1*a)*b2 Γëí (1)*b2 [ZMOD m] := by refine Int.ModEq.mul (by exact b1a) rfl
  -- have b14: (1)*b2 Γëí b1*1 [ZMOD m] := by exact Int.ModEq.trans (id (Int.ModEq.symm b15)) b13
  -- simp at b14
  -- exact id (Int.ModEq.symm b14)

-- Further, if a ┬╖ b1 Γëí a ┬╖ b2 Γëí 1 (mod m), then b1 Γëí b2 (mod m). We call b
-- the (multiplicative) inverse of a modulo m.
theorem prop1_13_b (a b1 b2 m: Γäñ)
  (h: m ΓëÑ 1):
  ((Γêâ b: Γäñ, congru_mod (a*b) 1 m (by trivial)) Γåö Int.gcd a m = 1) Γêº
  ( ((congru_mod (a * b1) (1) m (by trivial)) Γêº (congru_mod (a * b2) (1) m (by trivial)))  ΓåÆ congru_mod (b1) (b2) m h) := by
  apply And.intro
  . apply Iff.intro
    . intro ab_eq_1_mod
      apply Exists.elim (ab_eq_1_mod)
        (
          by
          intro b1 hb1
          have m_div : m Γêú (a*b1 - 1) := hb1
          --let c : Γäñ := by assumption
          rw[Int.dvd_def] at m_div
          apply Exists.elim (m_div)
          (
            intro c1 ha1
            have ha2: a*b1 - m*c1 = 1 := by linarith
            --simp only[Int.gcd_dvd_left,Int.gcd_eq_gcd_ab,congru_mod]
            --have gcd_div :  Γêú (a*b1 - m*c1) := by Int.dvd_sub (Int.gcd_dvd_left a m) (sorry)
            --have eq1 : a*b1 - m*c1 = a.gcd m := by exact Int.gcd_eq_gcd_ab a m
           -- have so : (Int.gcd a m) Γêú a*b1 := by sorry
            have eq1 : Int.gcd a m = a * (a.gcdA m) + m * (a.gcdB m) := by exact Int.gcd_eq_gcd_ab a m

            let c2 := a.gcdA m
            let b2 := a.gcdB m

            have eq2 : Int.gcd a m = a * c2+ m * b2 := by exact Int.gcd_eq_gcd_ab a m

            sorry

            -- a.gcdA m := b1
            -- let (a.gcdB m) := c1
            -- have eq2: Int.gcd a m = a * (b1) + m * (c1) := by exact eq1
            -- rw[\la ha2] at eq2
          )
          --have c_times_m : m*c = (a*b1 - 1) := by rw[Int.dvd_def]
        )
      --simp
    . intro gcd_eq_1
      --let u : Γäñ
      --let m : Γäñ
      --apply Exists.intro b
      --sorry
      have eq1 : a.gcd m = a * (a.gcdA m) + m * (a.gcdB m) := by exact Int.gcd_eq_gcd_ab a m
      have eq2 : 1 = a * (a.gcdA m) + m * (a.gcdB m) := by rw[gcd_eq_1] at eq1; exact eq1
```
first, rewrites eq1 to equal 1, then uses exact
```hs
have eq3: m * -(a.gcdB m) = (a * (a.gcdA m) - 1) := by linarith
      have eq4: m Γêú (a * (a.gcdA m) - 1) := by exact dvd_of_mul_right_eq (-(a.gcdB m)) eq3
      have eq5: congru_mod (a * (a.gcdA m)) 1 m (by trivial) := by exact eq4
      let b := a.gcdA m
      have eq6: congru_mod (a * (b)) 1 m (by trivial) := by exact eq5
      apply Exists.intro b
      exact eq6
      --exact fffk
      --sorry
      --have Γƒ¿ er,rt,yu Γƒ⌐ := Int.gcd_eq_gcd_ab a m
      --match Γƒ¿one, twoΓƒ⌐ with Int.gcd_eq_gcd_ab a m
      --have (one, two, three) := theorem1_11 a b
  . intro andstat
    simp[congru_mod,dvd_of_mul_right_eq,Int.dvd_add,Int.dvd_sub]
    have one : m Γêú a*b1 - 1 := by apply andstat.left
    have two : m Γêú a*b2 - 1 := by apply andstat.right
    have msub := (prop1_4_c one two).right
    have subdiv : a*b1 - 1 - (a*b2 - 1) = a*(b1 - b2) := by linarith
    rw[subdiv] at msub
    sorry
    --; rw[linarith]
    -- intro s
    -- simp[congru_mod,dvd_of_mul_right_eq,Int.dvd_add,Int.dvd_sub]
    -- have ab1_eq_ab2 : 1 Γêú a*(b1 - b2) := by simp[congru_mod]
    -- sorry
```
 next: integer rings, or skip and do primes
Klavins feedback:
-You have the machinery to prove that extended euclid faster than regular
-Look at mathlib's exsting proofs for numbers; proofs should be simpler
-Doing rings, through classes/instances (registering 0, 1, multiplicative inverse, etc) is powerful and a good idea
-Start with simpler proofs like gcd(a,b)=gcd(b,a) and build up

```hs
--  The Fast Powering Algorithm: computing g^A (mod N)

--  Ex: 3^(218) mod 1000

--  Ex: 218 = 2 + 2^3 + 2^4 + 2^6 + 2^7

--  Ex: 3^218 = 3^(2 + 2^3 + 2^4 + 2^6 + 2^7) mod 1000
--            = (3^2)(3^2^3)(3^2^4)(3^2^6)(3^2^7) mod 1000
```
  Use relationship: 3^2^0 = 3  = k
                      3^2^1 = 9  = k^2
                      3^2^2 = 81 = (k^2)^2
                      3^2^3 = 6516 = ((k^2)^2)^2
```hs
-- Ans: 489 mod 1000

--  Step 1. Compute the binary expansion of A as
--  A = A0 + A1├ù2 + A2├ù2^2 + A3├ù2^3 + ┬╖┬╖┬╖ + A_r├ù(2^r) with A0,...,Ar Γêê{0,1},
--  where we may assume that Ar =1.

--  Step 2. Compute the powers g^2^i (mod N) for 0 Γëñ i Γëñ r by successive squaring,
--  a0 Γëí g                    (mod N)
--  a1 Γëí a0^2 Γëí g^2           (mod N)
--  a2 Γëí a1^2 Γëí g^2^2         (mod N)
--  a3 Γëí a2^2 Γëí g^2^3         (mod N)
--  ...
--  a_r Γëí [a_(r-1)]^2 Γëí g^2^r (mod N)
--
--  Each term is the square of the previous one, so this requires r
--  multiplications.

--  Step 3. Compute g^A (mod N) usingtheformula
--  g^A = g^( A0 + A1├ù2 + A2├ù2^2 + A3├ù2^3 + ┬╖┬╖┬╖ + A_r├ù(2^r) )
--
--      = g^(A0) ├ù (g^2)^(A1) ├ù (g^2^2)^(A2) + ... (g^2^r)^(A_r)
--
--      = a0^(A0) ├ù a1^(A1) ├ù a2^(A2) + ... a_r^(A_r) (mod N)
--
```
 A ΓëÑ 0 unstated in book, assumed due to binary expansion being nonnegative

Ex of binary exp: 19 = 1(1) + 2(1) + 4(0) + 8(0) + 16(1)
19 mod 2 = 1
19/2 = 9
9 mod 2 = 1
9/2 = 4
4 mod 2 = 0
4/2 = 2
2 mod 2 = 0
2/2 = 1
1 mod 2 = 1
1/2 = 0 -> stop: 10011


 Coefficients of binary expansion
Note: Left to Right, due to algorithm
E.g. 001 represents 4 
```hs
def nat_to_binary (A : Γäò) : List Γäò :=
  if A = 0 then []
  else [A % 2] ++ nat_to_binary (A / 2) --++ means append

#eval nat_to_binary 5
#eval nat_to_binary 16
#eval nat_to_binary 19

def g_2_i (g r N: Nat): List Nat :=
-- for intended algorithm, recursion needs to go from 0 to r, not downwards
-- look at: getlast, head, tail
-- r = 2
-- [3^2^0,3^2^1,3^2^2] n = 2
-- [3^2^0,3^2^1] n = 1. takes return, concat the sq, return up
-- [3^2^0] n = 0. returns this upwards
  if r = 0 then [g^2^0 % N]
  else
  --else
    let rest := g_2_i g (r-1) N
    --if r = 1 then [g^2^1]
    rest ++ [(rest.getLast!)^2 % N]

def helperlist (n : Nat) : List Nat :=
  if n = 0 then [0]
  else
    let rest := helperlist (n - 1)
    if n = 1 then [1]
    else rest ++ [2*(rest.getLast!)]

#eval helperlist (5^2)

#eval g_2_i 3 0 1000
```
 $$ 3^2^0 mod 1000 $$ 2
```hs
#eval g_2_i 3 1 1000  --3^2^0, 3^2^1 mod 1000
#eval g_2_i 3 5 1000  --3^2^0, 3^2^1...3^2^4 mod 1000
#eval g_2_i 3 5 11    --3^2^0, 3^2^1...3^2^4 mod 11

-- Final mod not here, instead in alg
def fast_pow_helper (bases : List Γäò) (exps : List Γäò) (N: Γäò): Γäò :=
  match bases, exps with
  | [], [] => 1
  | firs :: res1, firs2 :: res2 => ((firs ^ firs2) % N) * fast_pow_helper res1 res2 N
  | _, _ => 1 --seems like lean needs this?

#eval fast_pow_helper [3,9,4] [1,0,1] 11 --(3^1)(9^0)(4^1)

def fast_pow_alg (g A N: Γäò) : Γäñ :=
  let binexp := nat_to_binary A
  let gs := g_2_i g (binexp.length-1) N
  (fast_pow_helper gs binexp N) % N

#eval fast_pow_alg 3 218 1000 --3^218 mod 1000
#eval 3^218 % 1000

#eval fast_pow_alg 3 218123 12345
#eval 3^218123 % 12345

#eval fast_pow_alg 7 234 3
#eval 7^234 % 3
```
Proposition 1.19
Let p be a prime number, and suppose that p divides the product ab of two integers a and b. Then p divides at least one of a and b.

More generally, if p divides a product of integers, say p Γêú a_1 ├ù a_2 ... a_n

then p divides at least one of the individual a_i .

```hs
def int_prime (p: Γäñ) :=
  ΓêÇ m : Γäñ, m Γêú p ΓåÆ (m = 1) Γê¿ (m = p)
  -- apply Or.elim h
  -- . sorry
  -- . sorry

theorem prop1_19_a (a b: Γäñ) (p: Γäò)
  (h: Nat.Prime p)
```
 ofNat needed for lean to recgonize that Nat p is also an Int
```hs
(h2: Int.ofNat p Γêú a*b) : (Int.ofNat p Γêú a) Γê¿ (Int.ofNat  p Γêú b) := by
  sorry
```
Klavins: can maybe prove for nat a,b easier

Theorem 1.20 (The Fundamental Theorem of Arithmetic).
Let a ΓëÑ 2 be an integer. Then a can be factored as a product of prime numbers

a = p_1^e_1 ├ù p_2^e^2 ... p_r^e_r

Further, other than rearranging the order of the primes, this factorization into prime powers is unique.

```hs
theorem prop_1_20 (a : Γäñ) (h: a ΓëÑ 2) (p1 p2 : Γäò): a = p1*p2 := sorry
```
Next: more primes, and using fields/groups/rings in proofs, make proofs shorter
