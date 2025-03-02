-- Helpful: mathlib4-all-tactics
/-

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

-/

import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Tactic
import Mathlib.Data.Int.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Algebra.Ring.MinimalAxioms
open Classical

/-
  Chapter 1: An Introduction to Cryptography
-/

/-. Prop 1.4 Let a, b, c ∈ Z be integers.
(a) If a | b and b | c, then a | c.-/
theorem prop1_4_a {a b c : ℤ} : a ∣ b → b ∣ c → a ∣ c := by
  intro h1 h2
  exact Int.dvd_trans h1 h2

/- if ab=1, then a=1 OR a=-1-/
-- Not in book
theorem helper_lemma_1 {a b : ℤ} : 1 = a * b → a = 1 ∨ a = -1 := by
  intro h
  exact Int.eq_one_or_neg_one_of_mul_eq_one (id (Eq.symm h))

/- if ab=1, then a,b=1 OR a,b=-1-/
-- Not in book
theorem helper_lemma_2 {a b : ℤ} : 1 = a * b → (a = 1 ∧ b = 1) ∨ (a = -1 ∧ b = -1) := by
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

-- (b) If a | b and b | a, then a = ±b.
/-classical not needed, but makes things easier-/
theorem prop1_4_b {a b : ℤ} : a ∣ b → b ∣ a → a = b ∨ a = -b := by
  apply Or.elim (Classical.em (a < 0))
  . apply Or.elim (Classical.em (b < 0))
    . intro hb ha hab hba
      have ha : 0 ≤ -a := by linarith
      have hb : 0 ≤ -b := by linarith
      have hab : -a ∣ -b := by simp_all
      have hba : -b ∣ -a := by simp_all
      have h1 := Int.dvd_antisymm ha hb hab hba
      have : a = b := by linarith
      left
      exact this
    . intro hb ha hab hba
      have ha : 0 ≤ -a := by linarith
      have hb : 0 ≤ b := by linarith
      have hab : -a ∣ b := by simp_all
      have hba : b ∣ -a := by simp_all
      have h1 := Int.dvd_antisymm ha hb hab hba
      have : a = -b := by linarith
      right
      exact this
  . apply Or.elim (Classical.em (b < 0))
    . intro hb ha hab hba
      have ha : 0 ≤ a := by linarith
      have hb : 0 ≤ -b := by linarith
      have hab : a ∣ -b := by simp_all
      have hba : -b ∣ a := by simp_all
      have h1 := Int.dvd_antisymm ha hb hab hba
      have : a = -b := by linarith
      right
      exact this
    . intro hb ha hab hba
      have ha : 0 ≤ a := by linarith
      have hb : 0 ≤ b := by linarith
      have h1 := Int.dvd_antisymm ha hb hab hba
      have : a = b := by linarith
      left
      exact this

-- (c) If a | b and a | c, then a | (b + c) and a | (b − c).
theorem prop1_4_c {a b c: ℤ } : a ∣ b → a ∣ c → a ∣ (b+c) ∧ a ∣ (b-c) := by
  intro h1 h2
  exact ⟨ Int.dvd_add h1 h2, Int.dvd_sub h1 h2⟩

/-
How do you prove a recursive algorithm to converges in L∃∀N?
1) Define the algorithm
2) Specify a decreasing value
3) Prove the value decreases each iteration
-/

def factorial1 (a:Nat) : Nat :=
  if a = 0 then 1
  else
    a * factorial1 (a-1)
  termination_by a
  decreasing_by
    rename_i ha
    exact Nat.sub_one_lt ha

#eval factorial1 4

-- Of course, for this simple example L∃∀N can infer that it terminates by the single argument a and it knows that a-1 < a pretty trivially....

def factorial2 (a:Nat) : Nat :=
  if a = 0 then 1
  else
    a * factorial2 (a-1)
  termination_by a

def factorial3 (a:Nat) : Nat :=
  if a = 0 then 1
  else
    a * factorial3 (a-1)

def factorial4 : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial4 n

/-
So, we return to wanting to prove that we can compute the GCD of two numbers in a finite number of steps, this is called the Euclidean Algorithm
-/

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

/-
There is a more computationally efficient definition for Euclidean's Algorithm that we can implement in lean as well:

Let a and b be positive integers. Then the equation
            au + bv = gcd(a, b)
always has a solution in integers u and v.
-/

-- Helper for extended euclidean algorithm
def theorem1_11_h (a b: Nat) (u x: Int) (y g : Nat) : (Nat × Int × Int) :=
  if y = 0 then
    ⟨g, u, ((g-a*u)/b)⟩
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
def theorem1_11 (a b : Nat) : (Nat × Int × Int) :=
  let u := 1
  let g := a
  let x := 0
  let y := b
  theorem1_11_h a b u x y g

#eval theorem1_11 93 6
/-
For fun let's check how many times we recursed! Add a counter variable to both functions:
-/

def gcd_slow_h (a b c : Nat) : Nat × Nat :=
  if a = 0 then
    ⟨b,c⟩
  else
    gcd_slow_h (b % a) a (c+1)
  termination_by a
  decreasing_by
    rename_i h
    simp_wf
    apply Nat.mod_lt _ (Nat.zero_lt_of_ne_zero _)
    assumption

def gcd_slow (a b : Nat) : Nat × Nat :=
  gcd_slow_h a b 0

-- Helper for extended euclidean algorithm
def gcd_fast_h (a b: Nat) (u x: Int) (y g c : Nat) : (Nat × Int × Int × Nat) :=
  if y = 0 then
    ⟨g, u, ((g-a*u)/b), c⟩
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
def gcd_fast (a b : Nat) : (Nat × Int × Int × Nat) :=
  let u := 1
  let g := a
  let x := 0
  let y := b
  let c := 0
  gcd_fast_h a b u x y g c

#eval gcd_slow 93 6
#eval gcd_fast 93 6

/-
What is the GCD of integers? It's just the GCD of their absolute values..
-/

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

theorem rel_prime_ex2 : ¬ rel_prime 5 35 := by
  simp[rel_prime, theorem1_7]

-- For fun: show that the first 100 numbers are relatively prime to 293 by raw computation using lists
def numbers : List Nat := List.range 101 |>.drop 1
def pairs : List (Nat × Nat) := numbers.map (λ n => (n,293))
def gcds : List Nat := pairs.map (λ ab => theorem1_7 ab.1 ab.2)
def sub1 : List Nat := gcds.map (λ gcd => gcd-1)
def sum := sub1.foldl (λ acc x => acc + x) 0

#eval numbers
#eval pairs
#eval gcds
#eval sub1
#eval sum

-- Definition. Let m ≥ 1 be an integer. We say that the integers a and b are
-- congruent modulo m if their difference a − b is divisible by m. We write
-- a ≡ b (mod m)
-- to indicate that a and b are congruent modulo m. The number m is called the
-- modulus.
def congru_mod (a b m: ℤ) (h: m ≥ 1) :=
  m ∣ (a-b)

-- Proposition 1.13. Let m ≥ 1 be an integer.
-- (a) If a1 ≡ a2 (mod m) and b1 ≡ b2 (mod m), then
-- a1 ± b1 ≡ a2 ± b2 (mod m) and a1 · b1 ≡ a2 · b2 (mod m).
theorem prop1_13_a (a1 a2 b1 b2 m: ℤ)
  (h: m ≥ 1)
  (h2: congru_mod a1 a2 m h)
  (h3: congru_mod b1 b2 m h):
  ((congru_mod (a1 + b1) (a2 + b2) m h) ∧ (congru_mod (a1 - b1) (a2 - b2) m h)) ∧ (congru_mod (a1 * b1) (a2 * b2) m h) := by
    simp_all[congru_mod]
    apply And.intro
    . have prop14c := prop1_4_c h2 h3
      have commu_sum : a1 - a2 + (b1 - b2) = a1 + b1 - (a2 + b2) := by ring
      have commu_sum2 : a1 - a2 - (b1 - b2) = a1 - b1 - (a2 - b2) := by ring
      rw[commu_sum,commu_sum2] at prop14c
      exact prop14c
    . exact dvd_mul_sub_mul h2 h3


/-gcd(a,m) divides a*b - c*m (any linear combination of a,m)-/
theorem helper_1_13_b (a b c m: ℤ): (Int.gcd a m) ∣ (a*b - c*m) := by sorry

theorem eq_iff_modEq_nat (n : ℕ) {a b : ℕ} : (a : ZMod n) = b ↔ a ≡ b [MOD n] := by
  cases n
  · simp [Nat.ModEq, Int.natCast_inj, Nat.mod_zero]
  · rw [Fin.ext_iff, Nat.ModEq, \la val_natCast, \la  val_natCast]
    exact Iff.rfl

set_option diagnostics true
theorem prop1_13_b_1 (a b: ℤ) (m: ℕ) (hm: m ≥ 1) : ((a * b: ZMod m) = 1) ↔ (Int.gcd a b = 1) := by
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
-- Proposition 1.13. Let m ≥ 1 be an integer.
-- (b) Let a be an integer. Then
-- a · b ≡ 1 (mod m) for some integer b if and only if gcd(a, m)=1.
theorem prop1_13_klavins {a b m: ℤ} : a*b ≡ 1 [ZMOD m] → Int.gcd a m = 1 := by

  intro h
  apply Int.modEq_iff_add_fac.mp at h

  obtain ⟨ k, hk ⟩ := h

  rw[←Int.isCoprime_iff_gcd_eq_one]

  use b
  use k
  rw[hk]

  ring


-- Here's a helper for for another version of the proof below

theorem helperklavins {d a b : ℤ} : d∣a → d∣b → ∀ x y, d ∣ a*x + b*y := by

  intro ha hb x y

  simp[Int.dvd_def] at ha hb

  obtain ⟨ k, hk ⟩ := ha
  obtain ⟨ j, hj ⟩ := hb

  rw[hk,hj]

  have : d * k * x + d * j * y = d*(k*x+j*y) := by ring

  rw[this]

  exact Int.dvd_mul_right d (k * x + j * y)

theorem prop1_13_klavins_2 {a b m: ℤ} : a*b ≡ 1 [ZMOD m] → gcd a m = 1 := by

  intro h

  have h' := Int.modEq_iff_add_fac.mp h

  obtain ⟨ k, hk ⟩ := h'

  have g1 : (gcd a m) ∣ a := by exact gcd_dvd_left a m
  have g2 : (gcd a m) ∣ m := by exact gcd_dvd_right a m
  have g3 : (gcd a m) ∣ a * b + m * k := by apply helperklavins g1 g2

  rw[←hk] at g3

  exact Int.eq_one_of_dvd_one (by exact Int.le.intro_sub (a.gcd m + 0) rfl) g3
   -- should be able to show g3 → gcd a m = 1

-- Proposition 1.13. Let m ≥ 1 be an integer.
-- (b) Let a be an integer. Then
-- a · b ≡ 1 (mod m) for some integer b if and only if gcd(a, m)=1.
-- Reverse direction
theorem prop_1_13b_reverse (a b m: ℤ) : Int.gcd a m = 1 → ∃ b: ℤ, a*b ≡ 1 [ZMOD m] := by
  intro h
  have eq1 : a.gcd m = a * (a.gcdA m) + m * (a.gcdB m) := by exact Int.gcd_eq_gcd_ab a m
  have eq2 : 1 = a * (a.gcdA m) + m * (a.gcdB m) := by rw[h] at eq1; exact eq1 /-first, rewrites eq1 to equal 1, then uses exact-/
  have eq3: m * -(a.gcdB m) = (a * (a.gcdA m) - 1) := by linarith
  have eq4: m ∣ (a * (a.gcdA m) - 1) := by exact dvd_of_mul_right_eq (-(a.gcdB m)) eq3
  have eq5: 1 ≡ a * (a.gcdA m) [ZMOD m] := by exact Int.modEq_iff_dvd.mpr eq4
  let b := a.gcdA m
  have eq6: a * (b) ≡ 1 [ZMOD m] := by exact id (Int.ModEq.symm eq5)
  apply Exists.intro b
  exact eq6

-- Further, if a · b1 ≡ a · b2 ≡ 1 (mod m), then b1 ≡ b2 (mod m). We call b
-- the (multiplicative) inverse of a modulo m.
theorem prop_1_13_b_part2 {a b1 b2 m : ℤ} : a * b1 ≡ 1 [ZMOD m] → a * b2 ≡ 1 [ZMOD m] → b1 ≡ b2 [ZMOD m] := by
  intro h1 h2
  have e1: b1*(a*b2) ≡ b1*1 [ZMOD m] := by exact Int.ModEq.mul (by trivial) (h2)
  have e2 : b1*(a*b2) ≡ b1*a*b2 [ZMOD m] := by rw[mul_assoc]
  have e3: (b1*a)*b2 ≡ b1*1 [ZMOD m] := by exact Int.ModEq.trans (id (Int.ModEq.symm e2)) e1
  have e4: b1*a ≡ a*b1 [ZMOD m] := by rw[mul_comm]
  have e5: b1*a ≡ 1 [ZMOD m] := by exact Int.ModEq.trans e4 h1
  have e6: (b1*a)*b2 ≡ (1)*b2 [ZMOD m] := by refine Int.ModEq.mul (by exact e5) rfl
  have e7: (1)*b2 ≡ b1*1 [ZMOD m] := by exact Int.ModEq.trans (id (Int.ModEq.symm e6)) e3
  simp at e7
  exact id (Int.ModEq.symm e7)

/- next: integer rings, or skip and do primes
Klavins feedback:
-You have the machinery to prove that extended euclid faster than regular
-Look at mathlib's exsting proofs for numbers; proofs should be simpler
-Doing rings, through classes/instances (registering 0, 1, multiplicative inverse, etc) is powerful and a good idea
-Start with simpler proofs like gcd(a,b)=gcd(b,a) and build up
-/


--  The Fast Powering Algorithm: computing g^A (mod N)

--  Ex: 3^(218) mod 1000

--  Ex: 218 = 2 + 2^3 + 2^4 + 2^6 + 2^7

--  Ex: 3^218 = 3^(2 + 2^3 + 2^4 + 2^6 + 2^7) mod 1000
--            = (3^2)(3^2^3)(3^2^4)(3^2^6)(3^2^7) mod 1000

/-  Use relationship: 3^2^0 = 3  = k
                      3^2^1 = 9  = k^2
                      3^2^2 = 81 = (k^2)^2
                      3^2^3 = 6516 = ((k^2)^2)^2-/

-- Ans: 489 mod 1000

--  Step 1. Compute the binary expansion of A as
--  A = A0 + A1×2 + A2×2^2 + A3×2^3 + ··· + A_r×(2^r) with A0,...,Ar ∈{0,1},
--  where we may assume that Ar =1.

--  Step 2. Compute the powers g^2^i (mod N) for 0 ≤ i ≤ r by successive squaring,
--  a0 ≡ g                    (mod N)
--  a1 ≡ a0^2 ≡ g^2           (mod N)
--  a2 ≡ a1^2 ≡ g^2^2         (mod N)
--  a3 ≡ a2^2 ≡ g^2^3         (mod N)
--  ...
--  a_r ≡ [a_(r-1)]^2 ≡ g^2^r (mod N)
--
--  Each term is the square of the previous one, so this requires r
--  multiplications.

--  Step 3. Compute g^A (mod N) usingtheformula
--  g^A = g^( A0 + A1×2 + A2×2^2 + A3×2^3 + ··· + A_r×(2^r) )
--
--      = g^(A0) × (g^2)^(A1) × (g^2^2)^(A2) + ... (g^2^r)^(A_r)
--
--      = a0^(A0) × a1^(A1) × a2^(A2) + ... a_r^(A_r) (mod N)
--
/- A ≥ 0 unstated in book, assumed due to binary expansion being nonnegative

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

-/

/- Coefficients of binary expansion
Note: Left to Right, due to algorithm
E.g. 001 represents 4 -/
def nat_to_binary (A : ℕ) : List ℕ :=
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
/- $$ 3^2^0 mod 1000 $$ 2-/
#eval g_2_i 3 1 1000  --3^2^0, 3^2^1 mod 1000
#eval g_2_i 3 5 1000  --3^2^0, 3^2^1...3^2^4 mod 1000
#eval g_2_i 3 5 11    --3^2^0, 3^2^1...3^2^4 mod 11

-- Final mod not here, instead in alg
def fast_pow_helper (bases : List ℕ) (exps : List ℕ) (N: ℕ): ℕ :=
  match bases, exps with
  | [], [] => 1
  | firs :: res1, firs2 :: res2 => ((firs ^ firs2) % N) * fast_pow_helper res1 res2 N
  | _, _ => 1 --seems like lean needs this?

#eval fast_pow_helper [3,9,4] [1,0,1] 11 --(3^1)(9^0)(4^1)

def fast_pow_alg (g A N: ℕ) : ℤ :=
  let binexp := nat_to_binary A
  let gs := g_2_i g (binexp.length-1) N
  (fast_pow_helper gs binexp N) % N

#eval fast_pow_alg 3 218 1000 --3^218 mod 1000
#eval 3^218 % 1000

#eval fast_pow_alg 3 218123 12345
#eval 3^218123 % 12345

#eval fast_pow_alg 7 234 3
#eval 7^234 % 3







































/-Proposition 1.19
Let p be a prime number, and suppose that p divides the product ab of two integers a and b. Then p divides at least one of a and b.

More generally, if p divides a product of integers, say p ∣ a_1 × a_2 ... a_n

then p divides at least one of the individual a_i .
-/
def int_prime (p: ℤ) :=
  ∀ m : ℤ, m ∣ p → (m = 1) ∨ (m = p)
  -- apply Or.elim h
  -- . sorry
  -- . sorry

theorem prop1_19_a (a b: ℤ) (p: ℕ)
  (h: Nat.Prime p)
  /- ofNat needed for lean to recgonize that Nat p is also an Int-/
  (h2: Int.ofNat p ∣ a*b) : (Int.ofNat p ∣ a) ∨ (Int.ofNat  p ∣ b) := by
  sorry

/-Klavins: can maybe prove for nat a,b easier-/


/-
Theorem 1.20 (The Fundamental Theorem of Arithmetic).
Let a ≥ 2 be an integer. Then a can be factored as a product of prime numbers

a = p_1^e_1 × p_2^e^2 ... p_r^e_r

Further, other than rearranging the order of the primes, this factorization into prime powers is unique.
-/
theorem prop_1_20 (a : ℤ) (h: a ≥ 2) (p1 p2 : ℕ): a = p1*p2 := sorry

/-Next: more primes, and using fields/groups/rings in proofs, make proofs shorter-/
