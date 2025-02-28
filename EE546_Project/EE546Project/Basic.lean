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

-- Proposition 1.13. Let m ≥ 1 be an integer.
-- (b) Let a be an integer. Then
-- a · b ≡ 1 (mod m) for some integer b if and only if gcd(a, m)=1.

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

theorem prop1_13_klavins {a b m: ℤ} : a*b ≡ 1 [ZMOD m] → Int.gcd a m = 1 := by

  intro h
  apply Int.modEq_iff_add_fac.mp at h

  obtain ⟨ k, hk ⟩ := h

  rw[leftarr Int.isCoprime_iff_gcd_eq_one]

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

rw[leftarr hk] at g3

sorry -- should be able to show g3 → gcd a m = 1

-- Further, if a · b1 ≡ a · b2 ≡ 1 (mod m), then b1 ≡ b2 (mod m). We call b
-- the (multiplicative) inverse of a modulo m.
theorem prop1_13_b (a b1 b2 m: ℤ)
  (h: m ≥ 1):
  ((∃ b: ℤ, congru_mod (a*b) 1 m (by trivial)) ↔ Int.gcd a m = 1) ∧
  ( ((congru_mod (a * b1) (1) m (by trivial)) ∧ (congru_mod (a * b2) (1) m (by trivial)))  → congru_mod (b1) (b2) m h) := by
  apply And.intro
  . apply Iff.intro
    . intro ab_eq_1_mod
      apply Exists.elim (ab_eq_1_mod)
        (
          by
          intro b1 hb1
          have m_div : m ∣ (a*b1 - 1) := hb1
          --let c : ℤ := by assumption
          rw[Int.dvd_def] at m_div
          apply Exists.elim (m_div)
          (
            intro c1 ha1
            have ha2: a*b1 - m*c1 = 1 := by linarith
            --simp only[Int.gcd_dvd_left,Int.gcd_eq_gcd_ab,congru_mod]
            --have gcd_div :  ∣ (a*b1 - m*c1) := by Int.dvd_sub (Int.gcd_dvd_left a m) (sorry)
            --have eq1 : a*b1 - m*c1 = a.gcd m := by exact Int.gcd_eq_gcd_ab a m
           -- have so : (Int.gcd a m) ∣ a*b1 := by sorry
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
      --let u : ℤ
      --let m : ℤ
      --apply Exists.intro b
      --sorry
      have eq1 : a.gcd m = a * (a.gcdA m) + m * (a.gcdB m) := by exact Int.gcd_eq_gcd_ab a m
      have eq2 : 1 = a * (a.gcdA m) + m * (a.gcdB m) := by rw[gcd_eq_1] at eq1; exact eq1 /-first, rewrites eq1 to equal 1, then uses exact-/
      have eq3: m * -(a.gcdB m) = (a * (a.gcdA m) - 1) := by linarith
      have eq4: m ∣ (a * (a.gcdA m) - 1) := by exact dvd_of_mul_right_eq (-(a.gcdB m)) eq3
      have eq5: congru_mod (a * (a.gcdA m)) 1 m (by trivial) := by exact eq4
      let b := a.gcdA m
      have eq6: congru_mod (a * (b)) 1 m (by trivial) := by exact eq5
      apply Exists.intro b
      exact eq6
      --exact fffk
      --sorry
      --have ⟨ er,rt,yu ⟩ := Int.gcd_eq_gcd_ab a m
      --match ⟨one, two⟩ with Int.gcd_eq_gcd_ab a m
      --have (one, two, three) := theorem1_11 a b
  . intro andstat
    simp[congru_mod,dvd_of_mul_right_eq,Int.dvd_add,Int.dvd_sub]
    have one : m ∣ a*b1 - 1 := by apply andstat.left
    have two : m ∣ a*b2 - 1 := by apply andstat.right
    have msub := (prop1_4_c one two).right
    have subdiv : a*b1 - 1 - (a*b2 - 1) = a*(b1 - b2) := by linarith
    rw[subdiv] at msub
    sorry
    --; rw[linarith]
    -- intro s
    -- simp[congru_mod,dvd_of_mul_right_eq,Int.dvd_add,Int.dvd_sub]
    -- have ab1_eq_ab2 : 1 ∣ a*(b1 - b2) := by simp[congru_mod]
    -- sorry

/- next: integer rings, or skip and do primes
Klavins feedback:
-You have the machinery to prove that extended euclid faster than regular
-Look at mathlib's exsting proofs for numbers; proofs should be simpler
-Doing rings, through classes/instances (registering 0, 1, multiplicative inverse, etc) is powerful and a good idea
-Start with simpler proofs like gcd(a,b)=gcd(b,a) and build up
-/


/-
Integer rings

Goal: "Ring of integers modulo m"
-/

/-
Start with simple definition:

Create an integer ring modulo 5
-/

structure IntRingMod5 where
  elements : Fin 5
  deriving Repr  -- For custom prints

-- Overwrite print
instance : Repr IntRingMod5 where
  reprPrec r _ := repr r.elements

/-
Problem in the code below:
-/

def a : IntRingMod5 := 4 -- OfNat required
def b : Fin 5 := 4

/-
Error:
```
failed to synthesize
  OfNat IntRingMod5 4
numerals are polymorphic in Lean, but the numeral `4` cannot be used in a context where the expected type is
  IntRingMod5
due to the absence of the instance above
```

So, we need to define `OfNat`:
-/

-- Define OfNat
instance (n : ℕ) : OfNat IntRingMod5 n where
  ofNat := { elements := Fin.ofNat' 5 n }

def c : IntRingMod5 := 4

/-
Great! So this code works, now we want to define addition and multiplication. The below code does not work.
-/
#eval c + c -- need to define addition
#eval c * c -- need to define multiplication

/-
Error:
```
failed to synthesize
  HAdd IntRingMod5 IntRingMod5 ?m.203412
```

So, let's define add and mul:
-/

-- Readable way
def IntRingMod5.add (a b : IntRingMod5) : IntRingMod5 :=
  {elements := a.elements + b.elements}

-- Less readable way
def IntRingMod5.add' (a b : IntRingMod5) : IntRingMod5 := match a, b with
| ⟨x⟩, ⟨y⟩ => ⟨x + y⟩

def IntRingMod5.mul (a b : IntRingMod5) : IntRingMod5 := match a, b with
| ⟨x⟩, ⟨y⟩ => ⟨x * y⟩

-- Show finset handles modulo already
#eval IntRingMod5.add ⟨2⟩ ⟨3⟩  -- Output: 0 (since 2 + 3 = 5 ≡ 0 mod 5)
#eval IntRingMod5.mul ⟨2⟩ ⟨3⟩  -- Output: 0 (since 2 * 3 = 6 ≡ 1 mod 5)

/-
The above code works, but lean still doesn't know what + and * are for our new type!
-/

-- not quite finished!
#eval c + c
#eval c * c

/-
Error:
```
failed to synthesize
  HAdd IntRingMod5 IntRingMod5 ?m.206704
```

Need to define HAdd and HMul:
-/

-- Define HAdd
instance : HAdd IntRingMod5 IntRingMod5 IntRingMod5 where
  hAdd a b := { elements := a.elements + b.elements }

-- Define HMul
instance : HMul IntRingMod5 IntRingMod5 IntRingMod5 where
  hMul a b := { elements := a.elements * b.elements }

/-
This now works!:
-/

#eval c
#eval c + c -- 4 + 4 = 8 = 3 + 5 = 3 mod 5
#eval c * c -- 4 * 4 = 16 = 1 + 15 = 1 mod 5

/-
Let's now extend this to general rings mod m, instead of just rings mod 5...
-/

-- General ring mod m
def IntRingModM : ℕ → Type
  | 0 => ℤ
  | n + 1 => Fin (n + 1)

/-
Need to define OfNat again...
-/

def a1 : IntRingModM 5 := 4 -- OfNat required

/-
Error:
```
failed to synthesize
  OfNat (IntRingModM 5) 4
numerals are polymorphic in Lean, but the numeral `4` cannot be used in a context where the expected type is
  IntRingModM 5
due to the absence of the instance above
```

Defining OfNat:
-/

instance (n m : ℕ) : OfNat (IntRingModM m) n where
  ofNat :=  match m with
  | 0 => Int.ofNat n
  | Nat.succ x => Fin.ofNat' (Nat.succ x) n

def c1 : IntRingModM 5 := 4
#eval c1

/-
This code works!

Let's define add and mul as before
-/

-- Define add and multiply

-- Readable way
set_option diagnostics.threshold 100
def IntRingModM.add {m : ℕ} (a b : IntRingModM m) : IntRingModM m := match m with
| 0 => Int.add a b
| Nat.succ _ => Fin.add a b

-- Readable way
set_option diagnostics.threshold 100
def IntRingModM.mul {m : ℕ} (a b : IntRingModM m) : IntRingModM m := match m with
| 0 => Int.mul a b
| Nat.succ _ => Fin.mul a b

set_option diagnostics.threshold 200
instance {m : ℕ} : CoeOut (IntRingModM m) Nat where
  coe a := match m with
  | 0 => Int.toNat a
  | Nat.succ _ => Fin.val a

instance {m : ℕ} : CoeOut (IntRingModM m) Int where
  coe a := match m with
  | 0 => Int.toNat a
  | Nat.succ _ => Fin.val a

/-
instance {m : ℕ} : Coe (IntRingModM m) Nat where
  coe a := by
    have b := (a : Fin m)
    have c := b.val
    exact c
-/

set_option diagnostics.threshold 200

-- Readable way
set_option diagnostics.threshold 100
def IntRingModM.neg {m : ℕ} (a : IntRingModM m) : IntRingModM m := match m with
| 0 => 0
| Nat.succ n => by
  exact (((n+1) - (a : Nat)  : Fin (n+1) ): IntRingModM (n+1))

/-
Once again, make + and * understandable by the interpreter
-/

-- Make lean parse understand "+" and "*"
-- Define HAdd
instance {m : ℕ} : HAdd (IntRingModM m) (IntRingModM m) (IntRingModM m) where
  hAdd a b := IntRingModM.add a b

instance {m : ℕ} : Add (IntRingModM m) where
  add a b := IntRingModM.add a b

-- Define HAdd
instance {m : ℕ} : HMul (IntRingModM m) (IntRingModM m) (IntRingModM m) where
  hMul a b := IntRingModM.mul a b

instance {m : ℕ} : Mul (IntRingModM m) where
  mul a b := IntRingModM.mul a b

instance {m : ℕ} : Neg (IntRingModM m) where
  neg a := IntRingModM.neg a


#eval (1 : ZMod 5)
#eval (1 : IntRingModM 5)
#eval (-102 : ZMod 5)
#eval (-102 : IntRingModM 5)

/-
The below code works!
-/

#eval c1
#eval c1 + c1 -- 4 + 4 = 8 = 3 + 5 = 3 mod 5
#eval c1 * c1 -- 4 * 4 = 16 = 1 + 15 = 1 mod 5

#eval (2 : (IntRingModM 0)) + (8 : (IntRingModM 0))
#eval (2 : (IntRingModM 10)) + (8 : (IntRingModM 10))
#eval (2 : (IntRingModM 10)) * (8 : (IntRingModM 10))

/-
How are integer rings defined in Mathlib? They are defined as `ZMod` which is a `CommRing`...
-/

-- ZMod in Mathlib is defined using Commutative Ring
#print CommRing

-- See:
-- https://github.com/leanprover-community/mathlib4/blob/d45d317d3256f91efd89409bbc981e28286530d9/Mathlib/Data/ZMod/Defs.lean#L122

-- Example elements in ZMod' 5
def m : ℕ := 5  -- Modulus
def d : ZMod m := 2
def e : ZMod m := 3

#eval d + e

#eval ZMod.inv 5 3

/-
For future work, we need to create our IntRingModM to become a CommRing with `CommRing.ofMinimalAxioms`:

```
{R : Type u} [Add R] [Mul R] [Neg R] [Zero R] [One R]
(add_assoc : ∀ (a b c : R), a + b + c = a + (b + c))
(zero_add : ∀ (a : R), 0 + a = a)
(neg_add_cancel : ∀ (a : R), -a + a = 0)
(mul_assoc : ∀ (a b c : R), a * b * c = a * (b * c))
(mul_comm : ∀ (a b : R), a * b = b * a)
(one_mul : ∀ (a : R), 1 * a = a)
(left_distrib : ∀ (a b c : R), a * (b + c) = a * b + a * c)
: CommRing R
```
-/

#eval (3 : ZMod 5)
#eval (3 : IntRingModM 5)
#eval (-3 : ZMod 5)
#eval (-3 : IntRingModM 5)

theorem eq_with_parens {α : Type} (a b : α) : (a = b) ↔ ((a) = (b)) := by
  -- The proof is trivial because parentheses don't change the meaning
  apply Iff.intro
  . intro h
    exact h
  . intro h
    exact h

-- Define the theorem
set_option diagnostics.threshold 5000
theorem fin_add_assoc {n : Nat} (ha hb hc : Fin (n + 1)) : ha + hb + hc = ha + (hb + hc) := by
  apply Fin.ext
  simp [Fin.add_def, Nat.add_assoc]

set_option diagnostics.threshold 5000
theorem IntRingModM.add_assoc {m : ℕ} : ∀ (a b c : IntRingModM m), a + b + c = a + (b + c) := by
  match m with
  | 0 =>
    intro ha hb hc
    unfold IntRingModM at ha hb hc
    simp at ha hb hc
    exact Int.add_assoc ha hb hc
  | Nat.succ n =>
    intro ha hb hc
    unfold IntRingModM at ha hb hc
    simp at ha hb hc
    exact fin_add_assoc ha hb hc



theorem IntRingModM.zero_add {m : ℕ} : ∀ (a : IntRingModM m), 0 + a = a := by
  sorry

theorem IntRingModM.neg_add_cancel {m : ℕ} : ∀ (a : IntRingModM m), -a + a = 0 := by
  sorry

theorem IntRingModM.mul_assoc {m : ℕ} : ∀ (a b c : IntRingModM m), a * b * c = a * (b * c) := by
  sorry

theorem IntRingModM.mul_comm {m : ℕ} : ∀ (a b : IntRingModM m), a * b = b * a := by
  sorry

theorem IntRingModM.one_mul {m : ℕ} : ∀ (a : IntRingModM m), 1 * a = a := by
  sorry

theorem IntRingModM.left_distrib {m : ℕ} : ∀ (a b c : IntRingModM m), a * (b + c) = a * b + a * c := by
  sorry


--noncomputable
set_option diagnostics true
instance {m : ℕ} : CommRing (IntRingModM m) :=
  CommRing.ofMinimalAxioms
    IntRingModM.add_assoc
    IntRingModM.zero_add
    IntRingModM.neg_add_cancel
    IntRingModM.mul_assoc
    IntRingModM.mul_comm
    IntRingModM.one_mul
    IntRingModM.left_distrib

--  The Fast Powering Algorithm: computing g^A (mod N)

--  Ex: 3^(218) mod 1000

--  Ex: 218 = 2 + 2^3 + 2^4 + 2^6 + 2^7

--  Ex: 3^218 = 3^(2 + 2^3 + 2^4 + 2^6 + 2^7) mod 1000
--            = (3^2)(3^2^3)(3^2^4)(3^2^6)(3^2^7) mod 1000

/-  Use relationship: 3^2^0 = 3  = k
                      3^2^1 = 9  = k^2
                      3^2^2 = 81 = (k^2)^2
                      3^2^3 = 6516 = ((k^2)^2)^2-/

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

def nat_to_binary (n : ℕ) : List ℕ :=
  if n = 0 then []
  else nat_to_binary (n / 2) ++ [n % 2] /-++ means append-/

#eval nat_to_binary 5
#eval nat_to_binary 16
#eval nat_to_binary 19

def g_2_i (L : List ℕ) (r g i : ℕ): List ℕ :=
  /-for intended algorithm, recursion needs to go from 0 to r, not downwards-/
  sorry

def fast_pow_alg (g N: ℤ) (A : ℕ) (L: List ℕ): ℤ :=
  sorry






































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
theorem prop_1_20 (a : ℤ) (h: a ≥ 2) :

/-Next: more primes, and using fields/groups/rings in proofs, make proofs shorter-/
