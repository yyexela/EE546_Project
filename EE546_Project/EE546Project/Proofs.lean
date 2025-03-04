
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Tactic
import Mathlib.Data.Int.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Algebra.Ring.MinimalAxioms
open Classical


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

-- Relatively Prime Definition
def rel_prime (a b : Nat) :=
  theorem1_7 a b = 1 -- theorem1_7: GCD

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

/- Coefficients of binary expansion
Note: Left to Right, due to algorithm
E.g. 001 represents 4 -/
def nat_to_binary (A : ℕ) : List ℕ :=
  if A = 0 then []
  else [A % 2] ++ nat_to_binary (A / 2) --++ means append

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

-- Final mod not here, instead in alg
def fast_pow_helper (bases : List ℕ) (exps : List ℕ) (N: ℕ): ℕ :=
  match bases, exps with
  | [], [] => 1
  | firs :: res1, firs2 :: res2 => ((firs ^ firs2) % N) * fast_pow_helper res1 res2 N
  | _, _ => 1 --seems like lean needs this?

def fast_pow_alg (g A N: ℕ) : ℤ :=
  let binexp := nat_to_binary A
  let gs := g_2_i g (binexp.length-1) N
  (fast_pow_helper gs binexp N) % N
