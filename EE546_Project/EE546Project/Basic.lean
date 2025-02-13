/-

  An Introduction to Mathematical Cryptography
  (Second Edition)

  Jeffrey Hoffstein
  Jill Pipher
  Joseph H. Silverman

  Lean code created by

  Henry Do
  Alexey Yermakov

-/

import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Tactic
import Mathlib.Data.Int.Defs
import Mathlib.Data.Nat.Defs
open Classical

/-
  Chapter 1: An Introduction to Cryptography
-/

theorem prop1_4_a {a b c : ℤ} : a ∣ b → b ∣ c → a ∣ c := by
  intro h1 h2
  exact Int.dvd_trans h1 h2

-- Not in book
theorem helper_lemma_1 {a b : ℤ} : 1 = a * b → a = 1 ∨ a = -1 := by
  intro h
  exact Int.eq_one_or_neg_one_of_mul_eq_one (id (Eq.symm h))

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

theorem prop1_4_c {a b c: ℤ } : a ∣ b → a ∣ c → a ∣ (b+c) ∧ a ∣ (b-c) := by
  intro h1 h2
  exact ⟨ Int.dvd_add h1 h2, Int.dvd_sub h1 h2⟩

/-Seems like proving big O notation in Lean is very difficult / currently not practical:
Because: "using functional extensionality, Lean thinks all computations of
gcd are the same." - Jason Rute, IBM
https://proofassistants.stackexchange.com/questions/2397/prove-an-upper-bound-on-the-computation-time-of-the-euclidean-algorithm-in-lean4

This will affect proving other theorems in the book
-/

/-Mathlib's implementation: Euclidean Domain, uses rings -/
def gcd (a b : R) : R :=
  if a0 : a = 0 then b
  else
    have _ := mod_lt b a0 /-mod_lt: depends on other things in Euclidean class-/
    gcd (b % a) a

/- Basic (non extended) implementation attempt-/
/- Nat used for simplicity, even though alg mentions "positive integers"
if the def in Lean has no errors, it implies it converges (finite steps)-/
def euclid_alg (a b: ℕ) (h : a ≥ b) : ℕ :=
  let r0 := a
  let r1 := b
  have i := 1
  let rem := r0 % r1
  match rem with
  | 0 => r1
  | x =>
    have h0 : rem < r1.succ := by
      apply Nat.lt_succ_of_le
      have h2 : rem ≤ r1 := by refine Nat.le_of_lt_succ (sorry)
      exact h2
    have h1 : r1 ≥ rem := by refine Nat.le_of_lt_succ (h0)
    euclid_alg r1 rem (h1)

/-another attempt-/
def euclid_alg2 (a b: ℕ) : ℕ :=
  if b = 0 then b
  else euclid_alg2 a (a % b)

/-Proves euclid_alg actually returns gcd-/
theorem euclid1_7 {a b: ℕ} : euclid_alg a b = Nat.gcd a b := sorry

/-Next: extended euclid, modulo, primes-/
