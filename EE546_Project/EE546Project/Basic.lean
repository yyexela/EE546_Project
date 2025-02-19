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

-/

import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Tactic
import Mathlib.Data.Int.Defs
import Mathlib.Data.Nat.Defs
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









































-- Presentation Feb 20: Alexey's contribution
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
def theorem1_11_h (a b u x y g : Nat) : (Nat × Nat × Nat) :=
  if y = 0 then
    ⟨g, u, ((g-a*u)/b)⟩
  else
    let s := g / y
    let t := g % y
    theorem1_11_h a b x s t y
  termination_by y
  decreasing_by
    rename_i hy
    refine Nat.mod_lt g (by exact Nat.zero_lt_of_ne_zero hy)

-- Extended Euclidean Algorithm
def theorem1_11 (a b : Nat) : (Nat × Nat × Nat) :=
  theorem1_11_h a b 1 0 b a

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
def gcd_fast_h (a b u x y g c : Nat) : (Nat × Nat × Nat × Nat) :=
  if y = 0 then
    ⟨g, u, ((g-a*u)/b), c⟩
  else
    let s := g / y
    let t := g % y
    gcd_fast_h a b x s t y c
  termination_by y
  decreasing_by
    rename_i hy
    refine Nat.mod_lt g (by exact Nat.zero_lt_of_ne_zero hy)

-- Extended Euclidean Algorithm
def gcd_fast (a b : Nat) : (Nat × Nat × Nat × Nat) :=
  gcd_fast_h a b 1 0 b a 0

#eval gcd_slow 93 6
#eval gcd_fast 93 6




























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
