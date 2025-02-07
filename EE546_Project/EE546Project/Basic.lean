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
open Classical

/-
  Chapter 1: An Introduction to Cryptography
-/

theorem prop1_4_a {a b c : ℤ} : a ∣ b → b ∣ c → a ∣ c := by
  intro h1 h2
  exact Int.dvd_trans h1 h2

theorem prop1_4_b {a b : ℤ} : a ∣ b → b ∣ a → a = b ∨ a = -b := by
  intro h1 h2
  simp_all[dvd_def]
  obtain ⟨c, h1⟩ := h1
  obtain ⟨d, h2⟩ := h2
  rw[h1] at h2
  have : 1 = c*d := by match a with
  | 0 => sorry
  | ofNat x => sorry
  | negSucc x => sorry
  sorry
