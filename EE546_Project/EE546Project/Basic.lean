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

theorem helper_lemma_1 {a b : ℤ} : 1 = a * b → a = 1 ∨ a = -1 := by
  intro h
  match a, b with
  | Int.ofNat x, Int.ofNat y =>
    match x, y with
    | 0, 0 =>
      simp_all
    | z + 1, 0 =>
      simp_all
    | 0, w + 1 =>
      simp_all
    | z + 1, w + 1 =>
      match z, w with
      | 0, 0 =>
        simp_all
      | e + 1, 0 =>
        simp_all
      | 0, f + 1 =>
        simp_all
      | e + 1, f + 1 =>
        by_contra! h2
        have h3: 1 < e + 1 + 1 := by simp
        have h4: 1 < f + 1 + 1 := by simp
        have : 1 < (e + 1 + 1)*(f + 1 + 1) := by simp[lt_mul_of_one_lt_of_lt_of_pos]
        have : 1 < Int.ofNat (e + 1 + 1)*Int.ofNat (f + 1 + 1) := by exact Int.lt_of_toNat_lt this
        have : 1 ≠ Int.ofNat (e + 1 + 1)*Int.ofNat (f + 1 + 1) := by linarith
        contradiction
  | Int.negSucc x, Int.negSucc y =>
    match x, y with
    | 0, 0 =>
      simp_all
    | z + 1, 0 =>
      simp_all
    | 0, w + 1 =>
      simp_all
    | z + 1, w + 1 =>
      match z, w with
      | 0, 0 =>
        simp_all
      | e + 1, 0 =>
        by_contra! h3
        simp_all
        have : 1 = -(2*Int.negSucc (e+1+1)) := by linarith
        have : 1 = -(Int.negSucc (e+1+1) + Int.negSucc (e+1+1)) := by rw[this,Int.two_mul]
        have : 1 = -(Int.negSucc (e+1+1 + e+1+1).succ) := by exact this
        have hh: e+1+1 + e+1+1 = 2*e + 4 := by linarith
        have : 1 = -(Int.negSucc (2*e + 5)) := by simp[hh, this]
        have h_1: 1 = (2*e + 6) := by exact Int.ofNat_inj.mp this
        have : 1 < 2*e + 6 := by exact Nat.one_lt_succ_succ (2 * e + 4)
        have h_2: 1 ≠ 2*e + 6 := by exact Nat.ne_of_beq_eq_false rfl
        contradiction

      | 0, f + 1 =>
        by_contra! h3
        simp_all
        have : 1 = -(2*Int.negSucc (f+1+1)) := by linarith
        have : 1 = -(Int.negSucc (f+1+1) + Int.negSucc (f+1+1)) := by rw[this,Int.two_mul]
        have : 1 = -(Int.negSucc (f+1+1 + f+1+1).succ) := by exact this
        have hh: f+1+1 + f+1+1 = 2*f + 4 := by linarith
        have : 1 = -(Int.negSucc (2*f + 5)) := by simp[hh, this]
        have h_1: 1 = (2*f + 6) := by exact Int.ofNat_inj.mp this
        have : 1 < 2*f + 6 := by exact Nat.one_lt_succ_succ (2 * f + 4)
        have h_2: 1 ≠ 2*f + 6 := by exact Nat.ne_of_beq_eq_false rfl
        contradiction

      | e + 1, f + 1 =>
        sorry
  | Int.negSucc x, Int.ofNat y => sorry
  | Int.ofNat x, Int.negSucc y => sorry



    /-
      have h1 : Int.negSucc y.succ = -y.succ.succ := by exact rfl
      have h2 : -(1:ℤ)*y.succ.succ = -1*(y+2) := by exact rfl
      have h3 : -(1:ℤ)*(y+2) = -y-2 := by linarith
      simp[h3,h2,h1] at h
      have h4 : 1 = (-y-2) * b := by linarith
      have h5 : 1 = -y*b-2*b := by linarith
      have h6 : 1 = -y*b-2*b := by linarith
      simp

      have : Int.negSucc y.succ < 0 := by simp[Int.negSucc_lt_zero]
      have : -y < -1 := by linarith
      have : Int.negSucc y.succ ≠ 1 := by linarith
    -/





theorem prop1_4_b {a b : ℤ} : a ∣ b → b ∣ a → a = b ∨ a = -b := by
  intro h1 h2
  simp_all[dvd_def]
  obtain ⟨c, h1⟩ := h1
  obtain ⟨d, h2⟩ := h2
  rw[h1] at h2
  have : 1 = c*d := by match a with
  | 0 => sorry
  | Int.ofNat x => sorry
  | Int.negSucc x => sorry
  sorry
