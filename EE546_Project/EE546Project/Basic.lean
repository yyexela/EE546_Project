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
        by_contra! h3
        have h3: 1 < e + 1 + 1 := by simp
        have h4: Int.negSucc (e + 1 + 1) < 1 := by
          exact (Mathlib.Tactic.Qify.intCast_lt (Int.negSucc (e + 1 + 1)) 1).mpr rfl
        have h5: Int.negSucc (e + 1 + 1) < 1 := by
          exact (Mathlib.Tactic.Qify.intCast_lt (Int.negSucc (e + 1 + 1)) 1).mpr rfl
        have : 1 < Int.negSucc (e + 1 + 1)*Int.negSucc (f + 1 + 1) := by exact compare_gt_iff_gt.mp rfl
        have : 1 ≠ Int.negSucc (e + 1 + 1)*Int.negSucc (f + 1 + 1) := by linarith
        contradiction

  | Int.negSucc x, Int.ofNat y =>
    match x, y with
    | 0, 0 =>
      simp_all
    | z + 1, 0 =>
      simp_all
    | 0, w + 1 =>
      match w with
      | 0 =>
        simp_all
      | f + 1 =>
        by_contra! h3
        have : 1 ≠ Int.negSucc 0 * Int.ofNat (f + 1 + 1) := by exact ne_of_beq_false rfl
        contradiction
    | z + 1, w + 1 =>
      match z, w with
      | 0, 0 =>
        simp_all
      | e + 1, 0 =>
        by_contra! h3
        simp_all

      | 0, f + 1 =>
        by_contra! h3
        by_contra! h3
        have : 1 ≠ Int.negSucc 0 * Int.ofNat (f + 1 + 1) := by exact ne_of_beq_false rfl
        contradiction
      | e + 1, f + 1 =>
        by_contra! h3
        have h3: 1 < e + 1 + 1 := by simp
        have h4: Int.negSucc (e + 1 + 1) < 1 := by
          exact (Mathlib.Tactic.Qify.intCast_lt (Int.negSucc (e + 1 + 1)) 1).mpr rfl
        have h5: Int.negSucc (e + 1 + 1) < 1 := by
          exact (Mathlib.Tactic.Qify.intCast_lt (Int.negSucc (e + 1 + 1)) 1).mpr rfl
        have : 1 < Int.negSucc (e + 1 + 1)*Int.negSucc (f + 1 + 1) := by exact compare_gt_iff_gt.mp rfl
        have : 1 ≠ Int.negSucc (e + 1 + 1)*Int.negSucc (f + 1 + 1) := by linarith
        contradiction

  | Int.ofNat y, Int.negSucc x =>
    match x, y with
    | 0, 0 =>
      simp_all
    | z + 1, 0 =>
      simp_all
    | 0, w + 1 =>
      match w with
      | 0 =>
        simp_all
      | f + 1 =>
        by_contra! h3
        have : 1 ≠ Int.negSucc 0 * Int.ofNat (f + 1 + 1) := by exact ne_of_beq_false rfl
        contradiction
    | z + 1, w + 1 =>
      match z, w with
      | 0, 0 =>
        simp_all
      | e + 1, 0 =>
        by_contra! h3
        simp_all

      | 0, f + 1 =>
        by_contra! h3
        by_contra! h3
        have : 1 ≠ Int.negSucc 0 * Int.ofNat (f + 1 + 1) := by exact ne_of_beq_false rfl
        contradiction
      | e + 1, f + 1 =>
        by_contra! h3
        have h3: 1 < e + 1 + 1 := by simp
        have h4: Int.negSucc (e + 1 + 1) < 1 := by
          exact (Mathlib.Tactic.Qify.intCast_lt (Int.negSucc (e + 1 + 1)) 1).mpr rfl
        have h5: Int.negSucc (e + 1 + 1) < 1 := by
          exact (Mathlib.Tactic.Qify.intCast_lt (Int.negSucc (e + 1 + 1)) 1).mpr rfl
        have : 1 < Int.negSucc (e + 1 + 1)*Int.negSucc (f + 1 + 1) := by exact compare_gt_iff_gt.mp rfl
        have : 1 ≠ Int.negSucc (e + 1 + 1)*Int.negSucc (f + 1 + 1) := by linarith
        contradiction

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
  intro h1 h2
  simp_all[dvd_def]
  obtain ⟨c, h1⟩ := h1
  obtain ⟨d, h2⟩ := h2
  rw[h1] at h2
  match a, b with
  | Int.ofNat x, Int.ofNat y =>
    match x, y with
    | 0, 0 =>
      simp_all
    | 0, Nat.succ z =>
      simp_all
    | Nat.succ z, 0 =>
      by_contra! h3
      simp at h1 h2 h3
      apply Or.elim h1
      . intro h
        exact h3 h
      . intro h
        simp[h] at h2
        exact h3 h2
    | Nat.succ z, Nat.succ w =>
      simp
      simp at h1 h2
      have h3: ((z:ℤ) + 1) ≠ 0 := by exact Ne.symm (Int.ne_of_lt (Int.sign_eq_one_iff_pos.mp rfl))
      have h4 : 1 * (↑z + 1) =  (c * d) * (↑z + 1) := by linarith
      have h5 : 1 = c * d := by apply Int.eq_of_mul_eq_mul_right h3 h4
      have h6 := helper_lemma_2 h5
      apply Or.elim h6
      . rintro ⟨h7, h8⟩
        simp[h7,h8] at h1 h2
        left
        exact id (Eq.symm h1)
      . rintro ⟨h7, h8⟩
        simp[h7,h8] at h1 h2
        left
        linarith
  | Int.negSucc x, Int.negSucc y =>
    match x, y with
    | 0, 0 =>
      sorry
    | z + 1, 0 =>
      sorry
    | 0, w + 1 =>
      sorry
    | z + 1, w + 1 =>
      sorry
  | Int.ofNat x, Int.negSucc y =>
    sorry
  | Int.negSucc y, Int.ofNat x =>
    sorry

/-
      -- simp[Int.mul_zero] at h1
      have h3b: Int.ofNat z.succ ≠ 0 := by exact Ne.symm (Int.ne_of_lt (Int.sign_eq_one_iff_pos.mp rfl))
      have h4 : 1 * Int.ofNat z.succ =  (c * d) * Int.ofNat z.succ := by linarith
      have h5 : 1 = c * d := by apply Int.eq_of_mul_eq_mul_right h3b h4
      have h6 := helper_lemma_1 h5
      apply Or.elim h6
      . intro h7

        sorry
      . sorry
-/
