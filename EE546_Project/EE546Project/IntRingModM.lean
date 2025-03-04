import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Tactic
import Mathlib.Data.Int.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Algebra.Ring.MinimalAxioms

-- TODO: Add comments for everything (Alexey)
-- Emmy suggests: convert and change

@[simp]
def IntRingModM : ℕ → Type
  | 0 => ℤ
  | n + 1 => Fin (n + 1)

@[simp]
theorem IntRingModM_of_nat_succ
  {m : ℕ} (h : m > 0) : IntRingModM m = Fin m := by
  match m with
  | 0 => contradiction
  | m + 1 => simp

@[simp]
instance (n m : ℕ) : OfNat (IntRingModM m) n where
  ofNat :=  match m with
  | 0 => Int.ofNat n
  | Nat.succ x => Fin.ofNat' (Nat.succ x) n

@[simp]
def IntRingModM.add {m : ℕ} (a b : IntRingModM m) : IntRingModM m := match m with
| 0 => Int.add a b
| Nat.succ _ => Fin.add a b

@[simp]
def IntRingModM.mul {m : ℕ} (a b : IntRingModM m) : IntRingModM m := match m with
| 0 => Int.mul a b
| Nat.succ _ => Fin.mul a b

@[simp]
instance {m : ℕ} : CoeOut (IntRingModM m) Nat where
  coe a := match m with
  | 0 => Int.toNat a
  | Nat.succ _ => Fin.val a

@[simp]
instance {m : ℕ} : CoeOut (IntRingModM m) Int where
  coe a := match m with
  | 0 => Int.toNat a
  | Nat.succ _ => Fin.val a

@[simp]
def IntRingModM.neg {m : ℕ} (a : IntRingModM m) : IntRingModM m := match m with
| 0 => Int.neg a
| Nat.succ n => by
  exact (((n+1) - (a : Nat)  : Fin (n+1) ): IntRingModM (n+1))

@[simp]
instance {m : ℕ} : Neg (IntRingModM m) where
  neg a := IntRingModM.neg a

@[simp]
instance {m : ℕ} : HAdd (IntRingModM m) (IntRingModM m) (IntRingModM m) where
  hAdd a b := IntRingModM.add a b

@[simp]
instance {m : ℕ} : Add (IntRingModM m) where
  add a b := IntRingModM.add a b

@[simp]
instance {m : ℕ} : HMul (IntRingModM m) (IntRingModM m) (IntRingModM m) where
  hMul a b := IntRingModM.mul a b

@[simp]
instance {m : ℕ} : Mul (IntRingModM m) where
  mul a b := IntRingModM.mul a b

-- Throws error? Klavins : HELP! Why does uncommenting this break my code lower down?
--instance {m : ℕ} : Neg (IntRingModM m) where
  --neg a := IntRingModM.neg a

@[simp]
theorem eq_with_parens {α : Type} (a b : α) : (a = b) ↔ ((a) = (b)) := by
  -- The proof is trivial because parentheses don't change the meaning
  apply Iff.intro
  . intro h
    exact h
  . intro h
    exact h

@[simp]
theorem fin_add_assoc {n : Nat} (ha hb hc : Fin (n + 1)) : ha + hb + hc = ha + (hb + hc) := by
  apply Fin.ext
  simp [Fin.add_def, Nat.add_assoc]

@[simp]
theorem fin_mul_assoc {n : Nat} (ha hb hc : Fin (n + 1)) : ha * hb * hc = ha * (hb * hc) := by
  apply Fin.ext
  simp [Fin.mul_def, Nat.mul_assoc]

@[simp]
theorem fin_zero_add {n : Nat} (ha : Fin (n + 1)) : 0 + ha = ha := by
  apply Fin.ext
  simp [Fin.add_def]

@[simp]
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

@[simp]
theorem IntRingModM.mul_assoc {m : ℕ} : ∀ (a b c : IntRingModM m), a * b * c = a * (b * c) := by
  match m with
  | 0 =>
    intro ha hb hc
    unfold IntRingModM at ha hb hc
    simp at ha hb hc
    exact Int.mul_assoc ha hb hc
  | Nat.succ n =>
    intro ha hb hc
    unfold IntRingModM at ha hb hc
    simp at ha hb hc
    exact fin_mul_assoc ha hb hc

@[simp]
theorem IntRingModM.zero_add {m : ℕ} : ∀ (a : IntRingModM m), 0 + a = a := by
  match m with
  | 0 =>
    intro ha
    unfold IntRingModM at ha
    simp at ha
    exact Int.zero_add ha
  | Nat.succ n =>
    intro ha
    unfold IntRingModM at ha
    simp at ha
    exact fin_zero_add ha

@[simp]
theorem neg_add_cancel' {a : ℤ} : -a + a = 0 := by
  exact Int.add_left_neg a

@[simp]
theorem fin_neg_add_cancel {n : Nat} (ha : Fin (n + 1)) : -ha + ha = 0 := by
  apply Fin.ext
  simp [Fin.add_def]

@[simp]
theorem IntRingModM.neg_add_cancel {m : ℕ} : ∀ (a : IntRingModM m), -a + a = 0 := by
  match m with
  | 0 =>
    intro ha
    unfold IntRingModM at ha
    exact Int.add_left_neg ha
  | Nat.succ n =>
    intro ha
    unfold IntRingModM at ha
    simp at ha
    have := fin_neg_add_cancel (ha:IntRingModM (n+1))
    simp

@[simp]
theorem IntRingModM.mul_comm {m : ℕ} : ∀ (a b : IntRingModM m), a * b = b * a := by
  match m with
  | 0 =>
    intro ha hb
    unfold IntRingModM at ha hb
    simp at ha hb
    exact Int.mul_comm ha hb
  | Nat.succ n =>
    intro ha hb
    unfold IntRingModM at ha hb
    simp at ha hb
    have := Fin.mul_comm ha hb
    exact this

@[simp]
theorem IntRingModM.one_mul {m : ℕ} : ∀ (a : IntRingModM m), 1 * a = a := by
  match m with
  | 0 =>
    intro ha
    unfold IntRingModM at ha
    simp at ha
    simp
  | Nat.succ n =>
    intro ha
    unfold IntRingModM at ha
    simp at ha
    simp

-- Copied and modified from Mathlib: ZMod.Defs.lean
-- Klavins help: What in the world is Fin.eq_of_val_eq doing
-- This is a private theorem for some reason
@[simp]
theorem fin_left_distrib {n : ℕ} (a b c : Fin n) : a * (b + c) = a * b + a * c :=
  Fin.eq_of_val_eq (
    calc
      a * ((b + c) % n) ≡ a * (b + c) [MOD n] := (Nat.mod_modEq (b+c) n).mul_left a
      _ ≡ a * b + a * c [MOD n] := by rw [mul_add]
      _ ≡ a * b % n + a * c % n [MOD n] := (Nat.mod_modEq (a*b) n).symm.add (Nat.mod_modEq (a*c) n).symm
  )

-- Klavins : Help! Why does this work? Why can't I just use "left_distrib"?
theorem int_left_distrib {a b c : ℤ} : a * (b + c) = a * b + a * c := left_distrib a b c

--set_option pp.raw true
--set_option pp.raw.maxDepth 10

theorem IntRingModM.left_distrib {m : ℕ} : ∀ (a b c : IntRingModM m), a * (b + c) = a * b + a * c := by
  match m with
  | 0 =>
    intro ha hb hc
    unfold IntRingModM at ha hb hc
    simp at ha hb hc
    have := @int_left_distrib ha hb hc
    exact this
  | Nat.succ n =>
    intro ha hb hc
    unfold IntRingModM at ha hb hc
    simp at ha hb hc
    have := @fin_left_distrib (n+1) ha hb hc
    exact this

instance {m : ℕ} : CommRing (IntRingModM m) :=
  CommRing.ofMinimalAxioms
    IntRingModM.add_assoc
    IntRingModM.zero_add
    IntRingModM.neg_add_cancel
    IntRingModM.mul_assoc
    IntRingModM.mul_comm
    IntRingModM.one_mul
    IntRingModM.left_distrib

example (R : Type) [CommRing R] (a b : R) : (a + b) * (a - b) = a^2 - b^2 := by
  ring

example {m : ℕ} (a b : IntRingModM m) : (a + b) * (a - b) = a^2 - b^2 := by
  ring
