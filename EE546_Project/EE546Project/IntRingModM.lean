import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Tactic
import Mathlib.Data.Int.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Algebra.Ring.MinimalAxioms

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


/-
OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 6 (instOfNatNat 6))) 2 (Fin.instOfNat (OfNat.ofNat.{0} Nat 6 (instOfNatNat 6)) (Nat.instNeZeroSucc (OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) 2)
OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 6 (instOfNatNat 6))) 2 (Fin.instOfNat (OfNat.ofNat.{0} Nat 6 (instOfNatNat 6)) (Nat.instNeZeroSucc (OfNat.ofNat.{0} Nat 5 (instOfNatNat 5))) 2)
-/

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

--example : ()

def c1 : Fin 5 := 3
def c2 : IntRingModM 5 := 3
#eval c1
#eval c2
#eval -c1
#eval -c2

--@[simp]
--theorem IntRingModM.ext {m : ℕ} {a b : IntRingModM m} (h : (a : ℕ) = b) : a = b := by
  --match m with
  --| 0 =>
  --| Nat.succ n => sorry

@[simp]
theorem fin_neg_add_cancel {n : Nat} (ha : Fin (n + 1)) : -ha + ha = 0 := by
  apply Fin.ext
  simp [Fin.add_def]

theorem intringmodm_eq_fin {m : ℕ} (hm : m > 0) : IntRingModM m = Fin m := by
  sorry

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

/-
type mismatch
  this
has type
  @Neg.neg (Fin (n + 1)) (Fin.neg (n + 1)) ha + ha = 0 : Prop
but is expected to have type
  @Neg.neg (IntRingModM n.succ) instNegIntRingModM ha + ha = 0 : Prop
-/

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
