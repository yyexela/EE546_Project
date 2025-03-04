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

  TODO:
  - Go through and comments proofs and theorems and definitions
  - Renaming functions to be more clear
  - Example repo: https://github.com/klavins/ModGroup
  - Chinese Remainder Theorem
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
