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

import EE546Project.IntRingModM
import EE546Project.Proofs

/-
  Chapter 1: An Introduction to Cryptography
-/

#eval (5: IntRingModM 3)
#check CommRing (IntRingModM 3)
