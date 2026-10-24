module

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- ---------------------------------------------------------------------
-- Demostrar que si `x = 2 ∧ y = 3`, entonces `y = 3`.
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (x y : ℝ)
  (h : x = 2 ∧ y = 3)
  : y = 3 :=
h.right

-- 2ª demostración
-- ===============

example
  (x y : ℝ)
  (h : x = 2 ∧ y = 3)
  : y = 3 :=
h.2

-- 3ª demostración
-- ===============

example
  (x y : ℝ)
  (h : x = 2 ∧ y = 3)
  : y = 3 :=
by
  exact h.2

-- 4ª demostración
-- ===============

example
  (x y : ℝ)
  (h : x = 2 ∧ y = 3)
  : y = 3 :=
by
  tauto
