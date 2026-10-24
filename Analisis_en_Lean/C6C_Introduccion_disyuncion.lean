import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- ---------------------------------------------------------------------
-- Demostrar que si `y = 3`, entonces se tiene que
--    x = 3 ∨ y = 3
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (x y : ℝ)
  (hy : y = 3)
  : x = 3 ∨ y = 3 :=
Or.inr hy

-- 2ª demostración
-- ===============

example
  (x y : ℝ)
  (hy : y = 3)
  : x = 3 ∨ y = 3 :=
by
  right
  -- ⊢ y = 3
  exact hy

-- 3ª demostración
-- ===============

example
  (x y : ℝ)
  (hy : y = 3)
  : x = 3 ∨ y = 3 :=
by
  tauto
