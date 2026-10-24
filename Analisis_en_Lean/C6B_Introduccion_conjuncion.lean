module

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- ---------------------------------------------------------------------
-- Demostrar que si `x = 2` y adenás `y = 3`, entonces se tiene que
--    x = 2 ∧ y = 3
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (x y : ℝ)
  (hx : x = 2)
  (hy : y = 3)
  : x = 2 ∧ y = 3 :=
And.intro hx hy

-- 2ª demostración
-- ===============

example
  (x y : ℝ)
  (hx : x = 2)
  (hy : y = 3)
  : x = 2 ∧ y = 3 :=
⟨hx, hy⟩

-- 3ª demostración
-- ===============

example
  (x y : ℝ)
  (hx : x = 2)
  (hy : y = 3)
  : x = 2 ∧ y = 3 :=
by
  constructor
  · -- ⊢ x = 2
    exact hx
  · -- hy : y = 3
    exact hy

-- 4ª demostración
-- ===============

example
  (x y : ℝ)
  (hx : x = 2)
  (hy : y = 3)
  : x = 2 ∧ y = 3 :=
by
  split_ands
  · -- ⊢ x = 2
    exact hx
  · -- hy : y = 3
    exact hy

-- 5ª demostración
-- ===============

example
  (x y : ℝ)
  (hx : x = 2)
  (hy : y = 3)
  : x = 2 ∧ y = 3 :=
by
  tauto
