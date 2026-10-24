module

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- ---------------------------------------------------------------------
-- Demostrar que si `x = 2 ∨ y = 3`, entonces `(x - 2)(y - 3) = 0`.
-- ---------------------------------------------------------------------

-- 1ª demostración
-- ===============

example
  (x y : ℝ)
  (h : x = 2 ∨ y = 3)
  : (x - 2) * (y - 3) = 0 :=
by
  obtain (h1 | h2) := h
  · -- h1 : x = 2
    rewrite [h1]
    -- ⊢ (2 - 2) * (y - 3) = 0
    simp
  · -- h2 : y = 3
    rewrite [h2]
    -- ⊢ (x - 2) * (3 - 3) = 0
    simp

-- 2ª demostración
-- ===============

example
  (x y : ℝ)
  (h : x = 2 ∨ y = 3)
  : (x - 2) * (y - 3) = 0 :=
by
  rcases h with (h1 | h2)
  · -- h1 : x = 2
    rewrite [h1]
    -- ⊢ (2 - 2) * (y - 3) = 0
    simp
  · -- h2 : y = 3
    rewrite [h2]
    -- ⊢ (x - 2) * (3 - 3) = 0
    simp

-- 3ª demostración
-- ===============

example
  (x y : ℝ)
  (h : x = 2 ∨ y = 3)
  : (x - 2) * (y - 3) = 0 :=
by
  cases h with
  | inl h1 =>
    -- h1 : x = 2
    rewrite [h1]
    -- ⊢ (2 - 2) * (y - 3) = 0
    simp
  | inr h2 =>
    -- h2 : y = 3
    rewrite [h2]
    -- ⊢ (x - 2) * (3 - 3) = 0
    simp

-- 4ª demostración
-- ===============

example
  (x y : ℝ)
  (h : x = 2 ∨ y = 3)
  : (x - 2) * (y - 3) = 0 :=
by
  grind
