-- C6_Ejercicio_1.lean
-- Si `x=2`, `y=3` y `z=4`, entonces `x = 2 ∧ y = 3 ∧ z = 4`
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 15-junio-2026
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si `x=2`, `y=3` y `z=4`, entonces
--    x = 2 ∧ y = 3 ∧ z = 4
-- ---------------------------------------------------------------------

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (x y z : ℝ)

-- 1ª demostración
-- ===============

example
  (hx : x = 2)
  (hy : y = 3)
  (hz : z = 4)
  : x = 2 ∧ y = 3 ∧ z = 4 :=
by
  grind

-- 2ª demostración
-- ===============

example
  (hx : x = 2)
  (hy : y = 3)
  (hz : z = 4)
  : x = 2 ∧ y = 3 ∧ z = 4 :=
by
  solve_by_elim

-- 3ª demostración
-- ===============

example
  (hx : x = 2)
  (hy : y = 3)
  (hz : z = 4)
  : x = 2 ∧ y = 3 ∧ z = 4 :=
by
  simp_all

-- 4ª demostración
-- ===============

example
  (hx : x = 2)
  (hy : y = 3)
  (hz : z = 4)
  : x = 2 ∧ y = 3 ∧ z = 4 :=
by
  trivial

-- 5ª demostración
-- ===============

example
  (hx : x = 2)
  (hy : y = 3)
  (hz : z = 4)
  : x = 2 ∧ y = 3 ∧ z = 4 :=
by
  simp [*]

example
  (hx : x = 2)
  (hy : y = 3)
  (hz : z = 4)
  : x = 2 ∧ y = 3 ∧ z = 4 :=
by
  simp only [and_self, hx, hy, hz]

-- 6ª demostración
-- ===============

example
  (hx : x = 2)
  (hy : y = 3)
  (hz : z = 4)
  : x = 2 ∧ y = 3 ∧ z = 4 :=
by
  constructor
  · -- ⊢ x = 2
    exact hx
  · -- ⊢ y = 3 ∧ z = 4
    constructor
    · -- ⊢ y = 3
      exact hy
    · -- ⊢ z = 4
      exact hz

-- 7ª demostración
-- ===============

example
  (hx : x = 2)
  (hy : y = 3)
  (hz : z = 4)
  : x = 2 ∧ y = 3 ∧ z = 4 :=
by
  split_ands
  · -- ⊢ x = 2
    exact hx
  · -- ⊢ y = 3
    exact hy
  · -- ⊢ z = 4
    exact hz

-- 8ª demostración
-- ===============

example
  (hx : x = 2)
  (hy : y = 3)
  (hz : z = 4)
  : x = 2 ∧ y = 3 ∧ z = 4 :=
And.intro hx (And.intro hy hz)

-- 9ª demostración
-- ===============

example
  (hx : x = 2)
  (hy : y = 3)
  (hz : z = 4)
  : x = 2 ∧ y = 3 ∧ z = 4 :=
⟨hx, ⟨hy, hz⟩⟩
