-- C6_Ejercicio_2.lean
-- Si `x = 2 ∧ y = 3 ∧ z = 4`, entonces `z=4`.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 15-junio-2026
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si `x = 2 ∧ y = 3 ∧ z = 4`, entonces `z=4`.
-- ---------------------------------------------------------------------

module

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

variable (x y z : ℝ)

-- 1ª demostración
-- ===============

example
  (h : x = 2 ∧ y = 3 ∧ z = 4)
  : z = 4 :=
by
  grind

-- 2ª demostración
-- ===============

example
  (h : x = 2 ∧ y = 3 ∧ z = 4)
  : z = 4 :=
by
  simp_all

-- 3ª demostración
-- ===============

example
  (h : x = 2 ∧ y = 3 ∧ z = 4)
  : z = 4 :=
by
  simp [*]

-- 4ª demostración
-- ===============

example
  (h : x = 2 ∧ y = 3 ∧ z = 4)
  : z = 4 :=
by
  simp only [h]

-- 4ª demostración
-- ===============

example
  (h : x = 2 ∧ y = 3 ∧ z = 4)
  : z = 4 :=
h.2.2
