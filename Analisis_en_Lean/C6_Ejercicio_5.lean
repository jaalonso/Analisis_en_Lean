-- C6_Ejercicio_5.lean
-- Generalización del lema del emparedado.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 21-junio-2026
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si las sucesiones a, c y e convergen a L y, para todo
-- n,
--    aₙ ≤ bₙ ≤ cₙ ≤ dₙ ≤ eₙ
-- enconces b y d también converge a L.
-- ---------------------------------------------------------------------

-- Demostraciones con Lean4
-- ========================

module

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
public import Analisis_en_Lean.C6G_Teorema_del_emparedado -- teorema_emparedado

variable (a b c d e : ℕ → ℝ)
variable (L : ℝ)

-- 1ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hc : SeqLim c L)
  (he : SeqLim e L)
  (hab : ∀ n, a n ≤ b n)
  (hbc : ∀ n, b n ≤ c n)
  (hcd : ∀ n, c n ≤ d n)
  (hde : ∀ n, d n ≤ e n)
  : SeqLim b L ∧ SeqLim d L :=
by
  constructor
  · -- ⊢ SeqLim b L
    exact teorema_emparedado a b c L ha hc hab hbc
  · -- ⊢ SeqLim d L
    exact teorema_emparedado c d e L hc he hcd hde

-- 2ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hc : SeqLim c L)
  (he : SeqLim e L)
  (hab : ∀ n, a n ≤ b n)
  (hbc : ∀ n, b n ≤ c n)
  (hcd : ∀ n, c n ≤ d n)
  (hde : ∀ n, d n ≤ e n)
  : SeqLim b L ∧ SeqLim d L :=
⟨teorema_emparedado a b c L ha hc hab hbc,
 teorema_emparedado c d e L hc he hcd hde⟩
