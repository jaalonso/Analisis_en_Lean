-- C6_Ejercicio_3.lean
-- Si a converge a 5, entonces es eventualmente positiva.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 15-junio-2026
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si la sucesión a converge a 5, entonces es
-- eventualmente positiva; es decir, existe un N tal que para todo n ≥ N
-- se tiene que aₙ > 0.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Puesto que a converge a 5, existe un N ∈ ℕ tal que
--    (∀ n ≥ N) |aₙ - 5| < 5                                          (1)
-- Veamos que
--    (∀ n ≥ N) [aₙ > 0]
-- En efecto, sea n ≥ N. Por (1),
--    |aₙ - 5| < 5
-- Luego,
--    -5 < aₙ - 5 ∧ aₙ - 5 < 5
--    ==> -5 < aₙ - 5
--    ==> aₙ > 0

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Analisis_en_Lean.C2_El_calculo_de_pi

variable {a : ℕ → ℝ}

-- 1ª demostración
-- ===============

example
  (ha : SeqLim a 5)
  : ∃ N, ∀ n ≥ N, 0 < a n :=
by
  obtain ⟨N, hN⟩ := ha 5 (by grind)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - 5| < 5
  refine ⟨N, by grind⟩

-- 2ª demostración
-- ===============

example
  (ha : SeqLim a 5)
  : ∃ N, ∀ n ≥ N, 0 < a n :=
by
  obtain ⟨N, hN⟩ := ha 5 (by norm_num)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - 5| < 5
  use N
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - 5| < 5
  -- ⊢ ∀ n ≥ N, 0 < a n
  grind

-- 3ª demostración
-- ===============

example
  (ha : SeqLim a 5)
  : ∃ N, ∀ n ≥ N, 0 < a n :=
by
  obtain ⟨N, hN⟩ := ha 5 (by norm_num)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - 5| < 5
  use N
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - 5| < 5
  -- ⊢ ∀ n ≥ N, 0 < a n
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ 0 < a n
  linarith [(abs_lt.mp (hN n hn)).1]

-- 4ª demostración
-- ===============

example
  (ha : SeqLim a 5)
  : ∃ N, ∀ n ≥ N, 0 < a n :=
by
  obtain ⟨N, hN⟩ := ha 5 (by norm_num)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - 5| < 5
  use N
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - 5| < 5
  -- ⊢ ∀ n ≥ N, 0 < a n
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ 0 < a n
  have h1 := hN n hn
  -- h1 : |a n - 5| < 5
  have h2 := abs_lt.mp h1
  -- -5 < a n - 5 ∧ a n - 5 < 5
  have h3 := h2.1
  -- h3 : -5 < a n - 5
  exact (lt_add_iff_pos_left (-5)).mp h3

-- 5ª demostración
-- ===============

example
  (ha : SeqLim a 5)
  : ∃ N, ∀ n ≥ N, 0 < a n :=
by
  obtain ⟨N, hN⟩ := ha 5 (by norm_num)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - 5| < 5
  refine ⟨N, fun n hn => (lt_add_iff_pos_left (-5)).mp (abs_lt.mp (hN n hn)).1⟩

-- Aª demostración
-- ===============

example
  (ha : SeqLim a 5)
  : ∃ N, ∀ n ≥ N, 0 < a n :=
by
  have h0 : (0 : ℝ) < 5 := by norm_num
  specialize ha 5 h0
  -- ha : ∃ N, ∀ n ≥ N, |a n - 5| < 5
  choose N hN using ha
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - 5| < 5
  use N
  -- ⊢ ∀ n ≥ N, 0 < a n
  intro n hn
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ 0 < a n
  specialize hN n hn
  -- hN : |a n - 5| < 5
  rewrite [abs_lt] at hN
  -- hN : -5 < a n - 5 ∧ a n - 5 < 5
  linarith [hN.1]
