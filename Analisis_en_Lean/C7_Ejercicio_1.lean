-- C7_Ejercicio_1.lean
-- Si una sucesión converge a un límite no nulo, entonces sus términos
--   están eventualmente acotados superiormente por el doble del valor
--   absoluto del límite.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 16-julio-2026
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si una sucesión converge a un límite no nulo, entonces
-- sus términos están eventualmente acotados superiormente por el doble
-- del valor absoluto del límite; es decir, si una sucesión a converge a
-- L con L ≠ 0, entonces existe k tal que para todo n ≥ k se tiene que
-- |aₙ| ≤ 2|L|.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Puesto que L ≠ 0, se tiene que
--    |L| / 2 > 0
-- y, como a converge a L, existe un k tal que
--    ∀ n ≥ k, |aₙ - L| < |L|                                        (1)
-- Veamos que
--    ∀ n ≥ k, |aₙ| ≤ 2|L|.
-- En efecto, sea n ≥ k. Entonces, por (1),
--    |aₙ - L| < |L|                                                 (2)
-- Además,
--    |aₙ| = |aₙ - L + L|
--         ≤ |aₙ - L| + |L|
--         ≤ |L| + |L|
--         = 2|L|
-- Luego,
--    |aₙ| < 2|L|

-- Demostraciones con Lean4
-- ========================

module

import Mathlib.Basic.Real.Basic
public import Analisis_en_Lean.C2_El_calculo_de_pi -- SeqLim
import Mathlib.Tactic

variable {a : ℕ → ℝ}
variable {L : ℝ}

-- 1ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hL : L ≠ 0)
  : ∃ k, ∀ n ≥ k, |a n| ≤ 2 * |L| :=
by
  have h1 : 0 < |L| := by grind
  obtain ⟨k, hk⟩ := ha |L| h1
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < |L|
  use k
  -- ⊢ ⊢ ∀ n ≥ k, |a n| ≤ 2 * |L|
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |a n| ≤ 2 * |L|
  have h2 : |a n - L| < |L| := hk n hn
  calc |a n|
       = |a n - L + L|   := by grind
     _ ≤ |a n - L| + |L| := by grind
     _ ≤ |L| + |L|       := by grind
     _ = 2 * |L|         := by grind

-- 2ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hL : L ≠ 0)
  : ∃ k, ∀ n ≥ k, |a n| < 2 * |L| :=
by
  obtain ⟨k, hk⟩ := ha |L| (by grind)
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < |L| / 2
  refine ⟨k, fun _ _ => by grind⟩

-- 3ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hL : L ≠ 0)
  : ∃ k, ∀ n ≥ k, |a n| ≤ 2 * |L| :=
by
  have h1 : 0 < |L| := abs_pos.mpr hL
  obtain ⟨k, hk⟩ := ha |L| h1
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < |L|
  use k
  -- ⊢ ⊢ ∀ n ≥ k, |a n| ≤ 2 * |L|
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |a n| ≤ 2 * |L|
  have h2 : |a n - L| < |L| := hk n hn
  calc |a n|
       = |a n - L + L|   := by ring_nf
     _ ≤ |a n - L| + |L| := abs_add_le (a n - L) L
     _ ≤ |L| + |L|       := by gcongr
     _ = 2 * |L|         := by ring_nf

-- 4ª demostración
-- ===============

public theorem EventAcotadaSiConvNoCero
  (ha : SeqLim a L)
  (hL : L ≠ 0)
  : ∃ k, ∀ n ≥ k, |a n| ≤ 2 * |L| := by
  have h1 : 0 < |L| := abs_pos.mpr hL
  obtain ⟨k, hk⟩ := ha |L| h1
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < |L|
  use k
  -- ⊢ ⊢ ∀ n ≥ k, |a n| ≤ 2 * |L|
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |a n| ≤ 2 * |L|
  have h2 : |a n - L| ≤ |L| := le_of_lt (hk n hn)
  calc |a n|
       = |a n - L + L|   := congrArg abs (sub_add_cancel (a n) L).symm
     _ ≤ |a n - L| + |L| := abs_add_le (a n - L) L
     _ ≤ |L| + |L|       := add_le_add_left h2 |L|
     _ = 2 * |L|         := (two_mul |L|).symm

-- Lemas usados
-- ============

-- variable (x y z : ℝ)
-- #check (abs_add_le x y : |x + y| ≤ |x| + |y|)
-- #check (abs_pos : 0 < |x| ↔ x ≠ 0)
-- #check (add_lt_add_iff_right x : y + x < z + x ↔ y < z)
-- #check (sub_add_cancel x y : x - y + y = x)
-- #check (two_mul x : 2 * x = x + x)
