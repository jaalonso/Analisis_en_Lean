-- C9B_Acotacion_de_convergentes.lean
-- Las sucesiones convergentes están acotadas.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 24-agosto-2026
-- -----------------------------------------------------------

-- -----------------------------------------------------------
-- Demostrar que si una sucesión aₙ es convergente, entonces
-- aₙ está acotada; es decir, existe un M ∈ ℝ tal que para
-- todo n ∈ ℕ, |aₙ| ≤ M.
-- -----------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

import Mathlib.Data.Real.Basic
import Analisis_en_Lean.C2_El_calculo_de_pi
import Analisis_en_Lean.C7_Ejercicio_1
import Analisis_en_Lean.C9A_Termino_menor_o_igual_que_suma
import Mathlib.Tactic

open Finset

variable {a : ℕ → ℝ}

def SeqConv (a : ℕ → ℝ) : Prop :=
  ∃ L, SeqLim a L

def SeqBdd (a : ℕ → ℝ) : Prop :=
  ∃ M, ∀ n, |a n| ≤ M

-- 1ª demostración
-- ===============

theorem AcotadaSiConvergente
  (ha : SeqConv a) :
  SeqBdd a :=
by
  obtain ⟨L, hL⟩ := ha
  -- L : ℝ
  -- hL : SeqLim a L
  obtain ⟨N, hN⟩ := hL 1 one_pos
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < 1
  refine ⟨1 + |L| + ∑ k ∈ range N, |a k|, fun n => ?_⟩
  -- n : ℕ
  -- ⊢ |a n| ≤ 1 + |L| + ∑ k ∈ range N, |a k|
  have h1 : 0 ≤ |L| := abs_nonneg L
  have h2 : 0 ≤ ∑ k ∈ range N, |a k| :=
    sum_nonneg (fun i _ => abs_nonneg (a i))
  rcases lt_or_ge n N with hn | hn
  · have h3 : |a n| ≤ ∑ k ∈ range N, |a k| := Termino_menor_o_igual_que_suma a N n hn
    linarith
  · have h4 : |a n| - |L| ≤ |a n - L| := abs_sub_abs_le_abs_sub (a n) L
    have h5 : |a n - L| < 1 := hN n hn
    linarith

-- 2ª demostración
-- ===============

example
  (ha : SeqConv a) :
  SeqBdd a :=
by
  obtain ⟨L, hL⟩ := ha
  -- L : ℝ
  -- hL : SeqLim a L
  obtain ⟨N, hN⟩ := hL 1 one_pos
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < 1
  use 1 + |L| + ∑ k ∈ range N, |a k|
  -- ⊢ ∀ (n : ℕ), |a n| ≤ 1 + |L| + ∑ k ∈ range N, |a k|
  intro n
  -- n : ℕ
  -- ⊢ |a n| ≤ 1 + |L| + ∑ k ∈ range N, |a k|
  have h0 : 0 ≤ |L| := abs_nonneg L
  have h1 : 0 ≤ 1 + |L| := add_nonneg (zero_le_one' ℝ) h0
  have h2 : 0 ≤ ∑ k ∈ range N, |a k| :=
    sum_nonneg (fun i _ => abs_nonneg (a i))
  rcases lt_or_ge n N with hn1 | hn2
  · -- hn1 : n < N
    have h3 : |a n| ≤ ∑ k ∈ range N, |a k| :=
      Termino_menor_o_igual_que_suma a N n hn1
    exact le_add_of_nonneg_of_le h1 h3
  · -- hn2 : N ≤ n
    calc |a n|
         = |a n - L + L|                  := congrArg abs (sub_add_cancel (a n) L).symm
       _ ≤ |a n - L| + |L|                := abs_add_le (a n - L) L
       _ ≤ 1 + |L|                        := add_le_add_left (le_of_lt (hN n hn2)) |L|
       _ ≤ 1 + |L| + ∑ k ∈ range N, |a k| := le_add_of_nonneg_right h2

-- 2ª demostración
-- ===============

example
  (ha : SeqConv a) :
  SeqBdd a :=
by
  obtain ⟨L, h⟩ := ha
  -- L : ℝ
  -- h : SeqLim a L
  by_cases hL : L = 0
  · rewrite [hL] at h
    -- h : SeqLim a 0
    obtain ⟨N, hN⟩ := h 1 (by norm_num)
    -- N : ℕ
    -- hN : ∀ n ≥ N, |a n - 0| < 1
    have h1 : 0 ≤ ∑ k ∈ range N, |a k| :=
      by apply sum_nonneg (by bound)
    use 1 + ∑ k ∈ range N, |a k|
    -- ⊢ ∀ (n : ℕ), |a n| ≤ 1 + ∑ k ∈ range N, |a k|
    intro n
    -- n : ℕ
    -- ⊢ |a n| ≤ 1 + ∑ k ∈ range N, |a k|
    by_cases hn : n < N
    · have h2 : |a n| ≤ ∑ k ∈ range N, |a k| :=
        Termino_menor_o_igual_que_suma a N n hn
      linarith [h2]
    · have hn' : N ≤ n := by bound
      specialize hN n hn'
      ring_nf at hN
      linarith [hN, h1]
  · -- hL : ¬L = 0
    obtain ⟨N, hN⟩ := EventAcotadaSiConvNoCero h hL
    -- N : ℕ
    -- hN : ∀ n ≥ N, |a n| ≤ 2 * |L|
    use 2 * |L| + ∑ k ∈ range N, |a k|
    -- ⊢ ∀ (n : ℕ), |a n| ≤ 2 * |L| + ∑ k ∈ range N, |a k|
    have h1 : ∀ k ∈ range N, 0 ≤ |a k| := by bound
    have h2 : 0 ≤ ∑ k ∈ range N, |a k| := sum_nonneg h1
    intro n
    -- n : ℕ
    -- ⊢ |a n| ≤ 2 * |L| + ∑ k ∈ range N, |a k|
    by_cases hn : N ≤ n
    · -- hn : N ≤ n
      specialize hN n hn
      -- hN : |a n| ≤ 2 * |L|
      linarith [hN, h2]
    · -- hn : ¬N ≤ n
      have hn' : n < N := by bound
      have h3 : |a n| ≤ ∑ k ∈ range N, |a k| :=
        Termino_menor_o_igual_que_suma a N n hn'
      exact le_add_of_nonneg_of_le (by positivity) h3
