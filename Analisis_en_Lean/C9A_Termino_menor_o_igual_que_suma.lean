-- C9A_Termino_menor_o_igual_que_suma.lean
-- Para todo n < N, |a(n)| es menor o igual que la suma de
--   los |a(k)| para k de 0 a N-1.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 24-agosto-2026
-- -----------------------------------------------------------

-- -----------------------------------------------------------
-- Sea (a : ℕ → ℝ) una sucesión y N un número
-- natural. Demostrar que para todo n < N:
--    |a(n)| ≤ ∑_{k=0}^{N-1} |a(k)|
-- -----------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por inducción en N.
--
-- Base: Para N = 0,
--    ∀ n < 0, |a n| ≤ ∑ k ∈ range 0, |a k|
-- se verifica porque no hay ningún número natural menor que
-- 0.
--
-- Paso de inducción: Supongamos que N verifica la propiedad;
--es decir,
--    ∀ n < N, |a n| ≤ ∑ k ∈ range N, |a k|               (HI)
-- Tenmos que demostrar que
--    ∀ n < N + 1, |a n| ≤ ∑ k ∈ range (N + 1), |a k|
-- Sea n ∈ ℕ tal que
--    n < N + 1                                            (1)
-- Tenemos que demostrar que
--    |a n| ≤ ∑ k ∈ range (N + 1), |a k|
-- que se reduce a
--    |a n| ≤ ∑ k ∈ range N, |a k| + |a N|                 (2)
-- Lo probaremos distinguiendo casos según que n < N.
--
-- 1ª caso: Supongamos que
--    n < N,                                               (3)
-- entonces
--    |a n| ≤ ∑ k ∈ range N, |a k|         [por (HI) y (3)]
--          ≤ ∑ k ∈ range N, |a k| + |a N|
--
-- 2ª caso: Supongamos que
--    ¬(n < N),                                            (4)
-- entonces, por (1) y (4), la (2) se transforma en
--    |a N| ≤ ∑ k ∈ range N, |a k| + |a N|
-- Cuya demostración se reduce a
--    0 ≤ ∑ k ∈ range N, |a k|
-- que se verifica puesto que
--    ∀ i ∈ range N, 0 ≤ |a i|

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Finset

-- 1ª demostración
-- ===============

example
  (a : ℕ → ℝ)
  (N : ℕ) :
  ∀ n < N, |a n| ≤ ∑ k ∈ range N, |a k| :=
by
  induction N with
  | zero =>
    -- ⊢ ∀ n < 0, |a n| ≤ ∑ k ∈ range 0, |a k|
    intro n hn
    -- n : ℕ
    -- hn : n < 0
    -- ⊢ |a n| ≤ ∑ k ∈ range 0, |a k|
    contradiction
  | succ N hi =>
    -- N : ℕ
    -- hi : ∀ n < N, |a n| ≤ ∑ k ∈ range N, |a k|
    -- ⊢ ∀ n < N + 1, |a n| ≤ ∑ k ∈ range (N + 1), |a k|
    intro n hn
    -- n : ℕ
    -- hn : n < N + 1
    -- ⊢ |a n| ≤ ∑ k ∈ range (N + 1), |a k|
    simp only [sum_range_succ]
    -- ⊢ |a n| ≤ ∑ k ∈ range N, |a k| + |a N|
    by_cases hn' : n < N
    · -- hn' : n < N
      calc |a n|
         _ ≤ ∑ k ∈ range N, |a k|         := hi n hn'
         _ ≤ ∑ k ∈ range N, |a k| + |a N| := by bound
    · -- hn' : ¬n < N
      have h2 : n = N := by bound
      rewrite [h2]
      -- ⊢ |a N| ≤ ∑ k ∈ range N, |a k| + |a N|
      apply le_add_of_nonneg_left
      -- ⊢ 0 ≤ ∑ k ∈ range N, |a k|
      apply sum_nonneg
      -- ⊢ ∀ i ∈ range N, 0 ≤ |a i|
      bound

-- 2ª demostración
-- ===============

example
  (a : ℕ → ℝ)
  (N : ℕ) :
  ∀ n < N, |a n| ≤ ∑ k ∈ range N, |a k| :=
by
  induction N with
  | zero =>
    -- ⊢ ∀ n < 0, |a n| ≤ ∑ k ∈ range 0, |a k|
    intro n hn
    -- n : ℕ
    -- hn : n < 0
    -- ⊢ |a n| ≤ ∑ k ∈ range 0, |a k|
    contradiction
  | succ N hi =>
    -- N : ℕ
    -- hi : ∀ n < N, |a n| ≤ ∑ k ∈ range N, |a k|
    -- ⊢ ∀ n < N + 1, |a n| ≤ ∑ k ∈ range (N + 1), |a k|
    intro n hn
    -- n : ℕ
    -- hn : n < N + 1
    -- ⊢ |a n| ≤ ∑ k ∈ range (N + 1), |a k|
    simp only [sum_range_succ]
    -- ⊢ |a n| ≤ ∑ k ∈ range N, |a k| + |a N|
    by_cases hn' : n < N
    · -- hn' : n < N
      calc |a n|
         _ ≤ ∑ k ∈ range N, |a k|         := hi n hn'
         _ ≤ ∑ k ∈ range N, |a k| + |a N| := le_add_of_nonneg_right (abs_nonneg (a N))
    · -- hn' : ¬n < N
      have h2 : n = N := Nat.eq_of_lt_succ_of_not_lt hn hn'
      rewrite [h2]
      -- ⊢ |a N| ≤ ∑ k ∈ range N, |a k| + |a N|
      apply le_add_of_nonneg_left
      -- ⊢ 0 ≤ ∑ k ∈ range N, |a k|
      apply sum_nonneg
      -- ⊢ ∀ i ∈ range N, 0 ≤ |a i|
      intro i hir
      -- i : ℕ
      -- hir : i ∈ range N
      -- ⊢ 0 ≤ |a i|
      exact abs_nonneg (a i)

-- 3ª demostración
-- ===============

example
  (a : ℕ → ℝ)
  (N : ℕ) :
  ∀ n < N, |a n| ≤ ∑ k ∈ range N, |a k| :=
by
  induction N with
  | zero =>
    -- ⊢ ∀ n < 0, |a n| ≤ ∑ k ∈ range 0, |a k|
    intro n hn
    -- n : ℕ
    -- hn : n < 0
    -- ⊢ |a n| ≤ ∑ k ∈ range 0, |a k|
    contradiction
  | succ N hi =>
    -- N : ℕ
    -- hi : ∀ n < N, |a n| ≤ ∑ k ∈ range N, |a k|
    -- ⊢ ∀ n < N + 1, |a n| ≤ ∑ k ∈ range (N + 1), |a k|
    intro n hn
    -- n : ℕ
    -- hn : n < N + 1
    -- ⊢ |a n| ≤ ∑ k ∈ range (N + 1), |a k|
    simp only [sum_range_succ]
    -- ⊢ |a n| ≤ ∑ k ∈ range N, |a k| + |a N|
    by_cases hn' : n < N
    · -- hn' : n < N
      calc |a n|
         _ ≤ ∑ k ∈ range N, |a k|         := hi n hn'
         _ ≤ ∑ k ∈ range N, |a k| + |a N| := le_add_of_nonneg_right (abs_nonneg (a N))
    · -- hn' : ¬n < N
      have h2 : n = N := Nat.eq_of_lt_succ_of_not_lt hn hn'
      rewrite [h2]
      -- ⊢ |a N| ≤ ∑ k ∈ range N, |a k| + |a N|
      exact le_add_of_nonneg_left (sum_nonneg (fun i _ => abs_nonneg (a i)))

-- 4ª demostración
-- ===============

example
  (a : ℕ → ℝ)
  (N : ℕ) :
  ∀ n < N, |a n| ≤ ∑ k ∈ range N, |a k| :=
by
  induction N with
  | zero =>
    -- ⊢ ∀ n < 0, |a n| ≤ ∑ k ∈ range 0, |a k|
    intro n hn
    -- n : ℕ
    -- hn : n < 0
    -- ⊢ |a n| ≤ ∑ k ∈ range 0, |a k|
    contradiction
  | succ N hi =>
    -- N : ℕ
    -- hi : ∀ n < N, |a n| ≤ ∑ k ∈ range N, |a k|
    -- ⊢ ∀ n < N + 1, |a n| ≤ ∑ k ∈ range (N + 1), |a k|
    intro n hn
    -- n : ℕ
    -- hn : n < N + 1
    -- ⊢ |a n| ≤ ∑ k ∈ range (N + 1), |a k|
    simp only [sum_range_succ]
    -- ⊢ |a n| ≤ ∑ k ∈ range N, |a k| + |a N|
    by_cases hn' : n < N
    · -- hn' : n < N
      calc |a n|
         _ ≤ ∑ k ∈ range N, |a k|         := hi n hn'
         _ ≤ ∑ k ∈ range N, |a k| + |a N| := le_add_of_nonneg_right (abs_nonneg (a N))
    · -- hn' : ¬n < N
      exact (Nat.eq_of_lt_succ_of_not_lt hn hn') ▸
        le_add_of_nonneg_left (sum_nonneg (fun i _ => abs_nonneg (a i)))

-- 5ª demostración
-- ===============

example
  (a : ℕ → ℝ)
  (N : ℕ) :
  ∀ n < N, |a n| ≤ ∑ k ∈ range N, |a k| :=
by
  induction N with
  | zero =>
    -- ⊢ ∀ n < 0, |a n| ≤ ∑ k ∈ range 0, |a k|
    intro n hn
    -- n : ℕ
    -- hn : n < 0
    -- ⊢ |a n| ≤ ∑ k ∈ range 0, |a k|
    contradiction
  | succ N hi =>
    -- N : ℕ
    -- hi : ∀ n < N, |a n| ≤ ∑ k ∈ range N, |a k|
    -- ⊢ ∀ n < N + 1, |a n| ≤ ∑ k ∈ range (N + 1), |a k|
    intro n hn
    -- n : ℕ
    -- hn : n < N + 1
    -- ⊢ |a n| ≤ ∑ k ∈ range (N + 1), |a k|
    have h1 : ∑ k ∈ range (N + 1), |a k| = (∑ k ∈ range N, |a k|) + |a N| :=
      by apply sum_range_succ
    rewrite [h1]
    -- ⊢ |a n| ≤ ∑ k ∈ range N, |a k| + |a N|
    by_cases hn' : n < N
    · -- hn' : n < N
      specialize hi n hn'
      -- hi : |a n| ≤ ∑ k ∈ range N, |a k|
      have h1' : 0 ≤ |a N| := by bound
      linarith [h1', hi]
    · -- hn' : ¬n < N
      have h2 : n = N := by bound
      rewrite [h2]
      -- ⊢ |a N| ≤ ∑ k ∈ range N, |a k| + |a N|
      have h3 : ∀ k ∈ range N, 0 ≤ |a k| := by bound
      have h4 : 0 ≤ ∑ k ∈ range N, |a k| := by apply sum_nonneg h3
      linarith [h4]

-- 6ª demostración
-- ===============

example
  (a : ℕ → ℝ)
  (N : ℕ) :
  ∀ n < N, |a n| ≤ ∑ k ∈ range N, |a k| :=
by
  intro n hn
  -- n : ℕ
  -- hn : n < N
  -- ⊢ |a n| ≤ ∑ k ∈ range N, |a k|
  apply single_le_sum (fun i _ => abs_nonneg (a i))
  -- ⊢ n ∈ range N
  exact mem_range.mpr hn

-- 7ª demostración
-- ===============

theorem Termino_menor_o_igual_que_suma
  (a : ℕ → ℝ)
  (N : ℕ) :
  ∀ n < N, |a n| ≤ ∑ k ∈ range N, |a k| :=
fun _ hn => single_le_sum (fun i _ => abs_nonneg (a i)) (mem_range.mpr hn)
