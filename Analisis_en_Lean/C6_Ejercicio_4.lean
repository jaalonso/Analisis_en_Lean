-- C6_Ejercicio_4.lean
-- Una sucesión cuyos términos superan 10 infinitas veces no puede
--   converger a un límite de valor absoluto menor que 5.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 15-junio-2026
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que una sucesión que posee infinitos términos con valor
-- absoluto superior a 10 no puede converger a un límite cuyo valor
-- absoluto sea menor que 5. Es decir, si la sucesión aₙ verifica que
--    ∀ N, ∃ n ≥ N, |aₙ| > 10
-- entonces aₙ no puede tener un límite cuyo valor absoluto sea menor
-- que 5.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Para demostrarlo por reducción al absurdo, supongamos que existe un
-- L ∈ ℝ tal que aₙ converge a L y
--    ∣L∣ < 5.                                                      (1)
-- Por la definición de límite, existe N ∈ ℕ tal que
--    ∀ n ≥ N, ∣aₙ − L∣ < 5                                         (2)
-- Por hipótesis sobre la sucesión, para ese mismo N existe tal que se
-- cumplen las siguientes dor relaciones:
--    n ≥ N                                                         (3)
--    ∣aₙ∣ > 10                                                     (4)
-- De (2) y (3) se tiene que
--    ∣aₙ − L∣ < 5                                                  (5)
-- Para obtener una contradicción basta probar que 0 < 0, como se
-- muestra a continuación:
--    0 < ∣aₙ∣              [por (4)]
--      = ∣(aₙ − L) + L∣
--      ≤ ∣aₙ − L∣ + ∣L∣
--      < 5 + 5             [por (5) y (1)]
--      = 10.

-- Demostraciones con Lean4
-- ========================

module

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import Analisis_en_Lean.C2_El_calculo_de_pi -- SeqLim

variable {a : ℕ → ℝ}
variable {L : ℝ}

-- 1ª demostración
-- ===============

example
  (ha : ∀ N, ∃ n ≥ N, |a n| > 10)
  : ¬ ∃ L, SeqLim a L ∧ |L| < 5 :=
by
  intro ⟨L, hL1, hL2⟩
  -- L : ℝ
  -- hL1 : SeqLim a L
  -- hL2 : |L| < 5
  -- ⊢ False
  obtain ⟨N, hN⟩ := hL1 5 (by norm_num)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < 5
  obtain ⟨n, hn, hn10⟩ := ha N
  -- n : ℕ
  -- hn : n ≥ N
  -- hn10 : |a n| > 10
  grind

-- 2ª demostración
-- ===============

example
  (ha : ∀ N, ∃ n ≥ N, |a n| > 10)
  : ¬ ∃ L, SeqLim a L ∧ |L| < 5  :=
by
  intro ⟨L, hL1, hL2⟩
  -- L : ℝ
  -- hL1 : SeqLim a L
  -- hL2 : |L| < 5
  -- ⊢ False
  obtain ⟨N, hN⟩ := hL1 5 (by norm_num)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < 5
  obtain ⟨n, hn1, hn2⟩ := ha N
  -- n : ℕ
  -- hn1 : n ≥ N
  -- hn2 : |a n| > 10
  apply lt_irrefl (10 : ℝ)
  -- ⊢ 10 < 10
  calc 10 < |a n|           := by exact hn2
        _ = |(a n - L) + L| := by grind
        _ ≤ |a n - L| + |L| := by grind
        _ < 5 + 5           := by grind
        _ = 10              := by grind

-- 3ª demostración
-- ===============

example
  (ha : ∀ N, ∃ n ≥ N, |a n| > 10)
  : ¬ ∃ L, SeqLim a L ∧ |L| < 5 :=
by
  intro ⟨L, hL1, hL2⟩
  -- L : ℝ
  -- hL1 : SeqLim a L
  -- hL2 : |L| < 5
  -- ⊢ False
  obtain ⟨N, hN⟩ := hL1 5 (by norm_num)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < 5
  obtain ⟨n, hn, hn10⟩ := ha N
  -- n : ℕ
  -- hn : n ≥ N
  -- hn10 : |a n| > 10
  have h1 : |a n - L| < 5 := hN n hn
  have h2 : |(a n - L) + L| ≤ |a n - L| + |L| := abs_add_le (a n - L) L
  rw [sub_add_cancel] at h2
  -- h2 : |a n| ≤ |a n - L| + |L|
  linarith

-- 4ª demostración
-- ===============

example
  (ha : ∀ N, ∃ n ≥ N, |a n| > 10)
  : ¬ ∃ L, SeqLim a L ∧ |L| < 5 :=
by
  intro ⟨L, hL1, hL2⟩
  -- L : ℝ
  -- hL1 : SeqLim a L
  -- hL2 : |L| < 5
  -- ⊢ False
  obtain ⟨N, hN⟩ := hL1 5 (by norm_num)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < 5
  obtain ⟨n, hn1, hn2⟩ := ha N
  -- n : ℕ
  -- hn1 : n ≥ N
  -- hn2 : |a n| > 10
  apply lt_irrefl (10 : ℝ)
  -- ⊢ 10 < 10
  have h : |a n - L| < 5 := hN n hn1
  calc 10 < |a n|           := by exact hn2
        _ = |(a n - L) + L| := by ring_nf
        _ ≤ |a n - L| + |L| := abs_add_le _ _
        _ < 5 + 5           := by linarith
        _ = 10              := by norm_num

-- 5ª demostración
-- ===============

example
  (ha : ∀ N, ∃ n ≥ N, |a n| > 10)
  : ¬ ∃ L, SeqLim a L ∧ |L| < 5 :=
by
  intro ⟨L, hL1, hL2⟩
  -- L : ℝ
  -- hL1 : SeqLim a L
  -- hL2 : |L| < 5
  -- ⊢ False
  obtain ⟨N, hN⟩ := hL1 5 (by norm_num)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |a n - L| < 5
  obtain ⟨n, hn1, hn2⟩ := ha N
  -- n : ℕ
  -- hn1 : n ≥ N
  -- hn2 : |a n| > 10
  apply lt_irrefl (10 : ℝ)
  -- ⊢ 10 < 10
  have h : |a n - L| < 5 := hN n hn1
  calc 10 < |a n|           := by exact hn2
        _ = |(a n - L) + L| := by rw [sub_add_cancel]
        _ ≤ |a n - L| + |L| := abs_add_le (a n - L) L
        _ < 5 + 5           := add_lt_add h hL2
        _ = 10              := by norm_num

-- Lemas usados
-- ============

variable (a b c d: ℝ)
#check (abs_add_le a b : |a + b| ≤ |a| + |b|)
#check (add_lt_add : a < b → c < d → a + c < b + d)
#check (lt_irrefl a : ¬a < a)
#check (sub_add_cancel a b : (a - b) + b = a)
