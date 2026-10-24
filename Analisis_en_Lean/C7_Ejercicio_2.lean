-- C7_Ejercicio_2.lean
-- Si las sucesiones aₙ y bₙ convergen a L y M, respectivamente, con
--   L < M, entonces eventualmente aₙ < bₙ; es decir, que existe un
--   k ∈ ℕ tal que, para todo n ≥ k, aₙ < bₙ.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 16-julio-2026
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si las sucesiones aₙ y bₙ convergen a L y M,
-- respectivamente, con L < M, entonces eventualmente aₙ < bₙ; es decir,
-- que existe un k ∈ ℕ tal que, para todo n ≥ k, aₙ < bₙ.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea
--    ε = (M - L) / 2                                                (1)
-- Puesto que L < M, se tiene que ε > 0. Y, usando las convergencias de
-- aₙ y bₙ, se tiene que existen k₁ y k₂ tales que
--    ∀ n ≥ k₁, |aₙ - L| < ε                                         (2)
--    ∀ n ≥ k₂, |bₙ - M| < ε                                         (3)
-- Sea
--    k = máx(k₁, k₂)                                                (4)
-- Veamos que
--    ∀ n ≥ k, aₙ < bₙ
-- Para ello, sea n ∈ ℕ tal que
--    n ≥ k.                                                         (5)
-- Entonces, (4) y (5), se tiene que
--    n ≥ k₁                                                         (6)
--    n ≥ k₂                                                         (7)
-- Veamos que
--    aₙ < (L + M) / 2                                               (8)
-- Efectivamente,
--    aₙ = aₙ - L + L
--       ≤ |aₙ - L| + L
--       < ε + L            [por (2) y (6)]
--       = (M - L) / 2 + L  [por (1)]
--       = (L + M) / 2
-- Veamos también que
--    bₙ > (L + M) / 2                                              (9)
-- Efectivamente
--    bₙ = bₙ - M + M
--        > -ε + M               [por (3) y (7)]
--        = -((M - L) / 2) + M   [por (1)]
--        = (L + M) / 2
-- Finalmente,
--    aₙ < (L + M) / 2  [por (8)]
--       < bₙ           [por (9)]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Analisis_en_Lean.C2_El_calculo_de_pi
import Mathlib.Tactic

variable {a b : ℕ → ℝ}
variable {L M : ℝ}

-- 1ª demostración
-- ===============

example (a b : ℕ → ℝ) (L M : ℝ)
  (ha : SeqLim a L)
  (hb : SeqLim b M)
  (hLM : L < M)
  : ∃ k, ∀ n ≥ k, a n < b n :=
by
  set ε := (M - L) / 2
  obtain ⟨k1, hk1⟩ := ha ε (by grind)
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |a n - L| < ε
  obtain ⟨k2, hk2⟩ := hb ε (by grind)
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |b n - M| < ε
  set k := max k1 k2
  use k
  -- ⊢ ∀ n ≥ k, a n < b n
  grind

-- 2ª demostración
-- ===============

example (a b : ℕ → ℝ) (L M : ℝ)
  (ha : SeqLim a L)
  (hb : SeqLim b M)
  (hLM : L < M)
  : ∃ k, ∀ n ≥ k, a n < b n :=
by
  set ε := (M - L) / 2
  have hε : ε > 0 := by grind
  obtain ⟨k1, hk1⟩ := ha ε hε
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |a n - L| < ε
  obtain ⟨k2, hk2⟩ := hb ε hε
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |b n - M| < ε
  set k := max k1 k2
  use k
  -- ⊢ ∀ n ≥ k, a n < b n
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ a n < b n
  have h1 : n ≥ k1 := by grind
  have h2 : n ≥ k2 := by grind
  have h3 : |a n - L| < ε := by grind
  have h4 : |b n - M| < ε := by grind
  have h5 : a n < (L + M) / 2 := by
    calc a n
         = a n - L + L     := by grind
       _ ≤ |a n - L| + L   := by grind
       _ < ε + L           := by grind
       _ = (M - L) / 2 + L := by grind
       _ = (L + M) / 2     := by grind
  have h6 : b n > (L + M) / 2 := by
    calc b n
         = b n - M + M        := by grind
       _ > -ε + M             := by grind
       _ = -((M - L) / 2) + M := by grind
       _ = (L + M) / 2        := by grind
  calc a n
       < (L + M) / 2     := h5
     _ < b n             := h6

-- 3ª demostración
-- ===============

example (a b : ℕ → ℝ) (L M : ℝ)
  (ha : SeqLim a L)
  (hb : SeqLim b M)
  (hLM : L < M)
  : ∃ k, ∀ n ≥ k, a n < b n :=
by
  set ε := (M - L) / 2
  have hε : ε > 0 := by positivity
  obtain ⟨k1, hk1⟩ := ha ε hε
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |a n - L| < ε
  obtain ⟨k2, hk2⟩ := hb ε hε
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |b n - M| < ε
  set k := max k1 k2
  use k
  -- ⊢ ∀ n ≥ k, a n < b n
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ a n < b n
  have h1 : n ≥ k1 := le_of_max_le_left hn
  have h2 : n ≥ k2 := le_of_max_le_right hn
  have h3 : |a n - L| < ε := hk1 n h1
  have h4 : |b n - M| < ε := hk2 n h2
  have h5 : a n < (L + M) / 2 := by calc
    a n = (a n - L) + L   := by ring
      _ ≤ |a n - L| + L   := add_le_add_left (le_abs_self (a n - L)) L
      _ < ε + L           := by gcongr
      _ = (M - L) / 2 + L := by ring
      _ = (L + M) / 2     := by ring
  have h6 : b n > (L + M) / 2 := by calc
    b n = (b n - M) + M       := by ring
      _ > -ε + M              := (add_lt_add_iff_right M).mpr (neg_lt_of_abs_lt (hk2 n h2))
      _ = -((M - L) / 2) + M  := by ring
      _ = (L + M) / 2         := by ring
  calc a n
       < (L + M) / 2     := h5
     _ < b n             := h6

-- 4ª demostración
-- ===============

example (a b : ℕ → ℝ) (L M : ℝ)
  (ha : SeqLim a L)
  (hb : SeqLim b M)
  (hLM : L < M)
  : ∃ k, ∀ n ≥ k, a n < b n :=
by
  set ε := (M - L) / 2
  have hε : ε > 0 := half_pos (sub_pos.mpr hLM)
  obtain ⟨k1, hk1⟩ := ha ε hε
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |a n - L| < ε
  obtain ⟨k2, hk2⟩ := hb ε hε
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |b n - M| < ε
  set k := max k1 k2
  use k
  -- ⊢ ∀ n ≥ k, a n < b n
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ a n < b n
  have h1 : n ≥ k1 := le_of_max_le_left hn
  have h2 : n ≥ k2 := le_of_max_le_right hn
  have h3 : |a n - L| < ε := hk1 n h1
  have h4 : |b n - M| < ε := hk2 n h2
  have h5 : a n < (L + M) / 2 := by
    calc a n
         = a n - L + L     := (sub_add_cancel (a n) L).symm
       _ < ε + L           := (add_lt_add_iff_right L).mpr (lt_of_abs_lt h3)
       _ = (M - L) / 2 + L := rfl
       _ = (L + M) / 2     := by ring
  have h6 : b n > (L + M) / 2 := by
   calc b n
        = b n - M + M        := (sub_add_cancel (b n) M).symm
      _ > -ε + M             := (add_lt_add_iff_right M).mpr (neg_lt_of_abs_lt h4)
      _ = -((M - L) / 2) + M := rfl
      _ = (L + M) / 2        := by ring
  exact lt_trans h5 h6

-- 5ª demostración
-- ===============

example (a b : ℕ → ℝ) (L M : ℝ)
  (ha : SeqLim a L)
  (hb : SeqLim b M)
  (hLM : L < M)
  : ∃ k, ∀ n ≥ k, a n < b n :=
by
  obtain ⟨k1, hk1⟩ := ha ((M - L) / 2) (by grind)
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |a n - L| < ε
  obtain ⟨k2, hk2⟩ := hb ((M - L) / 2) (by grind)
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |b n - M| < ε
  exact ⟨max k1 k2, fun _ _ => by grind⟩

-- 6ª demostración
-- ===============

example (a b : ℕ → ℝ) (L M : ℝ)
  (ha : SeqLim a L)
  (hb : SeqLim b M)
  (hLM : L < M)
  : ∃ k, ∀ n ≥ k, a n < b n :=
by
  have LneM : M - L ≠ 0 := by bound
  have absML : 0 < |M - L| := abs_pos.mpr LneM
  have MsubL : 0 ≤ M - L := by bound
  have absMLeq : |M - L| = M - L := abs_of_nonneg MsubL
  have absML2 : 0 < |M - L| / 2 := by bound
  specialize ha (|M - L| / 2) absML2
  -- ha : ∃ N, ∀ n ≥ N, |a n - L| < |M - L| / 2
  specialize hb (|M - L| / 2) absML2
  -- hb : ∃ N, ∀ n ≥ N, |b n - M| < |M - L| / 2
  choose k1 hk1 using ha
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |a n - L| < |M - L| / 2
  choose k2 hk2 using hb
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |b n - M| < |M - L| / 2
  use k1 + k2
  -- ⊢ ∀ n ≥ k1 + k2, a n < b n
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k1 + k2
  -- ⊢ a n < b n
  have nk1 : k1 ≤ n := by bound
  have nk2 : k2 ≤ n := by bound
  specialize hk1 n nk1
  -- hk1 : |a n - L| < |M - L| / 2
  specialize hk2 n nk2
  -- hk2 : |b n - M| < |M - L| / 2
  rewrite [abs_lt, absMLeq] at hk1
  -- hk1 : -((M - L) / 2) < a n - L ∧ a n - L < (M - L) / 2
  rewrite [abs_lt, absMLeq] at hk2
  -- hk2 : -((M - L) / 2) < b n - M ∧ b n - M < (M - L) / 2
  linarith [hk1.2, hk2.1]
