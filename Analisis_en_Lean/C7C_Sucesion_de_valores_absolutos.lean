-- C7C_Sucesion_de_valores_absolutos.lean
-- Si aₙ converge a L, entonces |aₙ| converge a |L|.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 26-junio-2026
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si aₙ converge a L, entonces |aₙ| converge a |L|.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea bₙ = |aₙ|, para todo n. Tenemos que demostrar que bₙ converge a
-- |L|. Para ello, sea ε > 0 y tenemos que demostrar que existe un k tal
-- que,
--    ∀ n ≥ k, |bₙ - |L|| < ε                                        (1)
--
-- Puesto que aₙ converge a L, existe un k tal que,
--    ∀ n ≥ k, |aₙ - L| < ε                                          (2)
-- Veamos que para dicho k se cumple (1). En efecto, sea
--    n ≥ k.                                                         (3)
-- Entonces,
--    |bₙ - |L|| = ||aₙ| - |L||
--               ≤ |aₙ - L|     [por la desigualdad triangular inversa]
--               < ε            [por (2) y (3)]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Analisis_en_Lean.C2_El_calculo_de_pi
import Mathlib.Tactic

variable {a b : ℕ → ℝ}
variable {L : ℝ}

-- 1ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hb : ∀ n, b n = |a n|)
  : SeqLim b |L| :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |b n - |L|| < ε
  obtain ⟨k, hk⟩ := ha ε hε
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < ε
  use k
  -- ⊢ ∀ n ≥ k, |b n - |L|| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |b n - |L|| < ε
  grind

-- 2ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hb : ∀ n, b n = |a n|)
  : SeqLim b |L| :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |b n - |L|| < ε
  obtain ⟨k, hk⟩ := ha ε hε
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < ε
  refine ⟨k, fun _ _ => by grind⟩

-- 3ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hb : ∀ n, b n = |a n|)
  : SeqLim b |L| :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |b n - |L|| < ε
  obtain ⟨k, hk⟩ := ha ε hε
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < ε
  use k
  -- ⊢ ∀ n ≥ k, |b n - |L|| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |b n - |L|| < ε
  calc |b n - (|L|)|
       = |(|a n|) - (|L|)| := by grind
     _ ≤ |a n - L|         := by grind
     _ < ε                 := by grind

-- 4ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hb : ∀ n, b n = |a n|)
  : SeqLim b |L| :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |b n - |L|| < ε
  obtain ⟨k, hk⟩ := ha ε hε
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < ε
  use k
  -- ⊢ ∀ n ≥ k, |b n - |L|| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |b n - |L|| < ε
  calc |b n - (|L|)|
       = |(|a n|) - (|L|)| := by rw [hb n]
     _ ≤ |a n - L|         := abs_abs_sub_abs_le (a n) L
     _ < ε                 := hk n hn

-- 5ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hb : ∀ n, b n = |a n|)
  : SeqLim b |L| :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |b n - |L|| < ε
  obtain ⟨k, hk⟩ := ha ε hε
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < ε
  use k
  -- ⊢ ∀ n ≥ k, |b n - |L|| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |b n - |L|| < ε
  calc |b n - (|L|)|
       = |(|a n|) - (|L|)| := congrArg (|· - (|L|)|) (hb n)
     _ ≤ |a n - L|         := abs_abs_sub_abs_le (a n) L
     _ < ε                 := hk n hn

-- 6ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hb : ∀ n, b n = |a n|)
  : SeqLim b |L| :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - |L|| < ε
  specialize ha ε hε
  -- ha : ∃ N, ∀ n ≥ N, |a n - L| < ε
  choose k hk using ha
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < ε
  use k
  -- ⊢ ∀ n ≥ k, |b n - |L|| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |b n - |L|| < ε
  specialize hk n hn
  -- hk : |a n - L| < ε
  specialize hb n
  -- hb : b n = |a n|
  rewrite [hb]
  -- ⊢ ||a n| - |L|| < ε
  have : |(|a n|) - (|L|)| ≤ |a n - L| := abs_abs_sub_abs_le (a n) L
  bound

-- Lemas usados
-- ============

variable (x y : ℝ)
#check (abs_abs_sub_abs_le x y : |(|x|) - (|y|)| ≤ |x - y|)
