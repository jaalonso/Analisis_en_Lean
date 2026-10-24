-- C8A_Eventualmente_alejadas.lean
-- Si aₙ → L, entonces |aₙ| ≥ |L|/2 eventualmente.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 24-junio-2026
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si una sucesión es convergente, entonces sus términos
-- están eventualmente acotados inferiormente por la mitad del valor
-- absoluto del límite; es decir, si una sucesión a converge a L con L ≠
-- 0, entonces existe k tal que para todo n ≥ k se tiene que
-- |aₙ| ≥ |L|/2.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Se distinguen dos casos según (L = 0).
--
-- Primer caso: Supongamos que L = 0. Entonces, basta tomar el índice 0
-- ya que
--    ∀ n ≥ 0, |a n| ≥ 0 = |0| / 2 = |L| / 2
--
-- Sefundo caso: Supongamos que L ≠ 0. Entonces se tiene que
--    |L| / 2 > 0
-- y, como a converge a L, existe un k tal que
--    ∀ n ≥ k, |aₙ - L| < |L| / 2                                    (1)
-- Veamos que
--    ∀ n ≥ k, |aₙ| ≥ |L|/2.
-- En efecto, sea n ≥ k. Entonces, por (1),
--    |aₙ - L| < |L| / 2                                             (2)
-- Además,
--    |L| = |aₙ + (L - aₙ)|
--        ≤ |aₙ| + |L - aₙ|
--        = |aₙ| + |-(aₙ - L)|
--        = |aₙ| + |aₙ - L|
--        ≤ |aₙ| + |L| / 2      [por (2)]
-- Luego,
--    |L| ≤ |aₙ| + |L| / 2
-- y, por tanto,
--    |aₙ| ≥ |L|/2

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Analisis_en_Lean.C2_El_calculo_de_pi
import Mathlib.Tactic

variable {a : ℕ → ℝ}
variable {L : ℝ}

-- 1ª demostración
-- ===============

example
  (ha : SeqLim a L)
  : ∃ k, ∀ n ≥ k, |a n| ≥ |L| / 2 :=
by
  by_cases h : L = 0
  · -- h : L = 0
    use 0
    -- ⊢ ∀ n ≥ 0, |a n| ≥ |L| / 2
    grind
  · -- h : ¬L = 0
    obtain ⟨k, hk⟩ := ha (|L| / 2) (by grind)
    -- k : ℕ
    -- hk : ∀ n ≥ k, |a n - L| < |L| / 2
    use k
    -- ⊢ ∀ n ≥ k, |L| / 2 ≤ |a n|
    intro n hn
    -- n : ℕ
    -- hn : n ≥ k
    -- ⊢ |L| / 2 ≤ |a n|
    grind

-- 2ª demostración
-- ===============

example
  (ha : SeqLim a L)
  : ∃ k, ∀ n ≥ k,  |a n| ≥ |L| / 2 :=
by
  by_cases h : L = 0
  · -- h : L = 0
    use 0
    -- ⊢ ∀ n ≥ 0, |a n| ≥ |L| / 2
    grind
  · -- h : ¬L = 0
    obtain ⟨k, hk⟩ := ha (|L| / 2) (by grind)
    -- k : ℕ
    -- hk : ∀ n ≥ k, |a n - L| < |L| / 2
    use k
    -- ⊢ ∀ n ≥ k, |L| / 2 ≤ |a n|
    intro n hn
    -- n : ℕ
    -- hn : n ≥ k
    -- ⊢ |L| / 2 ≤ |a n|
    have h3 : |a n - L| < |L| / 2 := hk n hn
    have h4 : |L| ≤ |a n| + |L| / 2 := by
      calc |L|
           = |a n + (L - a n)|    := by grind
         _ ≤ |a n| + |L - a n|    := by grind
         _ = |a n| + |-(a n - L)| := by grind
         _ = |a n| + |a n - L|    := by grind
         _ ≤ |a n| + |L| / 2      := by grind
    grind

-- 3ª demostración
-- ===============

example
  (ha : SeqLim a L)
  : ∃ k, ∀ n ≥ k, |a n| ≥ |L| / 2 :=
by
  by_cases h : L = 0
  · -- h : L = 0
    use 0
    -- ⊢ ∀ n ≥ 0, |a n| ≥ |L| / 2
    intro n hn
    -- n : ℕ
    -- hn : n ≥ 0
    -- ⊢ |a n| ≥ |L| / 2
    simp [h]
  · -- h : ¬L = 0
    obtain ⟨k, hk⟩ := ha (|L| / 2) (by positivity)
    -- k : ℕ
    -- hk : ∀ n ≥ k, |a n - L| < |L| / 2
    use k
    -- ⊢ ∀ n ≥ k, |L| / 2 ≤ |a n|
    intro n hn
    -- n : ℕ
    -- hn : n ≥ k
    -- ⊢ |L| / 2 ≤ |a n|
    have h3 : |a n - L| < |L| / 2 := hk n hn
    have h4 : |L| ≤ |a n| + |L| / 2 := by
      calc |L|
           = |a n + (L - a n)|    := by ring_nf
         _ ≤ |a n| + |L - a n|    := abs_add_le (a n) (L - a n)
         _ = |a n| + |-(a n - L)| := by ring_nf
         _ = |a n| + |a n - L|    := by congr 1 ; exact abs_neg (a n - L)
         _ ≤ |a n| + |L| / 2      := by gcongr
    linarith [h4]

-- 4ª demostración
-- ===============

example
  (ha : SeqLim a L)
  : ∃ k, ∀ n ≥ k, |a n| ≥ |L| / 2 :=
by
  by_cases h : L = 0
  · -- h : L = 0
    use 0
    -- ⊢ ∀ n ≥ 0, |a n| ≥ |L| / 2
    intro n hn
    -- n : ℕ
    -- hn : n ≥ 0
    -- ⊢ |a n| ≥ |L| / 2
    simp [h]
  · -- h : ¬L = 0
    have h1 : 0 < |L| := abs_pos.mpr h
    have h2 : 0 < |L| / 2 := half_pos h1
    obtain ⟨k, hk⟩ := ha (|L| / 2) h2
    -- k : ℕ
    -- hk : ∀ n ≥ k, |a n - L| < |L| / 2
    use k
    -- ⊢ ∀ n ≥ k, |L| / 2 ≤ |a n|
    intro n hn
    -- n : ℕ
    -- hn : n ≥ k
    -- ⊢ |L| / 2 ≤ |a n|
    have h3 : |a n - L| < |L| / 2 := hk n hn
    have h4 : |L| ≤ |a n| + |L| / 2 := by calc
      |L| = |a n + (L - a n)|    := by ring_nf
        _ ≤ |a n| + |L - a n|    := abs_add_le (a n) (L - a n)
        _ = |a n| + |-(a n - L)| := congrArg (|a n| + |·|) (neg_sub (a n) L).symm
        _ = |a n| + |a n - L|    := congrArg (|a n| + ·) (abs_neg (a n - L))
        _ ≤ |a n| + |L| / 2      := add_le_add_right (le_of_lt h3) |a n|
    calc |L| / 2
         = |L| - |L| / 2 := (sub_half |L|).symm
       _ ≤ |a n|         := tsub_le_iff_right.mpr h4

-- 5ª demostración
-- ===============

lemma EventualmenteMayorIgMitadAbsLimite
  (ha : SeqLim a L)
  : ∃ k, ∀ n ≥ k, |a n| ≥ |L| / 2 :=
by
  by_cases h : L = 0
  · -- h : L = 0
    refine ⟨0, fun _ _ => by grind⟩
  · -- h : ¬L = 0
    obtain ⟨k, hk⟩ := ha (|L| / 2) (by grind)
    -- k : ℕ
    -- hk : ∀ n ≥ k, |a n - L| < |L| / 2
    refine ⟨k, fun _ _ => by grind⟩

-- Lemas usados
-- ============

variable (x y z : ℝ)
#check (abs_add_le x y : |x + y| ≤ |x| + |y|)
#check (abs_neg x : |(-x)| = |x|)
#check (abs_pos : 0 < |x| ↔ x ≠ 0)
#check (add_le_add_right : y ≤ z → ∀ x, x + y ≤ x + z)
#check (half_pos : 0 < x → 0 < x / 2)
#check (neg_sub x y : -(x - y) = y - x)
#check (sub_half x : x - x / 2 = x / 2)
#check (tsub_le_iff_right : x - y ≤ z ↔ x ≤ z + y)
