-- C6g_Teorema_del_emparedado.lean
-- Si a y c convergen a L, y b está comprimida entre a y c (es decir,
--   aₙ ≤ bₙ ≤ cₙ para todo n), entonces b también converge a L.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 4-junio-2026
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si las sucesiones a y c convergen a L, y b está
-- comprimida entre a y c (es decir, aₙ ≤ bₙ ≤ cₙ para todo n), entonces
-- b también converge a L.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea ε > 0. Tenemos que demostrar que existe un N tal que,
--    ∀ n ≥ N, |bₙ - L| < ε                                          (1)
--
-- Puesto que a y c convergen a L, existen N₁ y ℕ₂ tales que
--    ∀ n ≥ N₁, |aₙ - L| < ε                                         (2)
--    ∀ n ≥ N₂, |cₙ - L| < ε                                         (3)
-- Sea
--    N = máx(N₁, ℕ₂).                                               (4)
-- Para demostrar (1), sea n ≥ N. Por  (4), se tiene que
--    n ≥ N₁
--    n ≥ N₂
-- Luego, usando (2) y (3), se tiene que
--    |aₙ - L| < ε
--    |cₙ - L| < ε
-- de donde se deduce que
--    - ε < aₙ - L < ε                                               (5)
--    - ε < bₙ - L < ε                                               (6)
-- Luego,
--    -ε < aₙ - L   [por (5)]
--       ≤ bₙ - L   [por hipótesis de b]
--       ≤ cₙ - L   [por hipótesis de b]
--       < ε        [por (6)]
-- Por tanto,
--    -ε < bₙ - L < ε
-- y, finalmente,
--    |bₙ - L| < ε

-- Demostraciones con Lean4
-- ========================

module

import Mathlib.Basic.Real.Basic
public import Analisis_en_Lean.C2_El_calculo_de_pi -- SeqLim
import Mathlib.Tactic

variable (a b c : ℕ → ℝ)
variable (L : ℝ)

-- 1ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hc : SeqLim c L)
  (hab : ∀ n, a n ≤ b n)
  (hbc : ∀ n, b n ≤ c n)
  : SeqLim b L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - L| < ε
  obtain ⟨Na, hNa⟩ := ha ε hε
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε
  obtain ⟨Nc, hNc⟩ := hc ε hε
  -- Nc : ℕ
  -- hNc : ∀ n ≥ Nc, |c n - L| < ε
  exact ⟨max Na Nc, by grind⟩

-- 2ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hc : SeqLim c L)
  (hab : ∀ n, a n ≤ b n)
  (hbc : ∀ n, b n ≤ c n)
  : SeqLim b L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - L| < ε
  have ha : ∃ N, ∀ n ≥ N, |a n - L| < ε := ha ε hε
  have hb : ∃ N, ∀ n ≥ N, |c n - L| < ε := hc ε hε
  obtain ⟨Na, hNa⟩ := ha
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε
  obtain ⟨Nc, hNc⟩ := hb
  -- Nc : ℕ
  -- hNc : ∀ n ≥ Nc, |c n - L| < ε
  use max Na Nc
  -- ⊢ ∀ n ≥ max Na Nc, |b n - L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ max Na Nc
  -- ⊢ |b n - L| < ε
  rewrite [abs_lt]
  -- ⊢ -ε < b n - L ∧ b n - L < ε
  constructor
  · -- ⊢ -ε < b n - L
    calc -ε
       < a n - L := by grind
     _ ≤ b n - L := by grind
  · -- ⊢ b n - L < ε
    calc b n - L
       ≤ c n - L := by grind
     _ < ε       := by grind

-- 3ª demostración
-- ===============

example
    (ha : SeqLim a L)
    (hc : SeqLim c L)
    (hab : ∀ n, a n ≤ b n)
    (hbc : ∀ n, b n ≤ c n) :
    SeqLim b L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - L| < ε
  obtain ⟨Na, hNa⟩ := ha ε hε
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε
  obtain ⟨Nc, hNc⟩ := hc ε hε
  -- Nc : ℕ
  -- hNc : ∀ n ≥ Nc, |c n - L| < ε
  refine ⟨max Na Nc, fun n hn => ?_⟩
  -- n : ℕ
  -- hn : n ≥ max Na Nc
  -- ⊢ |b n - L| < ε
  have hna := hNa n (le_of_max_le_left hn)
  have hnc := hNc n (le_of_max_le_right hn)
  rw [abs_lt] at hna hnc ⊢
  -- hna : -ε < a n - L ∧ a n - L < ε
  -- hnc : -ε < c n - L ∧ c n - L < ε
  -- ⊢ -ε < b n - L ∧ b n - L < ε
  exact ⟨by linarith [hab n], by linarith [hbc n]⟩

-- 4ª demostración
-- ===============

example
    (ha : SeqLim a L)
    (hc : SeqLim c L)
    (hab : ∀ n, a n ≤ b n)
    (hbc : ∀ n, b n ≤ c n)
    : SeqLim b L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - L| < ε
  obtain ⟨Na, hNa⟩ := ha ε hε
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε
  obtain ⟨Nc, hNc⟩ := hc ε hε
  -- Nc : ℕ
  -- hNc : ∀ n ≥ Nc, |c n - L| < ε
  refine ⟨max Na Nc, fun n hn => ?_⟩
  -- n : ℕ
  -- hn : n ≥ max Na Nc
  -- ⊢ |b n - L| < ε
  have hna := hNa n (le_of_max_le_left hn)
  have hnc := hNc n (le_of_max_le_right hn)
  rw [abs_lt] at hna hnc ⊢
  -- hna : -ε < a n - L ∧ a n - L < ε
  -- hnc : -ε < c n - L ∧ c n - L < ε
  -- ⊢ -ε < b n - L ∧ b n - L < ε
  refine ⟨?_, ?_⟩
  · -- ⊢ -ε < b n - L
    calc -ε
         < a n - L := hna.1
       _ ≤ b n - L := by linarith [hab n]
  · calc b n - L
         ≤ c n - L := by linarith [hbc n]
       _ < ε       := hnc.2

-- 5ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hc : SeqLim c L)
  (hab : ∀ n, a n ≤ b n)
  (hbc : ∀ n, b n ≤ c n)
  : SeqLim b L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - L| < ε
  have ha : ∃ N, ∀ n ≥ N, |a n - L| < ε := ha ε hε
  have hb : ∃ N, ∀ n ≥ N, |c n - L| < ε := hc ε hε
  obtain ⟨Na, hNa⟩ := ha
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε
  obtain ⟨Nc, hNc⟩ := hb
  -- Nc : ℕ
  -- hNc : ∀ n ≥ Nc, |c n - L| < ε
  use max Na Nc
  -- ⊢ ∀ n ≥ max Na Nc, |b n - L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ max Na Nc
  -- ⊢ |b n - L| < ε
  have hna : Na ≤ n := le_of_max_le_left hn
  have hnc : Nc ≤ n := le_of_max_le_right hn
  have hNa : |a n - L| < ε := hNa n hna
  have hNc : |c n - L| < ε := hNc n hnc
  rewrite [abs_lt] at hNa
  -- hNa : -ε < a n - L ∧ a n - L < ε
  rewrite [abs_lt] at hNc
  -- hNc : -ε < c n - L ∧ c n - L < ε
  rewrite [abs_lt]
  -- ⊢ -ε < b n - L ∧ b n - L < ε
  constructor
  · -- ⊢ -ε < b n - L
    calc -ε
       < a n - L := hNa.1
     _ ≤ b n - L := by simp only [tsub_le_iff_right, sub_add_cancel, hab]
  · -- ⊢ b n - L < ε
    calc b n - L
       ≤ c n - L := by simp only [tsub_le_iff_right, sub_add_cancel, hbc]
     _ < ε       := hNc.2

-- 6ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hc : SeqLim c L)
  (hab : ∀ n, a n ≤ b n)
  (hbc : ∀ n, b n ≤ c n)
  : SeqLim b L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - L| < ε
  have ha : ∃ N, ∀ n ≥ N, |a n - L| < ε := ha ε hε
  have hb : ∃ N, ∀ n ≥ N, |c n - L| < ε := hc ε hε
  obtain ⟨Na, hNa⟩ := ha
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε
  obtain ⟨Nc, hNc⟩ := hb
  -- Nc : ℕ
  -- hNc : ∀ n ≥ Nc, |c n - L| < ε
  use max Na Nc
  -- ⊢ ∀ n ≥ max Na Nc, |b n - L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ max Na Nc
  -- ⊢ |b n - L| < ε
  have hna : Na ≤ n := le_of_max_le_left hn
  have hnc : Nc ≤ n := le_of_max_le_right hn
  have hNa : |a n - L| < ε := hNa n hna
  have hNc : |c n - L| < ε := hNc n hnc
  rewrite [abs_lt] at hNa
  -- hNa : -ε < a n - L ∧ a n - L < ε
  rewrite [abs_lt] at hNc
  -- hNc : -ε < c n - L ∧ c n - L < ε
  rewrite [abs_lt]
  -- ⊢ -ε < b n - L ∧ b n - L < ε
  split_ands
  · -- ⊢ -ε < b n - L
    have hab : a n ≤ b n := hab n
    linarith
  · -- ⊢ b n - L < ε
    have hbc : b n ≤ c n := hbc n
    linarith

-- 7ª demostración
-- ===============

public theorem teorema_emparedado
  (ha : SeqLim a L)
  (hc : SeqLim c L)
  (hab : ∀ n, a n ≤ b n)
  (hbc : ∀ n, b n ≤ c n)
  : SeqLim b L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, |b n - L| < ε
  obtain ⟨Na, hNa⟩ := ha ε hε
  -- Na : ℕ
  -- hNa : ∀ n ≥ Na, |a n - L| < ε
  obtain ⟨Nc, hNc⟩ := hc ε hε
  -- Nc : ℕ
  -- hNc : ∀ n ≥ Nc, |c n - L| < ε
  refine ⟨max Na Nc, ?_⟩
  -- ⊢ ∀ n ≥ max Na Nc, |b n - L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ max Na Nc
  -- ⊢ |b n - L| < ε
  have hna : n ≥ Na := le_of_max_le_left hn
  have hnc : n ≥ Nc := le_of_max_le_right hn
  have ha' : |a n - L| < ε := hNa n hna
  have hc' : |c n - L| < ε := hNc n hnc
  rw [abs_lt] at ha' hc' ⊢
  -- ⊢ -ε < b n - L ∧ b n - L < ε
  constructor
  · -- ⊢ -ε < b n - L
    have h1 : -ε < a n - L := ha'.1
    have h2 : a n - L ≤ b n - L := by
      linarith [hab n]
    linarith
  · -- ⊢ b n - L < ε
    have h1 : b n - L ≤ c n - L := by
      linarith [hbc n]
    have h2 : c n - L < ε := hc'.2
    linarith

-- Lemas usados
-- ============

-- variable (a b c : ℝ)
-- #check (abs_lt : |a| < b ↔ -b < a ∧ a < b)
-- #check (le_of_max_le_left : max a b ≤ c → a ≤ c)
-- #check (le_of_max_le_right : max a b ≤ c → b ≤ c)
-- #check (sub_add_cancel a b : (a - b) + b = a)
-- #check (tsub_le_iff_right : a - b ≤ c ↔ a ≤ c + b)
