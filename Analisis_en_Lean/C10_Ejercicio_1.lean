-- C10_Ejercicio_1.lean
-- Si la mezcla de dos sucesiones converge a, entonces ambas
--   convergen a L.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 13-octubre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Supongamos que la sucesión cₙ es una mezcla de las sucesiones
-- aₙ y bₙ; es decir, que
--    (c₀, c₁, c₂, ...) = (a₀, b₀, a₁, b₁, a₂, b₂, ...)
--
-- Si cₙ es convergente, entonces aₙ y bₙ también lo son y
-- ambas convergen al mismo límite que cₙ.
--
-- El reto consiste en demostrar que si cₙ converge a L, entonces
-- aₙ y bₙ convergen a L.
--
-- Para ello, completar la siguiente teoría
--    import Mathlib.Tactic
--
--    def SeqLim (a : ℕ → ℝ) (L : ℝ) : Prop :=
--      ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε
--
--    example
--      (hc : ∀ n, c n = if Even n
--                       then a (n / 2)
--                       else b ((n - 1) / 2))
--      (hL : SeqLim c L)
--      : SeqLim a L ∧ SeqLim b L :=
--    by sorry
-- ---------------------------------------------------------------

module

import Mathlib.Tactic
import Analisis_en_Lean.C2_El_calculo_de_pi -- SeqLim

variable {a b c : ℕ → ℝ}
variable {L : ℝ}

-- 1ª demostración
-- ===============

example
  (hc : ∀ n, c n = if Even n
                   then a (n / 2)
                   else b ((n - 1) / 2))
  (hL : SeqLim c L)
  : SeqLim a L ∧ SeqLim b L :=
by
  constructor
  · -- ⊢ SeqLim a L
    intro ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ k, ∀ n ≥ k, |a n - L| < ε
    obtain ⟨k, hk⟩ := hL ε hε
    -- k : ℕ
    -- hk : ∀ n ≥ k, |c n - L| < ε
    use k
    -- ⊢ ∀ n ≥ k, |a n - L| < ε
    intro n hn
    -- n : ℕ
    -- hn : n ≥ k
    -- ⊢ |a n - L| < ε
    calc |a n - L|
         = |c (2 * n) - L| := by grind
       _ < ε               := by grind
  · -- ⊢ SeqLim b L
    intro ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ k, ∀ n ≥ k, |b n - L| < ε
    obtain ⟨k, hk⟩ := hL ε hε
    -- k : ℕ
    -- hk : ∀ n ≥ k, |c n - L| < ε
    use k
    -- ⊢ ∀ n ≥ k, |b n - L| < ε
    intro n hn
    -- n : ℕ
    -- hn : n ≥ k
    -- ⊢ |b n - L| < ε
    calc |b n - L|
         = |c (2 * n + 1) - L| := by grind
       _ < ε                   := by grind

-- 2ª demostración
-- ===============

example
  (hc : ∀ n, c n = if Even n
                   then a (n / 2)
                   else b ((n - 1) / 2))
  (hL : SeqLim c L)
  : SeqLim a L ∧ SeqLim b L :=
by
  constructor
  · -- ⊢ SeqLim a L
    intro ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ k, ∀ n ≥ k, |a n - L| < ε
    obtain ⟨k, hk⟩ := hL ε hε
    -- k : ℕ
    -- hk : ∀ n ≥ k, |c n - L| < ε
    use k
    -- ⊢ ∀ n ≥ k, |a n - L| < ε
    intro n hn
    -- n : ℕ
    -- hn : n ≥ k
    -- ⊢ |a n - L| < ε
    calc |a n - L|
         = |c (2 * n) - L| := by congr 1 ; simp [hc]
       _ < ε               := hk (2 * n) (by omega)
  · -- ⊢ SeqLim b L
    intro ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ k, ∀ n ≥ k, |b n - L| < ε
    obtain ⟨k, hk⟩ := hL ε hε
    -- k : ℕ
    -- hk : ∀ n ≥ k, |c n - L| < ε
    use k
    -- ⊢ ∀ n ≥ k, |b n - L| < ε
    intro n hn
    -- n : ℕ
    -- hn : n ≥ k
    -- ⊢ |b n - L| < ε
    calc |b n - L|
         = |c (2 * n + 1) - L| := by congr 1 ; simp [hc]
       _ < ε                   := hk (2 * n + 1) (by omega)

-- 3ª demostración
-- ===============

private lemma c_even
  (hc : ∀ n, c n = if Even n
                   then a (n / 2)
                   else b ((n - 1) / 2))
  (n : ℕ)
  : c (2 * n) = a n :=
by
  calc c (2 * n)
       = if Even (2 * n)
         then a (2 * n / 2)
         else b ((2 * n - 1) / 2) := hc (2 * n)
     _ = a (2 * n / 2)            := ite_eq_left (even_two_mul n)
     _ = a n                      := by simp

private lemma c_odd
  (hc : ∀ n, c n = if Even n
                   then a (n / 2)
                   else b ((n - 1) / 2))
  (n : ℕ)
  : c (2 * n + 1) = b n :=
by
  calc c (2 * n + 1)
       = if Even (2 * n + 1)
         then a ((2 * n + 1) / 2)
         else b ((2 * n + 1 - 1) / 2)  := hc (2 * n + 1)
     _ = b ((2 * n + 1 - 1) / 2)       := ite_eq_right (Nat.not_even_two_mul_add_one n)
     _ = b n                           := by simp

example
  (hc : ∀ n, c n = if Even n
                   then a (n / 2)
                   else b ((n - 1) / 2))
  (hL : SeqLim c L)
  : SeqLim a L ∧ SeqLim b L :=
by
  constructor
  · intro ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ k, ∀ n ≥ k, |a n - L| < ε
    obtain ⟨k, hk⟩ := hL ε hε
    -- k : ℕ
    -- hk : ∀ n ≥ k, |c n - L| < ε
    use k
    -- ⊢ ∀ n ≥ k, |a n - L| < ε
    intro n hn
    -- n : ℕ
    -- hn : n ≥ k
    -- ⊢ |a n - L| < ε
    calc |a n - L|
         = |c (2 * n) - L| := by rw [c_even hc]
       _ < ε               := hk (2 * n) (by omega)
  · -- ⊢ SeqLim b L
    intro ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ k, ∀ n ≥ k, |b n - L| < ε
    obtain ⟨k, hk⟩ := hL ε hε
    -- k : ℕ
    -- hk : ∀ n ≥ k, |c n - L| < ε
    use k
    -- ⊢ ∀ n ≥ k, |b n - L| < ε
    intro n hn
    -- n : ℕ
    -- hn : n ≥ k
    -- ⊢ |b n - L| < ε
    calc |b n - L|
         = |c (2 * n + 1) - L| := by rw [c_odd hc]
       _ < ε                   := hk (2 * n + 1) (by omega)

-- 4ª demostración
-- ===============

lemma seqLim_comp
  {c : ℕ → ℝ}
  {L : ℝ}
  {f : ℕ → ℕ}
  (hL : SeqLim c L)
  (hf : ∀ n, n ≤ f n)
  : SeqLim (c ∘ f) L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(c ∘ f) n - L| < ε
  obtain ⟨k, hk⟩ := hL ε hε
  -- k : ℕ
  -- hk : ∀ n ≥ k, |c n - L| < ε
  use k
  -- ⊢ ∀ n ≥ k, |(c ∘ f) n - L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |(c ∘ f) n - L| < ε
  have h : k ≤ f n :=
    calc k ≤ n   := hn
         _ ≤ f n := hf n
  calc |(c ∘ f) n - L|
       = |c (f n) - L| := rfl
     _ < ε             := hk (f n) h

example
  (hc : ∀ n, c n = if Even n
                   then a (n / 2)
                   else b ((n - 1) / 2))
  (hL : SeqLim c L)
  : SeqLim a L ∧ SeqLim b L :=
by
  constructor
  · -- ⊢ SeqLim a L
    have ha : a = c ∘ (2 * ·) :=
      funext fun n => (c_even hc n).symm
    rw [ha]
    -- ⊢ SeqLim (c ∘ fun x => 2 * x) L
    exact seqLim_comp (f := (2 * ·)) hL (fun n => by omega)
  · -- ⊢ SeqLim b L
    have hb : b = c ∘ (2 * · + 1) :=
      funext fun n => (c_odd hc n).symm
    rw [hb]
    -- ⊢ SeqLim (c ∘ fun x => 2 * x + 1) L
    exact seqLim_comp (f := (2 * · + 1)) hL (fun n => by omega)
