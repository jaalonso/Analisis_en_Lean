-- T2-El_calculo_de_pi.lean
-- El cálculo de pi.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 10-enero-2026
-- ---------------------------------------------------------------------

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring.RingNF        -- ring_nf

-- ---------------------------------------------------------------------
-- Ejercicio 1. Formalizar la definición de límite de una sucesión; es
-- decir, dada una sucesión (a : ℕ → ℝ) y un número real L ∈ ℝ,
-- decimos que la sucesión a converge a L si para todo ϵ > 0, existe k ∈
-- ℕ tal que, para todo n ≥ k, tenemos |a(n)−L|<ϵ.
-- ---------------------------------------------------------------------

@[expose] public
def SeqLim (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que si a es una sucesión tal que para todo
-- n, a(n) = L, entonces a converge a L.
-- ----------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que para cada ε ∈ ℝ tal que ε > 0, existe un
-- k ∈ ℕ, tal que (∀n ∈ ℕ)[n ≥ k → |a(n) - L| < ε]. Basta tomar k como
-- 0, ya que para todo n ≥ k se tiene
--    |a(n) - L| = |L - L|
--               = |0|
--               = 0
--               < ε

-- Demostraciones con Lean4
-- ========================

variable (a : ℕ → ℝ)
variable (L : ℝ)

-- 1ª demostración
-- ===============

example
  (h : ∀ n, a n = L)
  : SeqLim a L :=
by
  change ∀ ε > 0 , ∃ k : ℕ, ∀ n ≥ k , |a n - L| < ε
  -- ⊢ ∀ ε > 0, ∃ k, ∀ n ≥ k, |a n - L| < ε
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |a n - L| < ε
  use 0
  -- ⊢ ∀ n ≥ 0, |a n - L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ 0
  -- ⊢ |a n - L| < ε
  specialize h n
  -- h : a n = L
  rewrite [h]
  -- ⊢ |L - L| < ε
  ring_nf
  -- ⊢ |0| < ε
  norm_num
  -- ⊢ 0 < ε
  exact hε

-- 2ª demostración
-- ===============

example
  (h : ∀ n, a n = L)
  : SeqLim a L :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ (n : ℕ), n ≥ k → |a n - L| < ε
  use 0
  -- ⊢ ∀ (n : ℕ), n ≥ 0 → |a n - L| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ 0
  -- ⊢ |a n - L| < ε
  show |a n - L| < ε
  calc |a n - L| = |L - L| := by rw [h n]
               _ = |0|     := by {congr ; exact sub_self L}
               _ = 0       := abs_zero
               _ < ε       := hε

-- 3ª demostración
-- ===============

example
  (h : ∀ n, a n = L)
  : SeqLim a L :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ (n : ℕ), n ≥ k → |a n - L| < ε
  use 0
  -- ⊢ ∀ (n : ℕ), n ≥ 0 → |a n - L| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ 0
  -- ⊢ |a n - L| < ε
  show |a n - L| < ε
  calc |a n - L| = 0 := by simp [h n]
               _ < ε := hε

-- 4ª demostración
-- ===============

example
  (h : ∀ n, a n = L)
  : SeqLim a L :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ (n : ℕ), n ≥ k → |a n - L| < ε
  aesop

-- 5ª demostración
-- ===============

example
  (h : ∀ n, a n = L)
  : SeqLim a L :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ (n : ℕ), n ≥ k → |a n - L| < ε
  aesop

-- 6ª demostración
-- ===============

example
  (h : ∀ n, a n = L)
  : SeqLim a L :=
fun ε hε ↦ by aesop

-- Lemas usados
-- ============

-- #check (sub_self a : a - a = 0)
