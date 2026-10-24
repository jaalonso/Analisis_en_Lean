-- Las_subsucesiones_tienen_el_mismo_limite_que_la_sucesion.lean
-- Las subsucesiones tienen el mismo límite que la sucesión.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 21-septiembre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Una subsucesión se obtiene aplicando a la sucesión original una
-- función de extracción; es decir, una función φ : ℕ → ℕ
-- estrictamente creciente. Por ejemplo, la subsucesión
--    u₀, u₂, u₄, u₆, ...
-- se obtiene con la función de extracción φ definida por
-- φ(n) = 2n.
--
-- Las definiciones anteriores se formalizan en Lean 4 como:
--
--    -- φ es una función de extracción.
--    def IsExtraction (φ : ℕ → ℕ) :=
--      StrictMono φ
--
--    -- v es una subsucesión de u.
--    def Subseq (v u : ℕ → ℝ) :=
--      ∃ φ, IsExtraction φ ∧ v = u ∘ φ
--
--    -- a es el límite de u.
--    def SeqLim (u : ℕ → ℝ) (a : ℝ) :=
--      ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |u n - a| < ε
--
-- Demostrar que toda subsucesión de una sucesión convergente
-- converge al mismo límite que la sucesión.
-- ---------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Usaremos el siguiente lema: Si φ es una función de extracción,
-- entonces
--    ∀ n, n ≤ φ(n)
--
-- Por ser v una subsucesión de u, existe una función de
-- extracción φ tal que
--    v = u ∘ φ                                                (3)
--
-- Tenemos que demostrar que para cada ε > 0, existe un k ∈ ℕ tal
-- que
--     ∀ n ≥ k, |v(n) - a| < ε                                 (1)
--
-- Puesto que a es el límite de u, , existe un k ∈ ℕ tal
-- que
--     ∀ n ≥ k, |u(n) - a| < ε                                 (2)
--
-- Veamos que k verifica (1). Para ello, sea n ≥ k. Entonces,
--    φ(n) ≥ k                                                 (4)
-- ya que
--    φ(n) ≥ n    [por el Lema]
--         ≥ k
-- Luego,
--    |v(n) - a| = |(u ∘ φ )(n) - a|    [por (3)]
--               = |u(φ(n)) - a|
--               < ε                    [por (2) y (4)]

-- Demostraciones con Lean4
-- ========================

import Mathlib.Data.Real.Basic
import Analisis_en_Lean.C2_El_calculo_de_pi

open Nat

variable {u v : ℕ → ℝ}
variable {a : ℝ}

-- φ es una función de extracción.
def IsExtraction (φ : ℕ → ℕ):=
  StrictMono φ

-- v es una subsucesión de u.
def Subseq (v u : ℕ → ℝ) :=
  ∃ φ, IsExtraction φ ∧ v = u ∘ φ

-- 1ª demostración
-- ===============

example
  (hv : Subseq v u)
  (ha : SeqLim u a)
  : SeqLim v a :=
by
  obtain ⟨φ, hφ, hφ'⟩ := hv
  -- φ : ℕ → ℕ
  -- hφ : IsExtraction φ
  -- hφ' : v = u ∘ φ
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |v n - a| < ε
  obtain ⟨k, hk⟩ := ha ε hε
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| < ε
  use k
  -- ⊢ ∀ n ≥ k, |v n - a| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |v n - a| < ε
  have h1 : φ n ≥ k :=
    calc φ n
         ≥ n := StrictMono.le_apply hφ
       _ ≥ k := hn
  calc |v n - a|
       = |(u ∘ φ ) n  - a| := by rw [hφ']
     _ = |u (φ n) - a|     := rfl
     _ < ε                 := hk (φ n) h1

-- 2ª demostración
-- ===============

example
  (hv : Subseq v u)
  (ha : SeqLim u a)
  : SeqLim v a :=
by
  obtain ⟨φ, hφ, rfl⟩ := hv
  -- φ : ℕ → ℕ
  -- hφ : IsExtraction φ
  -- ⊢ SeqLim (u ∘ φ) a
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(u ∘ φ) n - a| < ε
  obtain ⟨k, hk⟩ := ha ε hε
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| < ε
  use k
  -- ⊢ ∀ n ≥ k, |(u ∘ φ) n - a| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |(u ∘ φ) n - a| < ε
  have h1 : φ n ≥ k :=
    calc φ n
         ≥ n := hφ.le_apply
       _ ≥ k := hn
  calc |(u ∘ φ) n  - a|
     _ = |u (φ n) - a|     := rfl
     _ < ε                 := hk (φ n) h1

-- 3ª demostración
-- ===============

example
  (hv : Subseq v u)
  (ha : SeqLim u a)
  : SeqLim v a :=
by
  obtain ⟨φ, hφ, rfl⟩ := hv
  -- φ : ℕ → ℕ
  -- hφ : IsExtraction φ
  -- ⊢ SeqLim (u ∘ φ) a
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(u ∘ φ) n - a| < ε
  obtain ⟨k, hk⟩ := ha ε hε
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| < ε
  use k
  -- ⊢ ∀ n ≥ k, |(u ∘ φ) n - a| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |(u ∘ φ) n - a| < ε
  apply hk
  -- ⊢ φ n ≥ k
  apply le_trans hn
  -- ⊢ n ≤ φ n
  exact hφ.le_apply

-- 4ª demostración
-- ===============

theorem seqLim_of_subseq
  (hv : Subseq v u)
  (ha : SeqLim u a)
  : SeqLim v a :=
by
  obtain ⟨φ, hφ, rfl⟩ := hv
  -- φ : ℕ → ℕ
  -- hφ : IsExtraction φ
  -- ⊢ SeqLim (u ∘ φ) a
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(u ∘ φ) n - a| < ε
  obtain ⟨k, hk⟩ := ha ε hε
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| < ε
  exact ⟨k, fun n hn ↦ hk (φ n) (le_trans hn hφ.le_apply)⟩

-- Lemas usados
-- ============

variable (m n x y z : ℕ)
#check (Nat.zero_le n : 0 ≤ n)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
