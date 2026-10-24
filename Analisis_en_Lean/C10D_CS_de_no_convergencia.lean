-- C10D_CS_de_no_convergencia.lean
-- Subsucesiones con límites distintos implican divergencia.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 2-octubre-2026
-- ----------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- La demostración se hará usando dos lemas demostrados en retos
-- anteriores:
-- + El lema seqLim_of_subseq (del Reto 21): toda subsucesión de
--   una sucesión convergente converge al mismo límite que la
--   sucesión.
-- + El lema seqLim_unique (del Reto 9): si una sucesión aₙ
--   converge tanto a L como a M, entonces L = M.
--
-- Para la demostración del reto, supongamos que la sucesión a es
-- convergente. Entonces, por el lema seqLim_of_subseq se tiene
-- que b₁ converge a L y, por el lema seqLim_unique se tiene que
--    L₁ = L
-- Análogamente se tiene que
--    L₂ = L
-- Por tanto L₁ = L₂ en contradicción con la hipótesis L₁ ≠ L₂.

-- Demostraciones en Lean 4
-- ========================

import Mathlib.Data.Real.Basic
import Analisis_en_Lean.C7A_Unicidad_del_limite
import Analisis_en_Lean.C9B_Acotacion_de_convergentes
import Analisis_en_Lean.C10C_Las_subsucesiones_tienen_el_mismo_limite_que_la_sucesion

variable {a b₁ b₂ : ℕ → ℝ}
variable {L L₁ L₂ : ℝ}

-- 1ª demostración
-- ===============

example
  (hb₁ : Subseq b₁ a)
  (hL₁ : SeqLim b₁ L₁)
  (hb₂ : Subseq b₂ a)
  (hL₂ : SeqLim b₂ L₂)
  (h : L₁ ≠ L₂)
  : ¬SucConvergente a :=
by
  intro h1
  -- h1 : SeqConv a
  -- ⊢ False
  obtain ⟨L, hL⟩ := h1
  -- L : ℝ
  -- hL : SeqLim a L
  apply h
  -- ⊢ L₁ = L₂
  have h2 : SeqLim b₁ L := seqLim_of_subseq hb₁ hL
  have h3 : SeqLim b₂ L := seqLim_of_subseq hb₂ hL
  calc L₁ = L  := seqLim_unique hL₁ h2
       _  = L₂ := seqLim_unique h3 hL₂

-- 2ª demostración
-- ===============

example
  (hb₁ : Subseq b₁ a)
  (hL₁ : SeqLim b₁ L₁)
  (hb₂ : Subseq b₂ a)
  (hL₂ : SeqLim b₂ L₂)
  (h : L₁ ≠ L₂)
  : ¬SucConvergente a :=
by
  rintro ⟨L, hL⟩
  -- L : ℝ
  -- hL : SeqLim a L
  -- ⊢ False
  exact h (Eq.trans
           (seqLim_unique hL₁ (seqLim_of_subseq hb₁ hL))
           (seqLim_unique (seqLim_of_subseq hb₂ hL) hL₂))

-- 3ª demostración
-- ===============

theorem not_seqConv_of_subseq_seqLim_ne
  (hb₁ : Subseq b₁ a)
  (hL₁ : SeqLim b₁ L₁)
  (hb₂ : Subseq b₂ a)
  (hL₂ : SeqLim b₂ L₂)
  (h : L₁ ≠ L₂)
  : ¬SucConvergente a :=
by
  rintro ⟨L, hL⟩
  -- L : ℝ
  -- hL : SeqLim a L
  -- ⊢ False
  exact h ((seqLim_unique hL₁ (seqLim_of_subseq hb₁ hL)).trans
           (seqLim_unique (seqLim_of_subseq hb₂ hL) hL₂))
