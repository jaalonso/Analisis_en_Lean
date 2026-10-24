-- C8_Ejercicio_4.lean
-- Crecimiento lineal de sucesiones estrictamente crecientes.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 24-agosto-2026
-- -----------------------------------------------------------

-- -----------------------------------------------------------
-- Demostrar que si una sucesión σ : ℕ → ℕ es estrictamente
-- creciente, entonces crece al menos linealmente. Es decir,
-- que si
--    ∀ i j, i < j → σ(i) < σ(j)
-- entonces
--    ∀ n, n ≤ σ(n)
-- -----------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Lo demostraremos por inducción en n.
--
-- Caso base: Para n = 0 se tiene que
--    0 ≤ σ(0)
-- porque 0 es el menor número natural.
--
-- Paso de inducción: Supongamos que la propiedad se cumple
-- para n; es decir,
--    n ≤ σ(n)                                            (HI)
-- tenemos que demostrarla para n+1
--    n+1 ≤ σ(n+1)
-- Para ello, basta demostrar que
--    n < σ(n+1)
-- que se prueba con
--    n ≤ σ(n)       [por (HI)]
--      < σ(n+1)     [porque σ es estictamente creciente]

-- Demostraciones con Lean 4
-- =========================

import Mathlib.Tactic

-- 1ª demostración
-- ===============

example
  {σ : ℕ → ℕ}
  (h : ∀ i j, i < j → σ i < σ j) :
  (∀ n, n ≤ σ n) :=
by
  intro n
  -- n : ℕ
  -- ⊢ n ≤ σ n
  induction n with
  | zero =>
    -- ⊢ 0 ≤ σ 0
    exact Nat.zero_le (σ 0)
  | succ n hi =>
    -- n : ℕ
    -- hi : n ≤ σ n
    -- ⊢ n + 1 ≤ σ (n + 1)
    apply Nat.succ_le_of_lt
    -- ⊢ n < σ (n + 1)
    calc n ≤ σ n       := hi
         _ < σ (n + 1) := h n (n + 1) (lt_add_one n)

-- 2ª demostración
-- ===============

example
  {σ : ℕ → ℕ}
  (h : ∀ i j, i < j → σ i < σ j) :
  (∀ n, n ≤ σ n) :=
by
  intro n
  -- n : ℕ
  -- ⊢ n ≤ σ n
  induction n with
  | zero =>
    -- ⊢ 0 ≤ σ 0
    exact Nat.zero_le (σ 0)
  | succ n hi =>
    -- n : ℕ
    -- hi : n ≤ σ n
    -- ⊢ n + 1 ≤ σ (n + 1)
    exact Nat.succ_le_of_lt
            (Nat.lt_of_le_of_lt hi
              (h n (n + 1) (lt_add_one n)))

-- 3ª demostración
-- ===============

example
  {σ : ℕ → ℕ}
  (hσ : ∀ i j, i < j → σ i < σ j) :
  ∀ n, n ≤ σ (n) :=
by
  intro n
  -- n : ℕ
  -- ⊢ n ≤ σ n
  induction n with
  | zero =>
    -- ⊢ 0 ≤ σ 0
    bound
  | succ n hi =>
    -- n : ℕ
    -- hn : n ≤ σ n
    -- ⊢ n + 1 ≤ σ (n + 1)
    have h1 : n < n + 1 := by bound
    specialize hσ n (n + 1) h1
    -- hσ : σ n < σ (n + 1)
    linarith

-- Lemas usados
-- ============

variable (n m k : ℕ)
#check (Nat.lt_of_le_of_lt : n ≤ m → m < k → n < k)
#check (Nat.succ_le_of_lt : n < m → n + 1 ≤ m)
#check (Nat.zero_le n : 0 ≤ n)
#check (lt_add_one n : n < n + 1)
