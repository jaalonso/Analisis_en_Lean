-- C8B_Crecimieto_exponencial.lean
-- Para todo n ∈ ℕ, n < 2ⁿ
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 6-agosto-2026
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que, para todo número natural n,
--    n < 2ⁿ
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por inducción en n.
--
-- Caso base: Para n = 0 se tiene:
--    n = 0 < 1 = 2⁰ = 2ⁿ
--
-- Paso inductivo: Suponiendo la hipótesis de inducción
--   k < 2ᵏ                                             (HI)
-- tenemos que demostrar que
--   k+1 < 2ᵏ⁺¹
-- La demostración es
--    k + 1 ≤ k + 2ᵏ
--          < 2ᵏ + 2ᵏ    [por la HI]
--          = 2 · 2ᵏ
--          = 2ᵏ⁺¹

-- Demostraciones con Lean 4
-- =========================

module

import Mathlib.Tactic

variable (n : ℕ)

open Nat

-- 1ª demostración
-- ===============

example : n < 2 ^ n :=
by
  induction n with
  | zero =>
    -- ⊢ 0 < 2 ^ 0
    grind
  | succ k HI =>
    -- k : ℕ
    -- HI : k < 2 ^ k
    -- ⊢ k + 1 < 2 ^ (k + 1)
    grind

-- 2ª demostración
-- ===============

example : n < 2 ^ n :=
by
  induction n with
  | zero =>
    -- ⊢ 0 < 2 ^ 0
    grind
  | succ k HI =>
    -- k : ℕ
    -- HI : k < 2 ^ k
    -- ⊢ k + 1 < 2 ^ (k + 1)
    calc k + 1
         ≤ k + 2 ^ k     := by grind
    _    < 2 ^ k + 2 ^ k := by grind
    _    = 2 * 2 ^ k     := by grind
    _    = 2 ^ (k + 1)   := by grind

-- 3ª demostración
-- ===============

example : n < 2 ^ n :=
by
  induction n with
  | zero =>
    -- ⊢ 0 < 2 ^ 0
    norm_num
  | succ k HI =>
    -- k : ℕ
    -- HI : k < 2 ^ k
    -- ⊢ k + 1 < 2 ^ (k + 1)
    calc k + 1
         ≤ k + 2 ^ k     := by gcongr ; exact Nat.one_le_two_pow
    _    < 2 ^ k + 2 ^ k := by gcongr
    _    = 2 * 2 ^ k     := by ring
    _    = 2 ^ (k + 1)   := by rw [← pow_succ']

-- 4ª demostración
-- ===============

example : n < 2 ^ n :=
by
  induction n with
  | zero =>
    -- ⊢ 0 < 2 ^ 0
    exact Nat.two_pow_pos 0
  | succ k HI =>
    -- k : ℕ
    -- HI : k < 2 ^ k
    -- ⊢ k + 1 < 2 ^ (k + 1)
    calc k + 1
         ≤ k + 2 ^ k     := (add_le_add_iff_left k).mpr Nat.one_le_two_pow
    _    < 2 ^ k + 2 ^ k := (add_lt_add_iff_right (2 ^ k)).mpr HI
    _    = 2 * 2 ^ k     := (two_mul (2 ^ k)).symm
    _    = 2 ^ (k + 1)   := pow_succ'.symm

-- 5ª demostración
-- ===============

example : n < 2 ^ n :=
by
  induction n with
  | zero =>
    -- ⊢ 0 < 2 ^ 0
    exact Nat.two_pow_pos 0
  | succ k HI =>
    -- k : ℕ
    -- HI : k < 2 ^ k
    -- ⊢ k + 1 < 2 ^ (k + 1)
    apply Nat.lt_of_lt_of_le
    · -- k + 1 < 2 ^ k + 1
      exact Nat.add_lt_add_right HI 1
    · -- 2 ^ k + 1 ≤ 2 ^ (k + 1)
      have h : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_succ (one_lt_two)
      exact add_one_le_iff.mpr h

-- 6ª demostración
-- ===============

example : n < 2 ^ n :=
by
  induction n with
  | zero =>
    -- ⊢ 0 < 2 ^ 0
    exact Nat.two_pow_pos 0
  | succ k HI =>
    -- k : ℕ
    -- HI : k < 2 ^ k
    -- ⊢ k + 1 < 2 ^ (k + 1)
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right HI 1)
                             (add_one_le_iff.mpr (Nat.pow_lt_pow_succ (one_lt_two)))

-- 7ª demostración
-- ===============

example : n < 2 ^ n :=
Nat.lt_two_pow_self

-- Lemas usados
-- ============

-- variable (k m : ℕ)
-- #check (Nat.add_le_add_iff_left : n + m ≤ n + k ↔ m ≤ k)
-- #check (Nat.add_lt_add_iff_right : n + k < m + k ↔ n < m)
-- #check (Nat.add_lt_add_right : n < m → ∀ k, n + k < m + k)
-- #check (Nat.lt_of_lt_of_le : n < m → m ≤ k → n < k)
-- #check (Nat.lt_two_pow_self : n < 2 ^ n)
-- #check (Nat.one_le_two_pow : 1 ≤ 2 ^ n)
-- #check (Nat.one_lt_two : 1 < 2)
-- #check (Nat.pow_lt_pow_succ : 1 < k → k ^ n < k ^ (n + 1))
-- #check (Nat.two_mul n : 2 * n = n + n)
-- #check (Nat.two_pow_pos n : 0 < 2 ^ n)
-- #check (pow_succ' : m ^ n.succ = m * m ^ n)
