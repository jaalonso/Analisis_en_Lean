-- C1_Introduccion_a_Lean.lean
-- Introducción a Lean.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 26-noviembre-2025
-- ---------------------------------------------------------------------

-- Este archivo constituye una guía práctica y progresiva sobre el uso
-- de las tácticas más comunes en el asistente de demostración Lean 4. A
-- través de una serie de ejercicios y múltiples variantes de
-- demostración para cada uno, se ilustran los siguientes conceptos:
--
-- 1. Lógica proposicional básica: Uso de `exact`, `apply` y
--    `assumption` para cerrar objetivos basándose en hipótesis
--    directas.
-- 2. Igualdad y simplificación: Introducción a la reflexividad (`rfl`)
--    y a la simplificación automática (`simp`).
-- 3. Reescritura: Técnicas para sustituir términos utilizando
--    igualdades, mediante `rewrite`, `rw` y `subst`.
-- 4. Álgebra: Uso de `ring` y `ring_nf` para la normalización y
--    demostración automática de identidades algebraicas en anillos
--    conmutativos.
-- 5. Cuantificadores:
--    - Existenciales (∃): Construcción de testigos con la táctica `use`.
--    - Universales (∀): Introducción de variables e hipótesis con `intro`.
-- 6. Manipulación de hipótesis: Especialización de proposiciones
--    generales a casos particulares mediante `specialize`.
-- 7. Automatización: Exploración de tácticas potentes de búsqueda y
--    resolución automática como `simp_all`, `aesop` y `solve_by_elim`.
--
-- El archivo concluye con un ejercicio integrador (§ 8) que combina la
-- instanciación de existenciales, la reescritura condicional y la
-- aritmética básica para resolver un problema más complejo.
--
-- Los ejercicios de esta relación son una adaptación del tema 1 del
-- curso "Introduction to formal real analysis" de Alex Kontorovich que
-- se encuentra en https://youtu.be/TN51-1RRenY

import Mathlib.Tactic

variable (x y : ℝ)

-- § 1. Las tácticas `exact`, `apply` y `assumption`
-- =================================================

-- ---------------------------------------------------------------------
-- Ejercicio 1. Suponiendo que x = 5, demostrar que x = 5.
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  (h : x = 5)
  : x = 5 :=
by
  exact h

-- 2ª demostración
example
  (h : x = 5)
  : x = 5 :=
by
  apply h

-- 3ª demostración
example
  (h : x = 5)
  : x = 5 :=
by
  assumption

-- § 2. Las tácticas `rfl` y `simp`
-- ================================

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que
--    x² + 2y = x² + 2y
-- ---------------------------------------------------------------------

-- 1ª demostración
example : x ^ 2 + 2 * y = x ^ 2 + 2 * y :=
by
  rfl

-- 2ª demostración
example : x ^ 2 + 2 * y = x ^ 2 + 2 * y :=
by
  simp

-- § 3. Las táctica `rewrite`, `subst` y `rw`
-- ==========================================

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que si x = 2, entonces
--    x + y = 2 + y
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  (h : x = 2)
  : x + y = 2 + y :=
by
  rewrite [h]
  -- ⊢ 2 + y = 2 + y
  rfl

-- 2ª demostración
example
  (h : x = 2)
  : x + y = 2 + y :=
by
  subst h
  -- ⊢ 2 + y = 2 + y
  rfl

-- 3ª demostración
example
  (h : x = 2)
  : x + y = 2 + y :=
by
  rw [h]

-- 4ª demostración
example
  (h : x = 2)
  : x + y = 2 + y :=
by
  simp [h]

-- § 4. Las tácticas `ring` y `ring_nf`
-- ====================================

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que
--    (x + y)³ = x³ + 3x²y + 3xy² + y³
-- ---------------------------------------------------------------------

-- 1ª demostración
example : (x + y)^3 = x^3 + 3*x^2*y + 3*x*y^2 + y^3 :=
by
  ring

-- 2ª demostración
example : (x + y)^3 = x^3 + 3*x^2*y + 3*x*y^2 + y^3 :=
by
  ring_nf

-- § 5. La táctica `use`
-- =====================

-- ---------------------------------------------------------------------
-- Ejercicio 5. Demostrar que existe un c tal que
--    (x + y)⁴ = x⁴ + 4x³y + cx²y² + 4xy³ + y⁴
-- ---------------------------------------------------------------------

example : ∃ c, (x + y)^4 = x^4 + 4*x^3*y + c*x^2*y^2 + 4*x*y^3 + y^4 :=
by
  use 6
  -- ⊢ (x+y)^4 = x^4 + 4*x^3*y + 6*x^2*y^2 + 4*x*y^3 + y^4
  ring

-- § 6. La táctica `intro`
-- =======================

-- ---------------------------------------------------------------------
-- Ejercicio 6. Demostrar que para todo ε > 0, se tiene que
--    (ε+1)² = (ε+1)²
-- ---------------------------------------------------------------------

example : ∀ ε : ℝ, ε > 0 → (ε + 1) ^ 2 = (ε + 1) ^ 2 :=
by
  intro ε h
  -- ε : ℝ
  -- h : ε > 0
  -- ⊢ (ε + 1) ^ 2 = (ε + 1) ^ 2
  rfl

-- § 7. Las tácticas `specialize`, `simp_all`, `aesop` y `solve_by_elim`
-- =====================================================================

-- ---------------------------------------------------------------------
-- Ejercicio 7. Si para todo x > 0, f(x) = x² y t > 0, entonces f(t) = t².
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  (t : ℝ)
  (ht : t > 0)
  (f : ℝ → ℝ)
  (hf : ∀ x > 0, f x = x ^ 2)
  : f t = t ^ 2 :=
by
  specialize hf t
  -- hf : t > 0 → f t = t ^ 2
  specialize hf ht
  -- hf : f t = t ^ 2
  exact hf

-- 2ª demostración
example
  (t : ℝ)
  (ht : t > 0)
  (f : ℝ → ℝ)
  (hf : ∀ x > 0, f x = x ^ 2)
  : f t = t ^ 2 :=
by
  apply hf
  -- ⊢ t > 0
  exact ht

-- 3ª demostración
-- ===============

example
  (t : ℝ)
  (ht : t > 0)
  (f : ℝ → ℝ)
  (hf : ∀ x > 0, f x = x ^ 2)
  : f t = t ^ 2 :=
by
  exact hf t ht

-- 4ª demostración
-- ===============

example
  (t : ℝ)
  (ht : t > 0)
  (f : ℝ → ℝ)
  (hf : ∀ x > 0, f x = x ^ 2)
  : f t = t ^ 2 :=
by
  rw [hf]
  -- ⊢ t > 0
  exact ht

-- 5ª demostración
-- ===============

example
  (t : ℝ)
  (ht : t > 0)
  (f : ℝ → ℝ)
  (hf : ∀ x > 0, f x = x ^ 2)
  : f t = t ^ 2 :=
by
  simp_all

-- 6ª demostración
-- ===============

example
  (t : ℝ)
  (ht : t > 0)
  (f : ℝ → ℝ)
  (hf : ∀ x > 0, f x = x ^ 2)
  : f t = t ^ 2 :=
by
  aesop

-- 7ª demostración
-- ===============

example
  (t : ℝ)
  (ht : t > 0)
  (f : ℝ → ℝ)
  (hf : ∀ x > 0, f x = x ^ 2)
  : f t = t ^ 2 :=
by
  solve_by_elim

-- § 8. Ejercicio final (y tácticas `choose`, `obtain`, `rcases` y `grind`)
-- ========================================================================

-- ---------------------------------------------------------------------
-- Ejercicio 8. Sea f una función de ℝ en ℝ. Demostrar que si existe un
-- a tal que f(a) = 3 y para todo x > 0 se tiene que f(x+1) = f(x)+9,
-- entonces existe un b tal que para todo y > 0,
--    f(y+1)² = (f(y) + f(b)²)²
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  (f : ℝ → ℝ)
  (h1 : ∃ a : ℝ, f a = 3)
  (h2 : ∀ x > 0, f (x + 1) = f x + 9)
  : ∃ b : ℝ, ∀ y > 0, f (y + 1) ^ 2 = (f y + (f b) ^ 2) ^ 2 :=
by
  choose a ha using h1
  -- a : ℝ
  -- ha : f a = 3
  use a
  -- ⊢ ∀ y > 0, f (y + 1) ^ 2 = (f y + f a ^ 2) ^ 2
  intro y hy
  -- y : ℝ
  -- hy : y > 0
  -- ⊢ f (y + 1) ^ 2 = (f y + f a ^ 2) ^ 2
  specialize h2 y hy
  -- h2 : f (y + 1) = f y + 9
  rewrite [h2]
  -- ⊢ (f y + 9) ^ 2 = (f y + f a ^ 2) ^ 2
  rewrite [ha]
  -- ⊢ (f y + 9) ^ 2 = (f y + 3 ^ 2) ^ 2
  ring_nf

-- 2ª demostración
example
  (f : ℝ → ℝ)
  (h1 : ∃ a : ℝ, f a = 3)
  (h2 : ∀ x > 0, f (x + 1) = f x + 9)
  : ∃ b : ℝ, ∀ y > 0, f (y + 1) ^ 2 = (f y + (f b) ^ 2) ^ 2 :=
by
  obtain ⟨a, ha⟩ := h1
  -- a : ℝ
  -- ha : f a = 3
  use a
  -- ⊢ ∀ y > 0, f (y + 1) ^ 2 = (f y + f a ^ 2) ^ 2
  intro y hy
  -- y : ℝ
  -- hy : y > 0
  -- ⊢ f (y + 1) ^ 2 = (f y + f a ^ 2) ^ 2
  rw [h2 y hy]
  -- ⊢ (f y + 9) ^ 2 = (f y + f a ^ 2) ^ 2
  rw [ha]
  -- ⊢ (f y + 9) ^ 2 = (f y + 3 ^ 2) ^ 2
  norm_num

-- 3ª demostración
example
  (f : ℝ → ℝ)
  (h1 : ∃ a : ℝ, f a = 3)
  (h2 : ∀ x > 0, f (x + 1) = f x + 9)
  : ∃ b : ℝ, ∀ y > 0, f (y + 1) ^ 2 = (f y + (f b) ^ 2) ^ 2 :=
by
  obtain ⟨a, ha⟩ := h1
  -- a : ℝ
  -- ha : f a = 3
  use a
  -- ⊢ ∀ y > 0, f (y + 1) ^ 2 = (f y + f a ^ 2) ^ 2
  grind

-- 4ª demostración
example
  (f : ℝ → ℝ)
  (h1 : ∃ a : ℝ, f a = 3)
  (h2 : ∀ x > 0, f (x + 1) = f x + 9)
  : ∃ b : ℝ, ∀ y > 0, f (y + 1) ^ 2 = (f y + (f b) ^ 2) ^ 2 :=
by
  rcases h1 with ⟨a, ha⟩
  -- a : ℝ
  -- ha : f a = 3
  use a
  -- ⊢ ∀ y > 0, f (y + 1) ^ 2 = (f y + f a ^ 2) ^ 2
  grind
