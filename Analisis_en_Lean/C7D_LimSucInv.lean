-- C7D_LimSucInv.lean
-- Si aₙ converge a L con L ≠ 0, entonces 1/aₙ converge a 1/L.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 27-junio-2026
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si aₙ converge a L con L ≠ 0, entonces 1/aₙ converge a
-- 1/L.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea bₙ la sucesión definida por
--    ∀ n, bₙ = 1/aₙ                                               (1)
-- Tenemos que demostrar que bₙ converge a 1/L. Para ello, sea ε > 0
-- dado y hay que probar que existe un k tal que
--    ∀ n ≥ k, |bₙ - 1/L| < ε                                      (2)
--
-- Por el teorema exists_half_abs_le_abs_of_seqLim_of_ne_zero,
-- existe k₁ tal que
--    ∀ n ≥ k₁, |aₙ| ≥ |L|/2                                       (3)
--
-- Como L ≠ 0, se tiene que
--    |L| > 0                                                      (4)
-- y, por tanto,
--    ε|L|²/2 > 0.                                                 (5)
-- Por la convergencia de aₙ, existe k₂ tal que
--    ∀ n ≥ k₂, |aₙ - L| < ε|L|²/2                                 (6)
--
-- Sea                                                             (7)
--    k = máx(k₁, k₂).
-- Veamos que se verifica (2). Para ello, sea
--    n ≥ k                                                        (8)
-- Por (6), se tiene
--    n ≥ k₁
-- y, por (3), se tiene
--    |aₙ| ≥ |L|/2                                                 (9)
-- que, junto con (4), asegura que
--    |aₙ| > 0
-- así que
--    aₙ ≠ 0
-- y bₙ = 1/aₙ está bien definido.
--
-- Además, de (7) también se tiene que
--    n ≥ k₂
-- y, por (6), se tiene
--    |aₙ - L| < ε|L|²/2                                          (10)
--
-- Finalmente,
--   |bₙ - 1/L| = |1/aₙ - 1/L|              [por (1)]
--              = |(L - aₙ) / (aₙL)|
--              = |L - aₙ| / |aₙL|
--              = |aₙ - L| / (|aₙ||L|)
--              < (ε|L|²/2) / (|aₙ||L|)     [por (10)]
--              ≤ (ε|L|²/2) / (|L|/2)|L|)   [por (9)]
--              = (ε|L|²/2) / (|L|²/2)
--              = ε.
-- con lo que se prueba (2).

-- Demostraciones con Lean4
-- ========================

module

import Mathlib.Basic.Real.Basic
public import Analisis_en_Lean.C7B_Eventualmente_alejadas_pos -- exists_half_abs_le_abs_of_seqLim_of_ne_zero
import Mathlib.Tactic

set_option linter.privateModule false

variable {a b : ℕ → ℝ}
variable {L : ℝ}

-- 1ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hL : L ≠ 0)
  (hb : ∀ n, b n = 1 / a n)
  : SeqLim b (1 / L) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |b n - 1 / L| < ε
  obtain ⟨k1, hk1⟩ := exists_half_abs_le_abs_of_seqLim_of_ne_zero ha hL
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |L| / 2 ≤ |a n|
  set cota := ε * (|L| ^ 2 / 2)
  obtain ⟨k2, hk2⟩ := ha cota (by positivity)
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |a n - L| < cota
  use max k1 k2
  -- ⊢ ∀ n ≥ max k1 k2, |b n - 1 / L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ ka + k
  -- ⊢ |b n - 1 / L| < ε
  have abs_an_ge_mitad_abs_L : |L| / 2 ≤ |a n| := by grind
  have an_ne_cero : a n ≠ 0 := by grind
  calc |b n - 1/L|
       = |1/(a n) - 1/L|           := by grind
     _ = |(L - a n) / (a n * L)|   := by grind
     _ = |L - a n| / |a n * L|     := by grind
     _ = |a n - L| / (|a n| * |L|) := by grind
     _ < cota / (|a n| * |L|)      := by field_simp ; grind
     _ ≤ cota / ((|L| / 2) * |L|)  := by gcongr
     _ = cota / (|L| ^ 2 / 2)      := by grind
     _ = ε                         := by grind

-- 2ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hL : L ≠ 0)
  (hb : ∀ n, b n = 1 / a n)
  : SeqLim b (1 / L) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |b n - 1 / L| < ε
  set cota := ε * (|L| ^ 2 / 2)
  have abs_L_pos : |L| > 0 := by positivity
  have cota_pos : cota > 0 := by positivity
  obtain ⟨k1, hk1⟩ := exists_half_abs_le_abs_of_seqLim_of_ne_zero ha hL
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |L| / 2 ≤ |a n|
  obtain ⟨k2, hk2⟩ := ha cota cota_pos
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |a n - L| < ε * |L| ^ 2 / 2
  set k := max k1 k2
  use k
  -- ⊢ ∀ n ≥ k, |b n - 1 / L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |b n - 1 / L| < ε
  have n_ge_k1 : n ≥ k1 := le_of_max_le_left hn
  have n_ge_k2 : n ≥ k2 := le_of_max_le_right hn
  have abs_an_ge_mitad_abs_L : |L| / 2 ≤ |a n| := hk1 n n_ge_k1
  have abs_an_pos : |a n| > 0 := by calc
     0 < |L| / 2 := half_pos abs_L_pos
     _ ≤ |a n|   := abs_an_ge_mitad_abs_L
  have an_ne_cero : a n ≠ 0 := abs_pos.mp abs_an_pos
  have abs_dif_an_L_lt_cota : |a n - L| < cota := hk2 n n_ge_k2
  calc |b n - 1/L|
       = |1/(a n) - 1/L| :=
           by congr ; exact hb n
     _ = |(L - a n) / (a n * L)| :=
           by congr ; field_simp
     _ = |L - a n| / |a n * L| :=
           abs_div (L - a n) (a n * L)
     _ = |a n - L| / |a n * L| :=
           by congr 1 ; exact abs_sub_comm L (a n)
     _ = |a n - L| / (|a n| * |L|) :=
           by congr ; exact abs_mul (a n) L
     _ < cota / (|a n| * |L|) :=
           by gcongr
     _ ≤ cota / ((|L| / 2) * |L|) :=
           by gcongr
     _ = cota / (|L| ^ 2 / 2) :=
           by field_simp
     _ = ε :=
           by field

-- 3ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hL : L ≠ 0)
  (hb : ∀ n, b n = 1 / a n)
  : SeqLim b (1 / L) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |b n - 1 / L| < ε
  set cota := ε * (|L| ^ 2 / 2)
  have abs_L_pos : |L| > 0 := by positivity
  have medio_abs_L_pos : |L| / 2 > 0 := half_pos abs_L_pos
  have medio_cuad_abs_L_pos : |L| ^ 2 / 2 > 0 := by positivity
  have cota_pos : cota > 0 := by positivity
  obtain ⟨k1, hk1⟩ := exists_half_abs_le_abs_of_seqLim_of_ne_zero ha hL
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |L| / 2 ≤ |a n|
  obtain ⟨k2, hk2⟩ := ha (cota) cota_pos
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |a n - L| < cota
  set k := max k1 k2
  use k
  -- ⊢ ∀ n ≥ k, |b n - 1 / L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |b n - 1 / L| < ε
  have n_ge_k1 : n ≥ k1 := le_of_max_le_left hn
  have n_ge_k2 : n ≥ k2 := le_of_max_le_right hn
  have cota_inf_abs_a : |L| / 2 ≤ |a n| := hk1 n n_ge_k1
  have abs_an_pos : |a n| > 0 := by calc
    0 < |L| / 2 := medio_abs_L_pos
    _ ≤ |a n|   := cota_inf_abs_a
  have an_ne_cero : a n ≠ 0 := abs_pos.mp abs_an_pos
  have abs_dif_an_L_lt_cota : |a n - L| < cota := hk2 n n_ge_k2
  have prod_abs_pos : |a n| * |L| > 0 := mul_pos abs_an_pos abs_L_pos
  have prod_abs_ge_cota_den : |a n| * |L| ≥ (|L| / 2) * |L| :=
    (mul_le_mul_iff_of_pos_right abs_L_pos).mpr cota_inf_abs_a
  have cota_den_pos : (|L| / 2) * |L| > 0 := mul_pos (half_pos abs_L_pos) abs_L_pos
  have medio_cuad_abs_L_ne_cero : (|L| ^ 2) / 2 ≠ 0 := (ne_of_lt medio_cuad_abs_L_pos).symm
  calc |b n - 1/L|
       = |1/(a n) - 1/L| :=
           by congr ; exact hb n
     _ = |(L - a n) / (a n * L)| :=
           by congr ; field_simp
     _ = |L - a n| / |a n * L| :=
           abs_div (L - a n) (a n * L)
     _ = |a n - L| / |a n * L| :=
           by congr 1 ; exact abs_sub_comm L (a n)
     _ = |a n - L| / (|a n| * |L|) :=
           by congr ; exact abs_mul (a n) L
     _ < cota / (|a n| * |L|) :=
           (div_lt_div_iff_of_pos_right prod_abs_pos).mpr abs_dif_an_L_lt_cota
     _ ≤ cota / ((|L| / 2) * |L|) :=
           (div_le_div_iff_of_pos_left cota_pos prod_abs_pos cota_den_pos).mpr prod_abs_ge_cota_den
     _ = cota / (|L| ^ 2 / 2) :=
           by congr 1 ; ring
     _ = ε :=
           mul_div_cancel_right₀ ε medio_cuad_abs_L_ne_cero

-- 4ª demostración
-- ===============

variable {x y z : ℝ}

lemma RestaFracciones
  (hx : x ≠ 0)
  (hy : y ≠ 0)
  : 1/x - 1/y = (y - x) / (x * y) :=
by
  calc 1/x - 1/y
       = (1 * y - x * 1) / (x * y) := div_sub_div 1 1 hx hy
     _ = (y - x) / (x * y)         := by rw [one_mul, mul_one]

lemma DesigualdadDenominador
  (hx : x > 0)
  (hy : y ≥ z)
  (hz : z > 0)
  : x / y ≤ x / z :=
(div_le_div_iff_of_pos_left hx (lt_of_lt_of_le hz hy) hz).mpr hy

lemma SimplificarDenominador
   : (x / 2) * x = x ^ 2 / 2 :=
by
  calc (x / 2) * x
       = (x * x) / 2 := div_mul_eq_mul_div x 2 x
     _ = x ^ 2 / 2   := congrArg (· / 2) (pow_two x).symm

example
  (ha : SeqLim a L)
  (hL : L ≠ 0)
  (hb : ∀ n, b n = 1 / a n)
  : SeqLim b (1 / L) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |b n - 1 / L| < ε
  set cota := ε * (|L| ^ 2 / 2)
  have abs_L_pos : |L| > 0 := abs_pos.mpr hL
  have medio_abs_L_pos : |L| / 2 > 0 := half_pos abs_L_pos
  have medio_cuad_abs_L_pos : |L| ^ 2 / 2 > 0 := half_pos (sq_pos_of_pos abs_L_pos)
  have cota_pos : cota > 0 := mul_pos hε medio_cuad_abs_L_pos
  obtain ⟨k1, hk1⟩ := exists_half_abs_le_abs_of_seqLim_of_ne_zero ha hL
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |L| / 2 ≤ |a n|
  obtain ⟨k2, hk2⟩ := ha cota cota_pos
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |a n - L| < cota
  set k := max k1 k2
  use k
  -- ⊢ ∀ n ≥ k, |b n - 1 / L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |b n - 1 / L| < ε
  have n_ge_k1 : n ≥ k1 := le_of_max_le_left hn
  have n_ge_k2 : n ≥ k2 := le_of_max_le_right hn
  have cota_inf_abs_a : |L| / 2 ≤ |a n| := hk1 n n_ge_k1
  have abs_an_pos : |a n| > 0 := by calc
    0 < |L| / 2 := medio_abs_L_pos
    _ ≤ |a n|   := cota_inf_abs_a
  have an_ne_cero : a n ≠ 0 := abs_pos.mp abs_an_pos
  have abs_dif_an_L_lt_cota : |a n - L| < cota := hk2 n n_ge_k2
  have prod_abs_pos : |a n| * |L| > 0 := mul_pos abs_an_pos abs_L_pos
  have prod_abs_ge_cota_den : |a n| * |L| ≥ (|L| / 2) * |L| :=
    (mul_le_mul_iff_of_pos_right abs_L_pos).mpr cota_inf_abs_a
  have cota_den_pos : (|L| / 2) * |L| > 0 := mul_pos (half_pos abs_L_pos) abs_L_pos
  have medio_cuad_abs_L_ne_cero : (|L| ^ 2) / 2 ≠ 0 := (ne_of_lt medio_cuad_abs_L_pos).symm
  calc |b n - 1/L|
     = |1/(a n) - 1/L| :=
         congrArg (|· - 1/L|) (hb n)
   _ = |(L - a n) / (a n * L)| :=
         congrArg abs (RestaFracciones an_ne_cero hL)
   _ = |L - a n| / |a n * L| :=
         abs_div (L - a n) (a n * L)
   _ = |a n - L| / (|a n| * |L|) :=
         congrArg₂ (· / ·) (abs_sub_comm L (a n)) (abs_mul (a n) L)
   _ < cota / (|a n| * |L|) :=
         (div_lt_div_iff_of_pos_right prod_abs_pos).mpr abs_dif_an_L_lt_cota
   _ ≤ cota / ((|L| / 2) * |L|) :=
         DesigualdadDenominador cota_pos prod_abs_ge_cota_den cota_den_pos
   _ = cota / ((|L| ^ 2 / 2)) :=
         congrArg (cota / ·) SimplificarDenominador
   _ = ε :=
         mul_div_cancel_right₀ ε medio_cuad_abs_L_ne_cero

-- 5ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hL : L ≠ 0)
  (hb : ∀ n, b n = 1 / a n)
  : SeqLim b (1 / L) := by
  intro ε hε
  let cota := ε * (|L| ^ 2 / 2)
  have cota_pos : cota > 0 := by positivity
  obtain ⟨k1, hk1⟩ := exists_half_abs_le_abs_of_seqLim_of_ne_zero ha hL
  obtain ⟨k2, hk2⟩ := ha cota cota_pos
  use max k1 k2
  intro n hn
  have n_ge_k1 : n ≥ k1 := le_of_max_le_left hn
  have n_ge_k2 : n ≥ k2 := le_of_max_le_right hn
  have abs_an_ge : |L| / 2 ≤ |a n| := hk1 n n_ge_k1
  have abs_dif_lt : |a n - L| < cota := hk2 n n_ge_k2
  have an_ne_cero : a n ≠ 0 := abs_pos.mp (by grind)
  calc |b n - 1 / L|
      = |1 / a n - 1 / L|           := by rw [hb]
    _ = |(L - a n) / (a n * L)|     := by field_simp [an_ne_cero, hL]
    _ = |L - a n| / |a n * L|       := by rw [abs_div]
    _ = |a n - L| / |a n * L|       := by rw [abs_sub_comm]
    _ = |a n - L| / (|a n| * |L|)   := by rw [abs_mul]
    _ < cota / (|a n| * |L|)        := by gcongr
    _ ≤ cota / ((|L| / 2) * |L|)    := by gcongr
    _ = cota / (|L| ^ 2 / 2)        := by ring
    _ = ε                           := by field

-- Lemas usados
-- ============

-- variable (x y z u : ℝ)
-- #check (exists_half_abs_le_abs_of_seqLim_of_ne_zero : SeqLim a L → L ≠ 0 → ∃ k, ∀ n ≥ k, |L| / 2 ≤ |a n|)
-- #check (abs_div x y : |x / y| = |x| / |y|)
-- #check (abs_mul x y : |x * y| = |x| * |y|)
-- #check (abs_pos : 0 < |x| ↔ x ≠ 0)
-- #check (abs_sub_comm x y : |x - y| = |y - x|)
-- #check (div_le_div_iff_of_pos_left : 0 < x → 0 < y → 0 < z → (x / y ≤ x / z ↔ z ≤ y))
-- #check (div_lt_div_iff_of_pos_right : 0 < z → (x / z < y / z ↔ x < y))
-- #check (div_mul_eq_mul_div x y z)
-- #check (div_sub_div x z : y ≠ 0 → u ≠ 0 → x / y - z / u = (x * u - y * z) / (y * u))
-- #check (half_pos : 0 < x → 0 < x / 2)
-- #check (le_of_max_le_left : max x y ≤ z → x ≤ z)
-- #check (le_of_max_le_right : max x y ≤ z → y ≤ z)
-- #check (lt_of_lt_of_le : x < y → y ≤ z → x < z)
-- #check (mul_div_cancel_right₀ x : y ≠ 0 → x * y / y = x)
-- #check (mul_le_mul_iff_of_pos_right : 0 < x → (y * x ≤ z * x ↔ y ≤ z))
-- #check (mul_one x : x * 1 = x)
-- #check (mul_pos : 0 < x → 0 < y → 0 < x * y)
-- #check (ne_of_lt : x < y → x ≠ y)
-- #check (one_mul x : 1 * x = x)
-- #check (pow_two x : x ^ 2 = x * x)
-- #check (sq_pos_of_pos : 0 < x → 0 < x ^ 2)
