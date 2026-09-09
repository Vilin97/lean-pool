/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SlotGeometry
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity.Finset

/-!
# Physical grid labels, bounded degree, and an explicit finite coloring

Labels consist of a dyadic level, three integer grid coordinates, and a sign.
The physical mesh at exponent `a` is `2^(-n*a)/n^6`, namely the mesh
`S_n^-3` with `S_n=n²`, rescaled by `Q_n^a` with `Q_n=2^-n`.
Closed boxes of two mesh widths include the fixed small enlargement of the
one-mesh supports in the manuscript.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.SlotColoring

open Set
open scoped BigOperators

/-- Grid: an abbreviation for `Fin 3 → ℤ`. -/
abbrev Grid := Fin 3 → ℤ
/-- Position: an abbreviation for `Fin 3 → ℝ`. -/
abbrev Position := Fin 3 → ℝ
/-- Label: an abbreviation for `ℕ × (Grid × Bool)`. -/
abbrev Label := ℕ × (Grid × Bool)

/-- Dyadic Q, given by `(2 : ℝ) ^ (-(n : ℝ))`. -/
def dyadicQ (n : ℕ) : ℝ := (2 : ℝ) ^ (-(n : ℝ))

/-- Spacing, given by `(2 : ℝ) ^ (-(n : ℝ) * a) / (n : ℝ) ^ 6`. -/
def spacing (a : ℝ) (n : ℕ) : ℝ := (2 : ℝ) ^ (-(n : ℝ) * a) / (n : ℝ) ^ 6

theorem spacing_eq_scaled_mesh (a : ℝ) (n : ℕ) :
    spacing a n = dyadicQ n ^ a * (1 / (((n : ℝ) ^ 2) ^ 3)) := by
  unfold spacing dyadicQ
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [← pow_mul]
  norm_num
  ring

theorem spacing_pos (a : ℝ) {n : ℕ} (hn : 1 ≤ n) : 0 < spacing a n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  exact div_pos (Real.rpow_pos_of_pos (by norm_num) _) (pow_pos hn' _)

theorem spacing_ratio (a : ℝ) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    spacing a n / spacing a m =
      ((m : ℝ) / (n : ℝ)) ^ 6 * (2 : ℝ) ^ (((m : ℝ) - (n : ℝ)) * a) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have he : (2 : ℝ) ^ (-(m : ℝ) * a) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hp : (2 : ℝ) ^ (((m : ℝ) - (n : ℝ)) * a) =
      (2 : ℝ) ^ (-(n : ℝ) * a) / (2 : ℝ) ^ (-(m : ℝ) * a) := by
    rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [hp]
  unfold spacing
  rw [div_pow]
  field_simp

/-- The mesh ratio is uniform across levels at distance at most four. -/
theorem spacing_ratio_le (a A : ℝ) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 4) (hmn : m ≤ n + 4)
    (ha : |a| ≤ A) :
    spacing a n / spacing a m ≤ (5 : ℝ) ^ 6 * (2 : ℝ) ^ (4 * A) := by
  rw [spacing_ratio a hn hm]
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hm5 : (m : ℝ) ≤ 5 * (n : ℝ) := by exact_mod_cast (by omega : m ≤ 5 * n)
  have hquot : (m : ℝ) / (n : ℝ) ≤ 5 := (div_le_iff₀ hn').mpr hm5
  have hpow : ((m : ℝ) / (n : ℝ)) ^ 6 ≤ (5 : ℝ) ^ 6 :=
    pow_le_pow_left₀ (div_nonneg hm0 hn'.le) hquot 6
  have hdiff : |(m : ℝ) - (n : ℝ)| ≤ 4 := by
    have h1 : (n : ℝ) ≤ (m : ℝ) + 4 := by exact_mod_cast hnm
    have h2 : (m : ℝ) ≤ (n : ℝ) + 4 := by exact_mod_cast hmn
    rw [abs_le]
    constructor <;> linarith
  have hexp : ((m : ℝ) - (n : ℝ)) * a ≤ 4 * A := by
    calc
      ((m : ℝ) - (n : ℝ)) * a ≤ |((m : ℝ) - (n : ℝ)) * a| := le_abs_self _
      _ = |(m : ℝ) - (n : ℝ)| * |a| := abs_mul _ _
      _ ≤ 4 * |a| := mul_le_mul_of_nonneg_right hdiff (abs_nonneg a)
      _ ≤ 4 * A := mul_le_mul_of_nonneg_left ha (by norm_num)
  exact mul_le_mul hpow (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
    (Real.rpow_nonneg (by norm_num) _) (by positivity)

/-- Axis exponent, given by `![1 / 2, D, 1]`. -/
def axisExponent (D : ℝ) : Fin 3 → ℝ := ![1 / 2, D, 1]
/-- Width, given by `spacing (axisExponent D j) n`. -/
def width (D : ℝ) (j : Fin 3) (n : ℕ) : ℝ := spacing (axisExponent D j) n
/-- Ratio bound, given by `(5 : ℝ) ^ 6 * (2 : ℝ) ^ (4 * (1 + |D|))`. -/
def ratioBound (D : ℝ) : ℝ := (5 : ℝ) ^ 6 * (2 : ℝ) ^ (4 * (1 + |D|))

theorem width_pos (D : ℝ) (j : Fin 3) {n : ℕ} (hn : 1 ≤ n) : 0 < width D j n :=
  spacing_pos _ hn

theorem width_ratio_le (D : ℝ) (j : Fin 3) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 4) (hmn : m ≤ n + 4) :
    width D j n / width D j m ≤ ratioBound D := by
  apply spacing_ratio_le _ _ hn hm hnm hmn
  fin_cases j
  · change |(1 / 2 : ℝ)| ≤ 1 + |D|
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    linarith [abs_nonneg D]
  · change |D| ≤ 1 + |D|
    linarith
  · change |(1 : ℝ)| ≤ 1 + |D|
    rw [abs_one]
    linarith [abs_nonneg D]

/-- Physical box, given by `{x | ∀ j, |x j - width D j L.1 * (L.2.1 j : ℝ)| ≤ 2 * width D j
L.1}`. -/
def physicalBox (D : ℝ) (L : Label) : Set Position :=
  {x | ∀ j, |x j - width D j L.1 * (L.2.1 j : ℝ)| ≤ 2 * width D j L.1}

/-- The exact enlarged-box interaction relation used for coloring. -/
structure Adj (D : ℝ) (L M : Label) : Prop where
  left_positive : 1 ≤ L.1
  right_positive : 1 ≤ M.1
  distinct : L ≠ M
  left_level_le : L.1 ≤ M.1 + 4
  right_level_le : M.1 ≤ L.1 + 4
  overlap : (physicalBox D L ∩ physicalBox D M).Nonempty

theorem overlapping_centers (D : ℝ) (L M : Label)
    (hov : (physicalBox D L ∩ physicalBox D M).Nonempty) (j : Fin 3) :
    |width D j L.1 * (L.2.1 j : ℝ) - width D j M.1 * (M.2.1 j : ℝ)| ≤
      2 * (width D j L.1 + width D j M.1) := by
  obtain ⟨x, hx, hy⟩ := hov
  have htriangle := abs_sub_le (width D j L.1 * (L.2.1 j : ℝ)) (x j)
    (width D j M.1 * (M.2.1 j : ℝ))
  rw [abs_sub_comm (width D j L.1 * (L.2.1 j : ℝ)) (x j)] at htriangle
  linarith [hx j, hy j]

theorem same_level_grid_gap (D : ℝ) (L M : Label) (hn : 1 ≤ L.1)
    (hl : L.1 = M.1) (hov : (physicalBox D L ∩ physicalBox D M).Nonempty) (j : Fin 3) :
    |L.2.1 j - M.2.1 j| ≤ (4 : ℤ) := by
  have h := overlapping_centers D L M hov j
  rw [← hl, ← mul_sub, abs_mul, abs_of_pos (width_pos D j hn)] at h
  have hr : |(L.2.1 j : ℝ) - (M.2.1 j : ℝ)| ≤ 4 := by
    nlinarith [width_pos D j hn]
  exact_mod_cast hr

/-- Int color as an element of `Fin 5`. -/
def intColor (z : ℤ) : Fin 5 :=
  ⟨(z % 5).toNat, by
    have h0 := Int.emod_nonneg z (by norm_num : (5 : ℤ) ≠ 0)
    have h1 := Int.emod_lt_of_pos z (by norm_num : (0 : ℤ) < 5)
    omega⟩

theorem intColor_eq_of_close {z w : ℤ} (hc : intColor z = intColor w)
    (hd : |z - w| ≤ 4) : z = w := by
  have hv := congrArg Fin.val hc
  dsimp [intColor] at hv
  have hz0 := Int.emod_nonneg z (by norm_num : (5 : ℤ) ≠ 0)
  have hw0 := Int.emod_nonneg w (by norm_num : (5 : ℤ) ≠ 0)
  have hdiff := abs_le.mp hd
  omega

/-- Palette: an abbreviation for `Fin 9 × ((Fin 3 → Fin 5) × Bool)`. -/
abbrev Palette := Fin 9 × ((Fin 3 → Fin 5) × Bool)

/-- Color data, given by `(⟨L.1 % 9, Nat.mod_lt _ (by norm_num)⟩, (fun j => intColor (L.2.1 j),
L.2.2))`. -/
def colorData (L : Label) : Palette :=
  (⟨L.1 % 9, Nat.mod_lt _ (by norm_num)⟩, (fun j => intColor (L.2.1 j), L.2.2))

theorem palette_card : Fintype.card Palette = 2250 := by
  norm_num [Palette, Fintype.card_prod, Fintype.card_fun]

/-- This is a constructed coloring, not a coloring hypothesis. -/
theorem colorData_proper (D : ℝ) {L M : Label} (h : Adj D L M) : colorData L ≠ colorData M := by
  intro hc
  have hlevel := congrArg (fun c : Palette => c.1.val) hc
  change L.1 % 9 = M.1 % 9 at hlevel
  have hl : L.1 = M.1 := by
    have h1 := h.left_level_le
    have h2 := h.right_level_le
    omega
  have hg : L.2.1 = M.2.1 := by
    funext j
    apply intColor_eq_of_close
    · exact congrArg (fun c : Palette => c.2.1 j) hc
    · exact same_level_grid_gap D L M h.left_positive hl h.overlap j
  have hs : L.2.2 = M.2.2 := congrArg (fun c : Palette => c.2.2) hc
  exact h.distinct (Prod.ext hl (Prod.ext hg hs))

/-- Color, given by `(Fintype.equivFin Palette) (colorData L)`. -/
def color (L : Label) : Fin (Fintype.card Palette) := (Fintype.equivFin Palette) (colorData L)

theorem color_proper (D : ℝ) {L M : Label} (h : Adj D L M) : color L ≠ color M := by
  intro hc
  exact colorData_proper D h ((Fintype.equivFin Palette).injective hc)

/-- A reusable one-dimensional bound: overlapping intervals force the finer
grid index to lie within a fixed distance of the rescaled reference index. -/
theorem normalized_index_gap (h h' B : ℝ) (i j : ℤ) (hh' : 0 < h')
    (hratio : h / h' ≤ B)
    (hgap : |h * (i : ℝ) - h' * (j : ℝ)| ≤ 2 * (h + h')) :
    |h / h' * (i : ℝ) - (j : ℝ)| ≤ 2 * (B + 1) := by
  calc
    |h / h' * (i : ℝ) - (j : ℝ)| = |(h * (i : ℝ) - h' * (j : ℝ)) / h'| := by
      congr 1
      field_simp
    _ = |h * (i : ℝ) - h' * (j : ℝ)| / h' := by rw [abs_div, abs_of_pos hh']
    _ ≤ (2 * (h + h')) / h' := div_le_div_of_nonneg_right hgap hh'.le
    _ = 2 * (h / h' + 1) := by field_simp
    _ ≤ 2 * (B + 1) := by linarith

theorem index_near_floor (c A : ℝ) (j : ℤ) (K : ℕ)
    (hgap : |c - (j : ℝ)| ≤ A) (hK : A + 1 ≤ (K : ℝ)) :
    |j - ⌊c⌋| ≤ (K : ℤ) := by
  have hfloor : |c - (⌊c⌋ : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le c))]
    linarith [Int.lt_floor_add_one c]
  have ht := abs_sub_le (j : ℝ) c (⌊c⌋ : ℝ)
  rw [abs_sub_comm (j : ℝ) c] at ht
  have hreal : |(j : ℝ) - (⌊c⌋ : ℝ)| ≤ (K : ℝ) := by linarith
  exact_mod_cast hreal

/-- Index radius, given by `⌈2 * (ratioBound D + 1) + 1⌉₊`. -/
def indexRadius (D : ℝ) : ℕ := ⌈2 * (ratioBound D + 1) + 1⌉₊

/-- Index center, given by `⌊width D j L.1 / width D j m * (L.2.1 j : ℝ)⌋`. -/
def indexCenter (D : ℝ) (L : Label) (m : ℕ) (j : Fin 3) : ℤ :=
  ⌊width D j L.1 / width D j m * (L.2.1 j : ℝ)⌋

/-- Candidate grids, given by `Fintype.piFinset (fun j => Finset.Icc (indexCenter D L m j -
(indexRadius D : ℤ)) (indexCenter D L m j + (indexRadius D : ℤ)))`. -/
def candidateGrids (D : ℝ) (L : Label) (m : ℕ) : Finset Grid :=
  Fintype.piFinset (fun j => Finset.Icc (indexCenter D L m j - (indexRadius D : ℤ))
    (indexCenter D L m j + (indexRadius D : ℤ)))

/-- Candidates at level, given by `((candidateGrids D L m).product (Finset.univ : Finset
Bool)).image (fun gs => (m, gs))`. -/
def candidatesAtLevel (D : ℝ) (L : Label) (m : ℕ) : Finset Label :=
  ((candidateGrids D L m).product (Finset.univ : Finset Bool)).image (fun gs => (m, gs))

/-- Candidates, given by `(Finset.Icc (L.1 - 4) (L.1 + 4)).biUnion (candidatesAtLevel D L)`. -/
def candidates (D : ℝ) (L : Label) : Finset Label :=
  (Finset.Icc (L.1 - 4) (L.1 + 4)).biUnion (candidatesAtLevel D L)

theorem adj_index_bound (D : ℝ) {L M : Label} (h : Adj D L M) (j : Fin 3) :
    |M.2.1 j - indexCenter D L M.1 j| ≤ (indexRadius D : ℤ) := by
  apply index_near_floor
  · exact normalized_index_gap _ _ _ _ _ (width_pos D j h.right_positive)
      (width_ratio_le D j h.left_positive h.right_positive h.left_level_le h.right_level_le)
      (overlapping_centers D L M h.overlap j)
  · exact Nat.le_ceil _

theorem adj_mem_candidates (D : ℝ) {L M : Label} (h : Adj D L M) : M ∈ candidates D L := by
  apply Finset.mem_biUnion.mpr
  refine ⟨M.1, ?_, ?_⟩
  · simp only [Finset.mem_Icc]
    have h1 := h.left_level_le
    have h2 := h.right_level_le
    omega
  · apply Finset.mem_image.mpr
    refine ⟨M.2, ?_, rfl⟩
    apply Finset.mem_product.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    apply Fintype.mem_piFinset.mpr
    intro j
    have hj := abs_le.mp (adj_index_bound D h j)
    simp only [Finset.mem_Icc]
    omega

theorem integer_interval_card (c : ℤ) (K : ℕ) :
    (Finset.Icc (c - (K : ℤ)) (c + (K : ℤ))).card = 2 * K + 1 := by
  rw [Int.card_Icc]
  omega

theorem candidateGrids_card (D : ℝ) (L : Label) (m : ℕ) :
    (candidateGrids D L m).card = (2 * indexRadius D + 1) ^ 3 := by
  unfold candidateGrids
  rw [Fintype.card_piFinset]
  simp only [integer_interval_card, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem candidatesAtLevel_card_le (D : ℝ) (L : Label) (m : ℕ) :
    (candidatesAtLevel D L m).card ≤ (2 * indexRadius D + 1) ^ 3 * 2 := by
  calc
    (candidatesAtLevel D L m).card ≤
        ((candidateGrids D L m).product (Finset.univ : Finset Bool)).card := Finset.card_image_le
    _ = (2 * indexRadius D + 1) ^ 3 * 2 := by
      change ((candidateGrids D L m) ×ˢ (Finset.univ : Finset Bool)).card = _
      simpa only [candidateGrids_card, Finset.card_univ, Fintype.card_bool] using
        Finset.card_product (candidateGrids D L m) (Finset.univ : Finset Bool)

/-- Degree bound, given by `18 * (2 * indexRadius D + 1) ^ 3`. -/
def degreeBound (D : ℝ) : ℕ := 18 * (2 * indexRadius D + 1) ^ 3

theorem candidates_card_le (D : ℝ) (L : Label) :
    (candidates D L).card ≤ degreeBound D := by
  have hlevels : (Finset.Icc (L.1 - 4) (L.1 + 4)).card ≤ 9 := by
    rw [Nat.card_Icc]
    omega
  calc
    (candidates D L).card ≤
        ∑ m ∈ Finset.Icc (L.1 - 4) (L.1 + 4), (candidatesAtLevel D L m).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _m ∈ Finset.Icc (L.1 - 4) (L.1 + 4), (2 * indexRadius D + 1) ^ 3 * 2 :=
      Finset.sum_le_sum (fun m _ => candidatesAtLevel_card_le D L m)
    _ = (Finset.Icc (L.1 - 4) (L.1 + 4)).card * ((2 * indexRadius D + 1) ^ 3 * 2) := by simp
    _ ≤ 9 * ((2 * indexRadius D + 1) ^ 3 * 2) := Nat.mul_le_mul_right _ hlevels
    _ = degreeBound D := by unfold degreeBound; ring

/-- The actual finite neighbor set, obtained by filtering an explicit finite box. -/
def neighbors (D : ℝ) (L : Label) : Finset Label := by
  classical
  exact (candidates D L).filter (Adj D L)

theorem mem_neighbors_iff (D : ℝ) (L M : Label) : M ∈ neighbors D L ↔ Adj D L M := by
  classical
  simp only [neighbors, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨adj_mem_candidates D h, h⟩⟩

/-- Uniform degree control for every dyadic level, grid point, and sign. -/
theorem neighbors_card_le (D : ℝ) (L : Label) : (neighbors D L).card ≤ degreeBound D := by
  classical
  exact (Finset.card_filter_le _ _).trans (candidates_card_le D L)

theorem label_type_countable : Countable Label := by infer_instance

/-- The expanding eigenvalue of the actual covering matrix. -/
def coverGrowth : ℝ := 4 + Real.sqrt 2

theorem log_coverGrowth_pos : 0 < Real.log coverGrowth := by
  apply Real.log_pos
  unfold coverGrowth
  linarith [Real.sqrt_nonneg (2 : ℝ)]

/-- The real expression whose floor defines the manuscript's native index. -/
def nativeArgument (h : ℝ) (n : ℕ) : ℝ :=
  Real.log (dyadicQ n ^ (-1 - h) / (n : ℝ) ^ 2) / Real.log coverGrowth

/-- Native index, given by `⌊nativeArgument h n⌋₊`. -/
def nativeIndex (h : ℝ) (n : ℕ) : ℕ := ⌊nativeArgument h n⌋₊

theorem nativeArgument_expanded (h : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    nativeArgument h n =
      ((n : ℝ) * (1 + h) * Real.log 2 - 2 * Real.log (n : ℝ)) / Real.log coverGrowth := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hq : 0 < dyadicQ n := Real.rpow_pos_of_pos (by norm_num) _
  unfold nativeArgument
  rw [Real.log_div (ne_of_gt (Real.rpow_pos_of_pos hq _)) (pow_ne_zero 2 hn'),
    Real.log_rpow hq, Real.log_pow]
  unfold dyadicQ
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  norm_num
  ring

/-- Native gap budget, given by `(4 * (1 + h) * Real.log 2 + 2 * Real.log 5) / Real.log
coverGrowth`. -/
def nativeGapBudget (h : ℝ) : ℝ :=
  (4 * (1 + h) * Real.log 2 + 2 * Real.log 5) / Real.log coverGrowth

/-- Native gap, given by `⌈nativeGapBudget h⌉₊ + 1`. -/
def nativeGap (h : ℝ) : ℕ := ⌈nativeGapBudget h⌉₊ + 1

theorem log_level_gap {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hnm : n ≤ m + 4) (hmn : m ≤ n + 4) :
    |Real.log (n : ℝ) - Real.log (m : ℝ)| ≤ Real.log 5 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm' : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hn5 : (n : ℝ) ≤ 5 * (m : ℝ) := by exact_mod_cast (by omega : n ≤ 5 * m)
  have hm5 : (m : ℝ) ≤ 5 * (n : ℝ) := by exact_mod_cast (by omega : m ≤ 5 * n)
  have h1 := Real.log_le_log hn' hn5
  have h2 := Real.log_le_log hm' hm5
  rw [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) (ne_of_gt hm')] at h1
  rw [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) (ne_of_gt hn')] at h2
  rw [abs_le]
  constructor <;> linarith

theorem nativeArgument_gap (h : ℝ) (hh : 0 ≤ h) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 4) (hmn : m ≤ n + 4) :
    |nativeArgument h n - nativeArgument h m| ≤ nativeGapBudget h := by
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num)).le
  have h1h : 0 ≤ 1 + h := by linarith
  have hdiff : |(n : ℝ) - (m : ℝ)| ≤ 4 := by
    have hn' : (n : ℝ) ≤ (m : ℝ) + 4 := by exact_mod_cast hnm
    have hm' : (m : ℝ) ≤ (n : ℝ) + 4 := by exact_mod_cast hmn
    rw [abs_le]
    constructor <;> linarith
  have hlogs := log_level_gap hn hm hnm hmn
  have hnum :
      |((n : ℝ) - (m : ℝ)) * (1 + h) * Real.log 2 -
        2 * (Real.log (n : ℝ) - Real.log (m : ℝ))| ≤
      4 * (1 + h) * Real.log 2 + 2 * Real.log 5 := by
    calc
      _ ≤ |((n : ℝ) - (m : ℝ)) * (1 + h) * Real.log 2| +
          |2 * (Real.log (n : ℝ) - Real.log (m : ℝ))| := abs_sub _ _
      _ = |(n : ℝ) - (m : ℝ)| * (1 + h) * Real.log 2 +
          2 * |Real.log (n : ℝ) - Real.log (m : ℝ)| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hlog2, abs_of_nonneg h1h,
              abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdiff h1h) hlog2)
        (mul_le_mul_of_nonneg_left hlogs (by norm_num))
  calc
    |nativeArgument h n - nativeArgument h m| =
        |(((n : ℝ) - (m : ℝ)) * (1 + h) * Real.log 2 -
          2 * (Real.log (n : ℝ) - Real.log (m : ℝ))) / Real.log coverGrowth| := by
            rw [nativeArgument_expanded h hn, nativeArgument_expanded h hm]
            congr 1
            ring
    _ = |((n : ℝ) - (m : ℝ)) * (1 + h) * Real.log 2 -
        2 * (Real.log (n : ℝ) - Real.log (m : ℝ))| / Real.log coverGrowth := by
          rw [abs_div, abs_of_pos log_coverGrowth_pos]
    _ ≤ nativeGapBudget h := div_le_div_of_nonneg_right hnum log_coverGrowth_pos.le

theorem natFloor_gap_le (u v C : ℝ) (h : u - v ≤ C) :
    ⌊u⌋₊ ≤ ⌊v⌋₊ + (⌈C⌉₊ + 1) := by
  apply Nat.floor_le_of_le
  push_cast
  linarith [Nat.lt_floor_add_one v, Nat.le_ceil C]

/-- The actual adjacent native indices have an explicit uniform gap. -/
theorem nativeIndex_gap (h : ℝ) (hh : 0 ≤ h) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m + 4) (hmn : m ≤ n + 4) :
    nativeIndex h n ≤ nativeIndex h m + nativeGap h ∧
      nativeIndex h m ≤ nativeIndex h n + nativeGap h := by
  have hg := abs_le.mp (nativeArgument_gap h hh hn hm hnm hmn)
  constructor
  · exact natFloor_gap_le _ _ _ hg.2
  · exact natFloor_gap_le _ _ _ (by linarith [hg.1])

theorem nat_square_le_two_pow {n : ℕ} (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hmul := Nat.mul_le_mul_right n hn
      calc
        (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- `n=4` is already a valid uniform threshold for nonnegative native indices
when `h≥0`; the manuscript subsequently retains still larger bands. -/
theorem nativeArgument_nonneg (h : ℝ) (hh : 0 ≤ h) {n : ℕ} (hn : 4 ≤ n) :
    0 ≤ nativeArgument h n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsquare : (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ n := by exact_mod_cast nat_square_le_two_pow hn
  have hq : (n : ℝ) ^ 2 ≤ dyadicQ n ^ (-1 - h) := by
    unfold dyadicQ
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ n := hsquare
      _ = (2 : ℝ) ^ (n : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (2 : ℝ) ^ (-(n : ℝ) * (-1 - h)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  have hratio : 1 ≤ dyadicQ n ^ (-1 - h) / (n : ℝ) ^ 2 := by
    apply (le_div_iff₀ (pow_pos hn' 2)).mpr
    simpa using hq
  exact div_nonneg (Real.log_nonneg hratio) log_coverGrowth_pos.le

theorem nativeIndex_eq_integer_floor (h : ℝ) (hh : 0 ≤ h) {n : ℕ} (hn : 4 ≤ n) :
    (nativeIndex h n : ℤ) = ⌊nativeArgument h n⌋ := by
  unfold nativeIndex
  rw [← Int.floor_toNat, Int.toNat_of_nonneg (Int.floor_nonneg.mpr (nativeArgument_nonneg h hh hn))]

/-- The constructed finite coloring feeds the proved rational-slot geometry
using the manuscript's actual native covering index, with no coloring or
native-index-gap assumption. -/
theorem physical_labels_have_auxiliary_slots (D h : ℝ) (hh : 0 ≤ h)
    (a b : SlotGeometry.Plane) :
    ∃ r : ℝ, 0 < r ∧ ∀ L M : Label, Adj D L M →
      Disjoint
        (SlotGeometry.liftedSupport (nativeIndex h L.1)
          (SlotGeometry.orientedRectangle
            (SlotGeometry.center (Fintype.card Palette) (nativeGap h) (color L)) a b (2 * r)))
        (SlotGeometry.liftedSupport (nativeIndex h M.1)
          (SlotGeometry.orientedRectangle
            (SlotGeometry.center (Fintype.card Palette) (nativeGap h) (color M)) a b (2 * r))) := by
  apply SlotGeometry.colored_labels_have_slots
    (Fintype.card Palette) (nativeGap h) a b (Adj D) color (fun L => nativeIndex h L.1)
  · intro L M hLM
    exact color_proper D hLM
  · intro L M hLM
    exact nativeIndex_gap h hh hLM.left_positive hLM.right_positive
      hLM.left_level_le hLM.right_level_le

end NavierStokes.SlotColoring
