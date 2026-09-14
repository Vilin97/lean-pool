/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Example.Density
public import LeanPool.Besicovitch.Example.Recursion
public import Mathlib.Analysis.PSeries

/-!
# The Lipschitz pieces of Besicovitch's graph are null

A point of `[0, 1]` that avoids every grid of level `N, N + 1, …` on both sides lies in a
set of measure zero.  Indeed, inside a level-`M` cell the survivors of the levels up to `M` form
an interval, and the level-`M + 1` grid punches holes of total relative size `1 / ((M+1) (L+1))`
into every interval, up to an error of a few holes per cell.  The errors are summable while
`∑ 1 / ((M + 1) (L + 1))` diverges, so the recursion of `LeanPool.Besicovitch.Example.Recursion` forces
the surviving measure to zero.

Combined with `ae_eventually_mem_avoid`, every subset of `[0, 1]` on which `g` is Lipschitz is
Lebesgue-null.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace LeanPool.Besicovitch.Example

/-- A subset of `[0, 1]` has finite Lebesgue measure. -/
theorem volume_ne_top_of_subset_Icc {S : Set ℝ} (hS : S ⊆ Icc 0 1) : volume S ≠ ⊤ :=
  ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (measure_mono hS)

/-! ### Holes around grid points -/

/-- The relative width `2 * margin L m / cellLength m` of a hole is `1 / (m (L + 1))`. -/
theorem two_mul_margin_div_cellLength {L : ℝ} (hL : 0 ≤ L) {m : ℕ} (hm : 1 ≤ m) :
    2 * margin L m / cellLength m = 1 / (m * (L + 1)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hpos := cellLength_pos m
  have hL1 : (0 : ℝ) < L + 1 := by linarith
  unfold margin
  field_simp

/-- The open hole of radius `margin L m` around the level-`m` grid point with index `k`. -/
def hole (L : ℝ) (m : ℕ) (k : ℤ) : Set ℝ :=
  Ioo (gridPoint m k - margin L m) (gridPoint m k + margin L m)

/-- A hole is measurable. -/
theorem measurableSet_hole (L : ℝ) (m : ℕ) (k : ℤ) : MeasurableSet (hole L m k) :=
  measurableSet_Ioo

/-- A hole has measure `2 * margin L m`. -/
theorem volume_hole (L : ℝ) (m : ℕ) (k : ℤ) :
    volume (hole L m k) = ENNReal.ofReal (2 * margin L m) := by
  rw [hole, Real.volume_Ioo]; congr 1; ring

/-- A hole misses the avoided set. -/
theorem disjoint_hole_avoid (L : ℝ) (m : ℕ) (k : ℤ) : Disjoint (hole L m k) (avoid L m) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [hole, mem_Ioo] at hx
  have h := hx' k
  have : |x - gridPoint m k| < margin L m := by rw [abs_lt]; constructor <;> linarith
  linarith

/-- Distinct holes of the same level are disjoint. -/
theorem pairwiseDisjoint_hole {L : ℝ} (hL : 0 ≤ L) {m : ℕ} (hm : 1 ≤ m) (I : Finset ℤ) :
    (I : Set ℤ).PairwiseDisjoint (hole L m) := by
  intro k _ k' _ hkk'
  have hμ := margin_le_half hL hm
  have hpos := cellLength_pos m
  show Disjoint (hole L m k) (hole L m k')
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [hole, gridPoint, mem_Ioo] at hx hx'
  have h1 : ((k : ℝ) - k') * cellLength m < 1 * cellLength m := by linarith
  have h2 : ((k' : ℝ) - k) * cellLength m < 1 * cellLength m := by linarith
  have h1' : (k : ℝ) - k' < 1 := lt_of_mul_lt_mul_right h1 hpos.le
  have h2' : (k' : ℝ) - k < 1 := lt_of_mul_lt_mul_right h2 hpos.le
  have h3 : k - k' < 1 := by exact_mod_cast h1'
  have h4 : k' - k < 1 := by exact_mod_cast h2'
  omega

/-! ### The estimate on one interval -/

/-- **Per-interval estimate.** An order-connected subset `S` of `[0, 1]` loses the fraction
`1 / (m (L + 1))` of its measure, up to an error of `4 * margin L m`, when the level-`m` grid
is avoided: the holes around the level-`m` grid points inside `S` are disjoint, are removed,
and number at least `volume S / cellLength m - 2`. -/
theorem volume_inter_avoid_le {L : ℝ} (hL : 0 ≤ L) {m : ℕ} (hm : 1 ≤ m) {S : Set ℝ}
    (hS : S.OrdConnected) (hS1 : S ⊆ Icc 0 1) :
    (volume (S ∩ avoid L m)).toReal ≤
      (1 - 1 / (m * (L + 1))) * (volume S).toReal + 4 * margin L m := by
  have hαpos := cellLength_pos m
  have hμpos := margin_pos hL hm
  have hμα := margin_le_half hL hm
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hratio := two_mul_margin_div_cellLength hL hm
  have hfin := volume_ne_top_of_subset_Icc hS1
  have hfin' : volume (S ∩ avoid L m) ≠ ⊤ :=
    volume_ne_top_of_subset_Icc (inter_subset_left.trans hS1)
  have hcpos : 0 ≤ 1 / ((m : ℝ) * (L + 1)) := by positivity
  have hc : 1 / ((m : ℝ) * (L + 1)) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [empty_inter, measure_empty, ENNReal.toReal_zero, mul_zero, zero_add]
    positivity
  -- the endpoints of `S`
  have hbb : BddBelow S := ⟨0, fun x hx ↦ (hS1 hx).1⟩
  have hba : BddAbove S := ⟨1, fun x hx ↦ (hS1 hx).2⟩
  have huv : sInf S ≤ sSup S := csInf_le_csSup hne hbb hba
  have hSuv : S ⊆ Icc (sInf S) (sSup S) := fun x hx ↦ ⟨csInf_le hbb hx, le_csSup hba hx⟩
  have huvS : Ioo (sInf S) (sSup S) ⊆ S := by
    rintro y ⟨hy1, hy2⟩
    obtain ⟨a, ha, hay⟩ := exists_lt_of_csInf_lt hne hy1
    obtain ⟨b, hb, hyb⟩ := exists_lt_of_lt_csSup hne hy2
    exact hS.out ha hb ⟨hay.le, hyb.le⟩
  have hℓ : (volume S).toReal ≤ sSup S - sInf S := by
    refine ENNReal.toReal_le_of_le_ofReal (by linarith) ?_
    rw [← Real.volume_Icc]; exact measure_mono hSuv
  -- the holes inside `S`: indices `k` with `sInf S + margin ≤ k α ≤ sSup S - margin`
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (sInf S + margin L m) / cellLength m := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (sSup S - margin L m) / cellLength m := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I : Finset ℤ, I = Finset.Icc ⌈A⌉ ⌊B⌋ := ⟨_, rfl⟩
  have hIS : ∀ k ∈ I, hole L m k ⊆ S := by
    intro k hk
    rw [hI, Finset.mem_Icc, Int.ceil_le, Int.le_floor, hA, hB, div_le_iff₀ hαpos,
      le_div_iff₀ hαpos] at hk
    intro x hx
    simp only [hole, gridPoint, mem_Ioo] at hx
    exact huvS ⟨by linarith [hk.1, hx.1], by linarith [hk.2, hx.2]⟩
  have hmeas : MeasurableSet (⋃ k ∈ I, hole L m k) :=
    Finset.measurableSet_biUnion _ fun k _ ↦ measurableSet_hole L m k
  have hdisj : Disjoint (S ∩ avoid L m) (⋃ k ∈ I, hole L m k) := by
    rw [disjoint_iUnion₂_right]
    intro k _
    exact (disjoint_hole_avoid L m k).symm.mono_left inter_subset_right
  have hvolU : volume (⋃ k ∈ I, hole L m k) = I.card * ENNReal.ofReal (2 * margin L m) := by
    rw [measure_biUnion_finset (pairwiseDisjoint_hole hL hm I) fun k _ ↦ measurableSet_hole L m k]
    simp only [volume_hole, Finset.sum_const, nsmul_eq_mul]
  have hU : volume (⋃ k ∈ I, hole L m k) ≠ ⊤ := by
    rw [hvolU]; exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  have hunion : volume (S ∩ avoid L m) + volume (⋃ k ∈ I, hole L m k) ≤ volume S := by
    rw [← measure_union hdisj hmeas]
    exact measure_mono (union_subset inter_subset_left (iUnion₂_subset hIS))
  -- in real numbers: the removed holes account for `card I * 2 * margin`
  have hreal : (volume (S ∩ avoid L m)).toReal + I.card * (2 * margin L m) ≤
      (volume S).toReal := by
    have := ENNReal.toReal_mono hfin hunion
    rwa [ENNReal.toReal_add hfin' hU, hvolU, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by positivity)] at this
  -- counting the holes
  have hcard : B - A - 1 ≤ I.card := by
    have h1 : ((⌊B⌋ + 1 - ⌈A⌉ : ℤ) : ℝ) ≤ I.card := by
      rw [hI, Int.card_Icc]; exact_mod_cast Int.self_le_toNat _
    push_cast at h1
    linarith [Int.lt_floor_add_one B, Int.ceil_lt_add_one A]
  have hBA : B - A = (sSup S - sInf S) / cellLength m - 2 * margin L m / cellLength m := by
    rw [hA, hB]; ring
  rw [hratio] at hBA
  have hkey : (sSup S - sInf S) * (1 / ((m : ℝ) * (L + 1))) - 4 * margin L m ≤
      I.card * (2 * margin L m) := by
    have h3 : ((sSup S - sInf S) / cellLength m - 2) * (2 * margin L m) ≤
        I.card * (2 * margin L m) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h4 : (sSup S - sInf S) / cellLength m * (2 * margin L m) =
        (sSup S - sInf S) * (1 / ((m : ℝ) * (L + 1))) := by
      rw [← hratio]; ring
    linarith
  have hℓc : (volume S).toReal * (1 / ((m : ℝ) * (L + 1))) ≤
      (sSup S - sInf S) * (1 / ((m : ℝ) * (L + 1))) := mul_le_mul_of_nonneg_right hℓ hcpos
  linarith

/-! ### Summing over the cells of the previous level -/

/-- `[0, 1]` is covered by the level-`M` cells with indices `0, …, cellIndex M 1`. -/
theorem Icc_subset_biUnion_cell (M : ℕ) :
    Icc (0 : ℝ) 1 ⊆ ⋃ i ∈ Finset.Icc (0 : ℤ) (cellIndex M 1), cell M i := by
  intro x hx
  have hpos := cellLength_pos M
  refine mem_iUnion₂.mpr ⟨cellIndex M x, ?_, mem_cell_cellIndex M x⟩
  rw [Finset.mem_Icc]
  unfold cellIndex
  exact ⟨Int.floor_nonneg.mpr (div_nonneg hx.1 hpos.le),
    Int.floor_mono (div_le_div_of_nonneg_right hx.2 hpos.le)⟩

/-- There are at most `1 / cellLength M + 1` level-`M` cells meeting `[0, 1]`. -/
theorem card_Icc_cellIndex_le (M : ℕ) :
    ((Finset.Icc (0 : ℤ) (cellIndex M 1)).card : ℝ) ≤ 1 / cellLength M + 1 := by
  have hpos := cellLength_pos M
  have h0 : 0 ≤ cellIndex M 1 := Int.floor_nonneg.mpr (by positivity)
  have hcard : ((Finset.Icc (0 : ℤ) (cellIndex M 1)).card : ℤ) = cellIndex M 1 + 1 := by
    rw [Int.card_Icc, sub_zero, Int.toNat_of_nonneg (by omega)]
  have hle : (cellIndex M 1 : ℝ) ≤ 1 / cellLength M := Int.floor_le _
  have hcardR : ((Finset.Icc (0 : ℤ) (cellIndex M 1)).card : ℝ) = cellIndex M 1 + 1 := by
    exact_mod_cast hcard
  linarith

/-- Consecutive cell lengths: `cellLength (M + 1) = cellLength M * (1/2) ^ (2 M + 1)`. -/
theorem cellLength_succ_eq (M : ℕ) :
    cellLength (M + 1) = cellLength M * (1 / 2) ^ (2 * M + 1) := by
  unfold cellLength; rw [← pow_add]; congr 1; ring

/-- The total error from the `1 / cellLength M + 1` cells of level `M` is geometrically small. -/
theorem error_le {L : ℝ} (hL : 0 ≤ L) (M : ℕ) :
    (1 / cellLength M + 1) * margin L (M + 1) ≤ (1 / 2) ^ (M + 1) := by
  have hpos := cellLength_pos M
  have hle1 := cellLength_le_one M
  have hμ := margin_le_half hL (Nat.le_add_left 1 M)
  rw [cellLength_succ_eq] at hμ
  have h1 : (1 / cellLength M + 1) * margin L (M + 1) ≤
      (1 / cellLength M + 1) * (cellLength M * (1 / 2) ^ (2 * M + 1) / 2) :=
    mul_le_mul_of_nonneg_left hμ (by positivity)
  have h2 : (1 / cellLength M + 1) * (cellLength M * (1 / 2) ^ (2 * M + 1) / 2) =
      (1 + cellLength M) / 2 * (1 / 2) ^ (2 * M + 1) := by
    field_simp
  have h3 : (1 + cellLength M) / 2 ≤ 1 := by linarith
  have h4 : ((1 : ℝ) / 2) ^ (2 * M + 1) ≤ (1 / 2) ^ (M + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h5 : (0 : ℝ) ≤ (1 / 2) ^ (2 * M + 1) := by positivity
  calc (1 / cellLength M + 1) * margin L (M + 1)
      ≤ (1 / cellLength M + 1) * (cellLength M * (1 / 2) ^ (2 * M + 1) / 2) := h1
    _ = (1 + cellLength M) / 2 * (1 / 2) ^ (2 * M + 1) := h2
    _ ≤ 1 * (1 / 2) ^ (2 * M + 1) := mul_le_mul_of_nonneg_right h3 h5
    _ ≤ (1 / 2) ^ (M + 1) := by rw [one_mul]; exact h4

/-- **One level of the recursion.** If `S ⊆ [0, 1]` meets every level-`M` cell in an
order-connected set, then avoiding the level-`M + 1` grid removes the fraction
`1 / ((M + 1) (L + 1))` of its measure, up to an error `4 * (1/2) ^ (M + 1)`. -/
theorem volume_inter_avoid_succ_le {L : ℝ} (hL : 0 ≤ L) (M : ℕ) {S : Set ℝ}
    (hS1 : S ⊆ Icc 0 1) (hS : ∀ i : ℤ, (S ∩ cell M i).OrdConnected) :
    (volume (S ∩ avoid L (M + 1))).toReal ≤
      (1 - 1 / (((M : ℝ) + 1) * (L + 1))) * (volume S).toReal + 4 * (1 / 2) ^ (M + 1) := by
  obtain ⟨I, hI⟩ : ∃ I : Finset ℤ, I = Finset.Icc (0 : ℤ) (cellIndex M 1) := ⟨_, rfl⟩
  have hm : 1 ≤ M + 1 := Nat.le_add_left 1 M
  have hμpos := margin_pos hL hm
  have hc0 : 0 ≤ 1 - 1 / (((M : ℝ) + 1) * (L + 1)) := by
    have : 1 / (((M : ℝ) + 1) * (L + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [Nat.cast_nonneg (α := ℝ) M]
    linarith
  have hfin : ∀ i ∈ I, volume (S ∩ cell M i ∩ avoid L (M + 1)) ≠ ⊤ := fun i _ ↦
    volume_ne_top_of_subset_Icc ((inter_subset_left.trans inter_subset_left).trans hS1)
  have hfin2 : ∀ i ∈ I, volume (S ∩ cell M i) ≠ ⊤ := fun i _ ↦
    volume_ne_top_of_subset_Icc (inter_subset_left.trans hS1)
  -- the measure is at most the sum over the cells
  have hcover : S ∩ avoid L (M + 1) ⊆ ⋃ i ∈ I, (S ∩ cell M i ∩ avoid L (M + 1)) := by
    rintro x ⟨hxS, hxa⟩
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (Icc_subset_biUnion_cell M (hS1 hxS))
    exact mem_iUnion₂.mpr ⟨i, hI ▸ hi, ⟨hxS, hxi⟩, hxa⟩
  have h1 : (volume (S ∩ avoid L (M + 1))).toReal ≤
      ∑ i ∈ I, (volume (S ∩ cell M i ∩ avoid L (M + 1))).toReal := by
    rw [← ENNReal.toReal_sum hfin]
    exact ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr hfin)
      ((measure_mono hcover).trans (measure_biUnion_finset_le I _))
  -- each cell loses the fraction `1 / ((M + 1) (L + 1))`
  have h2 : ∀ i ∈ I, (volume (S ∩ cell M i ∩ avoid L (M + 1))).toReal ≤
      (1 - 1 / (((M : ℝ) + 1) * (L + 1))) * (volume (S ∩ cell M i)).toReal +
        4 * margin L (M + 1) := fun i _ ↦ by
    have := volume_inter_avoid_le hL hm (hS i) (inter_subset_left.trans hS1)
    push_cast at this
    exact this
  -- the cells' measures add up to at most the measure of `S`
  have h3 : ∑ i ∈ I, (volume (S ∩ cell M i)).toReal ≤ (volume S).toReal := by
    rw [← ENNReal.toReal_sum hfin2]
    refine ENNReal.toReal_mono (volume_ne_top_of_subset_Icc hS1) ?_
    have hr : ∀ i ∈ I, volume (S ∩ cell M i) = (volume.restrict S) (cell M i) :=
      fun i _ ↦ by rw [Measure.restrict_apply (t := cell M i) measurableSet_Ico, inter_comm]
    have hU : (volume.restrict S) (⋃ i ∈ I, cell M i) =
        ∑ i ∈ I, (volume.restrict S) (cell M i) :=
      measure_biUnion_finset (fun i _ j _ hij ↦ cell_disjoint hij) fun i _ ↦ measurableSet_Ico
    rw [Finset.sum_congr rfl hr, ← hU]
    exact (measure_mono (subset_univ _)).trans (Measure.restrict_apply_univ S).le
  -- the number of cells times the error per cell
  have h4 : (I.card : ℝ) * (4 * margin L (M + 1)) ≤ 4 * (1 / 2) ^ (M + 1) := by
    have hc := card_Icc_cellIndex_le M
    rw [← hI] at hc
    have he := error_le hL M
    have h6 : (I.card : ℝ) * margin L (M + 1) ≤ (1 / cellLength M + 1) * margin L (M + 1) :=
      mul_le_mul_of_nonneg_right hc hμpos.le
    linarith
  calc (volume (S ∩ avoid L (M + 1))).toReal
      ≤ ∑ i ∈ I, (volume (S ∩ cell M i ∩ avoid L (M + 1))).toReal := h1
    _ ≤ ∑ i ∈ I, ((1 - 1 / (((M : ℝ) + 1) * (L + 1))) * (volume (S ∩ cell M i)).toReal +
          4 * margin L (M + 1)) := Finset.sum_le_sum h2
    _ = (1 - 1 / (((M : ℝ) + 1) * (L + 1))) * ∑ i ∈ I, (volume (S ∩ cell M i)).toReal +
          I.card * (4 * margin L (M + 1)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (1 - 1 / (((M : ℝ) + 1) * (L + 1))) * (volume S).toReal + 4 * (1 / 2) ^ (M + 1) :=
        add_le_add (mul_le_mul_of_nonneg_left h3 hc0) h4

/-! ### The survivors of the first `n` levels -/

/-- The points of `[0, 1]` avoiding the grids of levels `N + 1, …, N + n`. -/
def survivors (L : ℝ) (N : ℕ) : ℕ → Set ℝ
  | 0 => Icc 0 1
  | n + 1 => survivors L N n ∩ avoid L (N + n + 1)

/-- The survivors lie in `[0, 1]`. -/
theorem survivors_subset_Icc (L : ℝ) (N : ℕ) (n : ℕ) : survivors L N n ⊆ Icc 0 1 := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact inter_subset_left.trans ih

/-- The survivors have finite measure. -/
theorem volume_survivors_ne_top (L : ℝ) (N n : ℕ) : volume (survivors L N n) ≠ ⊤ :=
  volume_ne_top_of_subset_Icc (survivors_subset_Icc L N n)

/-- Inside a cell of level `M ≥ N + n` the survivors of `n` levels form an order-connected set. -/
theorem ordConnected_survivors_inter_cell (L : ℝ) (N : ℕ) (n : ℕ) :
    ∀ M : ℕ, N + n ≤ M → ∀ i : ℤ, (survivors L N n ∩ cell M i).OrdConnected := by
  induction n with
  | zero => intro M _ i; exact ordConnected_Icc.inter ordConnected_Ico
  | succ n ih =>
    intro M hM i
    show (survivors L N n ∩ avoid L (N + n + 1) ∩ cell M i).OrdConnected
    rw [inter_inter_distrib_right]
    exact (ih M (by omega) i).inter
      (ordConnected_avoid_inter_cell L (n := N + n + 1) (m := M) (by omega) i)

/-- The recursive estimate for the measure of the survivors. -/
theorem volume_survivors_succ_le {L : ℝ} (hL : 0 ≤ L) (N n : ℕ) :
    (volume (survivors L N (n + 1))).toReal ≤
      (1 - 1 / (((N : ℝ) + n + 1) * (L + 1))) * (volume (survivors L N n)).toReal +
        4 * (1 / 2) ^ (n + 1) := by
  have h := volume_inter_avoid_succ_le hL (N + n) (survivors_subset_Icc L N n)
    (ordConnected_survivors_inter_cell L N n (N + n) le_rfl)
  push_cast at h
  have h5 : ((1 : ℝ) / 2) ^ (N + n + 1) ≤ (1 / 2) ^ (n + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  show (volume (survivors L N n ∩ avoid L (N + n + 1))).toReal ≤ _
  linarith

/-- The sums `∑_{k < n} 1 / ((N + k) (L + 1))` diverge, by comparison with the harmonic series. -/
theorem tendsto_sum_one_div_atTop {L : ℝ} (hL : 0 ≤ L) {N : ℕ} (hN : 1 ≤ N) :
    Tendsto (fun n ↦ ∑ k ∈ Finset.range n, 1 / (((N : ℝ) + k) * (L + 1))) atTop atTop := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : (0 : ℝ) < 1 / (((N : ℝ) + 1) * (L + 1)) := by positivity
  have hterm : ∀ k : ℕ, 1 / (((N : ℝ) + 1) * (L + 1)) * (1 / ((k : ℝ) + 1)) ≤
      1 / (((N : ℝ) + k) * (L + 1)) := by
    intro k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [one_div_mul_one_div]
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) N) hk) hL]
  refine tendsto_atTop_mono (fun n ↦ ?_)
    (Tendsto.const_mul_atTop hc Real.tendsto_sum_range_one_div_nat_succ_atTop)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ ↦ hterm k

/-- The measure of the survivors tends to zero. -/
theorem tendsto_volume_survivors {L : ℝ} (hL : 0 ≤ L) {N : ℕ} (hN : 1 ≤ N) :
    Tendsto (fun n ↦ (volume (survivors L N n)).toReal) atTop (𝓝 0) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine tendsto_zero_of_recursive (a := fun k : ℕ ↦ 1 / (((N : ℝ) + k) * (L + 1)))
    (e := fun k : ℕ ↦ 4 * (1 / 2) ^ k) (fun n ↦ ENNReal.toReal_nonneg)
    (fun k ↦ show (0 : ℝ) ≤ 1 / (((N : ℝ) + k) * (L + 1)) by positivity) (fun k ↦ ?_)
    (fun k ↦ show (0 : ℝ) ≤ 4 * (1 / 2) ^ k by positivity) (tendsto_sum_one_div_atTop hL hN)
    (summable_geometric_two.mul_left 4) (fun n ↦ ?_)
  · show 1 / (((N : ℝ) + k) * (L + 1)) ≤ 1
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [div_le_one (by positivity)]
    nlinarith
  · show (volume (survivors L N (n + 1))).toReal ≤
      (1 - 1 / (((N : ℝ) + ((n + 1 : ℕ) : ℝ)) * (L + 1))) *
        (volume (survivors L N n)).toReal + 4 * (1 / 2) ^ (n + 1)
    push_cast
    rw [← add_assoc]
    exact volume_survivors_succ_le hL N n

/-! ### The main theorems -/

/-- **The two-sided avoiders are null.** The points of `[0, 1]` at distance at least
`margin L n` from every level-`n` grid point, for all `n ≥ N`, form a null set. -/
theorem volume_Icc_inter_iInter_avoid_eq_zero (L : ℝ) (hL : 0 ≤ L) (N : ℕ) :
    volume (Icc (0:ℝ) 1 ∩ ⋂ n : ℕ, avoid L (N + n)) = 0 := by
  have hsub : ∀ n, Icc (0:ℝ) 1 ∩ ⋂ n : ℕ, avoid L (N + n) ⊆ survivors L (N + 1) n := by
    intro n
    induction n with
    | zero => exact inter_subset_left
    | succ n ih =>
      show _ ⊆ survivors L (N + 1) n ∩ avoid L (N + 1 + n + 1)
      refine subset_inter ih fun x hx ↦ ?_
      have h := mem_iInter.mp hx.2 (n + 2)
      rwa [show N + 1 + n + 1 = N + (n + 2) by omega]
  have hfin : volume (Icc (0:ℝ) 1 ∩ ⋂ n : ℕ, avoid L (N + n)) ≠ ⊤ :=
    volume_ne_top_of_subset_Icc inter_subset_left
  have hle : ∀ n, (volume (Icc (0:ℝ) 1 ∩ ⋂ n : ℕ, avoid L (N + n))).toReal ≤
      (volume (survivors L (N + 1) n)).toReal := fun n ↦
    ENNReal.toReal_mono (volume_survivors_ne_top _ _ _) (measure_mono (hsub n))
  have h0 := ge_of_tendsto' (tendsto_volume_survivors hL (N := N + 1) (by omega)) hle
  have h0' : (volume (Icc (0:ℝ) 1 ∩ ⋂ n : ℕ, avoid L (N + n))).toReal = 0 :=
    le_antisymm h0 ENNReal.toReal_nonneg
  rcases (ENNReal.toReal_eq_zero_iff _).mp h0' with h | h
  · exact h
  · exact absurd h hfin

/-- **Lipschitz pieces are null.** A subset of `[0, 1]` on which Besicovitch's function is
Lipschitz has Lebesgue measure zero. -/
theorem volume_eq_zero_of_lipschitzOnWith {L : ℝ≥0} {A : Set ℝ} (hA : A ⊆ Icc 0 1)
    (hg : LipschitzOnWith L besicovitchFun A) : volume A = 0 := by
  have hae := ae_eventually_mem_avoid hg
  rw [ae_iff] at hae
  -- the points of `A` that do not eventually avoid the grids are null
  have h1 : volume ({x | ¬ ∀ᶠ n in atTop, x ∈ avoid (L : ℝ) n} ∩ A) = 0 :=
    nonpos_iff_eq_zero.mp ((Measure.le_restrict_apply A _).trans hae.le)
  -- the points of `A` that eventually avoid the grids are null by the main theorem
  have h2 : volume ({x | ∀ᶠ n in atTop, x ∈ avoid (L : ℝ) n} ∩ A) = 0 := by
    refine measure_mono_null ?_
      (measure_iUnion_null fun N ↦ volume_Icc_inter_iInter_avoid_eq_zero L L.coe_nonneg N)
    rintro x ⟨hx, hxA⟩
    obtain ⟨N, hN⟩ := eventually_atTop.mp hx
    exact mem_iUnion.mpr ⟨N, hA hxA, mem_iInter.mpr fun n ↦ hN (N + n) (Nat.le_add_right N n)⟩
  have hA' : A = {x | ¬ ∀ᶠ n in atTop, x ∈ avoid (L : ℝ) n} ∩ A ∪
      {x | ∀ᶠ n in atTop, x ∈ avoid (L : ℝ) n} ∩ A := by
    ext x; simp only [mem_union, mem_inter_iff, mem_setOf_eq]; tauto
  rw [hA']
  exact measure_union_null h1 h2

end LeanPool.Besicovitch.Example
