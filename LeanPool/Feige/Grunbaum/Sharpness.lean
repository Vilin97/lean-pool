/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import LeanPool.Feige.Grunbaum.Definitions
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sharpness of Grünbaum's centroid halfspace constant

This file constructs the full-dimensional standard simplex and its sharp
centroid halfspace.  It computes the relevant centroid coordinate by the
layer-cake formula and proves that every universal project-level lower bound
is at most `grunbaumConstant`.
-/

noncomputable section

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise

namespace Grunbaum

/-- Euclidean space in an arbitrary (possibly zero) dimension.  The project
type `Euc d` is definitionally `SimplexE (d + 1)`. -/
abbrev SimplexE (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The sum of the coordinates, bundled as a continuous linear functional. -/
def coordinateSum (n : ℕ) : SimplexE n →L[ℝ] ℝ :=
  ∑ i : Fin n, (EuclideanSpace.proj i : SimplexE n →L[ℝ] ℝ)

@[simp]
theorem coordinateSum_apply (n : ℕ) (x : SimplexE n) :
    coordinateSum n x = ∑ i, x i := by
  simp [coordinateSum]

/-- The full-dimensional standard simplex `xᵢ ≥ 0`, `∑ xᵢ ≤ 1`. -/
def simplexSet (n : ℕ) : Set (SimplexE n) :=
  {x | (∀ i, 0 ≤ x i) ∧ coordinateSum n x ≤ 1}

@[simp]
theorem mem_simplexSet {n : ℕ} {x : SimplexE n} :
    x ∈ simplexSet n ↔ (∀ i, 0 ≤ x i) ∧ coordinateSum n x ≤ 1 :=
  Iff.rfl

theorem convex_simplexSet (n : ℕ) : Convex ℝ (simplexSet n) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i ↦ ?_, ?_⟩
  · change 0 ≤ a * x i + b * y i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · rw [map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    calc
      a * coordinateSum n x + b * coordinateSum n y
          ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
          (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = 1 := by linarith

theorem isClosed_simplexSet (n : ℕ) : IsClosed (simplexSet n) := by
  have hcoord : IsClosed {x : SimplexE n | ∀ i, 0 ≤ x i} := by
    rw [show {x : SimplexE n | ∀ i, 0 ≤ x i} =
        ⋂ i : Fin n, {x : SimplexE n | 0 ≤ x i} by ext x; simp]
    exact isClosed_iInter fun i ↦
      isClosed_le continuous_const (EuclideanSpace.proj i).continuous
  have hsum : IsClosed {x : SimplexE n | coordinateSum n x ≤ 1} :=
    isClosed_le (coordinateSum n).continuous continuous_const
  exact hcoord.inter hsum

theorem isCompact_simplexSet (n : ℕ) : IsCompact (simplexSet n) := by
  let e : SimplexE n ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  have hcube : IsCompact (e.symm '' Icc (0 : Fin n → ℝ) 1) :=
    isCompact_Icc.image e.symm.continuous
  refine hcube.of_isClosed_subset (isClosed_simplexSet n) ?_
  intro x hx
  refine ⟨e x, ?_, e.symm_apply_apply x⟩
  constructor
  · intro i
    change 0 ≤ x i
    exact hx.1 i
  · intro i
    change x i ≤ 1
    exact (Finset.single_le_sum (fun j _ ↦ hx.1 j) (Finset.mem_univ i)).trans
      (by simpa using hx.2)

theorem nonempty_simplexSet (n : ℕ) : (simplexSet n).Nonempty := by
  refine ⟨0, ?_⟩
  simp

theorem interior_simplexSet_nonempty (n : ℕ) :
    (interior (simplexSet n)).Nonempty := by
  rw [(convex_simplexSet n).interior_nonempty_iff_affineSpan_eq_top]
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hsub : insert 0 (Set.range b) ⊆ simplexSet n := by
    rintro x (rfl | ⟨i, rfl⟩)
    · simp
    · constructor
      · intro j
        change 0 ≤ (EuclideanSpace.basisFun (Fin n) ℝ i) j
        rw [EuclideanSpace.basisFun_apply, PiLp.single_apply]
        split_ifs <;> positivity
      · simp [b, coordinateSum_apply, EuclideanSpace.basisFun_apply, PiLp.single_apply]
  have htop : affineSpan ℝ (insert 0 (Set.range b)) = ⊤ := by
    apply SetLike.ext
    intro x
    change x ∈ (affineSpan ℝ (insert 0 (Set.range b)) : Set (SimplexE n)) ↔
      x ∈ (⊤ : AffineSubspace ℝ (SimplexE n))
    have hi := Set.ext_iff.mp
      (affineSpan_insert_zero (k := ℝ) (Set.range b)) x
    rw [hi, b.span_eq]
    simp
  exact top_unique (htop ▸ affineSpan_mono ℝ hsub)

theorem volume_simplexSet_pos (n : ℕ) :
    0 < volume (simplexSet n) :=
  measure_pos_of_nonempty_interior volume (interior_simplexSet_nonempty n)

theorem volumeReal_simplexSet_pos (n : ℕ) :
    0 < volume.real (simplexSet n) := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos (volume_simplexSet_pos n).ne'
    (isCompact_simplexSet n).measure_ne_top

/-- The part of the simplex below coordinate-sum level `t`. -/
def simplexCap (n : ℕ) (t : ℝ) : Set (SimplexE n) :=
  simplexSet n ∩ {x | coordinateSum n x ≤ t}

theorem simplexCap_eq_smul {n : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    simplexCap n t = t • simplexSet n := by
  ext x
  constructor
  · rintro ⟨hx, hxt⟩
    refine Set.mem_smul_set.mpr ⟨t⁻¹ • x, ?_, ?_⟩
    · constructor
      · intro i
        change 0 ≤ t⁻¹ * x i
        exact mul_nonneg (inv_nonneg.mpr ht0.le) (hx.1 i)
      · rw [map_smul]
        simp only [smul_eq_mul]
        calc
          t⁻¹ * coordinateSum n x ≤ t⁻¹ * t :=
            mul_le_mul_of_nonneg_left hxt (inv_nonneg.mpr ht0.le)
          _ = 1 := inv_mul_cancel₀ ht0.ne'
    · simp [smul_smul, ht0.ne']
  · intro hx
    rcases Set.mem_smul_set.mp hx with ⟨y, hy, rfl⟩
    refine ⟨?_, ?_⟩
    · constructor
      · intro i
        change 0 ≤ t * y i
        exact mul_nonneg ht0.le (hy.1 i)
      · rw [map_smul]
        simp only [smul_eq_mul]
        calc
          t * coordinateSum n y ≤ t * 1 :=
            mul_le_mul_of_nonneg_left hy.2 ht0.le
          _ ≤ 1 := by simpa using ht1
    · change coordinateSum n (t • y) ≤ t
      rw [map_smul]
      simp only [smul_eq_mul]
      simpa using mul_le_mul_of_nonneg_left hy.2 ht0.le

theorem volumeReal_simplexCap {n : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    volume.real (simplexCap n t) = t ^ n * volume.real (simplexSet n) := by
  rw [simplexCap_eq_smul ht0 ht1, measureReal_def,
    Measure.addHaar_smul_of_nonneg volume ht0.le]
  simp only [finrank_euclideanSpace_fin]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg ht0.le n)]
  rw [measureReal_def]

/-- The exact strict-tail measure of the coordinate sum on the simplex. -/
theorem restrictSimplex_tail {n : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (volume.restrict (simplexSet n)).real {x | t < coordinateSum n x} =
      (1 - t ^ n) * volume.real (simplexSet n) := by
  let ν := volume.restrict (simplexSet n)
  let A : Set (SimplexE n) := {x | coordinateSum n x ≤ t}
  have hA : MeasurableSet A :=
    isClosed_le (coordinateSum n).continuous continuous_const |>.measurableSet
  have hset : {x : SimplexE n | t < coordinateSum n x} = Aᶜ := by
    ext x
    simp [A]
  have hν : ν.real A = volume.real (simplexCap n t) := by
    simp only [ν, measureReal_restrict_apply hA]
    congr 1
    ext x
    simp [A, simplexCap, and_comm]
  let : IsFiniteMeasure ν := ⟨by
    change volume.restrict (simplexSet n) univ < ∞
    rw [Measure.restrict_apply_univ]
    exact (isCompact_simplexSet n).measure_lt_top⟩
  rw [hset, measureReal_compl hA, measureReal_restrict_apply_univ, hν,
    volumeReal_simplexCap ht0 ht1]
  ring

/-- The first moment of the coordinate sum over the standard simplex. -/
theorem integral_coordinateSum (n : ℕ) :
    (∫ x in simplexSet n, coordinateSum n x ∂volume) =
      (n : ℝ) / ((n : ℝ) + 1) * volume.real (simplexSet n) := by
  let ν := volume.restrict (simplexSet n)
  let : IsFiniteMeasure ν := ⟨by
    change volume.restrict (simplexSet n) univ < ∞
    rw [Measure.restrict_apply_univ]
    exact (isCompact_simplexSet n).measure_lt_top⟩
  have hInt : Integrable (coordinateSum n) ν := by
    change IntegrableOn (coordinateSum n) (simplexSet n) volume
    exact (coordinateSum n).continuous.continuousOn.integrableOn_compact
      (isCompact_simplexSet n)
  have hnn : 0 ≤ᵐ[ν] coordinateSum n := by
    filter_upwards [ae_restrict_mem (isClosed_simplexSet n).measurableSet] with x hx
    rw [coordinateSum_apply]
    exact Finset.sum_nonneg fun i _ ↦ hx.1 i
  have hupper : coordinateSum n ≤ᵐ[ν] (fun _ ↦ (1 : ℝ)) := by
    filter_upwards [ae_restrict_mem (isClosed_simplexSet n).measurableSet] with x hx
    exact hx.2
  change (∫ x, coordinateSum n x ∂ν) =
    (n : ℝ) / ((n : ℝ) + 1) * volume.real (simplexSet n)
  rw [hInt.integral_eq_integral_meas_lt hnn]
  rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
      nullMeasurableSet_Ioi Ioc_subset_Ioi_self ?_]
  · rw [setIntegral_congr_fun measurableSet_Ioc fun t ht ↦
      restrictSimplex_tail ht.1 ht.2]
    rw [← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_mul_const]
    congr 1
    have h_one : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    have h_pow : IntervalIntegrable (fun t : ℝ ↦ t ^ n) volume 0 1 :=
      (continuous_id.pow n).intervalIntegrable 0 1
    rw [intervalIntegral.integral_sub h_one h_pow,
      intervalIntegral.integral_const, integral_pow]
    norm_num
    field_simp
    ring
  · apply Eventually.of_forall
    intro t ht
    have ht1 : 1 < t := by
      simp_all only [Set.mem_sdiff, mem_Ioi, mem_Ioc, not_and, not_le]
    have obs : ν {x | 1 < coordinateSum n x} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hupper] with x hx using not_lt.mpr hx
    rw [measureReal_def, ENNReal.toReal_eq_zero_iff]
    exact Or.inl <| measure_mono_null
      (fun _ hx ↦ ht1.trans hx) obs

/-- The volume centroid of the standard simplex. -/
def simplexCentroid (n : ℕ) : SimplexE n :=
  ⨍ x in simplexSet n, x ∂volume

/-- The scalar coordinate needed to locate the sharp supporting hyperplane. -/
theorem coordinateSum_simplexCentroid (n : ℕ) :
    coordinateSum n (simplexCentroid n) = (n : ℝ) / ((n : ℝ) + 1) := by
  have h_id : Integrable (fun x : SimplexE n ↦ x)
      (volume.restrict (simplexSet n)) := by
    change IntegrableOn (fun x : SimplexE n ↦ x) (simplexSet n) volume
    exact continuous_id.continuousOn.integrableOn_compact (isCompact_simplexSet n)
  have h_map :
      coordinateSum n (∫ x in simplexSet n, x ∂volume) =
        ∫ x in simplexSet n, coordinateSum n x ∂volume := by
    exact ((coordinateSum n).integral_comp_comm h_id).symm
  rw [simplexCentroid, setAverage_eq, map_smul, h_map, integral_coordinateSum]
  simp only [smul_eq_mul]
  field_simp [(volumeReal_simplexSet_pos n).ne']

/-- The sharp normalized coordinate-sum threshold in dimension `n`. -/
def sharpLevel (n : ℕ) : ℝ :=
  (n : ℝ) / ((n : ℝ) + 1)

/-- The simplex halfspace attaining the sharp Grünbaum fraction. -/
def sharpHalfspaceSet (n : ℕ) : Set (SimplexE n) :=
  {x | coordinateSum n x ≤ sharpLevel n}

theorem sharpLevel_pos {n : ℕ} (hn : 0 < n) : 0 < sharpLevel n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  exact div_pos hn' (by positivity)

theorem sharpLevel_le_one (n : ℕ) : sharpLevel n ≤ 1 := by
  apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
  norm_num

theorem simplexCentroid_mem_sharpHalfspaceSet (n : ℕ) :
    simplexCentroid n ∈ sharpHalfspaceSet n := by
  exact (coordinateSum_simplexCentroid n).le

theorem sharpHalfspaceSet_volume_ratio {n : ℕ} (hn : 0 < n) :
    volume.real (simplexSet n ∩ sharpHalfspaceSet n) /
        volume.real (simplexSet n) =
      sharpLevel n ^ n := by
  rw [show simplexSet n ∩ sharpHalfspaceSet n = simplexCap n (sharpLevel n) by rfl,
    volumeReal_simplexCap (sharpLevel_pos hn) (sharpLevel_le_one n)]
  field_simp [(volumeReal_simplexSet_pos n).ne']

/-- The standard simplex, regarded as a full-dimensional body in project
dimension `d + 1`. -/
def simplexFullBody (d : ℕ) : FullDimensionalConvexBody d where
  carrier := simplexSet (d + 1)
  convex' := convex_simplexSet (d + 1)
  isCompact' := isCompact_simplexSet (d + 1)
  interior_nonempty' := interior_simplexSet_nonempty (d + 1)

theorem simplexFullBody_centroid (d : ℕ) :
    (simplexFullBody d).centroid = simplexCentroid (d + 1) :=
  rfl

/-- The sharp halfspace for the standard simplex. -/
def sharpClosedHalfspace (d : ℕ) : ClosedHalfspace d where
  normal := coordinateSum (d + 1)
  threshold := sharpLevel (d + 1)
  normal_ne_zero := by
    intro h
    let i : Fin (d + 1) := ⟨0, Nat.succ_pos d⟩
    have h' := congrArg
      (fun L : SimplexE (d + 1) →L[ℝ] ℝ ↦
        L (EuclideanSpace.single i 1)) h
    simp [coordinateSum_apply, PiLp.single_apply] at h'

theorem simplexFullBody_centroid_mem_sharpClosedHalfspace (d : ℕ) :
    (simplexFullBody d).centroid ∈ sharpClosedHalfspace d := by
  change coordinateSum (d + 1) (simplexCentroid (d + 1)) ≤
    sharpLevel (d + 1)
  exact (coordinateSum_simplexCentroid (d + 1)).le

theorem sharpClosedHalfspace_ratio (d : ℕ) :
    halfspaceVolumeRatio (simplexFullBody d)
        (sharpClosedHalfspace d).normal
        (sharpClosedHalfspace d).threshold =
      grunbaumConstant d := by
  have h := sharpHalfspaceSet_volume_ratio (n := d + 1) (Nat.succ_pos d)
  rw [halfspaceVolumeRatio, ENNReal.toReal_div]
  change
    volume.real (simplexSet (d + 1) ∩ sharpHalfspaceSet (d + 1)) /
        volume.real (simplexSet (d + 1)) =
      grunbaumConstant d
  rw [h]
  simp only [sharpLevel, grunbaumConstant, Nat.cast_add, Nat.cast_one]
  congr 1
  ring

/-- `c` is a lower bound for every project convex body and every proper
closed halfspace containing its centroid. -/
def IsUniversalCentroidHalfspaceLowerBound (d : ℕ) (c : ℝ) : Prop :=
  ∀ (C : FullDimensionalConvexBody d) (H : ClosedHalfspace d),
    C.centroid ∈ H →
      c ≤ halfspaceVolumeRatio C H.normal H.threshold

/-- The simplex equality case shows that no universal centroid-halfspace
lower bound can exceed `grunbaumConstant d`. -/
theorem universalCentroidHalfspaceLowerBound_le_grunbaumConstant
    {d : ℕ} {c : ℝ}
    (hc : IsUniversalCentroidHalfspaceLowerBound d c) :
    c ≤ grunbaumConstant d := by
  have h := hc (simplexFullBody d) (sharpClosedHalfspace d)
    (simplexFullBody_centroid_mem_sharpClosedHalfspace d)
  rwa [sharpClosedHalfspace_ratio d] at h

end Grunbaum
