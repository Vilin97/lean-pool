/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Examples.RandomCheckerboard.Basic
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceLaw
import LeanPool.CoarseGraining.Homogenization.Probability.Source.Coarse.RescaledLaws
import LeanPool.CoarseGraining.Homogenization.Probability.Source.Coarse.RegIntegralAdapter
import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.RestrictionBridge

/-!
# Exact-source law for the refined Bernoulli checkerboard

The unit-cell checkerboard is only a restriction-local example: in dimension
at least two, sup-metric cell separation is weaker than Euclidean separation.
Here we use the dimension-safe refinement `d + 1`; after triadic rescaling,
Euclidean unit separation forces the two observations to use disjoint families
of Bernoulli coins.
-/

namespace Homogenization.Examples.RandomCheckerboard.Source

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The dimension-safe triadic refinement used by the exact-source checkerboard. -/
def refinementScale (d : ℕ) : ℕ := d + 1

private def ellipticityConstant (lam Lam : ℝ) : ℝ := min lam (min 1 Lam⁻¹)

private theorem ellipticityConstant_pos {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam) :
    0 < ellipticityConstant lam Lam := by
  unfold ellipticityConstant
  refine lt_min hlam ?_
  refine lt_min zero_lt_one ?_
  exact inv_pos.mpr (lt_of_lt_of_le hlam hle)

private theorem ellipticityConstant_le_one (lam Lam : ℝ) :
    ellipticityConstant lam Lam ≤ 1 := by
  unfold ellipticityConstant
  exact le_trans (min_le_right _ _) (min_le_left _ _)

private theorem ellipticityConstant_le_lam (lam Lam : ℝ) :
    ellipticityConstant lam Lam ≤ lam := by
  exact min_le_left _ _

private theorem Lam_le_ellipticityConstant_inv {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam) :
    Lam ≤ (ellipticityConstant lam Lam)⁻¹ := by
  apply (le_inv_comm₀ (lt_of_lt_of_le hlam hle) (ellipticityConstant_pos hlam hle)).2
  exact le_trans (min_le_right _ _) (min_le_right _ _)

/-- The literal exact-source carrier realization of one checkerboard sample. -/
def checkerCarrier {d : ℕ} (lam Lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ Lam)
    (ω : Sample d) : Source.Coarse.Carrier d where
  val := coeffField lam Lam ω
  property := by
    constructor
    · intro i j
      exact (measurable_pi_iff.1 (measurable_pi_iff.1
        (measurable_coeffField_spatial (lam := lam) (Lam := Lam) ω) i)) j
    · intro R _hR
      refine ⟨ellipticityConstant lam Lam, ellipticityConstant_pos hlam hle,
        ellipticityConstant_le_one lam Lam, ?_⟩
      intro x _hx
      exact (scalarMatrix_isEllipticMatrix_between (d := d) hlam hle
        (scalarAt_eq_lam_or_Lam (lam := lam) (Lam := Lam) ω x)).mono
          (ellipticityConstant_pos hlam hle)
          (ellipticityConstant_le_lam lam Lam)
          (Lam_le_ellipticityConstant_inv hlam hle)

/-- The refined exact-source carrier realization. -/
def refinedCheckerCarrier {d : ℕ} (lam Lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ Lam)
    (ω : Sample d) : Source.Coarse.Carrier d :=
  Source.Coarse.Carrier.rescale (refinementScale d) (checkerCarrier lam Lam hlam hle ω)

/-- The base source realization has the existing checkerboard as its regular realization. -/
private theorem coarseToRegular_checkerCarrier {d : ℕ} (lam Lam : ℝ)
    (hlam : 0 < lam) (hle : lam ≤ Lam) (ω : Sample d) :
    Source.Coarse.coarseToRegular (checkerCarrier lam Lam hlam hle ω) =
      checkerRegField lam Lam ω := by
  apply RegCoeffField.ext
  intro x
  rfl

private theorem measurable_checkerCarrier_local {d : ℕ} (lam Lam : ℝ)
    (hlam : 0 < lam) (hle : lam ≤ Lam) (U : Set (Vec d)) (hU : MeasurableSet U) :
    @Measurable (Sample d) (Source.Coarse.Carrier d)
      (sampleCellsSigma (cellsMeeting U)) (Source.Coarse.localSigma U hU)
      (checkerCarrier lam Lam hlam hle) := by
  have hregular : @Measurable (Sample d) (RegCoeffField d)
      (sampleCellsSigma (cellsMeeting U)) (LocalSigmaR U)
      (checkerRegField lam Lam) :=
    (measurable_checkerRegField_restrictionSigmaR lam Lam U hU).mono le_rfl
      (localSigmaR_le_restrictionSigmaR U hU)
  have hcomposite : @Measurable (Sample d) (RegCoeffField d)
      (sampleCellsSigma (cellsMeeting U)) (LocalSigmaR U)
      (Source.Coarse.coarseToRegular ∘ checkerCarrier lam Lam hlam hle) := by
    simpa only [Function.comp_apply, coarseToRegular_checkerCarrier] using! hregular
  rw [measurable_iff_comap_le]
  calc
    MeasurableSpace.comap (checkerCarrier lam Lam hlam hle) (Source.Coarse.localSigma U hU)
        ≤ MeasurableSpace.comap (checkerCarrier lam Lam hlam hle)
            (MeasurableSpace.comap Source.Coarse.coarseToRegular (LocalSigmaR U)) :=
      MeasurableSpace.comap_mono (Source.Coarse.coarseLocalSigma_le_comap_localSigmaR U hU)
    _ = MeasurableSpace.comap
          (Source.Coarse.coarseToRegular ∘ checkerCarrier lam Lam hlam hle) (LocalSigmaR U) :=
      MeasurableSpace.comap_comp
    _ ≤ sampleCellsSigma (cellsMeeting U) := hcomposite.comap_le

private theorem measurable_refinedCheckerCarrier_local {d : ℕ} (lam Lam : ℝ)
    (hlam : 0 < lam) (hle : lam ≤ Lam) (U : Set (Vec d)) (hU : MeasurableSet U) :
    @Measurable (Sample d) (Source.Coarse.Carrier d)
      (sampleCellsSigma (cellsMeeting (triadicDilateSet (refinementScale d) U)))
      (Source.Coarse.localSigma U hU)
      (refinedCheckerCarrier lam Lam hlam hle) := by
  let hDU : MeasurableSet (triadicDilateSet (refinementScale d) U) :=
    Source.Coarse.measurableSet_triadicDilateSet (refinementScale d) hU
  have hbase := measurable_checkerCarrier_local lam Lam hlam hle
    (triadicDilateSet (refinementScale d) U) hDU
  exact (Source.Coarse.measurable_rescale_localSigma (refinementScale d) U hU).comp hbase

private theorem euclideanNorm_lt_dim_succ_of_abs_lt_one {d : ℕ} {x : Vec d}
    (hx : ∀ i : Fin d, |x i| < 1) :
    euclideanNorm x < (d : ℝ) + 1 := by
  have hsq : ∀ i : Fin d, x i ^ 2 ≤ 1 := by
    intro i
    have hleft : -1 < x i := (abs_lt.mp (hx i)).1
    have hright : x i < 1 := (abs_lt.mp (hx i)).2
    have hmul : 0 < (1 - x i) * (1 + x i) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hsum : (∑ i : Fin d, x i ^ 2) ≤ (d : ℝ) := by
    calc
      ∑ i : Fin d, x i ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => hsq i
      _ = d := by simp
  have hsum_nonneg : 0 ≤ ∑ i : Fin d, |x i| ^ 2 := by positivity
  have hsum_abs : (∑ i : Fin d, |x i| ^ 2) ≤ (d : ℝ) := by
    simpa [sq_abs] using hsum
  have htarget : (∑ i : Fin d, |x i| ^ 2) < ((d : ℝ) + 1) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ d by positivity]
  unfold euclideanNorm
  change Real.sqrt (vecNormSq x) < (d : ℝ) + 1
  by_contra hnot
  have hle : (d : ℝ) + 1 ≤ Real.sqrt (vecNormSq x) :=
    le_of_not_gt hnot
  have hvec : vecNormSq x ≤ (d : ℝ) := by
    simpa [vecNormSq, vecDot, pow_two, sq_abs] using hsum_abs
  nlinarith [Real.sq_sqrt (vecNormSq_nonneg x), Real.sqrt_nonneg (vecNormSq x)]

private theorem euclideanDist_lt_dim_succ_of_mem_same_openUnitCell {d : ℕ}
    {x y : Vec d} {z : Lattice d} (hx : x ∈ openUnitCell z) (hy : y ∈ openUnitCell z) :
    euclideanDist x y < (d : ℝ) + 1 := by
  apply euclideanNorm_lt_dim_succ_of_abs_lt_one
  intro i
  have hx_i := hx i
  have hy_i := hy i
  have hsplit : x i - y i = (x i - (z i : ℝ)) - (y i - (z i : ℝ)) := by ring
  calc
    |(x - y) i| = |x i - y i| := rfl
    _ = |(x i - (z i : ℝ)) - (y i - (z i : ℝ))| := by rw [hsplit]
    _ ≤ |x i - (z i : ℝ)| + |y i - (z i : ℝ)| := by
      simpa [abs_sub_comm (z i : ℝ) (y i : ℝ)] using
        abs_sub_le (x i - (z i : ℝ)) 0 (y i - (z i : ℝ))
    _ < (1 / 2 : ℝ) + (1 / 2 : ℝ) := add_lt_add hx_i hy_i
    _ = 1 := by norm_num

private theorem dim_succ_le_triadicScale (d : ℕ) :
    (d : ℝ) + 1 ≤ (3 : ℝ) ^ refinementScale d := by
  have hnat : d + 1 ≤ 3 ^ (d + 1) := by
    induction d with
    | zero => norm_num
    | succ d hd =>
        calc
          d.succ + 1 = (d + 1) + 1 := by omega
          _ ≤ 3 ^ (d + 1) + 3 ^ (d + 1) :=
            Nat.add_le_add hd (Nat.one_le_pow (d + 1) 3 (by omega))
          _ = 3 ^ (d + 1) * 2 := by omega
          _ ≤ 3 ^ (d + 1) * 3 := Nat.mul_le_mul_left _ (by omega)
          _ = 3 ^ (d.succ + 1) := by
            simp [pow_succ, Nat.succ_eq_add_one]
  change (d : ℝ) + 1 ≤ (3 : ℝ) ^ (d + 1)
  exact_mod_cast hnat

private theorem disjoint_cellsMeeting_triadicDilate_of_euclideanUnitSeparated {d : ℕ}
    {U V : Set (Vec d)} (hUV : Source.Coarse.EuclideanUnitSeparated U V) :
    Disjoint (cellsMeeting (triadicDilateSet (refinementScale d) U))
      (cellsMeeting (triadicDilateSet (refinementScale d) V)) := by
  rw [Set.disjoint_left]
  intro z hzU hzV
  rcases hzU with ⟨x, hx, hxz⟩
  rcases hzV with ⟨y, hy, hyz⟩
  rcases hx with ⟨x0, hx0, rfl⟩
  rcases hy with ⟨y0, hy0, rfl⟩
  have hsep : 1 ≤ euclideanDist x0 y0 := hUV hx0 hy0
  have hscale : (d : ℝ) + 1 ≤ (3 : ℝ) ^ refinementScale d :=
    dim_succ_le_triadicScale d
  have hscaled : (d : ℝ) + 1 ≤
      euclideanDist (triadicDilateVec (refinementScale d) x0)
        (triadicDilateVec (refinementScale d) y0) := by
    rw [Source.Coarse.euclideanDist_triadicDilateVec]
    calc
      (d : ℝ) + 1 ≤ (3 : ℝ) ^ refinementScale d := hscale
      _ = (3 : ℝ) ^ refinementScale d * 1 := by ring
      _ ≤ (3 : ℝ) ^ refinementScale d * euclideanDist x0 y0 :=
        mul_le_mul_of_nonneg_left hsep (by positivity)
  have hsmall := euclideanDist_lt_dim_succ_of_mem_same_openUnitCell hxz hyz
  exact (not_le_of_gt hsmall) hscaled

private theorem measurable_checkerCarrier {d : ℕ} (lam Lam : ℝ)
    (hlam : 0 < lam) (hle : lam ≤ Lam) :
    Measurable (checkerCarrier (d := d) lam Lam hlam hle) := by
  simpa [Source.Coarse.globalSigma] using!
    (measurable_checkerCarrier_local (d := d) lam Lam hlam hle Set.univ MeasurableSet.univ).mono
      (sampleCellsSigma_le _) le_rfl

private theorem translate_checkerCarrier {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam) (z : Lattice d) (ω : Sample d) :
    Source.Coarse.Carrier.translate z (checkerCarrier lam Lam hlam hle ω) =
      checkerCarrier lam Lam hlam hle (shiftSample z ω) := by
  apply Subtype.ext
  funext x i j
  exact congrArg (fun a : RegCoeffField d => a x i j)
    (translateReg_checkerRegField (lam := lam) (Lam := Lam) z ω)

private theorem rotate_checkerCarrier {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam) (R : Mat d) (σ : Equiv.Perm (Fin d))
    (s : Fin d → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hRdef : ∀ i j, R i j = if i = σ j then s j else 0) (ω : Sample d) :
    Source.Coarse.Carrier.rotate R ⟨σ, s, hs, hRdef⟩
      (checkerCarrier lam Lam hlam hle ω) =
      checkerCarrier lam Lam hlam hle (reindexSample (signedLatticeEquiv σ s hs) ω) := by
  apply Subtype.ext
  funext x i j
  exact congrArg (fun a : RegCoeffField d => a x i j)
    (rotateReg_checkerRegField (lam := lam) (Lam := Lam) hs hRdef ⟨σ, s, hs, hRdef⟩ ω)

private theorem adjoint_checkerCarrier {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam) (ω : Sample d) :
    Source.Coarse.Carrier.adjoint (checkerCarrier lam Lam hlam hle ω) =
      checkerCarrier lam Lam hlam hle ω := by
  apply Subtype.ext
  funext x i j
  exact congrArg (fun a : RegCoeffField d => a x i j)
    (adjointReg_checkerRegField (lam := lam) (Lam := Lam) ω)

private def baseLaw (d : ℕ) (lam Lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ Lam)
    (p : ℝ≥0) (hp : p ≤ 1) : Measure (Source.Coarse.Carrier d) :=
  Measure.map (checkerCarrier lam Lam hlam hle) (sampleMeasure d p hp)

/-- The exact-source Bernoulli checkerboard law at the refined spatial scale. -/
def law (d : ℕ) (lam Lam : ℝ) (hlam : 0 < lam) (hle : lam ≤ Lam)
    (p : ℝ≥0) (hp : p ≤ 1) : Book.Ch04.SourceCoeffLaw d :=
  Source.Coarse.scaleNormalizedLaw (refinementScale d) (baseLaw d lam Lam hlam hle p hp)

private theorem baseLaw_stationary {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam) (p : ℝ≥0) (hp : p ≤ 1) :
    Source.Coarse.IsStationary (baseLaw d lam Lam hlam hle p hp) := by
  intro z
  rw [baseLaw]
  calc
    Measure.map (Source.Coarse.Carrier.translate z)
        (Measure.map (checkerCarrier lam Lam hlam hle) (sampleMeasure d p hp)) =
      Measure.map (fun ω : Sample d =>
        Source.Coarse.Carrier.translate z (checkerCarrier lam Lam hlam hle ω))
        (sampleMeasure d p hp) := by
          simpa [Function.comp] using! Measure.map_map
            (Source.Coarse.measurable_translate_globalSigma z)
            (measurable_checkerCarrier (d := d) lam Lam hlam hle)
            (μ := sampleMeasure d p hp)
    _ = Measure.map (fun ω : Sample d =>
        checkerCarrier lam Lam hlam hle (shiftSample z ω)) (sampleMeasure d p hp) := by
          congr 1
          funext ω
          exact translate_checkerCarrier hlam hle z ω
    _ = Measure.map (checkerCarrier lam Lam hlam hle)
        (Measure.map (shiftSample z) (sampleMeasure d p hp)) := by
          symm
          simpa [Function.comp] using! Measure.map_map
            (measurable_checkerCarrier (d := d) lam Lam hlam hle) (measurable_shiftSample z)
            (μ := sampleMeasure d p hp)
    _ = Measure.map (checkerCarrier lam Lam hlam hle) (sampleMeasure d p hp) := by
          rw [sampleMeasure_map_shiftSample z p hp]

private theorem baseLaw_isotropic_adjoint {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam) (p : ℝ≥0) (hp : p ≤ 1) :
    Source.Coarse.IsIsotropicAndAdjointInvariant (baseLaw d lam Lam hlam hle p hp) := by
  constructor
  · intro R hR
    obtain ⟨σ, s, hs, hRdef⟩ := hR
    let hR : IsSignedPermutationMatrix R := ⟨σ, s, hs, hRdef⟩
    let e : Lattice d ≃ Lattice d := signedLatticeEquiv σ s hs
    rw [baseLaw]
    calc
      Measure.map (Source.Coarse.Carrier.rotate R hR)
          (Measure.map (checkerCarrier lam Lam hlam hle) (sampleMeasure d p hp)) =
        Measure.map (fun ω : Sample d =>
          Source.Coarse.Carrier.rotate R hR (checkerCarrier lam Lam hlam hle ω))
          (sampleMeasure d p hp) := by
            simpa [Function.comp] using! Measure.map_map
              (Source.Coarse.measurable_rotate_globalSigma R hR)
              (measurable_checkerCarrier (d := d) lam Lam hlam hle)
              (μ := sampleMeasure d p hp)
      _ = Measure.map (fun ω : Sample d => checkerCarrier lam Lam hlam hle (reindexSample e ω))
          (sampleMeasure d p hp) := by
            congr 1
            funext ω
            exact rotate_checkerCarrier hlam hle R σ s hs hRdef ω
      _ = Measure.map (checkerCarrier lam Lam hlam hle)
          (Measure.map (reindexSample e) (sampleMeasure d p hp)) := by
            symm
            simpa [Function.comp, e] using! Measure.map_map
              (measurable_checkerCarrier (d := d) lam Lam hlam hle) (measurable_reindexSample e)
              (μ := sampleMeasure d p hp)
      _ = Measure.map (checkerCarrier lam Lam hlam hle) (sampleMeasure d p hp) := by
            rw [sampleMeasure_map_reindexSample e p hp]
  · rw [baseLaw]
    calc
      Measure.map Source.Coarse.Carrier.adjoint
          (Measure.map (checkerCarrier lam Lam hlam hle) (sampleMeasure d p hp)) =
        Measure.map (fun ω : Sample d =>
          Source.Coarse.Carrier.adjoint (checkerCarrier lam Lam hlam hle ω))
          (sampleMeasure d p hp) := by
            simpa [Function.comp] using! Measure.map_map
              Source.Coarse.measurable_adjoint_globalSigma
              (measurable_checkerCarrier (d := d) lam Lam hlam hle)
              (μ := sampleMeasure d p hp)
      _ = Measure.map (checkerCarrier lam Lam hlam hle) (sampleMeasure d p hp) := by
            congr 1
            funext ω
            exact adjoint_checkerCarrier hlam hle ω

instance instIsProbabilityMeasure_law (d : ℕ) (lam Lam : ℝ) (hlam : 0 < lam)
    (hle : lam ≤ Lam) (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (law d lam Lam hlam hle p hp) := by
  let : IsProbabilityMeasure (baseLaw d lam Lam hlam hle p hp) := by
    unfold baseLaw
    infer_instance
  unfold law
  exact Source.Coarse.isProbabilityMeasure_scaleNormalizedLaw _ _

theorem isProbabilityMeasure_law (d : ℕ) (lam Lam : ℝ) (hlam : 0 < lam)
    (hle : lam ≤ Lam) (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (law d lam Lam hlam hle p hp) := inferInstance

theorem stationary_law {d : ℕ} {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (p : ℝ≥0) (hp : p ≤ 1) : Book.Ch04.SourceStationaryLaw (law d lam Lam hlam hle p hp) := by
  exact (baseLaw_stationary hlam hle p hp).scaleNormalized (refinementScale d)

theorem isotropicAndAdjointInvariant_law {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam) (p : ℝ≥0) (hp : p ≤ 1) :
    Book.Ch04.SourceIsotropicAndAdjointInvariantLaw (law d lam Lam hlam hle p hp) := by
  exact (baseLaw_isotropic_adjoint hlam hle p hp).scaleNormalized (refinementScale d)

private theorem law_eq_map_refinedCheckerCarrier {d : ℕ} (lam Lam : ℝ)
    (hlam : 0 < lam) (hle : lam ≤ Lam) (p : ℝ≥0) (hp : p ≤ 1) :
    law d lam Lam hlam hle p hp =
      Measure.map (refinedCheckerCarrier lam Lam hlam hle) (sampleMeasure d p hp) := by
  unfold law Source.Coarse.scaleNormalizedLaw baseLaw
  rw [Measure.map_map (Source.Coarse.measurable_rescale_globalSigma _)
    (measurable_checkerCarrier (d := d) lam Lam hlam hle)]
  rfl

private theorem measurable_refinedCheckerCarrier {d : ℕ} (lam Lam : ℝ)
    (hlam : 0 < lam) (hle : lam ≤ Lam) :
    Measurable (refinedCheckerCarrier (d := d) lam Lam hlam hle) := by
  simpa only [refinedCheckerCarrier, Function.comp_apply] using!
    (Source.Coarse.measurable_rescale_globalSigma (d := d) (refinementScale d)).comp
      (measurable_checkerCarrier (d := d) lam Lam hlam hle)

theorem unitRangeDependent_law {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam) (p : ℝ≥0) (hp : p ≤ 1) :
    Book.Ch04.SourceUnitRangeDependentLaw (law d lam Lam hlam hle p hp) := by
  intro U V hU hV hUV
  rw [law_eq_map_refinedCheckerCarrier lam Lam hlam hle p hp]
  have hcells : Disjoint
      (cellsMeeting (triadicDilateSet (refinementScale d) U))
      (cellsMeeting (triadicDilateSet (refinementScale d) V)) :=
    disjoint_cellsMeeting_triadicDilate_of_euclideanUnitSeparated hUV
  have hIndCells : ProbabilityTheory.Indep
      (sampleCellsSigma (cellsMeeting (triadicDilateSet (refinementScale d) U)))
      (sampleCellsSigma (cellsMeeting (triadicDilateSet (refinementScale d) V)))
      (sampleMeasure d p hp) :=
    indep_sampleCellsSigma_of_disjoint hcells p hp
  rw [ProbabilityTheory.Indep_iff]
  intro s t hs ht
  have hs_ambient : MeasurableSet s :=
    Source.Coarse.localSigma_mono hU MeasurableSet.univ (Set.subset_univ _) s hs
  have ht_ambient : MeasurableSet t :=
    Source.Coarse.localSigma_mono hV MeasurableSet.univ (Set.subset_univ _) t ht
  have hst_ambient : MeasurableSet (s ∩ t) := hs_ambient.inter ht_ambient
  have hs_pre : @MeasurableSet (Sample d)
      (sampleCellsSigma (cellsMeeting (triadicDilateSet (refinementScale d) U)))
      ((refinedCheckerCarrier lam Lam hlam hle) ⁻¹' s) :=
    (measurable_refinedCheckerCarrier_local lam Lam hlam hle U hU) hs
  have ht_pre : @MeasurableSet (Sample d)
      (sampleCellsSigma (cellsMeeting (triadicDilateSet (refinementScale d) V)))
      ((refinedCheckerCarrier lam Lam hlam hle) ⁻¹' t) :=
    (measurable_refinedCheckerCarrier_local lam Lam hlam hle V hV) ht
  have hpre_ind :=
    (ProbabilityTheory.Indep_iff
      (sampleCellsSigma (cellsMeeting (triadicDilateSet (refinementScale d) U)))
      (sampleCellsSigma (cellsMeeting (triadicDilateSet (refinementScale d) V)))
      (sampleMeasure d p hp)).1 hIndCells
      ((refinedCheckerCarrier lam Lam hlam hle) ⁻¹' s)
      ((refinedCheckerCarrier lam Lam hlam hle) ⁻¹' t) hs_pre ht_pre
  have hmeas := measurable_refinedCheckerCarrier (d := d) lam Lam hlam hle
  rw [Measure.map_apply hmeas hst_ambient,
    Measure.map_apply hmeas hs_ambient,
    Measure.map_apply hmeas ht_ambient]
  simpa [Set.preimage_inter] using hpre_ind

theorem structuralLaw {d : ℕ} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam) (p : ℝ≥0) (hp : p ≤ 1) :
    Book.Ch04.SourceStructuralLaw (law d lam Lam hlam hle p hp) where
  stationary := stationary_law hlam hle p hp
  unit_range := unitRangeDependent_law hlam hle p hp
  isotropic_and_adjoint_invariant := isotropicAndAdjointInvariant_law hlam hle p hp

end
end Homogenization.Examples.RandomCheckerboard.Source
