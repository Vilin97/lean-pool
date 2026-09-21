/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.AxisCubeNormalizedLp
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.LocalHarmonicReplacement
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.LocalWeightedTail

/-! # Local Comparison Bridges -/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

open Filter MeasureTheory Set

/-!
# Local Hilbert-vector bridges for the comparison step

The local harmonic replacement is formulated with the weak PDE datum in the
plain `Vec d` carrier, while the good-`lambda` tails are Hilbert-vector valued.
This module records the exact restriction, norm, and a.e.-transport bridges
between those two interfaces.  In particular, the inverse Hilbert-vector map
is used only to prepare the weak datum, so no dimension factor is introduced
there.
-/

/-- A globally square-integrable Hilbert-vector realization yields an `L²`
plain-vector datum on every local set. -/
theorem memVectorL2_of_memLp_hilbertifyVecField
    {d : ℕ} {B : Set (Vec d)} {H : Vec d → Vec d}
    (hH : MemLp (hilbertifyVecField H) 2 volume) :
    MemVectorL2 B H := by
  let T : HilbertVec d →L[ℝ] Vec d :=
    (HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap
  simpa [MemVectorL2, volumeMeasureOn, hilbertifyVecField, Function.comp_def, T] using
    T.comp_memLp' (hH.restrict B)

/-- The local Hilbert-valued field inherits square integrability by measure
restriction. -/
theorem memHilbertVectorL2_restrict_of_memLp_hilbertifyVecField
    {d : ℕ} {B : Set (Vec d)} {H : Vec d → Vec d}
    (hH : MemLp (hilbertifyVecField H) 2 volume) :
    MemHilbertVectorL2 B (hilbertifyVecField H) :=
  hH.restrict B

/-- The norm of the Hilbert-vector `L²` representative is exactly the real
value of the Hilbert-valued `eLpNorm`. -/
theorem norm_toHilbertVectorL2OfVecField_eq_eLpNorm_toReal
    {d : ℕ} {B : Set (Vec d)} {H : Vec d → Vec d}
    (hH : MemVectorL2 B H) :
    ‖toHilbertVectorL2OfVecField hH‖ =
      (eLpNorm (hilbertifyVecField H) 2 (volume.restrict B)).toReal := by
  exact Lp.norm_toLp _ (memHilbertVectorL2_hilbertifyVecField hH)

private theorem eLpNorm_two_rpow_eq_lintegral_enorm
    {α E : Type*} [MeasurableSpace α] [ENorm E]
    (μ : Measure α) (F : α → E) :
    (eLpNorm F 2 μ) ^ (2 : ℝ) = ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  rw [← ENNReal.rpow_mul]
  norm_num

/-- The squared local Hilbert `L²` norm is the finite real value of its raw
squared norm integral. -/
theorem norm_sq_toHilbertVectorL2OfVecField_eq_lintegral_enorm
    {d : ℕ} {B : Set (Vec d)} {H : Vec d → Vec d}
    (hH : MemVectorL2 B H) :
    ‖toHilbertVectorL2OfVecField hH‖ ^ (2 : ℕ) =
      (∫⁻ x in B, ‖hilbertifyVecField H x‖ₑ ^ (2 : ℝ) ∂volume).toReal := by
  let hHH : MemHilbertVectorL2 B (hilbertifyVecField H) :=
    memHilbertVectorL2_hilbertifyVecField hH
  have hpow := eLpNorm_two_rpow_eq_lintegral_enorm (volume.restrict B)
    (hilbertifyVecField H)
  calc
    ‖toHilbertVectorL2OfVecField hH‖ ^ (2 : ℕ) =
        (eLpNorm (hilbertifyVecField H) 2 (volume.restrict B)).toReal ^ (2 : ℕ) := by
          rw [norm_toHilbertVectorL2OfVecField_eq_eLpNorm_toReal hH]
    _ = ((eLpNorm (hilbertifyVecField H) 2 (volume.restrict B)) ^ (2 : ℝ)).toReal := by
          rw [← ENNReal.toReal_rpow]
          norm_num
    _ = (∫⁻ x in B, ‖hilbertifyVecField H x‖ₑ ^ (2 : ℝ) ∂volume).toReal := by
          rw [hpow]

/-- The Hilbert-valued local `eLpNorm` in the preceding bridge is finite. -/
theorem eLpNorm_hilbertifyVecField_restrict_lt_top
    {d : ℕ} {B : Set (Vec d)} {H : Vec d → Vec d}
    (hH : MemVectorL2 B H) :
    eLpNorm (hilbertifyVecField H) 2 (volume.restrict B) < ∞ :=
  (memHilbertVectorL2_hilbertifyVecField hH).eLpNorm_lt_top

/-- Restricted a.e. equality transports the square-weighted measure built
from the two local representatives. -/
theorem sqWeightedMeasure_eq_of_ae_eq_restrict
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {B : Set α} {F G : α → E}
    (hFG : F =ᵐ[μ.restrict B] G) :
    sqWeightedMeasure F (μ.restrict B) = sqWeightedMeasure G (μ.restrict B) := by
  apply MeasureTheory.withDensity_congr_ae
  filter_upwards [hFG] with x hx
  rw [hx]

/-- On a measurable local set, restricted a.e. equality transports the
original square-weighted measure on every subset of that set. -/
theorem sqWeightedMeasure_apply_inter_eq_of_ae_eq_restrict
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {B T : Set α} (hB : MeasurableSet B) {F G : α → E}
    (hFG : F =ᵐ[μ.restrict B] G) :
    sqWeightedMeasure F μ (T ∩ B) = sqWeightedMeasure G μ (T ∩ B) := by
  have hlocal : sqWeightedMeasure F (μ.restrict B) = sqWeightedMeasure G (μ.restrict B) :=
    sqWeightedMeasure_eq_of_ae_eq_restrict hFG
  have hF : sqWeightedMeasure F (μ.restrict B) T = sqWeightedMeasure F μ (T ∩ B) := by
    change ((μ.restrict B).withDensity fun x => ENNReal.ofReal (‖F x‖ ^ (2 : ℕ))) T =
      (μ.withDensity fun x => ENNReal.ofReal (‖F x‖ ^ (2 : ℕ))) (T ∩ B)
    rw [← MeasureTheory.restrict_withDensity hB]
    exact Measure.restrict_apply' hB
  have hG : sqWeightedMeasure G (μ.restrict B) T = sqWeightedMeasure G μ (T ∩ B) := by
    change ((μ.restrict B).withDensity fun x => ENNReal.ofReal (‖G x‖ ^ (2 : ℕ))) T =
      (μ.withDensity fun x => ENNReal.ofReal (‖G x‖ ^ (2 : ℕ))) (T ∩ B)
    rw [← MeasureTheory.restrict_withDensity hB]
    exact Measure.restrict_apply' hB
  calc
    sqWeightedMeasure F μ (T ∩ B) = sqWeightedMeasure F (μ.restrict B) T := hF.symm
    _ = sqWeightedMeasure G (μ.restrict B) T := by rw [hlocal]
    _ = sqWeightedMeasure G μ (T ∩ B) := hG

/-- A local norm-power lintegral is invariant under restricted a.e. equality. -/
theorem local_lintegral_norm_rpow_eq_of_ae_eq_restrict
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {B : Set α} {F G : α → E} (q : ℝ)
    (hFG : F =ᵐ[μ.restrict B] G) :
    (∫⁻ x in B, ENNReal.ofReal (‖F x‖ ^ q) ∂μ) =
      ∫⁻ x in B, ENNReal.ofReal (‖G x‖ ^ q) ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [hFG] with x hx
  rw [hx]

/-- The local squared difference integral is invariant when its first field
is replaced by a restricted-a.e.-equal representative. -/
theorem local_lintegral_sub_norm_sq_eq_of_ae_eq_restrict
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {B : Set α} {F G V : α → E}
    (hFG : F =ᵐ[μ.restrict B] G) :
    (∫⁻ x in B, ENNReal.ofReal (‖F x - V x‖ ^ (2 : ℕ)) ∂μ) =
      ∫⁻ x in B, ENNReal.ofReal (‖G x - V x‖ ^ (2 : ℕ)) ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [hFG] with x hx
  rw [hx]

/-- Minkowski's triangle inequality on the normalized measure of an axis
cube, in the Hilbert-valued form consumed by the comparison argument. -/
theorem axisCubeNormalized_eLpNorm_two_add_le
    {d : ℕ} (z : Vec d) (L : ℝ) {F G : Vec d → HilbertVec d}
    (hF : AEStronglyMeasurable F (axisCubeNormalizedMeasure z L))
    (hG : AEStronglyMeasurable G (axisCubeNormalizedMeasure z L)) :
    eLpNorm (F + G) 2 (axisCubeNormalizedMeasure z L) ≤
      eLpNorm F 2 (axisCubeNormalizedMeasure z L) +
        eLpNorm G 2 (axisCubeNormalizedMeasure z L) :=
  eLpNorm_add_le hF hG (by norm_num)

/-- Scalar multiplication has its exact expected effect on the normalized
axis-cube Hilbert `L²` `eLpNorm`. -/
theorem axisCubeNormalized_eLpNorm_two_const_smul
    {d : ℕ} (z : Vec d) (L c : ℝ) (F : Vec d → HilbertVec d) :
    eLpNorm (c • F) 2 (axisCubeNormalizedMeasure z L) =
      ‖c‖ₑ * eLpNorm F 2 (axisCubeNormalizedMeasure z L) :=
  eLpNorm_const_smul c F 2 _

/-- The corresponding triangle inequality for the typed local Hilbert `L²`
representatives of two vector fields on an axis cube. -/
theorem norm_toHilbertVectorL2OfVecField_add_le_axisCube
    {d : ℕ} (z : Vec d) (L : ℝ) {F G : Vec d → Vec d}
    (hF : MemVectorL2 (axisCube z L) F) (hG : MemVectorL2 (axisCube z L) G) :
    ‖toHilbertVectorL2OfVecField (hF.add hG)‖ ≤
      ‖toHilbertVectorL2OfVecField hF‖ + ‖toHilbertVectorL2OfVecField hG‖ := by
  rw [toHilbertVectorL2OfVecField_add hF hG]
  exact norm_add_le _ _

end CubeCalderonZygmund

end

end Homogenization
