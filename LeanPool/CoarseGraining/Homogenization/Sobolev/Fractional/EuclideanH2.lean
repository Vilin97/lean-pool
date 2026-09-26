/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.UnitCubeEuclideanL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Exact Euclidean fractional `H^s` carrier on the centered unit cube

This module is the literal `p = 2` fractional Sobolev side of the Chapter 1
constant-coefficient Dirichlet argument.  It deliberately does not identify
this seminorm with the continuous `K`-functional: that equivalence is a
separate analytic theorem.

The project carrier `Vec d` retains its product norm.  Both the domain metric
and the target magnitude below are instead spelled out through `euclideanDist`
and `HilbertVec.ofVec`, exactly as required by the source's Euclidean
convention for vector fields.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The source measure `fint_{□_0} dx ∫_{□_0} dy`: normalized volume in the
first variable and unnormalized restricted Lebesgue volume in the second. -/
noncomputable def euclideanHsProductMeasure (d : ℕ) : Measure (Vec d × Vec d) :=
  (unitCenteredCubeDomain d).normalizedVolume.prod
    (unitCenteredCubeDomain d).restrictedVolume

/-- The literal nonnegative integrand
`|F(x)-F(y)|² / |x-y|^(d + 2s)` of the `p = 2` fractional Sobolev seminorm.
The numerator uses the Euclidean Hilbert realization, not the ambient `Vec`
norm. -/
noncomputable def euclideanHsIntegrand {d : ℕ} (s : FractionalOrder)
    (F : UnitCubeEuclideanL2Field d) : Vec d × Vec d → ℝ≥0∞ :=
  fun z => ENNReal.ofReal
    (‖HilbertVec.ofVec (F z.1 - F z.2)‖ ^ 2 /
      Real.rpow (euclideanDist z.1 z.2) ((d : ℝ) + 2 * s.1))

/-- The squared exact fractional Sobolev quantity, before the `1/2` power. -/
noncomputable def euclideanHsEnergy {d : ℕ} (s : FractionalOrder)
    (F : UnitCubeEuclideanL2Field d) : ℝ≥0∞ :=
  ∫⁻ z, euclideanHsIntegrand s F z ∂euclideanHsProductMeasure d

/-- The exact extended `H^s` seminorm of a vector field on the centered unit
cube.  It is extended-valued so that no non-finiteness is silently totalized. -/
noncomputable def euclideanHsESeminorm {d : ℕ} (s : FractionalOrder)
    (F : UnitCubeEuclideanL2Field d) : ℝ≥0∞ :=
  euclideanHsEnergy s F ^ ((2 : ℝ)⁻¹)

/-- Membership in the exact fractional Euclidean `H^s` carrier: the literal
kernel is measurable and its source integral is finite. -/
structure MemEuclideanHs {d : ℕ} (s : FractionalOrder)
    (F : UnitCubeEuclideanL2Field d) : Prop where
  integrand_aemeasurable : AEMeasurable (euclideanHsIntegrand s F)
    (euclideanHsProductMeasure d)
  energy_lt_top : euclideanHsEnergy s F < ∞

theorem euclideanHsEnergy_eq_lintegral {d : ℕ} (s : FractionalOrder)
    (F : UnitCubeEuclideanL2Field d) :
    euclideanHsEnergy s F =
      ∫⁻ z, ENNReal.ofReal
        (‖HilbertVec.ofVec (F z.1 - F z.2)‖ ^ 2 /
          Real.rpow (euclideanDist z.1 z.2) ((d : ℝ) + 2 * s.1))
        ∂euclideanHsProductMeasure d := rfl

theorem euclideanHsESeminorm_eq_lintegral {d : ℕ} (s : FractionalOrder)
    (F : UnitCubeEuclideanL2Field d) :
    euclideanHsESeminorm s F =
      (∫⁻ z, ENNReal.ofReal
        (‖HilbertVec.ofVec (F z.1 - F z.2)‖ ^ 2 /
          Real.rpow (euclideanDist z.1 z.2) ((d : ℝ) + 2 * s.1))
        ∂euclideanHsProductMeasure d) ^ ((2 : ℝ)⁻¹) := rfl

theorem memEuclideanHs_iff {d : ℕ} {s : FractionalOrder}
    {F : UnitCubeEuclideanL2Field d} :
    MemEuclideanHs s F ↔
      AEMeasurable (euclideanHsIntegrand s F) (euclideanHsProductMeasure d) ∧
        euclideanHsEnergy s F < ∞ := by
  constructor
  · intro hF
    exact ⟨hF.integrand_aemeasurable, hF.energy_lt_top⟩
  · rintro ⟨hmeas, hfin⟩
    exact ⟨hmeas, hfin⟩

private theorem ae_restrictedVolume_of_ae_normalizedVolume {d : ℕ}
    {F G : UnitCubeEuclideanL2Field d}
    (hFG : F =ᵐ[(unitCenteredCubeDomain d).normalizedVolume] G) :
    F =ᵐ[(unitCenteredCubeDomain d).restrictedVolume] G := by
  rw [BoundedMeasurableDomain.normalizedVolume] at hFG
  have hc := ENNReal.inv_ne_zero.mpr (unitCenteredCubeDomain d).volume_ne_top
  unfold Filter.EventuallyEq at hFG ⊢
  rwa [ae_iff, Measure.smul_apply, smul_eq_mul, mul_eq_zero, or_iff_right hc, ← ae_iff] at hFG

/-- Altering a datum on a normalized-volume null set does not alter the
literal double-integral integrand except on a product-measure null set. -/
theorem euclideanHsIntegrand_congr_ae {d : ℕ} {s : FractionalOrder}
    {F G : UnitCubeEuclideanL2Field d}
    (hFG : F =ᵐ[(unitCenteredCubeDomain d).normalizedVolume] G) :
    euclideanHsIntegrand s F =ᵐ[euclideanHsProductMeasure d]
      euclideanHsIntegrand s G := by
  letI := (unitCenteredCubeDomain d).restrictedVolume_isFiniteMeasure
  have hFG_restricted : F =ᵐ[(unitCenteredCubeDomain d).restrictedVolume] G :=
    ae_restrictedVolume_of_ae_normalizedVolume hFG
  have hfst : (fun z : Vec d × Vec d => F z.1) =ᵐ[euclideanHsProductMeasure d]
      fun z => G z.1 := by
    rw [euclideanHsProductMeasure]
    exact Measure.quasiMeasurePreserving_fst.ae_eq hFG
  have hsnd : (fun z : Vec d × Vec d => F z.2) =ᵐ[euclideanHsProductMeasure d]
      fun z => G z.2 := by
    rw [euclideanHsProductMeasure]
    exact Measure.quasiMeasurePreserving_snd.ae_eq hFG_restricted
  filter_upwards [hfst, hsnd] with z hz1 hz2
  simp only [euclideanHsIntegrand, hz1, hz2]

/-- The squared source integral is invariant under normalized-volume a.e.
replacement of the vector field. -/
theorem euclideanHsEnergy_congr_ae {d : ℕ} {s : FractionalOrder}
    {F G : UnitCubeEuclideanL2Field d}
    (hFG : F =ᵐ[(unitCenteredCubeDomain d).normalizedVolume] G) :
    euclideanHsEnergy s F = euclideanHsEnergy s G := by
  unfold euclideanHsEnergy
  exact lintegral_congr_ae (euclideanHsIntegrand_congr_ae hFG)

/-- The exact extended fractional seminorm is invariant under
normalized-volume a.e. replacement of the vector field. -/
theorem euclideanHsESeminorm_congr_ae {d : ℕ} {s : FractionalOrder}
    {F G : UnitCubeEuclideanL2Field d}
    (hFG : F =ᵐ[(unitCenteredCubeDomain d).normalizedVolume] G) :
    euclideanHsESeminorm s F = euclideanHsESeminorm s G := by
  unfold euclideanHsESeminorm
  rw [euclideanHsEnergy_congr_ae hFG]

/-- Exact fractional membership is stable under normalized-volume a.e.
replacement of the field. -/
theorem memEuclideanHs_congr_ae {d : ℕ} {s : FractionalOrder}
    {F G : UnitCubeEuclideanL2Field d}
    (hFG : F =ᵐ[(unitCenteredCubeDomain d).normalizedVolume] G) :
    MemEuclideanHs s F ↔ MemEuclideanHs s G := by
  constructor
  · intro hF
    refine ⟨?_, ?_⟩
    · exact hF.integrand_aemeasurable.congr
        (euclideanHsIntegrand_congr_ae hFG)
    · rw [← euclideanHsEnergy_congr_ae hFG]
      exact hF.energy_lt_top
  · intro hG
    refine ⟨?_, ?_⟩
    · exact hG.integrand_aemeasurable.congr
        (euclideanHsIntegrand_congr_ae hFG.symm)
    · rw [euclideanHsEnergy_congr_ae hFG]
      exact hG.energy_lt_top

end

end Homogenization
