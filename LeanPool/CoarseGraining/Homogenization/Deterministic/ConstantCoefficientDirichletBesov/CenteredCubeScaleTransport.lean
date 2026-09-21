/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.ContinuousKRegularity
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH1Dilation
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.CenteredCubeEuclideanH2

/-!
# Centered-cube transport for the Dirichlet divergence problem

This module transports the zero-trace weak problem on `originCube d m` to the
centered unit cube.  The solution is normalized as
`wHat(x) = (3 ^ m)⁻¹ w((3 ^ m) x)`, so its weak gradient is the unscaled
pullback of the physical gradient.

## Main definitions

- `centeredCubeGradientEuclideanL2Field`: the physical gradient as an exact
  centered-cube Euclidean `L²` field.
- `centeredCubeNormalizedPullback`: the normalized zero-trace pullback.

## Main results

- `centeredCubeNormalizedPullback_grad`: exact pointwise gradient transport.
- `cubeDirichletDivergenceProblem_normalizedPullback`: transport of the weak
  divergence problem to the unit cube.
- `unitCubeGradientEuclideanL2Field_normalizedPullback_apply`: compatibility
  of the unit gradient carrier with centered-cube field pullback.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

private theorem castH10Function_apply {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H10Function U) (x : Vec d) :
    (hUV ▸ u).toH1Function.toFun x = u.toH1Function.toFun x := by
  subst V
  rfl

private theorem castH10Function_grad {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H10Function U) (x : Vec d) :
    (hUV ▸ u).toH1Function.grad x = u.toH1Function.grad x := by
  subst V
  rfl

private theorem centeredOpenCube_eq_smul_unitCenteredOpenCube
    {d : ℕ} (m : ℤ) :
    openCubeSet (originCube d m) =
      centeredCubeScale m • openCubeSet (originCube d 0) := by
  simpa only [centeredCubeScale, cubeScaleFactor_originCube] using
    openCubeSet_originCube_eq_smul_originCube_zero (d := d) m

private theorem unitCenteredOpenCube_eq_inv_smul_centeredOpenCube
    {d : ℕ} (m : ℤ) :
    openCubeSet (originCube d 0) =
      (centeredCubeScale m)⁻¹ • openCubeSet (originCube d m) := by
  rw [openCubeSet_originCube_eq_smul_originCube_zero (d := d) m]
  rw [show cubeScaleFactor (originCube d m) = centeredCubeScale m by rfl]
  rw [smul_smul, inv_mul_cancel₀ (centeredCubeScale_ne_zero m), one_smul]

/-- The gradient of a physical centered-cube zero-trace function, packaged as
the exact Euclidean `L²` field used by the fractional scale-transport API. -/
noncomputable def centeredCubeGradientEuclideanL2Field {d : ℕ} {m : ℤ}
    (w : H10Function (openCubeSet (originCube d m))) :
    CenteredCubeEuclideanL2Field d m where
  toField := fun x => w.toH1Function.grad x
  euclideanMemL2 := by
    rw [centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
    rw [memLp_piLp_iff]
    intro i
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using
      w.toH1Function.grad_memL2_normalizedCubeMeasure (Q := originCube d m) i

@[simp] theorem centeredCubeGradientEuclideanL2Field_apply {d : ℕ} {m : ℤ}
    (w : H10Function (openCubeSet (originCube d m))) (x : Vec d) :
    centeredCubeGradientEuclideanL2Field w x = w.toH1Function.grad x :=
  rfl

/-- The normalized zero-trace pullback
`wHat(x) = (3 ^ m)⁻¹ w((3 ^ m) x)` from the centered physical cube to the
centered unit cube. -/
noncomputable def centeredCubeNormalizedPullback {d : ℕ} {m : ℤ}
    (w : H10Function (openCubeSet (originCube d m))) :
    H10Function (openCubeSet (originCube d 0)) :=
  (centeredCubeScale m)⁻¹ • H10Function.unscale (centeredCubeScale_pos m)
    (centeredOpenCube_eq_smul_unitCenteredOpenCube m ▸ w)

/-- Pointwise value formula for the normalized zero-trace pullback. -/
@[simp] theorem centeredCubeNormalizedPullback_apply {d : ℕ} {m : ℤ}
    (w : H10Function (openCubeSet (originCube d m))) (x : Vec d) :
    centeredCubeNormalizedPullback w x =
      (centeredCubeScale m)⁻¹ * w (centeredCubeScale m • x) := by
  unfold centeredCubeNormalizedPullback
  change (centeredCubeScale m)⁻¹ *
      (H10Function.unscale (centeredCubeScale_pos m)
        (centeredOpenCube_eq_smul_unitCenteredOpenCube m ▸ w)).toH1Function.toFun x = _
  rw [H10Function.unscale_toH1Function, H1Function.unscale_toFun]
  rw [castH10Function_apply]

/-- The normalized pullback has the unscaled physical gradient pointwise. -/
@[simp] theorem centeredCubeNormalizedPullback_grad {d : ℕ} {m : ℤ}
    (w : H10Function (openCubeSet (originCube d m))) (x : Vec d) :
    (centeredCubeNormalizedPullback w).toH1Function.grad x =
      w.toH1Function.grad (centeredCubeScale m • x) := by
  unfold centeredCubeNormalizedPullback
  change (centeredCubeScale m)⁻¹ •
      (H10Function.unscale (centeredCubeScale_pos m)
        (centeredOpenCube_eq_smul_unitCenteredOpenCube m ▸ w)).toH1Function.grad x = _
  rw [H10Function.unscale_toH1Function, H1Function.unscale_grad]
  rw [castH10Function_grad]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [centeredCubeScale_ne_zero m]

/-- Inverse normalized transport of a unit-cube zero-trace test:
`phi_m(y) = (3 ^ m) phi((3 ^ m)⁻¹ y)`. -/
private noncomputable def centeredCubeNormalizedTestPushforward {d : ℕ} {m : ℤ}
    (phi : H10Function (openCubeSet (originCube d 0))) :
    H10Function (openCubeSet (originCube d m)) :=
  centeredCubeScale m • H10Function.unscale (inv_pos.mpr (centeredCubeScale_pos m))
    (unitCenteredOpenCube_eq_inv_smul_centeredOpenCube m ▸ phi)

private theorem centeredCubeNormalizedTestPushforward_apply {d : ℕ} {m : ℤ}
    (phi : H10Function (openCubeSet (originCube d 0))) (y : Vec d) :
    centeredCubeNormalizedTestPushforward (m := m) phi y =
      centeredCubeScale m * phi ((centeredCubeScale m)⁻¹ • y) := by
  unfold centeredCubeNormalizedTestPushforward
  change centeredCubeScale m *
      (H10Function.unscale (inv_pos.mpr (centeredCubeScale_pos m))
        (unitCenteredOpenCube_eq_inv_smul_centeredOpenCube m ▸ phi)).toH1Function.toFun y = _
  rw [H10Function.unscale_toH1Function, H1Function.unscale_toFun]
  rw [castH10Function_apply]

private theorem centeredCubeNormalizedTestPushforward_grad {d : ℕ} {m : ℤ}
    (phi : H10Function (openCubeSet (originCube d 0))) (y : Vec d) :
    (centeredCubeNormalizedTestPushforward (m := m) phi).toH1Function.grad y =
      phi.toH1Function.grad ((centeredCubeScale m)⁻¹ • y) := by
  unfold centeredCubeNormalizedTestPushforward
  change centeredCubeScale m •
      (H10Function.unscale (inv_pos.mpr (centeredCubeScale_pos m))
        (unitCenteredOpenCube_eq_inv_smul_centeredOpenCube m ▸ phi)).toH1Function.grad y = _
  rw [H10Function.unscale_toH1Function, H1Function.unscale_grad]
  rw [castH10Function_grad]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [centeredCubeScale_ne_zero m]

private theorem setIntegral_centeredCube_comp_dilation {d : ℕ} {m : ℤ}
    (f : Vec d → ℝ) :
    ∫ x in openCubeSet (originCube d 0), f (centeredCubeScale m • x)
        ∂volume =
      ((centeredCubeScale m) ^ d)⁻¹ *
        ∫ y in openCubeSet (originCube d m), f y ∂volume := by
  have hchange := Measure.setIntegral_comp_smul_of_pos
    (μ := volume) (f := f) (s := openCubeSet (originCube d 0))
    (centeredCubeScale_pos m)
  rw [← centeredOpenCube_eq_smul_unitCenteredOpenCube (d := d) m]
    at hchange
  simpa only [centeredCubeScale, cubeScaleFactor_originCube, Module.finrank_fin_fun,
    smul_eq_mul] using hchange

/-- Exact transport of `-Delta w = div h` from a centered physical cube to
the centered unit cube under the normalized pullback. -/
theorem cubeDirichletDivergenceProblem_normalizedPullback {d : ℕ} {m : ℤ}
    (h : CenteredCubeEuclideanL2Field d m)
    (w : H10Function (openCubeSet (originCube d m)))
    (hproblem : CubeDirichletDivergenceProblem (originCube d m) w h) :
    CubeDirichletDivergenceProblem (originCube d 0)
      (centeredCubeNormalizedPullback w) h.pullbackToUnit := by
  intro phi
  let psi : H10Function (openCubeSet (originCube d m)) :=
    centeredCubeNormalizedTestPushforward (m := m) phi
  have hweak := hproblem psi
  let lhsPhysical : Vec d → ℝ := fun y =>
    vecDot (w.toH1Function.grad y) (psi.toH1Function.grad y)
  let rhsPhysical : Vec d → ℝ := fun y =>
    vecDot (h y) (psi.toH1Function.grad y)
  have hlhsPointwise (x : Vec d) :
      lhsPhysical (centeredCubeScale m • x) =
        vecDot ((centeredCubeNormalizedPullback w).toH1Function.grad x)
          (phi.toH1Function.grad x) := by
    dsimp only [lhsPhysical]
    rw [centeredCubeNormalizedPullback_grad]
    rw [show psi.toH1Function.grad (centeredCubeScale m • x) =
        phi.toH1Function.grad x by
      rw [show psi = centeredCubeNormalizedTestPushforward (m := m) phi by rfl]
      rw [centeredCubeNormalizedTestPushforward_grad]
      congr 2
      simp [centeredCubeScale_ne_zero m]]
  have hrhsPointwise (x : Vec d) :
      rhsPhysical (centeredCubeScale m • x) =
        vecDot (h.pullbackToUnit x) (phi.toH1Function.grad x) := by
    dsimp only [rhsPhysical]
    rw [CenteredCubeEuclideanL2Field.pullbackToUnit_apply]
    rw [show psi.toH1Function.grad (centeredCubeScale m • x) =
        phi.toH1Function.grad x by
      rw [show psi = centeredCubeNormalizedTestPushforward (m := m) phi by rfl]
      rw [centeredCubeNormalizedTestPushforward_grad]
      congr 2
      simp [centeredCubeScale_ne_zero m]]
  have hlhsChange :
      ∫ x in openCubeSet (originCube d 0),
          vecDot ((centeredCubeNormalizedPullback w).toH1Function.grad x)
            (phi.toH1Function.grad x) ∂volume =
        ((centeredCubeScale m) ^ d)⁻¹ *
          ∫ y in openCubeSet (originCube d m), lhsPhysical y ∂volume := by
    rw [← setIntegral_centeredCube_comp_dilation lhsPhysical]
    apply integral_congr_ae
    filter_upwards with x
    exact (hlhsPointwise x).symm
  have hrhsChange :
      ∫ x in openCubeSet (originCube d 0),
          vecDot (h.pullbackToUnit x) (phi.toH1Function.grad x) ∂volume =
        ((centeredCubeScale m) ^ d)⁻¹ *
          ∫ y in openCubeSet (originCube d m), rhsPhysical y ∂volume := by
    rw [← setIntegral_centeredCube_comp_dilation rhsPhysical]
    apply integral_congr_ae
    filter_upwards with x
    exact (hrhsPointwise x).symm
  rw [hlhsChange, hrhsChange]
  change ((centeredCubeScale m) ^ d)⁻¹ *
      (∫ y in openCubeSet (originCube d m),
        vecDot (w.toH1Function.grad y) (psi.toH1Function.grad y) ∂volume) = _
  rw [hweak]
  ring

/-- The unit gradient field is pointwise the centered-cube pullback of the
physical gradient field. -/
theorem unitCubeGradientEuclideanL2Field_normalizedPullback_apply {d : ℕ}
    {m : ℤ} (w : H10Function (openCubeSet (originCube d m))) (x : Vec d) :
    unitCubeGradientEuclideanL2Field (centeredCubeNormalizedPullback w) x =
      (centeredCubeGradientEuclideanL2Field w).pullbackToUnit x := by
  rw [unitCubeGradientEuclideanL2Field_apply,
    centeredCubeNormalizedPullback_grad,
    CenteredCubeEuclideanL2Field.pullbackToUnit_apply,
    centeredCubeGradientEuclideanL2Field_apply]

/-- The unit gradient field agrees almost everywhere with the pullback of the
physical gradient field. -/
theorem unitCubeGradientEuclideanL2Field_normalizedPullback_ae_eq {d : ℕ}
    {m : ℤ} (w : H10Function (openCubeSet (originCube d m))) :
    unitCubeGradientEuclideanL2Field (centeredCubeNormalizedPullback w) =ᵐ[
      (unitCenteredCubeDomain d).normalizedVolume]
        (centeredCubeGradientEuclideanL2Field w).pullbackToUnit :=
  Filter.Eventually.of_forall
    (unitCubeGradientEuclideanL2Field_normalizedPullback_apply w)

end

end Homogenization
