/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.OverlapGeometry
public import LeanPool.CoarseGraining.Homogenization.Sobolev.FiniteLpExponent
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareW1p.Dilation
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareW1p.Translation

/-! # Overlap Cube -/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

/-- One finite-`p` Poincare constant, selected on the unit centered cube,
controls every open overlap cube after its explicit scale factor. -/
theorem exists_overlapCube_meanZero_poincare_constant {d : ℕ} {q : ℝ}
    (hq : 1 < q) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : TriadicCube d)
        (u : W1pMeanZeroFunction (openOverlapCubeSet S) (ENNReal.ofReal q)),
        u.valueLpSeminorm ≤
          (C * overlapCubeScaleFactor S) * u.gradientCoordLpSeminormSum := by
  let hCunit : W1pPoincareEstimate (openCubeSet (originCube d 0)) (ENNReal.ofReal q) :=
    w1pPoincareEstimate_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet (originCube d 0)) hq
  refine ⟨hCunit.fixedValue, hCunit.constant_nonneg, ?_⟩
  intro S
  rw [openOverlapCubeSet_eq_translateSet_smul_originCube_zero S]
  intro u
  let a : ℝ := overlapCubeScaleFactor S
  have ha : 0 < a := overlapCubeScaleFactor_pos S
  let hCdil : W1pPoincareEstimate
      (a • openCubeSet (originCube d 0)) (ENNReal.ofReal q) :=
    hCunit.dilate ha ENNReal.ofReal_ne_top
  let hCtrans : W1pPoincareEstimate
      (translateSet (cubeCenter S) (a • openCubeSet (originCube d 0)))
        (ENNReal.ofReal q) :=
    hCdil.translate (cubeCenter S)
  calc
    u.valueLpSeminorm ≤ hCtrans.fixedValue * u.gradientCoordLpSeminormSum :=
      hCtrans.bound u
    _ = (hCunit.fixedValue * overlapCubeScaleFactor S) *
          u.gradientCoordLpSeminormSum := by
          simp only [hCtrans, hCdil, W1pPoincareEstimate.translate_constant,
            W1pPoincareEstimate.dilate_constant]
          simp only [a]
          ring

/-- The overlap-cube Poincare estimate in the finite-exponent carrier used by
the finite-`p` Sobolev and Calderon--Zygmund layers. -/
theorem exists_overlapCube_meanZero_poincare_constant_finite {d : ℕ}
    (q : FiniteLpExponent) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : TriadicCube d)
        (u : W1pMeanZeroFunction (openOverlapCubeSet S) q.exponent),
        u.valueLpSeminorm ≤
          (C * overlapCubeScaleFactor S) * u.gradientCoordLpSeminormSum := by
  have hq : 1 < q.exponent.toReal := by
    have hq' : (1 : ℝ≥0∞).toReal < q.exponent.toReal :=
      (ENNReal.toReal_lt_toReal (by norm_num) q.lt_top.ne).2 q.one_lt
    simpa using hq'
  rcases exists_overlapCube_meanZero_poincare_constant (d := d) hq with
    ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro S
  rw [← ENNReal.ofReal_toReal q.lt_top.ne]
  exact hC S

/-! The following reverse-translation package is deliberately private: it is
the one local transport needed to retain the source-facing subaverage form of
Poincare on overlap cubes. -/

private noncomputable def castW1pDomain {d : ℕ} {U V : Set (Vec d)} {p : ENNReal}
    (hUV : U = V) (u : W1pFunction U p) : W1pFunction V p :=
  hUV ▸ u

@[simp] private theorem castW1pDomain_toFun {d : ℕ} {U V : Set (Vec d)} {p : ENNReal}
    (hUV : U = V) (u : W1pFunction U p) :
    (castW1pDomain hUV u).toFun = u.toFun := by
  subst V
  rfl

@[simp] private theorem castW1pDomain_grad {d : ℕ} {U V : Set (Vec d)} {p : ENNReal}
    (hUV : U = V) (u : W1pFunction U p) :
    (castW1pDomain hUV u).grad = u.grad := by
  subst V
  rfl

private noncomputable def untranslateForOverlapPoincare {d : ℕ}
    {U : Set (Vec d)} {p : ENNReal} (z : Vec d)
    (u : W1pFunction (translateSet z U) p) : W1pFunction U p := by
  have hset : translateSet (-z) (translateSet z U) = U := by
    rw [translateSet_translateSet]
    simp
  exact castW1pDomain hset (u.translate (-z))

@[simp] private theorem untranslateForOverlapPoincare_toFun {d : ℕ}
    {U : Set (Vec d)} {p : ENNReal} (z : Vec d)
    (u : W1pFunction (translateSet z U) p) (x : Vec d) :
    (untranslateForOverlapPoincare z u).toFun x = u.toFun (x + z) := by
  simp [untranslateForOverlapPoincare, W1pFunction.translate, sub_eq_add_neg]

@[simp] private theorem untranslateForOverlapPoincare_grad {d : ℕ}
    {U : Set (Vec d)} {p : ENNReal} (z : Vec d)
    (u : W1pFunction (translateSet z U) p) (x : Vec d) :
    (untranslateForOverlapPoincare z u).grad x = u.grad (x + z) := by
  simp [untranslateForOverlapPoincare, W1pFunction.translate, sub_eq_add_neg]

private theorem integralAverage_untranslateForOverlapPoincare_eq {d : ℕ}
    {U : Set (Vec d)} {p : ENNReal} (z : Vec d)
    (u : W1pFunction (translateSet z U) p) :
    integralAverage U (untranslateForOverlapPoincare z u).toFun =
      integralAverage (translateSet z U) u.toFun := by
  change
    (volume U).toReal⁻¹ *
        ∫ x in U, (untranslateForOverlapPoincare z u).toFun x ∂volume =
      (volume (translateSet z U)).toReal⁻¹ *
        ∫ x in translateSet z U, u.toFun x ∂volume
  rw [volume_translateSet_eq]
  simp only [untranslateForOverlapPoincare_toFun]
  rw [← setIntegral_comp_addRight_translateSet]

private theorem subAverageLpSeminorm_untranslateForOverlapPoincare_eq {d : ℕ}
    {U : Set (Vec d)} {p : ENNReal} (z : Vec d)
    (u : W1pFunction (translateSet z U) p) :
    (untranslateForOverlapPoincare z u).subAverageLpSeminorm =
      u.subAverageLpSeminorm := by
  let V : Set (Vec d) := translateSet z U
  let T : Vec d → Vec d := fun x => x + z
  let hμ := measurePreserving_addRight_restrict_translateSet (d := d) z U
  unfold W1pFunction.subAverageLpSeminorm
  rw [integralAverage_untranslateForOverlapPoincare_eq]
  have hfun :
      (fun x => (untranslateForOverlapPoincare z u).toFun x -
        integralAverage V u.toFun) =
        (fun x => u.toFun x - integralAverage V u.toFun) ∘ T := by
    funext x
    simp [T, Function.comp]
  rw [hfun]
  exact congrArg ENNReal.toReal (by
    simpa [V, T, Function.comp, volumeMeasureOn] using
      (MeasureTheory.eLpNorm_comp_measurePreserving
        (g := fun x => u.toFun x - integralAverage V u.toFun) (p := p)
        (u.memLp.aestronglyMeasurable.sub continuous_const.aestronglyMeasurable) hμ))

private theorem gradientCoordLpSeminormSum_untranslateForOverlapPoincare_eq {d : ℕ}
    {U : Set (Vec d)} {p : ENNReal} (z : Vec d)
    (u : W1pFunction (translateSet z U) p) :
    (untranslateForOverlapPoincare z u).gradientCoordLpSeminormSum =
      u.gradientCoordLpSeminormSum := by
  unfold W1pFunction.gradientCoordLpSeminormSum W1pFunction.gradCoordLpSeminorm
  let V : Set (Vec d) := translateSet z U
  let T : Vec d → Vec d := fun x => x + z
  let hμ := measurePreserving_addRight_restrict_translateSet (d := d) z U
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg ENNReal.toReal
  have hfun : (fun x => (untranslateForOverlapPoincare z u).grad x i) =
      (fun x => u.grad x i) ∘ T := by
    funext x
    simp [T, Function.comp]
  rw [hfun]
  simpa [V, T, Function.comp, volumeMeasureOn] using
    (MeasureTheory.eLpNorm_comp_measurePreserving
      (g := fun x => u.grad x i) (p := p) (u.gradMemLp i).aestronglyMeasurable hμ)

private theorem exists_overlapCube_subAverage_poincare_constant_ofReal {d : ℕ} [NeZero d]
    {q : ℝ} (hq : 1 < q) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : TriadicCube d) (u : W1pFunction (openOverlapCubeSet S) (ENNReal.ofReal q)),
        u.subAverageLpSeminorm ≤
          (C * overlapCubeScaleFactor S) * u.gradientCoordLpSeminormSum := by
  let U0 : Set (Vec d) := openCubeSet (originCube d 0)
  obtain ⟨C, hC_nonneg, hC⟩ :=
    W1pFunction.exists_subAverage_poincare_constant_of_isOpenBoundedConvexDomain
      (U := U0) (isOpenBoundedConvexDomain_openCubeSet (originCube d 0)) hq
  refine ⟨C, hC_nonneg, ?_⟩
  intro S
  rw [openOverlapCubeSet_eq_translateSet_smul_originCube_zero S]
  intro u
  let a : ℝ := overlapCubeScaleFactor S
  let z : Vec d := cubeCenter S
  have ha : 0 < a := by simpa [a] using overlapCubeScaleFactor_pos S
  have hp_top : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  let uD : W1pFunction (a • U0) (ENNReal.ofReal q) :=
    untranslateForOverlapPoincare z u
  let u0 : W1pFunction U0 (ENNReal.ofReal q) := uD.unscale ha
  have hbase := hC u0
  have htrans_value : uD.subAverageLpSeminorm = u.subAverageLpSeminorm :=
    subAverageLpSeminorm_untranslateForOverlapPoincare_eq z u
  have htrans_grad : uD.gradientCoordLpSeminormSum = u.gradientCoordLpSeminormSum :=
    gradientCoordLpSeminormSum_untranslateForOverlapPoincare_eq z u
  have hdil_value : u0.subAverageLpSeminorm =
      W1pFunction.dilationLpFactor d (ENNReal.ofReal q) a⁻¹ * uD.subAverageLpSeminorm :=
    W1pFunction.subAverageLpSeminorm_unscale_eq ha hp_top uD
  have hdil_grad : u0.gradientCoordLpSeminormSum =
      a * W1pFunction.dilationLpFactor d (ENNReal.ofReal q) a⁻¹ *
        uD.gradientCoordLpSeminormSum :=
    W1pFunction.gradientCoordLpSeminormSum_unscale_eq ha hp_top uD
  have hfactor_pos : 0 < W1pFunction.dilationLpFactor d (ENNReal.ofReal q) a⁻¹ :=
    W1pFunction.dilationLpFactor_pos d (ENNReal.ofReal q) (inv_pos.mpr ha)
  have hscaled :
      W1pFunction.dilationLpFactor d (ENNReal.ofReal q) a⁻¹ *
          u.subAverageLpSeminorm ≤
        C * (a * W1pFunction.dilationLpFactor d (ENNReal.ofReal q) a⁻¹ *
          u.gradientCoordLpSeminormSum) := by
    simpa [u0, uD, htrans_value, htrans_grad, hdil_value, hdil_grad] using hbase
  have hscaled' :
      W1pFunction.dilationLpFactor d (ENNReal.ofReal q) a⁻¹ *
          u.subAverageLpSeminorm ≤
        W1pFunction.dilationLpFactor d (ENNReal.ofReal q) a⁻¹ *
          ((C * a) * u.gradientCoordLpSeminormSum) := by
    calc
      W1pFunction.dilationLpFactor d (ENNReal.ofReal q) a⁻¹ *
          u.subAverageLpSeminorm ≤
        C * (a * W1pFunction.dilationLpFactor d (ENNReal.ofReal q) a⁻¹ *
          u.gradientCoordLpSeminormSum) := hscaled
      _ = W1pFunction.dilationLpFactor d (ENNReal.ofReal q) a⁻¹ *
          ((C * a) * u.gradientCoordLpSeminormSum) := by ring
  have hresult : u.subAverageLpSeminorm ≤
      (C * a) * u.gradientCoordLpSeminormSum :=
    (mul_le_mul_iff_right₀ hfactor_pos).mp hscaled'
  simpa [a] using hresult

/-- One finite-`p` Poincare constant controls the subaverage seminorm on every
open overlap cube.  This is the scalar form consumed by normalized vector
interfaces. -/
theorem exists_overlapCube_subAverage_poincare_constant_finite {d : ℕ} [NeZero d]
    (q : FiniteLpExponent) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : TriadicCube d) (u : W1pFunction (openOverlapCubeSet S) q.exponent),
        u.subAverageLpSeminorm ≤
          (C * overlapCubeScaleFactor S) * u.gradientCoordLpSeminormSum := by
  have hq : 1 < q.exponent.toReal := by
    have hq' : (1 : ℝ≥0∞).toReal < q.exponent.toReal :=
      (ENNReal.toReal_lt_toReal (by norm_num) q.lt_top.ne).2 q.one_lt
    simpa using hq'
  rcases exists_overlapCube_subAverage_poincare_constant_ofReal (d := d) hq with
    ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro S
  rw [← ENNReal.ofReal_toReal q.lt_top.ne]
  exact hC S

end

end Homogenization
