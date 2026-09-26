/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.PDE.DirichletRHS
public import LeanPool.CoarseGraining.Homogenization.PDE.NeumannRHS
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH1Translation
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.CubeTranslationTransport

/-! # Cube Translation Finite P -/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

variable {d : ℕ}

/-!
# Finite-exponent translation on triadic cubes

This file packages the exact translation from an arbitrary triadic cube to the
centered cube of the same scale.  Both directions use `normalizedCubeMeasure`;
in particular, no unnormalized-volume factor enters the transport.
-/

/-- Pull a field on `Q` back to the centered cube of the same scale. -/
def pullbackToOrigin {E : Type*} (Q : TriadicCube d) (F : Vec d → E) : Vec d → E :=
  fun x ↦ F (x + triadicCubeShift Q)

/-- Push a field on the centered cube to `Q`. -/
def pushforwardFromOrigin {E : Type*} (Q : TriadicCube d) (F : Vec d → E) : Vec d → E :=
  fun x ↦ F (x - triadicCubeShift Q)

@[simp] theorem pushforwardFromOrigin_pullbackToOrigin {E : Type*}
    (Q : TriadicCube d) (F : Vec d → E) :
    pushforwardFromOrigin Q (pullbackToOrigin Q F) = F := by
  funext x
  simp [pushforwardFromOrigin, pullbackToOrigin, sub_eq_add_neg, add_assoc]

@[simp] theorem pullbackToOrigin_pushforwardFromOrigin {E : Type*}
    (Q : TriadicCube d) (F : Vec d → E) :
    pullbackToOrigin Q (pushforwardFromOrigin Q F) = F := by
  funext x
  simp [pushforwardFromOrigin, pullbackToOrigin, sub_eq_add_neg, add_assoc]

/-- Subtracting the cube shift preserves the normalized cube measure in the
reverse direction. -/
theorem measurePreserving_subRight_normalizedCubeMeasure_originCube
    (Q : TriadicCube d) :
    MeasurePreserving (fun x : Vec d ↦ x - triadicCubeShift Q)
      (normalizedCubeMeasure Q)
      (normalizedCubeMeasure (originCube d Q.scale)) := by
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addRight (triadicCubeShift Q)
  have he : MeasurePreserving e
      (normalizedCubeMeasure (originCube d Q.scale))
      (normalizedCubeMeasure Q) := by
    simpa [e] using measurePreserving_addRight_normalizedCubeMeasure_originCube Q
  simpa [e, sub_eq_add_neg] using MeasurePreserving.symm e he

/-- `MemLp` is preserved when a field is pulled back to the centered cube. -/
theorem memLp_pullbackToOrigin {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) {p : ℝ≥0∞} {F : Vec d → E}
    (hF : MemLp F p (normalizedCubeMeasure Q)) :
    MemLp (pullbackToOrigin Q F) p
      (normalizedCubeMeasure (originCube d Q.scale)) := by
  simpa [pullbackToOrigin] using!
    hF.comp_measurePreserving
      (measurePreserving_addRight_normalizedCubeMeasure_originCube Q)

/-- `MemLp` is preserved when a centered field is pushed forward to `Q`. -/
theorem memLp_pushforwardFromOrigin {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) {p : ℝ≥0∞} {F : Vec d → E}
    (hF : MemLp F p (normalizedCubeMeasure (originCube d Q.scale))) :
    MemLp (pushforwardFromOrigin Q F) p (normalizedCubeMeasure Q) := by
  simpa [pushforwardFromOrigin] using!
    hF.comp_measurePreserving
      (measurePreserving_subRight_normalizedCubeMeasure_originCube Q)

/-- Pullback preserves the extended normalized `Lᵖ` norm. -/
theorem eLpNorm_pullbackToOrigin_eq {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (p : ℝ≥0∞) {F : Vec d → E}
    (hF : AEStronglyMeasurable F (normalizedCubeMeasure Q)) :
    eLpNorm (pullbackToOrigin Q F) p
        (normalizedCubeMeasure (originCube d Q.scale)) =
      eLpNorm F p (normalizedCubeMeasure Q) := by
  simpa [pullbackToOrigin, Function.comp_def] using!
    (eLpNorm_comp_measurePreserving
      (g := F) (p := p) hF
      (measurePreserving_addRight_normalizedCubeMeasure_originCube Q))

/-- Pushforward preserves the extended normalized `Lᵖ` norm. -/
theorem eLpNorm_pushforwardFromOrigin_eq {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (p : ℝ≥0∞) {F : Vec d → E}
    (hF : AEStronglyMeasurable F
      (normalizedCubeMeasure (originCube d Q.scale))) :
    eLpNorm (pushforwardFromOrigin Q F) p (normalizedCubeMeasure Q) =
      eLpNorm F p (normalizedCubeMeasure (originCube d Q.scale)) := by
  simpa [pushforwardFromOrigin, Function.comp_def] using!
    (eLpNorm_comp_measurePreserving
      (g := F) (p := p) hF
      (measurePreserving_subRight_normalizedCubeMeasure_originCube Q))

/-- Pullback preserves the real normalized cube `Lᵖ` norm. -/
theorem cubeLpNorm_pullbackToOrigin_eq {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (p : ℝ≥0∞) {F : Vec d → E}
    (hF : AEStronglyMeasurable F (normalizedCubeMeasure Q)) :
    cubeLpNorm (originCube d Q.scale) p (pullbackToOrigin Q F) =
      cubeLpNorm Q p F := by
  have htrans : AEStronglyMeasurable (pullbackToOrigin Q F)
      (normalizedCubeMeasure (originCube d Q.scale)) := by
    simpa only [pullbackToOrigin, Function.comp_def] using
      hF.comp_measurePreserving
        (measurePreserving_addRight_normalizedCubeMeasure_originCube Q)
  rw [cubeLpNorm_eq_eLpNorm_toReal _ _ _ htrans,
    cubeLpNorm_eq_eLpNorm_toReal _ _ _ hF]
  exact congrArg ENNReal.toReal (eLpNorm_pullbackToOrigin_eq Q p hF)

/-- Pushforward preserves the real normalized cube `Lᵖ` norm. -/
theorem cubeLpNorm_pushforwardFromOrigin_eq {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (p : ℝ≥0∞) {F : Vec d → E}
    (hF : AEStronglyMeasurable F
      (normalizedCubeMeasure (originCube d Q.scale))) :
    cubeLpNorm Q p (pushforwardFromOrigin Q F) =
      cubeLpNorm (originCube d Q.scale) p F := by
  have htrans : AEStronglyMeasurable (pushforwardFromOrigin Q F)
      (normalizedCubeMeasure Q) := by
    simpa only [pushforwardFromOrigin, Function.comp_def] using
      hF.comp_measurePreserving
        (measurePreserving_subRight_normalizedCubeMeasure_originCube Q)
  rw [cubeLpNorm_eq_eLpNorm_toReal _ _ _ htrans,
    cubeLpNorm_eq_eLpNorm_toReal _ _ _ hF]
  exact congrArg ENNReal.toReal (eLpNorm_pushforwardFromOrigin_eq Q p hF)

/-- Raw vector fields retain `MemLp` under pullback. -/
theorem memLp_vec_pullbackToOrigin (Q : TriadicCube d) {p : ℝ≥0∞}
    {F : Vec d → Vec d} (hF : MemLp F p (normalizedCubeMeasure Q)) :
    MemLp (pullbackToOrigin Q F) p
      (normalizedCubeMeasure (originCube d Q.scale)) :=
  memLp_pullbackToOrigin Q hF

/-- Hilbert-realized vector fields retain `MemLp` under pullback. -/
theorem memLp_hilbertVec_pullbackToOrigin (Q : TriadicCube d) {p : ℝ≥0∞}
    {F : Vec d → HilbertVec d}
    (hF : MemLp F p (normalizedCubeMeasure Q)) :
    MemLp (pullbackToOrigin Q F) p
      (normalizedCubeMeasure (originCube d Q.scale)) :=
  memLp_pullbackToOrigin Q hF

/-- Raw vector fields retain their extended normalized norm under pullback. -/
theorem eLpNorm_vec_pullbackToOrigin_eq (Q : TriadicCube d) (p : ℝ≥0∞)
    {F : Vec d → Vec d}
    (hF : AEStronglyMeasurable F (normalizedCubeMeasure Q)) :
    eLpNorm (pullbackToOrigin Q F) p
        (normalizedCubeMeasure (originCube d Q.scale)) =
      eLpNorm F p (normalizedCubeMeasure Q) :=
  eLpNorm_pullbackToOrigin_eq Q p hF

/-- Hilbert-realized vector fields retain their extended normalized norm under
pullback. -/
theorem eLpNorm_hilbertVec_pullbackToOrigin_eq (Q : TriadicCube d) (p : ℝ≥0∞)
    {F : Vec d → HilbertVec d}
    (hF : AEStronglyMeasurable F (normalizedCubeMeasure Q)) :
    eLpNorm (pullbackToOrigin Q F) p
        (normalizedCubeMeasure (originCube d Q.scale)) =
      eLpNorm F p (normalizedCubeMeasure Q) :=
  eLpNorm_pullbackToOrigin_eq Q p hF

/-- Raw vector fields retain their real normalized cube norm under pullback. -/
theorem cubeLpNorm_vec_pullbackToOrigin_eq (Q : TriadicCube d) (p : ℝ≥0∞)
    {F : Vec d → Vec d}
    (hF : AEStronglyMeasurable F (normalizedCubeMeasure Q)) :
    cubeLpNorm (originCube d Q.scale) p (pullbackToOrigin Q F) =
      cubeLpNorm Q p F :=
  cubeLpNorm_pullbackToOrigin_eq Q p hF

/-- Hilbert-realized vector fields retain their real normalized cube norm under
pullback. -/
theorem cubeLpNorm_hilbertVec_pullbackToOrigin_eq
    (Q : TriadicCube d) (p : ℝ≥0∞) {F : Vec d → HilbertVec d}
    (hF : AEStronglyMeasurable F (normalizedCubeMeasure Q)) :
    cubeLpNorm (originCube d Q.scale) p (pullbackToOrigin Q F) =
      cubeLpNorm Q p F :=
  cubeLpNorm_pullbackToOrigin_eq Q p hF

/-- Pull an arbitrary-cube zero-trace function back to the centered cube. -/
noncomputable def untranslateH10ToOrigin (Q : TriadicCube d)
    (u : H10Function (openCubeSet Q)) :
    H10Function (openCubeSet (originCube d Q.scale)) := by
  let Q₀ : TriadicCube d := originCube d Q.scale
  let U₀ : Set (Vec d) := openCubeSet Q₀
  let z : Vec d := triadicCubeShift Q
  have hU : openCubeSet Q = translateSet z U₀ := by
    simpa [Q₀, U₀, z] using openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  let uT : H10Function (translateSet z U₀) :=
    { toH1Function :=
        { toFun := u.toH1Function.toFun
          grad := u.toH1Function.grad
          memL2 := by simpa [← hU] using u.toH1Function.memL2
          gradMemL2 := by
            intro i
            simpa [← hU] using u.toH1Function.gradMemL2 i
          hasWeakGradient := by simpa [← hU] using u.toH1Function.hasWeakGradient }
      approx := u.approx
      approx_smooth := u.approx_smooth
      approx_hasCompactSupport := u.approx_hasCompactSupport
      approx_support_subset := by
        intro n
        simpa [← hU] using u.approx_support_subset n
      tendsto_approx := by simpa [← hU] using u.tendsto_approx
      tendsto_approx_grad := by
        intro i
        simpa [← hU] using u.tendsto_approx_grad i }
  exact H10Function.untranslate z uT

@[simp] theorem untranslateH10ToOrigin_toFun (Q : TriadicCube d)
    (u : H10Function (openCubeSet Q)) (x : Vec d) :
    (untranslateH10ToOrigin Q u).toH1Function.toFun x =
      u.toH1Function.toFun (x + triadicCubeShift Q) := by
  simp [untranslateH10ToOrigin, H10Function.untranslate, H1Function.untranslate]

@[simp] theorem untranslateH10ToOrigin_grad (Q : TriadicCube d)
    (u : H10Function (openCubeSet Q)) (x : Vec d) :
    (untranslateH10ToOrigin Q u).toH1Function.grad x =
      u.toH1Function.grad (x + triadicCubeShift Q) := by
  simp [untranslateH10ToOrigin, H10Function.untranslate, H1Function.untranslate]

/-- Pushing the centered pullback gradient forward recovers the original
arbitrary-cube gradient exactly. -/
@[simp] theorem pushforwardFromOrigin_untranslateH10ToOrigin_grad
    (Q : TriadicCube d) (u : H10Function (openCubeSet Q)) :
    pushforwardFromOrigin Q (untranslateH10ToOrigin Q u).toH1Function.grad =
      u.toH1Function.grad := by
  funext x
  simp [pushforwardFromOrigin, sub_eq_add_neg, add_assoc]

/-- Pull an arbitrary-cube mean-zero function back to the centered cube. -/
noncomputable def untranslateH1MeanZeroToOrigin (Q : TriadicCube d)
    (u : H1MeanZeroFunction (openCubeSet Q)) :
    H1MeanZeroFunction (openCubeSet (originCube d Q.scale)) := by
  let Q₀ : TriadicCube d := originCube d Q.scale
  let U₀ : Set (Vec d) := openCubeSet Q₀
  let z : Vec d := triadicCubeShift Q
  have hU : openCubeSet Q = translateSet z U₀ := by
    simpa [Q₀, U₀, z] using openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  let uT : H1MeanZeroFunction (translateSet z U₀) :=
    { toH1Function :=
        { toFun := u.toH1Function.toFun
          grad := u.toH1Function.grad
          memL2 := by simpa [← hU] using u.toH1Function.memL2
          gradMemL2 := by
            intro i
            simpa [← hU] using u.toH1Function.gradMemL2 i
          hasWeakGradient := by simpa [← hU] using u.toH1Function.hasWeakGradient }
      meanZero := by simpa [MeanZeroOn, ← hU] using u.meanZero }
  exact H1MeanZeroFunction.untranslate z uT

@[simp] theorem untranslateH1MeanZeroToOrigin_toFun (Q : TriadicCube d)
    (u : H1MeanZeroFunction (openCubeSet Q)) (x : Vec d) :
    (untranslateH1MeanZeroToOrigin Q u).toH1Function.toFun x =
      u.toH1Function.toFun (x + triadicCubeShift Q) := by
  simp [untranslateH1MeanZeroToOrigin, H1MeanZeroFunction.untranslate,
    H1Function.untranslate]

@[simp] theorem untranslateH1MeanZeroToOrigin_grad (Q : TriadicCube d)
    (u : H1MeanZeroFunction (openCubeSet Q)) (x : Vec d) :
    (untranslateH1MeanZeroToOrigin Q u).toH1Function.grad x =
      u.toH1Function.grad (x + triadicCubeShift Q) := by
  simp [untranslateH1MeanZeroToOrigin, H1MeanZeroFunction.untranslate,
    H1Function.untranslate]

/-- Pushing the centered mean-zero pullback gradient forward recovers the
original arbitrary-cube gradient exactly. -/
@[simp] theorem pushforwardFromOrigin_untranslateH1MeanZeroToOrigin_grad
    (Q : TriadicCube d) (u : H1MeanZeroFunction (openCubeSet Q)) :
    pushforwardFromOrigin Q
        (untranslateH1MeanZeroToOrigin Q u).toH1Function.grad =
      u.toH1Function.grad := by
  funext x
  simp [pushforwardFromOrigin, sub_eq_add_neg, add_assoc]

/-- Pull the constant-coefficient Dirichlet divergence equation with datum
`-F` from an arbitrary cube to the centered cube of the same scale. -/
theorem isZeroTraceDirichletRhsWeakSolution_untranslateH10ToOrigin
    (Q : TriadicCube d) (A : Mat d) {u : H10Function (openCubeSet Q)}
    {F : Vec d → Vec d}
    (hu : IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d ↦ A) (openCubeSet Q) u (fun x ↦ -F x)) :
    IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d ↦ A)
      (openCubeSet (originCube d Q.scale)) (untranslateH10ToOrigin Q u)
      (fun x ↦ -(pullbackToOrigin Q F x)) := by
  let Q₀ : TriadicCube d := originCube d Q.scale
  let U₀ : Set (Vec d) := openCubeSet Q₀
  let z : Vec d := triadicCubeShift Q
  have hU : openCubeSet Q = translateSet z U₀ := by
    simpa [Q₀, U₀, z] using openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  intro φ
  let φT : H10Function (translateSet z U₀) := φ.translate z
  let φQ : H10Function (openCubeSet Q) :=
    { toH1Function :=
        { toFun := φT.toH1Function.toFun
          grad := φT.toH1Function.grad
          memL2 := by simpa [hU] using φT.toH1Function.memL2
          gradMemL2 := by
            intro i
            simpa [hU] using φT.toH1Function.gradMemL2 i
          hasWeakGradient := by simpa [hU] using φT.toH1Function.hasWeakGradient }
      approx := φT.approx
      approx_smooth := φT.approx_smooth
      approx_hasCompactSupport := φT.approx_hasCompactSupport
      approx_support_subset := by
        intro n
        simpa [hU] using φT.approx_support_subset n
      tendsto_approx := by simpa [hU] using φT.tendsto_approx
      tendsto_approx_grad := by
        intro i
        simpa [hU] using φT.tendsto_approx_grad i }
  have hEq := hu φQ
  have hleft :=
    setIntegral_comp_addRight_translateSet (d := d) (E := ℝ) z U₀
      (fun x ↦ vecDot (matVecMul A (u.toH1Function.grad x))
        (φT.toH1Function.grad x))
  have hright :=
    setIntegral_comp_addRight_translateSet (d := d) (E := ℝ) z U₀
      (fun x ↦ vecDot (-F x) (φT.toH1Function.grad x))
  calc
    ∫ x in openCubeSet Q₀,
        vecDot (matVecMul A
          ((untranslateH10ToOrigin Q u).toH1Function.grad x))
          (φ.toH1Function.grad x) ∂volume
        = ∫ x in translateSet z U₀,
            vecDot (matVecMul A (u.toH1Function.grad x))
              (φT.toH1Function.grad x) ∂volume := by
          simpa [Q₀, U₀, z, φT, H10Function.translate, H1Function.translate,
            sub_eq_add_neg, add_assoc] using hleft
    _ = ∫ x in translateSet z U₀, vecDot (-F x) (φT.toH1Function.grad x)
          ∂volume := by simpa [φQ, hU] using hEq
    _ = ∫ x in U₀, vecDot (-F (x + z)) (φ.toH1Function.grad x) ∂volume := by
          symm
          simpa [φT, H10Function.translate, H1Function.translate,
            sub_eq_add_neg, add_assoc] using hright
    _ = ∫ x in openCubeSet Q₀,
          vecDot (-(pullbackToOrigin Q F x)) (φ.toH1Function.grad x) ∂volume := by
          simp [Q₀, U₀, z, pullbackToOrigin]

/-- Pull the constant-coefficient Neumann divergence equation with datum `-F`
from an arbitrary cube to the centered cube of the same scale. -/
theorem isMeanZeroNeumannRhsWeakSolution_untranslateH1MeanZeroToOrigin
    (Q : TriadicCube d) (A : Mat d)
    {u : H1MeanZeroFunction (openCubeSet Q)} {F : Vec d → Vec d}
    (hu : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d ↦ A) (openCubeSet Q) u (fun x ↦ -F x)) :
    IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d ↦ A)
      (openCubeSet (originCube d Q.scale)) (untranslateH1MeanZeroToOrigin Q u)
      (fun x ↦ -(pullbackToOrigin Q F x)) := by
  let Q₀ : TriadicCube d := originCube d Q.scale
  let U₀ : Set (Vec d) := openCubeSet Q₀
  let z : Vec d := triadicCubeShift Q
  have hU : openCubeSet Q = translateSet z U₀ := by
    simpa [Q₀, U₀, z] using openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  intro φ
  let φT : H1MeanZeroFunction (translateSet z U₀) := φ.translate z
  let φQ : H1MeanZeroFunction (openCubeSet Q) :=
    { toH1Function :=
        { toFun := φT.toH1Function.toFun
          grad := φT.toH1Function.grad
          memL2 := by simpa [hU] using φT.toH1Function.memL2
          gradMemL2 := by
            intro i
            simpa [hU] using φT.toH1Function.gradMemL2 i
          hasWeakGradient := by simpa [hU] using φT.toH1Function.hasWeakGradient }
      meanZero := by simpa [MeanZeroOn, hU] using φT.meanZero }
  have hEq := hu φQ
  have hleft :=
    setIntegral_comp_addRight_translateSet (d := d) (E := ℝ) z U₀
      (fun x ↦ vecDot (matVecMul A (u.toH1Function.grad x))
        (φT.toH1Function.grad x))
  have hright :=
    setIntegral_comp_addRight_translateSet (d := d) (E := ℝ) z U₀
      (fun x ↦ vecDot (-F x) (φT.toH1Function.grad x))
  calc
    ∫ x in openCubeSet Q₀,
        vecDot (matVecMul A
          ((untranslateH1MeanZeroToOrigin Q u).toH1Function.grad x))
          (φ.toH1Function.grad x) ∂volume
        = ∫ x in translateSet z U₀,
            vecDot (matVecMul A (u.toH1Function.grad x))
              (φT.toH1Function.grad x) ∂volume := by
          simpa [Q₀, U₀, z, φT, H1MeanZeroFunction.translate,
            H1Function.translate, sub_eq_add_neg, add_assoc] using hleft
    _ = ∫ x in translateSet z U₀, vecDot (-F x) (φT.toH1Function.grad x)
          ∂volume := by simpa [φQ, hU] using hEq
    _ = ∫ x in U₀, vecDot (-F (x + z)) (φ.toH1Function.grad x) ∂volume := by
          symm
          simpa [φT, H1MeanZeroFunction.translate, H1Function.translate,
            sub_eq_add_neg, add_assoc] using hright
    _ = ∫ x in openCubeSet Q₀,
          vecDot (-(pullbackToOrigin Q F x)) (φ.toH1Function.grad x) ∂volume := by
          simp [Q₀, U₀, z, pullbackToOrigin]

end CubeCalderonZygmund

end

end Homogenization
