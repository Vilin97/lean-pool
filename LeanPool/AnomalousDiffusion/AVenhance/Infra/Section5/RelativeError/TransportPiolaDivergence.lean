/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TransportPiolaFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.PiolaFormula
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.SpaceLap

/-! # RelativeError: divergence of the transported gradient potential -/

@[expose] public section

noncomputable section

open Homogenization
open AVenhance
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

theorem TransportPiolaDivergence.spatialGradientMatrix_contDiff_one
    {Y : Vec 2 → Vec 2} (hY : ContDiff ℝ 2 Y) :
    ContDiff ℝ 1 (FaaDiBruno.spatialGradientMatrix Y) := by
  have hD : ContDiff ℝ 1 (fun x => fderiv ℝ Y x) :=
    hY.fderiv_right (m := 1) (by norm_num)
  apply contDiff_pi.2
  intro i
  apply contDiff_pi.2
  intro j
  have hcolumn : ContDiff ℝ 1
      (fun x => fderiv ℝ Y x (FaaDiBruno.coordinateVector 2 j)) :=
    hD.clm_apply contDiff_const
  have hcomponent : ContDiff ℝ 1
      (fun x => fderiv ℝ Y x (FaaDiBruno.coordinateVector 2 j) i) :=
    (contDiff_apply ℝ ℝ i).comp hcolumn
  simpa [FaaDiBruno.spatialGradientMatrix] using hcomponent

/-- The Piola vector built from the inverse-flow cofactor has divergence
equal to the divergence of the original vector field at the inverse point. -/
theorem inverseFlow_cofactor_divergence_transform
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    {g : Vec 2 → Vec 2} (hg : ContDiff ℝ 1 g)
    (t : ℝ) (x : Vec 2) :
    let Y : Vec 2 → Vec 2 := fun z => X 0 z t
    let Q : Vec 2 → FaaDiBruno.FlowMatrix := fun z =>
      FaaDiBruno.flowMatrixCofactorTranspose
        (FaaDiBruno.spatialGradientMatrix Y z)
    vecDiv (fun z => Matrix.mulVec (Q z) (g (Y z))) x = vecDiv g (Y x) := by
  dsimp only
  let Y : Vec 2 → Vec 2 := fun z => X 0 z t
  let Q : Vec 2 → FaaDiBruno.FlowMatrix := fun z =>
    FaaDiBruno.flowMatrixCofactorTranspose
      (FaaDiBruno.spatialGradientMatrix Y z)
  have hY2 : ContDiff ℝ 2 Y :=
    (inverseFlow_contDiff_three hb hX t).of_le (by norm_num)
  have hGrad : ContDiff ℝ 1 (FaaDiBruno.spatialGradientMatrix Y) :=
    TransportPiolaDivergence.spatialGradientMatrix_contDiff_one hY2
  have hQ : ContDiff ℝ 1 Q := by
    change ContDiff ℝ 1
      (FaaDiBruno.flowCofactorCLM ∘ FaaDiBruno.spatialGradientMatrix Y)
    exact FaaDiBruno.flowCofactorCLM.contDiff.comp hGrad
  let LQ : Fin 2 → Fin 2 → Vec 2 →L[ℝ] ℝ := fun i j =>
    fderiv ℝ (fun z => Q z i j) x
  have hQfd : ∀ i j,
      HasFDerivAt (fun z => Q z i j) (LQ i j) x := by
    intro i j
    have hQij : ContDiff ℝ 1 (fun z => Q z i j) :=
      contDiff_pi.1 (contDiff_pi.1 hQ i) j
    exact (hQij.differentiable (by norm_num) x).hasFDerivAt
  have hM : HasFDerivAt Y (fderiv ℝ Y x) x :=
    (hY2.differentiable (by norm_num) x).hasFDerivAt
  have hgAt : HasFDerivAt g (fderiv ℝ g (Y x)) (Y x) :=
    (hg.differentiable (by norm_num) (Y x)).hasFDerivAt
  obtain ⟨hPiolaDiv, hPiolaChain⟩ :=
    inverseFlow_cofactorPiolaData hb hX hdiv t x
  exact AVenhance.Infra.Section5.vecDiv_correctedPiola
    (M := Y) (g := g) (Q := Q) (x := x) (LQ := LQ)
    (LM := fderiv ℝ Y x) (Lg := fderiv ℝ g (Y x))
    hQfd hM hgAt hPiolaDiv hPiolaChain

/-- For a scalar potential, the transported cofactor vector is a Piola
representation of the pulled-back Laplacian. -/
theorem inverseFlow_transportLaplacian
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ 3 f)
    (t : ℝ) (x : Vec 2) :
    let Y : Vec 2 → Vec 2 := fun z => X 0 z t
    let Q : Vec 2 → FaaDiBruno.FlowMatrix := fun z =>
      FaaDiBruno.flowMatrixCofactorTranspose
        (FaaDiBruno.spatialGradientMatrix Y z)
    vecDiv (fun z => Matrix.mulVec (Q z) (spaceGrad f (Y z))) x =
      spaceLap f (Y x) := by
  dsimp only
  have hGrad : ContDiff ℝ 1 (spaceGrad f) := by
    apply contDiff_pi.2
    intro i
    change ContDiff ℝ 1 (fun y => fderiv ℝ f y (basisVec i))
    exact ((hf.fderiv_right (m := 2) (by norm_num)).of_le (by norm_num)).clm_apply
      contDiff_const
  have h := inverseFlow_cofactor_divergence_transform
    hb hX hdiv hGrad t x
  change vecDiv (fun z =>
    Matrix.mulVec (FaaDiBruno.flowMatrixCofactorTranspose
      (FaaDiBruno.spatialGradientMatrix (fun y => X 0 y t) z))
      (spaceGrad f (X 0 z t))) x = _ at h
  simpa [spaceLap, vecDiv, Matrix.mulVec] using h

end AVenhance.Infra.Section5.RelativeError

end
