/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Quadratic covariance on Zhou's symmetric tensor carrier. Paper: §3.
-/
import LeanPool.ConnesRigidity.Paper.Section3.DualActionConjugacyAlgebra

/-!
The dual action conjugacy quadratic component of the Connes rigidity formalization.
-/

namespace Connes
namespace PaperDualActionConjugacyQuadratic

open Construction
open Construction.PaperKernel
open PaperDualActions
open PaperDualCoordinates
open PaperFactorIsomorphism
open PaperDualActionConjugacyAlgebra

noncomputable section

/--
The `k` construction used in the Connes rigidity formalization.
-/
abbrev k := Construction.k
/--
The `H` construction used in the Connes rigidity formalization.
-/
abbrev H := Construction.H
/--
The `A` construction used in the Connes rigidity formalization.
-/
abbrev A := Construction.A
/--
The `PaperV` construction used in the Connes rigidity formalization.
-/
abbrev PaperV := PaperKernel.PaperV

/- Covariance on the square generators. Paper: §3. -/
theorem qTensor_covariance_on_diagonal (h : H)
    (z : A →ₗ[k] PaperV) (a : A) :
    qTensor (zAction h z) (PaperKernel.diagonal a : PaperKernel.TensorAA) =
      avDualEquiv.symm z
          (thetaTwoTermTensor h (PaperKernel.diagonal a : PaperKernel.TensorAA)) +
        qTensor z
          (sl3TensorAction (h⁻¹).1 (PaperKernel.diagonal a : PaperKernel.TensorAA)) := by
  have hqdiag (w : A →ₗ[k] PaperV) (b : A) :
      qTensor w (PaperKernel.diagonal b : PaperKernel.TensorAA) =
        quadraticMap w (PaperKernel.diagonal b) := by
    rfl
  have hsl3 :
      sl3TensorAction (h⁻¹).1
          (PaperKernel.diagonal a : PaperKernel.TensorAA) =
        (PaperKernel.diagonal ((sl3AAction (h⁻¹).1) a) :
          PaperKernel.TensorAA) := by
    rfl
  rw [hqdiag _ a, quadraticMap_diagonal]
  rw [show thetaTwoTermTensor h
        (PaperKernel.diagonal a : PaperKernel.TensorAA) =
      thetaTwoTermMap (h⁻¹) (PaperKernel.diagonal a) by rfl]
  rw [thetaTwoTermMap_apply, avDualEquiv_symm_eval]
  rw [sl3CAction_diagonal, PaperKernel.delta_diagonal]
  rw [hsl3, hqdiag _ _, quadraticMap_diagonal]
  rw [zAction_apply]
  rw [standardQuadraticForm_qVAction]
  simp [OpenAIPort.quadraticDefectLinear, sl3AAction]

/- Covariance on the fixed tensor module, using Zhou's square-span lemma.
Paper: §3. -/
theorem qTensor_covariance (h : H) (z : A →ₗ[k] PaperV)
    (c : PaperKernel.C) :
    qTensor (zAction h z) (c : PaperKernel.TensorAA) =
      avDualEquiv.symm z (thetaTwoTermTensor h (c : PaperKernel.TensorAA)) +
        qTensor z (sl3TensorAction (h⁻¹).1 (c : PaperKernel.TensorAA)) := by
  let F : PaperKernel.TensorAA →ₗ[k] k := qTensor (zAction h z)
  let G : PaperKernel.TensorAA →ₗ[k] k :=
    (avDualEquiv.symm z).comp (thetaTwoTermTensor h) +
      (qTensor z).comp (sl3TensorAction (h⁻¹).1)
  have hFG : ∀ x : PaperKernel.TensorAA, x ∈ squareSpan → F x = G x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        exact qTensor_covariance_on_diagonal h z a
    | zero => simp [F, G]
    | add x y hx hy ihx ihy =>
        simp only [map_add]
        rw [ihx, ihy]
    | smul r x hx ih =>
        simp [F, G, ih]
  have hc := hFG (c : PaperKernel.TensorAA)
    (concreteSquareSpanData.squares_span c)
  simpa [F, G, LinearMap.add_apply, LinearMap.comp_apply] using hc

/- Covariance of the raw quadratic map. Paper: §3. -/
theorem quadratic_covariance (h : H) (z : A →ₗ[k] PaperV)
    (c : PaperKernel.C) :
    quadraticMap (zAction h z) c =
      avDualEquiv.symm z (thetaTwoTermMap (h⁻¹) c) +
        quadraticMap z (sl3CAction (h⁻¹).1 c) := by
  have hcov := qTensor_covariance h z c
  have htheta :
      thetaTwoTermTensor h (c : PaperKernel.TensorAA) =
        thetaTwoTermMap (h⁻¹) c := by
    rfl
  rw [htheta] at hcov
  exact hcov

end
end PaperDualActionConjugacyQuadratic
end Connes
