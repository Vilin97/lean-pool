/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

The Zhou fiber shear conjugates the two dual actions. Paper: §3.
-/
import LeanPool.ConnesRigidity.Paper.Section3.DualActionConjugacyCoordinates
import LeanPool.ConnesRigidity.Paper.Section3.DualActionConjugacyQuadratic

/-!
The dual action conjugacy component of the Connes rigidity formalization.
-/

namespace Connes
namespace PaperDualActionConjugacy

open Construction
open Construction.PaperKernel
open PaperDualActions
open PaperDualCoordinates
open PaperFactorIsomorphism
open PaperDualActionConjugacyAlgebra
open PaperDualActionConjugacyCoordinates
open PaperDualActionConjugacyFirst
open PaperDualActionConjugacyQuadratic

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
/--
The `Coordinates` construction used in the Connes rigidity formalization.
-/
abbrev Coordinates := PaperFactorIsomorphism.DualCoordinates

/- The inverse actions agree on the first dual summand. Paper: §3. -/
theorem paperThetaOneTwo_symm_inl (h : H) (u : PaperKernel.AVStar) :
    (paperThetaOneLinearHom h).symm (u, 0) =
      (paperThetaTwoLinearHom h).symm (u, 0) := by
  change (paperThetaOneLinear h).symm (u, 0) =
    thetaTwoLinearMap h⁻¹ (u, 0)
  rw [paperThetaOne_symm_inl]
  change (avStarAction (h⁻¹).1 (h⁻¹).2 u, 0) =
    (avStarAction (h⁻¹).1 (h⁻¹).2 u +
        thetaTwoTermMap (h⁻¹) 0,
      sl3CAction (h⁻¹).1 0)
  simp [thetaTwoTermMap]

/- The first coordinate is unchanged by the shear-conjugacy comparison.
Paper: §3. -/
theorem paperCoordinateActionOneTwo_fst_eq
    (h : H) (z : A →ₗ[k] PaperV) (lam : PaperKernel.C →ₗ[k] k) :
    (paperCoordinateActionOne h (z, lam)).1 =
      (paperCoordinateActionTwo h
        (z, lam + quadraticMap z)).1 := by
  rw [paperCoordinateActionOne_fst, paperCoordinateActionTwo_fst]
  congr 1
  apply LinearMap.ext
  intro u
  simp only [LinearMap.comp_apply, LinearMap.inl_apply,
    LinearMap.coprod_apply]
  change (avDualEquiv.symm z)
      ((paperThetaOneLinearHom h).symm (u, 0)).1 +
      lam ((paperThetaOneLinearHom h).symm (u, 0)).2 =
    (avDualEquiv.symm z)
      ((paperThetaTwoLinearHom h).symm (u, 0)).1 +
      (lam + quadraticMap z)
        ((paperThetaTwoLinearHom h).symm (u, 0)).2
  rw [paperThetaOneTwo_symm_inl]
  have hzero :
      ((paperThetaTwoLinearHom h).symm (u, 0)).2 = 0 := by
    change (thetaTwoLinearMap h⁻¹ (u, 0)).2 = 0
    change sl3CAction (h⁻¹).1 0 = 0
    exact (sl3CAction (h⁻¹).1).map_zero
  rw [hzero]
  simp

/- The first raw coordinate is the transformed coordinate `zAction`. Paper: §3. -/
theorem paperCoordinateActionOne_fst_eq_zAction
    (h : H) (z : A →ₗ[k] PaperV) (lam : PaperKernel.C →ₗ[k] k) :
    (paperCoordinateActionOne h (z, lam)).1 = zAction h z := by
  rw [paperCoordinateActionOne_fst]
  rw [paperThetaOneHom_symm_eq]
  exact first_coordinate_eq_zAction h z lam

/- The first action's second coordinate is its linear transported value.
Paper: §3. -/
theorem paperCoordinateActionOne_snd_linear
    (h : H) (z : A →ₗ[k] PaperV) (lam : PaperKernel.C →ₗ[k] k)
    (c : PaperKernel.C) :
    (paperCoordinateActionOne h (z, lam)).2 c =
      lam (sl3CAction (h⁻¹).1 c) := by
  change (PaperDualCoordinates.dualEquiv.symm (z, lam))
      ((paperThetaOneLinearHom h).symm (0, c)) =
    lam (sl3CAction (h⁻¹).1 c)
  rw [paperThetaOne_symm_inr]
  simp [PaperDualCoordinates.dualEquiv,
    Module.dualProdDualEquivDual]

/- The second action's second coordinate carries the quadratic correction.
Paper: §3. -/
theorem paperCoordinateActionTwo_snd_linear
    (h : H) (z : A →ₗ[k] PaperV) (lam : PaperKernel.C →ₗ[k] k)
    (c : PaperKernel.C) :
    (paperCoordinateActionTwo h (z, lam)).2 c =
      avDualEquiv.symm z (thetaTwoTermMap (h⁻¹) c) +
        lam (sl3CAction (h⁻¹).1 c) := by
  change (PaperDualCoordinates.dualEquiv.symm (z, lam))
      ((paperThetaTwoLinearHom h).symm (0, c)) =
    avDualEquiv.symm z (thetaTwoTermMap (h⁻¹) c) +
      lam (sl3CAction (h⁻¹).1 c)
  rw [paperThetaTwo_symm_inr]
  simp [PaperDualCoordinates.dualEquiv,
    Module.dualProdDualEquivDual]

/- The second coordinate satisfies the shear-conjugacy identity. Paper: §3. -/
theorem paperCoordinateActionOneTwo_snd_eq
    (h : H) (z : A →ₗ[k] PaperV) (lam : PaperKernel.C →ₗ[k] k) :
    (fiberShear (paperCoordinateActionOne h (z, lam))).2 =
      (paperCoordinateActionTwo h (fiberShear (z, lam))).2 := by
  apply LinearMap.ext
  intro c
  change (paperCoordinateActionOne h (z, lam)).2 c +
      quadraticMap ((paperCoordinateActionOne h (z, lam)).1) c =
    (paperCoordinateActionTwo h (z, lam + quadraticMap z)).2 c
  rw [paperCoordinateActionOne_snd_linear,
    paperCoordinateActionTwo_snd_linear]
  rw [paperCoordinateActionOne_fst_eq_zAction]
  rw [quadratic_covariance]
  simp only [LinearMap.add_apply]
  abel

/- The full raw-coordinate conjugacy from Zhou's Proposition 3.2. Paper: §3. -/
theorem paperFiberShear_conjugates_paperActions (h : H)
    (p : Coordinates) :
    fiberShear (paperCoordinateActionOne h p) =
      paperCoordinateActionTwo h (fiberShear p) := by
  rcases p with ⟨z, lam⟩
  apply Prod.ext
  · exact paperCoordinateActionOneTwo_fst_eq h z lam
  · exact paperCoordinateActionOneTwo_snd_eq h z lam

end
end PaperDualActionConjugacy
end Connes
