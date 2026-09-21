/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges.CoeffField
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Definitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHS
import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.Duality
import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.CoarseGrainingL2
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.ForceLocalization
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.TerminalBounds
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.GlobalIteration
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.WeakSolutionBridge
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfaces.AECongruence
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesComponentwise
import LeanPool.CoarseGraining.Homogenization.PDE.EnergyIdentities
import LeanPool.CoarseGraining.Homogenization.PDE.NeumannRHS
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalCubeBridge

/-! # H1Casts -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Public H1 domain casts for Chapter 3

This file contains small domain-cast helpers used to transport public open-cube
H1, H10, and mean-zero H1 data to the deterministic cube realization.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable def castH1Domain {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1Function U) : H1Function V :=
  hUV ▸ u

noncomputable def castH10Domain {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H10Function U) : H10Function V :=
  hUV ▸ u

@[simp] theorem castH1Domain_grad {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1Function U) :
    (castH1Domain hUV u).grad = u.grad := by
  subst V
  rfl

@[simp] theorem castH1Domain_toFun {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1Function U) :
    (castH1Domain hUV u).toFun = u.toFun := by
  subst V
  rfl

@[simp] theorem castH10Domain_toH1Function_grad
    {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H10Function U) :
    (castH10Domain hUV u).toH1Function.grad = u.toH1Function.grad := by
  subst V
  rfl

@[simp] theorem castH10Domain_toH1Function_toFun
    {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H10Function U) :
    (castH10Domain hUV u).toH1Function.toFun = u.toH1Function.toFun := by
  subst V
  rfl

noncomputable def castH1MeanZeroDomain {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1MeanZeroFunction U) : H1MeanZeroFunction V :=
  hUV ▸ u

@[simp] theorem castH1MeanZeroDomain_toH1Function_grad
    {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1MeanZeroFunction U) :
    (castH1MeanZeroDomain hUV u).toH1Function.grad =
      u.toH1Function.grad := by
  subst V
  rfl

@[simp] theorem castH1MeanZeroDomain_toH1Function_toFun
    {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1MeanZeroFunction U) :
    (castH1MeanZeroDomain hUV u).toH1Function.toFun =
      u.toH1Function.toFun := by
  subst V
  rfl


end

end Ch03
end Book
end Homogenization
