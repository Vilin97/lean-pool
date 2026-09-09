/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FiniteGradeAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothLimit
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The linear and bilinear packet operators on actual space-time value/derivative jets. -/

@[expose] public section


noncomputable section


namespace EulerPacketPointJets

open EulerSmoothLimit InnerProductSpace EulerFiniteGrades
open scoped ContDiff

/-- Domain: an abbreviation for `ℝ × (Space × ℝ)`. -/
abbrev Domain := ℝ × (Space × ℝ)
/-- Jet: an abbreviation for `E × (Domain →L[ℝ] E)`. -/
abbrev Jet (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E × (Domain →L[ℝ] E)
/-- Vector jet: an abbreviation for `Jet Space`. -/
abbrev VectorJet := Jet Space
/-- Scalar jet: an abbreviation for `Jet ℝ`. -/
abbrev ScalarJet := Jet ℝ

/-- Time direction, given by `(1, (0, 0))`. -/
def timeDirection : Domain := (1, (0, 0))
/-- Angle direction, given by `(0, (0, 1))`. -/
def angleDirection : Domain := (0, (0, 1))

/-- Spatial injection, given by `(0 : Space →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ Space).prod
(0 : Space →L[ℝ] ℝ))`. -/
def spatialInjection : Space →L[ℝ] Domain :=
  (0 : Space →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ Space).prod (0 : Space →L[ℝ] ℝ))

/-- Jet, given by `(f z, fderiv ℝ f z)`. -/
def jet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Domain → E) (z : Domain) : Jet E := (f z, fderiv ℝ f z)

/-- Linear part, bundling `toFun`, `map_add`, `map_smul`. -/
def linearPart (M : Space →L[ℝ] Space) : VectorJet →ₗ[ℝ] Space where
  toFun J := J.2 timeDirection + M J.1
  map_add' J K := by simp [add_add_add_comm]
  map_smul' c J := by simp [smul_add]

/-- Slow pressure, bundling `toFun`, `map_add`, `map_smul`. -/
def slowPressure (FInv : Space →L[ℝ] Space) : ScalarJet →ₗ[ℝ] Space where
  toFun J := FInv.adjoint ((toDual ℝ Space).symm (J.2.comp spatialInjection))
  map_add' J K := by simp [ContinuousLinearMap.add_comp]
  map_smul' c J := by simp [ContinuousLinearMap.smul_comp]

/-- Fast pressure, bundling `toFun`, `map_add`, `map_smul`. -/
def fastPressure (m : Space) : ScalarJet →ₗ[ℝ] Space where
  toFun J := J.2 angleDirection • m
  map_add' J K := by simp [add_smul]
  map_smul' c J := by simp [smul_smul]

/-- Slow advection, bundling `toFun`, `map_add`, `map_smul`, `map_add` and the required
compatibility proofs. -/
def slowAdvection (FInv : Space →L[ℝ] Space) : VectorJet →ₗ[ℝ] VectorJet →ₗ[ℝ] Space where
  toFun J :=
    { toFun := fun K => K.2 (spatialInjection (FInv J.1))
      map_add' K H := by simp
      map_smul' c K := by simp }
  map_add' J K := by
    apply LinearMap.ext
    intro H
    simp
  map_smul' c J := by
    apply LinearMap.ext
    intro K
    simp

/-- Fast advection, bundling `toFun`, `map_add`, `map_smul`, `map_add` and the required
compatibility proofs. -/
def fastAdvection (m : Space) : VectorJet →ₗ[ℝ] VectorJet →ₗ[ℝ] Space where
  toFun J :=
    { toFun := fun K => ⟪m, J.1⟫_ℝ • K.2 angleDirection
      map_add' K H := by simp [smul_add]
      map_smul' c K := by simp [smul_smul, mul_comm] }
  map_add' J K := by
    apply LinearMap.ext
    intro H
    simp [inner_add_right, add_smul]
  map_smul' c J := by
    apply LinearMap.ext
    intro K
    simp [inner_smul_right, smul_smul]

/-- Field sum, given by `evaluate M κ (fun n => u n z)`. -/
def fieldSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℕ) (κ : ℝ) (u : ℕ → Domain → E) (z : Domain) : E :=
  evaluate M κ (fun n => u n z)

/-- Taking the actual first jet commutes with a finite packet sum. -/
theorem jet_fieldSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℕ) (κ : ℝ) (u : ℕ → Domain → E) (z : Domain)
    (hu : ∀ n ≤ M, DifferentiableAt ℝ (u n) z) :
    jet (fieldSum M κ u) z = evaluate M κ (fun n => jet (u n) z) := by
  have hd := HasFDerivAt.fun_sum (u := Finset.range (M+1))
    (fun n hn => ((hu n (by have h := Finset.mem_range.mp hn; omega)).hasFDerivAt).const_smul (κ^n))
  apply Prod.ext
  · change (∑ n ∈ Finset.range (M+1), κ^n • u n z) =
      (AddMonoidHom.fst E (Domain →L[ℝ] E))
        (∑ n ∈ Finset.range (M+1), κ^n • jet (u n) z)
    rw [map_sum]
    rfl
  · change fderiv ℝ (fieldSum M κ u) z = _
    rw [show fderiv ℝ (fieldSum M κ u) z =
      ∑ n ∈ Finset.range (M+1), κ^n • fderiv ℝ (u n) z from hd.fderiv]
    change (∑ n ∈ Finset.range (M+1), κ^n • fderiv ℝ (u n) z) =
      (AddMonoidHom.snd E (Domain →L[ℝ] E))
        (∑ n ∈ Finset.range (M+1), κ^n • jet (u n) z)
    rw [map_sum]
    rfl

/-- This is the literal normalized momentum expression evaluated through its true first derivatives.
-/
def momentumResidual (κ : ℝ) (FInv M : Space →L[ℝ] Space) (m : Space)
    (u : Domain → Space) (p : Domain → ℝ) (z : Domain) : Space :=
  linearPart M (jet u z) + slowPressure FInv (jet p z) + κ⁻¹ • fastPressure m (jet p z) +
    slowAdvection FInv (jet u z) (jet u z) + κ⁻¹ • fastAdvection m (jet u z) (jet u z)

theorem momentumResidual_formula (κ : ℝ) (FInv M : Space →L[ℝ] Space) (m : Space)
    (u : Domain → Space) (p : Domain → ℝ) (z : Domain) :
    momentumResidual κ FInv M m u p z =
      fderiv ℝ u z timeDirection + M (u z) +
      FInv.adjoint ((toDual ℝ Space).symm ((fderiv ℝ p z).comp spatialInjection)) +
      κ⁻¹ • (fderiv ℝ p z angleDirection • m) +
      fderiv ℝ u z (spatialInjection (FInv (u z))) +
      κ⁻¹ • (⟪m, u z⟫_ℝ • fderiv ℝ u z angleDirection) := rfl

end EulerPacketPointJets
