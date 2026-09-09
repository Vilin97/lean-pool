/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketSourceData
import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldChain

/-! The actual parent strain obeys the matrix Riccati equation. Its
inverse derivative is derived from the polynomial cofactor construction
and the genuine frame identity, including the time-interval endpoints. -/

@[expose] public section


noncomputable section

namespace EulerParentPacketFrames

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerPacketCofactor
  EulerVolterraConvolution
open scoped ContDiff BoundedContinuousFunction

namespace Parent

variable (G : Parent)

/-- Inverse derivative as an element of `SmoothTimeField (Icc (0 : ℝ) G.T) Space EndSpace`. -/
def inverseDerivative : SmoothTimeField (Icc (0 : ℝ) G.T) Space EndSpace :=
  (SmoothTimeField.bilinear (compL ℝ Space Space Space) G.inverse
    (SmoothTimeField.bilinear (compL ℝ Space Space Space) G.first G.inverse)).map
      (-ContinuousLinearMap.id ℝ EndSpace)

@[simp] theorem inverseDerivative_apply (t : Icc (0 : ℝ) G.T) (x : Space) :
    G.inverseDerivative.field t x =
      -((G.inverse.field t x).comp ((G.first.field t x).comp (G.inverse.field t x))) := rfl

theorem inverse_time : SmoothTimeField.TimeDerivative G.T G.T_pos.le G.inverse G.inverseDerivative
    := by
  let J := (SmoothTimeField.bilinear cofactorBilinear G.first G.frame).add
    (SmoothTimeField.bilinear cofactorBilinear G.frame G.first)
  have hJ : SmoothTimeField.TimeDerivative G.T G.T_pos.le G.inverse J :=
    G.frame_time.bilinear cofactorBilinear G.frame_time
  apply hJ.congr_fields (fun _ _ => rfl)
  intro t x
  have hd := (hJ t x).clm_comp (G.frame_time t x)
  have he : (fun s => (G.inverse.realField G.T G.T_pos.le s x).comp
      (G.frame.realField G.T G.T_pos.le s x)) = fun _ => ContinuousLinearMap.id ℝ Space := by
    funext s
    apply ContinuousLinearMap.ext
    intro v
    exact G.inverse_left (projIcc 0 G.T G.T_pos.le s) x v
  rw [he] at hd
  simp only [SmoothTimeField.realField_apply] at hd
  have hz : (J.field t x).comp (G.frame.field t x) +
      (G.inverse.field t x).comp (G.first.field t x)=0 :=
    (hd.derivWithin (uniqueDiffOn_Icc G.T_pos t t.property)).symm.trans
      ((hasDerivWithinAt_const (t : ℝ) (Icc (0 : ℝ) G.T)
        (ContinuousLinearMap.id ℝ Space)).derivWithin
          (uniqueDiffOn_Icc G.T_pos t t.property))
  rw [G.inverseDerivative_apply]
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun A : EndSpace => A (G.inverse.field t x v)) hz
  simp only [add_apply,comp_apply,G.inverse_right,zero_apply] at hv
  simpa only [neg_apply,comp_apply] using eq_neg_of_add_eq_zero_left hv

/-- Strain derivative as an element of `SmoothTimeField (Icc (0 : ℝ) G.T) Space EndSpace`. -/
def strainDerivative : SmoothTimeField (Icc (0 : ℝ) G.T) Space EndSpace :=
  ((SmoothTimeField.bilinear (compL ℝ Space Space Space) G.strain G.strain).add G.curvature).map
    (-ContinuousLinearMap.id ℝ EndSpace)

@[simp] theorem strainDerivative_apply (t : Icc (0 : ℝ) G.T) (x : Space) :
    G.strainDerivative.field t x =
      -(G.strain.field t x).comp (G.strain.field t x)-G.curvature.field t x := by
  change -((G.strain.field t x).comp (G.strain.field t x)+G.curvature.field t x)=_
  abel

theorem strain_time : SmoothTimeField.TimeDerivative G.T G.T_pos.le G.strain G.strainDerivative :=
    by
  have h := G.first_time.bilinear (compL ℝ Space Space Space) G.inverse_time
  apply h.congr_fields (fun _ _ => rfl)
  intro t x
  change (G.second.field t x).comp (G.inverse.field t x) +
    (G.first.field t x).comp (G.inverseDerivative.field t x)=G.strainDerivative.field t x
  rw [G.strainDerivative_apply,G.inverseDerivative_apply,G.strain_apply,G.curvature_apply]
  apply ContinuousLinearMap.ext
  intro v
  simp only [add_apply,comp_apply,neg_apply,sub_apply,map_neg]
  abel

/-- The exact clamped-time form used by the source ray/velocity dynamics. -/
theorem strain_within (t : Icc (0 : ℝ) G.T) (x : Space) :
    HasDerivWithinAt (fun s => extendPath G.T G.T_pos.le G.strain.field s x)
      (-(G.strain.field t x).comp (G.strain.field t x)-G.curvature.field t x)
      (Icc (0 : ℝ) G.T) t := by
  simpa only [SmoothTimeField.realField,G.strainDerivative_apply] using G.strain_time t x

theorem strainDerivative_norm_le (t : Icc (0 : ℝ) G.T) (x : Space) :
    ‖G.strainDerivative.field t x‖ ≤ ‖G.strain.field t x‖^2+‖G.curvature.field t x‖ := by
  rw [G.strainDerivative_apply]
  calc
    _ ≤ ‖-(G.strain.field t x).comp (G.strain.field t x)‖+‖G.curvature.field t x‖ :=
      norm_sub_le _ _
    _ ≤ _ := by
      rw [norm_neg,pow_two]
      exact add_le_add (opNorm_comp_le _ _) le_rfl

theorem strainDerivative_norm_bound (CM CH : ℝ) (hCM : 0 ≤ CM)
    (t : Icc (0 : ℝ) G.T) (x : Space)
    (hM : ‖G.strain.field t x‖ ≤ CM) (hH : ‖G.curvature.field t x‖ ≤ CH) :
    ‖G.strainDerivative.field t x‖ ≤ CM^2+CH := by
  apply (G.strainDerivative_norm_le t x).trans
  simpa only [pow_two] using add_le_add (mul_le_mul hM hM (norm_nonneg _) hCM) hH

/-- Center strain, given by `extendPath G.T G.T_pos.le G.strain.field t 0`. -/
def centerStrain (t : ℝ) : EndSpace :=
  extendPath G.T G.T_pos.le G.strain.field t 0

/-- Center curvature, given by `extendPath G.T G.T_pos.le G.curvature.field t 0`. -/
def centerCurvature (t : ℝ) : EndSpace :=
  extendPath G.T G.T_pos.le G.curvature.field t 0

/-- Center strain derivative, given by `extendPath G.T G.T_pos.le G.strainDerivative.field t 0`. -/
def centerStrainDerivative (t : ℝ) : EndSpace :=
  extendPath G.T G.T_pos.le G.strainDerivative.field t 0

theorem centerStrainDerivative_eq (t : ℝ) :
    G.centerStrainDerivative t = -(G.centerStrain t).comp (G.centerStrain t)-G.centerCurvature t :=
  G.strainDerivative_apply (projIcc 0 G.T G.T_pos.le t) 0

theorem centerStrain_derivative (τ : ℝ) (hτ : 0 ≤ τ)
    (t : ℝ) (ht : t ∈ Icc τ G.T) :
    HasDerivWithinAt G.centerStrain (G.centerStrainDerivative t) (Icc τ G.T) t := by
  have ht0 : t ∈ Icc (0 : ℝ) G.T := ⟨hτ.trans ht.1,ht.2⟩
  have hd := G.strain_time ⟨t,ht0⟩ 0
  have hd' := hd.mono (show Icc τ G.T ⊆ Icc (0 : ℝ) G.T from fun _ hs => ⟨hτ.trans hs.1,hs.2⟩)
  unfold centerStrain centerStrainDerivative
  simpa only [SmoothTimeField.realField,extendPath,
    projIcc_of_mem G.T_pos.le ht0] using hd'

/-- The fixed-center derivative bound needed by the next geometric stage
follows from the actual strain/curvature bounds and one scalar guard. -/
theorem centerStrainDerivative_bound (τ CM CH K : ℝ) (hτ : 0 ≤ τ) (hCM : 0 ≤ CM)
    (hM : ∀ t ∈ Icc τ G.T, ‖G.centerStrain t‖ ≤ CM)
    (hH : ∀ t ∈ Icc τ G.T, ‖G.centerCurvature t‖ ≤ CH)
    (hK : CM ^ 2 + CH ≤ K ^ 2) (t : ℝ) (ht : t ∈ Icc τ G.T) :
    ‖G.centerStrainDerivative t‖ ≤ K^2 := by
  have ht0 : t ∈ Icc (0 : ℝ) G.T := ⟨hτ.trans ht.1,ht.2⟩
  have hm := hM t ht
  have hh := hH t ht
  simp only [centerStrain,centerCurvature,extendPath,projIcc_of_mem G.T_pos.le ht0] at hm hh
  have hb := (G.strainDerivative_norm_bound CM CH hCM ⟨t,ht0⟩ 0 hm hh).trans hK
  simpa only [centerStrainDerivative,extendPath,projIcc_of_mem G.T_pos.le ht0] using hb

section Transverse

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] EulerTransverseFrameCoordinates.referencePlane m)
  (S : Set Space) (hS : IsCompact S)

theorem transverse_strain_within (t : Icc (0 : ℝ) G.T) (x : Space) :
    HasDerivWithinAt
      (fun s => extendPath G.T G.T_pos.le (G.transverseData m hm R S hS).M.field s x)
      (-((G.transverseData m hm R S hS).M.field t x).comp
        ((G.transverseData m hm R S hS).M.field t x)-G.curvature.field t x)
      (Icc (0 : ℝ) G.T) t := G.strain_within t x

end Transverse

end Parent
end EulerParentPacketFrames
