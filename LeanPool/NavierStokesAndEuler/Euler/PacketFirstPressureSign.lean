/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketShortTimePhysicalGrowth
public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardFactorization
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketTimeData

@[expose] public section

/-! Positivity of the first packet's actual pressure numerator on a short
base interval. The normal and uncut velocity are the constructed source
trajectories; their equations and the parent Riccati equation give the bound. -/

noncomputable section

namespace EulerPacketFirstPressureSign

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransversePacketProvider EulerVolterraConvolution EulerPacketSourcePropagator
  EulerPacketForwardFactorization

def firstSignRate (CM CH : ℝ) : ℝ := 4*(3*CM^2+CH)

private theorem numerator_derivative_bound (CM CH : ℝ) (hCM : 0 ≤ CM) (hCH : 0 ≤ CH)
    (m m₁ v v₁ : Space) (A A₁ : Space →L[ℝ] Space)
    (hm : ‖m‖ ≤ 2) (hm₁ : ‖m₁‖ ≤ 2*CM) (hv : ‖v‖ ≤ 2) (hv₁ : ‖v₁‖ ≤ 2*CM)
    (hA : ‖A‖ ≤ CM) (hA₁ : ‖A₁‖ ≤ CM^2+CH) :
    ‖⟪m,A₁ v+A v₁⟫_ℝ+⟪m₁,A v⟫_ℝ‖ ≤ firstSignRate CM CH := by
  have hav : ‖A v‖ ≤ CM*2 :=
    (A.le_opNorm v).trans (mul_le_mul hA hv (norm_nonneg _) hCM)
  have hav₁ : ‖A₁ v+A v₁‖ ≤ (CM^2+CH)*2+CM*(2*CM) := by
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact (A₁.le_opNorm v).trans
        (mul_le_mul hA₁ hv (norm_nonneg _) (by positivity))
    · exact (A.le_opNorm v₁).trans
        (mul_le_mul hA hv₁ (norm_nonneg _) hCM)
  calc
    _ ≤ ‖⟪m,A₁ v+A v₁⟫_ℝ‖+‖⟪m₁,A v⟫_ℝ‖ := norm_add_le _ _
    _ ≤ ‖m‖*‖A₁ v+A v₁‖+‖m₁‖*‖A v‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ 2*((CM^2+CH)*2+CM*(2*CM))+(2*CM)*(CM*2) :=
      add_le_add (mul_le_mul hm hav₁ (norm_nonneg _) (by norm_num))
        (mul_le_mul hm₁ hav (norm_nonneg _) (by positivity))
    _ = firstSignRate CM CH := by unfold firstSignRate; ring

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (ξ : U) (x : Space)
  (H : Icc (0 : ℝ) D.T → (Space →L[ℝ] Space))
  (CM CH : ℝ) (hCM : 0 ≤ CM) (hCH : 0 ≤ CH)
  (hM : ∀ t : Icc (0 : ℝ) D.T, ‖D.M.field t x‖ ≤ CM)
  (hH : ∀ t : Icc (0 : ℝ) D.T, ‖H t‖ ≤ CH)
  (hRiccati : ∀ t : Icc (0 : ℝ) D.T,
    HasDerivWithinAt (fun s => extendPath D.T D.T_pos.le D.M.field s x)
      (-(D.M.field t x).comp (D.M.field t x)-H t) (Icc (0 : ℝ) D.T) t)
  (hm0 : ‖D.normal.field ⟨0,le_rfl,D.T_pos.le⟩ x‖=1)
  (hv0 : ‖D.frame.field ⟨0,le_rfl,D.T_pos.le⟩ x ξ‖=1)
  (h0 : ⟪D.normal.field ⟨0,le_rfl,D.T_pos.le⟩ x,
    D.M.field ⟨0,le_rfl,D.T_pos.le⟩ x (D.frame.field ⟨0,le_rfl,D.T_pos.le⟩ x ξ)⟫_ℝ=1)
  (hshort : CM*D.T ≤ 1/2)

include hCM hCH hM hH hRiccati hm0 hv0 h0 hshort

theorem uncut_numerator_variation (t : Icc (0 : ℝ) D.T) :
    |⟪D.normal.field t x,D.M.field t x (uncutVelocity D ξ t x)⟫_ℝ-1| ≤
      firstSignRate CM CH*t := by
  let m : ℝ → Space := fun r => extendPath D.T D.T_pos.le D.normal.field r x
  let v : ℝ → Space := fun r => uncutVelocity D ξ r x
  let A : ℝ → (Space →L[ℝ] Space) := fun r => extendPath D.T D.T_pos.le D.M.field r x
  let m₁ : ℝ → Space := fun r => -(A r).adjoint (m r)
  let v₁ : ℝ → Space := fun r => -(A r) (v r)+(2*⟪m r,A r (v r)⟫_ℝ/‖m r‖^2) • m r
  let A₁ : ℝ → (Space →L[ℝ] Space) :=
    fun r => -(A r).comp (A r)-H (projIcc 0 D.T D.T_pos.le r)
  have hdm (r : ℝ) (hr : r ∈ Icc (0 : ℝ) D.T) :
      HasDerivWithinAt m (m₁ r) (Icc (0 : ℝ) D.T) r := by
    simpa only [m,m₁,A,extendPath,projIcc_of_mem D.T_pos.le hr,Data.normalDerivative_apply] using
      D.normal_hasDerivWithinAt r hr x
  have hdv (r : ℝ) (hr : r ∈ Icc (0 : ℝ) D.T) :
      HasDerivWithinAt v (v₁ r) (Icc (0 : ℝ) D.T) r := by
    simpa only [v,v₁,A,m,extendPath,projIcc_of_mem D.T_pos.le hr,
      EulerPacketPrimaryFactorization.physicalGenerator_apply] using
      uncutVelocity_equation D ξ ⟨r,hr⟩ x
  have hdA (r : ℝ) (hr : r ∈ Icc (0 : ℝ) D.T) :
      HasDerivWithinAt A (A₁ r) (Icc (0 : ℝ) D.T) r := by
    simpa only [A,A₁,extendPath,projIcc_of_mem D.T_pos.le hr] using hRiccati ⟨r,hr⟩
  have hAb (r : ℝ) (hr : r ∈ Icc (0 : ℝ) D.T) : ‖A r‖ ≤ CM := by
    simpa only [A,extendPath,projIcc_of_mem D.T_pos.le hr] using hM ⟨r,hr⟩
  have hm₁b (r : ℝ) (hr : r ∈ Icc (0 : ℝ) D.T) : ‖m₁ r‖ ≤ CM*‖m r‖ := by
    change ‖-(A r).adjoint (m r)‖ ≤ _
    rw [norm_neg]
    apply ((A r).adjoint.le_opNorm _).trans
    rw [LinearIsometryEquiv.norm_map]
    exact mul_le_mul_of_nonneg_right (hAb r hr) (norm_nonneg _)
  have hv₁b (r : ℝ) (hr : r ∈ Icc (0 : ℝ) D.T) : ‖v₁ r‖ ≤ CM*‖v r‖ := by
    change ‖-(A r) (v r)+(2*⟪m r,A r (v r)⟫_ℝ/‖m r‖^2) • m r‖ ≤ _
    rw [normal_reflection_norm]
    exact ((A r).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hAb r hr) (norm_nonneg _))
  have hmzero : ‖m 0‖=1 := by
    simpa only [m,extendPath,projIcc_of_mem D.T_pos.le ⟨le_rfl,D.T_pos.le⟩] using hm0
  have hvzero : ‖v 0‖=1 := by
    simpa only [v,uncutVelocity_initial] using hv0
  have hmb (r : ℝ) (hr : r ∈ Icc (0 : ℝ) D.T) : ‖m r‖ ≤ 2 := by
    have hh := EulerShortTimeLinearGrowth.norm_le_two D.T CM hCM m m₁ hdm hm₁b hshort
      ⟨0,le_rfl,D.T_pos.le⟩ ⟨r,hr⟩ hr.1
    simpa only [hmzero,mul_one] using hh
  have hvb (r : ℝ) (hr : r ∈ Icc (0 : ℝ) D.T) : ‖v r‖ ≤ 2 := by
    have hh := EulerShortTimeLinearGrowth.norm_le_two D.T CM hCM v v₁ hdv hv₁b hshort
      ⟨0,le_rfl,D.T_pos.le⟩ ⟨r,hr⟩ hr.1
    simpa only [hvzero,mul_one] using hh
  have hA₁b (r : ℝ) (hr : r ∈ Icc (0 : ℝ) D.T) : ‖A₁ r‖ ≤ CM^2+CH := by
    have haa : ‖(A r).comp (A r)‖ ≤ CM^2 := by
      exact (opNorm_comp_le _ _).trans
        ((mul_le_mul (hAb r hr) (hAb r hr) (norm_nonneg _) hCM).trans_eq (pow_two CM).symm)
    change ‖-(A r).comp (A r)-H (projIcc 0 D.T D.T_pos.le r)‖ ≤ _
    apply (norm_sub_le _ _).trans
    rw [norm_neg,projIcc_of_mem D.T_pos.le hr]
    exact add_le_add haa (hH ⟨r,hr⟩)
  let a : ℝ → ℝ := fun r => ⟪m r,A r (v r)⟫_ℝ
  let a₁ : ℝ → ℝ := fun r => ⟪m r,A₁ r (v r)+A r (v₁ r)⟫_ℝ+⟪m₁ r,A r (v r)⟫_ℝ
  have hda (r : ℝ) (hr : r ∈ Icc (0 : ℝ) D.T) :
      HasDerivWithinAt a (a₁ r) (Icc (0 : ℝ) D.T) r :=
    (hdm r hr).inner ℝ ((hdA r hr).clm_apply (hdv r hr))
  have hab (r : ℝ) (hr : r ∈ Icc (0 : ℝ) D.T) : ‖a₁ r‖ ≤ firstSignRate CM CH := by
    apply numerator_derivative_bound CM CH hCM hCH (m r) (m₁ r) (v r) (v₁ r) (A r) (A₁ r)
      (hmb r hr) _ (hvb r hr) _ (hAb r hr) (hA₁b r hr)
    · exact (hm₁b r hr).trans ((mul_le_mul_of_nonneg_left (hmb r hr) hCM).trans_eq (mul_comm _ _))
    · exact (hv₁b r hr).trans ((mul_le_mul_of_nonneg_left (hvb r hr) hCM).trans_eq (mul_comm _ _))
  have hazero : a 0=1 := by
    simpa only [a,m,A,v,extendPath,projIcc_of_mem D.T_pos.le ⟨le_rfl,D.T_pos.le⟩,
      uncutVelocity_initial] using h0
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (C := firstSignRate CM CH) hda hab (convex_Icc (0 : ℝ) D.T)
      (show (0 : ℝ) ∈ Icc 0 D.T from ⟨le_rfl,D.T_pos.le⟩) t.property
  change ‖a t-a 0‖ ≤ firstSignRate CM CH*‖(t : ℝ)-(0 : ℝ)‖ at hh
  rw [hazero] at hh
  simpa only [Real.norm_eq_abs,sub_zero,abs_of_nonneg t.property.1,
    a,m,A,v,extendPath,projIcc_of_mem D.T_pos.le t.property] using hh

theorem uncut_numerator_pos
    (hsmall : firstSignRate CM CH*D.T ≤ 1/2) (t : Icc (0 : ℝ) D.T) :
    1/2 ≤ ⟪D.normal.field t x,D.M.field t x (uncutVelocity D ξ t x)⟫_ℝ := by
  have h := uncut_numerator_variation D ξ x H CM CH hCM hCH hM hH hRiccati hm0 hv0 h0 hshort t
  have hrate : 0 ≤ firstSignRate CM CH := by unfold firstSignRate; positivity
  have ht := (mul_le_mul_of_nonneg_left t.property.2 hrate).trans hsmall
  linarith [(abs_le.mp h).1]

end EulerPacketFirstPressureSign
