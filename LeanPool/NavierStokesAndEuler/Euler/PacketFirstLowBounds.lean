/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketForwardGeometryLowBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketShortTimePhysicalGrowth
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketTimeData

@[expose] public section

/-! On the short base interval the actual normal and homogeneous
velocity have absolute size at most two. This gives the first packet's
size and sign estimates without any amplification-stage hypotheses. -/

noncomputable section

namespace EulerPacketFirstLowBounds

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerSpatialCutoffs
  EulerTransversePacketProvider EulerVolterraConvolution EulerPacketSourcePropagator
  EulerPacketForwardFactorization EulerPacketGeometryLowBounds

def firstRatio : ℝ := 4*cutoffBound

theorem firstRatio_pos : 0 < firstRatio := by unfold firstRatio; positivity [cutoffBound_pos]

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : Data U) (CM : ℝ) (hCM : 0 ≤ CM) (x : Space)
  (hM : ∀ t : Icc (0 : ℝ) D.T, ‖D.M.field t x‖ ≤ CM)
  (hshort : CM*D.T ≤ 1/2)

include hCM hM hshort in
theorem normal_norm_le_two
    (hzero : ‖D.normal.field ⟨0,le_rfl,D.T_pos.le⟩ x‖=1)
    (t : Icc (0 : ℝ) D.T) : ‖D.normal.field t x‖ ≤ 2 := by
  let f : ℝ → Space := fun r => extendPath D.T D.T_pos.le D.normal.field r x
  let f' : ℝ → Space := fun r => extendPath D.T D.T_pos.le D.normalDerivative r x
  have hd (r : ℝ) (hr : r ∈ Icc (0 : ℝ) D.T) :
      HasDerivWithinAt f (f' r) (Icc (0 : ℝ) D.T) r := D.normal_hasDerivWithinAt r hr x
  have hb (r : ℝ) (hr : r ∈ Icc (0 : ℝ) D.T) : ‖f' r‖ ≤ CM*‖f r‖ := by
    simp only [f,f',extendPath,projIcc_of_mem D.T_pos.le hr,Data.normalDerivative_apply,norm_neg]
    exact (((D.M.field ⟨r,hr⟩ x).adjoint.le_opNorm _).trans
      (by rw [LinearIsometryEquiv.norm_map]; exact mul_le_mul_of_nonneg_right (hM ⟨r,hr⟩)
        (norm_nonneg _)))
  have h := EulerShortTimeLinearGrowth.norm_le_two D.T CM hCM f f' hd hb hshort
    ⟨0,le_rfl,D.T_pos.le⟩ t t.property.1
  simpa only [f,extendPath,projIcc_of_mem D.T_pos.le t.property,
    projIcc_of_mem D.T_pos.le ⟨le_rfl,D.T_pos.le⟩,hzero,mul_one] using h

variable [CompleteSpace U]

include hCM hM hshort in
theorem uncut_norm_le_two (ξ : U)
    (hzero : ‖D.frame.field ⟨0,le_rfl,D.T_pos.le⟩ x ξ‖=1)
    (t : Icc (0 : ℝ) D.T) : ‖uncutVelocity D ξ t x‖ ≤ 2 := by
  let f : ℝ → Space := fun r => uncutVelocity D ξ r x
  let f' : ℝ → Space := fun r => physicalRhs D (projIcc 0 D.T D.T_pos.le r) x (f r)
  have hd (r : ℝ) (hr : r ∈ Icc (0 : ℝ) D.T) :
      HasDerivWithinAt f (f' r) (Icc (0 : ℝ) D.T) r := by
    simpa only [f,f',projIcc_of_mem D.T_pos.le hr,physicalRhs,
      EulerPacketPrimaryFactorization.physicalGenerator_apply] using uncutVelocity_equation D ξ
        ⟨r,hr⟩ x
  have hb (r : ℝ) (hr : r ∈ Icc (0 : ℝ) D.T) : ‖f' r‖ ≤ CM*‖f r‖ := by
    simp only [f',projIcc_of_mem D.T_pos.le hr,physicalRhs_norm]
    exact ((D.M.field ⟨r,hr⟩ x).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hM ⟨r,hr⟩) (norm_nonneg _))
  have h := EulerShortTimeLinearGrowth.norm_le_two D.T CM hCM f f' hd hb hshort
    ⟨0,le_rfl,D.T_pos.le⟩ t t.property.1
  simpa only [f,uncutVelocity_initial,hzero,mul_one] using h

include hCM hM hshort in
theorem primary_size_le (ξ : U)
    (hn : ‖D.normal.field ⟨0,le_rfl,D.T_pos.le⟩ x‖=1)
    (hv : ‖D.frame.field ⟨0,le_rfl,D.T_pos.le⟩ x ξ‖=1)
    (t : Icc (0 : ℝ) D.T) :
    ‖D.normal.field t x‖*‖canonicalVelocity D ξ t x‖ ≤ firstRatio := by
  have hnormal := normal_norm_le_two D CM hCM x hM hshort hn t
  have hvelocity := uncut_norm_le_two D CM hCM x hM hshort ξ hv t
  rw [canonicalVelocity,norm_smul,Real.norm_of_nonneg (innerCutoff_nonneg x)]
  calc
    _ = innerCutoff x*(‖D.normal.field t x‖*‖uncutVelocity D ξ t x‖) := by ring
    _ ≤ cutoffBound*(2*2) := mul_le_mul (cutoff_le x)
      (mul_le_mul hnormal hvelocity (norm_nonneg _) (by norm_num))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) cutoffBound_pos.le
    _ = _ := by unfold firstRatio; ring

theorem primary_flux_nonneg (ξ : U) (t : Icc (0 : ℝ) D.T)
    (hflux : x ∈ tsupport innerCutoff →
      0 ≤ ⟪D.normal.field t x,D.M.field t x (uncutVelocity D ξ t x)⟫_ℝ) :
    0 ≤ ⟪D.normal.field t x,D.M.field t x (canonicalVelocity D ξ t x)⟫_ℝ := by
  rw [canonicalVelocity,map_smul,real_inner_smul_right]
  by_cases hcut : innerCutoff x=0
  · rw [hcut,zero_mul]
  · exact mul_nonneg (innerCutoff_nonneg x)
      (hflux (subset_tsupport _ (Function.mem_support.mpr hcut)))

end EulerPacketFirstLowBounds
