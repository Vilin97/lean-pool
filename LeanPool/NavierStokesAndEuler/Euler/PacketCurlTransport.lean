/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FrameWronskian
public import LeanPool.NavierStokesAndEuler.Euler.CurlMatrixSymmetry
public import LeanPool.NavierStokesAndEuler.Euler.PacketPressureSymmetry

@[expose] public section

/-! Zero initial vorticity remains zero along every genuine finite-stage
particle trajectory. The proof uses the conserved antisymmetric pairing
of the particle frame and its time derivative. -/

noncomputable section

namespace EulerParentPacketFrames.Evolution

open Set InnerProductSpace EulerSmoothLimit EulerMeanBoundary EulerVectorCalculus
  EulerMeanCutoffCurl
  EulerVolterraConvolution EulerPacketCofactor Euler.ComparatorBridge
open scoped ContDiff

variable {A : Parent} (E : Evolution A)

include E in
theorem strain_symmetric_along_label (x : Space)
    (hzero : (A.strain.field A.zeroTime x).IsSymmetric)
    (t : Icc (0 : ℝ) A.T) : (A.strain.field t x).IsSymmetric := by
  let F : ℝ → EndSpace := fun r => A.frame.field (projIcc 0 A.T A.T_pos.le r) x
  let G : ℝ → EndSpace := fun r => A.first.field (projIcc 0 A.T A.T_pos.le r) x
  let H : ℝ → EndSpace := fun r => A.second.field (projIcc 0 A.T A.T_pos.le r) x
  let B : ℝ → EndSpace := fun r => A.curvature.field (projIcc 0 A.T A.T_pos.le r) x
  let S : ℝ → EndSpace := fun r => A.strain.field (projIcc 0 A.T A.T_pos.le r) x
  let J : ℝ → EndSpace := fun r => A.inverse.field (projIcc 0 A.T A.T_pos.le r) x
  have hF (r : ℝ) (hr : r ∈ Icc 0 A.T) :
      HasDerivWithinAt F (G r) (Icc 0 A.T) r := by
    simpa only [F,G,SmoothTimeField.realField,extendPath,
      projIcc_of_mem A.T_pos.le hr] using A.frame_time ⟨r,hr⟩ x
  have hG (r : ℝ) (hr : r ∈ Icc 0 A.T) :
      HasDerivWithinAt G (H r) (Icc 0 A.T) r := by
    simpa only [G,H,SmoothTimeField.realField,extendPath,
      projIcc_of_mem A.T_pos.le hr] using A.first_time ⟨r,hr⟩ x
  have hh := strain_symmetric_of_frame_wronskian F G H B S J A.T A.T_pos hF hG
    (fun r _ v => A.second_equation (projIcc 0 A.T A.T_pos.le r) x v)
    (fun r _ => E.curvature_symmetric (projIcc 0 A.T A.T_pos.le r) x)
    (fun r _ v => A.strain_equation (projIcc 0 A.T A.T_pos.le r) x v)
    (fun r _ v => A.inverse_right (projIcc 0 A.T A.T_pos.le r) x v)
    (by
      intro v w
      simpa only [S,Parent.zeroTime,projIcc_of_mem A.T_pos.le (show (0 : ℝ) ∈ Icc 0 A.T from
        ⟨le_rfl,A.T_pos.le⟩)] using hzero v w) t t.property
  intro v w
  simpa only [S,projIcc_of_mem A.T_pos.le t.property] using hh v w

/-- This statement needs only the actual parent Euler evolution, with no
additional Sobolev regularity or support hypotheses. -/
theorem curl_eq_zero_along_position (a : Space)
    (hzero : vectorCurl (fun x => E.velocity (0,x)) a = 0)
    (t : Icc (0 : ℝ) A.T) :
    vectorCurl (fun x => E.velocity (t,x)) (A.position t a) = 0 := by
  have hscale : A.ell • (A.ell⁻¹ • a) = a := by
    rw [smul_smul,mul_inv_cancel₀ A.ell_pos.ne',one_smul]
  have hinit : (A.strain.field A.zeroTime (A.ell⁻¹ • a)).IsSymmetric := by
    rw [E.strain_eq,hscale,A.position_initial]
    apply (curlMatrix_eq_zero_iff_isSymmetric _).mp
    rw [← vectorCurl_eq_matrix _ a ((E.velocity_smooth A.zeroTime).differentiable (by simp) a)]
    exact hzero
  have hsym := E.strain_symmetric_along_label (A.ell⁻¹ • a) hinit t
  rw [E.strain_eq,hscale] at hsym
  rw [vectorCurl_eq_matrix _ _ ((E.velocity_smooth t).differentiable (by simp) _)]
  exact (curlMatrix_eq_zero_iff_isSymmetric _).mpr hsym

end EulerParentPacketFrames.Evolution
