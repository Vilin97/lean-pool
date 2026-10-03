/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.RoundPoleLogBasic
public import LeanPool.PoincareGeometry.LichnerowiczObata.RoundSineSeries
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! # Smoothness of the actual round logarithm at the pole -/

@[expose] public noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace LichnerowiczObata

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

theorem roundPoleLog_roundPoleSine {R : ℝ} (hR : 0 < R) {z : P}
    (hz : ‖z‖ < Real.pi * R / 2) :
    roundPoleLog R (roundPoleSine R z) = z := by
  by_cases hzero : z = 0
  · simp [hzero]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hzero
  let u : P := ‖z‖⁻¹ • z
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, hn.ne']
  have he : roundPoleSine R z = (WithLp.fstL 2 ℝ P ℝ)
      (roundPolarCurve R roundNorth (roundAngularInclusion u) ‖z‖) := by
    rw [roundPoleSine_eq, Real.sinc_of_ne_zero (div_ne_zero hn.ne' hR.ne')]
    simp only [roundPolarCurve, roundNorth, roundAngularInclusion_apply,
      map_add, map_smul]
    simp [u, smul_smul, div_eq_mul_inv, mul_comm, mul_assoc]
  rw [he, roundPoleLog_polar_projection hR u hu ⟨hn, hz⟩]
  simp [u, smul_smul, hn.ne']

theorem roundPoleLog_roundPoleSine_eventually {R : ℝ} (hR : 0 < R) :
    (roundPoleLog (P := P) R ∘ roundPoleSine R) =ᶠ[𝓝 0] id := by
  filter_upwards [Metric.ball_mem_nhds (0 : P) (ε := Real.pi * R / 2)
    (div_pos (mul_pos Real.pi_pos hR) (by norm_num))] with z hz
  exact roundPoleLog_roundPoleSine hR (by simpa using hz)

theorem hasFDerivAt_roundPoleSine_zero (R : ℝ) :
    HasFDerivAt (roundPoleSine (P := P) R) (ContinuousLinearMap.id ℝ P) 0 := by
  have hq : ContDiffAt ℝ ∞ (fun z : P => ‖z‖ ^ 2 / R ^ 2) 0 :=
    (contDiff_norm_sq ℝ).contDiffAt.div_const _
  have hs : ContDiffAt ℝ ∞ roundSineSeries (‖(0 : P)‖ ^ 2 / R ^ 2) := by
    simpa using analyticAt_roundSineSeries_zero.contDiffAt
  have hc := ((hs.comp 0 hq).differentiableAt (by norm_num)).hasFDerivAt
  change HasFDerivAt ((roundSineSeries ∘ fun z : P => ‖z‖ ^ 2 / R ^ 2) • (id : P → P))
    (ContinuousLinearMap.id ℝ P) (0 : P)
  simpa using hc.smul (hasFDerivAt_id (0 : P))

theorem contDiffAt_roundPoleLog_zero [CompleteSpace P] {R : ℝ} (hR : 0 < R) :
    ContDiffAt ℝ ∞ (roundPoleLog (P := P) R) 0 := by
  let f := roundPoleSine (P := P) R
  have hf : ContDiffAt ℝ ∞ f 0 := contDiffAt_roundPoleSine_zero R
  have hd : HasFDerivAt f ((ContinuousLinearEquiv.refl ℝ P) : P →L[ℝ] P) 0 :=
    hasFDerivAt_roundPoleSine_zero R
  let e := hf.toOpenPartialHomeomorph f hd (by norm_num)
  have he0 : (0 : P) ∈ e.source := hf.mem_toOpenPartialHomeomorph_source hd (by norm_num)
  have hezero : e 0 = 0 := roundPoleSine_zero R
  have ht0 : (0 : P) ∈ e.target := hezero ▸ e.map_source he0
  have hsymm : e.symm 0 = 0 :=
    (congrArg e.symm hezero.symm).trans (e.left_inv he0)
  have hInv : ContDiffAt ℝ ∞ e.symm 0 := by
    apply e.contDiffAt_symm ht0 (f₀' := ContinuousLinearEquiv.refl ℝ P)
    · rw [hsymm]
      exact hd
    · rw [hsymm]
      exact hf
  have hc : Tendsto e.symm (𝓝 0) (𝓝 0) := by
    simpa only [hsymm] using (e.symm.continuousAt ht0).tendsto
  have hnear := hc.eventually (roundPoleLog_roundPoleSine_eventually (P := P) hR)
  apply hInv.congr_of_eventuallyEq
  filter_upwards [hnear, e.open_target.mem_nhds ht0] with y hy hyt
  change roundPoleLog R (f (e.symm y)) = e.symm y at hy
  have he : f (e.symm y) = y := e.right_inv hyt
  rwa [he] at hy

end LichnerowiczObata
