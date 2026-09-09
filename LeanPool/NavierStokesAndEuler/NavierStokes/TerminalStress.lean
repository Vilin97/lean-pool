/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.LeadingStress
public import LeanPool.NavierStokesAndEuler.NavierStokes.RadialHeatProfile
public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingTail
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricFlatFactor
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-!
# Terminal heat tails and backward stress

All derivatives and integrals are actual analytic operations. The backward
stress is defined independently of the separate global moment condition that
identifies it with an axis-based stress primitive.
-/

noncomputable section

namespace NavierStokes.TerminalStress

open Set Filter MeasureTheory
open SimilarityProfile (partialT partialS partialZ)
open scoped Topology ContDiff

theorem contDiffAt_deriv {f : ℝ → ℝ} {r : ℝ} {m n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f r) (hmn : m + 1 ≤ n) : ContDiffAt ℝ m (deriv f) r :=
  (hf.fderiv_right hmn).clm_apply contDiffAt_const

/-- Radial-viscosity terms left after cancelling the heat equation for `K`. -/
noncomputable def viscousResidual (K f : ℝ → ℝ) (r : ℝ) : ℝ :=
  -K r * (deriv (deriv f) r + deriv f r / r) - 2 * deriv K r * deriv f r

noncomputable def boundary (K f : ℝ → ℝ) (r : ℝ) : ℝ := r ^ 2 * K r * deriv f r

noncomputable def correction (K f : ℝ → ℝ) (r : ℝ) : ℝ :=
  (r * K r - r ^ 2 * deriv K r) * deriv f r

noncomputable def backwardStress (R : ℝ → ℝ) (r : ℝ) : ℝ :=
  (∫ u in Ioi r, u ^ 2 * R u) / r ^ 2

theorem boundary_hasDerivAt {K f : ℝ → ℝ} {r : ℝ} (hr : r ≠ 0)
    (hK : DifferentiableAt ℝ K r) (hf : ContDiffAt ℝ 2 f r) :
    HasDerivAt (boundary K f)
      (correction K f r - r ^ 2 * viscousResidual K f r) r := by
  have hdf := (contDiffAt_deriv hf (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd := (((hasDerivAt_id r).fun_pow 2).fun_mul hK.hasDerivAt).fun_mul hdf.hasDerivAt
  apply hd.congr_deriv
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  unfold correction viscousResidual
  field_simp ; ring

/-- The exact backward integration-by-parts identity. Integrability and the
vanishing boundary at infinity are explicit local-tail hypotheses. -/
theorem integral_viscousResidual {K f : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hK : ∀ u ∈ Ici r, DifferentiableAt ℝ K u)
    (hf : ∀ u ∈ Ici r, ContDiffAt ℝ 2 f u)
    (hv : IntegrableOn (fun u => u ^ 2 * viscousResidual K f u) (Ioi r))
    (hc : IntegrableOn (correction K f) (Ioi r))
    (hboundary : Tendsto (boundary K f) atTop (𝓝 0)) :
    (∫ u in Ioi r, u ^ 2 * viscousResidual K f u) =
      boundary K f r + ∫ u in Ioi r, correction K f u := by
  have hd : ∀ u ∈ Ici r, HasDerivAt (boundary K f)
      (correction K f u - u ^ 2 * viscousResidual K f u) u := by
    intro u hu
    exact boundary_hasDerivAt (ne_of_gt (hr.trans_le hu)) (hK u hu) (hf u hu)
  have he := integral_Ioi_of_hasDerivAt_of_tendsto' hd (hc.sub hv) hboundary
  rw [integral_sub hc hv] at he
  linarith

theorem backwardStress_formula {K f T : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hK : ∀ u ∈ Ici r, DifferentiableAt ℝ K u)
    (hf : ∀ u ∈ Ici r, ContDiffAt ℝ 2 f u)
    (hv : IntegrableOn (fun u => u ^ 2 * viscousResidual K f u) (Ioi r))
    (hc : IntegrableOn (correction K f) (Ioi r))
    (ht : IntegrableOn (fun u => u ^ 2 * T u) (Ioi r))
    (hboundary : Tendsto (boundary K f) atTop (𝓝 0)) :
    backwardStress (fun u => T u + viscousResidual K f u) r =
      K r * deriv f r +
        ((∫ u in Ioi r, u ^ 2 * T u) + ∫ u in Ioi r, correction K f u) / r ^ 2 := by
  unfold backwardStress
  simp_rw [mul_add]
  rw [integral_add ht hv, integral_viscousResidual hr hK hf hv hc hboundary]
  unfold boundary
  field_simp ; ring

theorem correction_nonneg {K f : ℝ → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hK : 0 ≤ K r) (hKr : deriv K r ≤ 0) (hfr : 0 ≤ deriv f r) :
    0 ≤ correction K f r := by
  apply mul_nonneg _ hfr
  exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos (sq_nonneg r) hKr).trans
    (mul_nonneg hr hK))

/-- The backward stress controls the positive radial boundary term. -/
theorem backwardStress_ge_boundary {K f T : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hK : ∀ u ∈ Ici r, DifferentiableAt ℝ K u)
    (hf : ∀ u ∈ Ici r, ContDiffAt ℝ 2 f u)
    (hv : IntegrableOn (fun u => u ^ 2 * viscousResidual K f u) (Ioi r))
    (hc : IntegrableOn (correction K f) (Ioi r))
    (ht : IntegrableOn (fun u => u ^ 2 * T u) (Ioi r))
    (hboundary : Tendsto (boundary K f) atTop (𝓝 0))
    (hKpos : ∀ u ∈ Ioi r, 0 ≤ K u) (hKdec : ∀ u ∈ Ioi r, deriv K u ≤ 0)
    (hfinc : ∀ u ∈ Ioi r, 0 ≤ deriv f u) (hTpos : ∀ u ∈ Ioi r, 0 ≤ T u) :
    K r * deriv f r ≤ backwardStress (fun u => T u + viscousResidual K f u) r := by
  rw [backwardStress_formula hr hK hf hv hc ht hboundary]
  have ht0 : 0 ≤ ∫ u in Ioi r, u ^ 2 * T u :=
    setIntegral_nonneg measurableSet_Ioi (fun u hu => mul_nonneg (sq_nonneg u) (hTpos u hu))
  have hc0 : 0 ≤ ∫ u in Ioi r, correction K f u :=
    setIntegral_nonneg measurableSet_Ioi (fun u hu =>
      correction_nonneg (hr.le.trans hu.le) (hKpos u hu) (hKdec u hu) (hfinc u hu))
  exact le_add_of_nonneg_right (div_nonneg (add_nonneg ht0 hc0) (sq_nonneg r))

/-- A precise version of the time-integral lower comparison. The extra
coefficient comparison is distinct from mere monotonicity of `K`. -/
theorem backwardStress_ge_mass {K f T : ℝ → ℝ} {r c : ℝ} (hr : 0 < r)
    (hK : ∀ u ∈ Ici r, DifferentiableAt ℝ K u)
    (hf : ∀ u ∈ Ici r, ContDiffAt ℝ 2 f u)
    (hv : IntegrableOn (fun u => u ^ 2 * viscousResidual K f u) (Ioi r))
    (hc : IntegrableOn (correction K f) (Ioi r))
    (ht : IntegrableOn (fun u => u ^ 2 * T u) (Ioi r))
    (hboundary : Tendsto (boundary K f) atTop (𝓝 0))
    (hfi : IntegrableOn (deriv f) (Ioi r)) (hflim : Tendsto f atTop (𝓝 1))
    (hKpos : ∀ u ∈ Ici r, 0 ≤ K u) (hKdec : ∀ u ∈ Ioi r, deriv K u ≤ 0)
    (hfinc : ∀ u ∈ Ici r, 0 ≤ deriv f u)
    (hcompare : ∀ u ∈ Ioi r, c * deriv f u ≤ u ^ 2 * T u) :
    (c / r ^ 2) * (1 - f r) ≤
      backwardStress (fun u => T u + viscousResidual K f u) r := by
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun u hu => ((hf u hu).differentiableAt (by norm_num)).hasDerivAt) hfi hflim
  have hcomp : c * (1 - f r) ≤ ∫ u in Ioi r, u ^ 2 * T u := by
    have hi := setIntegral_mono_on (hfi.const_mul c) ht measurableSet_Ioi hcompare
    simpa only [integral_const_mul, hFTC] using hi
  have hc0 : 0 ≤ ∫ u in Ioi r, correction K f u := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro u hu
    have hu' : u ∈ Ici r := by
      change r ≤ u
      exact le_of_lt hu
    exact correction_nonneg (hr.le.trans hu') (hKpos u hu') (hKdec u hu) (hfinc u hu')
  have hrmem : r ∈ Ici r := by simp
  have hb0 : 0 ≤ K r * deriv f r := mul_nonneg (hKpos r hrmem) (hfinc r hrmem)
  rw [backwardStress_formula hr hK hf hv hc ht hboundary]
  have hi := div_le_div_of_nonneg_right (hcomp.trans (le_add_of_nonneg_right hc0)) (sq_nonneg r)
  calc
    _ = c * (1 - f r) / r ^ 2 := by ring
    _ ≤ ((∫ u in Ioi r, u ^ 2 * T u) + ∫ u in Ioi r, correction K f u) / r ^ 2 := hi
    _ ≤ _ := le_add_of_nonneg_left hb0

/-- The heat carrier with the manuscript's arbitrary fixed normalization. -/
noncomputable def heatAmplitude (C a t r : ℝ) : ℝ :=
  C * RadialHeatProfile.radialProfile a (1 - t) r

theorem heatAmplitude_pos {C a t r : ℝ} (hC : 0 < C) (ha : 1 < a)
    (ht : t < 1) (hr : 0 < r) : 0 < heatAmplitude C a t r := by
  have hτ := sub_pos.mpr ht
  unfold heatAmplitude RadialHeatProfile.radialProfile RadialHeatProfile.spatialProfile
  exact mul_pos hC (mul_pos (Real.rpow_pos_of_pos (by positivity) _)
    (RadialHeatProfile.profile_pos ha (by positivity)))

theorem heatAmplitude_deriv_neg {C a t r : ℝ} (hC : 0 < C) (ha : 1 < a)
    (ht : t < 1) (hr : 0 < r) : deriv (heatAmplitude C a t) r < 0 :=
  RadialHeatProfile.scaled_radialProfile_derivative_neg hC ha (sub_pos.mpr ht) hr

theorem heatAmplitude_heat_equation (C : ℝ) {a t r : ℝ} (ha : 1 < a)
    (ht : t < 1) (hr : 0 < r) :
    deriv (fun t => heatAmplitude C a t r) t =
      deriv (deriv (heatAmplitude C a t)) r + deriv (heatAmplitude C a t) r / r -
        heatAmplitude C a t r / r ^ 2 := by
  unfold heatAmplitude
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
    RadialHeatProfile.scaled_forward_radial_heat_equation C ha ht hr

theorem deriv_deriv_mul {f g : ℝ → ℝ} {r : ℝ}
    (hf : ContDiffAt ℝ 2 f r) (hg : ContDiffAt ℝ 2 g r) :
    deriv (deriv (fun u => f u * g u)) r =
      deriv (deriv f) r * g r + 2 * deriv f r * deriv g r + f r * deriv (deriv g) r := by
  have hf' := hf.differentiableAt (by norm_num)
  have hg' := hg.differentiableAt (by norm_num)
  have hdf := (contDiffAt_deriv hf (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdg := (contDiffAt_deriv hg (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he : deriv (fun u => f u * g u) =ᶠ[𝓝 r]
      (fun u => deriv f u * g u + f u * deriv g u) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with u hfu hgu
    exact deriv_fun_mul (hfu.differentiableAt (by norm_num)) (hgu.differentiableAt (by norm_num))
  have hd := (hdf.hasDerivAt.mul hg'.hasDerivAt).add (hf'.hasDerivAt.mul hdg.hasDerivAt)
  exact ((hd.congr_of_eventuallyEq he).deriv).trans (by ring)

theorem heatAmplitude_contDiffAt (C : ℝ) {a t r : ℝ} (ha : 1 < a)
    (ht : t < 1) (hr : 0 < r) : ContDiffAt ℝ ∞ (heatAmplitude C a t) r := by
  have hτ : 0 < 1 - t := sub_pos.mpr ht
  have hn : {p : ℝ × ℝ | 0 < p.1 ∧ 0 ≤ p.2} ∈ 𝓝 (r, 1 - t) := by
    filter_upwards [continuousAt_fst.eventually (Ioi_mem_nhds hr),
      continuousAt_snd.eventually (Ioi_mem_nhds hτ)] with p hp hq
    exact ⟨hp, hq.le⟩
  have hd : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => RadialHeatProfile.radialProfile a p.2 p.1)
      (r, 1 - t) := (RadialHeatProfile.radialProfile_joint_contDiffOn ha).contDiffAt hn
  have he : ContDiffAt ℝ ∞ (fun u => RadialHeatProfile.radialProfile a (1 - t) u) r :=
    hd.comp (f := fun u : ℝ => (u, 1 - t)) r (contDiffAt_id.prodMk contDiffAt_const)
  exact contDiffAt_const.mul he

theorem heatAmplitude_time_differentiable (C : ℝ) {a t r : ℝ} (ha : 1 < a)
    (ht : t < 1) (hr : 0 < r) :
    DifferentiableAt ℝ (fun t => heatAmplitude C a t r) t := by
  have hd := ((RadialHeatProfile.radialProfile_hasDerivAt_time ha (sub_pos.mpr ht) hr).comp t
    ((hasDerivAt_id t).const_sub 1)).const_mul C
  exact hd.differentiableAt

/-- Product expansion of the actual heat equation. No formal jet variables occur. -/
theorem heat_times_factor_residual (C : ℝ) {a t r : ℝ} (ha : 1 < a)
    (ht : t < 1) (hr : 0 < r) {f : ℝ → ℝ → ℝ}
    (hft : DifferentiableAt ℝ (fun t => f t r) t) (hfr : ContDiffAt ℝ 2 (f t) r) :
    deriv (fun u => heatAmplitude C a u r * f u r) t -
      (deriv (deriv (fun u => heatAmplitude C a t u * f t u)) r +
        deriv (fun u => heatAmplitude C a t u * f t u) r / r -
        heatAmplitude C a t r * f t r / r ^ 2) =
      heatAmplitude C a t r * deriv (fun u => f u r) t +
        viscousResidual (heatAmplitude C a t) (f t) r := by
  have hKr : ContDiffAt ℝ 2 (heatAmplitude C a t) r :=
    (heatAmplitude_contDiffAt C ha ht hr).of_le (WithTop.coe_le_coe.mpr le_top)
  rw [deriv_fun_mul (heatAmplitude_time_differentiable C ha ht hr) hft,
    deriv_deriv_mul hKr hfr, deriv_fun_mul (hKr.differentiableAt (by norm_num))
      (hfr.differentiableAt (by norm_num)), heatAmplitude_heat_equation C ha ht hr]
  unfold viscousResidual
  ring

abbrev PhysicalPoint := SimilarityProfile.PhysicalPoint
abbrev PhysicalProfile := SimilarityProfile.PhysicalProfile

noncomputable def radiusPoint (t r z : ℝ) : PhysicalPoint := (t, (r ^ 2 / 2, z))

noncomputable def radialSlice (G : PhysicalProfile) (t z : ℝ) (r : ℝ) : ℝ :=
  G (radiusPoint t r z)

theorem radiusPoint_contDiff (t z : ℝ) : ContDiff ℝ ∞ (fun r => radiusPoint t r z) :=
  contDiff_const.prodMk (((contDiff_id.pow 2).div_const 2).prodMk contDiff_const)

theorem radialSlice_hasDerivAt {G : PhysicalProfile} {t r z : ℝ}
    (hG : DifferentiableAt ℝ G (radiusPoint t r z)) :
    HasDerivAt (radialSlice G t z) (r * partialS G (radiusPoint t r z)) r := by
  have hc := (hasDerivAt_const r t).prodMk
    ((RadialHeatProfile.radiusSquared_hasDerivAt r).prodMk (hasDerivAt_const r z))
  have hd := hG.hasFDerivAt.comp_hasDerivAt r hc
  apply hd.congr_deriv
  rw [show (0, (r, 0)) = r • ((0, (1, 0)) : PhysicalPoint) by ext <;> simp, map_smul]
  rfl

theorem timeSlice_hasDerivAt {G : PhysicalProfile} {p : PhysicalPoint}
    (hG : DifferentiableAt ℝ G p) :
    HasDerivAt (fun t => G (t, p.2)) (partialT G p) p.1 :=
  hG.hasFDerivAt.comp_hasDerivAt p.1 ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))

theorem partialS_contDiffAt {G : PhysicalProfile} {p : PhysicalPoint} {m n : WithTop ℕ∞}
    (hG : ContDiffAt ℝ n G p) (hmn : m + 1 ≤ n) : ContDiffAt ℝ m (partialS G) p :=
  (hG.fderiv_right hmn).clm_apply contDiffAt_const

theorem radialSlice_second {G : PhysicalProfile} {t r z : ℝ}
    (hG : ContDiffAt ℝ 2 G (radiusPoint t r z)) :
    deriv (deriv (radialSlice G t z)) r =
      partialS G (radiusPoint t r z) + r ^ 2 * partialS (partialS G) (radiusPoint t r z) := by
  have he : deriv (radialSlice G t z) =ᶠ[𝓝 r]
      (fun u => u * partialS G (radiusPoint t u z)) := by
    have hn := (radiusPoint_contDiff t z).continuous.continuousAt.eventually
      (hG.eventually (by norm_num))
    filter_upwards [hn] with u hu
    exact (radialSlice_hasDerivAt (hu.differentiableAt (by norm_num))).deriv
  have hg1 := (partialS_contDiffAt hG (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd := (hasDerivAt_id r).mul (radialSlice_hasDerivAt hg1)
  exact ((hd.congr_of_eventuallyEq he).deriv).trans (by simp only [id_eq, one_mul, radialSlice];
    ring)

/-- The actual cylindrical angular radial Laplacian of `r F`. -/
theorem angular_radial_operator {F : PhysicalProfile} {t r z : ℝ} (hr : r ≠ 0)
    (hF : ContDiffAt ℝ 2 F (radiusPoint t r z)) :
    deriv (deriv (fun u => u * radialSlice F t z u)) r +
        deriv (fun u => u * radialSlice F t z u) r / r -
        r * radialSlice F t z r / r ^ 2 =
      r * (2 * (radiusPoint t r z).2.1 * partialS (partialS F) (radiusPoint t r z) +
        4 * partialS F (radiusPoint t r z)) := by
  have hFs : ContDiffAt ℝ 2 (radialSlice F t z) r :=
    hF.comp r ((radiusPoint_contDiff t z).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
  have hd2 := deriv_deriv_mul (f := fun u : ℝ => u) contDiffAt_id hFs
  have hd1 : deriv (fun u => u * radialSlice F t z u) r =
      radialSlice F t z r + r * deriv (radialSlice F t z) r := by
    simpa only [one_mul, id_eq] using
      ((hasDerivAt_id r).fun_mul ((hFs.differentiableAt (by norm_num)).hasDerivAt)).deriv
  rw [hd2, hd1, radialSlice_second hF,
    (radialSlice_hasDerivAt (hF.differentiableAt (by norm_num))).deriv]
  simp only [deriv_id'', deriv_const, zero_mul]
  unfold radiusPoint
  dsimp only
  field_simp [hr] ; ring

/-- The terminal flattening factor is an actual function of logarithmic `X`. -/
noncomputable def flattening (h : ℝ) (f : ℝ → ℝ) (p : PhysicalPoint) : ℝ :=
  f (Real.log (SimilarityProfile.X h p))

theorem flattening_contDiffAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1) {f : ℝ → ℝ}
    (hf : ContDiffAt ℝ 2 f (Real.log (SimilarityProfile.X h p))) :
    ContDiffAt ℝ 2 (flattening h f) p := by
  have hX : ContDiffAt ℝ ∞ (SimilarityProfile.X h) p :=
    (SimilarityProfile.inner_smoothAt hh hh1 ht).fst
  have hXpos : 0 < SimilarityProfile.X h p := div_pos hs (SimilarityProfile.q_pos hh hh1 ht)
  exact hf.comp p ((hX.log hXpos.ne').of_le (WithTop.coe_le_coe.mpr le_top))

theorem flattening_time_hasDerivAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1) {f : ℝ → ℝ}
    (hf : DifferentiableAt ℝ f (Real.log (SimilarityProfile.X h p))) :
    HasDerivAt (fun t => flattening h f (t, p.2))
      (deriv f (Real.log (SimilarityProfile.X h p)) /
        (SimilarityProfile.q h p * CoordinateAlgebra.L h (SimilarityProfile.eta h p))) p.1 := by
  have hXpos : 0 < SimilarityProfile.X h p := div_pos hs (SimilarityProfile.q_pos hh hh1 ht)
  have hd := hf.hasDerivAt.comp p.1
    ((SimilarityProfile.X_hasDerivAt_time hh hh1 ht).log hXpos.ne')
  apply hd.congr_deriv
  unfold CoordinateAlgebra.xTime
  simp only [Prod.eta]
  rw [div_right_comm, div_self hXpos.ne']
  ring

theorem flattening_radial_hasDerivAt {h t r z : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (ht : t < 1) (hr : 0 < r) {f : ℝ → ℝ}
    (hf : DifferentiableAt ℝ f (Real.log (SimilarityProfile.X h (radiusPoint t r z)))) :
    HasDerivAt (radialSlice (flattening h f) t z)
      (2 * deriv f (Real.log (SimilarityProfile.X h (radiusPoint t r z))) / r) r := by
  have hq := SimilarityProfile.q_pos hh hh1 (p := radiusPoint t r z) ht
  have hXpos : 0 < SimilarityProfile.X h (radiusPoint t r z) :=
    div_pos (by dsimp [radiusPoint]; positivity) hq
  have hx : HasDerivAt (fun u => SimilarityProfile.X h (radiusPoint t u z))
      (r / SimilarityProfile.q h (radiusPoint t r z)) r := by
    simpa only [SimilarityProfile.X, SimilarityProfile.q, radiusPoint, Function.comp_def] using
      (RadialHeatProfile.radiusSquared_hasDerivAt r).div_const
        (SimilarityProfile.q h (radiusPoint t r z))
  have hd := hf.hasDerivAt.comp r (hx.log hXpos.ne')
  apply hd.congr_deriv
  have he : r / SimilarityProfile.q h (radiusPoint t r z) /
      SimilarityProfile.X h (radiusPoint t r z) = 2 / r := by
    change r / SimilarityProfile.q h (radiusPoint t r z) /
      (r ^ 2 / 2 / SimilarityProfile.q h (radiusPoint t r z)) = 2 / r
    field_simp [hr.ne', hq.ne']
  rw [he]
  ring

/-- The displayed terminal angular residual, before axial viscosity, is an
identity of actual time and radial derivatives of `K f_o`. -/
theorem terminal_radial_residual (C : ℝ) {h t r z : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (ht : t < 1) (hr : 0 < r) {f : ℝ → ℝ}
    (hf : ContDiffAt ℝ 2 f (Real.log (SimilarityProfile.X h (radiusPoint t r z)))) :
    deriv (fun u => heatAmplitude C (1 + h) u r * flattening h f (radiusPoint u r z)) t -
      (deriv (deriv (fun u => heatAmplitude C (1 + h) t u * radialSlice (flattening h f) t z u)) r +
        deriv (fun u => heatAmplitude C (1 + h) t u * radialSlice (flattening h f) t z u) r / r -
        heatAmplitude C (1 + h) t r * radialSlice (flattening h f) t z r / r ^ 2) =
      heatAmplitude C (1 + h) t r *
        (deriv f (Real.log (SimilarityProfile.X h (radiusPoint t r z))) /
          (SimilarityProfile.q h (radiusPoint t r z) *
            CoordinateAlgebra.L h (SimilarityProfile.eta h (radiusPoint t r z)))) +
        viscousResidual (heatAmplitude C (1 + h) t) (radialSlice (flattening h f) t z) r := by
  have hflat := flattening_contDiffAt hh hh1 (p := radiusPoint t r z) ht
    (by dsimp [radiusPoint]; positivity) hf
  have hft := flattening_time_hasDerivAt hh hh1 (p := radiusPoint t r z) ht
    (by dsimp [radiusPoint]; positivity) (hf.differentiableAt (by norm_num))
  have hfr : ContDiffAt ℝ 2 (radialSlice (flattening h f) t z) r :=
    hflat.comp r ((radiusPoint_contDiff t z).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
  have he := heat_times_factor_residual C (f := fun u v => flattening h f (radiusPoint u v z))
    (by linarith : 1 < 1 + h) ht hr hft.differentiableAt hfr
  have hft' := hft.deriv
  change deriv (fun u => flattening h f (radiusPoint u r z)) t = _ at hft'
  rw [hft'] at he
  exact he

/-- The angular heat carrier expressed in the regular coordinate `s`. -/
noncomputable def physicalHeat (C a : ℝ) (p : PhysicalPoint) : ℝ :=
  C * RadialHeatProfile.spatialProfile a (1 - p.1) p.2.1

/-- The regular Cartesian swirl coefficient: the physical angular velocity is `r F`. -/
noncomputable def swirlCoefficient (C h : ℝ) (f : ℝ → ℝ) (p : PhysicalPoint) : ℝ :=
  physicalHeat C (1 + h) p * flattening h f p / Real.sqrt (2 * p.2.1)

theorem physicalHeat_contDiffAt (C : ℝ) {a : ℝ} (ha : 1 < a) {p : PhysicalPoint}
    (ht : p.1 < 1) (hs : 0 < p.2.1) : ContDiffAt ℝ ∞ (physicalHeat C a) p := by
  have hτ : 0 < 1 - p.1 := sub_pos.mpr ht
  have hn : {y : ℝ × ℝ | 0 < y.1 ∧ 0 ≤ y.2} ∈ 𝓝 (p.2.1, 1 - p.1) := by
    filter_upwards [continuousAt_fst.eventually (Ioi_mem_nhds hs),
      continuousAt_snd.eventually (Ioi_mem_nhds hτ)] with y hy hq
    exact ⟨hy, hq.le⟩
  have hd : ContDiffAt ℝ ∞ (fun y : ℝ × ℝ => RadialHeatProfile.spatialProfile a y.2 y.1)
      (p.2.1, 1 - p.1) := (RadialHeatProfile.spatialProfile_joint_contDiffOn ha).contDiffAt hn
  have he : ContDiffAt ℝ ∞ (fun y : PhysicalPoint =>
      RadialHeatProfile.spatialProfile a (1 - y.1) y.2.1) p :=
    hd.comp (f := fun y : PhysicalPoint => (y.2.1, 1 - y.1)) p
      (contDiffAt_snd.fst.prodMk (contDiffAt_const.sub contDiffAt_fst))
  exact contDiffAt_const.mul he

theorem swirlCoefficient_contDiffAt (C : ℝ) {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1) {f : ℝ → ℝ}
    (hf : ContDiffAt ℝ 2 f (Real.log (SimilarityProfile.X h p))) :
    ContDiffAt ℝ 2 (swirlCoefficient C h f) p := by
  have hK : ContDiffAt ℝ 2 (physicalHeat C (1 + h)) p :=
    (physicalHeat_contDiffAt C (by linarith) ht hs).of_le (WithTop.coe_le_coe.mpr le_top)
  exact (hK.mul (flattening_contDiffAt hh hh1 ht hs hf)).div
    ((contDiffAt_const.mul contDiffAt_snd.fst).sqrt (show 2 * p.2.1 ≠ 0 by positivity))
    (ne_of_gt (Real.sqrt_pos.2 (by positivity)))

theorem swirlCoefficient_amplitude (C h : ℝ) (f : ℝ → ℝ) (t z : ℝ) {r : ℝ} (hr : 0 < r) :
    r * swirlCoefficient C h f (radiusPoint t r z) =
      heatAmplitude C (1 + h) t r * radialSlice (flattening h f) t z r := by
  have hsqrt : Real.sqrt (2 * (r ^ 2 / 2)) = r := by
    rw [show 2 * (r ^ 2 / 2) = r ^ 2 by ring, Real.sqrt_sq hr.le]
  unfold swirlCoefficient physicalHeat radiusPoint heatAmplitude RadialHeatProfile.radialProfile
    radialSlice
  dsimp only
  rw [hsqrt]
  simp only [radiusPoint]
  field_simp

/-- Transfer from regular Cartesian swirl derivatives to the actual radial operator. -/
theorem regular_leading_residual {F : PhysicalProfile} {t r z : ℝ} (hr : r ≠ 0)
    (hF : ContDiffAt ℝ 2 F (radiusPoint t r z)) :
    r * (partialT F (radiusPoint t r z) -
      2 * (radiusPoint t r z).2.1 * partialS (partialS F) (radiusPoint t r z) -
        4 * partialS F (radiusPoint t r z)) =
      deriv (fun u => r * F (radiusPoint u r z)) t -
        (deriv (deriv (fun u => u * radialSlice F t z u)) r +
          deriv (fun u => u * radialSlice F t z u) r / r - r * radialSlice F t z r / r ^ 2) := by
  have htime : deriv (fun u => r * F (radiusPoint u r z)) t =
      r * partialT F (radiusPoint t r z) :=
    ((timeSlice_hasDerivAt (hF.differentiableAt (by norm_num))).const_mul r).deriv
  rw [htime, angular_radial_operator hr hF]
  ring

noncomputable def leadingResidual (C h : ℝ) (f : ℝ → ℝ) (t r z : ℝ) : ℝ :=
  heatAmplitude C (1 + h) t r *
    (deriv f (Real.log (SimilarityProfile.X h (radiusPoint t r z))) /
      (SimilarityProfile.q h (radiusPoint t r z) *
        CoordinateAlgebra.L h (SimilarityProfile.eta h (radiusPoint t r z)))) +
    viscousResidual (heatAmplitude C (1 + h) t) (radialSlice (flattening h f) t z) r

theorem swirlCoefficient_leading_residual (C : ℝ) {h t r z : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (ht : t < 1) (hr : 0 < r) {f : ℝ → ℝ}
    (hf : ContDiffAt ℝ 2 f (Real.log (SimilarityProfile.X h (radiusPoint t r z)))) :
    r * (partialT (swirlCoefficient C h f) (radiusPoint t r z) -
      2 * (radiusPoint t r z).2.1 * partialS (partialS (swirlCoefficient C h f)) (radiusPoint t r
        z) -
        4 * partialS (swirlCoefficient C h f) (radiusPoint t r z)) = leadingResidual C h f t r z :=
          by
  have hF := swirlCoefficient_contDiffAt C hh hh1 (p := radiusPoint t r z) ht
    (by dsimp [radiusPoint]; positivity) hf
  rw [regular_leading_residual hr.ne' hF]
  have he : (fun u => u * radialSlice (swirlCoefficient C h f) t z u) =ᶠ[𝓝 r]
      (fun u => heatAmplitude C (1 + h) t u * radialSlice (flattening h f) t z u) := by
    filter_upwards [Ioi_mem_nhds hr] with u hu
    exact swirlCoefficient_amplitude C h f t z hu
  have htime : (fun u => r * swirlCoefficient C h f (radiusPoint u r z)) =
      (fun u => heatAmplitude C (1 + h) u r * flattening h f (radiusPoint u r z)) := by
    funext u
    exact swirlCoefficient_amplitude C h f u z hr
  have hval : r * radialSlice (swirlCoefficient C h f) t z r =
      heatAmplitude C (1 + h) t r * radialSlice (flattening h f) t z r := he.self_of_nhds
  rw [htime, he.deriv.deriv_eq, he.deriv_eq, hval]
  exact terminal_radial_residual C hh hh1 ht hr hf

/-- Canonical pressure, normalized at infinity, in the regular coordinate. -/
noncomputable def canonicalPressure (F : PhysicalProfile) (p : PhysicalPoint) : ℝ :=
  -∫ s in Ioi p.2.1, F (p.1, (s, p.2.2)) ^ 2

theorem neg_tailIntegral_hasDerivAt {g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hi : IntegrableOn g (Ioi a)) (hc : ContinuousOn g (Ioi a)) :
    HasDerivAt (fun x => -(∫ u in Ioi x, g u)) (g b) b := by
  have hint : IntervalIntegrable g volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 (hi.mono_set (fun _ h => h.1))
  have hd := (intervalIntegral.integral_hasDerivAt_right hint
    (hc.stronglyMeasurableAtFilter isOpen_Ioi b hab) (hc.continuousAt (Ioi_mem_nhds hab))).sub_const
      (∫ u in Ioi a, g u)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hab] with x hx
  have he := MeasureTheory.setIntegral_sdiff (measurableSet_Ioi : MeasurableSet (Ioi x)) hi
    (Ioi_subset_Ioi hx.le)
  rw [Set.Ioi_sdiff_Ioi] at he
  rw [intervalIntegral.integral_of_le hx.le]
  linarith

/-- The radial pressure balance is derived from the defining improper integral.
Joint pressure differentiability is a separate analytic regularity hypothesis. -/
theorem canonicalPressure_partialS {F : PhysicalProfile} {p : PhysicalPoint} {a : ℝ}
    (ha : a < p.2.1)
    (hi : IntegrableOn (fun s => F (p.1, (s, p.2.2)) ^ 2) (Ioi a))
    (hc : ContinuousOn (fun s => F (p.1, (s, p.2.2)) ^ 2) (Ioi a))
    (hp : DifferentiableAt ℝ (canonicalPressure F) p) :
    partialS (canonicalPressure F) p = F p ^ 2 := by
  have hd := neg_tailIntegral_hasDerivAt ha hi hc
  have hp' := hp.hasFDerivAt.comp_hasDerivAt p.2.1
    ((hasDerivAt_const p.2.1 p.1).prodMk
      ((hasDerivAt_id p.2.1).prodMk (hasDerivAt_const p.2.1 p.2.2)))
  exact hp'.unique hd

noncomputable def residualCoefficient (F : PhysicalProfile) (p : PhysicalPoint) : ℝ :=
  partialT F p - 2 * p.2.1 * partialS (partialS F) p - 4 * partialS F p - partialZ (partialZ F) p

/-- The actual Cartesian residual of a purely angular velocity. -/
theorem pureSwirl_navierStokesResidual {F P : PhysicalProfile} {t : ℝ} {x : ProblemStatement.Space}
    (hF : ContDiffAt ℝ 2 F (AxisymmetricFields.profilePoint t x))
    (hP : DifferentiableAt ℝ P (AxisymmetricFields.profilePoint t x)) :
    ProblemStatement.navierStokesResidual
      (AxisymmetricResidual.velocity (fun _ => 0) F (fun _ => 0)) (AxisymmetricResidual.pressure P)
        t x =
      AxisymmetricResidual.pack
        (x 0 * (partialS P (AxisymmetricFields.profilePoint t x) - F
          (AxisymmetricFields.profilePoint t x) ^ 2) -
          x 1 * residualCoefficient F (AxisymmetricFields.profilePoint t x))
        (x 1 * (partialS P (AxisymmetricFields.profilePoint t x) - F
          (AxisymmetricFields.profilePoint t x) ^ 2) +
          x 0 * residualCoefficient F (AxisymmetricFields.profilePoint t x))
        (partialZ P (AxisymmetricFields.profilePoint t x)) := by
  rw [LocalAxisymmetricResidual.navierStokesResidual_velocity contDiffAt_const hF contDiffAt_const
    hP]
  have hS : AxisymmetricFields.partialS = partialS := rfl
  have hZop : AxisymmetricFields.partialZ = partialZ := rfl
  have hT : AxisymmetricResidual.partialT = partialT := rfl
  have h0S : partialS (fun _ => 0) = fun _ => 0 := by funext p; simp [partialS]
  have h0Z : partialZ (fun _ => 0) = fun _ => 0 := by funext p; simp [partialZ]
  have h0T : partialT (fun _ => 0) = fun _ => 0 := by funext p; simp [partialT]
  have hR : AxisymmetricResidual.residualRadial (fun _ => 0) F (fun _ => 0) P
      (AxisymmetricFields.profilePoint t x) =
      partialS P (AxisymmetricFields.profilePoint t x) - F (AxisymmetricFields.profilePoint t x) ^
        2 := by
    simp [AxisymmetricResidual.residualRadial, AxisymmetricResidual.advectionRadial,
      AxisymmetricResidual.laplaceWeighted, hS, hZop, hT, h0S, h0Z, h0T]
    ring
  have hA : AxisymmetricResidual.residualAngular (fun _ => 0) F (fun _ => 0)
      (AxisymmetricFields.profilePoint t x) = -residualCoefficient F
        (AxisymmetricFields.profilePoint t x) := by
    simp only [AxisymmetricResidual.residualAngular, AxisymmetricResidual.advectionAngular,
      AxisymmetricResidual.laplaceWeighted, hS, hZop, hT, residualCoefficient]
    ring
  have hZ : AxisymmetricResidual.residualAxial (fun _ => 0) (fun _ => 0) P
      (AxisymmetricFields.profilePoint t x) = partialZ P (AxisymmetricFields.profilePoint t x) := by
    simp [AxisymmetricResidual.residualAxial, AxisymmetricResidual.advectionAxial,
      AxisymmetricResidual.laplaceScalar, hS, hZop, hT, h0S, h0Z, h0T]
  rw [hR, hA, hZ]
  apply congrArg₂ (fun a b : ℝ => AxisymmetricResidual.pack a b
    (partialZ P (AxisymmetricFields.profilePoint t x)))
  · ring
  · ring

/-- Exact axial viscosity retained in the terminal physical residual. -/
noncomputable def axialViscosity (C h : ℝ) (f : ℝ → ℝ) (p : PhysicalPoint) : ℝ :=
  Real.sqrt (2 * p.2.1) * partialZ (partialZ (swirlCoefficient C h f)) p

noncomputable def terminalVelocity (C h : ℝ) (f : ℝ → ℝ) : ProblemStatement.VelocityField :=
  AxisymmetricResidual.velocity (fun _ => 0) (swirlCoefficient C h f) (fun _ => 0)

noncomputable def terminalPressure (C h : ℝ) (f : ℝ → ℝ) : ProblemStatement.PressureField :=
  AxisymmetricResidual.pressure (canonicalPressure (swirlCoefficient C h f))

theorem radiusPoint_profilePoint {t : ℝ} {x : ProblemStatement.Space}
    (hs : 0 ≤ AxisymmetricFields.radialEnergy x) :
    radiusPoint t (Real.sqrt (2 * AxisymmetricFields.radialEnergy x)) (x 2) =
      AxisymmetricFields.profilePoint t x := by
  unfold radiusPoint AxisymmetricFields.profilePoint
  rw [Real.sq_sqrt (show 0 ≤ 2 * AxisymmetricFields.radialEnergy x by positivity)]
  simp

/-- Full terminal residual, with canonical radial balance and the omitted
axial-viscosity term displayed. The pressure's joint differentiability and
the tail-integral hypotheses are explicit and do not impose a residual identity. -/
theorem terminal_navierStokesResidual (C : ℝ) {h t : ℝ} {x : ProblemStatement.Space}
    (hh : 0 < h) (hh1 : h < 1 / 2) (ht : t < 1)
    (hs : 0 < AxisymmetricFields.radialEnergy x) {f : ℝ → ℝ}
    (hf : ContDiffAt ℝ 2 f
      (Real.log (SimilarityProfile.X h (AxisymmetricFields.profilePoint t x))))
    {a : ℝ} (ha : a < AxisymmetricFields.radialEnergy x)
    (hi : IntegrableOn (fun s => swirlCoefficient C h f (t, (s, x 2)) ^ 2) (Ioi a))
    (hc : ContinuousOn (fun s => swirlCoefficient C h f (t, (s, x 2)) ^ 2) (Ioi a))
    (hP : DifferentiableAt ℝ (canonicalPressure (swirlCoefficient C h f))
      (AxisymmetricFields.profilePoint t x)) :
    ProblemStatement.navierStokesResidual (terminalVelocity C h f) (terminalPressure C h f) t x =
      AxisymmetricResidual.pack
        (-x 1 / Real.sqrt (2 * AxisymmetricFields.radialEnergy x) *
          (leadingResidual C h f t (Real.sqrt (2 * AxisymmetricFields.radialEnergy x)) (x 2) -
            axialViscosity C h f (AxisymmetricFields.profilePoint t x)))
        (x 0 / Real.sqrt (2 * AxisymmetricFields.radialEnergy x) *
          (leadingResidual C h f t (Real.sqrt (2 * AxisymmetricFields.radialEnergy x)) (x 2) -
            axialViscosity C h f (AxisymmetricFields.profilePoint t x)))
        (partialZ (canonicalPressure (swirlCoefficient C h f)) (AxisymmetricFields.profilePoint t
          x)) := by
  have hF : ContDiffAt ℝ 2 (swirlCoefficient C h f) (AxisymmetricFields.profilePoint t x) :=
    swirlCoefficient_contDiffAt C (p := AxisymmetricFields.profilePoint t x) (f := f) hh hh1 ht hs
      hf
  have hpS : partialS (canonicalPressure (swirlCoefficient C h f)) (AxisymmetricFields.profilePoint
    t x) =
      swirlCoefficient C h f (AxisymmetricFields.profilePoint t x) ^ 2 :=
    canonicalPressure_partialS (F := swirlCoefficient C h f) (p := AxisymmetricFields.profilePoint
      t x) ha hi hc hP
  have hr : 0 < Real.sqrt (2 * AxisymmetricFields.radialEnergy x) := Real.sqrt_pos.2 (by positivity)
  have hpoint := radiusPoint_profilePoint (t := t) hs.le
  have hf' : ContDiffAt ℝ 2 f
      (Real.log (SimilarityProfile.X h (radiusPoint t (Real.sqrt (2 *
        AxisymmetricFields.radialEnergy x)) (x 2)))) := by
    rw [hpoint]
    exact hf
  have hlead := swirlCoefficient_leading_residual C (h := h) (t := t)
    (r := Real.sqrt (2 * AxisymmetricFields.radialEnergy x)) (z := x 2) (f := f) hh hh1 ht hr hf'
  rw [hpoint] at hlead
  have hcoef : residualCoefficient (swirlCoefficient C h f) (AxisymmetricFields.profilePoint t x) =
      (leadingResidual C h f t (Real.sqrt (2 * AxisymmetricFields.radialEnergy x)) (x 2) -
        axialViscosity C h f (AxisymmetricFields.profilePoint t x)) /
        Real.sqrt (2 * AxisymmetricFields.radialEnergy x) := by
    apply (eq_div_iff hr.ne').2
    dsimp [residualCoefficient, axialViscosity]
    change _ = _ - Real.sqrt (2 * AxisymmetricFields.radialEnergy x) * _
    linear_combination hlead
  unfold terminalVelocity terminalPressure
  rw [pureSwirl_navierStokesResidual (F := swirlCoefficient C h f)
    (P := canonicalPressure (swirlCoefficient C h f)) hF hP,
    hpS, sub_self, mul_zero, mul_zero, zero_sub, zero_add, hcoef]
  apply congrArg₂ (fun a b : ℝ => AxisymmetricResidual.pack a b
    (partialZ (canonicalPressure (swirlCoefficient C h f)) (AxisymmetricFields.profilePoint t x)))
  · ring
  · ring

/-- A backward stress solves the actual radial divergence equation without
any hypothesis about its integral over the whole radius. -/
theorem backwardStress_divergence {R : ℝ → ℝ} {a r : ℝ} (hr : r ≠ 0) (ha : a < r)
    (hi : IntegrableOn (fun u => u ^ 2 * R u) (Ioi a))
    (hc : ContinuousOn (fun u => u ^ 2 * R u) (Ioi a)) :
    deriv (backwardStress R) r + 2 * backwardStress R r / r = -R r := by
  have hd := (neg_tailIntegral_hasDerivAt ha hi hc).fun_neg
  have hd' : HasDerivAt (fun x => ∫ u in Ioi x, u ^ 2 * R u) (-(r ^ 2 * R r)) r := by
    simpa only [neg_neg] using hd
  have hT := hd'.fun_div ((hasDerivAt_id r).fun_pow 2) (pow_ne_zero 2 hr)
  rw [show deriv (backwardStress R) r = _ from hT.deriv]
  unfold backwardStress
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, id_eq]
  field_simp ; ring

noncomputable def forwardStress (R : ℝ → ℝ) (r : ℝ) : ℝ :=
  -(∫ u in (0 : ℝ)..r, u ^ 2 * R u) / r ^ 2

/-- The missing global matching condition is exactly the zero total weighted
residual. It is not part of the definition of either stress primitive. -/
theorem forward_eq_backward_iff {R : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hi : IntegrableOn (fun u => u ^ 2 * R u) (Ioi 0)) :
    forwardStress R r = backwardStress R r ↔ (∫ u in Ioi (0 : ℝ), u ^ 2 * R u) = 0 := by
  have he := MeasureTheory.setIntegral_sdiff (measurableSet_Ioi : MeasurableSet (Ioi r)) hi
    (Ioi_subset_Ioi hr.le)
  rw [Set.Ioi_sdiff_Ioi] at he
  unfold forwardStress backwardStress
  rw [intervalIntegral.integral_of_le hr.le]
  rw [div_left_inj' (pow_ne_zero 2 hr.ne')]
  constructor <;> intro h <;> linarith

noncomputable def timeDenominator (h t z : ℝ) : ℝ :=
  SimilarityProfile.q h (t, (0, z)) * CoordinateAlgebra.L h (SimilarityProfile.eta h (t, (0, z)))

noncomputable def timeResidual (C h : ℝ) (f : ℝ → ℝ) (t z r : ℝ) : ℝ :=
  heatAmplitude C (1 + h) t r * deriv f (Real.log (SimilarityProfile.X h (radiusPoint t r z))) /
    timeDenominator h t z

theorem timeDenominator_pos {h t z : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (ht : t < 1) :
    0 < timeDenominator h t z :=
  mul_pos (SimilarityProfile.q_pos hh hh1 ht) (SimilarityProfile.L_pos hh hh1 ht)

theorem leadingResidual_eq_time_add (C h : ℝ) (f : ℝ → ℝ) (t r z : ℝ) :
    leadingResidual C h f t r z = timeResidual C h f t z r +
      viscousResidual (heatAmplitude C (1 + h) t) (radialSlice (flattening h f) t z) r := by
  unfold leadingResidual timeResidual timeDenominator radiusPoint
  rw [mul_div_assoc]
  rfl

theorem timeResidual_nonneg {C h t r z : ℝ} (hC : 0 < C) (hh : 0 < h) (hh1 : h < 1 / 2)
    (ht : t < 1) (hr : 0 < r) {f : ℝ → ℝ}
    (hf : 0 ≤ deriv f (Real.log (SimilarityProfile.X h (radiusPoint t r z)))) :
    0 ≤ timeResidual C h f t z r :=
  div_nonneg (mul_nonneg (heatAmplitude_pos hC (by linarith) ht hr).le hf)
    (timeDenominator_pos hh hh1 ht).le

theorem terminal_correction_nonneg {C h t r z : ℝ} (hC : 0 < C) (hh : 0 < h) (hh1 : h < 1 / 2)
    (ht : t < 1) (hr : 0 < r) {f : ℝ → ℝ}
    (hf : DifferentiableAt ℝ f (Real.log (SimilarityProfile.X h (radiusPoint t r z))))
    (hfpos : 0 ≤ deriv f (Real.log (SimilarityProfile.X h (radiusPoint t r z)))) :
    0 ≤ correction (heatAmplitude C (1 + h) t) (radialSlice (flattening h f) t z) r := by
  apply correction_nonneg hr.le (heatAmplitude_pos hC (by linarith) ht hr).le
    (heatAmplitude_deriv_neg hC (by linarith) ht hr).le
  rw [(flattening_radial_hasDerivAt hh hh1 ht hr hf).deriv]
  exact div_nonneg (mul_nonneg (by norm_num) hfpos) hr.le

theorem heatAmplitude_antitoneOn {C a t : ℝ} (hC : 0 < C) (ha : 1 < a) (ht : t < 1) :
    AntitoneOn (heatAmplitude C a t) (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro r hr
    exact (heatAmplitude_contDiffAt C ha ht hr).continuousAt.continuousWithinAt
  · intro r hr
    have hr' : 0 < r := by simpa only [interior_Ioi, Set.mem_Ioi] using hr
    exact ((heatAmplitude_contDiffAt C ha ht hr').differentiableAt (by simp)).differentiableWithinAt
  · intro r hr
    have hr' : 0 < r := by simpa only [interior_Ioi, Set.mem_Ioi] using hr
    exact (heatAmplitude_deriv_neg hC ha ht hr').le

/-- The actual logarithmic time term is a positive weight times `∂r f_o`. -/
theorem weighted_timeResidual {C h t r z : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (ht : t < 1) (hr : 0 < r) {f : ℝ → ℝ}
    (hf : DifferentiableAt ℝ f (Real.log (SimilarityProfile.X h (radiusPoint t r z)))) :
    r ^ 2 * timeResidual C h f t z r =
      (r ^ 3 * heatAmplitude C (1 + h) t r / (2 * timeDenominator h t z)) *
        deriv (radialSlice (flattening h f) t z) r := by
  rw [(flattening_radial_hasDerivAt hh hh1 ht hr hf).deriv]
  unfold timeResidual
  field_simp [hr.ne', (timeDenominator_pos hh hh1 ht).ne']

/-- On a finite remaining radius interval, positivity and decreasing `K`
give a concrete time-weight comparison for the mass lower bound. -/
theorem timeResidual_lower_comparison {C h t r u R z : ℝ}
    (hC : 0 < C) (hh : 0 < h) (hh1 : h < 1 / 2) (ht : t < 1)
    (hr : 0 < r) (hru : r ≤ u) (huR : u ≤ R) {f : ℝ → ℝ}
    (hf : DifferentiableAt ℝ f (Real.log (SimilarityProfile.X h (radiusPoint t u z))))
    (hfpos : 0 ≤ deriv f (Real.log (SimilarityProfile.X h (radiusPoint t u z)))) :
    (r ^ 3 * heatAmplitude C (1 + h) t R / (2 * timeDenominator h t z)) *
        deriv (radialSlice (flattening h f) t z) u ≤ u ^ 2 * timeResidual C h f t z u := by
  have hu : 0 < u := hr.trans_le hru
  have hR : 0 < R := hu.trans_le huR
  rw [weighted_timeResidual hh hh1 ht hu hf]
  have hmono := heatAmplitude_antitoneOn hC (by linarith : 1 < 1 + h) ht hu hR huR
  have hp : r ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ hr.le hru 3
  have hnum := mul_le_mul hp hmono (heatAmplitude_pos hC (by linarith) ht hR).le
    (pow_nonneg hu.le 3)
  apply mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hnum
    (mul_nonneg (by norm_num) (timeDenominator_pos hh hh1 ht).le))
  rw [(flattening_radial_hasDerivAt hh hh1 ht hu hf).deriv]
  exact div_nonneg (mul_nonneg (by norm_num) hfpos) hu.le

noncomputable def terminalStress (C h : ℝ) (f : ℝ → ℝ) (t z r : ℝ) : ℝ :=
  backwardStress (fun u => leadingResidual C h f t u z) r

theorem flattening_radial_contDiffAt {h t r z : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (ht : t < 1) (hr : 0 < r) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiffAt ℝ 2 (radialSlice (flattening h f) t z) r := by
  have hflat := flattening_contDiffAt hh hh1 (p := radiusPoint t r z) ht
    (by dsimp [radiusPoint]; positivity) hf.contDiffAt
  exact hflat.comp r ((radiusPoint_contDiff t z).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))

/-- Backward formula instantiated with the actual heat carrier and actual
logarithmic flattening factor. The integrability and boundary conditions
are ordinary conditions on these functions, not assumed stress identities. -/
theorem terminalStress_formula (C : ℝ) {h t r z : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (ht : t < 1) (hr : 0 < r)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hv : IntegrableOn (fun u => u ^ 2 * viscousResidual (heatAmplitude C (1 + h) t)
      (radialSlice (flattening h f) t z) u) (Ioi r))
    (hc : IntegrableOn (correction (heatAmplitude C (1 + h) t)
      (radialSlice (flattening h f) t z)) (Ioi r))
    (hT : IntegrableOn (fun u => u ^ 2 * timeResidual C h f t z u) (Ioi r))
    (hb : Tendsto (boundary (heatAmplitude C (1 + h) t)
      (radialSlice (flattening h f) t z)) atTop (𝓝 0)) :
    terminalStress C h f t z r =
      heatAmplitude C (1 + h) t r * deriv (radialSlice (flattening h f) t z) r +
        ((∫ u in Ioi r, u ^ 2 * timeResidual C h f t z u) +
          ∫ u in Ioi r, correction (heatAmplitude C (1 + h) t)
            (radialSlice (flattening h f) t z) u) / r ^ 2 := by
  have hK : ∀ u ∈ Ici r, DifferentiableAt ℝ (heatAmplitude C (1 + h) t) u := by
    intro u hu
    exact (heatAmplitude_contDiffAt C (by linarith) ht (hr.trans_le hu)).differentiableAt (by simp)
  have hF : ∀ u ∈ Ici r, ContDiffAt ℝ 2 (radialSlice (flattening h f) t z) u :=
    fun u hu => flattening_radial_contDiffAt hh hh1 ht (hr.trans_le hu) hf
  have he : (fun u => leadingResidual C h f t u z) =
      (fun u => timeResidual C h f t z u + viscousResidual (heatAmplitude C (1 + h) t)
        (radialSlice (flattening h f) t z) u) := by
    funext u
    exact leadingResidual_eq_time_add C h f t u z
  unfold terminalStress
  rw [he]
  exact backwardStress_formula hr hK hF hv hc hT hb

theorem terminalStress_ge_boundary {C h t r z : ℝ}
    (hC : 0 < C) (hh : 0 < h) (hh1 : h < 1 / 2) (ht : t < 1) (hr : 0 < r)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hmono : ∀ y, 0 ≤ deriv f y)
    (hv : IntegrableOn (fun u => u ^ 2 * viscousResidual (heatAmplitude C (1 + h) t)
      (radialSlice (flattening h f) t z) u) (Ioi r))
    (hc : IntegrableOn (correction (heatAmplitude C (1 + h) t)
      (radialSlice (flattening h f) t z)) (Ioi r))
    (hT : IntegrableOn (fun u => u ^ 2 * timeResidual C h f t z u) (Ioi r))
    (hb : Tendsto (boundary (heatAmplitude C (1 + h) t)
      (radialSlice (flattening h f) t z)) atTop (𝓝 0)) :
    heatAmplitude C (1 + h) t r * deriv (radialSlice (flattening h f) t z) r ≤
      terminalStress C h f t z r := by
  rw [terminalStress_formula C hh hh1 ht hr hf hv hc hT hb]
  apply le_add_of_nonneg_right
  apply div_nonneg _ (sq_nonneg r)
  apply add_nonneg
  · apply setIntegral_nonneg measurableSet_Ioi
    intro u hu
    exact mul_nonneg (sq_nonneg u) (timeResidual_nonneg hC hh hh1 ht (hr.trans hu) (hmono _))
  · apply setIntegral_nonneg measurableSet_Ioi
    intro u hu
    exact terminal_correction_nonneg hC hh hh1 ht (hr.trans hu)
      (hf.differentiable (by norm_num) _) (hmono _)

theorem terminalStress_nonneg {C h t r z : ℝ}
    (hC : 0 < C) (hh : 0 < h) (hh1 : h < 1 / 2) (ht : t < 1) (hr : 0 < r)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hmono : ∀ y, 0 ≤ deriv f y)
    (hv : IntegrableOn (fun u => u ^ 2 * viscousResidual (heatAmplitude C (1 + h) t)
      (radialSlice (flattening h f) t z) u) (Ioi r))
    (hc : IntegrableOn (correction (heatAmplitude C (1 + h) t)
      (radialSlice (flattening h f) t z)) (Ioi r))
    (hT : IntegrableOn (fun u => u ^ 2 * timeResidual C h f t z u) (Ioi r))
    (hb : Tendsto (boundary (heatAmplitude C (1 + h) t)
      (radialSlice (flattening h f) t z)) atTop (𝓝 0)) :
    0 ≤ terminalStress C h f t z r := by
  apply le_trans _ (terminalStress_ge_boundary hC hh hh1 ht hr hf hmono hv hc hT hb)
  apply mul_nonneg (heatAmplitude_pos hC (by linarith) ht hr).le
  rw [(flattening_radial_hasDerivAt hh hh1 ht hr (hf.differentiable (by norm_num) _)).deriv]
  exact div_nonneg (mul_nonneg (by norm_num) (hmono _)) hr.le

/-- A plateau at infinity automatically removes the radial boundary term,
irrespective of the behavior of the heat carrier there. -/
theorem deriv_eventually_zero_of_eventually_const {g : ℝ → ℝ} {c : ℝ}
    (hg : g =ᶠ[atTop] fun _ => c) : deriv g =ᶠ[atTop] fun _ => 0 := by
  obtain ⟨R, hR⟩ := eventually_atTop.1 hg
  filter_upwards [eventually_gt_atTop R] with u hu
  have he : g =ᶠ[𝓝 u] fun _ => c := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    exact hR v hv.le
  rw [he.deriv_eq, deriv_const]

theorem boundary_tendsto_zero_of_plateau (K : ℝ → ℝ) {g : ℝ → ℝ} {c : ℝ}
    (hg : g =ᶠ[atTop] fun _ => c) : Tendsto (boundary K g) atTop (𝓝 0) := by
  have hd := deriv_eventually_zero_of_eventually_const hg
  have he : boundary K g =ᶠ[atTop] fun _ => 0 := by
    filter_upwards [hd] with u hu
    simp only [boundary, hu, mul_zero]
  exact tendsto_const_nhds.congr' he.symm

theorem logX_radial_tendsto {h t z : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (ht : t < 1) :
    Tendsto (fun r => Real.log (SimilarityProfile.X h (radiusPoint t r z))) atTop atTop := by
  have hq := SimilarityProfile.q_pos hh hh1 (p := (t, (0, z))) ht
  have hp : Tendsto (fun r : ℝ => r ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hd := Tendsto.atTop_div_const hq
    (Tendsto.atTop_div_const (show (0 : ℝ) < 2 by norm_num) hp)
  simpa only [SimilarityProfile.X, SimilarityProfile.q, radiusPoint, Function.comp_def] using
    Real.tendsto_log_atTop.comp hd

theorem radial_flattening_plateau {h t z c : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (ht : t < 1)
    {f : ℝ → ℝ} (hf : f =ᶠ[atTop] fun _ => c) :
    radialSlice (flattening h f) t z =ᶠ[atTop] fun _ => c :=
  (logX_radial_tendsto (z := z) hh hh1 ht).eventually hf

/-- In particular, the actual outgoing taper gives the zero boundary at infinity. -/
theorem outgoing_boundary_tendsto_zero (d : OutgoingTail.TailData) (C y₀ : ℝ)
    {t z : ℝ} (ht : t < 1) :
    Tendsto (boundary (heatAmplitude C (1 + d.h) t)
      (radialSlice (flattening d.h (fun y => OutgoingTail.tailShape d (y - y₀))) t z)) atTop (𝓝 0)
        := by
  apply boundary_tendsto_zero_of_plateau
  apply radial_flattening_plateau d.h_pos d.h_lt_half ht
  filter_upwards [eventually_ge_atTop (y₀ + 3)] with y hy
  exact OutgoingTail.tailShape_late d (by linarith)

/-! ## The actual terminal taper and its Gaussian edge -/

theorem edge_half (δ : ℝ) : FlatCutoff.edge 1 (δ / 2) = FlatCutoff.edge 4 δ := by
  by_cases hδ : 0 < δ
  · rw [FlatCutoff.edge_of_pos 1 (by positivity), FlatCutoff.edge_of_pos 4 hδ]
    congr 1
    field_simp ; ring
  · rw [FlatCutoff.edge_of_nonpos 1 (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hδ) (by
    norm_num)),
      FlatCutoff.edge_of_nonpos 4 (le_of_not_gt hδ)]

noncomputable def taperDenominator (δ : ℝ) : ℝ :=
  FlatCutoff.edge 1 (1 - δ / 2) + FlatCutoff.edge 4 δ

theorem taperDenominator_pos (δ : ℝ) : 0 < taperDenominator δ := by
  have he : 1 - (1 - δ / 2) = δ / 2 := by ring
  simpa only [he, edge_half, taperDenominator] using
    OutgoingSchedule.sigma_denom_pos (1 - δ / 2)

theorem taperDenominator_contDiff : ContDiff ℝ ∞ taperDenominator :=
  ((FlatCutoff.edge_contDiff (by norm_num : (0 : ℝ) < 1)).comp
    (contDiff_const.sub (contDiff_id.div_const 2))).add
      (FlatCutoff.edge_contDiff (by norm_num : (0 : ℝ) < 4))

noncomputable def taperFactor (δ : ℝ) : ℝ := (taperDenominator δ)⁻¹

theorem taperFactor_contDiff : ContDiff ℝ ∞ taperFactor :=
  taperDenominator_contDiff.inv (fun δ => (taperDenominator_pos δ).ne')

theorem taperFactor_pos (δ : ℝ) : 0 < taperFactor δ := inv_pos.mpr (taperDenominator_pos δ)

/-- The actual outgoing taper has the precise `exp(-4/δ²)` deficit. -/
theorem tailShape_deficit (d : OutgoingTail.TailData) (δ : ℝ) :
    1 - OutgoingTail.tailShape d (3 - δ) = d.rho * FlatCutoff.edge 4 δ * taperFactor δ := by
  have he : ((3 - δ) - 1) / 2 = 1 - δ / 2 := by ring
  have he' : 1 - (1 - δ / 2) = δ / 2 := by ring
  unfold OutgoingTail.tailShape OutgoingSchedule.sigma
  rw [he, he', edge_half]
  change _ = d.rho * FlatCutoff.edge 4 δ * (taperDenominator δ)⁻¹
  change 1 - (1 - d.rho + d.rho *
    (FlatCutoff.edge 1 (1 - δ / 2) / taperDenominator δ)) = _
  field_simp [(taperDenominator_pos δ).ne']
  unfold taperDenominator
  ring_nf

noncomputable def taperSlopeFactor (d : OutgoingTail.TailData) (δ : ℝ) : ℝ :=
  d.rho * (8 * taperFactor δ + δ ^ 3 * deriv taperFactor δ)

theorem taperSlopeFactor_contDiff (d : OutgoingTail.TailData) : ContDiff ℝ ∞ (taperSlopeFactor d) :=
  contDiff_const.mul ((contDiff_const.mul taperFactor_contDiff).add
    ((contDiff_id.pow 3).mul (contDiff_infty_iff_deriv.mp taperFactor_contDiff).2))

theorem taperSlopeFactor_zero_pos (d : OutgoingTail.TailData) : 0 < taperSlopeFactor d 0 := by
  simp only [taperSlopeFactor, zero_pow (by norm_num : 3 ≠ 0), zero_mul, add_zero]
  exact mul_pos d.rho_pos (mul_pos (by norm_num) (taperFactor_pos 0))

/-- The actual taper derivative has a smooth positive limiting coefficient
after division by the edge factor `exp(-4/δ²) δ⁻³`. -/
theorem tailShapeDeriv_factorization (d : OutgoingTail.TailData) (δ : ℝ) :
    OutgoingTail.tailShapeDeriv d (3 - δ) =
      (FlatCutoff.edge 4 δ / δ ^ 3) * taperSlopeFactor d δ := by
  have hL : HasDerivAt (fun u => 1 - OutgoingTail.tailShape d (3 - u))
      (OutgoingTail.tailShapeDeriv d (3 - δ)) δ := by
    simpa only [Function.comp_apply, mul_neg_one, neg_neg] using
      (((OutgoingTail.tailShape_hasDerivAt d (3 - δ)).comp δ
        ((hasDerivAt_id δ).const_sub 3)).const_sub 1)
  have hR := ((FlatPrimitive.edge_hasDerivAt (by norm_num : (0 : ℝ) < 4) δ).mul
    ((taperFactor_contDiff.differentiable (by simp) δ).hasDerivAt)).const_mul d.rho
  have he : (fun u => 1 - OutgoingTail.tailShape d (3 - u)) =
      (fun u => d.rho * (FlatCutoff.edge 4 u * taperFactor u)) := by
    funext u
    rw [tailShape_deficit]
    ring
  rw [he] at hL
  rw [hL.unique hR]
  unfold taperSlopeFactor
  by_cases hδ : δ = 0
  · subst δ
    simp
  · field_simp [hδ]
    ring

section ParametricEdge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The boundary term and actual backward integrals after the edge change of variables. -/
noncomputable def edgeStress (c : ℝ) (b a : E × ℝ → ℝ) (y : E × ℝ) : ℝ :=
  (FlatCutoff.edge c y.2 / y.2 ^ 3) * b y + ParametricFlatFactor.primitive c 3 a y

noncomputable def normalizedEdgeStress (c : ℝ) (b a : E × ℝ → ℝ) (y : E × ℝ) : ℝ :=
  b y + y.2 ^ 3 * ParametricFlatFactor.factor c 3 a y

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Actual integral factorization, including auxiliary parameters. -/
theorem edgeStress_factorization (c : ℝ) (b a : E × ℝ → ℝ) (y : E × ℝ) :
    edgeStress c b a y = (FlatCutoff.edge c y.2 / y.2 ^ 3) * normalizedEdgeStress c b a y := by
  rw [edgeStress, ParametricFlatFactor.primitive_eq_scale_mul_factor]
  unfold FlatPrimitive.scale normalizedEdgeStress
  ring

theorem normalizedEdgeStress_contDiff {c : ℝ} (hc : 0 < c) {b a : E × ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (normalizedEdgeStress c b a) :=
  hb.add ((contDiff_snd.pow 3).mul (ParametricFlatFactor.factor_contDiff hc 3 ha))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem normalizedEdgeStress_zero (c : ℝ) (b a : E × ℝ → ℝ) (p : E) :
    normalizedEdgeStress c b a (p, 0) = b (p, 0) := by simp [normalizedEdgeStress]

theorem normalizedEdgeStress_eventually_pos {c : ℝ} (hc : 0 < c) {b a : E × ℝ → ℝ}
    (hb : ContDiff ℝ ∞ b) (ha : ContDiff ℝ ∞ a) (p : E) (hbp : 0 < b (p, 0)) :
    ∀ᶠ y in 𝓝 (p, 0), 0 < normalizedEdgeStress c b a y := by
  have hp : 0 < normalizedEdgeStress c b a (p, 0) := by
    rw [normalizedEdgeStress_zero]
    exact hbp
  exact (normalizedEdgeStress_contDiff hc hb ha).continuous.continuousAt.eventually (Ioi_mem_nhds
    hp)

end ParametricEdge

end NavierStokes.TerminalStress
