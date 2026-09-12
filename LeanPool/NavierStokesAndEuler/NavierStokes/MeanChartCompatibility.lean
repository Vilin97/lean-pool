/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionState
public import LeanPool.NavierStokesAndEuler.NavierStokes.CommonCoverSolve
public import LeanPool.NavierStokesAndEuler.NavierStokes.SimilarityHomogeneity
import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalGraphBounds

/-!
# Naturality of the actual mean operators

Radial endpoints, the normalized density, the compactification cutoff,
frequencies, and amplitudes are transported together.  The identities below
are identities of the defined integral/Fourier/rank operators, not an
assumption that separately chosen chart outputs coincide.
-/

@[expose] public section


namespace NavierStokes.MeanChartCompatibility

noncomputable section

open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators Interval

section RadialScale

theorem cutoff_scale {l : ℝ} (hl : l ≠ 0) (a b x : ℝ) :
    TransportPrimitive.cutoff (l * a) (l * b) (l * x) = TransportPrimitive.cutoff a b x := by
  unfold TransportPrimitive.cutoff
  congr 1
  rw [← mul_sub, ← mul_sub, mul_div_mul_left _ _ hl]

theorem interiorCutoff_scale {l : ℝ} (hl : l ≠ 0) (a b x : ℝ) :
    TransportPrimitive.interiorCutoff (l * a) (l * b) (l * x) =
      TransportPrimitive.interiorCutoff a b x := by
  unfold TransportPrimitive.interiorCutoff
  rw [show (2 * (l * a) + l * b) / 3 = l * ((2 * a + b) / 3) by ring,
    show (l * a + 2 * (l * b)) / 3 = l * ((a + 2 * b) / 3) by ring]
  exact cutoff_scale hl _ _ _

theorem interiorCutoff_power_scale {l a b x : ℝ} (hl : 0 < l)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) (d : ℝ) :
    TransportPrimitive.interiorCutoff ((l * a) ^ d) ((l * b) ^ d) ((l * x) ^ d) =
      TransportPrimitive.interiorCutoff (a ^ d) (b ^ d) (x ^ d) := by
  rw [Real.mul_rpow hl.le ha, Real.mul_rpow hl.le hb, Real.mul_rpow hl.le hx]
  exact interiorCutoff_scale (Real.rpow_pos_of_pos hl d).ne' _ _ _

theorem meanBump_scale {l a b : ℝ} (hl : 0 < l) (hab : a < b) (x : ℝ) :
    PressureStream.meanBump (l * a) (l * b) (mul_lt_mul_of_pos_left hab hl) (l * x) =
      PressureStream.meanBump a b hab x := by
  rw [ContDiffBump.apply, ContDiffBump.apply]
  dsimp only [PressureStream.meanBump]
  rw [show l * b - l * a = l * (b - a) by ring,
    show (l * a + l * b) / 2 = l * ((a + b) / 2) by ring]
  have hba : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  congr 1
  · field_simp [hl.ne', hba]
  · simp only [smul_eq_mul]
    rw [← mul_sub]
    field_simp [hl.ne', hba]

theorem meanBump_integral_scale {l a b : ℝ} (hl : 0 < l) (hab : a < b) :
    (∫ x, PressureStream.meanBump (l * a) (l * b) (mul_lt_mul_of_pos_left hab hl) x) =
      l * ∫ x, PressureStream.meanBump a b hab x := by
  have he (x : ℝ) :
      PressureStream.meanBump (l * a) (l * b) (mul_lt_mul_of_pos_left hab hl) x =
        PressureStream.meanBump a b hab (x / l) := by
    simpa only [mul_div_cancel₀ _ hl.ne'] using meanBump_scale hl hab (x / l)
  simp_rw [he]
  simpa using MeanRankUpdate.integral_scaled hl 1 (PressureStream.meanBump a b hab)

/-- The density transforms with the inverse radial length. -/
theorem rho_scale {l a b : ℝ} (hl : 0 < l) (hab : a < b) (x : ℝ) :
    PressureStream.rho (l * a) (l * b) (mul_lt_mul_of_pos_left hab hl) (l * x) =
      l⁻¹ * PressureStream.rho a b hab x := by
  unfold PressureStream.rho
  rw [ContDiffBump.normed_def, ContDiffBump.normed_def, meanBump_scale hl hab,
    meanBump_integral_scale hl hab]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end RadialScale

section Pullback

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Chart linear, given by `(l • ContinuousLinearMap.id ℝ ℝ).prodMap C`. -/
noncomputable def chartLinear (l : ℝ) (C : E →L[ℝ] F) : ℝ × E →L[ℝ] ℝ × F :=
  (l • ContinuousLinearMap.id ℝ ℝ).prodMap C

@[simp] theorem chartLinear_apply (l : ℝ) (C : E →L[ℝ] F) (z : ℝ × E) :
    chartLinear l C z = (l * z.1, C z.2) := rfl

/-- Pull, given by `u * f (chartLinear l C z)`. -/
noncomputable def pull (l : ℝ) (C : E →L[ℝ] F) (u : ℝ) (f : ℝ × F → ℝ) (z : ℝ × E) : ℝ :=
  u * f (chartLinear l C z)

theorem pull_smooth (l : ℝ) (C : E →L[ℝ] F) (u : ℝ) {f : ℝ × F → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (pull l C u f) :=
  contDiff_const.mul (hf.comp (chartLinear l C).contDiff)

theorem pull_supported {l a b : ℝ} (hl : 0 < l) (C : E →L[ℝ] F) (u : ℝ)
    {f : ℝ × F → ℝ} (hs : RadialAlias.RadiallySupported (l * a) (l * b) f) :
    RadialAlias.RadiallySupported a b (pull l C u f) := by
  intro z hz
  have hne : f (chartLinear l C z) ≠ 0 := by
    intro he
    apply hz
    change u * f (chartLinear l C z) = 0
    rw [he, mul_zero]
  have hp := hs hne
  change l * a ≤ l * z.1 ∧ l * z.1 ≤ l * b at hp
  exact ⟨(mul_le_mul_iff_right₀ hl).mp hp.1, (mul_le_mul_iff_right₀ hl).mp hp.2⟩

theorem shifted_chart {l : ℝ} (hl : 0 < l) (C : E →L[ℝ] F)
    (d M N : ℝ) (v : E) (w : F)
    (hshift : M • C v = (N * l ^ d) • w)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (Y : E) :
    C (Y + (M * (s ^ d - r ^ d)) • v) =
      C Y + (N * ((l * s) ^ d - (l * r) ^ d)) • w := by
  rw [map_add, map_smul]
  calc
    _ = C Y + (s ^ d - r ^ d) • (M • C v) := by
      rw [smul_smul]
      congr 2
      ring
    _ = _ := by
      rw [hshift, smul_smul, Real.mul_rpow hl.le hs, Real.mul_rpow hl.le hr]
      congr 2
      ring

theorem shifted_integral_scale {l a t r : ℝ} (hl : 0 < l) (ha : 0 ≤ a)
    (hat : a ≤ t) (hr : 0 ≤ r) (C : E →L[ℝ] F)
    (d M N u : ℝ) (v : E) (w : F) (f : ℝ × F → ℝ) (Y : E)
    (hshift : M • C v = (N * l ^ d) • w) :
    (∫ s in a..t, pull l C u f (s, Y + (M * (s ^ d - r ^ d)) • v)) =
      (u / l) * ∫ x in (l * a)..(l * t),
        f (x, C Y + (N * (x ^ d - (l * r) ^ d)) • w) := by
  have he : (∫ s in a..t, pull l C u f (s, Y + (M * (s ^ d - r ^ d)) • v)) =
      ∫ s in a..t, u * f (l * s, C Y + (N * ((l * s) ^ d - (l * r) ^ d)) • w) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hsa : a ≤ s := (show s ∈ Icc a t by simpa only [uIcc_of_le hat] using hs).1
    simp only [pull, chartLinear_apply]
    rw [shifted_chart hl C d M N v w hshift hr (ha.trans hsa) Y]
  rw [he, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left
      (fun x => f (x, C Y + (N * (x ^ d - (l * r) ^ d)) • w)) hl.ne']
  simp only [smul_eq_mul, div_eq_mul_inv, mul_assoc]

/-- Scaling of the actual compact radial integral, with transformed
endpoints and the exact transformed transport direction. -/
theorem physicalCompact_pull {l a b d : ℝ} (hl : 0 < l) (ha : 0 < a)
    (hab : a < b) (hd : 0 < d) (C : E →L[ℝ] F) (M N u : ℝ) (v : E) (w : F)
    (hshift : M • C v = (N * l ^ d) • w) {f : ℝ × F → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported (l * a) (l * b) f)
    (z : ℝ × E) :
    RadialPullback.physicalCompact d a b M v (pull l C u f) z =
      (u / l) * RadialPullback.physicalCompact d (l * a) (l * b) N w f (chartLinear l C z) := by
  have hp := pull_smooth l C u hf
  have hsp := pull_supported hl C u hs
  have hla : 0 < l * a := mul_pos hl ha
  have hlab : l * a < l * b := mul_lt_mul_of_pos_left hab hl
  by_cases hz : a ≤ z.1
  · rw [RadialPullback.physicalCompact_eq_radialIntegral ha hab hd hp hsp M v z hz,
      RadialPullback.physicalCompact_eq_radialIntegral hla hlab hd hf hs N w
        (chartLinear l C z) (mul_le_mul_of_nonneg_left hz hl.le)]
    simp only [chartLinear_apply]
    rw [shifted_integral_scale hl ha.le hz (ha.le.trans hz) C d M N u v w f z.2 hshift,
      shifted_integral_scale hl ha.le hab.le (ha.le.trans hz) C d M N u v w f z.2 hshift,
      interiorCutoff_power_scale hl ha.le (ha.le.trans hab.le) (ha.le.trans hz) d]
    simp only [smul_eq_mul]
    ring
  · have hz' : z.1 < a := lt_of_not_ge hz
    have hleft : RadialPullback.physicalCompact d a b M v (pull l C u f) z = 0 := by
      by_contra hn
      exact hz (RadialPullback.physicalCompact_supported ha hab hd hp hsp M v hn).1
    have hright : RadialPullback.physicalCompact d (l * a) (l * b) N w f (chartLinear l C z) = 0 :=
        by
      by_contra hn
      have ht := (RadialPullback.physicalCompact_supported hla hlab hd hf hs N w hn).1
      exact (not_le_of_gt (mul_lt_mul_of_pos_left hz' hl)) ht
    rw [hleft, hright, mul_zero]

theorem weightedSource_pull {l : ℝ} (hl : l ≠ 0) (C : E →L[ℝ] F)
    (u : ℝ) (f : ℝ × F → ℝ) :
    PressureStream.weightedSource (pull l C u f) =
      pull l C (u / l) (PressureStream.weightedSource f) := by
  funext z
  change z.1 * (u * f (chartLinear l C z)) =
    (u / l) * ((l * z.1) * f (chartLinear l C z))
  field_simp

/-- The stream potential has one less velocity length factor. -/
theorem streamPotential_pull {l a b d : ℝ} (hl : 0 < l) (ha : 0 < a)
    (hab : a < b) (hd : 0 < d) (C : E →L[ℝ] F) (M N u : ℝ) (v : E) (w : F)
    (hshift : M • C v = (N * l ^ d) • w) {f : ℝ × F → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported (l * a) (l * b) f) :
    PressureStream.streamPotential d a b M v (pull l C u f) =
      pull l C (u / l) (PressureStream.streamPotential d (l * a) (l * b) N w f) := by
  funext z
  change RadialPullback.physicalCompact d a b M v
      (PressureStream.weightedSource (pull l C u f)) z / z.1 = _
  rw [weightedSource_pull hl.ne', physicalCompact_pull hl ha hab hd C M N (u / l) v w hshift
    (PressureStream.weightedSource_contDiff hf) (PressureStream.weightedSource_supported hs)]
  change (u / l / l * RadialPullback.physicalCompact d (l * a) (l * b) N w
    (PressureStream.weightedSource f) (chartLinear l C z)) / z.1 =
      (u / l) * (RadialPullback.physicalCompact d (l * a) (l * b) N w
        (PressureStream.weightedSource f) (chartLinear l C z) / (l * z.1))
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem fderiv_pull_apply (l : ℝ) (C : E →L[ℝ] F) (u : ℝ) {f : ℝ × F → ℝ}
    {z : ℝ × E} (hf : DifferentiableAt ℝ f (chartLinear l C z)) (v : ℝ × E) :
    fderiv ℝ (pull l C u f) z v = u * fderiv ℝ f (chartLinear l C z) (chartLinear l C v) := by
  have hd := (hf.hasFDerivAt.comp z (chartLinear l C).hasFDerivAt).const_mul u
  simp only [Function.comp_def] at hd
  rw [show pull l C u f = fun x => u * f (chartLinear l C x) from rfl, hd.fderiv]
  rfl

theorem divideRadius_pull {l : ℝ} (hl : l ≠ 0) (C : E →L[ℝ] F)
    (u : ℝ) (f : ℝ × F → ℝ) (z : ℝ × E) :
    PressureStream.divideRadius (pull l C u f) z =
      (u * l) * PressureStream.divideRadius f (chartLinear l C z) := by
  change (u * f (chartLinear l C z)) / z.1 =
    (u * l) * (f (chartLinear l C z) / (l * z.1))
  by_cases hz : z.1 = 0
  · simp [hz]
  · field_simp

theorem graphDr_pull (l : ℝ) (C : E →L[ℝ] F) (u : ℝ)
    (knew kold : ℝ → ℝ) (v : E) (w : F) {f : ℝ × F → ℝ} {z : ℝ × E}
    (hf : DifferentiableAt ℝ f (chartLinear l C z))
    (hvector : C (knew z.1 • v) = l • (kold (l * z.1) • w)) :
    PressureStream.graphDr knew v (pull l C u f) z =
      (u * l) * PressureStream.graphDr kold w f (chartLinear l C z) := by
  rw [PressureStream.graphDr, fderiv_pull_apply l C u hf]
  have he : chartLinear l C (PressureStream.radialVector knew v z) =
      l • PressureStream.radialVector kold w (chartLinear l C z) := by
    apply Prod.ext
    · simp [chartLinear_apply, PressureStream.radialVector]
    · exact hvector
  rw [he, map_smul]
  simp only [smul_eq_mul, PressureStream.graphDr]
  ring

theorem graphDz_pull (l : ℝ) (C : E →L[ℝ] F) (u k : ℝ) (v : E) (w : F)
    {f : ℝ × F → ℝ} {z : ℝ × E}
    (hf : DifferentiableAt ℝ f (chartLinear l C z)) (hvector : C v = k • w) :
    PressureStream.graphDz v (pull l C u f) z =
      (u * k) * PressureStream.graphDz w f (chartLinear l C z) := by
  rw [PressureStream.graphDz, fderiv_pull_apply l C u hf]
  have he : chartLinear l C (0, v) = k • ((0 : ℝ), w) := by
    apply Prod.ext
    · simp
    · exact hvector
  rw [he, map_smul]
  simp only [smul_eq_mul, PressureStream.graphDz]
  ring

theorem physicalSpeed_vector {l R : ℝ} (hl : 0 < l) (hR : 0 ≤ R)
    (C : E →L[ℝ] F) (d M N : ℝ) (v : E) (w : F)
    (hshift : M • C v = (N * l ^ d) • w) :
    C (PressureStream.physicalSpeed d M R • v) =
      l • (PressureStream.physicalSpeed d N (l * R) • w) := by
  have hpow : l * l ^ (d - 1) = l ^ d := by
    conv_lhs => lhs; rw [← Real.rpow_one l]
    rw [← Real.rpow_add hl]
    congr 1
    ring
  calc
    _ = (d * R ^ (d - 1)) • (M • C v) := by
      simp only [PressureStream.physicalSpeed, RadialPullback.radialJacobian, map_smul, smul_smul]
    _ = (d * R ^ (d - 1)) • ((N * l ^ d) • w) := by rw [hshift]
    _ = _ := by
      simp only [PressureStream.physicalSpeed, RadialPullback.radialJacobian, smul_smul,
        Real.mul_rpow hl.le hR]
      congr 1
      rw [show l * (d * (l ^ (d - 1) * R ^ (d - 1)) * N) =
        d * R ^ (d - 1) * N * (l * l ^ (d - 1)) by ring, hpow]
      ring

theorem streamGamma_pull {l : ℝ} (hl : l ≠ 0) (C : E →L[ℝ] F) (u : ℝ)
    (knew kold : ℝ → ℝ) (v : E) (w : F) {f : ℝ × F → ℝ} {z : ℝ × E}
    (hf : DifferentiableAt ℝ f (chartLinear l C z))
    (hvector : C (knew z.1 • v) = l • (kold (l * z.1) • w)) :
    PressureStream.streamGamma knew v (pull l C u f) z =
      (u * l) * PressureStream.streamGamma kold w f (chartLinear l C z) := by
  rw [PressureStream.streamGamma, graphDr_pull l C u knew kold v w hf hvector,
    divideRadius_pull hl]
  simp only [PressureStream.streamGamma]
  ring

theorem streamBeta_pull (l : ℝ) (C : E →L[ℝ] F) (u k : ℝ) (v : E) (w : F)
    {f : ℝ × F → ℝ} {z : ℝ × E}
    (hf : DifferentiableAt ℝ f (chartLinear l C z)) (hvector : C v = k • w) :
    PressureStream.streamBeta v (pull l C u f) z =
      (u * k) * PressureStream.streamBeta w f (chartLinear l C z) := by
  rw [PressureStream.streamBeta, graphDz_pull l C u k v w hf hvector]
  simp only [PressureStream.streamBeta]
  ring

end Pullback

section TorusPullback

open TorusInverse

variable {S T : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup T] [NormedSpace ℝ T]

/-- Parameter pull, given by `pull l (P.prodMap (ContinuousLinearMap.id ℝ Plane)) u f`. -/
noncomputable def parameterPull (l : ℝ) (P : S →L[ℝ] T) (u : ℝ)
    (f : PressureStream.Lift T → ℝ) : PressureStream.Lift S → ℝ :=
  pull l (P.prodMap (ContinuousLinearMap.id ℝ Plane)) u f

/-- Cover pull, given by `pull l (P.prodMap (TemporalMeanUpdate.coverMap k)) u f`. -/
noncomputable def coverPull (l : ℝ) (P : S →L[ℝ] T) (k : ℕ) (u : ℝ)
    (f : PressureStream.Lift T → ℝ) : PressureStream.Lift S → ℝ :=
  pull l (P.prodMap (TemporalMeanUpdate.coverMap k)) u f

theorem coverPull_eq (l : ℝ) (P : S →L[ℝ] T) (k : ℕ) (u : ℝ)
    (f : PressureStream.Lift T → ℝ) :
    coverPull l P k u f = TemporalMeanUpdate.pullbackCover k (parameterPull l P u f) := rfl

theorem parameterPull_smooth (l : ℝ) (P : S →L[ℝ] T) (u : ℝ)
    {f : PressureStream.Lift T → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (parameterPull l P u f) := pull_smooth _ _ _ hf

theorem parameterPull_periodic (l : ℝ) (P : S →L[ℝ] T) (u : ℝ)
    {f : PressureStream.Lift T → ℝ} (hp : PressureStream.TorusPeriodicLift f) :
    PressureStream.TorusPeriodicLift (parameterPull l P u f) := by
  intro r s Y k
  change u * f (l * r, (P s, Y + ((k.1 : ℝ), (k.2 : ℝ)))) = u * f (l * r, (P s, Y))
  exact congrArg (fun q : ℝ => u * q) (hp (l * r) (P s) Y k)

theorem coverPull_smooth (l : ℝ) (P : S →L[ℝ] T) (k : ℕ) (u : ℝ)
    {f : PressureStream.Lift T → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (coverPull l P k u f) := pull_smooth _ _ _ hf

theorem coverPull_periodic (l : ℝ) (P : S →L[ℝ] T) (k : ℕ) (u : ℝ)
    {f : PressureStream.Lift T → ℝ} (hp : PressureStream.TorusPeriodicLift f) :
    PressureStream.TorusPeriodicLift (coverPull l P k u f) :=
  TemporalMeanUpdate.pullbackCover_periodic k (parameterPull_periodic l P u hp)

theorem torusAverage_parameterPull (l : ℝ) (P : S →L[ℝ] T) (u : ℝ)
    (f : PressureStream.Lift T → ℝ) (p : ℝ × S) :
    PressureStream.torusAverage (parameterPull l P u f) p =
      u * PressureStream.torusAverage f (l * p.1, P p.2) := by
  change (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, u * f (l * p.1, (P p.2, (x, y)))) =
    u * (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (l * p.1, (P p.2, (x, y))))
  simp only [intervalIntegral.integral_const_mul]

theorem torusAverage_coverPull (l : ℝ) (P : S →L[ℝ] T) (k : ℕ) (u : ℝ)
    {f : PressureStream.Lift T → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f) (p : ℝ × S) :
    PressureStream.torusAverage (coverPull l P k u f) p =
      u * PressureStream.torusAverage f (l * p.1, P p.2) := by
  rw [coverPull_eq, TemporalMeanUpdate.torusAverage_pullbackCover k
    (parameterPull_smooth l P u hf) (parameterPull_periodic l P u hp), torusAverage_parameterPull]

theorem pressureMass_coverPull {l : ℝ} (hl : 0 < l) (P : S →L[ℝ] T) (k : ℕ) (u : ℝ)
    {f : PressureStream.Lift T → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f) (s : S) :
    PressureStream.pressureMass (coverPull l P k u f) s =
      (u / l) * PressureStream.pressureMass f (P s) := by
  unfold PressureStream.pressureMass
  simp_rw [torusAverage_coverPull l P k u hf hp]
  rw [integral_const_mul, Measure.integral_comp_mul_left
    (fun r => PressureStream.torusAverage f (r, P s)) l,
    abs_of_pos (inv_pos.mpr hl)]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_assoc]

theorem pressureSource_coverPull {l a b : ℝ} (hl : 0 < l) (hab : a < b)
    (P : S →L[ℝ] T) (k : ℕ) (u : ℝ) {f : PressureStream.Lift T → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f) :
    PressureStream.pressureSource a b hab (coverPull l P k u f) =
      coverPull l P k u (PressureStream.pressureSource (l * a) (l * b)
        (mul_lt_mul_of_pos_left hab hl) f) := by
  funext z
  change u * f (l * z.1, (P z.2.1, TemporalMeanUpdate.coverMap k z.2.2)) -
      PressureStream.rho a b hab z.1 * PressureStream.pressureMass (coverPull l P k u f) z.2.1 =
    u * (f (l * z.1, (P z.2.1, TemporalMeanUpdate.coverMap k z.2.2)) -
      PressureStream.rho (l * a) (l * b) (mul_lt_mul_of_pos_left hab hl) (l * z.1) *
        PressureStream.pressureMass f (P z.2.1))
  rw [pressureMass_coverPull hl P k u hf hp, rho_scale hl hab]
  simp only [div_eq_mul_inv]
  ring

theorem centered_coverPull (l : ℝ) (P : S →L[ℝ] T) (k : ℕ) (u : ℝ)
    {f : PressureStream.Lift T → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f) :
    TemporalMeanUpdate.centered (coverPull l P k u f) =
      coverPull l P k u (TemporalMeanUpdate.centered f) := by
  funext z
  change u * f (l * z.1, (P z.2.1, TemporalMeanUpdate.coverMap k z.2.2)) -
      PressureStream.torusAverage (coverPull l P k u f) (z.1, z.2.1) =
    u * (f (l * z.1, (P z.2.1, TemporalMeanUpdate.coverMap k z.2.2)) -
      PressureStream.torusAverage f (l * z.1, P z.2.1))
  rw [torusAverage_coverPull l P k u hf hp]
  ring

/-- Naturality of the actual pressure formula, including its normalized
mass correction and compactification, on a common covering. -/
theorem meanPressure_coverPull {l a b d : ℝ} (hl : 0 < l) (ha : 0 < a)
    (hab : a < b) (hd : 0 < d) (P : S →L[ℝ] T) (k : ℕ) (M N u : ℝ)
    (v w : Plane) (hshift : M • TemporalMeanUpdate.coverMap k v = (N * l ^ d) • w)
    {f : PressureStream.Lift T → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f)
    (hs : RadialAlias.RadiallySupported (l * a) (l * b) f) (z : PressureStream.Lift S) :
    PressureStream.meanPressure d a b M hab v (coverPull l P k u f) z =
      coverPull l P k (u / l)
        (PressureStream.meanPressure d (l * a) (l * b) N (mul_lt_mul_of_pos_left hab hl) w f) z :=
            by
  have hvector : M • (P.prodMap (TemporalMeanUpdate.coverMap k)) ((0 : S), v) =
      (N * l ^ d) • ((0 : T), w) := by
    apply Prod.ext
    · simp
    · exact hshift
  unfold PressureStream.meanPressure
  rw [pressureSource_coverPull hl hab P k u hf hp]
  exact physicalCompact_pull hl ha hab hd _ M N u _ _ hvector
    (PressureStream.pressureSource_contDiff (mul_lt_mul_of_pos_left hab hl) hf hs)
    (PressureStream.pressureSource_supported (mul_lt_mul_of_pos_left hab hl) hs) z

theorem absoluteInverse_const_mul (c : ℂ) (f : Plane → ℂ) (Y : Plane) :
    TemporalMeanUpdate.absoluteInverse (fun z => c * f z) Y =
      c * TemporalMeanUpdate.absoluteInverse f Y := by
  unfold TemporalMeanUpdate.absoluteInverse TorusInverse.directionalInverse TorusInverse.series
  simp only [TorusInverse.inverseCoeff, TemporalMeanUpdate.coefficient_const_mul]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  ring

theorem temporalInverse_parameterPull (l : ℝ) (P : S →L[ℝ] T) (u : ℝ)
    (f : PressureStream.Lift T → ℝ) (z : PressureStream.Lift S) :
    TemporalMeanUpdate.temporalInverse (parameterPull l P u f) z =
      parameterPull l P u (TemporalMeanUpdate.temporalInverse f) z := by
  change (TemporalMeanUpdate.absoluteInverse
    (fun Y => Complex.ofReal (u * f (l * z.1, (P z.2.1, Y)))) z.2.2).re =
      u * (TemporalMeanUpdate.absoluteInverse
        (fun Y => (f (l * z.1, (P z.2.1, Y)) : ℂ)) z.2.2).re
  simp_rw [Complex.ofReal_mul]
  rw [absoluteInverse_const_mul]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem temporalInverse_coverPull (l : ℝ) (P : S →L[ℝ] T) (k : ℕ) (u : ℝ)
    {f : PressureStream.Lift T → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f)
    (hm : ∀ p, PressureStream.torusAverage f p = 0) (z : PressureStream.Lift S) :
    TemporalMeanUpdate.temporalInverse (coverPull l P k u f) z =
      (ChartScales.Tg ^ k)⁻¹ * coverPull l P k u (TemporalMeanUpdate.temporalInverse f) z := by
  have hmean : ∀ p, PressureStream.torusAverage (parameterPull l P u f) p = 0 := by
    intro p
    rw [torusAverage_parameterPull, hm, mul_zero]
  have he := TemporalMeanUpdate.temporalInverse_coverMap
    (parameterPull_smooth l P u hf) (parameterPull_periodic l P u hp) hmean k z
  rw [temporalInverse_parameterPull] at he
  exact he

theorem temporalInverse_centered_coverPull (l : ℝ) (P : S →L[ℝ] T) (k : ℕ) (u : ℝ)
    {f : PressureStream.Lift T → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f) (z : PressureStream.Lift S) :
    TemporalMeanUpdate.temporalInverse (TemporalMeanUpdate.centered (coverPull l P k u f)) z =
      (ChartScales.Tg ^ k)⁻¹ * coverPull l P k u
        (TemporalMeanUpdate.temporalInverse (TemporalMeanUpdate.centered f)) z := by
  rw [centered_coverPull l P k u hf hp]
  exact temporalInverse_coverPull l P k u (TemporalMeanUpdate.centered_smooth hf)
    (TemporalMeanUpdate.centered_periodic hp) (TemporalMeanUpdate.centered_zeroMean hf) z

/-- The physical temporal update is one fixed Fourier operator. The native
cover factor and the momentum/velocity unit factors cancel exactly. -/
theorem temporal_physical_pull (h : ℝ) (n : ℕ) (l : ℝ) (P : S →L[ℝ] T)
    {f : PressureStream.Lift T → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f) (z : PressureStream.Lift S) :
    coverPull l P (ChartScales.nativeIndex h n)
      (ChartScales.Q n ^ (-CoordinateAlgebra.A h)) (TemporalMeanUpdate.desiredIncrement h n f) z =
      -TemporalMeanUpdate.temporalInverse (TemporalMeanUpdate.centered
        (coverPull l P (ChartScales.nativeIndex h n)
          (ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h + 1 / 2))) f)) z := by
  rw [temporalInverse_centered_coverPull l P _ _ hf hp]
  change ChartScales.Q n ^ (-CoordinateAlgebra.A h) *
      (-TemporalMeanUpdate.chartPrefactor h n *
        TemporalMeanUpdate.temporalInverse (TemporalMeanUpdate.centered f)
          (l * z.1, (P z.2.1, TemporalMeanUpdate.coverMap (ChartScales.nativeIndex h n) z.2.2))) =
    -((ChartScales.Tg ^ ChartScales.nativeIndex h n)⁻¹ *
      (ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h + 1 / 2)) *
        TemporalMeanUpdate.temporalInverse (TemporalMeanUpdate.centered f)
          (l * z.1, (P z.2.1, TemporalMeanUpdate.coverMap (ChartScales.nativeIndex h n) z.2.2))))
  rw [TemporalMeanUpdate.chartPrefactor_eq]
  have hpow : ChartScales.Q n ^ (-CoordinateAlgebra.A h) * ChartScales.Q n ^ (-1 - h) =
      ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h + 1 / 2)) := by
    rw [← Real.rpow_add (ChartScales.Q_pos n)]
    congr 1
    unfold CoordinateAlgebra.A
    ring
  calc
    _ = -(ChartScales.Q n ^ (-CoordinateAlgebra.A h) * ChartScales.Q n ^ (-1 - h)) *
      (ChartScales.Tg ^ ChartScales.nativeIndex h n)⁻¹ *
        TemporalMeanUpdate.temporalInverse (TemporalMeanUpdate.centered f)
          (l * z.1, (P z.2.1, TemporalMeanUpdate.coverMap (ChartScales.nativeIndex h n) z.2.2)) :=
              by
              ring
    _ = _ := by rw [hpow]; ring

/-- The common-index form of the actual temporal update. A common index
is independent of the dyadic band; the native recipe is its specialization. -/
noncomputable def temporalAtIndex (h : ℝ) (n i : ℕ)
    (f : PressureStream.Lift S → ℝ) (z : PressureStream.Lift S) : ℝ :=
  -((ChartScales.Tg ^ i * ChartScales.Q n ^ (1 + h))⁻¹) *
    TemporalMeanUpdate.temporalInverse (TemporalMeanUpdate.centered f) z

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem temporalAtIndex_native (h : ℝ) (n : ℕ) (f : PressureStream.Lift S → ℝ) :
    temporalAtIndex h n (ChartScales.nativeIndex h n) f = TemporalMeanUpdate.desiredIncrement h n f
        := rfl

/-- Physical temporal, given by `-TemporalMeanUpdate.temporalInverse
(TemporalMeanUpdate.centered f) z`. -/
noncomputable def physicalTemporal (f : PressureStream.Lift S → ℝ)
    (z : PressureStream.Lift S) : ℝ :=
  -TemporalMeanUpdate.temporalInverse (TemporalMeanUpdate.centered f) z

/-- All common indices give the same physical temporal operator after
the actual velocity and momentum normalizations. -/
theorem temporalAtIndex_physical_pull (h : ℝ) (n i : ℕ) (l : ℝ) (P : S →L[ℝ] T)
    {f : PressureStream.Lift T → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f) (z : PressureStream.Lift S) :
    coverPull l P i (ChartScales.Q n ^ (-CoordinateAlgebra.A h)) (temporalAtIndex h n i f) z =
      physicalTemporal (coverPull l P i (ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h + 1 / 2)))
          f) z := by
  unfold physicalTemporal
  rw [temporalInverse_centered_coverPull l P i _ hf hp]
  change ChartScales.Q n ^ (-CoordinateAlgebra.A h) *
      (-((ChartScales.Tg ^ i * ChartScales.Q n ^ (1 + h))⁻¹) *
        TemporalMeanUpdate.temporalInverse (TemporalMeanUpdate.centered f)
          (l * z.1, (P z.2.1, TemporalMeanUpdate.coverMap i z.2.2))) =
    -((ChartScales.Tg ^ i)⁻¹ *
      (ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h + 1 / 2)) *
        TemporalMeanUpdate.temporalInverse (TemporalMeanUpdate.centered f)
          (l * z.1, (P z.2.1, TemporalMeanUpdate.coverMap i z.2.2))))
  rw [mul_inv_rev, ← Real.rpow_neg (ChartScales.Q_pos n).le]
  have hpow : ChartScales.Q n ^ (-CoordinateAlgebra.A h) * ChartScales.Q n ^ (-(1 + h)) =
      ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h + 1 / 2)) := by
    rw [← Real.rpow_add (ChartScales.Q_pos n)]
    congr 1
    unfold CoordinateAlgebra.A
    ring
  calc
    _ = -(ChartScales.Q n ^ (-CoordinateAlgebra.A h) * ChartScales.Q n ^ (-(1 + h))) *
      (ChartScales.Tg ^ i)⁻¹ * TemporalMeanUpdate.temporalInverse (TemporalMeanUpdate.centered f)
        (l * z.1, (P z.2.1, TemporalMeanUpdate.coverMap i z.2.2)) := by ring
    _ = _ := by rw [hpow]; ring

end TorusPullback

section RankScaling

theorem normalizeDebt_scale {l u ell U : ℝ} (hl : l ≠ 0) (hu : u ≠ 0)
    (hell : ell ≠ 0) (hU : U ≠ 0) (d : MeanRankUpdate.Debt) :
    MeanRankUpdate.normalizeDebt (l * ell) (u * U) (MeanRankUpdate.scaleDebt l u d) =
      MeanRankUpdate.normalizeDebt ell U d := by
  ext i
  fin_cases i <;> simp [MeanRankUpdate.normalizeDebt, MeanRankUpdate.scaleDebt] <;>
    field_simp [hl, hu, hell, hU]

/-- Naturality of the constructed five-row inverse, not just of its rows. -/
theorem rankAngular_scale {l u ell U : ℝ} (hl : l ≠ 0) (hu : u ≠ 0)
    (hell : ell ≠ 0) (hU : U ≠ 0) (lam C a b : ℝ) (d : MeanRankUpdate.Debt) (r : ℝ) :
    MeanRankUpdate.angularIncrement lam C a b (l * ell) (u * U)
      (MeanRankUpdate.scaleDebt l u d) (l * r) =
        u * MeanRankUpdate.angularIncrement lam C a b ell U d r := by
  unfold MeanRankUpdate.angularIncrement
  rw [normalizeDebt_scale hl hu hell hU]
  simp only [MeanRankUpdate.scaleField, mul_div_mul_left _ _ hl]
  ring

theorem rankDesiredAxial_scale {l u ell U : ℝ} (hl : l ≠ 0) (hu : u ≠ 0)
    (hell : ell ≠ 0) (hU : U ≠ 0) (lam C a b : ℝ) (d : MeanRankUpdate.Debt) (r : ℝ) :
    MeanRankUpdate.desiredAxialIncrement lam C a b (l * ell) (u * U)
      (MeanRankUpdate.scaleDebt l u d) (l * r) =
        u * MeanRankUpdate.desiredAxialIncrement lam C a b ell U d r := by
  unfold MeanRankUpdate.desiredAxialIncrement
  rw [normalizeDebt_scale hl hu hell hU]
  simp only [MeanRankUpdate.scaleField, mul_div_mul_left _ _ hl]
  ring

theorem rankBackground_scale {l : ℝ} (hl : l ≠ 0) (u ell U lam C r : ℝ) :
    MeanRankUpdate.background lam C (l * ell) (u * U) (l * r) =
      u * MeanRankUpdate.background lam C ell U r := by
  simp only [MeanRankUpdate.background, MeanRankUpdate.scaleField, mul_div_mul_left _ _ hl]
  ring

end RankScaling

section CommonTemporalBounds

open TorusInverse

/-- Common ratio, given by `ChartScales.Tg ^ ChartScales.nativeIndex h n / ChartScales.Tg ^ i`. -/
noncomputable def commonRatio (h : ℝ) (n i : ℕ) : ℝ :=
  ChartScales.Tg ^ ChartScales.nativeIndex h n / ChartScales.Tg ^ i

theorem commonRatio_pos (h : ℝ) (n i : ℕ) : 0 < commonRatio h n i :=
  div_pos (pow_pos ChartScales.Tg_pos _) (pow_pos ChartScales.Tg_pos _)

theorem commonRatio_le {h : ℝ} {n i D : ℕ}
    (hgap : ChartScales.nativeIndex h n ≤ i + D) : commonRatio h n i ≤ ChartScales.Tg ^ D := by
  apply (div_le_iff₀ (pow_pos ChartScales.Tg_pos i)).mpr
  simpa only [pow_add, mul_comm] using pow_le_pow_right₀ ChartScales.Tg_one_lt.le hgap

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem temporalAtIndex_eq_native (h : ℝ) (n i : ℕ) (f : PressureStream.Lift S → ℝ) :
    temporalAtIndex h n i f = fun z => commonRatio h n i * TemporalMeanUpdate.desiredIncrement h n
        f z := by
  funext z
  unfold temporalAtIndex commonRatio TemporalMeanUpdate.desiredIncrement
    TemporalMeanUpdate.chartPrefactor ChartScales.timeCoefficient
  field_simp [pow_ne_zero _ ChartScales.Tg_pos.ne',
    (Real.rpow_pos_of_pos (ChartScales.Q_pos n) (1 + h)).ne']

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem temporalAtIndex_periodic (h : ℝ) (n i : ℕ) (f : PressureStream.Lift S → ℝ) :
    PressureStream.TorusPeriodicLift (temporalAtIndex h n i f) := by
  intro r s Y k
  exact congrArg (-((ChartScales.Tg ^ i * ChartScales.Q n ^ (1 + h))⁻¹) * ·)
    (TemporalMeanUpdate.temporalInverse_periodic (TemporalMeanUpdate.centered f) r s Y k)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem temporalAtIndex_supported (h : ℝ) (n i : ℕ) {a b : ℝ}
    {f : PressureStream.Lift S → ℝ} (hs : RadialAlias.RadiallySupported a b f) :
    RadialAlias.RadiallySupported a b (temporalAtIndex h n i f) := by
  intro z hz
  apply TemporalMeanUpdate.temporalInverse_supported (TemporalMeanUpdate.centered_supported hs)
  intro hi
  exact hz (by simp only [temporalAtIndex, hi, mul_zero])

theorem meanClass_temporalAtIndex_of_native (s : WeightedClasses.StripData (PressureStream.Lift S))
    {h α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ} (index : ℕ → ℕ) (D : ℕ)
    (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + D)
    (hf : WeightedClasses.MeanClass s α (fun n => TemporalMeanUpdate.desiredIncrement h n (f n))) :
    WeightedClasses.MeanClass s α (fun n => temporalAtIndex h n (index n) (f n)) := by
  have hb : WeightedClasses.BandBound s 0 (fun n => commonRatio h n (index n)) := by
    refine ⟨ChartScales.Tg ^ D, (pow_pos ChartScales.Tg_pos D).le, 0, ?_⟩
    intro n
    simp only [Real.norm_eq_abs, abs_of_pos (commonRatio_pos h n (index n)), Real.rpow_zero,
      pow_zero, mul_one]
    exact commonRatio_le (hgap n)
  have hout := hf.band_smul hb
  simpa only [add_zero, temporalAtIndex_eq_native, smul_eq_mul] using hout

/-- Fast at index, given by `(ChartScales.Tg ^ i * ChartScales.Q n ^ (1 + h)) *
PressureStream.graphDz ((0 : S), vector .temporal) f z`. -/
noncomputable def fastAtIndex (h : ℝ) (n i : ℕ) (f : PressureStream.Lift S → ℝ)
    (z : PressureStream.Lift S) : ℝ :=
  (ChartScales.Tg ^ i * ChartScales.Q n ^ (1 + h)) *
    PressureStream.graphDz ((0 : S), vector .temporal) f z

variable [FiniteDimensional ℝ S]

theorem temporalAtIndex_smooth (h : ℝ) (n i : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f) :
    ContDiff ℝ ∞ (temporalAtIndex h n i f) :=
  contDiff_const.mul (TemporalMeanUpdate.temporalInverse_smooth
    (TemporalMeanUpdate.centered_smooth hf) (TemporalMeanUpdate.centered_periodic hp))

theorem temporalAtIndex_fast_cancellation (h : ℝ) (n i : ℕ) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f) (z : PressureStream.Lift S) :
    fastAtIndex h n i (temporalAtIndex h n i f) z = -TemporalMeanUpdate.centered f z := by
  let c := ChartScales.Tg ^ i * ChartScales.Q n ^ (1 + h)
  have hc : c ≠ 0 := (mul_pos (pow_pos ChartScales.Tg_pos _)
    (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _)).ne'
  have hi := TemporalMeanUpdate.temporalInverse_smooth
    (TemporalMeanUpdate.centered_smooth hf) (TemporalMeanUpdate.centered_periodic hp)
  have hd := (((hi.differentiable (by simp)) z).hasFDerivAt).const_smul (-c⁻¹)
  change HasFDerivAt (temporalAtIndex h n i f) _ z at hd
  rw [fastAtIndex, PressureStream.graphDz, hd.fderiv]
  change c * (-c⁻¹ * PressureStream.graphDz ((0 : S), vector .temporal)
    (TemporalMeanUpdate.temporalInverse (TemporalMeanUpdate.centered f)) z) = _
  rw [TemporalMeanUpdate.temporalInverse_solves (TemporalMeanUpdate.centered_smooth hf)
    (TemporalMeanUpdate.centered_periodic hp) (TemporalMeanUpdate.centered_zeroMean hf)]
  field_simp

end CommonTemporalBounds

section PhysicalFamilies

open TorusInverse

theorem coverMap_eq_coverPower (i : ℕ) (Y : Plane) :
    TemporalMeanUpdate.coverMap i Y = CommonCoverSolve.coverPower i Y := by
  induction i with
  | zero => rfl
  | succ i hi =>
      change TemporalMeanUpdate.coverLinear (TemporalMeanUpdate.coverMap i Y) =
        CommonCoverSolve.coverEquiv (CommonCoverSolve.coverPower i Y)
      rw [hi, TemporalMeanUpdate.coverLinear_apply, CommonCoverSolve.coverEquiv_apply,
        SlotGeometry.cover_apply]
      rfl

theorem coverMap_radial (i : ℕ) :
    TemporalMeanUpdate.coverMap i (vector .radial) = ChartScales.Lambda ^ i • vector .radial := by
  rw [coverMap_eq_coverPower, CommonCoverSolve.coverPower_apply]
  exact PhysicalGraphBounds.cover_pow_radialDirection i

/-- Chart scale, given by `ChartScales.Q n ^ (-(1 / 2 : ℝ))`. -/
noncomputable def chartScale (n : ℕ) : ℝ := ChartScales.Q n ^ (-(1 / 2 : ℝ))

theorem chartScale_pos (n : ℕ) : 0 < chartScale n :=
  Real.rpow_pos_of_pos (ChartScales.Q_pos n) _

/-- Radial frequency, given by `M * ChartScales.Lambda ^ i * ChartScales.Q n ^ (d / 2)`. -/
noncomputable def radialFrequency (_h : ℝ) (n i : ℕ) (d M : ℝ) : ℝ :=
  M * ChartScales.Lambda ^ i * ChartScales.Q n ^ (d / 2)

theorem radialFrequency_scale (h : ℝ) (n i : ℕ) (d M : ℝ) :
    radialFrequency h n i d M * chartScale n ^ d = M * ChartScales.Lambda ^ i := by
  have hs : chartScale n ^ d = ChartScales.Q n ^ (-(d / 2)) := by
    unfold chartScale
    rw [← Real.rpow_mul (ChartScales.Q_pos n).le]
    congr 1
    ring
  rw [hs, radialFrequency, mul_assoc, ← Real.rpow_add (ChartScales.Q_pos n)]
  simp

theorem radialFrequency_native (h : ℝ) (n : ℕ) :
    radialFrequency h n (ChartScales.nativeIndex h n) (ChartScales.radialExponent h) 1 =
      ChartScales.radialCoefficient h n := by
  simp [radialFrequency, ChartScales.radialCoefficient]

theorem radialFrequency_shift (h : ℝ) (n i : ℕ) (d M : ℝ) :
    M • TemporalMeanUpdate.coverMap i (vector .radial) =
      (radialFrequency h n i d M * chartScale n ^ d) • vector .radial := by
  rw [coverMap_radial, smul_smul, radialFrequency_scale]

/-- The physical slow variables are `(z,τ)` with `τ=1-t`. -/
noncomputable def slowToChart (h : ℝ) (n : ℕ) : Plane →L[ℝ] Plane :=
  (ChartScales.Q n ^ (-CoordinateAlgebra.D h) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (ChartScales.Q n ^ (-1 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- Physical to chart, given by `chartLinear (chartScale n) ((slowToChart h n).prodMap
(TemporalMeanUpdate.coverMap i))`. -/
noncomputable def physicalToChart (h : ℝ) (n i : ℕ) :
    PressureStream.Lift Plane →L[ℝ] PressureStream.Lift Plane :=
  chartLinear (chartScale n) ((slowToChart h n).prodMap (TemporalMeanUpdate.coverMap i))

@[simp] theorem physicalToChart_apply (h : ℝ) (n i : ℕ) (z : PressureStream.Lift Plane) :
    physicalToChart h n i z = (chartScale n * z.1,
      ((ChartScales.Q n ^ (-CoordinateAlgebra.D h) * z.2.1.1,
        ChartScales.Q n ^ (-1 : ℝ) * z.2.1.2), TemporalMeanUpdate.coverMap i z.2.2)) := rfl

/-- Normalize a chart field of scaling degree `a` on the actual physical
slow variables and absolute auxiliary lift. -/
noncomputable def fieldOnPhysical (h : ℝ) (n i : ℕ) (a : ℝ)
    (f : PressureStream.Lift Plane → ℝ) : PressureStream.Lift Plane → ℝ :=
  coverPull (chartScale n) (slowToChart h n) i (ChartScales.Q n ^ (-a)) f

theorem fieldOnPhysical_apply (h : ℝ) (n i : ℕ) (a : ℝ)
    (f : PressureStream.Lift Plane → ℝ) (z : PressureStream.Lift Plane) :
    fieldOnPhysical h n i a f z = ChartScales.Q n ^ (-a) * f (physicalToChart h n i z) := rfl

theorem pressure_unit_factor (h : ℝ) (n : ℕ) :
    ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h + 1 / 2)) / chartScale n =
      ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h)) := by
  unfold chartScale
  rw [← Real.rpow_sub (ChartScales.Q_pos n)]
  congr 1
  ring

/-- A chart-specific instance of the existing reconstruction recipe. The
physical endpoints and frequency are transported, rather than copied. -/
noncomputable def bandReconstruction (h : ℝ) (n i : ℕ) (d a b M : ℝ) (hab : a < b) :
    CorrectionState.ReconstructionData where
  exponent := d
  inner := chartScale n * a
  outer := chartScale n * b
  inner_lt_outer := mul_lt_mul_of_pos_left hab (chartScale_pos n)
  frequency _ := radialFrequency h n i d M
  radialDirection := vector .radial

/-- The normalized chart pressure is exactly one physical pressure
operator applied to the normalized radial source. -/
theorem physicalPressure_naturality {d a b : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (h : ℝ) (n i : ℕ) (M : ℝ) {f : PressureStream.Lift Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f)
    (hs : RadialAlias.RadiallySupported (chartScale n * a) (chartScale n * b) f) :
    PressureStream.meanPressure d a b M hab (vector .radial)
      (fieldOnPhysical h n i (2 * CoordinateAlgebra.A h + 1 / 2) f) =
        fieldOnPhysical h n i (2 * CoordinateAlgebra.A h)
          (PressureStream.meanPressure d (chartScale n * a) (chartScale n * b)
            (radialFrequency h n i d M) (mul_lt_mul_of_pos_left hab (chartScale_pos n))
            (vector .radial) f) := by
  funext z
  have ht := meanPressure_coverPull (chartScale_pos n) ha hab hd (slowToChart h n) i M
    (radialFrequency h n i d M) (ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h + 1 / 2)))
    (vector .radial) (vector .radial) (radialFrequency_shift h n i d M) hf hp hs z
  rw [pressure_unit_factor] at ht
  exact ht

/-- Reconstruct pressure family, given by `{ u with pressure := fun n =>
(CorrectionState.reconstructPressure (r n) c u).pressure n }`. -/
noncomputable def reconstructPressureFamily (r : ℕ → CorrectionState.ReconstructionData)
    (c : CorrectionState.Context (PressureStream.Lift Plane))
    (u : CorrectionState.State (PressureStream.Lift Plane)) :
    CorrectionState.State (PressureStream.Lift Plane) :=
  { u with pressure := fun n => (CorrectionState.reconstructPressure (r n) c u).pressure n }

/-- If the normalized sources are one physical source, the recomputed
pressures are representations of its single, defined physical pressure.
Compatibility of the output is the conclusion, not an input. -/
theorem reconstructPressureFamily_represents {d a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (h M : ℝ) (index : ℕ → ℕ)
    (c : CorrectionState.Context (PressureStream.Lift Plane))
    (u : CorrectionState.State (PressureStream.Lift Plane))
    (F : PressureStream.Lift Plane → ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (u.gr c n))
    (hp : ∀ n, PressureStream.TorusPeriodicLift (u.gr c n))
    (hs : ∀ n, RadialAlias.RadiallySupported (chartScale n * a) (chartScale n * b) (u.gr c n))
    (hsource : ∀ n, fieldOnPhysical h n (index n) (2 * CoordinateAlgebra.A h + 1 / 2) (u.gr c n) =
        F) :
    ∀ n, fieldOnPhysical h n (index n) (2 * CoordinateAlgebra.A h)
      ((reconstructPressureFamily (fun k => bandReconstruction h k (index k) d a b M hab) c
          u).pressure n) =
        PressureStream.meanPressure d a b M hab (vector .radial) F := by
  intro n
  have ht := physicalPressure_naturality ha hab hd h n (index n) M (hf n) (hp n) (hs n)
  rw [hsource n] at ht
  exact ht.symm

theorem temporalFamily_represents (h : ℝ) (index : ℕ → ℕ)
    (f : ℕ → PressureStream.Lift Plane → ℝ) (F : PressureStream.Lift Plane → ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hp : ∀ n, PressureStream.TorusPeriodicLift (f n))
    (hsource : ∀ n, fieldOnPhysical h n (index n) (2 * CoordinateAlgebra.A h + 1 / 2) (f n) = F) :
    ∀ n, fieldOnPhysical h n (index n) (CoordinateAlgebra.A h)
      (temporalAtIndex h n (index n) (f n)) = physicalTemporal F := by
  intro n
  have ht : fieldOnPhysical h n (index n) (CoordinateAlgebra.A h)
      (temporalAtIndex h n (index n) (f n)) = physicalTemporal
        (fieldOnPhysical h n (index n) (2 * CoordinateAlgebra.A h + 1 / 2) (f n)) := by
    funext z
    exact temporalAtIndex_physical_pull h n (index n) (chartScale n) (slowToChart h n) (hf n) (hp
        n) z
  rw [hsource n] at ht
  exact ht

end PhysicalFamilies

section ReconstructedStream

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem reconstructedGamma_pull {l a b d : ℝ} (hl : 0 < l) (ha : 0 < a)
    (hab : a < b) (hd : 0 < d) (C : E →L[ℝ] F) (M N u : ℝ) (v : E) (w : F)
    (hshift : M • C v = (N * l ^ d) • w) {f : ℝ × F → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported (l * a) (l * b) f)
    (z : ℝ × E) (hz : 0 ≤ z.1) :
    PressureStream.streamGamma (PressureStream.physicalSpeed d M) v
      (PressureStream.streamPotential d a b M v (pull l C u f)) z =
        u * PressureStream.streamGamma (PressureStream.physicalSpeed d N) w
          (PressureStream.streamPotential d (l * a) (l * b) N w f) (chartLinear l C z) := by
  rw [streamPotential_pull hl ha hab hd C M N u v w hshift hf hs,
    streamGamma_pull hl.ne' C (u / l) _ _ v w
      (((PressureStream.streamPotential_contDiff (mul_pos hl ha)
        (mul_lt_mul_of_pos_left hab hl) hd w hf hs).differentiable (by simp)) _)
      (physicalSpeed_vector hl hz C d M N v w hshift), div_mul_cancel₀ _ hl.ne']

theorem reconstructedBeta_pull {l a b d : ℝ} (hl : 0 < l) (ha : 0 < a)
    (hab : a < b) (hd : 0 < d) (C : E →L[ℝ] F) (M N u : ℝ) (v : E) (w : F)
    (hshift : M • C v = (N * l ^ d) • w) (znew : E) (zold : F)
    (haxial : C znew = l • zold) {f : ℝ × F → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported (l * a) (l * b) f) (z : ℝ × E) :
    PressureStream.streamBeta znew
      (PressureStream.streamPotential d a b M v (pull l C u f)) z =
        u * PressureStream.streamBeta zold
          (PressureStream.streamPotential d (l * a) (l * b) N w f) (chartLinear l C z) := by
  rw [streamPotential_pull hl ha hab hd C M N u v w hshift hf hs,
    streamBeta_pull l C (u / l) l znew zold
      (((PressureStream.streamPotential_contDiff (mul_pos hl ha)
        (mul_lt_mul_of_pos_left hab hl) hd w hf hs).differentiable (by simp)) _) haxial,
    div_mul_cancel₀ _ hl.ne']

/-- The axial alias itself transforms as a velocity. It is retained as
the exact compactification term. -/
theorem streamAlias_pull {l a b d : ℝ} (hl : 0 < l) (ha : 0 < a)
    (hab : a < b) (hd : 0 < d) (C : E →L[ℝ] F) (M N u : ℝ) (v : E) (w : F)
    (hshift : M • C v = (N * l ^ d) • w) {f : ℝ × F → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported (l * a) (l * b) f)
    (z : ℝ × E) (hz : 0 ≤ z.1) :
    RadialPullback.physicalAlias d a b M v (PressureStream.weightedSource (pull l C u f)) z / z.1 =
      u * (RadialPullback.physicalAlias d (l * a) (l * b) N w
        (PressureStream.weightedSource f) (chartLinear l C z) / (l * z.1)) := by
  have he := reconstructedGamma_pull hl ha hab hd C M N u v w hshift hf hs z hz
  rw [PressureStream.streamGamma_eq_desired_sub_alias_global ha hab hd v
    (pull_smooth l C u hf) (pull_supported hl C u hs),
    PressureStream.streamGamma_eq_desired_sub_alias_global (mul_pos hl ha)
      (mul_lt_mul_of_pos_left hab hl) hd w hf hs] at he
  change u * f (chartLinear l C z) - _ =
    u * (f (chartLinear l C z) -
      RadialPullback.physicalAlias d (l * a) (l * b) N w
        (PressureStream.weightedSource f) (chartLinear l C z) / (l * z.1)) at he
  linarith

end ReconstructedStream

section PressureAlias

open TorusInverse

variable {S T : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup T] [NormedSpace ℝ T]

theorem pressureAlias_eq_source_sub_derivative {d a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : Plane)
    {f : PressureStream.Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f) (z : PressureStream.Lift S) :
    PressureStream.pressureAlias d a b M hab v f z =
      PressureStream.pressureSource a b hab f z -
        PressureStream.graphDr (PressureStream.physicalSpeed d M) ((0 : S), v)
          (PressureStream.meanPressure d a b M hab v f) z := by
  have he := PressureStream.meanPressure_radial_residual_global (M := M) ha hab hd v hf hs z
  unfold PressureStream.pressureSource
  linarith

theorem pressureAlias_coverPull {l a b d : ℝ} (hl : 0 < l) (ha : 0 < a)
    (hab : a < b) (hd : 0 < d) (P : S →L[ℝ] T) (k : ℕ) (M N u : ℝ)
    (v w : Plane) (hshift : M • TemporalMeanUpdate.coverMap k v = (N * l ^ d) • w)
    {f : PressureStream.Lift T → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f)
    (hs : RadialAlias.RadiallySupported (l * a) (l * b) f)
    (z : PressureStream.Lift S) (hz : 0 ≤ z.1) :
    PressureStream.pressureAlias d a b M hab v (coverPull l P k u f) z =
      coverPull l P k u
        (PressureStream.pressureAlias d (l * a) (l * b) N (mul_lt_mul_of_pos_left hab hl) w f) z :=
            by
  let C := P.prodMap (TemporalMeanUpdate.coverMap k)
  have hvector : M • C ((0 : S), v) = (N * l ^ d) • ((0 : T), w) := by
    apply Prod.ext
    · simp [C]
    · exact hshift
  have hpressure : PressureStream.meanPressure d a b M hab v (coverPull l P k u f) =
      pull l C (u / l) (PressureStream.meanPressure d (l * a) (l * b) N
        (mul_lt_mul_of_pos_left hab hl) w f) := by
    funext x
    exact meanPressure_coverPull hl ha hab hd P k M N u v w hshift hf hp hs x
  have hps := PressureStream.meanPressure_contDiff (M := N) (mul_pos hl ha)
    (mul_lt_mul_of_pos_left hab hl) hd w hf hs
  rw [pressureAlias_eq_source_sub_derivative ha hab hd v (coverPull_smooth l P k u hf)
    (pull_supported hl C u hs), pressureSource_coverPull hl hab P k u hf hp, hpressure,
    graphDr_pull l C (u / l) _ _ ((0 : S), v) ((0 : T), w)
      ((hps.differentiable (by simp)) _)
      (physicalSpeed_vector hl hz C d M N ((0 : S), v) ((0 : T), w) hvector),
    div_mul_cancel₀ _ hl.ne']
  change u * PressureStream.pressureSource (l * a) (l * b) _ f (chartLinear l C z) -
      u * PressureStream.graphDr _ _ _ (chartLinear l C z) =
    u * PressureStream.pressureAlias d (l * a) (l * b) N _ w f (chartLinear l C z)
  rw [pressureAlias_eq_source_sub_derivative (mul_pos hl ha) (mul_lt_mul_of_pos_left hab hl) hd w
      hf hs]
  ring

end PressureAlias

section CommonTemporalReconstruction

open TorusInverse

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- The potential uses the explicitly chosen common torus index. -/
noncomputable def commonTemporalPotential (r : ℕ → CorrectionState.ReconstructionData)
    (h : ℝ) (index : ℕ → ℕ) (f : ℕ → PressureStream.Lift S → ℝ) (n : ℕ) :
    PressureStream.Lift S → ℝ :=
  PressureStream.streamPotential (r n).exponent (r n).inner (r n).outer ((r n).frequency n)
    ((0 : S), (r n).radialDirection) (temporalAtIndex h n (index n) (f n))

/-- Common temporal fields, bundling `radial`, `angular`, `axial`. -/
noncomputable def commonTemporalFields (r : ℕ → CorrectionState.ReconstructionData)
    (h : ℝ) (index : ℕ → ℕ) (epsilon : ℕ → ℝ) (axial : S × Plane)
    (fθ fz : ℕ → PressureStream.Lift S → ℝ) : MeanIncrementBounds.Triple (PressureStream.Lift S)
        where
  radial := fun n => PressureStream.streamBeta (epsilon n • axial)
    (commonTemporalPotential r h index fz n)
  angular := fun n => temporalAtIndex h n (index n) (fθ n)
  axial := fun n => PressureStream.streamGamma
    (PressureStream.physicalSpeed (r n).exponent ((r n).frequency n))
    ((0 : S), (r n).radialDirection) (commonTemporalPotential r h index fz n)

/-- Common temporal alias, constructed using `PressureStream.divideRadius`. -/
noncomputable def commonTemporalAlias (r : ℕ → CorrectionState.ReconstructionData)
    (h : ℝ) (index : ℕ → ℕ) (f : ℕ → PressureStream.Lift S → ℝ) (n : ℕ) :
    PressureStream.Lift S → ℝ :=
  PressureStream.divideRadius (RadialPullback.physicalAlias (r n).exponent (r n).inner
    (r n).outer ((r n).frequency n) ((0 : S), (r n).radialDirection)
    (PressureStream.weightedSource (temporalAtIndex h n (index n) (f n))))

/-- Common temporal increment, given by `commonTemporalFields r h index c.operators.epsilon
axial (u.thetaResidual c) (u.axialResidual c)`. -/
noncomputable def commonTemporalIncrement (r : ℕ → CorrectionState.ReconstructionData)
    (h : ℝ) (index : ℕ → ℕ) (axial : S × Plane)
    (c : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S)) :
    MeanIncrementBounds.Triple (PressureStream.Lift S) :=
  commonTemporalFields r h index c.operators.epsilon axial (u.thetaResidual c) (u.axialResidual c)

variable [FiniteDimensional ℝ S]

omit [FiniteDimensional ℝ S] in
theorem commonTemporalIncrement_native (r : CorrectionState.ReconstructionData)
    (h : ℝ) (axial : S × Plane) (c : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S)) :
    commonTemporalIncrement (fun _ => r) h (ChartScales.nativeIndex h) axial c u =
      CorrectionState.temporalIncrement r h axial c u := rfl

theorem commonTemporalPotential_smooth (r : ℕ → CorrectionState.ReconstructionData)
    (h : ℝ) (index : ℕ → ℕ) (f : ℕ → PressureStream.Lift S → ℝ) (n : ℕ)
    (ha : 0 < (r n).inner) (hd : 0 < (r n).exponent)
    (hf : ContDiff ℝ ∞ (f n)) (hp : PressureStream.TorusPeriodicLift (f n))
    (hs : RadialAlias.RadiallySupported (r n).inner (r n).outer (f n)) :
    ContDiff ℝ ∞ (commonTemporalPotential r h index f n) :=
  PressureStream.streamPotential_contDiff ha (r n).inner_lt_outer hd _
    (temporalAtIndex_smooth h n (index n) hf hp) (temporalAtIndex_supported h n (index n) hs)

theorem commonTemporalPotential_supported (r : ℕ → CorrectionState.ReconstructionData)
    (h : ℝ) (index : ℕ → ℕ) (f : ℕ → PressureStream.Lift S → ℝ) (n : ℕ)
    (ha : 0 < (r n).inner) (hd : 0 < (r n).exponent)
    (hf : ContDiff ℝ ∞ (f n)) (hp : PressureStream.TorusPeriodicLift (f n))
    (hs : RadialAlias.RadiallySupported (r n).inner (r n).outer (f n)) :
    RadialAlias.RadiallySupported (r n).inner (r n).outer (commonTemporalPotential r h index f n) :=
  PressureStream.streamPotential_supported ha (r n).inner_lt_outer hd _
    (temporalAtIndex_smooth h n (index n) hf hp) (temporalAtIndex_supported h n (index n) hs)

theorem commonTemporalAlias_smooth (r : ℕ → CorrectionState.ReconstructionData)
    (h : ℝ) (index : ℕ → ℕ) (f : ℕ → PressureStream.Lift S → ℝ) (n : ℕ)
    (ha : 0 < (r n).inner) (hd : 0 < (r n).exponent)
    (hf : ContDiff ℝ ∞ (f n)) (hp : PressureStream.TorusPeriodicLift (f n))
    (hs : RadialAlias.RadiallySupported (r n).inner (r n).outer (f n)) :
    ContDiff ℝ ∞ (commonTemporalAlias r h index f n) :=
  PressureStream.divideRadius_contDiff ha
    (RadialPullback.physicalAlias_contDiff ha (r n).inner_lt_outer hd
      (PressureStream.weightedSource_contDiff (temporalAtIndex_smooth h n (index n) hf hp))
      (PressureStream.weightedSource_supported (temporalAtIndex_supported h n (index n) hs))
      ((r n).frequency n) ((0 : S), (r n).radialDirection))
    (RadialPullback.physicalAlias_supported ha (r n).inner_lt_outer hd _ _ _)

theorem commonTemporalFields_axial_eq (r : ℕ → CorrectionState.ReconstructionData)
    (h : ℝ) (index : ℕ → ℕ) (epsilon : ℕ → ℝ) (axial : S × Plane)
    (fθ fz : ℕ → PressureStream.Lift S → ℝ) (n : ℕ)
    (ha : 0 < (r n).inner) (hd : 0 < (r n).exponent)
    (hf : ContDiff ℝ ∞ (fz n)) (hp : PressureStream.TorusPeriodicLift (fz n))
    (hs : RadialAlias.RadiallySupported (r n).inner (r n).outer (fz n)) :
    (commonTemporalFields r h index epsilon axial fθ fz).axial n =
      fun z => temporalAtIndex h n (index n) (fz n) z - commonTemporalAlias r h index fz n z := by
  funext z
  exact PressureStream.streamGamma_eq_desired_sub_alias_global ha (r n).inner_lt_outer hd _
    (temporalAtIndex_smooth h n (index n) hf hp) (temporalAtIndex_supported h n (index n) hs) z

theorem commonTemporalFields_fast_cancellation (r : ℕ → CorrectionState.ReconstructionData)
    (h : ℝ) (index : ℕ → ℕ) (epsilon : ℕ → ℝ) (axial : S × Plane)
    (fθ fz : ℕ → PressureStream.Lift S → ℝ) (n : ℕ)
    (ha : 0 < (r n).inner) (hd : 0 < (r n).exponent)
    (hθ : ContDiff ℝ ∞ (fθ n)) (hz : ContDiff ℝ ∞ (fz n))
    (hpθ : PressureStream.TorusPeriodicLift (fθ n)) (hpz : PressureStream.TorusPeriodicLift (fz n))
    (hsz : RadialAlias.RadiallySupported (r n).inner (r n).outer (fz n))
    (z : PressureStream.Lift S) :
    fastAtIndex h n (index n) ((commonTemporalFields r h index epsilon axial fθ fz).angular n) z +
        TemporalMeanUpdate.centered (fθ n) z = 0 ∧
    fastAtIndex h n (index n) ((commonTemporalFields r h index epsilon axial fθ fz).axial n) z +
        TemporalMeanUpdate.centered (fz n) z =
      -fastAtIndex h n (index n) (commonTemporalAlias r h index fz n) z := by
  constructor
  · exact add_eq_zero_iff_eq_neg.mpr (temporalAtIndex_fast_cancellation h n (index n) hθ hpθ z)
  · rw [commonTemporalFields_axial_eq r h index epsilon axial fθ fz n ha hd hz hpz hsz]
    have hf := (temporalAtIndex_smooth h n (index n) hz hpz).differentiable (by simp)
    have hg := (commonTemporalAlias_smooth r h index fz n ha hd hz hpz hsz).differentiable (by simp)
    have he : fastAtIndex h n (index n)
        (fun z => temporalAtIndex h n (index n) (fz n) z - commonTemporalAlias r h index fz n z) z =
        fastAtIndex h n (index n) (temporalAtIndex h n (index n) (fz n)) z -
          fastAtIndex h n (index n) (commonTemporalAlias r h index fz n) z := by
      simp only [fastAtIndex, PressureStream.graphDz, fderiv_fun_sub (hf z) (hg z),
        _root_.sub_apply, mul_sub]
    rw [he, temporalAtIndex_fast_cancellation h n (index n) hz hpz z]
    ring

end CommonTemporalReconstruction

section PhysicalTemporalFields

open TorusInverse

/-- Physical auxiliary, given by `(slowToChart h n).prodMap (TemporalMeanUpdate.coverMap i)`. -/
noncomputable def physicalAuxiliary (h : ℝ) (n i : ℕ) : Plane × Plane →L[ℝ] Plane × Plane :=
  (slowToChart h n).prodMap (TemporalMeanUpdate.coverMap i)

/-- Axial unit, given by `((1, 0), (0, 0))`. -/
noncomputable def axialUnit : Plane × Plane := ((1, 0), (0, 0))

theorem physicalAuxiliary_radial (h : ℝ) (n i : ℕ) (d M : ℝ) :
    M • physicalAuxiliary h n i ((0 : Plane), vector .radial) =
      (radialFrequency h n i d M * chartScale n ^ d) • ((0 : Plane), vector .radial) := by
  apply Prod.ext
  · simp [physicalAuxiliary]
  · exact radialFrequency_shift h n i d M

theorem physicalAuxiliary_temporal (h : ℝ) (n i : ℕ) :
    physicalAuxiliary h n i ((0 : Plane), vector .temporal) =
      ChartScales.Tg ^ i • ((0 : Plane), vector .temporal) := by
  apply Prod.ext
  · simp [physicalAuxiliary]
  · exact TemporalMeanUpdate.coverMap_temporal i

theorem physicalAuxiliary_axial (h : ℝ) (n i : ℕ) :
    physicalAuxiliary h n i axialUnit =
      chartScale n • (ChartScales.epsilon h n • axialUnit) := by
  have he : ChartScales.Q n ^ (-CoordinateAlgebra.D h) =
      chartScale n * ChartScales.epsilon h n := by
    rw [chartScale, ChartScales.epsilon, ← Real.rpow_add (ChartScales.Q_pos n)]
    congr 1
    unfold CoordinateAlgebra.D
    ring
  simp only [physicalAuxiliary, slowToChart, he, axialUnit, ContinuousLinearMap.coe_prodMap',
      Prod.map_apply,
    ContinuousLinearMap.prod_apply, smul_apply, ContinuousLinearMap.coe_fst', smul_eq_mul, mul_one,
    ContinuousLinearMap.coe_snd', mul_zero, Prod.smul_mk, Prod.mk.injEq, true_and]
  exact (TemporalMeanUpdate.coverMap i).map_zero

theorem physicalFast_naturality (h : ℝ) (n i : ℕ) {f : PressureStream.Lift Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (z : PressureStream.Lift Plane) :
    fieldOnPhysical h n i (2 * CoordinateAlgebra.A h + 1 / 2) (fastAtIndex h n i f) z =
      PressureStream.graphDz ((0 : Plane), vector .temporal)
        (fieldOnPhysical h n i (CoordinateAlgebra.A h) f) z := by
  have he := graphDz_pull (chartScale n) (physicalAuxiliary h n i)
    (ChartScales.Q n ^ (-CoordinateAlgebra.A h)) (ChartScales.Tg ^ i)
    ((0 : Plane), vector .temporal) ((0 : Plane), vector .temporal)
    ((hf.differentiable (by simp)) (physicalToChart h n i z)) (physicalAuxiliary_temporal h n i)
  change PressureStream.graphDz _ (fieldOnPhysical h n i (CoordinateAlgebra.A h) f) z = _ at he
  rw [he, fieldOnPhysical_apply, fastAtIndex]
  have hunit : ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h + 1 / 2)) *
      ChartScales.Q n ^ (1 + h) = ChartScales.Q n ^ (-CoordinateAlgebra.A h) := by
    rw [← Real.rpow_add (ChartScales.Q_pos n)]
    congr 1
    unfold CoordinateAlgebra.A
    ring
  change ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h + 1 / 2)) *
    ((ChartScales.Tg ^ i * ChartScales.Q n ^ (1 + h)) *
      PressureStream.graphDz _ f (physicalToChart h n i z)) = _
  rw [show ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h + 1 / 2)) *
      ((ChartScales.Tg ^ i * ChartScales.Q n ^ (1 + h)) *
        PressureStream.graphDz ((0 : Plane), vector .temporal) f (physicalToChart h n i z)) =
      (ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h + 1 / 2)) * ChartScales.Q n ^ (1 + h)) *
        ChartScales.Tg ^ i * PressureStream.graphDz _ f (physicalToChart h n i z) by ring, hunit]
  rfl

theorem physicalGamma_naturality {d a b : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (h : ℝ) (n i : ℕ) (M : ℝ) {f : PressureStream.Lift Plane → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported (chartScale n * a) (chartScale n * b) f)
    (z : PressureStream.Lift Plane) (hz : 0 ≤ z.1) :
    PressureStream.streamGamma (PressureStream.physicalSpeed d M) ((0 : Plane), vector .radial)
      (PressureStream.streamPotential d a b M ((0 : Plane), vector .radial)
        (fieldOnPhysical h n i (CoordinateAlgebra.A h) f)) z =
      fieldOnPhysical h n i (CoordinateAlgebra.A h)
        (PressureStream.streamGamma (PressureStream.physicalSpeed d (radialFrequency h n i d M))
          ((0 : Plane), vector .radial)
          (PressureStream.streamPotential d (chartScale n * a) (chartScale n * b)
            (radialFrequency h n i d M) ((0 : Plane), vector .radial) f)) z :=
  reconstructedGamma_pull (chartScale_pos n) ha hab hd (physicalAuxiliary h n i)
    M (radialFrequency h n i d M) (ChartScales.Q n ^ (-CoordinateAlgebra.A h))
    ((0 : Plane), vector .radial) ((0 : Plane), vector .radial)
    (physicalAuxiliary_radial h n i d M) hf hs z hz

theorem physicalBeta_naturality {d a b : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (h : ℝ) (n i : ℕ) (M : ℝ) {f : PressureStream.Lift Plane → ℝ}
    (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported (chartScale n * a) (chartScale n * b) f)
    (z : PressureStream.Lift Plane) :
    PressureStream.streamBeta axialUnit
      (PressureStream.streamPotential d a b M ((0 : Plane), vector .radial)
        (fieldOnPhysical h n i (CoordinateAlgebra.A h) f)) z =
      fieldOnPhysical h n i (CoordinateAlgebra.A h)
        (PressureStream.streamBeta (ChartScales.epsilon h n • axialUnit)
          (PressureStream.streamPotential d (chartScale n * a) (chartScale n * b)
            (radialFrequency h n i d M) ((0 : Plane), vector .radial) f)) z :=
  reconstructedBeta_pull (chartScale_pos n) ha hab hd (physicalAuxiliary h n i)
    M (radialFrequency h n i d M) (ChartScales.Q n ^ (-CoordinateAlgebra.A h))
    ((0 : Plane), vector .radial) ((0 : Plane), vector .radial)
    (physicalAuxiliary_radial h n i d M) axialUnit (ChartScales.epsilon h n • axialUnit)
    (physicalAuxiliary_axial h n i) hf hs z

/-- One physical vector field, constructed from the two physical sources. -/
noncomputable def physicalTemporalFields (d a b M : ℝ)
    (Fθ Fz : PressureStream.Lift Plane → ℝ) (z : PressureStream.Lift Plane) : Fin 3 → ℝ :=
  ![PressureStream.streamBeta axialUnit
      (PressureStream.streamPotential d a b M ((0 : Plane), vector .radial) (physicalTemporal Fz))
          z,
    physicalTemporal Fθ z,
    PressureStream.streamGamma (PressureStream.physicalSpeed d M) ((0 : Plane), vector .radial)
      (PressureStream.streamPotential d a b M ((0 : Plane), vector .radial) (physicalTemporal Fz))
          z]

/-- The three defined chart components are restrictions of one physical
vector field. The source identities are the only compatibility premises. -/
theorem commonTemporalFields_represents {d a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (h M : ℝ) (index : ℕ → ℕ)
    (fθ fz : ℕ → PressureStream.Lift Plane → ℝ) (Fθ Fz : PressureStream.Lift Plane → ℝ)
    (hθ : ∀ n, ContDiff ℝ ∞ (fθ n)) (hz : ∀ n, ContDiff ℝ ∞ (fz n))
    (hpθ : ∀ n, PressureStream.TorusPeriodicLift (fθ n))
    (hpz : ∀ n, PressureStream.TorusPeriodicLift (fz n))
    (hsz : ∀ n, RadialAlias.RadiallySupported (chartScale n * a) (chartScale n * b) (fz n))
    (hsourceθ : ∀ n, fieldOnPhysical h n (index n) (2 * CoordinateAlgebra.A h + 1 / 2) (fθ n) = Fθ)
    (hsourcez : ∀ n, fieldOnPhysical h n (index n) (2 * CoordinateAlgebra.A h + 1 / 2) (fz n) = Fz)
    (n : ℕ) (z : PressureStream.Lift Plane) (hr : 0 ≤ z.1) :
    let δ := commonTemporalFields (fun k => bandReconstruction h k (index k) d a b M hab)
      h index (ChartScales.epsilon h) axialUnit fθ fz
    ![fieldOnPhysical h n (index n) (CoordinateAlgebra.A h) (δ.radial n) z,
      fieldOnPhysical h n (index n) (CoordinateAlgebra.A h) (δ.angular n) z,
      fieldOnPhysical h n (index n) (CoordinateAlgebra.A h) (δ.axial n) z] =
        physicalTemporalFields d a b M Fθ Fz z := by
  have hθphys := temporalFamily_represents h index fθ Fθ hθ hpθ hsourceθ n
  have hzphys := temporalFamily_represents h index fz Fz hz hpz hsourcez n
  have hβ := physicalBeta_naturality ha hab hd h n (index n) M
    (temporalAtIndex_smooth h n (index n) (hz n) (hpz n))
    (temporalAtIndex_supported h n (index n) (hsz n)) z
  have hγ := physicalGamma_naturality ha hab hd h n (index n) M
    (temporalAtIndex_smooth h n (index n) (hz n) (hpz n))
    (temporalAtIndex_supported h n (index n) (hsz n)) z hr
  rw [hzphys] at hβ hγ
  ext j
  fin_cases j
  · exact hβ.symm
  · exact congrFun hθphys z
  · exact hγ.symm

end PhysicalTemporalFields

section DebtTransport

open TorusInverse

variable {S T : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup T] [NormedSpace ℝ T]

/-- Source moment, given by `PressureStream.pressureMass (fun z => z.1 ^ m * f z) s`. -/
noncomputable def sourceMoment (m : ℕ) (f : PressureStream.Lift S → ℝ) (s : S) : ℝ :=
  PressureStream.pressureMass (fun z => z.1 ^ m * f z) s

/-- Source debt, given by `![sourceMoment 0 g s, sourceMoment 2 qθ s, sourceMoment 1 qz s - (1 /
2 : ℝ) * sourceMoment 2 g s]`. -/
noncomputable def sourceDebt (g qθ qz : PressureStream.Lift S → ℝ) (s : S) : MeanRankUpdate.Debt :=
  ![sourceMoment 0 g s, sourceMoment 2 qθ s, sourceMoment 1 qz s - (1 / 2 : ℝ) * sourceMoment 2 g s]

theorem sourceMoment_coverPull {l : ℝ} (hl : 0 < l) (P : S →L[ℝ] T)
    (k m : ℕ) (u : ℝ) {f : PressureStream.Lift T → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : PressureStream.TorusPeriodicLift f) (s : S) :
    sourceMoment m (coverPull l P k u f) s =
      (u / l ^ (m + 1)) * sourceMoment m f (P s) := by
  have he : (fun z : PressureStream.Lift S => z.1 ^ m * coverPull l P k u f z) =
      coverPull l P k (u / l ^ m) (fun z => z.1 ^ m * f z) := by
    funext z
    change z.1 ^ m * (u * f (chartLinear l (P.prodMap (TemporalMeanUpdate.coverMap k)) z)) =
      (u / l ^ m) * ((l * z.1) ^ m * f (chartLinear l (P.prodMap (TemporalMeanUpdate.coverMap k))
          z))
    rw [mul_pow]
    field_simp
  have hfp : PressureStream.TorusPeriodicLift (fun z : PressureStream.Lift T => z.1 ^ m * f z) := by
    intro r t Y j
    exact congrArg (r ^ m * ·) (hp r t Y j)
  unfold sourceMoment
  rw [he, pressureMass_coverPull hl P k (u / l ^ m) ((contDiff_fst.pow m).mul hf) hfp]
  rw [pow_succ]
  field_simp

/-- The radial source carries one additional inverse-length factor.
The actual three integrated debts then have the required different length powers. -/
theorem sourceDebt_coverPull {l : ℝ} (hl : 0 < l) (P : S →L[ℝ] T) (k : ℕ) (u : ℝ)
    {g qθ qz : PressureStream.Lift T → ℝ}
    (hg : ContDiff ℝ ∞ g) (hθ : ContDiff ℝ ∞ qθ) (hz : ContDiff ℝ ∞ qz)
    (hpg : PressureStream.TorusPeriodicLift g) (hpθ : PressureStream.TorusPeriodicLift qθ)
    (hpz : PressureStream.TorusPeriodicLift qz) (s : S) :
    sourceDebt (coverPull l P k (l * u ^ 2) g) (coverPull l P k (u ^ 2) qθ)
      (coverPull l P k (u ^ 2) qz) s =
        MeanRankUpdate.scaleDebt l⁻¹ u (sourceDebt g qθ qz (P s)) := by
  ext j
  fin_cases j
  · change sourceMoment 0 (coverPull l P k (l * u ^ 2) g) s =
      u ^ 2 * sourceMoment 0 g (P s)
    rw [sourceMoment_coverPull hl P k 0 (l * u ^ 2) hg hpg]
    simp [hl.ne']
  · change sourceMoment 2 (coverPull l P k (u ^ 2) qθ) s =
      l⁻¹ ^ 3 * u ^ 2 * sourceMoment 2 qθ (P s)
    rw [sourceMoment_coverPull hl P k 2 (u ^ 2) hθ hpθ]
    simp only [show 2 + 1 = 3 from rfl, inv_pow, div_eq_mul_inv]
    ring
  · change sourceMoment 1 (coverPull l P k (u ^ 2) qz) s -
        (1 / 2 : ℝ) * sourceMoment 2 (coverPull l P k (l * u ^ 2) g) s =
      l⁻¹ ^ 2 * u ^ 2 * (sourceMoment 1 qz (P s) - (1 / 2 : ℝ) * sourceMoment 2 g (P s))
    rw [sourceMoment_coverPull hl P k 1 (u ^ 2) hz hpz,
      sourceMoment_coverPull hl P k 2 (l * u ^ 2) hg hpg]
    field_simp; ring

omit [NormedAddCommGroup T] [NormedSpace ℝ T] in
theorem stateDebt_eq_sourceDebt (c : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S)) (n : ℕ) (s : S) :
    CorrectionState.debt c u n s =
      sourceDebt (u.gr c n)
        ((MeanIncrementBounds.thetaAxial c.base u.mean + u.covariance 2 1) n)
        ((MeanIncrementBounds.axialAxial c.base u.mean + u.covariance 2 2) n) s := rfl

end DebtTransport

section RankFamilies

variable {S T : Type}

/-- Naturality with slow-dependent length, velocity, amplitude and debt.
Only the primitive input data are transported. -/
theorem rankAngularFamily_transport {l u : ℝ} (hl : l ≠ 0) (hu : u ≠ 0)
    (P : S → T) (lam a b : ℝ) (ell U C : S → ℝ) (debt : S → MeanRankUpdate.Debt)
    (ell' U' C' : T → ℝ) (debt' : T → MeanRankUpdate.Debt)
    (hell : ∀ s, ell s ≠ 0) (hU : ∀ s, U s ≠ 0)
    (hlength : ∀ s, ell' (P s) = l * ell s) (hvelocity : ∀ s, U' (P s) = u * U s)
    (hcoefficient : ∀ s, C' (P s) = C s)
    (hdebt : ∀ s, debt' (P s) = MeanRankUpdate.scaleDebt l u (debt s))
    (r : ℝ) (s : S) :
    MeanRankUpdate.angularFamily lam a b ell' U' C' debt' (l * r, P s) =
      u * MeanRankUpdate.angularFamily lam a b ell U C debt (r, s) := by
  change MeanRankUpdate.angularIncrement lam (C' (P s)) a b (ell' (P s)) (U' (P s))
    (debt' (P s)) (l * r) =
      u * MeanRankUpdate.angularIncrement lam (C s) a b (ell s) (U s) (debt s) r
  rw [hlength, hvelocity, hcoefficient, hdebt]
  exact rankAngular_scale hl hu (hell s) (hU s) lam (C s) a b (debt s) r

theorem rankDesiredAxialFamily_transport {l u : ℝ} (hl : l ≠ 0) (hu : u ≠ 0)
    (P : S → T) (lam a b : ℝ) (ell U C : S → ℝ) (debt : S → MeanRankUpdate.Debt)
    (ell' U' C' : T → ℝ) (debt' : T → MeanRankUpdate.Debt)
    (hell : ∀ s, ell s ≠ 0) (hU : ∀ s, U s ≠ 0)
    (hlength : ∀ s, ell' (P s) = l * ell s) (hvelocity : ∀ s, U' (P s) = u * U s)
    (hcoefficient : ∀ s, C' (P s) = C s)
    (hdebt : ∀ s, debt' (P s) = MeanRankUpdate.scaleDebt l u (debt s))
    (r : ℝ) (s : S) :
    MeanRankUpdate.desiredAxialFamily lam a b ell' U' C' debt' (l * r, P s) =
      u * MeanRankUpdate.desiredAxialFamily lam a b ell U C debt (r, s) := by
  change MeanRankUpdate.desiredAxialIncrement lam (C' (P s)) a b (ell' (P s)) (U' (P s))
    (debt' (P s)) (l * r) =
      u * MeanRankUpdate.desiredAxialIncrement lam (C s) a b (ell s) (U s) (debt s) r
  rw [hlength, hvelocity, hcoefficient, hdebt]
  exact rankDesiredAxial_scale hl hu (hell s) (hU s) lam (C s) a b (debt s) r

end RankFamilies

section PhysicalProfile

open TorusInverse

/-- Slow projection, given by `(z.1, z.2.1)`. -/
noncomputable def slowProjection (z : PressureStream.Lift Plane) : SimilarityHomogeneity.ChartPoint
    :=
  (z.1, z.2.1)

theorem slowProjection_physicalToChart (h : ℝ) (n i : ℕ) (z : PressureStream.Lift Plane) :
    slowProjection (physicalToChart h n i z) =
      SimilarityHomogeneity.chartTransition h 1 (ChartScales.Q n) (slowProjection z) := by
  simp [slowProjection, physicalToChart_apply, SimilarityHomogeneity.chartTransition,
    chartScale, one_div, Real.inv_rpow (ChartScales.Q_pos n).le,
    Real.rpow_neg (ChartScales.Q_pos n).le]

theorem physicalProfile_inner {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (n i : ℕ) {z : PressureStream.Lift Plane} (hz : 0 < z.2.1.2) :
    SimilarityHomogeneity.chartInner h (slowProjection (physicalToChart h n i z)) =
      SimilarityHomogeneity.chartInner h (slowProjection z) := by
  rw [slowProjection_physicalToChart]
  exact SimilarityHomogeneity.chartInner_transition hh hh1 zero_lt_one (ChartScales.Q_pos n) hz

/-- Every function of the true profile coordinates `(X,η)` is invariant,
including the radial profile weight and its logarithmic edge distance. -/
theorem physicalProfile_weight {V : Type} {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (n i : ℕ) {z : PressureStream.Lift Plane} (hz : 0 < z.2.1.2) (w : ℝ × ℝ → V) :
    w (SimilarityHomogeneity.chartInner h (slowProjection (physicalToChart h n i z))) =
      w (SimilarityHomogeneity.chartInner h (slowProjection z)) :=
  congrArg w (physicalProfile_inner hh hh1 n i hz)

/-- The slow similarity length itself scales; it is not a fixed radial
endpoint shared by all normalized band charts. -/
theorem physicalProfile_q {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (n i : ℕ) {z : PressureStream.Lift Plane} (hz : 0 < z.2.1.2) :
    SimilarityHomogeneity.chartQ h (slowProjection (physicalToChart h n i z)) =
      (ChartScales.Q n)⁻¹ * SimilarityHomogeneity.chartQ h (slowProjection z) := by
  rw [slowProjection_physicalToChart]
  simpa only [one_div] using
    SimilarityHomogeneity.chartQ_transition hh hh1 zero_lt_one (ChartScales.Q_pos n) hz

end PhysicalProfile

end

end NavierStokes.MeanChartCompatibility
