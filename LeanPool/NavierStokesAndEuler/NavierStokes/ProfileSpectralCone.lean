/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ModulatedProfileAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryRepresentatives
public import LeanPool.NavierStokesAndEuler.NavierStokes.LeadingStress
public import LeanPool.NavierStokesAndEuler.NavierStokes.BaseChartJets

@[expose] public section

/-!
# From the actual profile cone to the primary spectral cone

The signed axial shear in the profile cone is `c = -2 X U_X / E`.
Consequently the physical shear vector is `F * (-a,-c)`, while the
leading stress is a positive multiple of `(p₁-a,p₂-c)`.  The results
below derive the primary spectral and target cones from these identities.
-/

noncomputable section

namespace NavierStokes.ProfileSpectralCone

open Set Function Filter
open scoped ContDiff Topology InnerProductSpace


abbrev Plane := MovingFrameODE.Plane
abbrev Slow := PhaseCalculus.Slow

private theorem shear_size_mul {a c : ℝ} (ha : a ≠ 0) :
    a * (a * (1 + (c / a) ^ 2)) = a ^ 2 + c ^ 2 := by
  field_simp

theorem referenceCone_of_trueCone {F p₁ p₂ a c : ℝ} (hF : 0 < F)
    (h : TrueConeLoop.InTrueCone p₁ p₂ a c) :
    PrimaryRepresentatives.ReferenceCone F (F • !₂[-a, -c]) := by
  apply PrimaryRepresentatives.referenceCone_of_shear_coordinates hF h.1
  have he := shear_size_mul (c := c) h.1.ne'
  have hm := mul_lt_mul_of_pos_left h.2.1 h.1
  nlinarith

/-- The square of the actual unstable eigenvector slope. -/
theorem c0_sq_signedShear {F a c : ℝ} (hF : 0 < F) (ha : 0 < a)
    (hv : 2 < a * (1 + (c / a) ^ 2)) :
    PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) ^ 2 = (a * (1 + (c / a) ^ 2) - 2) / 2 := by
  have ho : 2 * a < a ^ 2 + (-c) ^ 2 := by
    have he := shear_size_mul (c := c) ha.ne'
    have hm := mul_lt_mul_of_pos_left hv ha
    nlinarith
  have hr := PrimaryRepresentatives.referenceCone_of_shear_coordinates hF ha ho
  have hn0 : ‖F • !₂[-a, -c]‖ ≠ 0 := norm_ne_zero_iff.mpr hr.shear_ne_zero
  have hn : ‖F • !₂[-a, -c]‖ ^ 2 = F ^ 2 * (a ^ 2 + c ^ 2) := by
    have hh := ViscousPropagator.plane_norm_sq (F • !₂[-a, -c])
    change ‖F • !₂[-a, -c]‖ ^ 2 = (F * -a) ^ 2 + (F * -c) ^ 2 at hh
    rw [hh]
    ring
  have he : PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) ^ 2 =
      -(PrimaryRepresentatives.coupling F (F • !₂[-a, -c]) + ‖F • !₂[-a, -c]‖) /
        PrimaryRepresentatives.coupling F (F • !₂[-a, -c]) := by
    rw [PrimaryRepresentatives.c0, div_pow, hr.lambda0_sq]
    field_simp [hr.coupling_neg.ne]
  rw [he, PrimaryRepresentatives.coupling_eq]
  change -((2 * F * (F * -a)) / ‖F • !₂[-a, -c]‖ + ‖F • !₂[-a, -c]‖) /
      ((2 * F * (F * -a)) / ‖F • !₂[-a, -c]‖) = _
  field_simp [hF.ne', ha.ne', hn0]
  nlinarith [hn]

/-- Projection of the actual stress coordinates onto the normal. -/
theorem stress_inner_normal (F τ p₁ p₂ a c : ℝ) (ha : a ≠ 0) :
    ⟪τ • !₂[p₁ - a, p₂ - c], PrimaryRepresentatives.normalDirection (F • !₂[-a, -c])⟫_ℝ =
      -(τ * F * a / ‖F • !₂[-a, -c]‖) *
        (p₁ + p₂ * (c / a) - a * (1 + (c / a) ^ 2)) := by
  have he : a * (p₁ + p₂ * (c / a) - a * (1 + (c / a) ^ 2)) =
      a * p₁ + c * p₂ - a ^ 2 - c ^ 2 := by
    field_simp ; ring
  calc
    _ = -(τ * F / ‖F • !₂[-a, -c]‖) *
        (a * p₁ + c * p₂ - a ^ 2 - c ^ 2) := by
      simp [PrimaryRepresentatives.normalDirection, PiLp.inner_apply, Fin.sum_univ_two]
      ring
    _ = _ := by rw [← he]; ring

/-- Projection onto the fixed transverse orientation `-quarterTurn N`. -/
theorem stress_inner_transverse (F τ p₁ p₂ a c : ℝ) (ha : a ≠ 0) :
    ⟪τ • !₂[p₁ - a, p₂ - c], PrimaryRepresentatives.transverseDirection (F • !₂[-a, -c])⟫_ℝ =
      (τ * F * a / ‖F • !₂[-a, -c]‖) * (p₂ - p₁ * (c / a)) := by
  have he : a * (p₂ - p₁ * (c / a)) = a * p₂ - c * p₁ := by
    field_simp
  calc
    _ = (τ * F / ‖F • !₂[-a, -c]‖) * (a * p₂ - c * p₁) := by
      simp [PrimaryRepresentatives.transverseDirection, PrimaryRepresentatives.normalDirection,
        MovingFrameODE.quarterTurn, PiLp.inner_apply, Fin.sum_univ_two]
      ring
    _ = _ := by rw [← he]; ring

private theorem cancel_signed_scale (q k j d : ℝ) (hk : k ≠ 0) :
    q * (k * j) / (-k * d) = -(q * j / d) := by
  rw [neg_mul, div_neg]
  congr 1
  calc
    q * (k * j) / (k * d) = k * (q * j) / (k * d) := by ring
    _ = _ := mul_div_mul_left _ _ hk

/-- The true profile cone implies both primary cones, without assuming
an eigenvector or target-cone inequality. -/
theorem spectral_cones_of_trueCone {F τ p₁ p₂ a c : ℝ} (hF : 0 < F) (hτ : 0 < τ)
    (h : TrueConeLoop.InTrueCone p₁ p₂ a c) :
    PrimaryRepresentatives.ReferenceCone F (F • !₂[-a, -c]) ∧
      PrimaryRepresentatives.TargetCone F (F • !₂[-a, -c]) (τ • !₂[p₁ - a, p₂ - c]) := by
  have hr := referenceCone_of_trueCone hF h
  have hq := (ConeAlgebra.true_cone_iff h.2.1).mp h.2.2
  have hn := norm_pos_iff.mpr hr.shear_ne_zero
  have hk : 0 < τ * F * a / ‖F • !₂[-a, -c]‖ :=
    div_pos (mul_pos (mul_pos hτ hF) h.1) hn
  have hd : 0 < p₁ + p₂ * (c / a) - a * (1 + (c / a) ^ 2) := sub_pos.mpr hq.1
  have hc := c0_sq_signedShear hF h.1 h.2.1
  have hsq : (PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) * (p₂ - p₁ * (c / a))) ^ 2 <
      (p₁ + p₂ * (c / a) - a * (1 + (c / a) ^ 2)) ^ 2 := by
    rw [mul_pow, hc]
    nlinarith [hq.2]
  have habs : |PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) * (p₂ - p₁ * (c / a))| <
      p₁ + p₂ * (c / a) - a * (1 + (c / a) ^ 2) := by
    nlinarith [sq_abs (PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) * (p₂ - p₁ * (c / a))),
      abs_nonneg (PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) * (p₂ - p₁ * (c / a)))]
  refine ⟨hr, ⟨?_, ?_⟩⟩
  · rw [stress_inner_normal F τ p₁ p₂ a c h.1.ne']
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hk) hd
  · rw [PrimaryRepresentatives.targetRatio, stress_inner_normal F τ p₁ p₂ a c h.1.ne',
      stress_inner_transverse F τ p₁ p₂ a c h.1.ne']
    rw [cancel_signed_scale _ _ _ _ hk.ne', abs_neg, abs_div, abs_of_pos hd]
    exact (div_lt_one hd).mpr habs

theorem stress_coordinates_ne_zero {p₁ p₂ a c : ℝ}
    (h : TrueConeLoop.InTrueCone p₁ p₂ a c) : (!₂[p₁ - a, p₂ - c] : Plane) ≠ 0 := by
  have ht := (spectral_cones_of_trueCone (F := 1) (τ := 1) (by norm_num) (by norm_num) h).2
  intro hz
  simpa only [one_smul, hz, inner_zero_left, lt_self_iff_false] using ht.inward

/-- A scalar criterion for any direction, including a nonzero smooth
edge factor when the actual stress itself vanishes. -/
theorem targetCone_of_signedShear {F a c : ℝ} (hF : 0 < F) (ha : 0 < a)
    (hv : 2 < a * (1 + (c / a) ^ 2)) (T : Plane)
    (hin : 0 < a * T 0 + c * T 1)
    (hquad : (a * (1 + (c / a) ^ 2) - 2) * (a * T 1 - c * T 0) ^ 2 <
      2 * (a * T 0 + c * T 1) ^ 2) :
    PrimaryRepresentatives.TargetCone F (F • !₂[-a, -c]) T := by
  have ho : 2 * a < a ^ 2 + (-c) ^ 2 := by
    have he := shear_size_mul (c := c) ha.ne'
    have hm := mul_lt_mul_of_pos_left hv ha
    nlinarith
  have hr := PrimaryRepresentatives.referenceCone_of_shear_coordinates hF ha ho
  have hk : 0 < F / ‖F • !₂[-a, -c]‖ :=
    div_pos hF (norm_pos_iff.mpr hr.shear_ne_zero)
  have hN : ⟪T, PrimaryRepresentatives.normalDirection (F • !₂[-a, -c])⟫_ℝ =
      -(F / ‖F • !₂[-a, -c]‖) * (a * T 0 + c * T 1) := by
    simp [PrimaryRepresentatives.normalDirection, PiLp.inner_apply, Fin.sum_univ_two]
    ring
  have hK : ⟪T, PrimaryRepresentatives.transverseDirection (F • !₂[-a, -c])⟫_ℝ =
      (F / ‖F • !₂[-a, -c]‖) * (a * T 1 - c * T 0) := by
    simp [PrimaryRepresentatives.transverseDirection, PrimaryRepresentatives.normalDirection,
      MovingFrameODE.quarterTurn, PiLp.inner_apply, Fin.sum_univ_two]
    ring
  have hsq : (PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) * (a * T 1 - c * T 0)) ^ 2 <
      (a * T 0 + c * T 1) ^ 2 := by
    rw [mul_pow, c0_sq_signedShear hF ha hv]
    nlinarith only [hquad]
  have habs : |PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) * (a * T 1 - c * T 0)| <
      a * T 0 + c * T 1 := by
    nlinarith [sq_abs (PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) * (a * T 1 - c * T 0)),
      abs_nonneg (PrimaryRepresentatives.c0 F (F • !₂[-a, -c]) * (a * T 1 - c * T 0))]
  constructor
  · rw [hN]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hk) hin
  · rw [PrimaryRepresentatives.targetRatio, hN, hK,
      cancel_signed_scale _ _ _ _ hk.ne', abs_neg, abs_div, abs_of_pos hin]
    exact (div_lt_one hin).mpr habs

/-- The edge-collar convention uses the target tilt `T₁ / T₀` and the
signed shear tilt `c / a`. Its two strict scalar margins imply the
primary target cone. -/
theorem targetCone_of_tilt {F a c : ℝ} (hF : 0 < F) (ha : 0 < a)
    (hv : 2 < a * (1 + (c / a) ^ 2)) (T : Plane) (hT : 0 < T 0)
    (hin : 0 < 1 + (c / a) * (T 1 / T 0))
    (hgap : 0 < 2 * (1 + (c / a) * (T 1 / T 0)) ^ 2 -
      (a * (1 + (c / a) ^ 2) - 2) * (T 1 / T 0 - c / a) ^ 2) :
    PrimaryRepresentatives.TargetCone F (F • !₂[-a, -c]) T := by
  have hi : a * T 0 + c * T 1 = a * T 0 * (1 + (c / a) * (T 1 / T 0)) := by
    field_simp [ha.ne', hT.ne']
  have ht : a * T 1 - c * T 0 = a * T 0 * (T 1 / T 0 - c / a) := by
    field_simp [ha.ne', hT.ne']
  apply targetCone_of_signedShear hF ha hv T
  · rw [hi]
    exact mul_pos (mul_pos ha hT) hin
  · rw [hi, ht]
    have hm := mul_pos (sq_pos_of_pos (mul_pos ha hT)) hgap
    nlinarith only [hm]

/-! ## The actual profile histories and stresses -/

open ProfileHistories

/-- The two actual leading stress coefficients, in the Euclidean plane
used by the primary ODE. -/
noncomputable def stressVector {D : RadialDomain} (P : Profiles D) (h : ℝ)
    (p : Point) : Plane := !₂[LeadingStress.theta P h p, LeadingStress.axial P h p]

/-- Both entries use the actual integral-history stocks; the axial sign
agrees with the modulation convention. -/
theorem stressVector_eq_stocks {D : RadialDomain} (P : Profiles D) (h : ℝ) {p : Point}
    (hp : p ∈ D.carrier) (hX : 0 < p.1) (hf : P.f p ≠ 0) :
    stressVector P h p = P.f p •
      !₂[ActivationStocks.profileStockOne P h p - ModulatedCone.angularShear P.E p,
        ActivationStocks.profileStockTwo P h p - ModulatedCone.signedAxialShear P.E P.U p] := by
  have hs := NominalConeAssembly.modulated_shears_eq P hp hX hf
  ext i
  fin_cases i
  · change LeadingStress.theta P h p = P.f p * _
    rw [LeadingStress.theta_eq_lag_minus_slope P h hf, hs.1]
    rfl
  · change LeadingStress.axial P h p = P.f p * _
    rw [LeadingStress.axial_eq_lag_plus_slope P h hX hf, hs.2]
    unfold ActivationStocks.profileStockTwo LeadingStress.slopeB ActivationContinuation.shearB
    change P.f p * (p.1 * P.axialLag h p / (CoordinateAlgebra.L h p.2 * P.E p) +
      2 * p.1 * radialPartial P.U p / P.E p) =
      P.f p * (p.1 * P.axialLag h p / (CoordinateAlgebra.L h p.2 * P.E p) -
        -2 * p.1 * radialPartial P.U p / P.E p)
    ring

/-- The actual leading stress belongs to the primary target cone whenever
the actual five-history profile has the true cone. -/
theorem profile_spectral_cones {D : RadialDomain} (P : Profiles D) (h : ℝ) {p : Point}
    (hp : p ∈ D.carrier) (hX : 0 < p.1) (hf : 0 < P.f p) {F : ℝ} (hF : 0 < F)
    (hc : TrueConeLoop.InTrueCone (ActivationStocks.profileStockOne P h p)
      (ActivationStocks.profileStockTwo P h p) (ModulatedCone.angularShear P.E p)
      (ModulatedCone.signedAxialShear P.E P.U p)) :
    PrimaryRepresentatives.ReferenceCone F
        (F • !₂[-ModulatedCone.angularShear P.E p, -ModulatedCone.signedAxialShear P.E P.U p]) ∧
      PrimaryRepresentatives.TargetCone F
        (F • !₂[-ModulatedCone.angularShear P.E p, -ModulatedCone.signedAxialShear P.E P.U p])
        (stressVector P h p) := by
  rw [stressVector_eq_stocks P h hp hX hf.ne']
  exact spectral_cones_of_trueCone hF hf hc

theorem profile_stress_ne_zero {D : RadialDomain} (P : Profiles D) (h : ℝ) {p : Point}
    (hp : p ∈ D.carrier) (hX : 0 < p.1) (hf : 0 < P.f p)
    (hc : TrueConeLoop.InTrueCone (ActivationStocks.profileStockOne P h p)
      (ActivationStocks.profileStockTwo P h p) (ModulatedCone.angularShear P.E p)
      (ModulatedCone.signedAxialShear P.E P.U p)) : stressVector P h p ≠ 0 := by
  have ht := (profile_spectral_cones P h hp hX hf (F := 1) (by norm_num) hc).2
  intro hz
  simpa only [hz, inner_zero_left, lt_self_iff_false] using ht.inward

/-! ## Genuine radial derivatives of the normalized leading fields -/

theorem normalizedCoordinates_radial (h : ℝ) (p : Slow) (R : ℝ) :
    BaseChartJets.normalizedCoordinates h (R, p.2) =
      ((BaseChartJets.normalizedCoordinates h p).1,
        ((R ^ 2 / 2) / (BaseChartJets.normalizedCoordinates h p).1,
          (BaseChartJets.normalizedCoordinates h p).2.2)) := by
  simp only [BaseChartJets.normalizedCoordinates_eq, SimilarityHomogeneity.chartQ,
    SimilarityHomogeneity.chartX, SimilarityHomogeneity.chartEta,
    SimilarityCoordinates.coordinateX]

private theorem slowR_hasDerivAt {f : Slow → ℝ} {p : Slow}
    (hf : DifferentiableAt ℝ f p) :
    HasDerivAt (fun R => f (R, p.2)) (PhaseCalculus.slowR f p) p.1 :=
  hf.hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))

private theorem radial_composition_hasDerivAt {f : Point → ℝ} {rho eta R : ℝ}
    (hf : DifferentiableAt ℝ f ((R ^ 2 / 2) / rho, eta)) :
    HasDerivAt (fun r => f ((r ^ 2 / 2) / rho, eta))
      (R / rho * SimilarityProfile.partialX f ((R ^ 2 / 2) / rho, eta)) R := by
  have hx : HasDerivAt (fun r : ℝ => (r ^ 2 / 2) / rho) (R / rho) R := by
    convert! (((hasDerivAt_id R).pow 2).div_const 2).div_const rho using 1
    simp
  convert! (LeadingStress.partialX_hasDerivAt hf).comp R hx using 1
  ring

theorem leadingFrequency_germ {h C : ℝ} {d : SlowBorelBase.Coefficients}
    (hh : 0 < h) (hh1 : h < 1 / 2) {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    BaseChartJets.leadingFrequency h C d =ᶠ[𝓝 p]
      (fun q => (BaseChartJets.normalizedCoordinates h q).1 ^ (-CoordinateAlgebra.A h - 1 / 2) / C *
        d.phi 0 (BaseChartJets.normalizedCoordinates h q).2) := by
  filter_upwards [continuous_fst.continuousAt.eventually (Ioi_mem_nhds hR),
    continuous_snd.snd.continuousAt.eventually (Ioi_mem_nhds hT)] with q hqR hqT
  exact BaseChartJets.leadingFrequency_eq hh hh1 hqT hqR

theorem leadingFrequency_smoothAt {h C : ℝ} {d : SlowBorelBase.Coefficients}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    ContDiffAt ℝ ∞ (BaseChartJets.leadingFrequency h C d) p := by
  have hs := BaseChartJets.normalizedCoordinates_smoothAt hh hh1 hT
  have hn := BaseChartJets.normalizedCoordinates_q_pos hh hh1 hT
  exact (((hs.fst.rpow_const_of_ne hn.ne').div_const C).mul
    ((hd.phi 0).contDiffAt.comp p hs.snd)).congr_of_eventuallyEq
      (leadingFrequency_germ hh hh1 hT hR)

theorem leadingAxial_smoothAt {h : ℝ} {d : SlowBorelBase.Coefficients}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) :
    ContDiffAt ℝ ∞ (BaseChartJets.leadingAxial h d) p := by
  have hs := BaseChartJets.normalizedCoordinates_smoothAt hh hh1 hT
  have hn := BaseChartJets.normalizedCoordinates_q_pos hh hh1 hT
  exact (hs.fst.rpow_const_of_ne hn.ne').mul ((hd.axial 0).contDiffAt.comp p hs.snd)

/-- This is the Fréchet radial derivative of the actual leading angular
frequency, with all chart scale factors retained. -/
theorem leadingFrequency_slowR {h C : ℝ} {d : SlowBorelBase.Coefficients}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    PhaseCalculus.slowR (BaseChartJets.leadingFrequency h C d) p =
      (BaseChartJets.normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h - 1 / 2) / C *
        (p.1 / (BaseChartJets.normalizedCoordinates h p).1 *
          SimilarityProfile.partialX (d.phi 0) (BaseChartJets.normalizedCoordinates h p).2) := by
  have hp := congrArg Prod.snd (normalizedCoordinates_radial h p p.1)
  change (BaseChartJets.normalizedCoordinates h p).2 =
    ((p.1 ^ 2 / 2) / (BaseChartJets.normalizedCoordinates h p).1,
      (BaseChartJets.normalizedCoordinates h p).2.2) at hp
  have hf := (hd.phi 0).differentiable (by simp) (BaseChartJets.normalizedCoordinates h p).2
  rw [hp] at hf
  have hr := (radial_composition_hasDerivAt hf).const_mul
    ((BaseChartJets.normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h - 1 / 2) / C)
  have he : (fun R => BaseChartJets.leadingFrequency h C d (R, p.2)) =ᶠ[𝓝 p.1]
      (fun R => (BaseChartJets.normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h - 1 / 2) / C *
        d.phi 0 ((R ^ 2 / 2) / (BaseChartJets.normalizedCoordinates h p).1,
          (BaseChartJets.normalizedCoordinates h p).2.2)) := by
    filter_upwards [Ioi_mem_nhds hR] with R hRp
    rw [BaseChartJets.leadingFrequency_eq (p := (R, p.2)) hh hh1 hT hRp,
      normalizedCoordinates_radial]
  rw [← hp] at hr
  exact (slowR_hasDerivAt ((leadingFrequency_smoothAt hh hh1 hd hT hR).differentiableAt
    (by simp))).unique (hr.congr_of_eventuallyEq he)

theorem leadingAxial_slowR {h : ℝ} {d : SlowBorelBase.Coefficients}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) :
    PhaseCalculus.slowR (BaseChartJets.leadingAxial h d) p =
      (BaseChartJets.normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h) *
        (p.1 / (BaseChartJets.normalizedCoordinates h p).1 *
          SimilarityProfile.partialX (d.axial 0) (BaseChartJets.normalizedCoordinates h p).2) := by
  have hp := congrArg Prod.snd (normalizedCoordinates_radial h p p.1)
  change (BaseChartJets.normalizedCoordinates h p).2 =
    ((p.1 ^ 2 / 2) / (BaseChartJets.normalizedCoordinates h p).1,
      (BaseChartJets.normalizedCoordinates h p).2.2) at hp
  have hf := (hd.axial 0).differentiable (by simp) (BaseChartJets.normalizedCoordinates h p).2
  rw [hp] at hf
  have hr := (radial_composition_hasDerivAt hf).const_mul
    ((BaseChartJets.normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h))
  have he : (fun R => BaseChartJets.leadingAxial h d (R, p.2)) =
      (fun R => (BaseChartJets.normalizedCoordinates h p).1 ^ (-CoordinateAlgebra.A h) *
        d.axial 0 ((R ^ 2 / 2) / (BaseChartJets.normalizedCoordinates h p).1,
          (BaseChartJets.normalizedCoordinates h p).2.2)) := by
    funext R
    simp only [BaseChartJets.leadingAxial, BaseChartJets.axialFactor, normalizedCoordinates_radial]
  rw [← hp] at hr
  rw [← he] at hr
  exact (slowR_hasDerivAt ((leadingAxial_smoothAt hh hh1 hd hT).differentiableAt
    (by simp))).unique hr

theorem normalized_X_eq (h : ℝ) (p : Slow) :
    (BaseChartJets.normalizedCoordinates h p).2.1 =
      p.1 ^ 2 / (2 * (BaseChartJets.normalizedCoordinates h p).1) := by
  rw [BaseChartJets.normalizedCoordinates_eq]
  unfold SimilarityHomogeneity.chartX SimilarityCoordinates.coordinateX
    SimilarityHomogeneity.chartQ
  ring

theorem normalized_X_pos {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1) :
    0 < (BaseChartJets.normalizedCoordinates h p).2.1 := by
  rw [normalized_X_eq]
  exact div_pos (sq_pos_of_pos hR)
    (mul_pos (by norm_num) (BaseChartJets.normalizedCoordinates_q_pos hh hh1 hT))

/-- Value and radial-germ agreement with a profile suffice to identify the
genuine shear vector of the coefficient-defined leading fields. -/
theorem leading_shear_eq_profile {D : RadialDomain} (P : Profiles D)
    {h C : ℝ} {d : SlowBorelBase.Coefficients}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hC : C ≠ 0) (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) (hR : 0 < p.1)
    (hp : (BaseChartJets.normalizedCoordinates h p).2 ∈ D.carrier)
    (hf : P.f (BaseChartJets.normalizedCoordinates h p).2 ≠ 0)
    (hphi : (fun X => d.phi 0 (X, (BaseChartJets.normalizedCoordinates h p).2.2)) =ᶠ[
      𝓝 (BaseChartJets.normalizedCoordinates h p).2.1]
      (fun X => C * P.f (X, (BaseChartJets.normalizedCoordinates h p).2.2)))
    (hU : (fun X => d.axial 0 (X, (BaseChartJets.normalizedCoordinates h p).2.2)) =ᶠ[
      𝓝 (BaseChartJets.normalizedCoordinates h p).2.1]
      (fun X => P.U (X, (BaseChartJets.normalizedCoordinates h p).2.2))) :
    PhaseEstimates.shearVector (BaseChartJets.leadingFrequency h C d) (BaseChartJets.leadingAxial h
      d) p =
      BaseChartJets.leadingFrequency h C d p •
        !₂[-ModulatedCone.angularShear P.E (BaseChartJets.normalizedCoordinates h p).2,
          -ModulatedCone.signedAxialShear P.E P.U (BaseChartJets.normalizedCoordinates h p).2] := by
  let w := (BaseChartJets.normalizedCoordinates h p).2
  let rho := (BaseChartJets.normalizedCoordinates h p).1
  have hrho : 0 < rho := BaseChartJets.normalizedCoordinates_q_pos hh hh1 hT
  have hX : 0 < w.1 := normalized_X_pos hh hh1 hT hR
  have hphi0 : d.phi 0 w = C * P.f w := hphi.eq_of_nhds
  have hfx := LeadingStress.partialX_hasDerivAt
    ((P.f_smooth.contDiffAt (D.isOpen.mem_nhds hp)).differentiableAt (by simp))
  have hux := LeadingStress.partialX_hasDerivAt
    ((P.U_smooth.contDiffAt (D.isOpen.mem_nhds hp)).differentiableAt (by simp))
  have hphiX : SimilarityProfile.partialX (d.phi 0) w = C * SimilarityProfile.partialX P.f w :=
    (LeadingStress.partialX_hasDerivAt ((hd.phi 0).differentiable (by simp) w)).unique
      ((hfx.const_mul C).congr_of_eventuallyEq hphi)
  have hUX : SimilarityProfile.partialX (d.axial 0) w = SimilarityProfile.partialX P.U w :=
    (LeadingStress.partialX_hasDerivAt ((hd.axial 0).differentiable (by simp) w)).unique
      (hux.congr_of_eventuallyEq hU)
  have hF : BaseChartJets.leadingFrequency h C d p =
      rho ^ (-CoordinateAlgebra.A h - 1 / 2) * P.f w := by
    rw [BaseChartJets.leadingFrequency_eq hh hh1 hT hR, hphi0]
    dsimp only [rho]
    field_simp
  have hFX : PhaseCalculus.slowR (BaseChartJets.leadingFrequency h C d) p =
      rho ^ (-CoordinateAlgebra.A h - 1 / 2) * (p.1 / rho * SimilarityProfile.partialX P.f w) := by
    rw [leadingFrequency_slowR hh hh1 hd hT hR, hphiX]
    dsimp only [rho]
    field_simp
  have hGX : PhaseCalculus.slowR (BaseChartJets.leadingAxial h d) p =
      rho ^ (-CoordinateAlgebra.A h) * (p.1 / rho * SimilarityProfile.partialX P.U w) := by
    rw [leadingAxial_slowR hh hh1 hd hT, hUX]
  have hw : w.1 = p.1 ^ 2 / (2 * rho) := normalized_X_eq h p
  have hsqrt : Real.sqrt (2 * w.1) = p.1 / Real.sqrt rho := by
    have he : 2 * w.1 = p.1 ^ 2 / rho := by rw [hw]; ring
    rw [he, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hR.le]
  have hpow : rho ^ (-CoordinateAlgebra.A h - 1 / 2) =
      rho ^ (-CoordinateAlgebra.A h) / Real.sqrt rho := by
    rw [Real.rpow_sub hrho, Real.sqrt_eq_rpow]
  have hs := NominalConeAssembly.modulated_shears_eq P hp hX hf
  rw [hs.1, hs.2]
  ext i
  fin_cases i
  · change p.1 * PhaseCalculus.slowR (BaseChartJets.leadingFrequency h C d) p =
      BaseChartJets.leadingFrequency h C d p * (-ActivationContinuation.shearA P w)
    rw [hFX, hF]
    unfold ActivationContinuation.shearA
    change p.1 * (rho ^ (-CoordinateAlgebra.A h - 1 / 2) * (p.1 / rho * radialPartial P.f w)) =
      rho ^ (-CoordinateAlgebra.A h - 1 / 2) * P.f w * (-(-2 * w.1 * radialPartial P.f w / P.f w))
    rw [hw]
    field_simp [show P.f w ≠ 0 from hf, hrho.ne']
  · change PhaseCalculus.slowR (BaseChartJets.leadingAxial h d) p =
      BaseChartJets.leadingFrequency h C d p * (-ActivationContinuation.shearB P w)
    rw [hGX, hF]
    unfold ActivationContinuation.shearB Profiles.E
    change rho ^ (-CoordinateAlgebra.A h) * (p.1 / rho * radialPartial P.U w) =
      rho ^ (-CoordinateAlgebra.A h - 1 / 2) * P.f w *
        (-(-2 * w.1 * radialPartial P.U w / (Real.sqrt (2 * w.1) * P.f w)))
    rw [hpow, hsqrt, hw]
    field_simp [show P.f w ≠ 0 from hf, hrho.ne', hR.ne', (Real.sqrt_pos.mpr hrho).ne']

/-! ## Uniform choices on a compact reference set -/

theorem signedShear_continuousOn {K : Set Slow} {F a c : Slow → ℝ}
    (hF : ContinuousOn F K) (ha : ContinuousOn a K) (hc : ContinuousOn c K) :
    ContinuousOn (fun p => F p • !₂[-a p, -c p]) K := by
  apply hF.smul
  apply (PiLp.continuous_toLp 2 _).comp_continuousOn
  change ContinuousOn (fun p => (![-a p, -c p] : Fin 2 → ℝ)) K
  apply continuousOn_pi.mpr
  intro i
  fin_cases i
  · exact ha.neg
  · exact hc.neg

/-- Scalar shear and direction margins on a compact set produce all
reference bounds and one mixed-point target margin. All constants are
chosen before a band or label is selected. `T` can be an extended edge
direction: no positive lower bound for a separate amplitude is used. -/
theorem compact_signedShear_bounds {K : Set Slow} (hK : IsCompact K)
    {F a c : Slow → ℝ} {T : Slow → Plane}
    (hF : ContinuousOn F K) (ha : ContinuousOn a K) (hc : ContinuousOn c K)
    (hT : ContinuousOn T K) (hR : ∀ p ∈ K, 0 < p.1)
    (hFp : ∀ p ∈ K, 0 < F p) (hap : ∀ p ∈ K, 0 < a p)
    (hv : ∀ p ∈ K, 2 < a p * (1 + (c p / a p) ^ 2))
    (hin : ∀ p ∈ K, 0 < a p * T p 0 + c p * T p 1)
    (hquad : ∀ p ∈ K, (a p * (1 + (c p / a p) ^ 2) - 2) *
      (a p * T p 1 - c p * T p 0) ^ 2 < 2 * (a p * T p 0 + c p * T p 1) ^ 2) :
    ∃ M u eta delta : ℝ, 1 ≤ M ∧ 0 < u ∧ 0 < eta ∧ 0 < delta ∧
      (∀ p ∈ K, PrimaryRepresentatives.ReferenceCone (F p) (F p • !₂[-a p, -c p]) ∧
        PrimaryRepresentatives.TargetCone (F p) (F p • !₂[-a p, -c p]) (T p) ∧
        PrimaryRepresentatives.ParameterBounds M p.1 (F p) (F p • !₂[-a p, -c p])) ∧
      ∀ p₀ ∈ K, ∀ p ∈ K, dist p p₀ < delta →
        ⟪T p, PrimaryRepresentatives.normalDirection (F p₀ • !₂[-a p₀, -c p₀])⟫_ℝ ≤ -eta ∧
        |PrimaryRepresentatives.c0 (F p₀) (F p₀ • !₂[-a p₀, -c p₀]) *
          ⟪T p, PrimaryRepresentatives.transverseDirection (F p₀ • !₂[-a p₀, -c p₀])⟫_ℝ /
          ⟪T p, PrimaryRepresentatives.normalDirection (F p₀ • !₂[-a p₀, -c p₀])⟫_ℝ| + eta ≤
          PrimaryRepresentatives.slopeRatio u := by
  have hRef : ∀ p ∈ K, PrimaryRepresentatives.ReferenceCone (F p) (F p • !₂[-a p, -c p]) := by
    intro p hp
    apply PrimaryRepresentatives.referenceCone_of_shear_coordinates (hFp p hp) (hap p hp)
    have he := shear_size_mul (c := c p) (hap p hp).ne'
    have hm := mul_lt_mul_of_pos_left (hv p hp) (hap p hp)
    nlinarith
  have hTar : ∀ p ∈ K, PrimaryRepresentatives.TargetCone (F p) (F p • !₂[-a p, -c p]) (T p) :=
    fun p hp => targetCone_of_signedShear (hFp p hp) (hap p hp) (hv p hp) (T p)
      (hin p hp) (hquad p hp)
  have hg := signedShear_continuousOn hF ha hc
  obtain ⟨M, hM, hMb⟩ := PrimaryRepresentatives.compact_parameter_bounds hK hF hg hR hRef
  obtain ⟨u, eta, delta, hu, he, hd, hb⟩ :=
    PrimaryRepresentatives.compact_mixed_target_margin hK hF hg hT hRef hTar
  exact ⟨M, u, eta, delta, hM, hu, he, hd,
    fun p hp => ⟨hRef p hp, hTar p hp, hMb p hp⟩, hb⟩

/-- A vanishing nonnegative amplitude preserves the linear inward
margin; where it is positive it cancels exactly from the target ratio. -/
theorem weighted_target_margin {F eta u zeta : ℝ} {g T : Plane}
    (hz : 0 ≤ zeta)
    (hin : ⟪T, PrimaryRepresentatives.normalDirection g⟫_ℝ ≤ -eta)
    (hratio : PrimaryRepresentatives.targetRatio F g T + eta ≤ PrimaryRepresentatives.slopeRatio u)
      :
    ⟪zeta • T, PrimaryRepresentatives.normalDirection g⟫_ℝ ≤ -eta * zeta ∧
      (0 < zeta → PrimaryRepresentatives.targetRatio F g (zeta • T) + eta ≤
        PrimaryRepresentatives.slopeRatio u) := by
  constructor
  · rw [real_inner_smul_left]
    simpa only [mul_comm zeta (-eta)] using mul_le_mul_of_nonneg_left hin hz
  · intro hz'
    rw [PrimaryRepresentatives.targetRatio_smul F g T hz'.ne']
    exact hratio

end NavierStokes.ProfileSpectralCone
