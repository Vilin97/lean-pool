/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.StateMomentBalances
public import LeanPool.NavierStokesAndEuler.NavierStokes.VariableGaugeMean

/-!
# Measured moment balances in the actual moving pressure gauge

The pressure coefficient is the measured second moment of the normalized
physical density. It varies with the true similarity coordinate. All moment
identities below use the actual state residual and the actual pressure recipe.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.GaugeMomentBalances

open Set Filter Function MeasureTheory
open CorrectionState
open scoped ContDiff Topology BigOperators Interval

/-- Plane: an abbreviation for `PressureStream.Plane`. -/
abbrev Plane := PressureStream.Plane
/-- Point: an abbreviation for `PressureStream.Lift Plane`. -/
abbrev Point := PressureStream.Lift Plane

/-- Base pressure coefficient, given by `IntegratedMeanBalances.moment 2 (PressureStream.rho a b
hab) / 2`. -/
noncomputable def basePressureCoefficient (a b : ℝ) (hab : a < b) : ℝ :=
  IntegratedMeanBalances.moment 2 (PressureStream.rho a b hab) / 2

theorem basePressureCoefficient_lower {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    a ^ 2 / 2 ≤ basePressureCoefficient a b hab := by
  have hm : (∫ r, a ^ 2 * PressureStream.rho a b hab r) ≤
      ∫ r, r ^ 2 * PressureStream.rho a b hab r := by
    apply integral_mono ((PressureStream.rho_integrable a b hab).const_mul (a ^ 2))
      (IntegratedMeanBalances.weighted_integrable (PressureStream.rho_contDiff a b hab).continuous
        (PressureStream.rho_hasCompactSupport a b hab) 2)
    intro r
    by_cases hr : PressureStream.rho a b hab r = 0
    · simp only [hr, mul_zero, le_refl]
    · have har := (PressureStream.rho_support a b hab hr).1
      apply mul_le_mul_of_nonneg_right _ (PressureStream.rho_nonneg a b hab r)
      nlinarith [mul_nonneg (sub_nonneg.mpr har) (add_nonneg (ha.le.trans har) ha.le)]
  rw [integral_const_mul, PressureStream.rho_integral, mul_one] at hm
  exact div_le_div_of_nonneg_right hm (by norm_num)

theorem basePressureCoefficient_pos {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < basePressureCoefficient a b hab :=
  lt_of_lt_of_le (by positivity : 0 < a ^ 2 / 2) (basePressureCoefficient_lower ha hab)

/-- Pressure coefficient, given by `basePressureCoefficient g.radial.inner g.radial.outer
g.radial.inner_lt_outer * g.length n s ^ 2`. -/
noncomputable def pressureCoefficient {S : Type} (g : VariableGaugeMean.GaugeData S)
    (n : ℕ) (s : S) : ℝ :=
  basePressureCoefficient g.radial.inner g.radial.outer g.radial.inner_lt_outer * g.length n s ^ 2

/-- Exact second moment of the scaled, normalized density. -/
theorem rho_second_moment_scale {l a b : ℝ} (hl : 0 < l) (hab : a < b) :
    IntegratedMeanBalances.moment 2
      (PressureStream.rho (l * a) (l * b) (mul_lt_mul_of_pos_left hab hl)) =
      l ^ 2 * IntegratedMeanBalances.moment 2 (PressureStream.rho a b hab) := by
  have he : PressureStream.rho (l * a) (l * b) (mul_lt_mul_of_pos_left hab hl) =
      fun r => l⁻¹ * PressureStream.rho a b hab (l⁻¹ * r) := by
    funext r
    have hh := MeanChartCompatibility.rho_scale hl hab (r / l)
    rw [mul_div_cancel₀ _ hl.ne'] at hh
    simpa only [div_eq_mul_inv, mul_comm] using hh
  rw [he, IntegratedMeanBalances.moment_const_mul]
  change l⁻¹ * (∫ r, r ^ 2 * PressureStream.rho a b hab (l⁻¹ * r)) = _
  rw [SignedStressPrimitive.integral_dilate_weighted 2 _ (inv_pos.mpr hl)]
  unfold IntegratedMeanBalances.moment
  field_simp [hl.ne']; ring_nf; field_simp [hl.ne']

section GeneralGauge

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
/-- This is the coefficient of the pressure debt, measured in the moving
physical radius, rather than in the normalized profile radius. -/
theorem pressureCoefficient_measured (g : VariableGaugeMean.GaugeData S) (n : ℕ) (s : S)
    (hl : 0 < g.length n s) (Y : Plane) :
    (IntegratedMeanBalances.moment 2 (fun R => VariableGaugeMean.density
      g.radial.inner g.radial.outer g.radial.inner_lt_outer (g.length n) (R, (s, Y)))) / 2 =
      pressureCoefficient g n s := by
  have he : (fun R => VariableGaugeMean.density g.radial.inner g.radial.outer
      g.radial.inner_lt_outer (g.length n) (R, (s, Y))) =
      PressureStream.rho (g.length n s * g.radial.inner) (g.length n s * g.radial.outer)
        (mul_lt_mul_of_pos_left g.radial.inner_lt_outer hl) := by
    funext R
    exact VariableGaugeMean.density_eq_scaled g.radial.inner_lt_outer (g.length n) (R, (s, Y)) hl
  rw [he, rho_second_moment_scale hl g.radial.inner_lt_outer]
  unfold pressureCoefficient basePressureCoefficient
  ring

/-- The actual moving-gauge pressure moment. Freezing is used only to apply
a radial integral theorem on one fiber; no slow derivative is frozen. -/
theorem moving_pressure_moment {a b d M : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (ell : S → ℝ) (v : Plane) {U : Set S} (hU : IsOpen U)
    {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U))
    (hs : VariableGaugeMean.SupportedGauge a b ell U f)
    (hp : PhysicalMeanDomain.PeriodicOn U f) {s : S} (hsm : s ∈ U) (hl : 0 < ell s) :
    IntegratedMeanBalances.moment 1 (fun R => PressureStream.torusAverage
      (VariableGaugeMean.meanPressure d a b M hab ell v f) (R, s)) =
      -(1 / 2 : ℝ) * IntegratedMeanBalances.moment 2
        (fun R => PressureStream.torusAverage f (R, s)) +
      (basePressureCoefficient a b hab * ell s ^ 2) * PressureStream.pressureMass f s := by
  let F := PhysicalMeanDomain.freezeSlow s f
  have hF : ContDiff ℝ ∞ F := VariableGaugeMean.freezeSlow_contDiff hU hsm hf
  have hFs : RadialAlias.RadiallySupported (ell s * a) (ell s * b) F := by
    intro p hn
    exact hs (p.1, (s, p.2.2)) hsm hn
  have hFp : PressureStream.TorusPeriodicLift F := by
    intro R t Y k
    exact hp R s hsm Y k
  have he (R : ℝ) (Y : Plane) :
      VariableGaugeMean.meanPressure d a b M hab ell v f (R, (s, Y)) =
      PressureStream.meanPressure d (ell s * a) (ell s * b) M (mul_lt_mul_of_pos_left hab hl)
        v F (R, (s, Y)) := by
    rw [VariableGaugeMean.meanPressure_eq_fixed hab d M ell v f _ hl]
    exact PhysicalMeanDomain.meanPressure_fiberLocal d (ell s * a) (ell s * b) M
      (mul_lt_mul_of_pos_left hab hl) v f F s (fun _ _ => rfl) R Y
  have hbar : (fun R => PressureStream.torusAverage
      (VariableGaugeMean.meanPressure d a b M hab ell v f) (R, s)) =
      (fun R => PressureStream.torusAverage
        (PressureStream.meanPressure d (ell s * a) (ell s * b) M
          (mul_lt_mul_of_pos_left hab hl) v F) (R, s)) := by
    funext R
    exact PressureStream.torusAverage_congr_slice (R, s) (he R)
  have hFbar : (fun R => PressureStream.torusAverage F (R, s)) =
      (fun R => PressureStream.torusAverage f (R, s)) := by
    funext R
    exact PressureStream.torusAverage_congr_slice (R, s) (fun _ => rfl)
  have hmass : PressureStream.pressureMass F s = PressureStream.pressureMass f s := by
    change (∫ R, PressureStream.torusAverage F (R, s)) = _
    rw [hFbar]
    rfl
  rw [hbar, IntegratedMeanBalances.constructed_pressure_moment (mul_pos hl ha)
    (mul_lt_mul_of_pos_left hab hl) hd v hF hFs hFp s, hFbar, hmass, rho_second_moment_scale hl hab]
  unfold basePressureCoefficient
  ring

@[simp] theorem reconstructState_gr (g : VariableGaugeMean.GaugeData S)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S)) :
    (VariableGaugeMean.reconstructState g c u).gr c = u.gr c := rfl

@[simp] theorem reconstructState_idempotent (g : VariableGaugeMean.GaugeData S)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S)) :
    VariableGaugeMean.reconstructState g c (VariableGaugeMean.reconstructState g c u) =
      VariableGaugeMean.reconstructState g c u := rfl

end GeneralGauge

section SimilarityCoefficient

theorem similarity_pressureCoefficient {h d a b M : ℝ} (hab : a < b) (index : ℕ → ℕ)
    (hc : 0 < 2 * h) (hc1 : 2 * h < 1) (n : ℕ) {s : Plane} (hs : 0 < s.1) :
    pressureCoefficient (VariableGaugeMean.similarityGauge h d a b M hab index) n s =
      basePressureCoefficient a b hab * SimilarityCoordinates.coordinateQ (2 * h) s := by
  unfold pressureCoefficient VariableGaugeMean.similarityGauge VariableGaugeMean.qLength
  rw [Real.sq_sqrt (SimilarityCoordinates.coordinateQ_spec hc hc1 hs).1.le]

theorem similarity_pressureCoefficient_fderiv {h d a b M : ℝ} (hab : a < b) (index : ℕ → ℕ)
    (hc : 0 < 2 * h) (hc1 : 2 * h < 1) (n : ℕ) {s : Plane} (hs : 0 < s.1) (v : Plane) :
    fderiv ℝ (pressureCoefficient (VariableGaugeMean.similarityGauge h d a b M hab index) n) s v =
      basePressureCoefficient a b hab *
        ((v.1 + 2 * s.2 * SimilarityCoordinates.coordinateQ (2 * h) s ^ (2 * h) * v.2) /
          SimilarityCoordinates.scalarSlope (2 * h) s.2 (SimilarityCoordinates.coordinateQ (2 * h)
              s)) := by
  have he : pressureCoefficient (VariableGaugeMean.similarityGauge h d a b M hab index) n =ᶠ[𝓝 s]
      (fun t => basePressureCoefficient a b hab * SimilarityCoordinates.coordinateQ (2 * h) t) := by
    filter_upwards [continuousAt_fst.eventually (Ioi_mem_nhds hs)] with t ht
    exact similarity_pressureCoefficient hab index hc hc1 n ht
  rw [he.fderiv_eq]
  have hd := ((SimilarityCoordinates.coordinateQ_smooth hc hc1 hs).differentiableAt (by
      simp)).hasFDerivAt
  rw [(hd.const_mul (basePressureCoefficient a b hab)).fderiv]
  change basePressureCoefficient a b hab * fderiv ℝ (SimilarityCoordinates.coordinateQ (2 * h)) s v
      = _
  rw [SimilarityCoordinates.coordinateQ_fderiv_apply hc hc1 hs]

end SimilarityCoefficient

/-! ## Local integration on a genuine open slow region -/

section LocalIntegration

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

open StateMomentBalances

/-- Local smoothness, compact radial support, and true torus periodicity of a
field. These are regularity hypotheses, not a moment equation. -/
structure LocalField (a b : ℝ) (U : Set S) (f : ScalarField (PressureStream.Lift S)) : Prop where
  smooth : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U)
  supported : ∀ n, PhysicalMeanDomain.SupportedOn a b U (f n)
  periodic : ∀ n, PhysicalMeanDomain.PeriodicOn U (f n)

theorem LocalField.add {a b : ℝ} {U : Set S} {f g : ScalarField (PressureStream.Lift S)}
    (hf : LocalField a b U f) (hg : LocalField a b U g) : LocalField a b U (f + g) := by
  refine ⟨fun n => (hf.smooth n).add (hg.smooth n), ?_, ?_⟩
  · intro n x hx hn
    by_cases h : f n x = 0
    · apply hg.supported n x hx
      simpa only [Pi.add_apply, h, zero_add] using hn
    · exact hf.supported n x hx h
  · intro n R s hs Y k
    exact congrArg₂ (· + ·) (hf.periodic n R s hs Y k) (hg.periodic n R s hs Y k)

/-- Localize family, defined pointwise by `PhysicalMeanDomain.localize χ (f n)`. -/
noncomputable def localizeFamily (χ : S → ℝ) (f : ScalarField (PressureStream.Lift S)) :
    ScalarField (PressureStream.Lift S) := fun n => PhysicalMeanDomain.localize χ (f n)

theorem LocalField.localize {a b : ℝ} {U : Set S} (hU : IsOpen U)
    {f : ScalarField (PressureStream.Lift S)} (hf : LocalField a b U f)
    {χ : S → ℝ} (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ U) :
    DefectIncrementBounds.Shell a b (localizeFamily χ f) :=
  ⟨fun n => PhysicalMeanDomain.localize_smooth hU hχ hs (hf.smooth n),
    fun n => PhysicalMeanDomain.localize_supported hs (hf.supported n)⟩

theorem LocalField.localize_periodic {a b : ℝ} {U : Set S}
    {f : ScalarField (PressureStream.Lift S)} (hf : LocalField a b U f)
    {χ : S → ℝ} (hs : tsupport χ ⊆ U) (n : ℕ) :
    PressureStream.TorusPeriodicLift (localizeFamily χ f n) :=
  PhysicalMeanDomain.localize_periodic hs (hf.periodic n)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem radialMoment_fiber_congr (k : ℕ) {f g : ScalarField (PressureStream.Lift S)}
    (n : ℕ) (s : S) (he : ∀ R Y, f n (R, (s, Y)) = g n (R, (s, Y))) :
    CorrectionState.radialMoment k f n s = CorrectionState.radialMoment k g n s := by
  rw [state_radialMoment_eq, state_radialMoment_eq]
  apply integral_congr_ae
  filter_upwards [] with R
  exact congrArg (fun v => R ^ k * v) (PressureStream.torusAverage_congr_slice (R, s) (he R))

omit [NormedSpace ℝ S] in
theorem radialMoment_fiber_germ (k : ℕ) {f g : ScalarField (PressureStream.Lift S)}
    (n : ℕ) {s : S} (he : PhysicalMeanDomain.FiberGerm s (f n) (g n)) :
    CorrectionState.radialMoment k f n =ᶠ[𝓝 s] CorrectionState.radialMoment k g n := by
  filter_upwards [he] with t ht
  exact radialMoment_fiber_congr k n t ht

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem radialMoment_localize (k : ℕ) (χ : S → ℝ) (f : ScalarField (PressureStream.Lift S))
    (n : ℕ) (s : S) :
    CorrectionState.radialMoment k (localizeFamily χ f) n s =
      χ s * CorrectionState.radialMoment k f n s := by
  have hb (R : ℝ) : PressureStream.torusAverage (localizeFamily χ f n) (R, s) =
      χ s * PressureStream.torusAverage (f n) (R, s) := by
    rw [← AuxiliaryAverage.average_const_mul]
    exact PressureStream.torusAverage_congr_slice (R, s) (fun _ => rfl)
  rw [state_radialMoment_eq, state_radialMoment_eq]
  change IntegratedMeanBalances.moment k (fun R => PressureStream.torusAverage
    (localizeFamily χ f n) (R, s)) = _
  simp only [hb]
  exact IntegratedMeanBalances.moment_const_mul k (χ s) _

theorem dr_eventuallyEq (o : MeanIncrementBounds.Operators (PressureStream.Lift S))
    {f g : ScalarField (PressureStream.Lift S)} {n : ℕ} {x : PressureStream.Lift S}
    (he : f n =ᶠ[𝓝 x] g n) : o.dr f n =ᶠ[𝓝 x] o.dr g n := by
  filter_upwards [he.fderiv (𝕜 := ℝ)] with y hy
  simp only [MeanIncrementBounds.Operators.dr, WeightedClasses.graphDerivative, hy]

theorem dz_eventuallyEq (o : MeanIncrementBounds.Operators (PressureStream.Lift S))
    {f g : ScalarField (PressureStream.Lift S)} {n : ℕ} {x : PressureStream.Lift S}
    (he : f n =ᶠ[𝓝 x] g n) : o.dz f n =ᶠ[𝓝 x] o.dz g n := by
  filter_upwards [he.fderiv (𝕜 := ℝ)] with y hy
  simp only [MeanIncrementBounds.Operators.dz, hy]

theorem fluxResidual_eventuallyEq (o : MeanIncrementBounds.Operators (PressureStream.Lift S))
    (d k : ℝ) {u R Z T u' R' Z' T' : ScalarField (PressureStream.Lift S)}
    {n : ℕ} {x : PressureStream.Lift S}
    (hu : u n =ᶠ[𝓝 x] u' n) (hR : R n =ᶠ[𝓝 x] R' n)
    (hZ : Z n =ᶠ[𝓝 x] Z' n) (hT : T n =ᶠ[𝓝 x] T' n) :
    fluxResidual o d k u R Z T n =ᶠ[𝓝 x] fluxResidual o d k u' R' Z' T' n := by
  have hdu := dr_eventuallyEq o hu
  have hddu := dr_eventuallyEq o hdu
  have hzzu := dz_eventuallyEq o (dz_eventuallyEq o hu)
  have hdR := dr_eventuallyEq o hR
  have hdT := dr_eventuallyEq o hT
  have hdZ := dz_eventuallyEq o hZ
  filter_upwards [hu, hu.fderiv (𝕜 := ℝ), hR, hT, hdu, hddu, hzzu, hdR, hdT, hdZ]
    with y hy hdy hRy hTy hduy hdduy hzzy hdRy hdTy hdZy
  simp only [fluxResidual, MeanIncrementBounds.Operators.time,
    MeanIncrementBounds.Operators.slowTime, MeanIncrementBounds.Operators.fastTime,
    MeanIncrementBounds.Operators.radialDiv, MeanIncrementBounds.Operators.viscosity,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply,
    hy, hdy, hRy, hTy, hduy, hdduy, hzzy, hdRy, hdTy, hdZy]

theorem global_angular_moment {a b : ℝ} (ha : 0 < a)
    (r : ReconstructionData) (ε fast : ℕ → ℝ) (z t : S) (v : Plane)
    {u R Z T : ScalarField (PressureStream.Lift S)} (H : FluxInputs a b u R Z T)
    (hmass : CorrectionState.radialMoment 2 u = 0) (n : ℕ) (s : S) :
    CorrectionState.radialMoment 2
      (fluxResidual (nativeOperators r ε fast z t v) 2 1 u R Z T) n s =
      ε n * fderiv ℝ (CorrectionState.radialMoment 2 Z n) s z := by
  have hm : IntegratedMeanBalances.radialMoment 2 (averaged u n) = 0 := by
    funext q
    rw [← state_radialMoment_eq, hmass]
    rfl
  have he : averaged (fluxResidual (nativeOperators r ε fast z t v) 2 1 u R Z T) n =
      angularBalanceAlong (ε n) z t (averaged u n) (averaged R n) (averaged Z n) (averaged T n) :=
          by
    funext x
    rw [averaged_fluxResidual ha r ε fast z t v 2 1 H.velocity H.radial H.axial H.stress
      H.velocity_periodic H.radial_periodic H.axial_periodic H.stress_periodic, balance_angular]
  rw [state_radialMoment_eq, he, integrated_angular_along (ε n) z t
    (averaged_radialShell H.velocity n) (averaged_radialShell H.radial n)
    (averaged_radialShell H.axial n) (averaged_radialShell H.stress n) hm s]
  rw [show IntegratedMeanBalances.radialMoment 2 (averaged Z n) =
    CorrectionState.radialMoment 2 Z n from funext fun q => (state_radialMoment_eq 2 Z n q).symm]

theorem global_axial_moment {a b : ℝ} (ha : 0 < a)
    (r : ReconstructionData) (ε fast : ℕ → ℝ) (z t : S) (v : Plane)
    {u R Z T : ScalarField (PressureStream.Lift S)} (H : FluxInputs a b u R Z T)
    (hmass : CorrectionState.radialMoment 1 u = 0) (n : ℕ) (s : S) :
    CorrectionState.radialMoment 1
      (fluxResidual (nativeOperators r ε fast z t v) 1 0 u R Z T) n s =
      ε n * fderiv ℝ (CorrectionState.radialMoment 1 Z n) s z := by
  have hm : IntegratedMeanBalances.radialMoment 1 (averaged u n) = 0 := by
    funext q
    rw [← state_radialMoment_eq, hmass]
    rfl
  have he : averaged (fluxResidual (nativeOperators r ε fast z t v) 1 0 u R Z T) n =
      axialBalanceAlong (ε n) z t (averaged u n) (averaged R n) (averaged Z n) (averaged T n) := by
    funext x
    rw [averaged_fluxResidual ha r ε fast z t v 1 0 H.velocity H.radial H.axial H.stress
      H.velocity_periodic H.radial_periodic H.axial_periodic H.stress_periodic, balance_axial]
  rw [state_radialMoment_eq, he, integrated_axial_along (ε n) z t
    (averaged_radialShell H.velocity n) (averaged_radialShell H.radial n)
    (averaged_radialShell H.axial n) (averaged_radialShell H.stress n) hm s]
  rw [show IntegratedMeanBalances.radialMoment 1 (averaged Z n) =
    CorrectionState.radialMoment 1 Z n from funext fun q => (state_radialMoment_eq 1 Z n q).symm]

/-- Local flux inputs data, collecting `velocity`, `radial`, `axial`, `stress`. -/
structure LocalFluxInputs (a b : ℝ) (U : Set S)
    (u R Z T : ScalarField (PressureStream.Lift S)) : Prop where
  velocity : LocalField a b U u
  radial : LocalField a b U R
  axial : LocalField a b U Z
  stress : LocalField a b U T

omit [NormedSpace ℝ S] in
theorem localize_fiber_germ {s : S} {χ : S → ℝ} (hχ : χ =ᶠ[𝓝 s] fun _ => 1)
    (f : ScalarField (PressureStream.Lift S)) (n : ℕ) :
    PhysicalMeanDomain.FiberGerm s (localizeFamily χ f n) (f n) := by
  filter_upwards [hχ] with t ht
  intro R Y
  simp only [localizeFamily, PhysicalMeanDomain.localize, ht, one_smul]

omit [NormedSpace ℝ S] in
theorem localize_zero_moment {U : Set S} {χ : S → ℝ}
    (hχ : tsupport χ ⊆ U) (e : ℕ) {u : ScalarField (PressureStream.Lift S)}
    (hmass : ∀ n s, s ∈ U → CorrectionState.radialMoment e u n s = 0) :
    CorrectionState.radialMoment e (localizeFamily χ u) = 0 := by
  funext n s
  rw [radialMoment_localize]
  by_cases hc : χ s = 0
  · simp [hc]
  · rw [hmass n s (hχ (subset_tsupport χ hc)), mul_zero]
    rfl

variable [FiniteDimensional ℝ S]

theorem exists_slow_cutoff {U : Set S} (hU : IsOpen U) {s : S} (hs : s ∈ U) :
    ∃ χ : S → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ U ∧ χ =ᶠ[𝓝 s] fun _ => 1 := by
  obtain ⟨χ, hc, hcs, _, he⟩ := PhysicalMeanDomain.exists_fiber_localization hU hs
    (f := fun _ : PressureStream.Lift S => (1 : ℝ)) contDiffOn_const
  refine ⟨χ, hc, hcs, ?_⟩
  filter_upwards [he] with t ht
  simpa only [PhysicalMeanDomain.localize, smul_eq_mul, mul_one] using ht 0 0

omit [FiniteDimensional ℝ S] in
theorem LocalFluxInputs.localize {a b : ℝ} {U : Set S} (hU : IsOpen U)
    {u R Z T : ScalarField (PressureStream.Lift S)} (H : LocalFluxInputs a b U u R Z T)
    {χ : S → ℝ} (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ U) :
    FluxInputs a b (localizeFamily χ u) (localizeFamily χ R)
      (localizeFamily χ Z) (localizeFamily χ T) :=
  ⟨H.velocity.localize hU hχ hs, H.radial.localize hU hχ hs,
    H.axial.localize hU hχ hs, H.stress.localize hU hχ hs,
    H.velocity.localize_periodic hs, H.radial.localize_periodic hs,
    H.axial.localize_periodic hs, H.stress.localize_periodic hs⟩

omit [FiniteDimensional ℝ S] in
theorem residual_moment_localize (o : MeanIncrementBounds.Operators (PressureStream.Lift S))
    (e : ℕ) (d k : ℝ) {s : S} {χ : S → ℝ} (hχ : χ =ᶠ[𝓝 s] fun _ => 1)
    (u R Z T : ScalarField (PressureStream.Lift S)) (n : ℕ) :
    CorrectionState.radialMoment e (fluxResidual o d k
      (localizeFamily χ u) (localizeFamily χ R) (localizeFamily χ Z) (localizeFamily χ T)) n s =
      CorrectionState.radialMoment e (fluxResidual o d k u R Z T) n s := by
  apply radialMoment_fiber_congr
  intro r Y
  exact (fluxResidual_eventuallyEq o d k
    ((localize_fiber_germ hχ u n).eventuallyEq r Y)
    ((localize_fiber_germ hχ R n).eventuallyEq r Y)
    ((localize_fiber_germ hχ Z n).eventuallyEq r Y)
    ((localize_fiber_germ hχ T n).eventuallyEq r Y)).self_of_nhds

/-- All slow and radial derivatives are taken before integration. A compact
slow cutoff equals one on a whole neighborhood, so no moving-boundary terms
are omitted. -/
theorem local_angular_moment {a b : ℝ} (ha : 0 < a) {U : Set S} (hU : IsOpen U)
    (r : ReconstructionData) (ε fast : ℕ → ℝ) (z t : S) (v : Plane)
    {u R Z T : ScalarField (PressureStream.Lift S)} (H : LocalFluxInputs a b U u R Z T)
    (hmass : ∀ n s, s ∈ U → CorrectionState.radialMoment 2 u n s = 0)
    (n : ℕ) {s : S} (hs : s ∈ U) :
    CorrectionState.radialMoment 2
      (fluxResidual (nativeOperators r ε fast z t v) 2 1 u R Z T) n s =
      ε n * fderiv ℝ (CorrectionState.radialMoment 2 Z n) s z := by
  obtain ⟨χ, hc, hcs, he⟩ := exists_slow_cutoff hU hs
  have hh := global_angular_moment ha r ε fast z t v (H.localize hU hc hcs)
    (localize_zero_moment hcs 2 hmass) n s
  rw [residual_moment_localize _ 2 2 1 he u R Z T n,
    (radialMoment_fiber_germ 2 n (localize_fiber_germ he Z n)).fderiv_eq] at hh
  exact hh

theorem local_axial_moment {a b : ℝ} (ha : 0 < a) {U : Set S} (hU : IsOpen U)
    (r : ReconstructionData) (ε fast : ℕ → ℝ) (z t : S) (v : Plane)
    {u R Z T : ScalarField (PressureStream.Lift S)} (H : LocalFluxInputs a b U u R Z T)
    (hmass : ∀ n s, s ∈ U → CorrectionState.radialMoment 1 u n s = 0)
    (n : ℕ) {s : S} (hs : s ∈ U) :
    CorrectionState.radialMoment 1
      (fluxResidual (nativeOperators r ε fast z t v) 1 0 u R Z T) n s =
      ε n * fderiv ℝ (CorrectionState.radialMoment 1 Z n) s z := by
  obtain ⟨χ, hc, hcs, he⟩ := exists_slow_cutoff hU hs
  have hh := global_axial_moment ha r ε fast z t v (H.localize hU hc hcs)
    (localize_zero_moment hcs 1 hmass) n s
  rw [residual_moment_localize _ 1 1 0 he u R Z T n,
    (radialMoment_fiber_germ 1 n (localize_fiber_germ he Z n)).fderiv_eq] at hh
  exact hh

theorem LocalField.radialMoment_smooth {a b : ℝ} {U : Set S} (hU : IsOpen U)
    {f : ScalarField (PressureStream.Lift S)} (hf : LocalField a b U f) (e n : ℕ) :
    ContDiffOn ℝ ∞ (CorrectionState.radialMoment e f n) U := by
  have hsm : ContDiffOn ℝ ∞ (fun x : PressureStream.Lift S => x.1 ^ e * f n x)
      (PhysicalMeanDomain.slowDomain U) := (contDiffOn_fst.pow e).mul (hf.smooth n)
  have hsp : PhysicalMeanDomain.SupportedOn a b U
      (fun x : PressureStream.Lift S => x.1 ^ e * f n x) := by
    intro x hx hn
    exact hf.supported n x hx (right_ne_zero_of_mul hn)
  have hm := PhysicalMeanDomain.liftedPressureMass_contDiffOn hU hsm hsp
  have hi : ContDiffOn ℝ ∞ (fun s : S => ((0 : ℝ), (s, (0 : Plane)))) U :=
    contDiffOn_const.prodMk (contDiffOn_id.prodMk contDiffOn_const)
  exact hm.comp hi (fun s hs => hs)

theorem LocalField.radialMoment_add {a b : ℝ} {U : Set S} (hU : IsOpen U)
    {f g : ScalarField (PressureStream.Lift S)} (hf : LocalField a b U f)
    (hg : LocalField a b U g) (e n : ℕ) {s : S} (hs : s ∈ U) :
    CorrectionState.radialMoment e (f + g) n s =
      CorrectionState.radialMoment e f n s + CorrectionState.radialMoment e g n s := by
  obtain ⟨χ, hc, hcs, he⟩ := exists_slow_cutoff hU hs
  have hχ : χ s = 1 := he.self_of_nhds
  have hh := congrFun (congrFun
    (DefectIncrementBounds.barMoment_add (hf.localize hU hc hcs) (hg.localize hU hc hcs) e) n) s
  have heq : localizeFamily χ f + localizeFamily χ g = localizeFamily χ (f + g) := by
    funext n x
    simp [localizeFamily, PhysicalMeanDomain.localize, mul_add]
  change CorrectionState.radialMoment e (localizeFamily χ f + localizeFamily χ g) n s =
    CorrectionState.radialMoment e (localizeFamily χ f) n s +
    CorrectionState.radialMoment e (localizeFamily χ g) n s at hh
  simpa only [heq, radialMoment_localize, hχ, one_mul] using hh

end LocalIntegration

/-! ## The actual reconstructed state in a moving similarity shell -/

section MovingState

open StateMomentBalances LocalSignedRequest

/-- Regularity of an actual field on the moving physical shell. -/
structure MovingField {coord : ℝ} (U : SlowRegion coord) (a b : ℝ)
    (f : ScalarField Point) : Prop where
  smooth : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier)
  supported : ∀ n, VariableGaugeMean.SupportedGauge a b
    (VariableGaugeMean.qLength coord) U.carrier (f n)
  periodic : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (f n)

theorem MovingField.containing {coord a b c e : ℝ} {U : SlowRegion coord}
    {f : ScalarField Point} (hf : MovingField U a b f)
    (hl : ∀ s ∈ U.carrier, c ≤ VariableGaugeMean.qLength coord s * a)
    (hr : ∀ s ∈ U.carrier, VariableGaugeMean.qLength coord s * b ≤ e) :
    LocalField c e U.carrier f := by
  refine ⟨hf.smooth, ?_, hf.periodic⟩
  intro n x hx hn
  exact ⟨(hl _ hx).trans (hf.supported n x hx hn).1,
    (hf.supported n x hx hn).2.trans (hr _ hx)⟩

theorem MovingField.radialMoment_smooth {coord a b : ℝ} {U : SlowRegion coord}
    (ha : 0 < a) (hab : a < b) {f : ScalarField Point} (hf : MovingField U a b f)
    (e n : ℕ) : ContDiffOn ℝ ∞ (CorrectionState.radialMoment e f n) U.carrier := by
  obtain ⟨c, e', _, _, _, _, _, hl, hr, _⟩ := VariableGaugeMean.qLength_reference_bounds U ha hab
  exact (hf.containing hl hr).radialMoment_smooth U.isOpen e n

/-- Moving flux inputs data, collecting `velocity`, `radial`, `axial`, `stress`. -/
structure MovingFluxInputs {coord : ℝ} (U : SlowRegion coord) (a b : ℝ)
    (u R Z T : ScalarField Point) : Prop where
  velocity : MovingField U a b u
  radial : MovingField U a b R
  axial : MovingField U a b Z
  stress : MovingField U a b T

/-- Moving angular inputs: an abbreviation for `MovingFluxInputs U a b u.mean.angular
(thetaRadialFlux c u) (thetaAxialFlux c u) c.virtualTheta`. -/
abbrev MovingAngularInputs {coord : ℝ} (U : SlowRegion coord) (a b : ℝ)
    (c : Context Point) (u : State Point) :=
  MovingFluxInputs U a b u.mean.angular (thetaRadialFlux c u) (thetaAxialFlux c u) c.virtualTheta

/-- Moving axial inputs: an abbreviation for `MovingFluxInputs U a b u.mean.axial
(axialRadialFlux c u) (axialAxialFlux c u) c.virtualAxial`. -/
abbrev MovingAxialInputs {coord : ℝ} (U : SlowRegion coord) (a b : ℝ)
    (c : Context Point) (u : State Point) :=
  MovingFluxInputs U a b u.mean.axial (axialRadialFlux c u) (axialAxialFlux c u) c.virtualAxial

/-- Pressure recipe, given by `(VariableGaugeMean.reconstructState g c u).pressure`. -/
noncomputable def pressureRecipe (g : VariableGaugeMean.GaugeData Plane)
    (c : Context Point) (u : State Point) : ScalarField Point :=
  (VariableGaugeMean.reconstructState g c u).pressure

/-- Axial debt potential, defined pointwise by `CorrectionState.axialDefect c u n s +
pressureCoefficient g n s * CorrectionState.pressureDefect c u n s`. -/
noncomputable def axialDebtPotential (g : VariableGaugeMean.GaugeData Plane)
    (c : Context Point) (u : State Point) : ScalarField Plane :=
  fun n s => CorrectionState.axialDefect c u n s +
    pressureCoefficient g n s * CorrectionState.pressureDefect c u n s

theorem pressureRecipe_movingField {coord : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane) (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (c : Context Point) (u : State Point)
    (hf : MovingField U g.radial.inner g.radial.outer (u.gr c)) :
    MovingField U g.radial.inner g.radial.outer (pressureRecipe g c u) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    change ContDiffOn ℝ ∞ (VariableGaugeMean.meanPressure g.radial.exponent g.radial.inner
      g.radial.outer (g.radial.frequency n) g.radial.inner_lt_outer (g.length n)
      g.radial.radialDirection (u.gr c n)) _
    rw [hg n]
    exact VariableGaugeMean.meanPressure_q_contDiffOn U ha g.radial.inner_lt_outer hd
      (g.radial.frequency n) g.radial.radialDirection (hf.smooth n) (hf.supported n)
  · intro n
    change VariableGaugeMean.SupportedGauge _ _ _ _
      (VariableGaugeMean.meanPressure g.radial.exponent g.radial.inner g.radial.outer
        (g.radial.frequency n) g.radial.inner_lt_outer (g.length n) g.radial.radialDirection (u.gr
            c n))
    rw [hg n]
    exact VariableGaugeMean.meanPressure_q_supportedGauge U ha g.radial.inner_lt_outer hd
      (g.radial.frequency n) g.radial.radialDirection (hf.smooth n) (hf.supported n)
  · intro n
    exact VariableGaugeMean.meanPressure_periodicOn g.radial.inner_lt_outer
      g.radial.exponent (g.radial.frequency n) (g.length n) g.radial.radialDirection (hf.periodic n)

theorem pressureRecipe_moment {coord : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane) (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (c : Context Point) (u : State Point)
    (hf : MovingField U g.radial.inner g.radial.outer (u.gr c))
    (n : ℕ) {s : Plane} (hs : s ∈ U.carrier) :
    CorrectionState.radialMoment 1 (pressureRecipe g c u) n s =
      -(1 / 2 : ℝ) * CorrectionState.radialMoment 2 (u.gr c) n s +
      pressureCoefficient g n s * CorrectionState.pressureDefect c u n s := by
  have hl : 0 < g.length n s := by
    rw [hg n]
    exact VariableGaugeMean.qLength_pos U.coord_pos U.coord_lt_one (U.time_pos s hs)
  have hsp : VariableGaugeMean.SupportedGauge g.radial.inner g.radial.outer (g.length n)
      U.carrier (u.gr c n) := by rw [hg n]; exact hf.supported n
  have hh := moving_pressure_moment (M := g.radial.frequency n) ha g.radial.inner_lt_outer hd
      (g.length n)
    g.radial.radialDirection U.isOpen (hf.smooth n) hsp (hf.periodic n) hs hl
  rw [state_radialMoment_eq, state_radialMoment_eq]
  simpa only [pressureRecipe, VariableGaugeMean.reconstructState, averaged,
    IntegratedMeanBalances.radialMoment, pressureCoefficient,
    CorrectionState.pressureDefect, CorrectionState.radialMoment, pow_zero, one_mul] using hh

theorem axial_flux_pressure_moment {coord : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane) (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (c : Context Point) (u : State Point)
    (hZ : MovingField U g.radial.inner g.radial.outer (axialAxialFlux c u))
    (hf : MovingField U g.radial.inner g.radial.outer (u.gr c))
    (n : ℕ) {s : Plane} (hs : s ∈ U.carrier) :
    CorrectionState.radialMoment 1 (axialAxialFlux c u + pressureRecipe g c u) n s =
      axialDebtPotential g c u n s := by
  obtain ⟨a, b, _, _, _, _, _, hl, hr, _⟩ :=
    VariableGaugeMean.qLength_reference_bounds U ha g.radial.inner_lt_outer
  rw [(hZ.containing hl hr).radialMoment_add U.isOpen
    ((pressureRecipe_movingField U g ha hd hg c u hf).containing hl hr) 1 n hs,
    pressureRecipe_moment U g ha hd hg c u hf n hs]
  simp only [axialDebtPotential, CorrectionState.axialDefect, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, axialAxialFlux]
  ring

theorem state_angular_moment {coord a b : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b) (r : ReconstructionData)
    (ε fast : ℕ → ℝ) (z t v : Plane) (c : Context Point) (u : State Point)
    (ho : c.operators = nativeOperators r ε fast z t v)
    (H : MovingAngularInputs U a b c u)
    (hmass : ∀ n s, s ∈ U.carrier → CorrectionState.radialMoment 2 u.mean.angular n s = 0)
    (n : ℕ) {s : Plane} (hs : s ∈ U.carrier) :
    CorrectionState.radialMoment 2 (u.thetaResidual c) n s =
      ε n * fderiv ℝ (CorrectionState.thetaDefect c u n) s z := by
  obtain ⟨a', b', _, ha', _, _, _, hl, hr, _⟩ := VariableGaugeMean.qLength_reference_bounds U ha hab
  have he : u.thetaResidual c = fluxResidual (nativeOperators r ε fast z t v) 2 1
      u.mean.angular (thetaRadialFlux c u) (thetaAxialFlux c u) c.virtualTheta := by
    simp only [State.thetaResidual, MeanIncrementBounds.thetaResidual, fluxResidual,
      thetaRadialFlux, thetaAxialFlux, ho]
  rw [he]
  exact local_angular_moment ha' U.isOpen r ε fast z t v
    ⟨H.velocity.containing hl hr, H.radial.containing hl hr,
      H.axial.containing hl hr, H.stress.containing hl hr⟩ hmass n hs

/-- The residual is evaluated on the literal moving-gauge reconstruction.
The differentiated potential contains the full variable measured coefficient. -/
theorem reconstructed_state_axial_moment {coord : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane) (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (ε fast : ℕ → ℝ) (z t v : Plane) (c : Context Point) (u : State Point)
    (ho : c.operators = nativeOperators g.radial ε fast z t v)
    (H : MovingAxialInputs U g.radial.inner g.radial.outer c u)
    (hf : MovingField U g.radial.inner g.radial.outer (u.gr c))
    (hmass : ∀ n s, s ∈ U.carrier → CorrectionState.radialMoment 1 u.mean.axial n s = 0)
    (n : ℕ) {s : Plane} (hs : s ∈ U.carrier) :
    CorrectionState.radialMoment 1 ((VariableGaugeMean.reconstructState g c u).axialResidual c) n s
        =
      ε n * fderiv ℝ (axialDebtPotential g c u n) s z := by
  obtain ⟨a', b', _, ha', _, _, _, hl, hr, _⟩ :=
    VariableGaugeMean.qLength_reference_bounds U ha g.radial.inner_lt_outer
  have hp := (pressureRecipe_movingField U g ha hd hg c u hf).containing hl hr
  have he : (VariableGaugeMean.reconstructState g c u).axialResidual c =
      fluxResidual (nativeOperators g.radial ε fast z t v) 1 0
        u.mean.axial (axialRadialFlux c u) (axialAxialFlux c u + pressureRecipe g c u)
            c.virtualAxial := by
    simp only [VariableGaugeMean.reconstructState, State.axialResidual,
      MeanIncrementBounds.axialResidual, fluxResidual, axialRadialFlux, axialAxialFlux,
      pressureRecipe, ho]
    rfl
  have hh := local_axial_moment ha' U.isOpen g.radial ε fast z t v
    ⟨H.velocity.containing hl hr, H.radial.containing hl hr,
      (H.axial.containing hl hr).add hp, H.stress.containing hl hr⟩ hmass n hs
  have heq : CorrectionState.radialMoment 1 (axialAxialFlux c u + pressureRecipe g c u) n =ᶠ[𝓝 s]
      axialDebtPotential g c u n := by
    filter_upwards [U.isOpen.mem_nhds hs] with q hq
    exact axial_flux_pressure_moment U g ha hd hg c u H.axial hf n hq
  rwa [he, ← heq.fderiv_eq]

theorem state_axial_moment {coord : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane) (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (ε fast : ℕ → ℝ) (z t v : Plane) (c : Context Point) (u : State Point)
    (ho : c.operators = nativeOperators g.radial ε fast z t v)
    (H : MovingAxialInputs U g.radial.inner g.radial.outer c u)
    (hf : MovingField U g.radial.inner g.radial.outer (u.gr c))
    (hfixed : VariableGaugeMean.reconstructState g c u = u)
    (hmass : ∀ n s, s ∈ U.carrier → CorrectionState.radialMoment 1 u.mean.axial n s = 0)
    (n : ℕ) {s : Plane} (hs : s ∈ U.carrier) :
    CorrectionState.radialMoment 1 (u.axialResidual c) n s =
      ε n * fderiv ℝ (axialDebtPotential g c u n) s z := by
  simpa only [hfixed] using
    reconstructed_state_axial_moment U g ha hd hg ε fast z t v c u ho H hf hmass n hs

end MovingState

/-! ## All variable-coefficient terms and the actual debt classes -/

section DebtClasses

open WeightedClasses LocalSignedRequest StateMomentBalances

theorem q_pressureCoefficient {coord : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (n : ℕ) {s : Plane} (hs : s ∈ U.carrier) :
    pressureCoefficient g n s =
      basePressureCoefficient g.radial.inner g.radial.outer g.radial.inner_lt_outer *
        SimilarityCoordinates.coordinateQ coord s := by
  unfold pressureCoefficient
  rw [hg n]
  unfold VariableGaugeMean.qLength
  rw [Real.sq_sqrt (SimilarityCoordinates.coordinateQ_spec U.coord_pos U.coord_lt_one
    (U.time_pos s hs)).1.le]

theorem pressureCoefficient_smooth {coord : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord) (n : ℕ) :
    ContDiffOn ℝ ∞ (pressureCoefficient g n) U.carrier := by
  change ContDiffOn ℝ ∞ (fun s =>
    basePressureCoefficient g.radial.inner g.radial.outer g.radial.inner_lt_outer * g.length n s ^
        2) _
  rw [hg n]
  exact contDiffOn_const.mul (((VariableGaugeMean.qLength_contDiffOn U.coord_pos
      U.coord_lt_one).mono
    (fun s hs => U.time_pos s hs)).pow 2)

theorem q_pressureCoefficient_fderiv {coord : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (n : ℕ) {s : Plane} (hs : s ∈ U.carrier) (v : Plane) :
    fderiv ℝ (pressureCoefficient g n) s v =
      basePressureCoefficient g.radial.inner g.radial.outer g.radial.inner_lt_outer *
        ((v.1 + 2 * s.2 * SimilarityCoordinates.coordinateQ coord s ^ coord * v.2) /
          SimilarityCoordinates.scalarSlope coord s.2 (SimilarityCoordinates.coordinateQ coord s))
              := by
  have he : pressureCoefficient g n =ᶠ[𝓝 s]
      (fun t => basePressureCoefficient g.radial.inner g.radial.outer g.radial.inner_lt_outer *
        SimilarityCoordinates.coordinateQ coord t) := by
    filter_upwards [U.isOpen.mem_nhds hs] with t ht
    exact q_pressureCoefficient U g hg n ht
  rw [he.fderiv_eq]
  have hd := ((SimilarityCoordinates.coordinateQ_smooth U.coord_pos U.coord_lt_one
    (U.time_pos s hs)).differentiableAt (by simp)).hasFDerivAt
  rw [(hd.const_mul (basePressureCoefficient g.radial.inner g.radial.outer
    g.radial.inner_lt_outer)).fderiv]
  change basePressureCoefficient _ _ _ * fderiv ℝ (SimilarityCoordinates.coordinateQ coord) s v = _
  rw [SimilarityCoordinates.coordinateQ_fderiv_apply U.coord_pos U.coord_lt_one (U.time_pos s hs)]

/-- On the positive axial half-plane the coefficient has a strictly positive
axial derivative, so replacing it by a constant would change the identity. -/
theorem q_pressureCoefficient_axial_derivative_pos {coord : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane) (ha : 0 < g.radial.inner)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (n : ℕ) {s : Plane} (hs : s ∈ U.carrier) (hz : 0 < s.2) :
    0 < fderiv ℝ (pressureCoefficient g n) s (0, 1) := by
  have hq := SimilarityCoordinates.coordinateQ_spec U.coord_pos U.coord_lt_one (U.time_pos s hs)
  have hforward : 0 < SimilarityCoordinates.forwardScalar coord s.2
      (SimilarityCoordinates.coordinateQ coord s) := by rw [hq.2]; exact U.time_pos s hs
  have hsl := SimilarityCoordinates.scalarSlope_pos U.coord_pos U.coord_lt_one hq.1 hforward
  rw [q_pressureCoefficient_fderiv U g hg n hs]
  simp only [zero_add, mul_one]
  exact mul_pos (basePressureCoefficient_pos ha g.radial.inner_lt_outer)
    (div_pos (mul_pos (mul_pos (by norm_num) hz) (Real.rpow_pos_of_pos hq.1 coord)) hsl)

theorem axialDebtPotential_smooth {coord : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane) (ha : 0 < g.radial.inner)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (c : Context Point) (u : State Point)
    (hZ : MovingField U g.radial.inner g.radial.outer (axialAxialFlux c u))
    (hf : MovingField U g.radial.inner g.radial.outer (u.gr c)) (n : ℕ) :
    ContDiffOn ℝ ∞ (axialDebtPotential g c u n) U.carrier := by
  exact ((hZ.radialMoment_smooth ha g.radial.inner_lt_outer 1 n).sub
      ((hf.radialMoment_smooth ha g.radial.inner_lt_outer 2 n).const_smul (1 / 2 : ℝ))).add
    ((pressureCoefficient_smooth U g hg n).mul
      (hf.radialMoment_smooth ha g.radial.inner_lt_outer 0 n))

/-- The product rule is applied to the actual measured coefficient. In
particular, the last summand is present even if the unweighted debts are known. -/
theorem axialDebtPotential_fderiv {coord : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane) (ha : 0 < g.radial.inner)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (c : Context Point) (u : State Point)
    (hZ : MovingField U g.radial.inner g.radial.outer (axialAxialFlux c u))
    (hf : MovingField U g.radial.inner g.radial.outer (u.gr c))
    (n : ℕ) {s : Plane} (hs : s ∈ U.carrier) (v : Plane) :
    fderiv ℝ (axialDebtPotential g c u n) s v =
      fderiv ℝ (CorrectionState.axialDefect c u n) s v +
      pressureCoefficient g n s * fderiv ℝ (CorrectionState.pressureDefect c u n) s v +
      fderiv ℝ (pressureCoefficient g n) s v * CorrectionState.pressureDefect c u n s := by
  have hP : ContDiffOn ℝ ∞ (CorrectionState.pressureDefect c u n) U.carrier :=
    hf.radialMoment_smooth ha g.radial.inner_lt_outer 0 n
  have hJ : ContDiffOn ℝ ∞ (CorrectionState.axialDefect c u n) U.carrier :=
    (hZ.radialMoment_smooth ha g.radial.inner_lt_outer 1 n).sub
      ((hf.radialMoment_smooth ha g.radial.inner_lt_outer 2 n).const_smul (1 / 2 : ℝ))
  have hp := ((hP.contDiffAt (U.isOpen.mem_nhds hs)).differentiableAt (by simp)).hasFDerivAt
  have hj := ((hJ.contDiffAt (U.isOpen.mem_nhds hs)).differentiableAt (by simp)).hasFDerivAt
  have hc := (((pressureCoefficient_smooth U g hg n).contDiffAt
    (U.isOpen.mem_nhds hs)).differentiableAt (by simp)).hasFDerivAt
  change fderiv ℝ (fun s => CorrectionState.axialDefect c u n s +
    pressureCoefficient g n s * CorrectionState.pressureDefect c u n s) s v = _
  rw [(hj.fun_add (hc.fun_mul hp)).fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

/-- Explicit native `Z` balance, with the moving-density derivative retained. -/
theorem state_axial_moment_expanded {coord : ℝ} (U : SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane) (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (ε fast : ℕ → ℝ) (v : Plane) (c : Context Point) (u : State Point)
    (ho : c.operators = nativeOperators g.radial ε fast (0, 1) (1, 0) v)
    (H : MovingAxialInputs U g.radial.inner g.radial.outer c u)
    (hf : MovingField U g.radial.inner g.radial.outer (u.gr c))
    (hfixed : VariableGaugeMean.reconstructState g c u = u)
    (hmass : ∀ n s, s ∈ U.carrier → CorrectionState.radialMoment 1 u.mean.axial n s = 0)
    (n : ℕ) {s : Plane} (hs : s ∈ U.carrier) :
    CorrectionState.radialMoment 1 (u.axialResidual c) n s = ε n *
      (fderiv ℝ (CorrectionState.axialDefect c u n) s (0, 1) +
        pressureCoefficient g n s * fderiv ℝ (CorrectionState.pressureDefect c u n) s (0, 1) +
        (basePressureCoefficient g.radial.inner g.radial.outer g.radial.inner_lt_outer *
          ((2 * s.2 * SimilarityCoordinates.coordinateQ coord s ^ coord) /
            SimilarityCoordinates.scalarSlope coord s.2 (SimilarityCoordinates.coordinateQ coord
                s))) *
          CorrectionState.pressureDefect c u n s) := by
  rw [state_axial_moment U g ha hd hg ε fast (0, 1) (1, 0) v c u ho H hf hfixed hmass n hs,
    axialDebtPotential_fderiv U g ha hg c u H.axial hf n hs,
    q_pressureCoefficient_fderiv U g hg n hs]
  simp only [zero_add, mul_one]

theorem pressureCoefficient_unweighted {coord : ℝ} (U : SlowRegion coord)
    (P : SignedStressPrimitive.Patch) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (g : VariableGaugeMean.GaugeData Plane)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord) :
    UnweightedClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) 0
      (fun n x => pressureCoefficient g n x.2.1) := by
  have hq := qPower_unweighted U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL 1
  simp only [Real.rpow_one] at hq
  have hc := hq.map ((ContinuousLinearMap.lsmul ℝ ℝ)
    (basePressureCoefficient g.radial.inner g.radial.outer g.radial.inner_lt_outer))
  apply MeanIncrementBounds.class_congr hc
  intro n x hx
  have hs := ((movingStrip_domain U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL x).mp hx).1
  change pressureCoefficient g n x.2.1 =
    basePressureCoefficient g.radial.inner g.radial.outer g.radial.inner_lt_outer *
      SimilarityCoordinates.coordinateQ coord x.2.1
  exact q_pressureCoefficient U g hg n hs

/-- The combined potential has the same all-jet order as its actual two
debt components. The coefficient estimate uses the same moving strip. -/
theorem axialDebtPotential_unweighted {coord : ℝ} (U : SlowRegion coord)
    (P : SignedStressPrimitive.Patch) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (g : VariableGaugeMean.GaugeData Plane)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (c : Context Point) (u : State Point) (α : ℝ)
    (hP : UnweightedClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) α
      (fun n x => CorrectionState.pressureDefect c u n x.2.1))
    (hZ : UnweightedClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) α
      (fun n x => CorrectionState.axialDefect c u n x.2.1)) :
    UnweightedClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) α
      (fun n x => axialDebtPotential g c u n x.2.1) := by
  have hc := (pressureCoefficient_unweighted U P hcL hcR ε L hε hεone hL g hg).mul hP
  simp only [one_mul, zero_add] at hc
  exact hZ.add hc

end DebtClasses

/-! ## Removed physical bumps for the same actual residuals -/

section RemovedBumps

open WeightedClasses LocalSignedRequest StateMomentBalances

/-- The literal angular residual, its measured mass, and the removed physical
bump all refer to the same state and moving chart. -/
theorem state_angular_bump_improvedClass {coord a b : ℝ} (U : SlowRegion coord)
    (P : SignedStressPrimitive.Patch) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (ha : 0 < a) (hab : a < b) (r : ReconstructionData)
    (ε fast L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (z t v : Plane) (c : Context Point) (u : State Point) (α : ℝ)
    (ho : c.operators = nativeOperators r ε fast z t v)
    (H : MovingAngularInputs U a b c u)
    (hmass : ∀ n s, s ∈ U.carrier → CorrectionState.radialMoment 2 u.mean.angular n s = 0)
    (hD : UnweightedClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) α
      (fun n x => CorrectionState.thetaDefect c u n x.2.1)) :
    MeanClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) (α + 1)
      (fun n x => SignedStressPrimitive.physicalBump P 2 (SimilarityCoordinates.coordinateQ coord)
        (PressureStream.torusAverage (u.thetaResidual c n)) (x.1, x.2.1)) := by
  apply physicalBump_improvedClass_of_moment U P 2 hcL hcR ε L hε hεone hL
    (u.thetaResidual c) (CorrectionState.thetaDefect c u) z α
    (fun n => H.axial.radialMoment_smooth ha hab 2 n) hD
  intro n s hs
  change IntegratedMeanBalances.radialMoment 2 (averaged (u.thetaResidual c) n) s = _
  rw [← state_radialMoment_eq]
  exact state_angular_moment U ha hab r ε fast z t v c u ho H hmass n hs

/-- Direct reconstruction version: the source is the actual axial residual
after applying the moving pressure recipe, with no moment identity as input. -/
theorem reconstructed_state_axial_bump_improvedClass {coord : ℝ} (U : SlowRegion coord)
    (P : SignedStressPrimitive.Patch) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (g : VariableGaugeMean.GaugeData Plane) (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (ε fast L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (z t v : Plane) (c : Context Point) (u : State Point) (α : ℝ)
    (ho : c.operators = nativeOperators g.radial ε fast z t v)
    (H : MovingAxialInputs U g.radial.inner g.radial.outer c u)
    (hf : MovingField U g.radial.inner g.radial.outer (u.gr c))
    (hmass : ∀ n s, s ∈ U.carrier → CorrectionState.radialMoment 1 u.mean.axial n s = 0)
    (hP : UnweightedClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) α
      (fun n x => CorrectionState.pressureDefect c u n x.2.1))
    (hZ : UnweightedClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) α
      (fun n x => CorrectionState.axialDefect c u n x.2.1)) :
    MeanClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) (α + 1)
      (fun n x => SignedStressPrimitive.physicalBump P 1 (SimilarityCoordinates.coordinateQ coord)
        (PressureStream.torusAverage ((VariableGaugeMean.reconstructState g c u).axialResidual c n))
        (x.1, x.2.1)) := by
  apply physicalBump_improvedClass_of_moment U P 1 hcL hcR ε L hε hεone hL
    ((VariableGaugeMean.reconstructState g c u).axialResidual c) (axialDebtPotential g c u) z α
    (axialDebtPotential_smooth U g ha hg c u H.axial hf)
    (axialDebtPotential_unweighted U P hcL hcR ε L hε hεone hL g hg c u α hP hZ)
  intro n s hs
  change IntegratedMeanBalances.radialMoment 1
    (averaged ((VariableGaugeMean.reconstructState g c u).axialResidual c) n) s = _
  rw [← state_radialMoment_eq]
  exact reconstructed_state_axial_moment U g ha hd hg ε fast z t v c u ho H hf hmass n hs

/-- Fixed-point version for the actual output of a temporal or rank stage,
whose constructor finishes with `reconstructState`. -/
theorem state_axial_bump_improvedClass {coord : ℝ} (U : SlowRegion coord)
    (P : SignedStressPrimitive.Patch) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (g : VariableGaugeMean.GaugeData Plane) (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (ε fast L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (z t v : Plane) (c : Context Point) (u : State Point) (α : ℝ)
    (ho : c.operators = nativeOperators g.radial ε fast z t v)
    (H : MovingAxialInputs U g.radial.inner g.radial.outer c u)
    (hf : MovingField U g.radial.inner g.radial.outer (u.gr c))
    (hfixed : VariableGaugeMean.reconstructState g c u = u)
    (hmass : ∀ n s, s ∈ U.carrier → CorrectionState.radialMoment 1 u.mean.axial n s = 0)
    (hP : UnweightedClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) α
      (fun n x => CorrectionState.pressureDefect c u n x.2.1))
    (hZ : UnweightedClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) α
      (fun n x => CorrectionState.axialDefect c u n x.2.1)) :
    MeanClass (movingStripData U P.a P.b cL cR P.a_pos hcL hcR ε L hε hεone hL) (α + 1)
      (fun n x => SignedStressPrimitive.physicalBump P 1 (SimilarityCoordinates.coordinateQ coord)
        (PressureStream.torusAverage (u.axialResidual c n)) (x.1, x.2.1)) := by
  simpa only [hfixed] using reconstructed_state_axial_bump_improvedClass U P hcL hcR g ha hd hg
    ε fast L hε hεone hL z t v c u α ho H hf hmass hP hZ

end RemovedBumps

end NavierStokes.GaugeMomentBalances
