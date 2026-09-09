/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.BaseResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.SlowDivergence

@[expose] public section

/-!
# The curl of the finite slow potentials

The finite Borel prefixes use the average of the axial coefficient and the
primitive of the angular coefficient.  Their curl is identified here with
the finite slow field, using the actual radial flux formula and FTC.
-/

noncomputable section

namespace NavierStokes.BasePrefixIdentity

open Set Filter
open scoped Topology ContDiff


open SlowBorelBase (Inner Chart Coefficients SmoothCoefficients)

/-- Differentiating the actual primitive gives the radial average identity. -/
theorem average_radial_identity {U : Inner → ℝ} (hU : ContDiff ℝ ∞ U) (w : Inner) :
    ProfileHistories.average U w + w.1 * SimilarityProfile.partialX (ProfileHistories.average U) w =
      U w := by
  have he : ProfileHistories.primitive U =
      fun y => y.1 * ProfileHistories.average U y :=
    funext (ProfileHistories.primitive_eq_mul_average U)
  have hf : HasFDerivAt (fun y : Inner => y.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) w :=
    hasFDerivAt_fst
  have hd := hf.fun_mul
    ((SlowBorelBase.average_smooth hU).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hi := congrFun (SlowBorelBase.partialX_primitive hU) w
  rw [he] at hi
  unfold SimilarityProfile.partialX at hi ⊢
  rw [hd.fderiv] at hi
  simpa [add_comm] using hi

/-- The flux computed from histories is the axial derivative of the averaged
stream coefficient, with its exact exponent.  No divergence equation is assumed. -/
theorem radialFlux_eq_neg_X_Z_average {U : Inner → ℝ} (hU : ContDiff ℝ ∞ U)
    (h lam : ℝ) (w : Inner) :
    SlowDivergence.radialFlux h lam U w =
      -w.1 * SimilarityProfile.Z h (-CoordinateAlgebra.A h + lam) (ProfileHistories.average U) w :=
        by
  have hi := average_radial_identity hU w
  unfold SlowDivergence.radialFlux SimilarityProfile.Z CoordinateAlgebra.axialCoeff
  rw [← hi]
  simp only [CoordinateAlgebra.A, CoordinateAlgebra.D, div_eq_mul_inv]
  ring

/-- The direct finite profile and the finite Borel prefix have the same local
germ throughout the past-time chart. -/
theorem physicalUncutPrefix_germ {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (b : ℝ) (f : ℕ → Inner → ℝ) (J : ℕ) {p : Chart} (hp : p.1 < 1) :
    SlowBorelBase.physicalUncutPrefix h b f J =ᶠ[𝓝 p] SlowExpansionResidual.finiteProfile J h b f
      := by
  filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hp] with y hy
  exact SlowBorelBase.physicalUncutPrefix_eq_finiteProfile hh hh1 b f J hy

theorem partialS_physicalUncutPrefix {h b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (J : ℕ) (f : ℕ → Inner → ℝ) {p : Chart} (hp : p.1 < 1)
    (hf : ∀ n ≤ J, DifferentiableAt ℝ (f n) (SimilarityProfile.inner h p)) :
    AxisymmetricFields.partialS (SlowBorelBase.physicalUncutPrefix h b f J) p =
      SlowExpansionResidual.finiteProfile J h (b - 1) (fun n => SimilarityProfile.partialX (f n)) p
        := by
  change fderiv ℝ _ p (0, (1, 0)) = _
  rw [(physicalUncutPrefix_germ hh hh1 b f J hp).fderiv_eq]
  exact SlowExpansionResidual.partialS_finiteProfile hh hh1 J f hp hf

theorem partialZ_physicalUncutPrefix {h b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (J : ℕ) (f : ℕ → Inner → ℝ) {p : Chart} (hp : p.1 < 1)
    (hf : ∀ n ≤ J, DifferentiableAt ℝ (f n) (SimilarityProfile.inner h p)) :
    AxisymmetricFields.partialZ (SlowBorelBase.physicalUncutPrefix h b f J) p =
      SlowExpansionResidual.finiteProfile J h (b - CoordinateAlgebra.D h)
        (fun n => SimilarityProfile.Z h (b + SlowExpansionResidual.slowOrder h n) (f n)) p := by
  change fderiv ℝ _ p (0, (0, 1)) = _
  rw [(physicalUncutPrefix_germ hh hh1 b f J hp).fderiv_eq]
  exact SlowExpansionResidual.partialZ_finiteProfile hh hh1 J f hp hf

/-- The coefficient family whose flux is constructed from its axial history. -/
noncomputable def profiles (h : ℝ) (d : Coefficients) : SlowExpansionResidual.SlowProfiles where
  phi := d.phi
  axial := d.axial
  pressure := d.pressure
  flux n := SlowDivergence.radialFlux h (SlowExpansionResidual.slowOrder h n) (d.axial n)

theorem prefixStream_axial {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) (J : ℕ) (C : ℝ)
    {p : Chart} (hp : p.1 < 1) :
    BaseResidual.prefixStream J h C d p + p.2.1 * AxisymmetricFields.partialS
      (BaseResidual.prefixStream J h C d) p =
      SlowExpansionResidual.slowAxial J h (profiles h d) p := by
  have hq := SimilarityProfile.q_pos hh hh1 hp
  rw [BaseResidual.prefixStream, SlowBorelBase.physicalUncutPrefix_eq_finiteProfile hh hh1 _ _ _ hp]
  rw [partialS_physicalUncutPrefix hh hh1 J _ hp
    (fun n _ => ((SlowBorelBase.bundleComponent_smooth hd C 0 n).differentiable (by
      simp)).differentiableAt)]
  simp only [SlowExpansionResidual.slowAxial, SlowExpansionResidual.axialExponent, profiles,
    SlowExpansionResidual.finiteProfile,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  change SimilarityProfile.pullback h (-CoordinateAlgebra.A h + SlowExpansionResidual.slowOrder h n)
      (ProfileHistories.average (d.axial n)) p +
      p.2.1 * SimilarityProfile.pullback h (-CoordinateAlgebra.A h - 1 +
        SlowExpansionResidual.slowOrder h n)
        (SimilarityProfile.partialX (ProfileHistories.average (d.axial n))) p =
    SimilarityProfile.pullback h (-CoordinateAlgebra.A h + SlowExpansionResidual.slowOrder h n)
      (d.axial n) p
  have hi := average_radial_identity (hd.axial n) (SimilarityProfile.inner h p)
  rw [show -CoordinateAlgebra.A h - 1 + SlowExpansionResidual.slowOrder h n =
    (-CoordinateAlgebra.A h + SlowExpansionResidual.slowOrder h n) - 1 by ring]
  simp only [SimilarityProfile.pullback, Real.rpow_sub_one hq.ne']
  rw [← hi]
  simp only [SimilarityProfile.inner, SimilarityProfile.X]
  ring

theorem prefixSwirl_radial {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) (J : ℕ) (C : ℝ)
    {p : Chart} (hp : p.1 < 1) :
    -AxisymmetricFields.partialS (BaseResidual.prefixSwirl J h C d) p =
      SlowExpansionResidual.slowSwirl J h C (profiles h d) p := by
  rw [BaseResidual.prefixSwirl, partialS_physicalUncutPrefix hh hh1 J _ hp
    (fun n _ => ((SlowBorelBase.bundleComponent_smooth hd C 1 n).differentiable (by
      simp)).differentiableAt)]
  have he : (fun n => SimilarityProfile.partialX (SlowBorelBase.bundleComponent C d 1 n)) =
      fun n w => -C⁻¹ * d.phi n w := by
    funext n
    exact SlowBorelBase.partialX_swirl_primitive (hd.phi n) C
  rw [he]
  simp only [SlowExpansionResidual.slowSwirl, SlowExpansionResidual.angularExponent, profiles,
    SlowExpansionResidual.finiteProfile,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [SimilarityProfile.pullback]
  rw [show 1 / 2 - CoordinateAlgebra.A h - 1 + SlowExpansionResidual.slowOrder h n =
    -CoordinateAlgebra.A h - 1 / 2 + SlowExpansionResidual.slowOrder h n by ring]
  ring

theorem prefixStream_flux {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) (J : ℕ) (C : ℝ)
    {p : Chart} (hp : p.1 < 1) :
    -p.2.1 * AxisymmetricFields.partialZ (BaseResidual.prefixStream J h C d) p =
      SlowExpansionResidual.slowFlux J h (profiles h d) p := by
  have hq := SimilarityProfile.q_pos hh hh1 hp
  rw [BaseResidual.prefixStream, partialZ_physicalUncutPrefix hh hh1 J _ hp
    (fun n _ => ((SlowBorelBase.bundleComponent_smooth hd C 0 n).differentiable (by
      simp)).differentiableAt)]
  simp only [SlowExpansionResidual.slowFlux, profiles, SlowExpansionResidual.finiteProfile,
    Finset.mul_sum, zero_add]
  apply Finset.sum_congr rfl
  intro n hn
  change -p.2.1 * SimilarityProfile.pullback h
      (-CoordinateAlgebra.A h - CoordinateAlgebra.D h + SlowExpansionResidual.slowOrder h n)
      (SimilarityProfile.Z h (-CoordinateAlgebra.A h + SlowExpansionResidual.slowOrder h n)
        (ProfileHistories.average (d.axial n))) p =
    SimilarityProfile.pullback h (SlowExpansionResidual.slowOrder h n)
      (SlowDivergence.radialFlux h (SlowExpansionResidual.slowOrder h n) (d.axial n)) p
  rw [show -CoordinateAlgebra.A h - CoordinateAlgebra.D h + SlowExpansionResidual.slowOrder h n =
    SlowExpansionResidual.slowOrder h n - 1 by unfold CoordinateAlgebra.A CoordinateAlgebra.D; ring]
  simp only [SimilarityProfile.pullback, Real.rpow_sub_one hq.ne',
    radialFlux_eq_neg_X_Z_average (hd.axial n)]
  simp only [SimilarityProfile.inner, SimilarityProfile.X]
  ring

/-- The actual finite curl is the slow field with the flux constructed above. -/
theorem prefixVelocity_eq_profiles {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) (J : ℕ) (C : ℝ)
    {t : ℝ} (ht : t < 1) (x : ProblemStatement.Space)
    (hs : 0 < AxisymmetricFields.radialEnergy x) :
    BaseResidual.prefixVelocity J h C d (t, x) =
      SlowExpansionResidual.slowVelocity J h C (profiles h d) (t, x) := by
  have hH := (SlowBorelBase.physicalUncutPrefix_smoothAt hh hh1
    (SlowBorelBase.bundleComponent_smooth hd C 0) (-CoordinateAlgebra.A h) J
    (p := AxisymmetricFields.profilePoint t x) ht).differentiableAt (by simp)
  have hK := (SlowBorelBase.physicalUncutPrefix_smoothAt hh hh1
    (SlowBorelBase.bundleComponent_smooth hd C 1) (1 / 2 - CoordinateAlgebra.A h) J
    (p := AxisymmetricFields.profilePoint t x) ht).differentiableAt (by simp)
  change DifferentiableAt ℝ (BaseResidual.prefixStream J h C d)
    (AxisymmetricFields.profilePoint t x) at hH
  change DifferentiableAt ℝ (BaseResidual.prefixSwirl J h C d)
    (AxisymmetricFields.profilePoint t x) at hK
  have hu := prefixStream_axial hh hh1 hd J C (p := AxisymmetricFields.profilePoint t x) ht
  have hf := prefixSwirl_radial hh hh1 hd J C (p := AxisymmetricFields.profilePoint t x) ht
  have hv := prefixStream_flux hh hh1 hd J C (p := AxisymmetricFields.profilePoint t x) ht
  change AxisymmetricFields.velocity (BaseResidual.prefixStream J h C d)
    (BaseResidual.prefixSwirl J h C d) (t, x) = _
  rw [SlowExpansionResidual.slowVelocity_components]
  ext i
  fin_cases i
  · change AxisymmetricFields.velocity (BaseResidual.prefixStream J h C d)
      (BaseResidual.prefixSwirl J h C d) (t, x) 0 = _
    rw [AxisymmetricFields.velocity_zero _ _ _ _ hH hK, ← hf, ← hv]
    norm_num [AxisymmetricResidual.pack, ProblemStatement.coordinateVector, PiLp.single_apply]
    norm_num [Fin.ext_iff]
    dsimp only [AxisymmetricFields.profilePoint]
    field_simp [hs.ne']
  · change AxisymmetricFields.velocity (BaseResidual.prefixStream J h C d)
      (BaseResidual.prefixSwirl J h C d) (t, x) 1 = _
    rw [AxisymmetricFields.velocity_one _ _ _ _ hH hK, ← hf, ← hv]
    norm_num [AxisymmetricResidual.pack, ProblemStatement.coordinateVector, PiLp.single_apply]
    norm_num [Fin.ext_iff]
    dsimp only [AxisymmetricFields.profilePoint]
    field_simp [hs.ne'] ; ring
  · change AxisymmetricFields.velocity (BaseResidual.prefixStream J h C d)
      (BaseResidual.prefixSwirl J h C d) (t, x) 2 = _
    rw [AxisymmetricFields.velocity_two _ _ _ _ hH hK]
    simp [AxisymmetricResidual.pack, ProblemStatement.coordinateVector] at hu ⊢
    exact hu

/-- The physical similarity coordinates range inside this open half strip. -/
noncomputable def profileWindow : Set Inner := Ioi 0 ×ˢ Ioo (-1) 1

theorem profileWindow_open : IsOpen profileWindow := isOpen_Ioi.prod isOpen_Ioo

theorem inner_mem_profileWindow {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Chart} (ht : p.1 < 1) (hs : 0 < p.2.1) :
    SimilarityProfile.inner h p ∈ profileWindow := by
  refine ⟨LeadingStress.inner_X_pos hh hh1 ht hs, ?_⟩
  have he := SimilarityProfile.eta_sq_lt_one hh hh1 ht
  change -1 < SimilarityProfile.eta h p ∧ SimilarityProfile.eta h p < 1
  constructor <;> nlinarith [sq_nonneg (SimilarityProfile.eta h p + 1),
    sq_nonneg (SimilarityProfile.eta h p - 1)]

/-- Only scalar coefficient values and the actual flux identity are needed
to identify the reconstructed velocity. -/
structure VelocityMatches (h : ℝ) (d : Coefficients)
    (f : SlowExpansionResidual.SlowProfiles) : Prop where
  phi : ∀ n, EqOn (d.phi n) (f.phi n) profileWindow
  axial : ∀ n, EqOn (d.axial n) (f.axial n) profileWindow
  flux : ∀ n, EqOn
    (SlowDivergence.radialFlux h (SlowExpansionResidual.slowOrder h n) (d.axial n))
    (f.flux n) profileWindow

theorem finiteProfile_eq_of_values (J : ℕ) (h b : ℝ)
    {f g : ℕ → Inner → ℝ} {p : Chart}
    (he : ∀ n ≤ J, f n (SimilarityProfile.inner h p) = g n (SimilarityProfile.inner h p)) :
    SlowExpansionResidual.finiteProfile J h b f p =
      SlowExpansionResidual.finiteProfile J h b g p := by
  apply Finset.sum_congr rfl
  intro n hn
  unfold SimilarityProfile.pullback
  rw [he n (Nat.le_of_lt_succ (Finset.mem_range.mp hn))]

theorem prefixVelocity_eq_slowVelocity {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) {f : SlowExpansionResidual.SlowProfiles}
    (hm : VelocityMatches h d f) (J : ℕ) (C : ℝ)
    {t : ℝ} (ht : t < 1) (x : ProblemStatement.Space)
    (hs : 0 < AxisymmetricFields.radialEnergy x) :
    BaseResidual.prefixVelocity J h C d (t, x) =
      SlowExpansionResidual.slowVelocity J h C f (t, x) := by
  rw [prefixVelocity_eq_profiles hh hh1 hd J C ht x hs]
  have hw := inner_mem_profileWindow hh hh1 (p := AxisymmetricFields.profilePoint t x) ht hs
  have hv : SlowExpansionResidual.slowFlux J h (profiles h d)
      (AxisymmetricFields.profilePoint t x) =
      SlowExpansionResidual.slowFlux J h f (AxisymmetricFields.profilePoint t x) :=
    finiteProfile_eq_of_values J h 0 (fun n _ => hm.flux n hw)
  have hu : SlowExpansionResidual.slowAxial J h (profiles h d)
      (AxisymmetricFields.profilePoint t x) =
      SlowExpansionResidual.slowAxial J h f (AxisymmetricFields.profilePoint t x) :=
    finiteProfile_eq_of_values J h _ (fun n _ => hm.axial n hw)
  have hf : SlowExpansionResidual.slowSwirl J h C (profiles h d)
      (AxisymmetricFields.profilePoint t x) =
      SlowExpansionResidual.slowSwirl J h C f (AxisymmetricFields.profilePoint t x) := by
    exact congrArg (fun r : ℝ => C⁻¹ * r)
      (finiteProfile_eq_of_values J h _ (fun n _ => hm.phi n hw))
  rw [SlowExpansionResidual.slowVelocity_components, SlowExpansionResidual.slowVelocity_components,
    hv, hu, hf]

theorem prefixVelocity_germ {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) {f : SlowExpansionResidual.SlowProfiles}
    (hm : VelocityMatches h d f) (J : ℕ) (C : ℝ) {z : ProblemStatement.SpaceTime}
    (hz : z ∈ BaseResidual.annularPast) :
    BaseResidual.prefixVelocity J h C d =ᶠ[𝓝 z] SlowExpansionResidual.slowVelocity J h C f := by
  filter_upwards [BaseResidual.annularPast_isOpen.mem_nhds hz] with w hw
  exact prefixVelocity_eq_slowVelocity hh hh1 hd hm J C hw.1 w.2 hw.2

/-- In the regular radial-quotient convention, the sole radial input is the
proved identity `X * beta = radialFlux`; it determines the finite curl. -/
theorem velocityMatches_of_beta (h : ℝ) (d : Coefficients) (beta : ℕ → Inner → ℝ)
    (hb : ∀ n, ∀ w ∈ profileWindow, w.1 * beta n w =
      SlowDivergence.radialFlux h (SlowExpansionResidual.slowOrder h n) (d.axial n) w) :
    VelocityMatches h d (SlowResidualMatching.ofBeta d.phi d.axial beta d.pressure) where
  phi := fun _ _ _ => rfl
  axial := fun _ _ _ => rfl
  flux := fun n w hw => (hb n w hw).symm

/-- The remaining agreements concern scalar pressure and the actual canonical
stress primitives.  No finite-field or residual identity is an input. -/
structure CoefficientMatches (h C : ℝ) (d : Coefficients)
    (f : SlowExpansionResidual.SlowProfiles) : Prop extends VelocityMatches h d f where
  pressure : ∀ n, EqOn (d.pressure n) (f.pressure n) profileWindow
  stressTheta : ∀ n, EqOn (d.stressTheta n) (SlowResidualMatching.thetaStress h C f n) profileWindow
  stressAxial : ∀ n, EqOn (d.stressAxial n) (SlowResidualMatching.zStress h f n) profileWindow

theorem coefficient_germ {f g : Inner → ℝ} (he : EqOn f g profileWindow)
    {w : Inner} (hw : w ∈ profileWindow) : f =ᶠ[𝓝 w] g := by
  filter_upwards [profileWindow_open.mem_nhds hw] with y hy
  exact he hy

theorem prefixProfile_germ_of_coefficients {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (J : ℕ) (b : ℝ) {f g : ℕ → Inner → ℝ}
    (he : ∀ n, EqOn (f n) (g n) profileWindow)
    {p : Chart} (ht : p.1 < 1) (hs : 0 < p.2.1) :
    SlowBorelBase.physicalUncutPrefix h b f J =ᶠ[𝓝 p]
      SlowExpansionResidual.finiteProfile J h b g := by
  filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds ht,
    (isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).mem_nhds hs]
    with y hyt hys
  rw [SlowBorelBase.physicalUncutPrefix_eq_finiteProfile hh hh1 b f J hyt]
  exact finiteProfile_eq_of_values J h b (fun n _ => he n (inner_mem_profileWindow hh hh1 hyt hys))

theorem prefixPressure_germ {h C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} {f : SlowExpansionResidual.SlowProfiles}
    (hm : CoefficientMatches h C d f) (J : ℕ) {z : ProblemStatement.SpaceTime}
    (hz : z ∈ BaseResidual.annularPast) :
    BaseResidual.prefixPressure J h C d =ᶠ[𝓝 z] SlowExpansionResidual.slowPressureField J h f := by
  have he := prefixProfile_germ_of_coefficients hh hh1 J (-2 * CoordinateAlgebra.A h)
    (f := SlowBorelBase.bundleComponent C d 2) hm.pressure
    (p := AxisymmetricFields.profilePoint z.1 z.2) hz.1 hz.2
  exact he.comp_tendsto (AxisymmetricFields.contDiff_profilePoint (n := ∞)).continuous.continuousAt

theorem radialDivergence_congr_germ (k : ℝ) {f g : Chart → ℝ} {p : Chart}
    (he : f =ᶠ[𝓝 p] g) :
    LeadingStress.radialDivergence k f p = LeadingStress.radialDivergence k g p := by
  unfold LeadingStress.radialDivergence SimilarityProfile.partialS
  rw [he.eq_of_nhds, he.fderiv_eq]

theorem prefixStressForce_eq {h C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} {f : SlowExpansionResidual.SlowProfiles}
    (hm : CoefficientMatches h C d f) (J : ℕ) {z : ProblemStatement.SpaceTime}
    (hz : z ∈ BaseResidual.annularPast) :
    BaseResidual.prefixStressForce J h C d z =
      SlowResidualMatching.tangentialStressForce
        (SlowResidualMatching.physicalThetaStress J h C f)
        (SlowResidualMatching.physicalZStress J h f) z.1 z.2 := by
  have htheta := prefixProfile_germ_of_coefficients hh hh1 J (-CoordinateAlgebra.A h - 1 / 2)
    (f := SlowBorelBase.bundleComponent C d 3) hm.stressTheta
    (p := AxisymmetricFields.profilePoint z.1 z.2) hz.1 hz.2
  have haxial := prefixProfile_germ_of_coefficients hh hh1 J (-CoordinateAlgebra.A h - 1 / 2)
    (f := SlowBorelBase.bundleComponent C d 4) hm.stressAxial
    (p := AxisymmetricFields.profilePoint z.1 z.2) hz.1 hz.2
  change BaseResidual.prefixStressTheta J h C d =ᶠ[𝓝 (AxisymmetricFields.profilePoint z.1 z.2)]
    SlowResidualMatching.physicalThetaStress J h C f at htheta
  change BaseResidual.prefixStressAxial J h C d =ᶠ[𝓝 (AxisymmetricFields.profilePoint z.1 z.2)]
    SlowResidualMatching.physicalZStress J h f at haxial
  unfold BaseResidual.prefixStressForce BaseResidual.stressForce
    SlowResidualMatching.tangentialStressForce
  rw [radialDivergence_congr_germ 2 htheta, radialDivergence_congr_germ 1 haxial]

theorem VelocityMatches.phi_contDiffAt {h : ℝ} {d : Coefficients}
    (hd : SmoothCoefficients d) {f : SlowExpansionResidual.SlowProfiles}
    (hm : VelocityMatches h d f) (n : ℕ) {w : Inner} (hw : w ∈ profileWindow) :
    ContDiffAt ℝ ∞ (f.phi n) w :=
  (hd.phi n).contDiffAt.congr_of_eventuallyEq (coefficient_germ (hm.phi n) hw).symm

theorem VelocityMatches.axial_contDiffAt {h : ℝ} {d : Coefficients}
    (hd : SmoothCoefficients d) {f : SlowExpansionResidual.SlowProfiles}
    (hm : VelocityMatches h d f) (n : ℕ) {w : Inner} (hw : w ∈ profileWindow) :
    ContDiffAt ℝ ∞ (f.axial n) w :=
  (hd.axial n).contDiffAt.congr_of_eventuallyEq (coefficient_germ (hm.axial n) hw).symm

theorem VelocityMatches.flux_contDiffAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) {f : SlowExpansionResidual.SlowProfiles}
    (hm : VelocityMatches h d f) (n : ℕ) {w : Inner} (hw : w ∈ profileWindow) :
    ContDiffAt ℝ ∞ (f.flux n) w := by
  have hs : w.2 ^ 2 ≤ 1 := by
    have h1 := hw.2.1
    have h2 := hw.2.2
    nlinarith [mul_nonneg (show 0 ≤ 1 - w.2 by linarith) (show 0 ≤ 1 + w.2 by linarith)]
  have hL := (CoordinateAlgebra.L_pos hh.le hh1 hs).ne'
  exact (SlowDivergence.radialFlux_smoothAt SlowBorelBase.globalRadialDomain
    (hd.axial n).contDiffOn h (SlowExpansionResidual.slowOrder h n) (mem_univ _)
      hL).congr_of_eventuallyEq
      (coefficient_germ (hm.flux n) hw).symm

theorem CoefficientMatches.pressure_contDiffAt {h C : ℝ} {d : Coefficients}
    (hd : SmoothCoefficients d) {f : SlowExpansionResidual.SlowProfiles}
    (hm : CoefficientMatches h C d f) (n : ℕ) {w : Inner} (hw : w ∈ profileWindow) :
    ContDiffAt ℝ ∞ (f.pressure n) w :=
  (hd.pressure n).contDiffAt.congr_of_eventuallyEq (coefficient_germ (hm.pressure n) hw).symm

/-- The finite identity required by the Borel residual estimates, now derived
from the actual finite potentials and scalar recurrence data. -/
theorem finiteIdentities_of_coefficients {h C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) {f : SlowExpansionResidual.SlowProfiles}
    (hm : CoefficientMatches h C d f)
    (hTheta : ∀ n, SlowStressSupport.Smooth (Ioo (-1) 1) (SlowResidualMatching.thetaDensity h C f
      n))
    (hZ : ∀ n, SlowStressSupport.Smooth (Ioo (-1) 1) (SlowResidualMatching.zDensity h f n))
    (hp : ∀ n, ∀ w ∈ profileWindow, SlowExpansionResidual.pressureCoefficient h C f n w = 0) :
    BaseResidual.FiniteIdentities h C d f := by
  intro J z hz
  have hw := inner_mem_profileWindow hh hh1 (p := AxisymmetricFields.profilePoint z.1 z.2) hz.1 hz.2
  rw [ResidualRegularity.residual_congr (prefixVelocity_germ hh hh1 hd hm.toVelocityMatches J C hz)
    (prefixPressure_germ hh hh1 hm J hz), prefixStressForce_eq hh hh1 hm J hz]
  exact SlowResidualMatching.navierStokesResidual_eq_stress_add_truncation isOpen_Ioo hh hh1 J C f
    (fun n _ => hTheta n) (fun n _ => hZ n) hz.1 hz.2 hw.2
    (fun n _ => (hm.toVelocityMatches.flux_contDiffAt hh hh1 hd n hw).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (fun n _ => (hm.toVelocityMatches.phi_contDiffAt hd n hw).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (fun n _ => (hm.toVelocityMatches.axial_contDiffAt hd n hw).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (fun n _ => (hm.pressure_contDiffAt hd n hw).differentiableAt (by simp))
    (fun n _ => hp n _ hw)

end NavierStokes.BasePrefixIdentity
