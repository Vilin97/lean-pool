/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.NominalProfile

/-!
# Quantitative bounds for the actual five-row matching debt

The vanishing rescaled prefix and the drift of the held axial endpoint are
estimated separately.  All parameter derivatives below are actual derivatives
of the constructed fields and their moment integrals.
-/

@[expose] public section


noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff BigOperators

namespace NavierStokes.MatchingDebtBounds

/-- Point: an abbreviation for `ℝ × ℝ`. -/
abbrev Point := ℝ × ℝ
/-- Field: an abbreviation for `Point → ℝ`. -/
abbrev Field := Point → ℝ
/-- Debt: an abbreviation for `FiveProfileMoments.Debt`. -/
abbrev Debt := FiveProfileMoments.Debt

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)

/-! ## Smooth extensions which preserve the entire parameter germ

The incoming fields are smooth on their natural open strip.  These explicit
retractions allow the global smooth integral estimates to be used without
assuming a global extension as additional data.
-/

/-- Parameter clamp, given by `eta * (1 - OutgoingSchedule.sigma (20 * (eta ^ 2 - 1) - 1))`. -/
noncomputable def parameterClamp (eta : ℝ) : ℝ :=
  eta * (1 - OutgoingSchedule.sigma (20 * (eta ^ 2 - 1) - 1))

theorem parameterClamp_smooth : ContDiff ℝ ∞ parameterClamp :=
  contDiff_id.mul (contDiff_const.sub (OutgoingSchedule.sigma_contDiff.comp
    ((contDiff_const.mul ((contDiff_id.pow 2).sub contDiff_const)).sub contDiff_const)))

theorem parameterClamp_eq {eta : ℝ} (h : eta ^ 2 ≤ 21 / 20) : parameterClamp eta = eta := by
  simp [parameterClamp, OutgoingSchedule.sigma_zero (by linarith : 20 * (eta ^ 2 - 1) - 1 ≤ 0)]

theorem parameterClamp_mem (eta : ℝ) : parameterClamp eta ∈ ReferencePath.parameterInterval := by
  have hs0 := OutgoingSchedule.sigma_nonneg (20 * (eta ^ 2 - 1) - 1)
  have hs1 := OutgoingSchedule.sigma_le_one (20 * (eta ^ 2 - 1) - 1)
  have hnorm : |parameterClamp eta| < 11 / 10 := by
    by_cases h : eta ^ 2 < 11 / 10
    · have he : |eta| < 11 / 10 := by nlinarith [sq_abs eta, abs_nonneg eta]
      calc
        |parameterClamp eta| = |eta| * (1 - OutgoingSchedule.sigma (20 * (eta ^ 2 - 1) - 1)) := by
          rw [parameterClamp, abs_mul, abs_of_nonneg (sub_nonneg.mpr hs1)]
        _ ≤ |eta| := mul_le_of_le_one_right (abs_nonneg eta) (by linarith)
        _ < 11 / 10 := he
    · have hs := OutgoingSchedule.sigma_one (show 1 ≤ 20 * (eta ^ 2 - 1) - 1 by linarith)
      simp only [parameterClamp, hs, sub_self, mul_zero, abs_zero]
      norm_num
  simpa only [ReferencePath.parameterInterval, NaturalAxisCoefficients.window, mem_Ioo,
    neg_div] using abs_lt.mp hnorm

theorem parameterClamp_eventuallyEq {eta : ℝ} (hη : eta ∈ Icc (-1 : ℝ) 1) :
    parameterClamp =ᶠ[𝓝 eta] id := by
  have hs : eta ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one eta).mpr (abs_le.mpr hη)
  have hn : {x : ℝ | x ^ 2 < 21 / 20} ∈ 𝓝 eta :=
    (continuousAt_id.pow 2).eventually (Iio_mem_nhds (by linarith : eta ^ 2 < 21 / 20))
  filter_upwards [hn] with x hx
  exact parameterClamp_eq hx.le

/-- Radial clamp, given by `X * OutgoingSchedule.sigma (scale * X + 2)`. -/
noncomputable def radialClamp (scale X : ℝ) : ℝ :=
  X * OutgoingSchedule.sigma (scale * X + 2)

theorem radialClamp_smooth (scale : ℝ) : ContDiff ℝ ∞ (radialClamp scale) :=
  contDiff_id.mul (OutgoingSchedule.sigma_contDiff.comp
    ((contDiff_const.mul contDiff_id).add contDiff_const))

theorem radialClamp_eq {scale X : ℝ} (hscale : 0 < scale) (hX : 0 ≤ X) :
    radialClamp scale X = X := by
  simp [radialClamp, OutgoingSchedule.sigma_one (show 1 ≤ scale * X + 2 by
    linarith [mul_nonneg hscale.le hX])]

theorem radialClamp_mem {scale : ℝ} (hscale : 0 < scale) (X : ℝ) :
    -20 < scale * radialClamp scale X := by
  have hs0 := OutgoingSchedule.sigma_nonneg (scale * X + 2)
  have hs1 := OutgoingSchedule.sigma_le_one (scale * X + 2)
  by_cases h : scale * X + 2 ≤ 0
  · simp [radialClamp, OutgoingSchedule.sigma_zero h]
  · by_cases hX : 0 ≤ X
    · rw [radialClamp_eq hscale hX]
      linarith [mul_nonneg hscale.le hX]
    · have hXn : X ≤ 0 := (lt_of_not_ge hX).le
      have hm : scale * X ≤ scale * X * OutgoingSchedule.sigma (scale * X + 2) := by
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hscale.le hXn]
      dsimp [radialClamp]
      linarith

/-- Strip, given by `{p | -20 < scale * p.1 ∧ p.2 ∈ ReferencePath.parameterInterval}`. -/
noncomputable def strip (scale : ℝ) : Set Point :=
  {p | -20 < scale * p.1 ∧ p.2 ∈ ReferencePath.parameterInterval}

theorem strip_open (scale : ℝ) : IsOpen (strip scale) :=
  (isOpen_lt continuous_const (continuous_const.mul continuous_fst)).inter
    (ReferencePath.parameterInterval_open.preimage continuous_snd)

/-- Extend parameter, given by `g (parameterClamp eta)`. -/
noncomputable def extendParameter (g : ℝ → ℝ) (eta : ℝ) : ℝ := g (parameterClamp eta)

/-- Extend field, given by `f (radialClamp scale p.1, parameterClamp p.2)`. -/
noncomputable def extendField (scale : ℝ) (f : Field) (p : Point) : ℝ :=
  f (radialClamp scale p.1, parameterClamp p.2)

theorem extendParameter_smooth {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g ReferencePath.parameterInterval) :
    ContDiff ℝ ∞ (extendParameter g) := by
  apply contDiff_iff_contDiffAt.mpr
  intro eta
  exact (hg.contDiffAt (ReferencePath.parameterInterval_open.mem_nhds (parameterClamp_mem
      eta))).comp
    eta parameterClamp_smooth.contDiffAt

theorem extendField_smooth {scale : ℝ} (hscale : 0 < scale) {f : Field}
    (hf : ContDiffOn ℝ ∞ f (strip scale)) : ContDiff ℝ ∞ (extendField scale f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (hf.contDiffAt ((strip_open scale).mem_nhds
    ⟨radialClamp_mem hscale p.1, parameterClamp_mem p.2⟩)).comp p
      (((radialClamp_smooth scale).contDiffAt.comp p contDiffAt_fst).prodMk
        (parameterClamp_smooth.contDiffAt.comp p contDiffAt_snd))

theorem extendParameter_eventuallyEq {eta : ℝ} (hη : eta ∈ Icc (-1 : ℝ) 1)
    (g : ℝ → ℝ) : extendParameter g =ᶠ[𝓝 eta] g :=
  (parameterClamp_eventuallyEq hη).fun_comp g

theorem extendField_slice_eventuallyEq {scale X eta : ℝ} (hscale : 0 < scale)
    (hX : 0 ≤ X) (hη : eta ∈ Icc (-1 : ℝ) 1) (f : Field) :
    (fun e => extendField scale f (X, e)) =ᶠ[𝓝 eta] (fun e => f (X, e)) := by
  filter_upwards [parameterClamp_eventuallyEq hη] with e he
  simp only [extendField, radialClamp_eq hscale hX, he, id_eq]

/-! ## The actual five-row vector and its jets -/

/-- Reset vector as an element of `Debt`. -/
noncomputable def resetVector (R r b : ℝ) (u f : Field) (Gi A : ℝ → ℝ)
    (eta : ℝ) : Debt :=
  ![ShapeTransition.resetDebtM u Gi r b eta,
    ShapeTransition.resetDebtI R f A r eta,
    ShapeTransition.resetDebtJ R u f Gi A r b eta,
    ShapeTransition.resetDebtS R u f Gi A r b eta,
    ShapeTransition.resetDebtP R f A r eta]

theorem resetVector_smooth {R r b : ℝ} (hR : 0 ≤ R) (hr : 0 < r) (hrb : r ≤ b)
    {u f : Field} {Gi A : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (hGi : ContDiff ℝ ∞ Gi) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (resetVector R r b u f Gi A) := by
  obtain ⟨huM, huI, huJ, huS, huP⟩ := ShapeTransition.rows_contDiff hR hr.le hu hf
  have hg4 : ContDiff ℝ ∞ (fun e : ℝ => 4 * e) := contDiff_const.mul contDiff_id
  obtain ⟨hiM, hiI, hiJ, hiS, hiP⟩ := ShapeTransition.ideal_rows_contDiff r hg4 hA
  have hrM : ContDiff ℝ ∞ (ShapeTransition.restoreDebtM Gi r b) :=
    (ShapeTransition.smooth_parameter_interval hrb
      (fun x hx e => (ShapeTransition.restore_local_smooth hGi hA (hr.trans_le hx.1) e).1)).1
  have hrJ : ContDiff ℝ ∞ (ShapeTransition.restoreDebtJ Gi A r b) :=
    (ShapeTransition.smooth_parameter_interval hrb
      (fun x hx e => (ShapeTransition.restore_local_smooth hGi hA (hr.trans_le hx.1) e).2.1)).1
  have hrS : ContDiff ℝ ∞ (ShapeTransition.restoreDebtS Gi r b) :=
    (ShapeTransition.smooth_parameter_interval hrb
      (fun x hx e => (ShapeTransition.restore_local_smooth hGi hA (hr.trans_le hx.1) e).2.2)).1
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact (huM.sub hiM).add hrM
  · exact huI.sub hiI
  · exact (huJ.sub hiJ).add hrJ
  · exact (huS.sub hiS).add hrS
  · exact huP.sub hiP

theorem iteratedDeriv_component {d : ℝ → Debt} (hd : ContDiff ℝ ∞ d)
    (n : ℕ) (eta : ℝ) (i : Fin 5) :
    (iteratedDeriv n d eta) i = iteratedDeriv n (fun e => d e i) eta := by
  have he := (ContinuousLinearMap.proj i : Debt →L[ℝ] ℝ).iteratedFDeriv_comp_left (x := eta)
    hd.contDiffAt (nat_le_infty n)
  have h := (congrArg (fun L => L (fun _ : Fin n => (1 : ℝ))) he).symm
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_def] at h
  exact h

theorem vector_jet_le_sum {d : ℝ → Debt} (hd : ContDiff ℝ ∞ d) (n : ℕ) (eta : ℝ) :
    ‖iteratedFDeriv ℝ n d eta‖ ≤ ∑ i : Fin 5, |iteratedDeriv n (fun e => d e i) eta| := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).mpr
  intro i
  rw [Real.norm_eq_abs, iteratedDeriv_component hd]
  exact Finset.single_le_sum
    (f := fun i : Fin 5 => |iteratedDeriv n (fun e => d e i) eta|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

theorem resetVector_jet_bound {R r b : ℝ} (hR : 0 ≤ R) (hr : 0 < r) (hrb : r ≤ b)
    {u f : Field} {Gi A : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (hGi : ContDiff ℝ ∞ Gi) (hA : ContDiff ℝ ∞ A) (n : ℕ) (eta : ℝ) :
    ‖iteratedFDeriv ℝ n (resetVector R r b u f Gi A) eta‖ ≤
      ShapeTransition.resetDebtJetSize n R r b u f Gi A eta := by
  convert! vector_jet_le_sum (resetVector_smooth hR hr hrb hu hf hGi hA) n eta using 1
  simp [resetVector, ShapeTransition.resetDebtJetSize, Fin.sum_univ_succ, add_assoc]

theorem resetVector_congr {R r b eta : ℝ} (hr : 0 ≤ r)
    {u₁ u₂ f₁ f₂ : Field} {Gi₁ Gi₂ A : ℝ → ℝ}
    (hu : ∀ x ∈ Icc (0 : ℝ) r, u₁ (x, eta) = u₂ (x, eta))
    (hf : ∀ x ∈ Icc (0 : ℝ) r, f₁ (x, eta) = f₂ (x, eta))
    (hG : Gi₁ eta = Gi₂ eta) :
    resetVector R r b u₁ f₁ Gi₁ A eta = resetVector R r b u₂ f₂ Gi₂ A eta := by
  have he (x : ℝ) (hx : x ∈ Icc (0 : ℝ) r) :
      ShapeTransition.scaledE R f₁ (x, eta) = ShapeTransition.scaledE R f₂ (x, eta) := by
    simp only [ShapeTransition.scaledE, hf x hx]
  have hm : ShapeTransition.rowM u₁ r eta = ShapeTransition.rowM u₂ r eta := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact hu x (by simpa only [uIcc_of_le hr] using hx)
  have hi : ShapeTransition.rowI R f₁ r eta = ShapeTransition.rowI R f₂ r eta := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [he x (by simpa only [uIcc_of_le hr] using hx)]
  have hj : ShapeTransition.rowJ R u₁ f₁ r eta = ShapeTransition.rowJ R u₂ f₂ r eta := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) r := by simpa only [uIcc_of_le hr] using hx
    simp only [hu x hx', he x hx']
  have hs : ShapeTransition.rowS R u₁ f₁ r eta = ShapeTransition.rowS R u₂ f₂ r eta := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) r := by simpa only [uIcc_of_le hr] using hx
    simp only [hu x hx', he x hx']
  have hp : ShapeTransition.rowP R f₁ r eta = ShapeTransition.rowP R f₂ r eta := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [he x (by simpa only [uIcc_of_le hr] using hx)]
  have hrm : ShapeTransition.restoreDebtM Gi₁ r b eta = ShapeTransition.restoreDebtM Gi₂ r b eta :=
      by
    simp only [ShapeTransition.restoreDebtM, ShapeTransition.restoreDefect,
        ShapeTransition.restore, hG]
  have hrj : ShapeTransition.restoreDebtJ Gi₁ A r b eta = ShapeTransition.restoreDebtJ Gi₂ A r b
      eta := by
    simp only [ShapeTransition.restoreDebtJ, ShapeTransition.restoreDensityJ,
      ShapeTransition.restoreDefect, ShapeTransition.restore, hG]
  have hrs : ShapeTransition.restoreDebtS Gi₁ r b eta = ShapeTransition.restoreDebtS Gi₂ r b eta :=
      by
    simp only [ShapeTransition.restoreDebtS, ShapeTransition.restoreDensityS,
      ShapeTransition.restoreDefect, ShapeTransition.restore, hG]
  simp only [resetVector, ShapeTransition.resetDebtM, ShapeTransition.resetDebtI,
    ShapeTransition.resetDebtJ, ShapeTransition.resetDebtS, ShapeTransition.resetDebtP,
    hm, hi, hj, hs, hp, hrm, hrj, hrs]

section ActualFields

variable {F : OutgoingProfile.Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A)

/-- Extended U, given by `ShapeTransition.scaledFamily c.radius (extendField A.scale c.seedU)`. -/
noncomputable def extendedU : Field :=
  ShapeTransition.scaledFamily c.radius (extendField A.scale c.seedU)

/-- Extended F, constructed using `ShapeTransition.scaledFamily`. -/
noncomputable def extendedF : Field :=
  ShapeTransition.scaledFamily c.radius (ShapeTransition.shapeField NominalProfile.Xi c.shapeTime
    (extendParameter c.initialShape) (extendField A.scale c.seedF))

/-- Extended debt, constructed using `resetVector`. -/
noncomputable def extendedDebt : ℝ → Debt :=
  resetVector c.radius c.separation NominalProfile.matchFraction (extendedU c) (extendedF c)
    (extendParameter c.initialAxial) (NominalProfile.idealAmplitude F)

theorem extendedU_smooth : ContDiff ℝ ∞ (extendedU c) :=
  ShapeTransition.scaledFamily_contDiff c.radius (extendField_smooth A.scale_pos c.seedU_smooth)

theorem extendedF_smooth : ContDiff ℝ ∞ (extendedF c) :=
  ShapeTransition.scaledFamily_contDiff c.radius
    (ShapeTransition.shapeField_contDiff NominalProfile.Xi_pos c.shapeTime_pos
      (extendParameter_smooth c.initialShape_smooth) (extendField_smooth A.scale_pos
          c.seedF_smooth))

theorem extendedDebt_smooth (hsep : c.separation ≤ Real.exp (-8)) :
    ContDiff ℝ ∞ (extendedDebt c) :=
  resetVector_smooth c.radius_pos.le c.separation_pos
    (hsep.trans (Real.exp_le_exp.mpr (by norm_num : (-8 : ℝ) ≤ -5)))
    (extendedU_smooth c) (extendedF_smooth c) (extendParameter_smooth c.initialAxial_smooth)
    (NominalProfile.idealAmplitude_smooth F)

theorem extendedDebt_eventuallyEq {eta : ℝ} (hη : eta ∈ Icc (-1 : ℝ) 1) :
    extendedDebt c =ᶠ[𝓝 eta] c.manuscriptDebt := by
  filter_upwards [parameterClamp_eventuallyEq hη] with e he
  change resetVector _ _ _ _ _ _ _ e = resetVector _ _ _ _ _ _ _ e
  apply resetVector_congr c.separation_pos.le
  · intro x hx
    simp only [extendedU, ShapeTransition.scaledFamily, extendField,
      NominalProfile.Controls.rawU, radialClamp_eq A.scale_pos (mul_nonneg c.radius_pos.le hx.1),
          he, id_eq]
  · intro x hx
    simp only [extendedF, ShapeTransition.scaledFamily, ShapeTransition.shapeField,
      extendField, extendParameter, NominalProfile.Controls.rawF, NominalProfile.Controls.shapedF,
      radialClamp_eq A.scale_pos (mul_nonneg c.radius_pos.le hx.1), he, id_eq]
  · simp only [extendParameter, he, id_eq]

theorem debt_eventuallyEq_negative_extended (hsep : c.separation ≤ Real.exp (-8))
    {eta : ℝ} (hη : eta ∈ Icc (-1 : ℝ) 1) :
    c.debt =ᶠ[𝓝 eta] (fun e => -extendedDebt c e) := by
  filter_upwards [extendedDebt_eventuallyEq c hη,
    ReferencePath.parameterInterval_open.mem_nhds
      (NaturalAxisCoefficients.original_interval_interior hη)] with e he heJ
  rw [c.debt_eq_negative_manuscriptDebt hsep heJ, he]

/-- Bounds on actual seed fields, before the shape modification or any
moment integration.  They are supplied below by `ordered_seed_bounds`. -/
structure SeedJets (N : ℕ) (B K BJ : ℝ) : Prop where
  axial : ∀ X, 0 ≤ X → ∀ eta ∈ Icc (-1 : ℝ) 1, ∀ n ≤ N,
    |iteratedDeriv n (fun e => c.seedU (X, e)) eta| ≤ B
  angular : ∀ X, 0 ≤ X → ∀ eta ∈ Icc (-1 : ℝ) 1, ∀ n ≤ N,
    |iteratedDeriv n (fun e => c.seedF (X, e)) eta| ≤ K / A.normalization
  logarithm : ∀ eta ∈ Icc (-1 : ℝ) 1, ∀ n ≤ N,
    |iteratedDeriv n c.initialShape eta| ≤ BJ

theorem radius_mul_separation : c.radius * c.separation = NominalProfile.Xi * Real.exp c.shapeTime
    :=
  ShapeTransition.resetRadius_mul_separation _ _ _ _
    (mul_pos A.normalization_pos F.data.core.P_pos).ne'

theorem extendedU_jets {N : ℕ} {B K BJ : ℝ} (hj : SeedJets c N B K BJ)
    {eta x : ℝ} (hη : eta ∈ Icc (-1 : ℝ) 1) (hx : 0 ≤ x) {n : ℕ} (hn : n ≤ N) :
    |iteratedDeriv n (fun e => extendedU c (x, e)) eta| ≤ B := by
  change |iteratedDeriv n (fun e => extendField A.scale c.seedU (c.radius * x, e)) eta| ≤ B
  rw [(extendField_slice_eventuallyEq A.scale_pos (mul_nonneg c.radius_pos.le hx) hη
      c.seedU).iteratedDeriv_eq n]
  exact hj.axial _ (mul_nonneg c.radius_pos.le hx) eta hη n hn

theorem extendedF_jets {N : ℕ} {B K BJ : ℝ} (hj : SeedJets c N B K BJ)
    (hBJ : 1 ≤ BJ) (hK : 0 ≤ K)
    (hshape : ∀ eta ∈ Icc (-1 : ℝ) 1, ∀ n ≤ N,
      |iteratedDeriv n ShapeTransition.logShape eta| ≤ BJ)
    {eta x : ℝ} (hη : eta ∈ Icc (-1 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) c.separation)
    {n : ℕ} (hn : n ≤ N) :
    |iteratedDeriv n (fun e => extendedF c (x, e)) eta| ≤
      ShapeTransition.shapeJetConstant N NominalProfile.Xi c.shapeTime BJ K / A.normalization := by
  have hx0 := mul_nonneg c.radius_pos.le hx.1
  have hxL : c.radius * x ≤ NominalProfile.Xi * Real.exp c.shapeTime := by
    rw [← radius_mul_separation c]
    exact mul_le_mul_of_nonneg_left hx.2 c.radius_pos.le
  change |iteratedDeriv n (fun e => ShapeTransition.shapeField NominalProfile.Xi c.shapeTime
    (extendParameter c.initialShape) (extendField A.scale c.seedF) (c.radius * x, e)) eta| ≤ _
  apply ShapeTransition.shapeField_jets_uniform NominalProfile.Xi_pos A.normalization_pos
    c.shapeTime_pos hx0 hxL (extendParameter_smooth c.initialShape_smooth) hBJ hK N eta _ _ _ _ n hn
  · intro _ k hk
    rw [(extendField_slice_eventuallyEq A.scale_pos hx0 hη c.seedF).iteratedDeriv_eq k]
    exact hj.angular _ hx0 eta hη k hk
  · intro hX e
    simp only [extendField, radialClamp_eq A.scale_pos hx0, extendParameter]
    exact c.seedF_held hX (parameterClamp_mem e)
  · intro k hk
    rw [(extendParameter_eventuallyEq hη c.initialShape).iteratedDeriv_eq k]
    exact hj.logarithm eta hη k hk
  · exact hshape eta hη

theorem extendedDebt_bound {N : ℕ} {B K BJ BG KA delta : ℝ}
    (hj : SeedJets c N B K BJ) (hB : 0 ≤ B) (hK : 0 ≤ K) (hBJ : 1 ≤ BJ)
    (hBG : 0 ≤ BG) (hKA : 0 ≤ KA) (hd : 0 ≤ delta) (hC : 1 ≤ A.normalization)
    (hsep : c.separation ≤ Real.exp (-8))
    (hshape : ∀ eta ∈ Icc (-1 : ℝ) 1, ∀ n ≤ N,
      |iteratedDeriv n ShapeTransition.logShape eta| ≤ BJ)
    (hG : ∀ eta ∈ Icc (-1 : ℝ) 1, ∀ n ≤ N,
      |iteratedDeriv n (fun e : ℝ => 4 * e) eta| ≤ BG)
    (hA : ∀ eta ∈ Icc (-1 : ℝ) 1, ∀ n ≤ N,
      |iteratedDeriv n (NominalProfile.idealAmplitude F) eta| ≤ KA)
    (hdef : ∀ eta ∈ Icc (-1 : ℝ) 1, ∀ n ≤ N,
      |iteratedDeriv n (fun e => c.initialAxial e - 4 * e) eta| ≤ delta)
    {n : ℕ} (hn : n ≤ N) {eta : ℝ} (hη : eta ∈ Icc (-1 : ℝ) 1) :
    ‖iteratedFDeriv ℝ n (extendedDebt c) eta‖ ≤
      ShapeTransition.vanishingDebtBound n B
        (ShapeTransition.shapeJetConstant N NominalProfile.Xi c.shapeTime BJ K)
        (NominalProfile.Xi * Real.exp c.shapeTime) BG KA c.separation A.normalization +
      ShapeTransition.restorationBound n BG KA delta := by
  have hrb : c.separation ≤ NominalProfile.matchFraction :=
    hsep.trans (Real.exp_le_exp.mpr (by norm_num : (-8 : ℝ) ≤ -5))
  apply (resetVector_jet_bound c.radius_pos.le c.separation_pos hrb
    (extendedU_smooth c) (extendedF_smooth c) (extendParameter_smooth c.initialAxial_smooth)
    (NominalProfile.idealAmplitude_smooth F) n eta).trans
  apply ShapeTransition.resetDebtJetSize_bound c.radius_pos.le c.separation_pos hrb
    NominalProfile.matchFraction_lt_one.le (radius_mul_separation c) hB
    (ShapeTransition.shapeJetConstant_nonneg N (zero_le_one.trans hBJ) hK) hC hBG hKA hd
    (extendedU_smooth c) (extendedF_smooth c) (extendParameter_smooth c.initialAxial_smooth)
    (NominalProfile.idealAmplitude_smooth F) n eta
  · intro x hx k hk
    exact extendedU_jets c hj hη hx.1.le (hk.trans hn)
  · intro x hx k hk
    exact extendedF_jets c hj hBJ hK hshape hη ⟨hx.1.le, hx.2⟩ (hk.trans hn)
  · exact fun k hk => hG eta hη k (hk.trans hn)
  · exact fun k hk => hA eta hη k (hk.trans hn)
  · intro k hk
    have he : (fun e => extendParameter c.initialAxial e - 4 * e) =ᶠ[𝓝 eta]
        (fun e => c.initialAxial e - 4 * e) :=
      (extendParameter_eventuallyEq hη c.initialAxial).sub EventuallyEq.rfl
    rw [he.iteratedDeriv_eq k]
    exact hdef eta hη k (hk.trans hn)

end ActualFields

/-! ## A finite-order budget, with separate vanishing and drift terms -/

/-- Vanishing sum, given by `∑ n ∈ Finset.range (N + 1), |ShapeTransition.vanishingDebtBound n B
K L BG KA (ShapeTransition.separation T C P) C|`. -/
noncomputable def vanishingSum (N : ℕ) (B K L BG KA T P C : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    |ShapeTransition.vanishingDebtBound n B K L BG KA (ShapeTransition.separation T C P) C|

theorem vanishingSum_nonneg (N : ℕ) (B K L BG KA T P C : ℝ) :
    0 ≤ vanishingSum N B K L BG KA T P C :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem vanishing_le_sum {N n : ℕ} (hn : n ≤ N) (B K L BG KA T P C : ℝ) :
    ShapeTransition.vanishingDebtBound n B K L BG KA (ShapeTransition.separation T C P) C ≤
      vanishingSum N B K L BG KA T P C := by
  apply (le_abs_self _).trans
  exact Finset.single_le_sum
    (f := fun n => |ShapeTransition.vanishingDebtBound n B K L BG KA (ShapeTransition.separation T
        C P) C|)
    (fun _ _ => abs_nonneg _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))

theorem vanishingSum_tendsto (N : ℕ) (B K L BG KA T : ℝ) {P : ℝ} (hP : P ≠ 0) :
    Tendsto (vanishingSum N B K L BG KA T P) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (Finset.range (N + 1)) (fun n _ =>
    (ShapeTransition.vanishingDebtBound_tendsto n B K L BG KA T hP).abs)
  unfold vanishingSum
  simpa only [abs_zero, Finset.sum_const_zero] using h

/-- Drift factor, given by `1 + 2 * (2 ^ N * KA) + 2 ^ N * (1 + 2 * BG)`. -/
noncomputable def driftFactor (N : ℕ) (BG KA : ℝ) : ℝ :=
  1 + 2 * (2 ^ N * KA) + 2 ^ N * (1 + 2 * BG)

theorem driftFactor_pos (N : ℕ) {BG KA : ℝ} (hBG : 0 ≤ BG) (hKA : 0 ≤ KA) :
    0 < driftFactor N BG KA := by unfold driftFactor; positivity

theorem restoration_le_linear {N n : ℕ} (hn : n ≤ N) {BG KA delta : ℝ}
    (hBG : 0 ≤ BG) (hKA : 0 ≤ KA) (hd : 0 ≤ delta) (hd1 : delta ≤ 1) :
    ShapeTransition.restorationBound n BG KA delta ≤ delta * driftFactor N BG KA := by
  have hp : (2 : ℝ) ^ n ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hn
  unfold ShapeTransition.restorationBound driftFactor
  gcongr

theorem compact_scalar_jets {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (N : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ eta ∈ Icc (-1 : ℝ) 1, ∀ n ≤ N, |iteratedDeriv n g eta| ≤ B := by
  obtain ⟨B, hB, hb⟩ := FiveProfileMoments.compact_global_jet_bound (Icc (-1 : ℝ) 1) isCompact_Icc
      hg N
  refine ⟨max B 1, le_max_right _ _, ?_⟩
  intro eta hη n hn
  have h := hb n hn eta hη
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

/-- These constants depend only on the already fixed outgoing witness and
the requested finite order.  In particular they precede `j`, `Λ`, and `C`. -/
structure FixedBounds (F : OutgoingProfile.Profile) (N : ℕ) where
  /-- Normalizer of `FixedBounds`, of type `ℝ`. -/
  normalizer : ℝ
  normalizer_pos : 0 < normalizer
  normalize : ∀ d : ℝ → Debt, ContDiff ℝ ∞ d → ∀ D : ℝ, 0 ≤ D →
    JetBounds.FiniteJetBound N d (Icc (-1 : ℝ) 1) D →
    JetBounds.FiniteJetBound N (NominalProfile.normalizedDebt F d) (Icc (-1 : ℝ) 1) (normalizer * D)
  /-- Axial of `FixedBounds`, of type `ℝ`. -/
  axial : ℝ
  /-- Angular of `FixedBounds`, of type `ℝ`. -/
  angular : ℝ
  /-- Logarithm of `FixedBounds`, of type `ℝ`. -/
  logarithm : ℝ
  axial_one : 1 ≤ axial
  angular_one : 1 ≤ angular
  logarithm_one : 1 ≤ logarithm
  axial_jets : ∀ eta ∈ Icc (-1 : ℝ) 1, ∀ n ≤ N,
    |iteratedDeriv n (fun e : ℝ => 4 * e) eta| ≤ axial
  angular_jets : ∀ eta ∈ Icc (-1 : ℝ) 1, ∀ n ≤ N,
    |iteratedDeriv n (NominalProfile.idealAmplitude F) eta| ≤ angular
  logarithm_jets : ∀ eta ∈ Icc (-1 : ℝ) 1, ∀ n ≤ N,
    |iteratedDeriv n ShapeTransition.logShape eta| ≤ logarithm

theorem fixedBounds_exists (F : OutgoingProfile.Profile) (N : ℕ) : Nonempty (FixedBounds F N) := by
  obtain ⟨K, hK, hnorm⟩ := FiveProfileMoments.compact_normalizedDebt_jets
    (Icc (-1 : ℝ) 1) isCompact_Icc (NominalProfile.idealAmplitude_smooth F)
    NominalProfile.idealU_smooth (fun e => (NominalProfile.idealAmplitude_pos F e).ne') N
  obtain ⟨BG, hBG, hG⟩ := compact_scalar_jets (contDiff_const.mul contDiff_id :
    ContDiff ℝ ∞ (fun e : ℝ => 4 * e)) N
  obtain ⟨KA, hKA, hA⟩ := compact_scalar_jets (NominalProfile.idealAmplitude_smooth F) N
  obtain ⟨BJ, hBJ, hJ⟩ := compact_scalar_jets ShapeTransition.logShape_contDiff N
  exact ⟨⟨K, hK, hnorm, BG, KA, BJ, hBG, hKA, hBJ, hG, hA, hJ⟩⟩

/-- Fixed bounds, given by `Classical.choice (fixedBounds_exists F N)`. -/
noncomputable def fixedBounds (F : OutgoingProfile.Profile) (N : ℕ) : FixedBounds F N :=
  Classical.choice (fixedBounds_exists F N)

/-- Prefix budget, constructed using `vanishingSum`. -/
noncomputable def prefixBudget {F : OutgoingProfile.Profile} {N : ℕ} (q : FixedBounds F N)
    (B K BJ T C : ℝ) : ℝ :=
  vanishingSum N B (ShapeTransition.shapeJetConstant N NominalProfile.Xi T BJ K)
    (NominalProfile.Xi * Real.exp T) q.axial q.angular T F.data.core.P C

theorem prefixBudget_nonneg {F : OutgoingProfile.Profile} {N : ℕ} (q : FixedBounds F N)
    (B K BJ T C : ℝ) : 0 ≤ prefixBudget q B K BJ T C := vanishingSum_nonneg _ _ _ _ _ _ _ _ _

theorem prefixBudget_tendsto {F : OutgoingProfile.Profile} {N : ℕ} (q : FixedBounds F N)
    (B K BJ T : ℝ) : Tendsto (prefixBudget q B K BJ T) atTop (𝓝 0) :=
  vanishingSum_tendsto _ _ _ _ _ _ _ F.data.core.P_pos.ne'

theorem normalized_actual_debt_bound {F : OutgoingProfile.Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) {N : ℕ} (q : FixedBounds F N) {B K BJ delta : ℝ}
    (hj : SeedJets c N B K BJ) (hB : 0 ≤ B) (hK : 0 ≤ K) (hBJ : 1 ≤ BJ)
    (hqJ : q.logarithm ≤ BJ) (hd : 0 ≤ delta) (hd1 : delta ≤ 1)
    (hC : 1 ≤ A.normalization) (hsep : c.separation ≤ Real.exp (-8))
    (hdef : ∀ eta ∈ Icc (-1 : ℝ) 1, ∀ n ≤ N,
      |iteratedDeriv n (fun e => c.initialAxial e - 4 * e) eta| ≤ delta) :
    JetBounds.FiniteJetBound N (NominalProfile.normalizedDebt F c.debt) (Icc (-1 : ℝ) 1)
      (q.normalizer * (prefixBudget q B K BJ c.shapeTime A.normalization +
        delta * driftFactor N q.axial q.angular)) := by
  let D := prefixBudget q B K BJ c.shapeTime A.normalization + delta * driftFactor N q.axial
      q.angular
  have hD : 0 ≤ D := add_nonneg (prefixBudget_nonneg q _ _ _ _ _)
    (mul_nonneg hd (driftFactor_pos N (zero_le_one.trans q.axial_one) (zero_le_one.trans
        q.angular_one)).le)
  have hraw : JetBounds.FiniteJetBound N (fun e => -extendedDebt c e) (Icc (-1 : ℝ) 1) D := by
    intro n hn eta hη
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_fun_neg, norm_neg,
      ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    apply (extendedDebt_bound c hj hB hK hBJ (zero_le_one.trans q.axial_one)
      (zero_le_one.trans q.angular_one) hd hC hsep
      (fun e he k hk => (q.logarithm_jets e he k hk).trans hqJ)
      q.axial_jets q.angular_jets hdef hn hη).trans
    exact add_le_add (vanishing_le_sum hn _ _ _ _ _ _ _ _)
      (restoration_le_linear hn (zero_le_one.trans q.axial_one) (zero_le_one.trans q.angular_one)
          hd hd1)
  have hnorm := q.normalize (fun e => -extendedDebt c e) (extendedDebt_smooth c hsep).neg D hD hraw
  intro n hn eta hη
  have he : NominalProfile.normalizedDebt F c.debt =ᶠ[𝓝 eta]
      NominalProfile.normalizedDebt F (fun e => -extendedDebt c e) := by
    filter_upwards [debt_eventuallyEq_negative_extended c hsep hη] with e he
    simp only [NominalProfile.normalizedDebt, he]
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, he.iteratedDeriv_eq n,
    ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact hnorm n hn eta hη

/-- Small control, given by `c.reference.SmallLogControl (Icc (-1 : ℝ) 1) N eps c.activationTime
c.kappa c.axialWidth c.angularWidth`. -/
noncomputable def SmallControl {F : OutgoingProfile.Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) (N : ℕ) (eps : ℝ) : Prop :=
  c.reference.SmallLogControl (Icc (-1 : ℝ) 1) N eps
    c.activationTime c.kappa c.axialWidth c.angularWidth

theorem SmallControl.mono {F : OutgoingProfile.Profile} {A : NominalProfile.AxisStage F}
    {c : NominalProfile.Controls A} {N : ℕ} {eps eps' : ℝ}
    (hc : SmallControl c N eps) (he : eps ≤ eps') : SmallControl c N eps' :=
  TransitionRamp.StockReference.SmallLogControl.mono_tolerance c.reference hc he

theorem SmallControl.of_le {F : OutgoingProfile.Profile} {A : NominalProfile.AxisStage F}
    {c : NominalProfile.Controls A} {N M : ℕ} {eps : ℝ}
    (hc : SmallControl c M eps) (hNM : N ≤ M) : SmallControl c N eps where
  finish_before := hc.finish_before
  axial_jets := fun y hy eta hη n hn => hc.axial_jets y hy eta hη n (hn.trans hNM)
  positive_log_jets := fun y hy eta hη n hn hn0 =>
    hc.positive_log_jets y hy eta hη n (hn.trans hNM) hn0
  log_value := hc.log_value

theorem actual_endpoint_drift {F : OutgoingProfile.Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) {N : ℕ} {eps : ℝ} (hc : SmallControl c N eps)
    {eta : ℝ} (hη : eta ∈ Icc (-1 : ℝ) 1) {n : ℕ} (hn : n ≤ N) :
    |iteratedDeriv n (fun e => c.initialAxial e - 4 * e) eta| ≤
      ReferenceJetBounds.jetConstant A.preparation.inputs.coefficients 0 n / A.scale + eps + |A.j|
          :=
  TransitionRamp.endpointU_four_eta_jet_bound A.preparation.inputs A.scale_pos A.small
    F.axisDatum_contDiff A.natural.profile c.referenceWidth_pos c.referenceWidth_small
    c.reference_before_big.le hc hn hη

/-- Drift budget, given by `min 1 (rho / (4 * (q.normalizer * driftFactor N q.axial
q.angular)))`. -/
noncomputable def driftBudget {F : OutgoingProfile.Profile} {N : ℕ}
    (q : FixedBounds F N) (rho : ℝ) : ℝ :=
  min 1 (rho / (4 * (q.normalizer * driftFactor N q.axial q.angular)))

theorem driftBudget_pos {F : OutgoingProfile.Profile} {N : ℕ}
    (q : FixedBounds F N) {rho : ℝ} (hrho : 0 < rho) : 0 < driftBudget q rho := by
  have hd := driftFactor_pos N (zero_le_one.trans q.axial_one) (zero_le_one.trans q.angular_one)
  exact lt_min zero_lt_one (div_pos hrho (mul_pos (by norm_num) (mul_pos q.normalizer_pos hd)))

theorem driftBudget_le_one {F : OutgoingProfile.Profile} {N : ℕ}
    (q : FixedBounds F N) (rho : ℝ) : driftBudget q rho ≤ 1 := min_le_left _ _

theorem driftBudget_weighted {F : OutgoingProfile.Profile} {N : ℕ}
    (q : FixedBounds F N) (rho : ℝ) :
    q.normalizer * (driftBudget q rho * driftFactor N q.axial q.angular) ≤ rho / 4 := by
  have hd := driftFactor_pos N (zero_le_one.trans q.axial_one) (zero_le_one.trans q.angular_one)
  have hm := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) (mul_pos q.normalizer_pos hd))).mp
    (min_le_right 1 (rho / (4 * (q.normalizer * driftFactor N q.axial q.angular))))
  change driftBudget q rho * (4 * (q.normalizer * driftFactor N q.axial q.angular)) ≤ rho at hm
  linarith

theorem normalized_debt_small_of_budgets {F : OutgoingProfile.Profile} {A :
    NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) {N : ℕ} (q : FixedBounds F N) {B K BJ rho : ℝ}
    (hj : SeedJets c N B K BJ) (hB : 0 ≤ B) (hK : 0 ≤ K) (hBJ : 1 ≤ BJ)
    (hqJ : q.logarithm ≤ BJ) (hrho : 0 < rho)
    (hC : 1 ≤ A.normalization) (hsep : c.separation ≤ Real.exp (-8))
    (hp : prefixBudget q B K BJ c.shapeTime A.normalization < rho / (4 * q.normalizer))
    (hdef : ∀ eta ∈ Icc (-1 : ℝ) 1, ∀ n ≤ N,
      |iteratedDeriv n (fun e => c.initialAxial e - 4 * e) eta| ≤ driftBudget q rho) :
    ∀ n ≤ N, ∀ eta ∈ Icc (-1 : ℝ) 1,
      ‖iteratedFDeriv ℝ n (NominalProfile.normalizedDebt F c.debt) eta‖ < rho := by
  have hb := normalized_actual_debt_bound c q hj hB hK hBJ hqJ
    (driftBudget_pos q hrho).le (driftBudget_le_one q rho) hC hsep hdef
  have hpre : q.normalizer * prefixBudget q B K BJ c.shapeTime A.normalization < rho / 4 := by
    have hh := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) q.normalizer_pos)).mp hp
    linarith
  have hrest := driftBudget_weighted q rho
  intro n hn eta hη
  exact (hb n hn eta hη).trans_lt (by linarith)

/-- Matching bounds data, collecting `separation`, `normalized_jets`, `shape_slope`. -/
structure MatchingBounds {F : OutgoingProfile.Profile} {A : NominalProfile.AxisStage F}
    (c : NominalProfile.Controls A) (N : ℕ) (rho : ℝ) : Prop where
  separation : c.separation < Real.exp (-8)
  normalized_jets : ∀ n ≤ N, ∀ eta ∈ Icc (-1 : ℝ) 1,
    ‖iteratedFDeriv ℝ n (NominalProfile.normalizedDebt F c.debt) eta‖ < rho
  shape_slope : ∀ y : ℝ, ∀ eta ∈ Icc (-1 : ℝ) 1,
    11 / 20 ≤ 1 / 2 + deriv (fun s => ShapeTransition.logProfile A.normalization c.shapeTime
      c.initialShape (s, eta)) y ∧
    1 / 2 + deriv (fun s => ShapeTransition.logProfile A.normalization c.shapeTime
      c.initialShape (s, eta)) y ≤ 13 / 20

theorem MatchingBounds.smallDebt {F : OutgoingProfile.Profile} {A : NominalProfile.AxisStage F}
    {c : NominalProfile.Controls A} {N : ℕ} {rho : ℝ} (hb : MatchingBounds c N rho)
    (hr : rho ≤ NominalProfile.resetSolver.radius) {eta : ℝ} (hη : eta ∈ Icc (-1 : ℝ) 1) :
    NominalProfile.SmallDebt F c.debt eta := by
  have hh := hb.normalized_jets 0 (Nat.zero_le _) eta hη
  rw [norm_iteratedFDeriv_zero] at hh
  exact hh.trans_le hr

theorem MatchingBounds.of_heq {F : OutgoingProfile.Profile}
    {A B : NominalProfile.AxisStage F} {c : NominalProfile.Controls A} {d : NominalProfile.Controls
        B}
    {N : ℕ} {rho : ℝ} (hb : MatchingBounds c N rho) (hA : B = A) (hc : HEq d c) :
    MatchingBounds d N rho := by
  cases hA
  cases hc
  exact hb

theorem shapeTime_eq_of_heq {F : OutgoingProfile.Profile}
    {A B : NominalProfile.AxisStage F} {c : NominalProfile.Controls A} {d : NominalProfile.Controls
        B}
    (hA : B = A) (hc : HEq d c) : d.shapeTime = c.shapeTime := by
  cases hA
  cases hc
  rfl

/-- Actual finite jets of the coefficients produced by the fixed nonlinear
inverse.  The constant depends only on the requested order and that inverse.
The debt hypothesis is fulfilled by the ordered construction below, with the
target chosen to be `tau^(N+1)`. -/
theorem resetCoefficients_jet_control (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {F : OutgoingProfile.Profile} {A : NominalProfile.AxisStage F},
      ∀ c : NominalProfile.Controls A, c.separation ≤ Real.exp (-8) →
      ∀ tau : ℝ, 0 < tau → tau ≤ min 1 (NominalProfile.resetSolver.radius / 2) →
      JetBounds.FiniteJetBound N (NominalProfile.normalizedDebt F c.debt)
        (Icc (-1 : ℝ) 1) (tau ^ (N + 1)) →
      JetBounds.FiniteJetBound N (NominalProfile.resetCoefficients F c.debt)
        (Icc (-1 : ℝ) 1) (K * tau) := by
  obtain ⟨K, hK, hsolver⟩ := FiveProfileMoments.smooth_solver_parameter_jets
    NominalProfile.resetSolver.radius_pos NominalProfile.resetSolver.bound_pos
    NominalProfile.resetSolver.smooth NominalProfile.resetSolver.norm_bound N
  refine ⟨K, hK, ?_⟩
  intro F A c hsep tau htau hmax hdebt n hn eta hη
  let f := NominalProfile.normalizedDebt F (fun e => -extendedDebt c e)
  have hf : ContDiff ℝ ∞ f :=
    FiveProfileMoments.normalizedDebt_contDiff (NominalProfile.idealAmplitude_smooth F)
      NominalProfile.idealU_smooth (extendedDebt_smooth c hsep).neg
      (fun e => (NominalProfile.idealAmplitude_pos F e).ne')
  have he : NominalProfile.normalizedDebt F c.debt =ᶠ[𝓝 eta] f := by
    filter_upwards [debt_eventuallyEq_negative_extended c hsep hη] with e he
    simp only [f, NominalProfile.normalizedDebt, he]
  have hfj : ∀ k ≤ N, ‖iteratedFDeriv ℝ k f eta‖ ≤ tau ^ (N + 1) := by
    intro k hk
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← he.iteratedDeriv_eq k,
      ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hdebt k hk eta hη
  have hec : NominalProfile.resetCoefficients F c.debt =ᶠ[𝓝 eta]
      (NominalProfile.resetSolver.solve ∘ f) := he.fun_comp NominalProfile.resetSolver.solve
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hec.iteratedDeriv_eq n,
    ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact hsolver f hf tau eta htau hmax hfj n hn

/-- The thresholds hold for every incoming coefficient solution and every
later control choice satisfying the displayed actual log-control estimate.
Thus no new incoming profile is selected when a smaller control tolerance is
required by another part of the construction. -/
theorem exists_ordered_matching_threshold (F : OutgoingProfile.Profile) (N : ℕ)
    {rho : ℝ} (hrho : 0 < rho) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧
      ∀ j : ℝ, |j| ≤ eps → ∀ hj : NaturalAxisData.SmallParameters F.data.h j,
      ∀ prep : NominalProfile.AxisPreparation F j,
      ∃ Λ0 : ℝ, 1 ≤ Λ0 ∧ prep.scaleBound ≤ Λ0 ∧
        ∀ Λ : ℝ, ∀ hΛlarge : prep.scaleBound ≤ Λ, Λ0 ≤ Λ →
        ∃ T : ℝ, 0 < T ∧ ∃ C0 : ℝ, 1 ≤ C0 ∧
          NaturalEntrance.entranceNormalization prep.inputs Λ prep.delta ≤ C0 ∧
          ∀ C : ℝ, ∀ hClarge : NaturalEntrance.entranceNormalization prep.inputs Λ prep.delta ≤ C,
          C0 ≤ C → ∀ E : NaturalEntrance.EntranceProfile prep.inputs Λ C,
          ∀ c : NominalProfile.Controls (NominalProfile.AxisStage.ofEntrance hj prep Λ C hΛlarge
              hClarge E),
          c.shapeTime = T → SmallControl c N eps → MatchingBounds c N rho := by
  let q := fixedBounds F N
  let delta := driftBudget q rho
  have hd : 0 < delta := driftBudget_pos q hrho
  have hd1 : delta ≤ 1 := driftBudget_le_one q rho
  let eps := delta / 3
  have heps : 0 < eps := by dsimp [eps]; positivity
  have heps1 : eps ≤ 1 := by dsimp [eps]; linarith
  refine ⟨eps, heps, heps1, ?_⟩
  intro j hjbound hj prep
  obtain ⟨D, hD, hDb⟩ := TransitionRamp.finite_majorant
    (fun n => ReferenceJetBounds.jetConstant prep.inputs.coefficients 0 n) N
  let naturalScale := AxisReference.stabilityScale prep.inputs.coefficients.epsilon
    (NaturalProfile.profileErrorConstant prep.inputs)
  let Λ0 := max (max (max 1 prep.scaleBound) naturalScale) (3 * D / delta)
  have hL1 : 1 ≤ Λ0 := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hLprep : prep.scaleBound ≤ Λ0 :=
    (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨Λ0, hL1, hLprep, ?_⟩
  intro Λ hΛlarge hΛ0
  have hΛ : 0 < Λ := zero_lt_one.trans_le (hL1.trans hΛ0)
  have hnatural : naturalScale ≤ Λ := (le_max_right _ _).trans ((le_max_left _ _).trans hΛ0)
  have hLD : 3 * D / delta ≤ Λ := (le_max_right _ _).trans hΛ0
  have hcoef (n : ℕ) (hn : n ≤ N) :
      ReferenceJetBounds.jetConstant prep.inputs.coefficients 0 n / Λ ≤ delta / 3 := by
    apply (div_le_iff₀ hΛ).mpr
    have hm := (div_le_iff₀ hd).mp hLD
    linarith [hDb n hn]
  obtain ⟨B, hB, K, hK, BJ0, hBJ0, hseed⟩ := TransitionRamp.ordered_seed_bounds
    prep.inputs hΛ hj prep.sigma_pos hnatural F.axisDatum_contDiff N
  let BJ := max BJ0 q.logarithm
  have hBJ : 1 ≤ BJ := hBJ0.trans (le_max_left _ _)
  have hqJ : q.logarithm ≤ BJ := le_max_right _ _
  obtain ⟨T, hT, hslopes⟩ := ShapeTransition.exists_duration (2 * BJ) (by positivity)
  have hpre : ∀ᶠ C : ℝ in atTop, prefixBudget q B K BJ T C < rho / (4 * q.normalizer) :=
    (prefixBudget_tendsto q B K BJ T).eventually
      (gt_mem_nhds (div_pos hrho (by have := q.normalizer_pos; positivity)))
  have hsep := ShapeTransition.separation_eventually_before T F.data.core.P_pos (-8)
  obtain ⟨Cmin, hmin⟩ := eventually_atTop.mp (hpre.and hsep)
  let C0 := max (max 1 (NaturalEntrance.entranceNormalization prep.inputs Λ prep.delta)) Cmin
  have hC01 : 1 ≤ C0 := (le_max_left _ _).trans (le_max_left _ _)
  have hC0norm : NaturalEntrance.entranceNormalization prep.inputs Λ prep.delta ≤ C0 :=
    (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨T, hT, C0, hC01, hC0norm, ?_⟩
  intro C hClarge hC0 E c hcT hc
  have hC1 : 1 ≤ C := hC01.trans hC0
  have hCpos : 0 < C := zero_lt_one.trans_le hC1
  have hlarge := hmin C ((le_max_right _ _).trans hC0)
  have hfields := hseed C hCpos E.profile c.referenceWidth c.referenceWidth_pos
      c.referenceWidth_small
    c.activationTime c.kappa c.axialWidth c.angularWidth c.before_big c.axialWidth_pos
    c.angularWidth_pos (hc.mono heps1)
  have hsj : SeedJets c N B K BJ := by
    refine ⟨?_, ?_, ?_⟩
    · intro X hX eta hη n hn
      exact (hfields.1 X hX eta hη n hn).2
    · intro X hX eta hη n hn
      exact (hfields.1 X hX eta hη n hn).1
    · intro eta hη n hn
      exact (hfields.2 eta hη n hn).1.trans (le_max_left _ _)
  have hcsep : c.separation < Real.exp (-8) := by
    simp only [NominalProfile.Controls.separation, hcT]
    exact hlarge.2
  have hcp : prefixBudget q B K BJ c.shapeTime C < rho / (4 * q.normalizer) := by
    simpa only [hcT] using hlarge.1
  have hdef : ∀ eta ∈ Icc (-1 : ℝ) 1, ∀ n ≤ N,
      |iteratedDeriv n (fun e => c.initialAxial e - 4 * e) eta| ≤ driftBudget q rho := by
    intro eta hη n hn
    have hh := actual_endpoint_drift c hc hη hn
    change _ ≤ ReferenceJetBounds.jetConstant prep.inputs.coefficients 0 n / Λ + eps + |j| at hh
    apply hh.trans
    change ReferenceJetBounds.jetConstant prep.inputs.coefficients 0 n / Λ + eps + |j| ≤ delta
    have hjb : |j| ≤ delta / 3 := hjbound
    dsimp [eps]
    linarith [hcoef n hn]
  refine ⟨hcsep, normalized_debt_small_of_budgets c q hsj (zero_le_one.trans hB)
    (zero_le_one.trans hK) hBJ hqJ hrho hC1 hcsep.le hcp hdef, ?_⟩
  intro y eta hη
  have hli := hsj.logarithm eta hη 0 (Nat.zero_le _)
  have hlog := (q.logarithm_jets eta hη 0 (Nat.zero_le _)).trans hqJ
  simp only [iteratedDeriv_zero] at hli hlog
  have hdata : |ShapeTransition.logShape eta - c.initialShape eta| ≤ 2 * BJ :=
    (abs_sub _ _).trans (by linarith)
  simp only [hcT]
  exact hslopes c.initialShape C y eta hdata

/-- Ordered existence with the exact entrance profile produced by the actual
activation-continuation theorem.  The profile is chosen before the final
control order and tolerance.  The same controls retain the continuation cone,
the physical and logarithmic estimates, and the matching-debt bounds. -/
theorem exists_ordered_matching_continuation (F : OutgoingProfile.Profile) (N : ℕ)
    {rho : ℝ} (hrho : 0 < rho) (hradius : rho ≤ NominalProfile.resetSolver.radius) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧
      ∀ j : ℝ, |j| ≤ eps → ∀ hj : NaturalAxisData.SmallParameters F.data.h j,
      ∀ prep : NominalProfile.AxisPreparation F j,
      ∀ nu : ℝ, 0 < nu →
      (∀ eta ∈ Icc (-1 : ℝ) 1, |NaturalAxisData.Z F.data.h j F.axisDatum eta| ≤ nu →
        99 / 100 < NaturalAxisData.chi F.data.h j prep.sigma eta) →
      ∃ Λ0 : ℝ, 1 ≤ Λ0 ∧ ∀ Λ : ℝ, ∀ hΛ : 0 < Λ, Λ0 ≤ Λ →
        ∃ T : ℝ, ∃ hT : 0 < T, ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ C : ℝ, C0 ≤ C →
          ∃ hΛlarge : prep.scaleBound ≤ Λ,
          ∃ hClarge : NaturalEntrance.entranceNormalization prep.inputs Λ prep.delta ≤ C,
          ∃ E : NaturalEntrance.EntranceProfile prep.inputs Λ C,
          ∀ J : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
            ∃ w : ActivationContinuation.ContinuationWitness E hΛ hj F.axisDatum_contDiff
              (max N J) (min eps epsilon),
              let A := NominalProfile.AxisStage.ofEntrance hj prep Λ C hΛlarge hClarge E
              let c := NominalProfile.Controls.ofContinuation A w T hT
              MatchingBounds c N rho ∧
                ∀ eta ∈ Icc (-1 : ℝ) 1, NominalProfile.SmallDebt F c.debt eta := by
  obtain ⟨eps, heps, heps1, hthreshold⟩ := exists_ordered_matching_threshold F N hrho
  refine ⟨eps, heps, heps1, ?_⟩
  intro j hjbound hj prep nu hnu hcut
  obtain ⟨L0, hL0, hLprep, hmatch⟩ := hthreshold j hjbound hj prep
  obtain ⟨M, hM, hcontinue⟩ := ActivationContinuation.exists_activation_continuation
    prep.inputs hj prep.sigma_pos F.axisDatum_contDiff hnu hcut
  refine ⟨max L0 M, hL0.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ hΛ0
  have hLΛ : L0 ≤ Λ := (le_max_left _ _).trans hΛ0
  have hΛlarge : prep.scaleBound ≤ Λ := hLprep.trans hLΛ
  obtain ⟨T, hT, Cmatch, hCmatch, hCnorm, hmatchC⟩ := hmatch Λ hΛlarge hLΛ
  obtain ⟨Ccontinue, hCcontinue, hcontinueC⟩ :=
    hcontinue Λ hΛ ((le_max_right _ _).trans hΛ0)
  refine ⟨T, hT, max Cmatch Ccontinue, hCmatch.trans (le_max_left _ _), ?_⟩
  intro C hC0
  have hCm : Cmatch ≤ C := (le_max_left _ _).trans hC0
  have hClarge : NaturalEntrance.entranceNormalization prep.inputs Λ prep.delta ≤ C := hCnorm.trans
      hCm
  obtain ⟨E, hE⟩ := hcontinueC C ((le_max_right _ _).trans hC0)
  refine ⟨hΛlarge, hClarge, E, ?_⟩
  intro J epsilon hepsilon
  obtain ⟨w⟩ := hE (max N J) (min eps epsilon) (lt_min heps hepsilon)
  let A := NominalProfile.AxisStage.ofEntrance hj prep Λ C hΛlarge hClarge E
  let c := NominalProfile.Controls.ofContinuation A w T hT
  have hc : SmallControl c (max N J) (min eps epsilon) := w.logarithmic_control
  have hm : MatchingBounds c N rho :=
    hmatchC C hClarge hCm E c rfl ((hc.of_le (le_max_left _ _)).mono (min_le_left _ _))
  exact ⟨w, hm, fun _ hη => hm.smallDebt hradius hη⟩

/-- The late heat-completion radius is met by increasing the same `C` before
selecting the entrance profile.  The assembled witness keeps that profile and
its exact continuation controls.  No separation or final-debt hypothesis is
left as an input. -/
theorem exists_ordered_assembled_profile {F : OutgoingProfile.Profile} {D : ℝ}
    (hF : OutgoingProfile.Specification F D) (N : ℕ)
    {rho : ℝ} (hrho : 0 < rho) (hradius : rho ≤ NominalProfile.resetSolver.radius) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧
      ∀ j : ℝ, |j| ≤ eps → ∀ hj : NaturalAxisData.SmallParameters F.data.h j,
      ∀ prep : NominalProfile.AxisPreparation F j,
      ∀ nu : ℝ, 0 < nu →
      (∀ eta ∈ Icc (-1 : ℝ) 1, |NaturalAxisData.Z F.data.h j F.axisDatum eta| ≤ nu →
        99 / 100 < NaturalAxisData.chi F.data.h j prep.sigma eta) →
      ∃ Λ0 : ℝ, 1 ≤ Λ0 ∧ ∀ Λ : ℝ, ∀ hΛ : 0 < Λ, Λ0 ≤ Λ →
        ∃ T : ℝ, ∃ hT : 0 < T, ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ C : ℝ, C0 ≤ C →
          ∃ hΛlarge : prep.scaleBound ≤ Λ,
          ∃ hClarge : NaturalEntrance.entranceNormalization prep.inputs Λ prep.delta ≤ C,
          ∃ E : NaturalEntrance.EntranceProfile prep.inputs Λ C,
          ∀ J : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
            ∃ w : ActivationContinuation.ContinuationWitness E hΛ hj F.axisDatum_contDiff
              (max N J) (min eps epsilon),
            ∃ W : NominalProfile.Witness F,
              let A := NominalProfile.AxisStage.ofEntrance hj prep Λ C hΛlarge hClarge E
              let c := NominalProfile.Controls.ofContinuation A w T hT
              W.axis = A ∧ HEq W.controls c ∧ MatchingBounds W.controls N rho := by
  obtain ⟨eps, heps, heps1, hmatched⟩ := exists_ordered_matching_continuation F N hrho hradius
  obtain ⟨R0, _hR0, hassemble⟩ := NominalProfile.exists_assembly_threshold_preserving hF
  refine ⟨eps, heps, heps1, ?_⟩
  intro j hjbound hj prep nu hnu hcut
  obtain ⟨Λ0, hΛ0, hscale⟩ := hmatched j hjbound hj prep nu hnu hcut
  refine ⟨Λ0, hΛ0, ?_⟩
  intro Λ hΛ hΛlarge
  obtain ⟨T, hT, Cbase, hCbase, hnormalization⟩ := hscale Λ hΛ hΛlarge
  obtain ⟨Cgeo, hgeo⟩ := eventually_atTop.mp
    (NominalProfile.eventually_matching_geometry F T R0 Cbase)
  refine ⟨T, hT, max Cbase Cgeo, hCbase.trans (le_max_left _ _), ?_⟩
  intro C hC
  have hCb : Cbase ≤ C := (le_max_left _ _).trans hC
  have hCg := hgeo C ((le_max_right _ _).trans hC)
  obtain ⟨hL, hCl, E, hcontrols⟩ := hnormalization C hCb
  refine ⟨hL, hCl, E, ?_⟩
  intro J epsilon hepsilon
  obtain ⟨w, hmatch, hsmall⟩ := hcontrols J epsilon hepsilon
  let A := NominalProfile.AxisStage.ofEntrance hj prep Λ C hL hCl E
  let c := NominalProfile.Controls.ofContinuation A w T hT
  have hR : R0 ≤ c.radius := hCg.2.2.1.le
  obtain ⟨W, hWA, hWc⟩ := hassemble A c hR hmatch.separation.le hsmall
  exact ⟨w, W, hWA, hWc, hmatch.of_heq hWA hWc⟩

/-- The analytic preparation and its cutoff margin are now chosen together.
The assembled witness has the prescribed scale and normalization; both may
be increased in their displayed order. -/
theorem exists_ordered_nominal_witness {F : OutgoingProfile.Profile} {D : ℝ}
    (hF : OutgoingProfile.Specification F D) (hP : 2 ≤ F.data.core.P) (N : ℕ)
    {rho : ℝ} (hrho : 0 < rho) (hradius : rho ≤ NominalProfile.resetSolver.radius) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧
      ∀ j : ℝ, |j| ≤ eps → NaturalAxisData.SmallParameters F.data.h j →
      ∃ Λ0 : ℝ, 1 ≤ Λ0 ∧ ∀ Λ : ℝ, 0 < Λ → Λ0 ≤ Λ →
        ∃ T : ℝ, 0 < T ∧ ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ C : ℝ, C0 ≤ C →
          ∃ W : NominalProfile.Witness F,
            W.axis.j = j ∧ W.axis.scale = Λ ∧ W.axis.normalization = C ∧
            W.controls.shapeTime = T ∧ MatchingBounds W.controls N rho := by
  obtain ⟨eps, heps, heps1, hassembled⟩ := exists_ordered_assembled_profile hF N hrho hradius
  refine ⟨eps, heps, heps1, ?_⟩
  intro j hjbound hj
  obtain ⟨prep, hcut⟩ := NominalProfile.prepare_axis_with_cutoff F hP hj
  obtain ⟨Λ0, hΛ0, hscale⟩ := hassembled j hjbound hj prep prep.delta prep.delta_pos hcut
  refine ⟨Λ0, hΛ0, ?_⟩
  intro Λ hΛ hL
  obtain ⟨T, hT, C0, hC0, hnorm⟩ := hscale Λ hΛ hL
  refine ⟨T, hT, C0, hC0, ?_⟩
  intro C hC
  obtain ⟨hLprep, hCprep, E, hcontrols⟩ := hnorm C hC
  obtain ⟨w, W, hWA, hWc, hmatch⟩ := hcontrols 0 1 zero_lt_one
  refine ⟨W, ?_, ?_, ?_, ?_, hmatch⟩
  · rw [hWA]
    rfl
  · rw [hWA]
    rfl
  · rw [hWA]
    rfl
  · exact shapeTime_eq_of_heq hWA hWc

/-- Actual nominal-profile existence from the fixed outgoing profile. The
positive axial perturbation is chosen small enough for the fixed inverse,
and all five moments are then repaired by its actual normalized solver. -/
theorem exists_nominal_witness {F : OutgoingProfile.Profile} {D : ℝ}
    (hF : OutgoingProfile.Specification F D) (hP : 2 ≤ F.data.core.P)
    (hh : F.data.h ≤ 1 / 1000) (N : ℕ) {rho : ℝ}
    (hrho : 0 < rho) (hradius : rho ≤ NominalProfile.resetSolver.radius) :
    ∃ W : NominalProfile.Witness F, MatchingBounds W.controls N rho := by
  obtain ⟨eps, heps, _heps1, hordered⟩ := exists_ordered_nominal_witness hF hP N hrho hradius
  let j : ℝ := min (eps / 2) (1 / 2000)
  have hj : 0 < j := lt_min (by positivity) (by norm_num)
  have hjbound : |j| ≤ eps := by
    rw [abs_of_pos hj]
    exact (min_le_left _ _).trans (by linarith)
  have hsmall : NaturalAxisData.SmallParameters F.data.h j :=
    ⟨F.data.h_pos, hh, hj, (min_le_right _ _).trans (by norm_num)⟩
  obtain ⟨Λ0, hΛ0, hscale⟩ := hordered j hjbound hsmall
  obtain ⟨T, _hT, C0, _hC0, hnorm⟩ := hscale Λ0 (zero_lt_one.trans_le hΛ0) le_rfl
  obtain ⟨W, _hj, _hL, _hC, _hT, hmatch⟩ := hnorm C0 le_rfl
  exact ⟨W, hmatch⟩

theorem exists_nominal_with_small_coefficients {F : OutgoingProfile.Profile} {D : ℝ}
    (hF : OutgoingProfile.Specification F D) (hP : 2 ≤ F.data.core.P)
    (hh : F.data.h ≤ 1 / 1000) (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ tau : ℝ, 0 < tau →
      tau ≤ min 1 (NominalProfile.resetSolver.radius / 2) →
      ∃ W : NominalProfile.Witness F,
        MatchingBounds W.controls N (tau ^ (N + 1)) ∧
        JetBounds.FiniteJetBound N (NominalProfile.resetCoefficients F W.controls.debt)
          (Icc (-1 : ℝ) 1) (K * tau) := by
  obtain ⟨K, hK, hk⟩ := resetCoefficients_jet_control N
  refine ⟨K, hK, ?_⟩
  intro tau htau hmax
  have ht1 : tau ≤ 1 := hmax.trans (min_le_left _ _)
  have hpow : tau ^ (N + 1) ≤ tau := by
    simpa only [pow_one] using
      pow_le_pow_of_le_one htau.le ht1 (show 1 ≤ N + 1 by omega)
  have hradius : tau ^ (N + 1) ≤ NominalProfile.resetSolver.radius :=
    hpow.trans ((hmax.trans (min_le_right _ _)).trans
      (by linarith [NominalProfile.resetSolver.radius_pos]))
  obtain ⟨W, hw⟩ := exists_nominal_witness hF hP hh N (pow_pos htau _) hradius
  refine ⟨W, hw, hk W.controls hw.separation.le tau htau hmax ?_⟩
  exact fun n hn eta hη => (hw.normalized_jets n hn eta hη).le

theorem nominal_witness_exists {F : OutgoingProfile.Profile} {D : ℝ}
    (hF : OutgoingProfile.Specification F D) (hP : 2 ≤ F.data.core.P)
    (hh : F.data.h ≤ 1 / 1000) : Nonempty (NominalProfile.Witness F) := by
  obtain ⟨W, _⟩ := exists_nominal_witness hF hP hh 0
    (show 0 < NominalProfile.resetSolver.radius / 2 by
      exact div_pos NominalProfile.resetSolver.radius_pos (by norm_num))
    (show NominalProfile.resetSolver.radius / 2 ≤ NominalProfile.resetSolver.radius by
      linarith [NominalProfile.resetSolver.radius_pos])
  exact ⟨W⟩

end NavierStokes.MatchingDebtBounds

end
