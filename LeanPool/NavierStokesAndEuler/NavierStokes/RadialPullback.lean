/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.WeightedRadialPrimitive
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

/-!
# Physical power-coordinate pullback of the weighted radial inverse

The power coordinate is `U = R^d` on a fixed positive annulus. Smooth positive
regularizations below the annulus make every source and output a genuine
globally defined smooth function. They agree with the prescribed power maps
where the source or the output can be nonzero.
-/

noncomputable section

namespace NavierStokes.RadialPullback

open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
open WeightedRadialPrimitive

private theorem nat_le_smooth (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n))

/-- A globally smooth positive radius, identical to the radius above `2ℓ`. -/
noncomputable def positiveRadius (ℓ x : ℝ) : ℝ :=
  ℓ + (x - ℓ) * Real.smoothTransition ((x - ℓ) / ℓ)

theorem positiveRadius_contDiff (ℓ : ℝ) : ContDiff ℝ ∞ (positiveRadius ℓ) := by
  unfold positiveRadius
  exact contDiff_const.add ((contDiff_id.sub contDiff_const).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const ℓ)))

theorem positiveRadius_eq_left {ℓ x : ℝ} (hℓ : 0 < ℓ) (hx : x ≤ ℓ) :
    positiveRadius ℓ x = ℓ := by
  simp only [positiveRadius, Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hℓ.le), mul_zero, add_zero]

theorem positiveRadius_eq_self {ℓ x : ℝ} (hℓ : 0 < ℓ) (hx : 2 * ℓ ≤ x) :
    positiveRadius ℓ x = x := by
  have ht : 1 ≤ (x - ℓ) / ℓ := (one_le_div hℓ).mpr (by linarith)
  simp only [positiveRadius, Real.smoothTransition.one_of_one_le ht, mul_one]
  ring

theorem positiveRadius_pos {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ) : 0 < positiveRadius ℓ x := by
  by_cases hx : x ≤ ℓ
  · rw [positiveRadius_eq_left hℓ hx]
    exact hℓ
  · have hprod : 0 ≤ (x - ℓ) * Real.smoothTransition ((x - ℓ) / ℓ) :=
      mul_nonneg (sub_nonneg.mpr (le_of_not_ge hx)) (Real.smoothTransition.nonneg _)
    unfold positiveRadius
    linarith

theorem positiveRadius_le_max {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ℝ) :
    positiveRadius ℓ x ≤ max ℓ x := by
  by_cases hx : x ≤ ℓ
  · rw [positiveRadius_eq_left hℓ hx, max_eq_left hx]
  · have hxl : ℓ ≤ x := le_of_not_ge hx
    rw [max_eq_right hxl]
    have hm := mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one ((x - ℓ) / ℓ))
      (sub_nonneg.mpr hxl)
    unfold positiveRadius
    linarith

theorem positiveRadius_lt {ℓ x t : ℝ} (hℓ : 0 < ℓ) (hℓt : ℓ < t) (hxt : x < t) :
    positiveRadius ℓ x < t :=
  (positiveRadius_le_max hℓ x).trans_lt (max_lt hℓt hxt)

noncomputable def powerChart (d a R : ℝ) : ℝ := (positiveRadius (a / 4) R) ^ d
noncomputable def inverseChart (d a U : ℝ) : ℝ := (positiveRadius (a ^ d / 4) U) ^ d⁻¹
noncomputable def radialJacobian (d R : ℝ) : ℝ := d * R ^ (d - 1)

theorem powerChart_contDiff {a : ℝ} (ha : 0 < a) (d : ℝ) :
    ContDiff ℝ ∞ (powerChart d a) :=
  (positiveRadius_contDiff (a / 4)).rpow_const_of_ne
    (fun R => (positiveRadius_pos (by positivity) R).ne')

theorem inverseChart_contDiff {a : ℝ} (ha : 0 < a) (d : ℝ) :
    ContDiff ℝ ∞ (inverseChart d a) :=
  (positiveRadius_contDiff (a ^ d / 4)).rpow_const_of_ne
    (fun U => (positiveRadius_pos (div_pos (Real.rpow_pos_of_pos ha d) (by norm_num)) U).ne')

theorem powerChart_pos {a : ℝ} (ha : 0 < a) (d R : ℝ) : 0 < powerChart d a R :=
  Real.rpow_pos_of_pos (positiveRadius_pos (by positivity) R) d

theorem inverseChart_pos {a : ℝ} (ha : 0 < a) (d U : ℝ) : 0 < inverseChart d a U :=
  Real.rpow_pos_of_pos
    (positiveRadius_pos (div_pos (Real.rpow_pos_of_pos ha d) (by norm_num)) U) d⁻¹

theorem radialJacobian_pos {d R : ℝ} (hd : 0 < d) (hR : 0 < R) :
    0 < radialJacobian d R := mul_pos hd (Real.rpow_pos_of_pos hR _)

theorem powerChart_eq {a R : ℝ} (ha : 0 < a) (hR : a / 2 ≤ R) (d : ℝ) :
    powerChart d a R = R ^ d := by
  rw [powerChart, positiveRadius_eq_self (by positivity) (by linarith)]

theorem inverseChart_eq {a U : ℝ} (ha : 0 < a) (d : ℝ) (hU : a ^ d / 2 ≤ U) :
    inverseChart d a U = U ^ d⁻¹ := by
  rw [inverseChart, positiveRadius_eq_self
    (div_pos (Real.rpow_pos_of_pos ha d) (by norm_num)) (by linarith)]

theorem inverseChart_power {a R d : ℝ} (ha : 0 < a) (hd : 0 < d) (hR : a ≤ R) :
    inverseChart d a (R ^ d) = R := by
  have haU : 0 < a ^ d := Real.rpow_pos_of_pos ha d
  have hRU : a ^ d ≤ R ^ d := Real.rpow_le_rpow ha.le hR hd.le
  rw [inverseChart_eq ha d (by linarith), Real.rpow_rpow_inv (ha.le.trans hR) hd.ne']

theorem powerChart_inverse {a U d : ℝ} (ha : 0 < a) (hd : 0 < d) (hU : a ^ d ≤ U) :
    powerChart d a (inverseChart d a U) = U := by
  have haU : 0 < a ^ d := Real.rpow_pos_of_pos ha d
  have hUp : 0 < U := haU.trans_le hU
  have hR : a ≤ U ^ d⁻¹ := by
    have h := Real.rpow_le_rpow haU.le hU (inv_pos.mpr hd).le
    simpa only [Real.rpow_rpow_inv ha.le hd.ne'] using h
  rw [inverseChart_eq ha d (by linarith), powerChart_eq ha (by linarith) d,
    Real.rpow_inv_rpow hUp.le hd.ne']

theorem inverseChart_rpow {a U d : ℝ} (ha : 0 < a) (hd : 0 < d) (hU : a ^ d ≤ U) :
    (inverseChart d a U) ^ d = U := by
  have haU := Real.rpow_pos_of_pos ha d
  rw [inverseChart_eq ha d (by linarith), Real.rpow_inv_rpow (haU.le.trans hU) hd.ne']

theorem powerChart_lt_left {a R d : ℝ} (ha : 0 < a) (hd : 0 < d) (hR : R < a) :
    powerChart d a R < a ^ d :=
  Real.rpow_lt_rpow (positiveRadius_pos (by positivity) R).le
    (positiveRadius_lt (by positivity) (by linarith) hR) hd

theorem inverseChart_lt_left {a U d : ℝ} (ha : 0 < a) (hd : 0 < d) (hU : U < a ^ d) :
    inverseChart d a U < a := by
  have hp : 0 < a ^ d := Real.rpow_pos_of_pos ha d
  have h := Real.rpow_lt_rpow (positiveRadius_pos (by positivity : 0 < a ^ d / 4) U).le
    (positiveRadius_lt (by positivity : 0 < a ^ d / 4) (by linarith) hU) (inv_pos.mpr hd)
  simpa only [inverseChart, Real.rpow_rpow_inv ha.le hd.ne'] using h

theorem powerChart_gt_right {a b R d : ℝ} (ha : 0 < a) (hab : a < b)
    (hd : 0 < d) (hR : b < R) : b ^ d < powerChart d a R := by
  rw [powerChart_eq ha (by linarith) d]
  exact Real.rpow_lt_rpow (ha.trans hab).le hR hd

theorem inverseChart_gt_right {a b U d : ℝ} (ha : 0 < a) (hab : a < b)
    (hd : 0 < d) (hU : b ^ d < U) : b < inverseChart d a U := by
  have haU : 0 < a ^ d := Real.rpow_pos_of_pos ha d
  have habU : a ^ d < b ^ d := Real.rpow_lt_rpow ha.le hab hd
  rw [inverseChart_eq ha d (by linarith)]
  have h := Real.rpow_lt_rpow (Real.rpow_pos_of_pos (ha.trans hab) d).le hU (inv_pos.mpr hd)
  simpa only [Real.rpow_rpow_inv (ha.trans hab).le hd.ne'] using h

theorem powerChart_mem {a b R d : ℝ} (ha : 0 < a) (hd : 0 < d) (hR : R ∈ Ioo a b) :
    powerChart d a R ∈ Ioo (a ^ d) (b ^ d) := by
  rw [powerChart_eq ha (by linarith [hR.1]) d]
  exact ⟨Real.rpow_lt_rpow ha.le hR.1 hd, Real.rpow_lt_rpow (ha.trans hR.1).le hR.2 hd⟩

theorem inverseChart_mem {a b U d : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (hU : U ∈ Ioo (a ^ d) (b ^ d)) : inverseChart d a U ∈ Ioo a b := by
  have haU : 0 < a ^ d := Real.rpow_pos_of_pos ha d
  have hbU : 0 < b ^ d := Real.rpow_pos_of_pos (ha.trans hab) d
  rw [inverseChart_eq ha d (by linarith [hU.1])]
  constructor
  · have h := Real.rpow_lt_rpow haU.le hU.1 (inv_pos.mpr hd)
    simpa only [Real.rpow_rpow_inv ha.le hd.ne'] using h
  · have h := Real.rpow_lt_rpow (haU.trans hU.1).le hU.2 (inv_pos.mpr hd)
    simpa only [Real.rpow_rpow_inv (ha.trans hab).le hd.ne'] using h

theorem powerChart_hasDerivAt {a R : ℝ} (ha : 0 < a) (hR : a / 2 < R) (d : ℝ) :
    HasDerivAt (powerChart d a) (radialJacobian d R) R := by
  have heq : powerChart d a =ᶠ[𝓝 R] (fun s : ℝ => s ^ d) := by
    filter_upwards [Ioi_mem_nhds hR] with s hs
    exact powerChart_eq ha hs.le d
  exact (Real.hasDerivAt_rpow_const (Or.inl (show R ≠ 0 by linarith))).congr_of_eventuallyEq heq

section Sources

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def liftChart (φ : ℝ → ℝ) (z : ℝ × E) : ℝ × E := (φ z.1, z.2)

theorem liftChart_contDiff {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (liftChart (E := E) φ) := (hφ.comp contDiff_fst).prodMk contDiff_snd

theorem liftChart_hasFDerivAt {φ : ℝ → ℝ} {c : ℝ} (z : ℝ × E) (hφ : HasDerivAt φ c z.1) :
    HasFDerivAt (liftChart φ)
      ((c • ContinuousLinearMap.fst ℝ ℝ E).prod (ContinuousLinearMap.snd ℝ ℝ E)) z := by
  exact (hφ.comp_hasFDerivAt z (ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt).prodMk
    (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt

noncomputable def sourceMultiplier (d a U : ℝ) : ℝ := (radialJacobian d (inverseChart d a U))⁻¹
noncomputable def normalizeSource (d a : ℝ) (g : ℝ × E → V) (z : ℝ × E) : V :=
  sourceMultiplier d a z.1 • g (liftChart (inverseChart d a) z)

theorem sourceMultiplier_contDiff {a d : ℝ} (ha : 0 < a) (hd : 0 < d) :
    ContDiff ℝ ∞ (sourceMultiplier d a) := by
  apply ContDiff.inv
  · exact contDiff_const.mul ((inverseChart_contDiff ha d).rpow_const_of_ne
      (fun U => (inverseChart_pos ha d U).ne'))
  · exact fun U => (radialJacobian_pos hd (inverseChart_pos ha d U)).ne'

theorem normalizeSource_contDiff {a d : ℝ} (ha : 0 < a) (hd : 0 < d)
    {g : ℝ × E → V} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (normalizeSource d a g) :=
  ((sourceMultiplier_contDiff ha hd).comp contDiff_fst).smul
    (hg.comp (liftChart_contDiff (inverseChart_contDiff ha d)))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem normalizeSource_at_power {a R d : ℝ} (ha : 0 < a) (hd : 0 < d)
    (hR : a ≤ R) (g : ℝ × E → V) (Y : E) :
    normalizeSource d a g (R ^ d, Y) = (radialJacobian d R)⁻¹ • g (R, Y) := by
  simp only [normalizeSource, sourceMultiplier, liftChart, inverseChart_power ha hd hR]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem normalizeSource_supported {a b d : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    {g : ℝ × E → V} (hs : RadialAlias.RadiallySupported a b g) :
    RadialAlias.RadiallySupported (a ^ d) (b ^ d) (normalizeSource d a g) := by
  intro z hz
  have hg : g (liftChart (inverseChart d a) z) ≠ 0 := by
    intro h
    exact hz (by simp [normalizeSource, h])
  have hr := hs hg
  constructor
  · by_contra h
    exact (not_lt_of_ge hr.1) (inverseChart_lt_left ha hd (lt_of_not_ge h))
  · by_contra h
    exact (not_lt_of_ge hr.2) (inverseChart_gt_right ha hab hd (lt_of_not_ge h))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem normalizeSource_eq_formula {a b d U : ℝ} (ha : 0 < a) (hab : a < b)
    (hd : 0 < d) (hU : 0 < U) {g : ℝ × E → V}
    (hs : RadialAlias.RadiallySupported a b g) (Y : E) :
    normalizeSource d a g (U, Y) = (radialJacobian d (U ^ d⁻¹))⁻¹ • g (U ^ d⁻¹, Y) := by
  have haU := Real.rpow_pos_of_pos ha d
  by_cases hUa : a ^ d ≤ U
  · simp only [normalizeSource, sourceMultiplier, liftChart,
      inverseChart_eq ha d (show a ^ d / 2 ≤ U by linarith)]
  · have hsmall : U < a ^ d := lt_of_not_ge hUa
    have hR : U ^ d⁻¹ < a := by
      have h := Real.rpow_lt_rpow hU.le hsmall (inv_pos.mpr hd)
      simpa only [Real.rpow_rpow_inv ha.le hd.ne'] using h
    rw [TransportPrimitive.radial_zero_of_lt (normalizeSource_supported ha hab hd hs) hsmall,
      TransportPrimitive.radial_zero_of_lt hs hR, smul_zero]

noncomputable def pullback (d a : ℝ) (F : ℝ × E → V) : ℝ × E → V :=
  F ∘ liftChart (powerChart d a)

theorem pullback_contDiff {a : ℝ} (ha : 0 < a) (d : ℝ)
    {F : ℝ × E → V} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (pullback d a F) :=
  hF.comp (liftChart_contDiff (powerChart_contDiff ha d))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ V] in
theorem pullback_supported {a b d : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    {F : ℝ × E → V} (hs : RadialAlias.RadiallySupported (a ^ d) (b ^ d) F) :
    RadialAlias.RadiallySupported a b (pullback d a F) := by
  intro z hz
  have hr := hs hz
  constructor
  · by_contra h
    exact (not_lt_of_ge hr.1) (powerChart_lt_left ha hd (lt_of_not_ge h))
  · by_contra h
    exact (not_lt_of_ge hr.2) (powerChart_gt_right ha hab hd (lt_of_not_ge h))

noncomputable def physicalGraphDeriv (d M : ℝ) (v : E) (F : ℝ × E → V) (z : ℝ × E) : V :=
  fderiv ℝ F z (1, (radialJacobian d z.1 * M) • v)

/-- The physical radial graph derivative is the transformed transport
derivative multiplied by the actual power-coordinate Jacobian. -/
theorem physicalGraphDeriv_pullback {a d M : ℝ} (ha : 0 < a) (v : E)
    {F : ℝ × E → V} (z : ℝ × E) (hz : a / 2 < z.1)
    (hF : DifferentiableAt ℝ F (liftChart (powerChart d a) z)) :
    physicalGraphDeriv d M v (pullback d a F) z = radialJacobian d z.1 •
      TransportPrimitive.fixedDeriv (1, M • v) F (liftChart (powerChart d a) z) := by
  have h := hF.hasFDerivAt.comp z (liftChart_hasFDerivAt z (powerChart_hasDerivAt ha hz d))
  change (fderiv ℝ (F ∘ liftChart (powerChart d a)) z)
    (1, (radialJacobian d z.1 * M) • v) = _
  rw [h.fderiv, ContinuousLinearMap.comp_apply]
  have hv : ((radialJacobian d z.1 • ContinuousLinearMap.fst ℝ ℝ E).prod
      (ContinuousLinearMap.snd ℝ ℝ E)) (1, (radialJacobian d z.1 * M) • v) =
        radialJacobian d z.1 • (1, M • v) := by
    ext <;> simp [smul_smul]
  rw [hv, map_smul]
  rfl

/-- Pure auxiliary derivatives are unchanged by the radial coordinate map. -/
theorem auxiliaryDeriv_pullback {a d : ℝ} (ha : 0 < a) (w : E)
    {F : ℝ × E → V} (z : ℝ × E) (hz : a / 2 < z.1)
    (hF : DifferentiableAt ℝ F (liftChart (powerChart d a) z)) :
    TransportPrimitive.fixedDeriv (0, w) (pullback d a F) z =
      TransportPrimitive.fixedDeriv (0, w) F (liftChart (powerChart d a) z) := by
  have h := hF.hasFDerivAt.comp z (liftChart_hasFDerivAt z (powerChart_hasDerivAt ha hz d))
  unfold TransportPrimitive.fixedDeriv pullback
  rw [h.fderiv, ContinuousLinearMap.comp_apply]
  congr 1
  ext <;> simp

/-- The positive power substitution includes the actual radial Jacobian. -/
theorem power_substitution {a R d : ℝ} (ha : 0 < a) (hR : a ≤ R)
    (F : ℝ → V) (hF : Continuous F) :
    (∫ s in a..R, radialJacobian d s • F (s ^ d)) =
      ∫ U in (a ^ d)..(R ^ d), F U := by
  have hspos (s : ℝ) (hs : s ∈ uIcc a R) : 0 < s := by
    rw [uIcc_of_le hR] at hs
    exact ha.trans_le hs.1
  have hj : ContDiffOn ℝ ∞ (radialJacobian d) (uIcc a R) :=
    contDiffOn_const.mul (contDiffOn_id.rpow_const_of_ne (fun s hs => (hspos s hs).ne'))
  exact intervalIntegral.integral_deriv_smul_comp
    (fun s hs => Real.hasDerivAt_rpow_const (Or.inl (hspos s hs).ne')) hj.continuousOn hF

/-- After source normalization, the Jacobian cancels exactly, including the
auxiliary shift in the transformed coordinate. -/
theorem normalized_radial_integral {a R d : ℝ} (ha : 0 < a) (hd : 0 < d) (hR : a ≤ R)
    {g : ℝ × E → V} (hg : ContDiff ℝ ∞ g) (M U₀ : ℝ) (v Y : E) :
    (∫ U in (a ^ d)..(R ^ d), normalizeSource d a g (U, Y + (M * (U - U₀)) • v)) =
      ∫ s in a..R, g (s, Y + (M * (s ^ d - U₀)) • v) := by
  let F : ℝ → V := fun U => normalizeSource d a g (U, Y + (M * (U - U₀)) • v)
  have hF : Continuous F := (normalizeSource_contDiff ha hd hg).continuous.comp
    (continuous_id.prodMk (continuous_const.add
      ((continuous_const.mul (continuous_id.sub continuous_const)).smul continuous_const)))
  rw [← power_substitution ha hR F hF]
  apply intervalIntegral.integral_congr
  intro s hs
  have has : a ≤ s := by
    have hs' : s ∈ Icc a R := by simpa only [uIcc_of_le hR] using hs
    exact hs'.1
  dsimp only [F]
  rw [normalizeSource_at_power ha hd has, smul_smul,
    mul_inv_cancel₀ (radialJacobian_pos hd (ha.trans_le has)).ne', one_smul]

/-- The total transformed integral has exactly the original physical radial
measure. In particular no Jacobian remains when taking a torus mean later. -/
theorem total_normalized_eq_radialIntegral {a b d : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) {g : ℝ × E → V}
    (hg : ContDiff ℝ ∞ g) (hs : RadialAlias.RadiallySupported a b g)
    (M U : ℝ) (v Y : E) :
    TransportPrimitive.totalIntegral M v (normalizeSource d a g) (U, Y) =
      ∫ s in a..b, g (s, Y + (M * (s ^ d - U)) • v) := by
  rw [TransportPrimitive.totalIntegral_eq_radialInterval (normalizeSource_contDiff ha hd
    hg).continuous
    (normalizeSource_supported ha hab hd hs)]
  exact normalized_radial_integral ha hd hab.le hg M U v Y

noncomputable def physicalCompact (d a b M : ℝ) (v : E) (g : ℝ × E → V) : ℝ × E → V :=
  pullback d a (TransportPrimitive.compactIntegral
    (TransportPrimitive.interiorCutoff (a ^ d) (b ^ d)) M v (normalizeSource d a g))

theorem physicalCompact_contDiff [CompleteSpace V] {a b d : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) {g : ℝ × E → V}
    (hg : ContDiff ℝ ∞ g) (hs : RadialAlias.RadiallySupported a b g) (M : ℝ) (v : E) :
    ContDiff ℝ ∞ (physicalCompact d a b M v g) :=
  pullback_contDiff ha d (TransportPrimitive.compactIntegral_contDiff
    (TransportPrimitive.interiorCutoff_contDiff _ _)
    (normalizeSource_contDiff ha hd hg) (normalizeSource_supported ha hab hd hs))

theorem physicalCompact_supported {a b d : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) {g : ℝ × E → V}
    (hg : ContDiff ℝ ∞ g) (hs : RadialAlias.RadiallySupported a b g) (M : ℝ) (v : E) :
    RadialAlias.RadiallySupported a b (physicalCompact d a b M v g) :=
  pullback_supported ha hab hd (TransportPrimitive.canonicalCompact_supported
    (Real.rpow_lt_rpow ha.le hab hd) (normalizeSource_contDiff ha hd hg).continuous
    (normalizeSource_supported ha hab hd hs))

/-- The pulled-back operator is the physical shifted radial integral, with
the original source g and no uncancelled Jacobian. -/
theorem physicalCompact_eq_radialIntegral {a b d : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) {g : ℝ × E → V}
    (hg : ContDiff ℝ ∞ g) (hs : RadialAlias.RadiallySupported a b g)
    (M : ℝ) (v : E) (z : ℝ × E) (hz : a ≤ z.1) :
    physicalCompact d a b M v g z =
      (∫ s in a..z.1, g (s, z.2 + (M * (s ^ d - z.1 ^ d)) • v)) -
      TransportPrimitive.interiorCutoff (a ^ d) (b ^ d) (z.1 ^ d) •
        (∫ s in a..b, g (s, z.2 + (M * (s ^ d - z.1 ^ d)) • v)) := by
  have hF := (normalizeSource_contDiff ha hd hg).continuous
  have hS := normalizeSource_supported ha hab hd hs
  change TransportPrimitive.compactIntegral _ _ _ _ (powerChart d a z.1, z.2) = _
  rw [powerChart_eq ha (by linarith) d, TransportPrimitive.compactIntegral,
    TransportPrimitive.pastIntegral_eq_radialInterval hF hS,
    TransportPrimitive.totalIntegral_eq_radialInterval hF hS]
  simp only [normalized_radial_integral ha hd hz hg, normalized_radial_integral ha hd hab.le hg]

noncomputable def physicalAlias (d a b M : ℝ) (v : E) (g : ℝ × E → V) (z : ℝ × E) : V :=
  (radialJacobian d z.1 * deriv (TransportPrimitive.interiorCutoff (a ^ d) (b ^ d))
      (powerChart d a z.1)) •
    TransportPrimitive.totalIntegral M v (normalizeSource d a g) (liftChart (powerChart d a) z)

noncomputable def physicalCutoff (d a b R : ℝ) : ℝ :=
  TransportPrimitive.interiorCutoff (a ^ d) (b ^ d) (powerChart d a R)

theorem physicalCutoff_contDiff {a : ℝ} (ha : 0 < a) (d b : ℝ) :
    ContDiff ℝ ∞ (physicalCutoff d a b) :=
  (TransportPrimitive.interiorCutoff_contDiff _ _).comp (powerChart_contDiff ha d)

theorem deriv_physicalCutoff {a R : ℝ} (ha : 0 < a) (hR : a / 2 < R) (d b : ℝ) :
    deriv (physicalCutoff d a b) R = radialJacobian d R *
      deriv (TransportPrimitive.interiorCutoff (a ^ d) (b ^ d)) (powerChart d a R) := by
  have h := ((TransportPrimitive.interiorCutoff_contDiff (a ^ d) (b ^ d)).differentiable
    (by simp) (powerChart d a R)).hasDerivAt.comp R (powerChart_hasDerivAt ha hR d)
  unfold physicalCutoff
  simpa only [Function.comp_def, mul_comm] using h.deriv

theorem physicalAlias_eq_cutoff_derivative {a d b M : ℝ} (ha : 0 < a)
    (v : E) (g : ℝ × E → V) (z : ℝ × E) (hz : a / 2 < z.1) :
    physicalAlias d a b M v g z = deriv (physicalCutoff d a b) z.1 •
      TransportPrimitive.totalIntegral M v (normalizeSource d a g) (liftChart (powerChart d a) z)
        := by
  rw [deriv_physicalCutoff ha hz]
  rfl

/-- Exact inverse identity in the physical radial graph coordinate, including
the compactification alias and the source normalization. -/
theorem physicalGraphDeriv_physicalCompact [CompleteSpace V] {a b d : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) {g : ℝ × E → V}
    (hg : ContDiff ℝ ∞ g) (hs : RadialAlias.RadiallySupported a b g)
    (M : ℝ) (v : E) (z : ℝ × E) (hz : a ≤ z.1) :
    physicalGraphDeriv d M v (physicalCompact d a b M v g) z =
      g z - physicalAlias d a b M v g z := by
  have hnf := normalizeSource_contDiff ha hd hg
  have hns := normalizeSource_supported ha hab hd hs
  have hχ := TransportPrimitive.interiorCutoff_contDiff (a ^ d) (b ^ d)
  have hF := TransportPrimitive.compactIntegral_contDiff (M := M) (v := v) hχ hnf hns
  unfold physicalCompact
  rw [physicalGraphDeriv_pullback ha v z (by linarith)
    (hF.differentiable (by simp) _), TransportPrimitive.transport_compactIntegral hχ hnf hns]
  simp only [physicalAlias, liftChart, powerChart_eq ha (by linarith : a / 2 ≤ z.1) d,
    normalizeSource_at_power ha hd hz, smul_sub, smul_smul,
    mul_inv_cancel₀ (radialJacobian_pos hd (ha.trans_le hz)).ne', one_smul]

theorem deriv_interiorCutoff_zero_left {a b U : ℝ} (hab : a < b) (hU : U ≤ a) :
    deriv (TransportPrimitive.interiorCutoff a b) U = 0 := by
  have hgerm : TransportPrimitive.interiorCutoff a b =ᶠ[𝓝 U] (fun _ => 0) := by
    filter_upwards [Iio_mem_nhds (show U < (2 * a + b) / 3 by linarith)] with x hx
    exact TransportPrimitive.interiorCutoff_zero hab hx.le
  exact ((hasDerivAt_const U (0 : ℝ)).congr_of_eventuallyEq hgerm).deriv

theorem deriv_interiorCutoff_zero_right {a b U : ℝ} (hab : a < b) (hU : b ≤ U) :
    deriv (TransportPrimitive.interiorCutoff a b) U = 0 := by
  have hgerm : TransportPrimitive.interiorCutoff a b =ᶠ[𝓝 U] (fun _ => 1) := by
    filter_upwards [Ioi_mem_nhds (show (a + 2 * b) / 3 < U by linarith)] with x hx
    exact TransportPrimitive.interiorCutoff_one hab hx.le
  exact ((hasDerivAt_const U (1 : ℝ)).congr_of_eventuallyEq hgerm).deriv

theorem physicalAlias_supported {a b d : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (M : ℝ) (v : E) (g : ℝ × E → V) :
    RadialAlias.RadiallySupported a b (physicalAlias d a b M v g) := by
  have habU : a ^ d < b ^ d := Real.rpow_lt_rpow ha.le hab hd
  intro z hz
  constructor
  · by_contra h
    have hc := deriv_interiorCutoff_zero_left habU (powerChart_lt_left ha hd (lt_of_not_ge h)).le
    exact hz (by simp only [physicalAlias, hc, mul_zero, zero_smul])
  · by_contra h
    have hc := deriv_interiorCutoff_zero_right habU (powerChart_gt_right ha hab hd (lt_of_not_ge
      h)).le
    exact hz (by simp only [physicalAlias, hc, mul_zero, zero_smul])

theorem physicalCutoff_zero_left {a b d R : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (hR : R < a) : physicalCutoff d a b R = 0 := by
  have habU : a ^ d < b ^ d := Real.rpow_lt_rpow ha.le hab hd
  have hpow := powerChart_lt_left ha hd hR
  exact TransportPrimitive.interiorCutoff_zero habU (by linarith)

theorem deriv_physicalCutoff_zero_left {a b d R : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (hR : R < a) : deriv (physicalCutoff d a b) R = 0 := by
  have hgerm : physicalCutoff d a b =ᶠ[𝓝 R] (fun _ => 0) := by
    filter_upwards [Iio_mem_nhds hR] with x hx
    exact physicalCutoff_zero_left ha hab hd hx
  exact ((hasDerivAt_const R (0 : ℝ)).congr_of_eventuallyEq hgerm).deriv

theorem physicalAlias_eq_cutoff_derivative_global {a b d M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : E) (g : ℝ × E → V) (z : ℝ × E) :
    physicalAlias d a b M v g z = deriv (physicalCutoff d a b) z.1 •
      TransportPrimitive.totalIntegral M v (normalizeSource d a g) (liftChart (powerChart d a) z)
        := by
  by_cases hz : a / 2 < z.1
  · exact physicalAlias_eq_cutoff_derivative ha v g z hz
  · have hza : z.1 < a := by linarith
    rw [TransportPrimitive.radial_zero_of_lt (physicalAlias_supported ha hab hd M v g) hza,
      deriv_physicalCutoff_zero_left ha hab hd hza, zero_smul]

theorem physicalAlias_contDiff [CompleteSpace V] {a b d : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) {g : ℝ × E → V}
    (hg : ContDiff ℝ ∞ g) (hs : RadialAlias.RadiallySupported a b g) (M : ℝ) (v : E) :
    ContDiff ℝ ∞ (physicalAlias d a b M v g) := by
  have heq : physicalAlias d a b M v g = (fun z : ℝ × E =>
      deriv (physicalCutoff d a b) z.1 •
        TransportPrimitive.totalIntegral M v (normalizeSource d a g) (liftChart (powerChart d a)
          z)) :=
    funext (physicalAlias_eq_cutoff_derivative_global ha hab hd v g)
  rw [heq]
  exact (((contDiff_infty_iff_deriv.mp (physicalCutoff_contDiff ha d b)).2).comp contDiff_fst).smul
    ((TransportPrimitive.totalIntegral_contDiff (normalizeSource_contDiff ha hd hg)
      (normalizeSource_supported ha hab hd hs)).comp (liftChart_contDiff (powerChart_contDiff ha
        d)))

/-- Global physical inverse identity. Below the positive annulus, the source,
the output derivative, and the alias all vanish by their proved support. -/
theorem physicalGraphDeriv_physicalCompact_global [CompleteSpace V] {a b d : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) {g : ℝ × E → V}
    (hg : ContDiff ℝ ∞ g) (hs : RadialAlias.RadiallySupported a b g)
    (M : ℝ) (v : E) (z : ℝ × E) :
    physicalGraphDeriv d M v (physicalCompact d a b M v g) z = g z - physicalAlias d a b M v g z :=
      by
  by_cases hz : a ≤ z.1
  · exact physicalGraphDeriv_physicalCompact ha hab hd hg hs M v z hz
  · have hza : z.1 < a := lt_of_not_ge hz
    have hD := TransportPrimitive.radial_zero_of_lt
      (TransportPrimitive.radialSupport_fderiv (physicalCompact_supported ha hab hd hg hs M v)) hza
    rw [physicalGraphDeriv, hD, _root_.zero_apply,
      TransportPrimitive.radial_zero_of_lt hs hza,
      TransportPrimitive.radial_zero_of_lt (physicalAlias_supported ha hab hd M v g) hza, sub_self]

end Sources

/-! ### Exact exponential weight and controlled inverse-edge powers -/

theorem logPosition_power {a R : ℝ} (ha : 0 < a) (hR : 0 < R) (d : ℝ) :
    logPosition (a ^ d) (R ^ d) = d * logPosition a R := by
  unfold logPosition
  rw [Real.log_div (Real.rpow_pos_of_pos hR d).ne' (Real.rpow_pos_of_pos ha d).ne',
    Real.log_rpow hR, Real.log_rpow ha, Real.log_div hR.ne' ha.ne']
  ring

theorem logLength_power {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (d : ℝ) :
    logLength (a ^ d) (b ^ d) = d * logLength a b := logPosition_power ha hb d

theorem delta_scale_lower {d L x : ℝ} (hd : 0 < d) (hx : x ∈ Ioo 0 L) :
    min 1 d * delta L x ≤ delta (d * L) (d * x) := by
  have hc : 0 ≤ min 1 d := le_min zero_le_one hd.le
  have hδ : 0 ≤ delta L x := (delta_pos hx).le
  change min 1 d * delta L x ≤ min 1 (min (d * x) (d * L - d * x))
  apply le_min
  · exact (mul_le_mul (min_le_left _ _) (delta_le_one L x) hδ zero_le_one).trans_eq (one_mul 1)
  · apply le_min
    · exact mul_le_mul (min_le_right _ _) (delta_le_left L x) hδ hd.le
    · have h := mul_le_mul (min_le_right (1 : ℝ) d) (delta_le_right L x) hδ hd.le
      nlinarith

theorem delta_scale_reverse_lower {d L x : ℝ} (hd : 0 < d) (hx : x ∈ Ioo 0 L) :
    min 1 d⁻¹ * delta (d * L) (d * x) ≤ delta L x := by
  have hy : d * x ∈ Ioo 0 (d * L) := ⟨mul_pos hd hx.1, mul_lt_mul_of_pos_left hx.2 hd⟩
  have h := delta_scale_lower (inv_pos.mpr hd) hy
  simpa only [inv_mul_cancel_left₀ hd.ne'] using h

theorem edge_scaled (c : ℝ) {d x : ℝ} (hd : 0 < d) (hx : 0 < x) :
    FlatCutoff.edge (d ^ 2 * c) (d * x) = FlatCutoff.edge c x := by
  rw [FlatCutoff.edge_of_pos _ (mul_pos hd hx), FlatCutoff.edge_of_pos _ hx]
  congr 1
  field_simp

theorem zeta_scaled (cL cR : ℝ) {d L x : ℝ} (hd : 0 < d) (hx : x ∈ Ioo 0 L) :
    zeta (d ^ 2 * cL) (d ^ 2 * cR) (d * L) (d * x) = zeta cL cR L x := by
  unfold zeta
  rw [show d * L - d * x = d * (L - x) by ring,
    edge_scaled cL hd hx.1, edge_scaled cR hd (sub_pos.mpr hx.2)]

theorem weight_scale_forward (cL cR : ℝ) {d L x : ℝ} (hd : 0 < d)
    (hx : x ∈ Ioo 0 L) (p : ℕ) :
    weight (d ^ 2 * cL) (d ^ 2 * cR) (d * L) p (d * x) ≤
      ((min 1 d) ^ p)⁻¹ * weight cL cR L p x := by
  have hc : 0 < min 1 d := lt_min zero_lt_one hd
  have hδ := delta_pos hx
  have hp := pow_le_pow_left₀ (mul_nonneg hc.le hδ.le) (delta_scale_lower hd hx) p
  rw [weight, zeta_scaled cL cR hd hx]
  calc
    _ ≤ zeta cL cR L x / (min 1 d * delta L x) ^ p :=
      div_le_div_of_nonneg_left (zeta_pos cL cR hx).le (pow_pos (mul_pos hc hδ) p) hp
    _ = ((min 1 d) ^ p)⁻¹ * weight cL cR L p x := by
      simp only [weight, mul_pow, div_eq_mul_inv, mul_inv_rev]
      ring

theorem weight_scale_reverse (cL cR : ℝ) {d L x : ℝ} (hd : 0 < d)
    (hx : x ∈ Ioo 0 L) (p : ℕ) :
    weight cL cR L p x ≤ ((min 1 d⁻¹) ^ p)⁻¹ *
      weight (d ^ 2 * cL) (d ^ 2 * cR) (d * L) p (d * x) := by
  have hc : 0 < min 1 d⁻¹ := lt_min zero_lt_one (inv_pos.mpr hd)
  have hy : d * x ∈ Ioo 0 (d * L) := ⟨mul_pos hd hx.1, mul_lt_mul_of_pos_left hx.2 hd⟩
  have hδ := delta_pos hy
  have hp := pow_le_pow_left₀ (mul_nonneg hc.le hδ.le) (delta_scale_reverse_lower hd hx) p
  rw [weight]
  calc
    _ ≤ zeta cL cR L x / (min 1 d⁻¹ * delta (d * L) (d * x)) ^ p :=
      div_le_div_of_nonneg_left (zeta_pos cL cR hx).le (pow_pos (mul_pos hc hδ) p) hp
    _ = ((min 1 d⁻¹) ^ p)⁻¹ *
        weight (d ^ 2 * cL) (d ^ 2 * cR) (d * L) p (d * x) := by
      rw [weight, zeta_scaled cL cR hd hx]
      simp only [mul_pow, div_eq_mul_inv, mul_inv_rev]
      ring

/-- Scaling the exponential coefficients by d² preserves exactly the same
exponential flat weight under U=R^d; only a fixed clipped-edge factor changes. -/
theorem logWeight_power_forward {a b R d : ℝ} (ha : 0 < a) (hd : 0 < d)
    (hR : R ∈ Ioo a b) (cL cR : ℝ) (p : ℕ) :
    logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p (R ^ d) ≤
      ((min 1 d) ^ p)⁻¹ * logWeight cL cR a b p R := by
  unfold logWeight
  rw [logLength_power ha (ha.trans (hR.1.trans hR.2)) d,
    logPosition_power ha (ha.trans hR.1) d]
  exact weight_scale_forward cL cR hd (logPosition_mem ha hR) p

theorem logWeight_power_reverse {a b R d : ℝ} (ha : 0 < a) (hd : 0 < d)
    (hR : R ∈ Ioo a b) (cL cR : ℝ) (p : ℕ) :
    logWeight cL cR a b p R ≤ ((min 1 d⁻¹) ^ p)⁻¹ *
      logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p (R ^ d) := by
  unfold logWeight
  rw [logLength_power ha (ha.trans (hR.1.trans hR.2)) d,
    logPosition_power ha (ha.trans hR.1) d]
  exact weight_scale_reverse cL cR hd (logPosition_mem ha hR) p

/-! ### Uniform genuine finite jets under fixed radial maps -/

section FiniteJets

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Positive-order derivatives of a radial coordinate change are independent
of the auxiliary base point. This follows from translation identities. -/
theorem liftChart_jet_aux_independent {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (n : ℕ) (R : ℝ) (Y : E) :
    iteratedFDeriv ℝ (n + 1) (liftChart φ) (R, Y) =
      iteratedFDeriv ℝ (n + 1) (liftChart φ) (R, (0 : E)) := by
  have hmap : (fun z : ℝ × E => liftChart φ (z + (0, Y))) =
      (fun z => liftChart φ z + (0, Y)) := by
    funext z
    simp only [liftChart, Prod.fst_add, Prod.snd_add, add_zero, Prod.mk_add_mk]
  calc
    _ = iteratedFDeriv ℝ (n + 1) (fun z : ℝ × E => liftChart φ (z + (0, Y))) (R, 0) := by
      rw [iteratedFDeriv_comp_add_right]
      simp only [Prod.mk_add_mk, add_zero, zero_add]
    _ = iteratedFDeriv ℝ (n + 1) (fun z : ℝ × E => liftChart φ z + (0, Y)) (R, 0) := by rw [hmap]
    _ = iteratedFDeriv ℝ (n + 1) (liftChart φ) (R, (0 : E)) := by
      rw [fun_iteratedFDeriv_add_apply
        (((liftChart_contDiff hφ).of_le (nat_le_smooth (n + 1))).contDiffAt)
        contDiffAt_const, iteratedFDeriv_succ_const]
      simp

theorem liftChart_positive_jets_bound (a b : ℝ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ j : ℕ, 1 ≤ j → j ≤ m →
      ∀ z : ℝ × E, z.1 ∈ Icc a b → ‖iteratedFDeriv ℝ j (liftChart φ) z‖ ≤ B := by
  classical
  have hex : ∀ j : Fin (m + 1), ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ (Icc a b) ×ˢ ({0} : Set E), ‖iteratedFDeriv ℝ (j : ℕ) (liftChart φ) z‖ ≤ C := by
    intro j
    obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_singleton).exists_bound_of_continuousOn
      (((liftChart_contDiff hφ).continuous_iteratedFDeriv (nat_le_smooth j)).continuousOn :
        ContinuousOn (iteratedFDeriv ℝ (j : ℕ) (liftChart φ)) ((Icc a b) ×ˢ ({0} : Set E)))
    exact ⟨max C 0, le_max_right _ _, fun z hz => (hC z hz).trans (le_max_left _ _)⟩
  choose C hC hb using hex
  let B := max 1 (∑ j, C j)
  refine ⟨B, le_max_left _ _, ?_⟩
  intro j hj hjm z hz
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  let j' : Fin (m + 1) := ⟨k + 1, Nat.lt_succ_of_le hjm⟩
  rw [liftChart_jet_aux_independent hφ k z.1 z.2]
  exact (hb j' (z.1, 0) ⟨hz, mem_singleton 0⟩).trans
    ((Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ j')).trans (le_max_right _ _))

/-- A fixed radial coordinate map has a finite-order composition constant,
uniform on the full auxiliary strip, for actual multilinear derivative norms. -/
theorem radial_comp_finiteJets_uniform (a b : ℝ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : ℝ × E → V), ContDiff ℝ ∞ F →
      ∀ (z : ℝ × E), z.1 ∈ Icc a b → ∀ C : ℝ, 0 ≤ C →
      (∀ i : ℕ, i ≤ m → ‖iteratedFDeriv ℝ i F (liftChart φ z)‖ ≤ C) →
      ∀ j : ℕ, j ≤ m → ‖iteratedFDeriv ℝ j (F ∘ liftChart φ) z‖ ≤ K * C := by
  obtain ⟨B, hB, hb⟩ := liftChart_positive_jets_bound (E := E) a b hφ m
  refine ⟨(m.factorial : ℝ) * B ^ m, mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (zero_le_one.trans
    hB) _), ?_⟩
  intro F hF z hz C hC hsource j hj
  have h := norm_iteratedFDeriv_comp_le hF (liftChart_contDiff hφ) (nat_le_smooth j) z
    (fun i hi => hsource i (hi.trans hj)) (fun i hi hij =>
      (hb i hi (hij.trans hj) z hz).trans (by
        calc
          B = B ^ (1 : ℕ) := by simp
          _ ≤ B ^ i := pow_le_pow_right₀ hB hi))
  calc
    _ ≤ (j.factorial : ℝ) * C * B ^ j := h
    _ ≤ (m.factorial : ℝ) * C * B ^ m :=
      mul_le_mul (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) hC)
        (pow_le_pow_right₀ hB hj) (pow_nonneg (zero_le_one.trans hB) _)
        (mul_nonneg (Nat.cast_nonneg _) hC)
    _ = ((m.factorial : ℝ) * B ^ m) * C := by ring

/-- Multiplication by a fixed smooth radial coefficient has a finite-order
constant, with all product-rule terms retained. -/
theorem radial_multiplier_finiteJets_uniform (a b : ℝ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : ℝ × E → V), ContDiff ℝ ∞ F →
      ∀ (z : ℝ × E), z.1 ∈ Icc a b → ∀ C : ℝ, 0 ≤ C →
      (∀ i : ℕ, i ≤ m → ‖iteratedFDeriv ℝ i F z‖ ≤ C) →
      ∀ j : ℕ, j ≤ m →
        ‖iteratedFDeriv ℝ j (fun y : ℝ × E => h y.1 • F y) z‖ ≤ K * C := by
  obtain ⟨B, hB, hb⟩ := cutoff_finiteJet_bound (E := E) a b h hh m
  refine ⟨(2 : ℝ) ^ m * B, mul_nonneg (by positivity) hB, ?_⟩
  intro F hF z hz C hC hsource j hj
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y : ℝ × E => h y.1) z‖ * ‖iteratedFDeriv ℝ (j - i) F z‖ :=
      norm_iteratedFDeriv_smul_le (hh.comp contDiff_fst) hF z (nat_le_smooth j)
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B * C := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hb i ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hj) z
          hz)
          (Nat.cast_nonneg _))
        (hsource (j - i) ((Nat.sub_le _ _).trans hj)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hB)
    _ = (2 : ℝ) ^ j * B * C := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose j
    _ ≤ ((2 : ℝ) ^ m * B) * C :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hB) hC

end FiniteJets

/-! ### Weighted source normalization -/

section Weighted

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem normalizeSource_finiteJets_uniform {a b d : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (cL cR : ℝ) (p m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : ℝ × E → V), ContDiff ℝ ∞ g → ∀ A : ℝ, 0 ≤ A →
      (∀ j : ℕ, j ≤ m → ∀ R ∈ Ioo a b, ∀ Y : E,
        ‖iteratedFDeriv ℝ j g (R, Y)‖ ≤ A * logWeight cL cR a b p R) →
      ∀ z : ℝ × E, z.1 ∈ Ioo (a ^ d) (b ^ d) → ∀ j : ℕ, j ≤ m →
        ‖iteratedFDeriv ℝ j (normalizeSource d a g) z‖ ≤
          K * A * logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p z.1 := by
  obtain ⟨KC, hKC, hbC⟩ := radial_comp_finiteJets_uniform (E := E) (V := V)
    (a ^ d) (b ^ d) (inverseChart_contDiff ha d) m
  obtain ⟨KM, hKM, hbM⟩ := radial_multiplier_finiteJets_uniform (E := E) (V := V)
    (a ^ d) (b ^ d) (sourceMultiplier_contDiff ha hd) m
  let Q := ((min 1 d⁻¹) ^ p)⁻¹
  have hQ : 0 ≤ Q := (inv_pos.mpr (pow_pos (lt_min zero_lt_one (inv_pos.mpr hd)) p)).le
  refine ⟨KM * KC * Q, mul_nonneg (mul_nonneg hKM hKC) hQ, ?_⟩
  intro g hg A hA hsource z hz j hj
  have hr := inverseChart_mem ha hab hd hz
  have hw : 0 ≤ logWeight cL cR a b p (inverseChart d a z.1) :=
    (weight_pos cL cR p (logPosition_mem ha hr)).le
  have hcomp (i : ℕ) (hi : i ≤ m) :
      ‖iteratedFDeriv ℝ i (g ∘ liftChart (inverseChart d a)) z‖ ≤
        KC * (A * logWeight cL cR a b p (inverseChart d a z.1)) :=
    hbC g hg z ⟨hz.1.le, hz.2.le⟩ _ (mul_nonneg hA hw)
      (fun k hk => hsource k hk _ hr z.2) i hi
  have hmul := hbM (g ∘ liftChart (inverseChart d a))
    (hg.comp (liftChart_contDiff (inverseChart_contDiff ha d))) z ⟨hz.1.le, hz.2.le⟩
    (KC * (A * logWeight cL cR a b p (inverseChart d a z.1)))
    (mul_nonneg hKC (mul_nonneg hA hw)) hcomp j hj
  change ‖iteratedFDeriv ℝ j (normalizeSource d a g) z‖ ≤
    KM * (KC * (A * logWeight cL cR a b p (inverseChart d a z.1))) at hmul
  have hweight := logWeight_power_reverse ha hd hr cL cR p
  rw [inverseChart_rpow ha hd hz.1.le] at hweight
  calc
    _ ≤ KM * (KC * (A * logWeight cL cR a b p (inverseChart d a z.1))) := hmul
    _ ≤ KM * (KC * (A * (Q * logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p z.1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hweight hA) hKC) hKM
    _ = (KM * KC * Q) * A * logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p z.1 := by ring

variable [CompleteSpace V]

/-- The complete physical inverse preserves the original exponential weight
and the same finite inverse-edge degree. All constants precede the arbitrary
transport shift, source, amplitude, and evaluation point. -/
theorem physicalCompact_finiteJets_uniform {a b d cL cR : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR) (p m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℝ) (v : E) (g : ℝ × E → V), ContDiff ℝ ∞ g →
      RadialAlias.RadiallySupported a b g → ∀ A : ℝ, 0 ≤ A →
      (∀ j : ℕ, j ≤ m → ∀ R ∈ Ioo a b, ∀ Y : E,
        ‖iteratedFDeriv ℝ j g (R, Y)‖ ≤ A * logWeight cL cR a b p R) →
      ∀ z : ℝ × E, z.1 ∈ Ioo a b → ∀ j : ℕ, j ≤ m →
        ‖iteratedFDeriv ℝ j (physicalCompact d a b M v g) z‖ ≤
          K * A * logWeight cL cR a b p z.1 := by
  have haU : 0 < a ^ d := Real.rpow_pos_of_pos ha d
  have habU : a ^ d < b ^ d := Real.rpow_lt_rpow ha.le hab hd
  have hcLU : 0 < d ^ 2 * cL := mul_pos (sq_pos_of_pos hd) hcL
  have hcRU : 0 < d ^ 2 * cR := mul_pos (sq_pos_of_pos hd) hcR
  obtain ⟨KN, hKN, hbN⟩ := normalizeSource_finiteJets_uniform (E := E) (V := V) ha hab hd cL cR p m
  obtain ⟨KT, hKT, hbT⟩ := canonical_transport_finiteJets_uniform (E := E) (V := V) haU habU hcLU
    hcRU p m
  obtain ⟨KP, hKP, hbP⟩ := radial_comp_finiteJets_uniform (E := E) (V := V) a b
    (powerChart_contDiff ha d) m
  let Q := ((min 1 d) ^ p)⁻¹
  have hQ : 0 ≤ Q := (inv_pos.mpr (pow_pos (lt_min zero_lt_one hd) p)).le
  refine ⟨KP * KT * KN * Q, mul_nonneg (mul_nonneg (mul_nonneg hKP hKT) hKN) hQ, ?_⟩
  intro M v g hg hs A hA hsource z hz j hj
  have hnf := normalizeSource_contDiff ha hd hg
  have hns := normalizeSource_supported ha hab hd hs
  have hnsource : ∀ i : ℕ, i ≤ m → ∀ U ∈ Ioo (a ^ d) (b ^ d), ∀ Y : E,
      ‖iteratedFDeriv ℝ i (normalizeSource d a g) (U, Y)‖ ≤
        (KN * A) * logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p U :=
    fun i hi U hU Y => hbN g hg A hA hsource (U, Y) hU i hi
  let F := TransportPrimitive.compactIntegral (TransportPrimitive.interiorCutoff (a ^ d) (b ^ d))
    M v (normalizeSource d a g)
  have hF : ContDiff ℝ ∞ F := TransportPrimitive.compactIntegral_contDiff
    (TransportPrimitive.interiorCutoff_contDiff _ _) hnf hns
  have hU := powerChart_mem ha hd hz
  have hwU : 0 ≤ logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p (powerChart d a z.1) :=
    (weight_pos _ _ p (logPosition_mem haU hU)).le
  have ht (i : ℕ) (hi : i ≤ m) :
      ‖iteratedFDeriv ℝ i F (liftChart (powerChart d a) z)‖ ≤
        KT * (KN * A) * logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p (powerChart d a z.1)
          :=
    hbT M v _ hnf hns (KN * A) (mul_nonneg hKN hA) hnsource _ hU i hi
  have hp := hbP F hF z ⟨hz.1.le, hz.2.le⟩
    (KT * (KN * A) * logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p (powerChart d a z.1))
    (mul_nonneg (mul_nonneg hKT (mul_nonneg hKN hA)) hwU) ht j hj
  change ‖iteratedFDeriv ℝ j (physicalCompact d a b M v g) z‖ ≤
    KP * (KT * (KN * A) * logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p (powerChart d a
      z.1)) at hp
  rw [powerChart_eq ha (show a / 2 ≤ z.1 by linarith [hz.1]) d] at hp
  have hw := logWeight_power_forward ha hd hz cL cR p
  calc
    _ ≤ KP * (KT * (KN * A) * logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p (z.1 ^ d)) := hp
    _ ≤ KP * (KT * (KN * A) * (Q * logWeight cL cR a b p z.1)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hw (mul_nonneg hKT (mul_nonneg hKN hA))) hKP
    _ = (KP * KT * KN * Q) * A * logWeight cL cR a b p z.1 := by ring

/-- The physical/chart inverse maps the concrete all-jet mean class to itself.
The input and output weights are exactly the same logarithmic exponential. -/
theorem meanClass_physicalCompact {a b d cL cR : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hS : ∀ n, 1 ≤ S n)
    (α : ℝ) (M : ℕ → ℝ) (v : ℕ → E) (g : ℕ → ℝ × E → V)
    (hg : ∀ n, ContDiff ℝ ∞ (g n)) (hs : ∀ n, RadialAlias.RadiallySupported a b (g n))
    (hclass : WeightedClasses.MeanClass
      (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α g) :
    WeightedClasses.MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α
      (fun n => physicalCompact d a b (M n) (v n) (g n)) := by
  refine ⟨hclass.weight_nonneg, ?_, ?_⟩
  · exact fun n => (physicalCompact_contDiff ha hab hd (hg n) (hs n) (M n) (v n)).contDiffOn
  · intro m
    obtain ⟨C, hC, p, hsource⟩ := hclass.bounds m
    obtain ⟨K, hK, hbound⟩ := physicalCompact_finiteJets_uniform (E := E) (V := V)
      ha hab hd hcL hcR p m
    refine ⟨K * C, mul_nonneg hK hC, p, ?_⟩
    intro n z hz j hj
    change z.1 ∈ Ioo a b at hz
    have hA : 0 ≤ C * (ε n) ^ α * (S n) ^ p :=
      mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos (hε n) α).le)
        (pow_nonneg (zero_le_one.trans (hS n)) p)
    have hinput : ∀ i : ℕ, i ≤ m → ∀ R ∈ Ioo a b, ∀ Y : E,
        ‖iteratedFDeriv ℝ i (g n) (R, Y)‖ ≤
          (C * (ε n) ^ α * (S n) ^ p) * logWeight cL cR a b p R := by
      intro i hi R hR Y
      have hpnt := hsource n (R, Y) hR i hi
      rw [logStrip_majorant_eq ha hcL hcR ε S hε hεone hS α C p n (R, Y) hR] at hpnt
      exact hpnt
    have hout := hbound (M n) (v n) (g n) (hg n) (hs n)
      (C * (ε n) ^ α * (S n) ^ p) hA hinput z hz j hj
    rw [logStrip_majorant_eq ha hcL hcR ε S hε hεone hS α (K * C) p n z hz]
    simpa only [mul_assoc] using hout

theorem supported_meanClass_physicalCompact {a b d cL cR : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hS : ∀ n, 1 ≤ S n)
    (α : ℝ) (M : ℕ → ℝ) (v : ℕ → E) (g : ℕ → ℝ × E → V)
    (hg : ∀ n, ContDiff ℝ ∞ (g n)) (hs : ∀ n, RadialAlias.RadiallySupported a b (g n))
    (hclass : WeightedClasses.MeanClass
      (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α g) :
    let F := fun n => physicalCompact d a b (M n) (v n) (g n)
    (∀ n, ContDiff ℝ ∞ (F n)) ∧
      (∀ n, RadialAlias.RadiallySupported a b (F n)) ∧
      WeightedClasses.MeanClass (logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α F := by
  refine ⟨?_, ?_, meanClass_physicalCompact ha hab hd hcL hcR ε S hε hεone hS α M v g hg hs hclass⟩
  · exact fun n => physicalCompact_contDiff ha hab hd (hg n) (hs n) (M n) (v n)
  · exact fun n => physicalCompact_supported ha hab hd (hg n) (hs n) (M n) (v n)

end Weighted

end NavierStokes.RadialPullback
