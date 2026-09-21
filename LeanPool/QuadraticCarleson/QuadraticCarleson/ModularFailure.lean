/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.CounterexampleModular

/-!
# Modular-estimate failure from counterexamples

The global modular estimate is defined for measurable extended-nonnegative
operators on `L0Infinity`, retaining infinite values. An abstract `o(N)`
contradiction criterion and exact positive-homogeneity normalization yield
unit-height witnesses. For the paper's `χ_N`, the modular bound is extended
to every fixed positive factor, and the non-strict analytic lower level is
converted to a strict level at half the height. The analytic lower bound
remains an explicit hypothesis, not an assertion in this file.
-/

open MeasureTheory Set Filter Asymptotics
open scoped Topology ENNReal

namespace QuadraticCarleson


/-- A measurable extended-nonnegative-valued operator on the paper's
space of bounded compactly supported measurable functions. -/
structure NonnegativeOperator where
  /-- The nonnegative measurable operator acting on compactly supported bounded test functions. -/
  toFun : L0Infinity → ℝ → ℝ≥0∞
  measurable_toFun : ∀ f, Measurable (toFun f)

instance : CoeFun NonnegativeOperator (fun _ ↦ L0Infinity → ℝ → ℝ≥0∞) :=
  ⟨NonnegativeOperator.toFun⟩

/-- The strict level set used in the definition of a modular estimate. -/
def operatorLevelSet (T : NonnegativeOperator) (f : L0Infinity) (α : ℝ) : Set ℝ :=
  {x | ENNReal.ofReal α < T f x}

theorem measurableSet_operatorLevelSet (T : NonnegativeOperator) (f : L0Infinity) (α : ℝ) :
    MeasurableSet (operatorLevelSet T f α) :=
  measurableSet_lt measurable_const (T.measurable_toFun f)

/-- The real-valued modular mass at a positive height. Its integrability
on `L0Infinity` is established below. -/
noncomputable def modularMass (Φ : YoungFunction) (f : L0Infinity) (α : ℝ) : ℝ :=
  ∫ x : ℝ, Φ (‖f x‖ / α)

theorem modularMass_nonneg (Φ : YoungFunction) (f : L0Infinity) {α : ℝ} (hα : 0 < α) :
    0 ≤ modularMass Φ f α :=
  integral_nonneg (fun _x ↦ Φ.nonneg (div_nonneg (norm_nonneg _) hα.le))

theorem measurable_modularIntegrand (Φ : YoungFunction) (f : L0Infinity)
    {α : ℝ} (hα : 0 < α) : Measurable (fun x : ℝ ↦ Φ (‖f x‖ / α)) := by
  have he : Continuous (fun t : ℝ ↦ Φ (max t 0)) :=
    Φ.continuousOn_nonneg.comp_continuous (continuous_id.max continuous_const)
      (by intro x; exact le_max_right x 0)
  have hm := he.measurable.comp (f.measurable_toFun.norm.div_const α)
  simpa only [Function.comp_def, max_eq_left (div_nonneg (norm_nonneg _) hα.le)] using hm

theorem integrable_modularIntegrand (Φ : YoungFunction) (f : L0Infinity)
    {α : ℝ} (hα : 0 < α) : Integrable (fun x : ℝ ↦ Φ (‖f x‖ / α)) := by
  let g : ℝ → ℝ := fun x ↦ Φ (‖f x‖ / α)
  have hg : HasCompactSupport g :=
    f.hasCompactSupport_toFun.comp_left
      (g := fun z : ℂ ↦ Φ (‖z‖ / α)) (by simp [Φ.map_zero])
  obtain ⟨C, hC⟩ := f.bounded_toFun
  have hCn : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  have hbound : ∀ x, ‖g x‖ ≤ Φ (C / α) := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (Φ.nonneg (div_nonneg (norm_nonneg _) hα.le))]
    exact Φ.strictMonoOn_nonneg.monotoneOn
      (div_nonneg (norm_nonneg _) hα.le) (div_nonneg hCn hα.le)
      (div_le_div_of_nonneg_right (hC x) hα.le)
  apply (integrableOn_iff_integrable_of_support_subset (subset_tsupport g)).mp
  exact volume.integrableOn_of_bounded hg.measure_lt_top.ne
    (measurable_modularIntegrand Φ f hα).aestronglyMeasurable
    (Eventually.of_forall hbound)

theorem ofReal_modularMass_eq_lintegral (Φ : YoungFunction) (f : L0Infinity)
    {α : ℝ} (hα : 0 < α) :
    ENNReal.ofReal (modularMass Φ f α) =
      ∫⁻ x : ℝ, ENNReal.ofReal (Φ (‖f x‖ / α)) :=
  ofReal_integral_eq_lintegral_ofReal (integrable_modularIntegrand Φ f hα)
    (Eventually.of_forall fun _x ↦ Φ.nonneg (div_nonneg (norm_nonneg _) hα.le))

/-- The paper's global, unweighted `Φ`-modular estimate. The codomain is
extended nonnegative, so infinite operator values and level-set measures
are retained. -/
def HasPhiModularEstimate (Φ : YoungFunction) (T : NonnegativeOperator) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (f : L0Infinity) (α : ℝ), 0 < α →
    volume (operatorLevelSet T f α) ≤
      ENNReal.ofReal C * ∫⁻ x : ℝ, ENNReal.ofReal (Φ (‖f x‖ / α))

/-- A modular estimate passes from an operator to every pointwise smaller
operator. This is the abstract step behind the paper's phrase “and therefore
the full operator as well”: the full supremum dominates the lacunary one. -/
theorem HasPhiModularEstimate.of_pointwise_le
    (Φ : YoungFunction) (S T : NonnegativeOperator)
    (hST : ∀ f x, S f x ≤ T f x)
    (hT : HasPhiModularEstimate Φ T) :
    HasPhiModularEstimate Φ S := by
  obtain ⟨C, hC, hbound⟩ := hT
  refine ⟨C, hC, fun f α hα ↦ ?_⟩
  apply (measure_mono ?_).trans (hbound f α hα)
  intro x hx
  exact hx.trans_le (hST f x)

theorem hasPhiModularEstimate_iff_real (Φ : YoungFunction) (T : NonnegativeOperator) :
    HasPhiModularEstimate Φ T ↔
      ∃ C : ℝ, 0 < C ∧ ∀ (f : L0Infinity) (α : ℝ), 0 < α →
        volume (operatorLevelSet T f α) ≤ ENNReal.ofReal (C * modularMass Φ f α) := by
  unfold HasPhiModularEstimate
  constructor <;> rintro ⟨C, hC, h⟩ <;> refine ⟨C, hC, fun f α hα ↦ ?_⟩
  · simpa only [← ofReal_modularMass_eq_lintegral Φ f hα,
      ENNReal.ofReal_mul hC.le] using h f α hα
  · simpa only [← ofReal_modularMass_eq_lintegral Φ f hα,
      ENNReal.ofReal_mul hC.le] using h f α hα

/-- A modular sequence of size `o(N)` cannot coexist with a level-set
measure bounded below by a positive multiple of `N` under a modular estimate. -/
theorem not_hasPhiModularEstimate_of_sequence (Φ : YoungFunction) (T : NonnegativeOperator)
    (f : ℕ → L0Infinity) (α : ℕ → ℝ)
    (hα : ∀ᶠ N in atTop, 0 < α N)
    (hmod : (fun N ↦ modularMass Φ (f N) (α N)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)))
    {δ : ℝ} (hδ : 0 < δ)
    (hlevel : ∀ᶠ N : ℕ in atTop, ENNReal.ofReal (δ * (N : ℝ)) ≤
      volume (operatorLevelSet T (f N) (α N))) :
    ¬HasPhiModularEstimate Φ T := by
  intro h
  obtain ⟨C, hC, hest⟩ := (hasPhiModularEstimate_iff_real Φ T).mp h
  have hsmall := (hmod.const_mul_left C).bound (half_pos hδ)
  have hfalse : ∀ᶠ N : ℕ in atTop, False := by
    filter_upwards [hα, hsmall, hlevel, eventually_ge_atTop 1] with N hαN hs hl hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    have hmass : 0 ≤ C * modularMass Φ (f N) (α N) :=
      mul_nonneg hC.le (modularMass_nonneg Φ (f N) hαN)
    have hlreal : δ * (N : ℝ) ≤ C * modularMass Φ (f N) (α N) :=
      (ENNReal.ofReal_le_ofReal_iff hmass).mp (hl.trans (hest (f N) (α N) hαN))
    rw [Real.norm_eq_abs, abs_of_nonneg hmass, Real.norm_eq_abs,
      abs_of_pos hNpos] at hs
    nlinarith [mul_pos hδ hNpos]
  obtain ⟨N, hN⟩ := hfalse.exists
  exact hN

/-- Real scalar multiplication preserves the paper's test-function space. -/
noncomputable def scaleL0Infinity (a : ℝ) (f : L0Infinity) : L0Infinity where
  toFun x := a • f x
  measurable_toFun := f.measurable_toFun.const_smul a
  bounded_toFun := by
    obtain ⟨C, hC⟩ := f.bounded_toFun
    refine ⟨‖a‖ * C, fun x ↦ ?_⟩
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg a)
  hasCompactSupport_toFun := f.hasCompactSupport_toFun.comp_left
    (g := fun z : ℂ ↦ a • z) (smul_zero a)

@[simp] theorem scaleL0Infinity_apply (a : ℝ) (f : L0Infinity) (x : ℝ) :
    scaleL0Infinity a f x = a • f x := rfl

/-- Positive homogeneity is stated pointwise, including infinite outputs. -/
def NonnegativeOperator.PositivelyHomogeneous (T : NonnegativeOperator) : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ (f : L0Infinity) (x : ℝ),
    T (scaleL0Infinity a f) x = ENNReal.ofReal a * T f x

theorem modularMass_scale_inv (Φ : YoungFunction) (f : L0Infinity)
    {α : ℝ} (hα : 0 < α) :
    modularMass Φ (scaleL0Infinity α⁻¹ f) 1 = modularMass Φ f α := by
  unfold modularMass
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [scaleL0Infinity_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hα), div_one]
  congr 1
  ring

/-- Dividing the input by the testing height transports its strict level
set exactly to height one, without requiring finite operator values. -/
theorem operatorLevelSet_scale_inv (T : NonnegativeOperator)
    (hT : T.PositivelyHomogeneous) (f : L0Infinity) {α : ℝ} (hα : 0 < α) :
    operatorLevelSet T (scaleL0Infinity α⁻¹ f) 1 = operatorLevelSet T f α := by
  ext x
  change ENNReal.ofReal 1 < T (scaleL0Infinity α⁻¹ f) x ↔
    ENNReal.ofReal α < T f x
  rw [hT α⁻¹ (inv_pos.mpr hα)]
  have hzero : ENNReal.ofReal α ≠ 0 := (ENNReal.ofReal_pos.mpr hα).ne'
  have hcancel : ENNReal.ofReal α * ENNReal.ofReal α⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hα.le, mul_inv_cancel₀ hα.ne', ENNReal.ofReal_one]
  have h := ENNReal.mul_lt_mul_iff_right (b := ENNReal.ofReal 1)
    (c := ENNReal.ofReal α⁻¹ * T f x) hzero ENNReal.ofReal_ne_top
  simpa only [ENNReal.ofReal_one, mul_one, ← mul_assoc, hcancel, one_mul] using h.symm

/-- The sequence criterion also supplies the normalized witnesses in the
paper: for every positive `κ`, a test function has modular mass less than
`κ` times the measure of its strict level set at height one. -/
theorem exists_unit_modular_witness_of_sequence (Φ : YoungFunction) (T : NonnegativeOperator)
    (hT : T.PositivelyHomogeneous) (f : ℕ → L0Infinity) (α : ℕ → ℝ)
    (hα : ∀ᶠ N in atTop, 0 < α N)
    (hmod : (fun N ↦ modularMass Φ (f N) (α N)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)))
    {δ : ℝ} (hδ : 0 < δ)
    (hlevel : ∀ᶠ N : ℕ in atTop, ENNReal.ofReal (δ * (N : ℝ)) ≤
      volume (operatorLevelSet T (f N) (α N)))
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ g : L0Infinity, ENNReal.ofReal (modularMass Φ g 1) <
      ENNReal.ofReal κ * volume (operatorLevelSet T g 1) := by
  have hsmall := hmod.bound (half_pos (mul_pos hκ hδ))
  obtain ⟨N, hαN, hs, hl, hN⟩ :=
    (hα.and (hsmall.and (hlevel.and (eventually_ge_atTop 1)))).exists
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  rw [Real.norm_eq_abs, abs_of_nonneg (modularMass_nonneg Φ (f N) hαN),
    Real.norm_eq_abs, abs_of_pos hNpos] at hs
  refine ⟨scaleL0Infinity (α N)⁻¹ (f N), ?_⟩
  rw [modularMass_scale_inv Φ (f N) hαN, operatorLevelSet_scale_inv T hT (f N) hαN]
  calc
    ENNReal.ofReal (modularMass Φ (f N) (α N)) <
        ENNReal.ofReal (κ * (δ * (N : ℝ))) := by
      apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      nlinarith [mul_pos (mul_pos hκ hδ) hNpos]
    _ = ENNReal.ofReal κ * ENNReal.ofReal (δ * (N : ℝ)) :=
      ENNReal.ofReal_mul hκ.le
    _ ≤ ENNReal.ofReal κ * volume (operatorLevelSet T (f N) (α N)) := by gcongr

/-- The same counterexample modular with an arbitrary fixed positive
factor. This factor is essential when normalizing a lower-bound height. -/
noncomputable def scaledCounterexampleModular (Φ : YoungFunction) (a : ℝ) (N : ℕ) : ℝ :=
  ∫ x : ℝ, Φ (a * ((N : ℝ) * ‖counterexample N x‖ / Real.log (N : ℝ)))

theorem scaledCounterexampleModular_eq (Φ : YoungFunction) (a : ℝ) {N : ℕ} (hN : 0 < N) :
    scaledCounterexampleModular Φ a N =
      ∫ x : ℝ, Φ (a * (packetSum N x / Real.log (N : ℝ))) := by
  simp only [scaledCounterexampleModular, scaled_counterexample_eq_packetSum hN]

theorem scaledCounterexampleModular_le_secant (Φ : YoungFunction) {a : ℝ} (ha : 0 < a)
    {C : ℝ} (hC : 0 < C) (hbound : ∀ x, baseBump x ≤ C)
    {N : ℕ} (hN : 0 < N) (hlog : 1 ≤ Real.log (N : ℝ)) :
    scaledCounterexampleModular Φ a N ≤
      (a * (Φ (Real.exp (a + C + (N : ℝ) ^ 2)) /
        Real.exp (a + C + (N : ℝ) ^ 2))) * ((N : ℝ) / Real.log (N : ℝ)) := by
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hc : Continuous (fun x ↦ a * (packetSum N x / Real.log (N : ℝ))) :=
    ((continuous_packetSum N).div_const _).const_mul a
  have hs : HasCompactSupport (fun x ↦ a * (packetSum N x / Real.log (N : ℝ))) :=
    (packetSum_hasCompactSupport N).comp_left
      (g := fun t : ℝ ↦ a * (t / Real.log (N : ℝ))) (by simp)
  have hn : ∀ x, 0 ≤ a * (packetSum N x / Real.log (N : ℝ)) :=
    fun x ↦ mul_nonneg ha.le (div_nonneg (packetSum_nonneg N x) hlogpos.le)
  have hM : ∀ x, a * (packetSum N x / Real.log (N : ℝ)) ≤
      Real.exp (a + C + (N : ℝ) ^ 2) := by
    intro x
    calc
      a * (packetSum N x / Real.log (N : ℝ)) ≤ a * packetSum N x :=
        mul_le_mul_of_nonneg_left (div_le_self (packetSum_nonneg N x) hlog) ha.le
      _ ≤ Real.exp a * Real.exp (C + (N : ℝ) ^ 2) :=
        mul_le_mul (by linarith [Real.add_one_le_exp a])
          (packetSum_le_exp hC hbound hN x) (packetSum_nonneg N x) (Real.exp_nonneg a)
      _ = Real.exp (a + C + (N : ℝ) ^ 2) := by rw [← Real.exp_add]; congr 1; ring
  rw [scaledCounterexampleModular_eq Φ a hN]
  calc
    (∫ x : ℝ, Φ (a * (packetSum N x / Real.log (N : ℝ)))) ≤
        (Φ (Real.exp (a + C + (N : ℝ) ^ 2)) / Real.exp (a + C + (N : ℝ) ^ 2)) *
          ∫ x : ℝ, a * (packetSum N x / Real.log (N : ℝ)) :=
      Φ.integral_le_secant hc hs hn (Real.exp_pos _) hM
    _ = _ := by rw [integral_const_mul, integral_div, packetSum_integral]; ring

/-- Fixed scalar factors preserve modular smallness. No doubling or
regularity assumption on the Young function beyond its definition is used. -/
theorem scaledCounterexampleModular_isLittleO (Φ : YoungFunction)
    (hΦ : GrowsSlowerThanEndpoint Φ) {a : ℝ} (ha : 0 < a) :
    scaledCounterexampleModular Φ a =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_baseBump_bound
  have hsec := (endpoint_secant_isLittleO_log Φ hΦ (a + C) (by positivity)).const_mul_left a
  have hcast : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  apply IsLittleO.of_bound
  intro ε hε
  filter_upwards [hsec.bound hε, hcast.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop 1] with N hs hNr hlog
  change 1 ≤ Real.log (N : ℝ) at hlog
  have hN : 0 < N := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hNr)
  have hl : 0 < Real.log (N : ℝ) := by linarith
  have hn : 0 ≤ scaledCounterexampleModular Φ a N := by
    rw [scaledCounterexampleModular_eq Φ a hN]
    exact integral_nonneg (fun x ↦ Φ.nonneg
      (mul_nonneg ha.le (div_nonneg (packetSum_nonneg N x) hl.le)))
  rw [Real.norm_eq_abs, abs_of_nonneg hn,
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N)]
  rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg ha.le (div_nonneg (Φ.nonneg (Real.exp_nonneg _)) (Real.exp_nonneg _))),
    Real.norm_eq_abs, abs_of_nonneg hl.le] at hs
  calc
    scaledCounterexampleModular Φ a N ≤
        (a * (Φ (Real.exp (a + C + (N : ℝ) ^ 2)) /
          Real.exp (a + C + (N : ℝ) ^ 2))) * ((N : ℝ) / Real.log (N : ℝ)) :=
      scaledCounterexampleModular_le_secant Φ ha hC hbound hN hlog
    _ ≤ (ε * Real.log (N : ℝ)) * ((N : ℝ) / Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hs (div_nonneg (Nat.cast_nonneg N) hl.le)
    _ = ε * (N : ℝ) := by field_simp

/-- The paper's normalized counterexample height, with its fixed
positive constant exposed. -/
noncomputable def counterexampleHeight (c : ℝ) (N : ℕ) : ℝ :=
  c * Real.log (N : ℝ) / (N : ℝ)

theorem eventually_counterexampleHeight_pos {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, 0 < counterexampleHeight c N := by
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hNr : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hN)
  exact div_pos (mul_pos hc (Real.log_pos hNr)) (by linarith)

theorem modularMass_counterexample_height (Φ : YoungFunction) (c : ℝ) (N : ℕ) :
    modularMass Φ (counterexampleL0Infinity N) (counterexampleHeight c N) =
      scaledCounterexampleModular Φ c⁻¹ N := by
  unfold modularMass scaledCounterexampleModular
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  change ‖counterexample N x‖ / (c * Real.log (N : ℝ) / (N : ℝ)) = _
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem modularMass_counterexample_height_isLittleO (Φ : YoungFunction)
    (hΦ : GrowsSlowerThanEndpoint Φ) {c : ℝ} (hc : 0 < c) :
    (fun N ↦ modularMass Φ (counterexampleL0Infinity N) (counterexampleHeight c N))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)) := by
  simpa only [modularMass_counterexample_height] using
    scaledCounterexampleModular_isLittleO Φ hΦ (inv_pos.mpr hc)

/-- Halving the height turns the paper's non-strict lower level set into
the strict level set appearing in a modular estimate. -/
theorem counterexample_nonstrict_level_subset (T : NonnegativeOperator) {c : ℝ}
    (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      {x | ENNReal.ofReal (counterexampleHeight c N) ≤ T (counterexampleL0Infinity N) x} ⊆
        operatorLevelSet T (counterexampleL0Infinity N) (counterexampleHeight (c / 2) N) := by
  filter_upwards [eventually_counterexampleHeight_pos hc] with N hN
  intro x hx
  change ENNReal.ofReal (counterexampleHeight (c / 2) N) < T (counterexampleL0Infinity N) x
  apply lt_of_lt_of_le _ hx
  apply (ENNReal.ofReal_lt_ofReal_iff hN).mpr
  have heq : counterexampleHeight (c / 2) N = counterexampleHeight c N / 2 := by
    unfold counterexampleHeight
    ring
  rw [heq]
  linarith

/-- The exact remaining analytic input for modular failure: the paper's
counterexample has a non-strict lower level set of measure at least `δN`
at height `c log(N)/N`. This theorem does not assert that input. -/
theorem not_hasPhiModularEstimate_of_counterexample_lower_bound (Φ : YoungFunction)
    (hΦ : GrowsSlowerThanEndpoint Φ) (T : NonnegativeOperator)
    {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hlevel : ∀ᶠ N : ℕ in atTop, ENNReal.ofReal (δ * (N : ℝ)) ≤
      volume {x | ENNReal.ofReal (counterexampleHeight c N) ≤
        T (counterexampleL0Infinity N) x}) :
    ¬HasPhiModularEstimate Φ T := by
  apply not_hasPhiModularEstimate_of_sequence Φ T counterexampleL0Infinity
    (counterexampleHeight (c / 2)) (eventually_counterexampleHeight_pos (half_pos hc))
    (modularMass_counterexample_height_isLittleO Φ hΦ (half_pos hc)) hδ
  filter_upwards [hlevel, counterexample_nonstrict_level_subset T hc] with N hl hs
  exact hl.trans (measure_mono hs)

/-- The normalized `f_κ` conclusion, conditional only on the operator's
positive homogeneity and the still-separate analytic lower bound. -/
theorem exists_unit_modular_witness_of_counterexample_lower_bound (Φ : YoungFunction)
    (hΦ : GrowsSlowerThanEndpoint Φ) (T : NonnegativeOperator)
    (hT : T.PositivelyHomogeneous) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hlevel : ∀ᶠ N : ℕ in atTop, ENNReal.ofReal (δ * (N : ℝ)) ≤
      volume {x | ENNReal.ofReal (counterexampleHeight c N) ≤
        T (counterexampleL0Infinity N) x})
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ g : L0Infinity, ENNReal.ofReal (modularMass Φ g 1) <
      ENNReal.ofReal κ * volume (operatorLevelSet T g 1) := by
  apply exists_unit_modular_witness_of_sequence Φ T hT counterexampleL0Infinity
    (counterexampleHeight (c / 2)) (eventually_counterexampleHeight_pos (half_pos hc))
    (modularMass_counterexample_height_isLittleO Φ hΦ (half_pos hc)) hδ _ hκ
  filter_upwards [hlevel, counterexample_nonstrict_level_subset T hc] with N hl hs
  exact hl.trans (measure_mono hs)

end QuadraticCarleson
