/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.CounterexampleSchwartz
import LeanPool.QuadraticCarleson.QuadraticCarleson.ModularFailure

/-!
# The measurable lacunary operator and its Schwartz modular estimate

The canonical quadratic principal values are measurable as pointwise
limits of measurable symmetric truncations. Their countable dyadic
supremum is therefore a measurable extended-nonnegative-valued operator.
The modular estimate is tested on compactly supported Schwartz functions,
the literal intersection of Schwartz space with the paper's `L0Infinity`
test domain. No operator on arbitrary `L0Infinity` is defined here.
-/

open MeasureTheory Filter Set Asymptotics
open scoped SchwartzMap Topology ENNReal

namespace QuadraticCarleson


theorem measurable_quadraticHilbertTrunc (modulation ε : ℝ) (f : 𝓢(ℝ, ℂ)) :
    Measurable (quadraticHilbertTrunc modulation ε f) := by
  have hm : Measurable (fun p : ℝ × ℝ ↦
      f (p.1 - p.2) * phase (modulation * p.2 ^ 2) / (p.2 : ℂ)) := by
    unfold phase
    fun_prop
  exact (hm.stronglyMeasurable.integral_prod_right
    (ν := volume.restrict {t : ℝ | ε < |t|})).measurable

/-- The distributional principal value is a pointwise limit of measurable
functions, for the precise one-sided symmetric truncation filter. -/
theorem measurable_quadraticHilbertSchwartz (modulation : ℝ) (f : 𝓢(ℝ, ℂ)) :
    Measurable (quadraticHilbertSchwartz modulation f) := by
  apply measurable_of_tendsto_metrizable' (𝓝[>] (0 : ℝ))
    (fun ε ↦ measurable_quadraticHilbertTrunc modulation ε f)
  exact tendsto_pi_nhds.mpr (fun x ↦ hasQuadraticPrincipalValue_schwartz modulation f x)

theorem measurable_lacunaryQuadraticCarlesonSchwartz (f : 𝓢(ℝ, ℂ)) :
    Measurable (lacunaryQuadraticCarlesonSchwartz f) := by
  exact Measurable.iSup (fun n : ℤ ↦
    (measurable_quadraticHilbertSchwartz (dyadicModulation n) f).norm.ennreal_ofReal)

theorem schwartzFlipTranslate_real_smul (a : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    schwartzFlipTranslate (a • f) x = a • schwartzFlipTranslate f x := by
  ext y
  simp only [schwartzFlipTranslate_apply, smul_apply]

theorem quadraticHilbertSchwartz_real_smul (modulation a : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    quadraticHilbertSchwartz modulation (a • f) x =
      a • quadraticHilbertSchwartz modulation f x := by
  unfold quadraticHilbertSchwartz
  rw [schwartzFlipTranslate_real_smul]
  exact ContinuousLinearMap.map_smul_of_tower (quadraticKernelDistribution modulation) a _

/-- Exact scalar homogeneity retains infinite suprema and also covers
negative and zero real scalars through their absolute value. -/
theorem lacunaryQuadraticCarlesonSchwartz_real_smul (a : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    lacunaryQuadraticCarlesonSchwartz (a • f) x =
      ENNReal.ofReal |a| * lacunaryQuadraticCarlesonSchwartz f x := by
  unfold lacunaryQuadraticCarlesonSchwartz
  rw [ENNReal.mul_iSup]
  congr 1
  funext n
  rw [quadraticHilbertSchwartz_real_smul, norm_smul, Real.norm_eq_abs,
    ENNReal.ofReal_mul (abs_nonneg a)]

/-- A measurable operator defined on all Schwartz functions. -/
structure SchwartzNonnegativeOperator where
  /-- The measurable nonnegative function assigned to each Schwartz input. -/
  toFun : 𝓢(ℝ, ℂ) → ℝ → ℝ≥0∞
  measurable_toFun : ∀ f, Measurable (toFun f)

instance : CoeFun SchwartzNonnegativeOperator (fun _ ↦ 𝓢(ℝ, ℂ) → ℝ → ℝ≥0∞) :=
  ⟨SchwartzNonnegativeOperator.toFun⟩

/-- The lacunary quadratic Carleson operator on Schwartz inputs. -/
noncomputable def lacunarySchwartzOperator : SchwartzNonnegativeOperator where
  toFun := lacunaryQuadraticCarlesonSchwartz
  measurable_toFun := measurable_lacunaryQuadraticCarlesonSchwartz

/-- Compatibility of the operator with multiplication of its input by a positive real scalar. -/
def SchwartzNonnegativeOperator.PositivelyHomogeneous (T : SchwartzNonnegativeOperator) : Prop :=
  ∀ a : ℝ, 0 < a → ∀ (f : 𝓢(ℝ, ℂ)) (x : ℝ),
    T (a • f) x = ENNReal.ofReal a * T f x

theorem lacunarySchwartzOperator_positivelyHomogeneous :
    lacunarySchwartzOperator.PositivelyHomogeneous := by
  intro a ha f x
  change lacunaryQuadraticCarlesonSchwartz (a • f) x =
    ENNReal.ofReal a * lacunaryQuadraticCarlesonSchwartz f x
  simpa only [abs_of_pos ha] using lacunaryQuadraticCarlesonSchwartz_real_smul a f x

/-- A compactly supported Schwartz input belongs to the paper's domain;
this embeds test functions, not operators. -/
noncomputable def compactSchwartzToL0Infinity (f : 𝓢(ℝ, ℂ))
    (hf : HasCompactSupport (f : ℝ → ℂ)) : L0Infinity where
  toFun := f
  measurable_toFun := f.continuous.measurable
  bounded_toFun := ⟨SchwartzMap.seminorm ℂ 0 0 f, fun x ↦ f.norm_le_seminorm ℂ x⟩
  hasCompactSupport_toFun := hf

@[simp] theorem compactSchwartzToL0Infinity_apply (f : 𝓢(ℝ, ℂ))
    (hf : HasCompactSupport (f : ℝ → ℂ)) (x : ℝ) :
    compactSchwartzToL0Infinity f hf x = f x := rfl

/-- The set where a nonnegative Schwartz operator exceeds the given real level. -/
def schwartzOperatorLevelSet (T : SchwartzNonnegativeOperator) (f : 𝓢(ℝ, ℂ))
    (α : ℝ) : Set ℝ := {x | ENNReal.ofReal α < T f x}

theorem measurableSet_schwartzOperatorLevelSet (T : SchwartzNonnegativeOperator)
    (f : 𝓢(ℝ, ℂ)) (α : ℝ) : MeasurableSet (schwartzOperatorLevelSet T f α) :=
  measurableSet_lt measurable_const (T.measurable_toFun f)

/-- The integral of the Young function of the input norm divided by the level parameter. -/
noncomputable def schwartzModularMass (Φ : YoungFunction) (f : 𝓢(ℝ, ℂ)) (α : ℝ) : ℝ :=
  ∫ x : ℝ, Φ (‖f x‖ / α)

/-- The exact restriction of the paper's estimate to smooth compactly
supported inputs, with no assumed definition on rougher functions. -/
def HasSchwartzPhiModularEstimate (Φ : YoungFunction) (T : SchwartzNonnegativeOperator) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (f : 𝓢(ℝ, ℂ)), HasCompactSupport (f : ℝ → ℂ) →
    ∀ α : ℝ, 0 < α → volume (schwartzOperatorLevelSet T f α) ≤
      ENNReal.ofReal C * ∫⁻ x : ℝ, ENNReal.ofReal (Φ (‖f x‖ / α))

theorem schwartzModularMass_nonneg (Φ : YoungFunction) (f : 𝓢(ℝ, ℂ))
    {α : ℝ} (hα : 0 < α) : 0 ≤ schwartzModularMass Φ f α :=
  integral_nonneg (fun _x ↦ Φ.nonneg (div_nonneg (norm_nonneg _) hα.le))

theorem ofReal_schwartzModularMass_eq_lintegral (Φ : YoungFunction) (f : 𝓢(ℝ, ℂ))
    (hf : HasCompactSupport (f : ℝ → ℂ)) {α : ℝ} (hα : 0 < α) :
    ENNReal.ofReal (schwartzModularMass Φ f α) =
      ∫⁻ x : ℝ, ENNReal.ofReal (Φ (‖f x‖ / α)) :=
  ofReal_modularMass_eq_lintegral Φ (compactSchwartzToL0Infinity f hf) hα

theorem hasSchwartzPhiModularEstimate_iff_real (Φ : YoungFunction)
    (T : SchwartzNonnegativeOperator) :
    HasSchwartzPhiModularEstimate Φ T ↔
      ∃ C : ℝ, 0 < C ∧ ∀ (f : 𝓢(ℝ, ℂ)), HasCompactSupport (f : ℝ → ℂ) →
        ∀ α : ℝ, 0 < α → volume (schwartzOperatorLevelSet T f α) ≤
          ENNReal.ofReal (C * schwartzModularMass Φ f α) := by
  unfold HasSchwartzPhiModularEstimate
  constructor <;> rintro ⟨C, hC, h⟩ <;> refine ⟨C, hC, fun f hf α hα ↦ ?_⟩
  · simpa only [← ofReal_schwartzModularMass_eq_lintegral Φ f hf hα,
      ENNReal.ofReal_mul hC.le] using h f hf α hα
  · simpa only [← ofReal_schwartzModularMass_eq_lintegral Φ f hf hα,
      ENNReal.ofReal_mul hC.le] using h f hf α hα

/-- Abstract contradiction on the exact smooth compact-support test class. -/
theorem not_hasSchwartzPhiModularEstimate_of_sequence (Φ : YoungFunction)
    (T : SchwartzNonnegativeOperator) (f : ℕ → 𝓢(ℝ, ℂ))
    (hf : ∀ N, HasCompactSupport (f N : ℝ → ℂ)) (α : ℕ → ℝ)
    (hα : ∀ᶠ N in atTop, 0 < α N)
    (hmod : (fun N ↦ schwartzModularMass Φ (f N) (α N))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)))
    {δ : ℝ} (hδ : 0 < δ)
    (hlevel : ∀ᶠ N : ℕ in atTop, ENNReal.ofReal (δ * (N : ℝ)) ≤
      volume (schwartzOperatorLevelSet T (f N) (α N))) :
    ¬HasSchwartzPhiModularEstimate Φ T := by
  intro h
  obtain ⟨C, hC, hest⟩ := (hasSchwartzPhiModularEstimate_iff_real Φ T).mp h
  have hsmall := (hmod.const_mul_left C).bound (half_pos hδ)
  have hfalse : ∀ᶠ N : ℕ in atTop, False := by
    filter_upwards [hα, hsmall, hlevel, eventually_ge_atTop 1] with N hαN hs hl hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    have hmass : 0 ≤ C * schwartzModularMass Φ (f N) (α N) :=
      mul_nonneg hC.le (schwartzModularMass_nonneg Φ (f N) hαN)
    have hlreal : δ * (N : ℝ) ≤ C * schwartzModularMass Φ (f N) (α N) :=
      (ENNReal.ofReal_le_ofReal_iff hmass).mp (hl.trans (hest (f N) (hf N) (α N) hαN))
    rw [Real.norm_eq_abs, abs_of_nonneg hmass, Real.norm_eq_abs,
      abs_of_pos hNpos] at hs
    nlinarith [mul_pos hδ hNpos]
  obtain ⟨N, hN⟩ := hfalse.exists
  exact hN

theorem schwartzModularMass_real_smul_inv (Φ : YoungFunction) (f : 𝓢(ℝ, ℂ))
    {α : ℝ} (hα : 0 < α) :
    schwartzModularMass Φ (α⁻¹ • f) 1 = schwartzModularMass Φ f α := by
  unfold schwartzModularMass
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hα), div_one]
  congr 1
  ring

theorem schwartzOperatorLevelSet_real_smul_inv (T : SchwartzNonnegativeOperator)
    (hT : T.PositivelyHomogeneous) (f : 𝓢(ℝ, ℂ)) {α : ℝ} (hα : 0 < α) :
    schwartzOperatorLevelSet T (α⁻¹ • f) 1 = schwartzOperatorLevelSet T f α := by
  ext x
  change ENNReal.ofReal 1 < T (α⁻¹ • f) x ↔ ENNReal.ofReal α < T f x
  rw [hT α⁻¹ (inv_pos.mpr hα)]
  have hzero : ENNReal.ofReal α ≠ 0 := (ENNReal.ofReal_pos.mpr hα).ne'
  have hcancel : ENNReal.ofReal α * ENNReal.ofReal α⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hα.le, mul_inv_cancel₀ hα.ne', ENNReal.ofReal_one]
  have h := ENNReal.mul_lt_mul_iff_right (b := ENNReal.ofReal 1)
    (c := ENNReal.ofReal α⁻¹ * T f x) hzero ENNReal.ofReal_ne_top
  simpa only [ENNReal.ofReal_one, mul_one, ← mul_assoc, hcancel, one_mul] using h.symm

theorem counterexampleSchwartz_hasCompactSupport (N : ℕ) :
    HasCompactSupport (counterexampleSchwartz N : ℝ → ℂ) :=
  counterexample_hasCompactSupport N

theorem hasCompactSupport_schwartz_real_smul (a : ℝ) (f : 𝓢(ℝ, ℂ))
    (hf : HasCompactSupport (f : ℝ → ℂ)) :
    HasCompactSupport (a • f : 𝓢(ℝ, ℂ)) := by
  change HasCompactSupport (fun x : ℝ ↦ a • f x)
  exact hf.comp_left (g := fun z : ℂ ↦ a • z) (smul_zero a)

/-- Every positive `κ` admits a unit-height witness taken explicitly from
the normalized sequence. The conclusion uses the nonnegative integral,
and neither the operator values nor the level-set measure must be finite. -/
theorem exists_unit_schwartz_modular_witness_of_sequence (Φ : YoungFunction)
    (T : SchwartzNonnegativeOperator) (hT : T.PositivelyHomogeneous)
    (f : ℕ → 𝓢(ℝ, ℂ)) (hf : ∀ N, HasCompactSupport (f N : ℝ → ℂ))
    (α : ℕ → ℝ) (hα : ∀ᶠ N in atTop, 0 < α N)
    (hmod : (fun N ↦ schwartzModularMass Φ (f N) (α N))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)))
    {δ : ℝ} (hδ : 0 < δ)
    (hlevel : ∀ᶠ N : ℕ in atTop, ENNReal.ofReal (δ * (N : ℝ)) ≤
      volume (schwartzOperatorLevelSet T (f N) (α N)))
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ N : ℕ, 0 < α N ∧ HasCompactSupport ((α N)⁻¹ • f N : 𝓢(ℝ, ℂ)) ∧
      (∫⁻ x : ℝ, ENNReal.ofReal (Φ (‖((α N)⁻¹ • f N) x‖))) <
        ENNReal.ofReal κ * volume (schwartzOperatorLevelSet T ((α N)⁻¹ • f N) 1) := by
  have hsmall := hmod.bound (half_pos (mul_pos hκ hδ))
  obtain ⟨N, hαN, hs, hl, hN⟩ :=
    (hα.and (hsmall.and (hlevel.and (eventually_ge_atTop 1)))).exists
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hg := hasCompactSupport_schwartz_real_smul (α N)⁻¹ (f N) (hf N)
  rw [Real.norm_eq_abs, abs_of_nonneg (schwartzModularMass_nonneg Φ (f N) hαN),
    Real.norm_eq_abs, abs_of_pos hNpos] at hs
  refine ⟨N, hαN, hg, ?_⟩
  have hint : (∫⁻ x : ℝ, ENNReal.ofReal (Φ (‖((α N)⁻¹ • f N) x‖))) =
      ENNReal.ofReal (schwartzModularMass Φ ((α N)⁻¹ • f N) 1) := by
    simpa only [div_one] using
      (ofReal_schwartzModularMass_eq_lintegral Φ ((α N)⁻¹ • f N) hg zero_lt_one).symm
  rw [hint, schwartzModularMass_real_smul_inv Φ (f N) hαN,
    schwartzOperatorLevelSet_real_smul_inv T hT (f N) hαN]
  calc
    ENNReal.ofReal (schwartzModularMass Φ (f N) (α N)) <
        ENNReal.ofReal (κ * (δ * (N : ℝ))) := by
      apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      nlinarith [mul_pos (mul_pos hκ hδ) hNpos]
    _ = ENNReal.ofReal κ * ENNReal.ofReal (δ * (N : ℝ)) := ENNReal.ofReal_mul hκ.le
    _ ≤ ENNReal.ofReal κ * volume (schwartzOperatorLevelSet T (f N) (α N)) := by gcongr

theorem schwartzModularMass_counterexample_height_isLittleO (Φ : YoungFunction)
    (hΦ : GrowsSlowerThanEndpoint Φ) {c : ℝ} (hc : 0 < c) :
    (fun N ↦ schwartzModularMass Φ (counterexampleSchwartz N) (counterexampleHeight c N))
      =o[atTop] (fun N : ℕ ↦ (N : ℝ)) :=
  modularMass_counterexample_height_isLittleO Φ hΦ hc

/-- The remaining lower bound has precisely the paper's non-strict level,
height, and linear-in-`N` measure, now for the actual lacunary operator. -/
theorem not_hasSchwartzPhiModularEstimate_lacunary_of_counterexample_lower_bound
    (Φ : YoungFunction) (hΦ : GrowsSlowerThanEndpoint Φ)
    {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hlevel : ∀ᶠ N : ℕ in atTop, ENNReal.ofReal (δ * (N : ℝ)) ≤
      volume {x | ENNReal.ofReal (counterexampleHeight c N) ≤
        lacunaryQuadraticCarlesonSchwartz (counterexampleSchwartz N) x}) :
    ¬HasSchwartzPhiModularEstimate Φ lacunarySchwartzOperator := by
  apply not_hasSchwartzPhiModularEstimate_of_sequence Φ lacunarySchwartzOperator
    counterexampleSchwartz counterexampleSchwartz_hasCompactSupport
    (counterexampleHeight (c / 2)) (eventually_counterexampleHeight_pos (half_pos hc))
    (schwartzModularMass_counterexample_height_isLittleO Φ hΦ (half_pos hc)) hδ
  filter_upwards [hlevel, eventually_counterexampleHeight_pos hc] with N hl hN
  apply hl.trans (measure_mono ?_)
  intro x hx
  change ENNReal.ofReal (counterexampleHeight (c / 2) N) <
    lacunaryQuadraticCarlesonSchwartz (counterexampleSchwartz N) x
  apply lt_of_lt_of_le _ hx
  apply (ENNReal.ofReal_lt_ofReal_iff hN).mpr
  have heq : counterexampleHeight (c / 2) N = counterexampleHeight c N / 2 := by
    unfold counterexampleHeight
    ring
  rw [heq]
  linarith

/-- The paper's witnesses are normalized members of the actual
`counterexampleSchwartz` family. Halving the given analytic height ensures
the required strict level `> 1`. The lower bound remains a hypothesis. -/
theorem exists_normalized_counterexampleSchwartz_modular_witness
    (Φ : YoungFunction) (hΦ : GrowsSlowerThanEndpoint Φ)
    {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hlevel : ∀ᶠ N : ℕ in atTop, ENNReal.ofReal (δ * (N : ℝ)) ≤
      volume {x | ENNReal.ofReal (counterexampleHeight c N) ≤
        lacunaryQuadraticCarlesonSchwartz (counterexampleSchwartz N) x})
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ N : ℕ, 0 < counterexampleHeight (c / 2) N ∧
      HasCompactSupport ((counterexampleHeight (c / 2) N)⁻¹ • counterexampleSchwartz N :
        𝓢(ℝ, ℂ)) ∧
      (∫⁻ x : ℝ, ENNReal.ofReal
        (Φ (‖((counterexampleHeight (c / 2) N)⁻¹ • counterexampleSchwartz N) x‖))) <
        ENNReal.ofReal κ * volume {x | 1 < lacunaryQuadraticCarlesonSchwartz
          ((counterexampleHeight (c / 2) N)⁻¹ • counterexampleSchwartz N) x} := by
  have hs : ∀ᶠ N : ℕ in atTop, ENNReal.ofReal (δ * (N : ℝ)) ≤
      volume (schwartzOperatorLevelSet lacunarySchwartzOperator (counterexampleSchwartz N)
        (counterexampleHeight (c / 2) N)) := by
    filter_upwards [hlevel, eventually_counterexampleHeight_pos hc] with N hl hN
    apply hl.trans (measure_mono ?_)
    intro x hx
    change ENNReal.ofReal (counterexampleHeight (c / 2) N) <
      lacunaryQuadraticCarlesonSchwartz (counterexampleSchwartz N) x
    apply lt_of_lt_of_le _ hx
    apply (ENNReal.ofReal_lt_ofReal_iff hN).mpr
    have heq : counterexampleHeight (c / 2) N = counterexampleHeight c N / 2 := by
      unfold counterexampleHeight
      ring
    rw [heq]
    linarith
  simpa only [schwartzOperatorLevelSet, ENNReal.ofReal_one, lacunarySchwartzOperator] using
    exists_unit_schwartz_modular_witness_of_sequence Φ lacunarySchwartzOperator
      lacunarySchwartzOperator_positivelyHomogeneous
      counterexampleSchwartz counterexampleSchwartz_hasCompactSupport
      (counterexampleHeight (c / 2)) (eventually_counterexampleHeight_pos (half_pos hc))
      (schwartzModularMass_counterexample_height_isLittleO Φ hΦ (half_pos hc)) hδ hs hκ

/-- The explicit `f_κ` conclusion for every `κ > 0`; the paper's
restriction `κ < 1` is unnecessary for this implication. -/
theorem exists_unit_schwartz_modular_witness_lacunary_of_counterexample_lower_bound
    (Φ : YoungFunction) (hΦ : GrowsSlowerThanEndpoint Φ)
    {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hlevel : ∀ᶠ N : ℕ in atTop, ENNReal.ofReal (δ * (N : ℝ)) ≤
      volume {x | ENNReal.ofReal (counterexampleHeight c N) ≤
        lacunaryQuadraticCarlesonSchwartz (counterexampleSchwartz N) x})
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ g : 𝓢(ℝ, ℂ), HasCompactSupport (g : ℝ → ℂ) ∧
      (∫⁻ x : ℝ, ENNReal.ofReal (Φ (‖g x‖))) <
        ENNReal.ofReal κ * volume {x | 1 < lacunaryQuadraticCarlesonSchwartz g x} := by
  obtain ⟨N, _, hg, hw⟩ :=
    exists_normalized_counterexampleSchwartz_modular_witness Φ hΦ hc hδ hlevel hκ
  exact ⟨(counterexampleHeight (c / 2) N)⁻¹ • counterexampleSchwartz N, hg, hw⟩

/-- Any independently defined ambient operator agreeing on smooth compact
inputs inherits the restricted estimate. This is a compatibility theorem,
not a definition of an extension by arbitrary values. -/
theorem HasPhiModularEstimate.schwartz_restriction (Φ : YoungFunction)
    (T : NonnegativeOperator) (S : SchwartzNonnegativeOperator)
    (hagree : ∀ (f : 𝓢(ℝ, ℂ)) (hf : HasCompactSupport (f : ℝ → ℂ)) (x : ℝ),
      T (compactSchwartzToL0Infinity f hf) x = S f x)
    (h : HasPhiModularEstimate Φ T) : HasSchwartzPhiModularEstimate Φ S := by
  obtain ⟨C, hC, hest⟩ := h
  refine ⟨C, hC, fun f hf α hα ↦ ?_⟩
  have heq : operatorLevelSet T (compactSchwartzToL0Infinity f hf) α =
      schwartzOperatorLevelSet S f α := by
    ext x
    change ENNReal.ofReal α < T (compactSchwartzToL0Infinity f hf) x ↔
      ENNReal.ofReal α < S f x
    rw [hagree]
  simpa only [heq, compactSchwartzToL0Infinity_apply] using
    hest (compactSchwartzToL0Infinity f hf) α hα

/-- Failure of the restricted estimate prevents a compatible ambient
operator from satisfying the paper's modular estimate. -/
theorem not_hasPhiModularEstimate_of_schwartz_restriction (Φ : YoungFunction)
    (T : NonnegativeOperator) (S : SchwartzNonnegativeOperator)
    (hagree : ∀ (f : 𝓢(ℝ, ℂ)) (hf : HasCompactSupport (f : ℝ → ℂ)) (x : ℝ),
      T (compactSchwartzToL0Infinity f hf) x = S f x)
    (hfailure : ¬HasSchwartzPhiModularEstimate Φ S) : ¬HasPhiModularEstimate Φ T := by
  intro h
  exact hfailure (HasPhiModularEstimate.schwartz_restriction Φ T S hagree h)

end QuadraticCarleson
