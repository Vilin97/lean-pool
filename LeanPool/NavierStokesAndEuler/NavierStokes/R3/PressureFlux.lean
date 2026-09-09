/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.PressureFluxTest
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.PressureRecoveryHelpers
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszTestOperators
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.LocalizedTensorBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ActualPressureFlux
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.HeatKernelCommutator
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-!
# Canonical pressure flux

The pressure is paired with compact smooth tests through its canonical Riesz
functional. Every integral used to split the weighted pairing is shown to be
integrable before its norm is estimated.
-/


noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology BigOperators

namespace NavierStokesR3.PressureFlux

open ProblemStatement Comparison

theorem lpNorm_ofReal (p : ℝ≥0∞) (f : Space → ℝ) :
    comparisonLpNorm p (fun x => (f x : ℂ)) = comparisonLpNorm p f := by
  apply congrArg ENNReal.toReal
  exact eLpNorm_congr_norm_ae (Eventually.of_forall fun x => Complex.norm_real (f x))

theorem norm_fderiv_ofReal {f : Space → ℝ} {x : Space}
    (hf : DifferentiableAt ℝ f x) :
    ‖fderiv ℝ (fun y => (f y : ℂ)) x‖ = ‖fderiv ℝ f x‖ := by
  have hd := (Complex.ofRealCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  simp only [Function.comp_def, Complex.ofRealCLM_apply] at hd
  rw [hd]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro y
    change ‖(fderiv ℝ f x y : ℂ)‖ ≤ ‖fderiv ℝ f x‖ * ‖y‖
    simpa only [Complex.norm_real] using (fderiv ℝ f x).le_opNorm y
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro y
    have h := (Complex.ofRealCLM.comp (fderiv ℝ f x)).le_opNorm y
    change ‖(fderiv ℝ f x y : ℂ)‖ ≤ _ at h
    simpa only [Complex.norm_real] using h

theorem lpNorm_fderiv_realTest (p : ℝ≥0∞) (f : Space → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    comparisonLpNorm p (fderiv ℝ (fun x => PressureRecovery.realTest f hf hc x)) =
      comparisonLpNorm p (fderiv ℝ f) := by
  apply congrArg ENNReal.toReal
  apply eLpNorm_congr_norm_ae
  exact Eventually.of_forall fun x =>
    norm_fderiv_ofReal ((contDiff_infty.1 hf 1).differentiable (by simp) x)

theorem cutoff_lipschitz {R : ℝ} (hR : 0 < R) (x y : Space) :
    |ComparisonCutoffs.cutoff R x - ComparisonCutoffs.cutoff R y| ≤
      (ComparisonCutoffs.derivativeConstant 1 / R) * ‖x - y‖ := by
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ (univ : Set Space)) =>
      (contDiff_infty.1 (ComparisonCutoffs.cutoff_smooth R) 1).differentiable (by simp) z)
    (fun z (_ : z ∈ (univ : Set Space)) => ComparisonCutoffs.cutoff_fderiv_le hR z)
    (convex_univ : Convex ℝ (univ : Set Space)) (mem_univ y) (mem_univ x)
  exact h

private instance holder_six_fifths_six :
    ENNReal.HolderTriple (6 / 5) 6 1 := ⟨by
  have hz : (6 / 5 : ℝ≥0∞) ≠ 0 :=
    (ENNReal.toReal_pos_iff.mp (by norm_num : 0 < (6 / 5 : ℝ≥0∞).toReal)).1.ne'
  have hn := ENNReal.inv_ne_top.mpr hz
  apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.add_ne_top.mpr ⟨hn, by norm_num⟩)
    (by norm_num)).mp
  rw [ENNReal.toReal_add hn (by norm_num)]
  norm_num⟩

theorem integrable_holder_pair {f : Space → ℝ} {g : Space → ℂ}
    (hf : MemLp f (6 / 5) volume) (hg : MemLp g 6 volume) :
    Integrable (fun x => (f x : ℂ) * g x) volume :=
  hf.ofReal.integrable_mul hg

theorem norm_holder_pair_le {f : Space → ℝ} {g : Space → ℂ}
    (hf : MemLp f (6 / 5) volume) (hg : MemLp g 6 volume) :
    ‖∫ x, (f x : ℂ) * g x‖ ≤ comparisonLpNorm (6 / 5) f * comparisonLpNorm 6 g := by
  have hfc : MemLp (fun x => (f x : ℂ)) (6 / 5) volume := hf.ofReal
  have he : eLpNorm (fun x => (f x : ℂ) * g x) 1 volume ≤
      eLpNorm (fun x => (f x : ℂ)) (6 / 5) volume * eLpNorm g 6 volume := by
    simpa only [ENNReal.coe_one, one_mul] using
      eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hfc.1 hg.1
        (fun a b : ℂ => a * b) 1
        (Eventually.of_forall fun x => by simp [nnnorm_mul])
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top hfc.eLpNorm_ne_top hg.eLpNorm_ne_top) he
  change comparisonLpNorm 1 (fun x => (f x : ℂ) * g x) ≤
    (eLpNorm (fun x => (f x : ℂ)) (6 / 5) volume * eLpNorm g 6 volume).toReal at ht
  rw [ENNReal.toReal_mul] at ht
  change comparisonLpNorm 1 (fun x => (f x : ℂ) * g x) ≤
    comparisonLpNorm (6 / 5) (fun x => (f x : ℂ)) * comparisonLpNorm 6 g at ht
  rw [lpNorm_ofReal] at ht
  calc
    ‖∫ x, (f x : ℂ) * g x‖ ≤ ∫ x, ‖(f x : ℂ) * g x‖ := norm_integral_le_integral_norm _
    _ = comparisonLpNorm 1 (fun x => (f x : ℂ) * g x) :=
      (LpNormTools.lpNorm_one_eq_integral_norm (integrable_holder_pair hf hg)).symm
    _ ≤ _ := ht

/-- The scalar test in the localized pressure flux. -/
noncomputable def fluxFunction (χ : Space → ℝ) (w : Space → Space) (x : Space) : ℝ :=
  fderiv ℝ χ x (w x)

theorem fluxFunction_smooth {χ : Space → ℝ} {w : Space → Space}
    (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fluxFunction χ w) :=
  (hχ.fderiv_right (m := ∞) (by simp)).clm_apply hw

theorem fluxFunction_compact {χ : Space → ℝ} (hc : HasCompactSupport χ)
    (w : Space → Space) : HasCompactSupport (fluxFunction χ w) := by
  apply (hc.fderiv ℝ).mono
  intro x hx
  change fderiv ℝ χ x ≠ 0
  intro hz
  apply hx
  simp [fluxFunction, hz]

/-- The raw complex canonical pairing, with no pressure function selected. -/
def canonicalFlux (g : Fin 3 → Fin 3 → Space → ℝ) (f : Space → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (g i j) (PressureRecovery.realTest f hf hc)

theorem canonical_pair_integrable (g : Fin 3 → Fin 3 → Space → ℝ) (f : Space → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hg : ∀ i j, Integrable (g i j) volume) (i j : Fin 3) :
    Integrable (fun x => (g i j x : ℂ) *
      rieszTest i j (PressureRecovery.realTest f hf hc) x) volume := by
  apply RieszTestOperators.integrable_mul_rieszTest
  simpa only [Complex.ofRealCLM_apply] using Complex.ofRealCLM.integrable_comp (hg i j)

theorem norm_canonicalFlux_le {g : Fin 3 → Fin 3 → Space → ℝ} {f : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {C : ℝ}
    (hbound : ∀ i j : Fin 3,
      ‖pressurePair i j (g i j) (PressureRecovery.realTest f hf hc)‖ ≤ C) :
    ‖canonicalFlux g f hf hc‖ ≤ 9 * C := by
  calc
    _ ≤ ∑ i : Fin 3, ‖∑ j : Fin 3,
        pressurePair i j (g i j) (PressureRecovery.realTest f hf hc)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        ‖pressurePair i j (g i j) (PressureRecovery.realTest f hf hc)‖ :=
      Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, C :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hbound i j))
    _ = 9 * C := by simp; ring

/-- The compact Schwartz test used on the uncommuted side of the Riesz operator. -/
def rTest (R : ℝ) (hR : 0 < R) (w : Space → Space) (hw : ContDiff ℝ ∞ w) :
    ComplexTest :=
  PressureRecovery.realTest (PressureFluxTest.cutoffTest R w)
    (PressureFluxTest.cutoffTest_smooth R hw) (PressureFluxTest.cutoffTest_hasCompactSupport hR w)

/-- The actual flux test `Dχ_R[w]`, represented in the Schwartz space. -/
def fluxTest (R : ℝ) (hR : 0 < R) (w : Space → Space) (hw : ContDiff ℝ ∞ w) :
    ComplexTest :=
  PressureRecovery.realTest (fluxFunction (ComparisonCutoffs.weight R) w)
    (fluxFunction_smooth (ComparisonCutoffs.weight_smooth R) hw)
    (fluxFunction_compact (ComparisonCutoffs.weight_hasCompactSupport hR) w)

@[simp] theorem rTest_apply (R : ℝ) (hR : 0 < R) (w : Space → Space)
    (hw : ContDiff ℝ ∞ w) (x : Space) :
    rTest R hR w hw x = (PressureFluxTest.cutoffTest R w x : ℂ) := rfl

@[simp] theorem fluxTest_apply (R : ℝ) (hR : 0 < R) (w : Space → Space)
    (hw : ContDiff ℝ ∞ w) (x : Space) :
    fluxTest R hR w hw x = (fderiv ℝ (ComparisonCutoffs.weight R) x (w x) : ℂ) := rfl

theorem fluxTest_eq_multiplier_rTest (R : ℝ) (hR : 0 < R) (w : Space → Space)
    (hw : ContDiff ℝ ∞ w) (x : Space) :
    fluxTest R hR w hw x = ComparisonCutoffs.cutoff R x ^ 2 • rTest R hR w hw x := by
  rw [fluxTest_apply, rTest_apply, ← PressureFluxTest.cutoffTest_flux_identity]
  simp [ComparisonCutoffs.multiplier, Complex.real_smul]

theorem lpNorm_rTest (R : ℝ) (hR : 0 < R) (w : Space → Space)
    (hw : ContDiff ℝ ∞ w) (p : ℝ≥0∞) :
    comparisonLpNorm p (rTest R hR w hw : Space → ℂ) = comparisonLpNorm p
      (PressureFluxTest.cutoffTest R w) :=
  lpNorm_ofReal _ _

theorem lpNorm_fderiv_rTest (R : ℝ) (hR : 0 < R) (w : Space → Space)
    (hw : ContDiff ℝ ∞ w) :
    comparisonLpNorm 2 (fderiv ℝ (fun x => rTest R hR w hw x)) =
      comparisonLpNorm 2 (fderiv ℝ (PressureFluxTest.cutoffTest R w)) :=
  lpNorm_fderiv_realTest _ _ _ _

/-- Canonical flux for a time slice of the difference of two velocities. -/
def canonicalCutoffFlux (R : ℝ) (hR : 0 < R) (u v : VelocityField) (t : ℝ)
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x))) : ℂ :=
  canonicalFlux (tensorDiff u v t)
    (fluxFunction (ComparisonCutoffs.weight R) (fun x => (u - v) (t, x)))
    (fluxFunction_smooth (ComparisonCutoffs.weight_smooth R) (hu.sub hv))
    (fluxFunction_compact (ComparisonCutoffs.weight_hasCompactSupport hR) _)

theorem canonicalCutoffFlux_eq_sum (R : ℝ) (hR : 0 < R) (u v : VelocityField) (t : ℝ)
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x))) :
    canonicalCutoffFlux R hR u v t hu hv =
      ∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (tensorDiff u v t i j)
        (fluxTest R hR (fun x => (u - v) (t, x)) (hu.sub hv)) := rfl

theorem norm_canonicalCutoffFlux_le (R : ℝ) (hR : 0 < R) (u v : VelocityField) (t : ℝ)
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x)))
    {C : ℝ} (hbound : ∀ i j : Fin 3, ‖pressurePair i j (tensorDiff u v t i j)
      (fluxTest R hR (fun x => (u - v) (t, x)) (hu.sub hv))‖ ≤ C) :
    ‖canonicalCutoffFlux R hR u v t hu hv‖ ≤ 9 * C :=
  norm_canonicalFlux_le _ _ hbound

theorem actual_flux_eq_canonicalCutoffFlux {T t R : ℝ} {u v : VelocityField}
    {p q : PressureField} (H : PressureRecovery.Hypotheses T u v p q)
    (ht : t ∈ Ioo 0 T) (hR : 0 < R)
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x))) :
    (∫ x, (p - q) (t, x) * fderiv ℝ (ComparisonCutoffs.weight R) x ((u - v) (t, x))) =
      (canonicalCutoffFlux R hR u v t hu hv).re := by
  simpa only [canonicalCutoffFlux, canonicalFlux, fluxFunction] using!
    ActualPressureFlux.pressure_flux_eq_canonical H ht
      (ComparisonCutoffs.weight_smooth R) (ComparisonCutoffs.weight_hasCompactSupport hR)

theorem actual_flux_integrable_and_le_canonicalNorm {T t R : ℝ} {u v : VelocityField}
    {p q : PressureField} (H : PressureRecovery.Hypotheses T u v p q)
    (ht : t ∈ Ioo 0 T) (hR : 0 < R)
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x))) :
    Integrable (fun x => (p - q) (t, x) *
      fderiv ℝ (ComparisonCutoffs.weight R) x ((u - v) (t, x))) volume ∧
    |∫ x, (p - q) (t, x) * fderiv ℝ (ComparisonCutoffs.weight R) x ((u - v) (t, x))| ≤
      ‖canonicalCutoffFlux R hR u v t hu hv‖ := by
  refine ⟨ActualPressureFlux.actual_pressure_flux_integrable H ht
    (ComparisonCutoffs.weight_smooth R) (ComparisonCutoffs.weight_hasCompactSupport hR), ?_⟩
  rw [actual_flux_eq_canonicalCutoffFlux H ht hR hu hv]
  exact Complex.abs_re_le_norm _

/-- The commutator integral in the heat-kernel estimate. -/
def commutatorPair (i j : Fin 3) (h g : Space → ℝ) (ψ ψh : ComplexTest) : ℂ :=
  ∫ x, g x • (rieszTest i j ψh x - h x • rieszTest i j ψ x)

theorem integrable_commutator_pair (i j : Fin 3) {h g : Space → ℝ}
    (hg : Integrable g volume) (hhg : MemLp (fun x => h x * g x) (6 / 5) volume)
    (ψ ψh : ComplexTest) :
    Integrable (fun x => g x • (rieszTest i j ψh x - h x • rieszTest i j ψ x)) volume := by
  have hgc : Integrable (fun x => (g x : ℂ)) volume := by
    simpa only [Complex.ofRealCLM_apply] using Complex.ofRealCLM.integrable_comp hg
  have hq := RieszTestOperators.integrable_mul_rieszTest i j ψh hgc
  have hl := integrable_holder_pair hhg (RieszTestOperators.memLp_rieszTest_six i j ψ)
  convert! hq.sub hl using 1
  funext x
  simp only [Pi.sub_apply, Complex.real_smul, Complex.ofReal_mul]
  ring

theorem pressurePair_decomposition (i j : Fin 3) {h g : Space → ℝ}
    (hg : Integrable g volume) (hhg : MemLp (fun x => h x * g x) (6 / 5) volume)
    (ψ ψh : ComplexTest) :
    pressurePair i j g ψh =
      (∫ x, (h x * g x : ℝ) * rieszTest i j ψ x) + commutatorPair i j h g ψ ψh := by
  have hgc : Integrable (fun x => (g x : ℂ)) volume := by
    simpa only [Complex.ofRealCLM_apply] using Complex.ofRealCLM.integrable_comp hg
  have hq := RieszTestOperators.integrable_mul_rieszTest i j ψh hgc
  have hl := integrable_holder_pair hhg (RieszTestOperators.memLp_rieszTest_six i j ψ)
  have he : commutatorPair i j h g ψ ψh = pressurePair i j g ψh -
      (∫ x, (h x * g x : ℝ) * rieszTest i j ψ x) := by
    rw [commutatorPair, pressurePair, ← integral_sub hq hl]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [Complex.real_smul, Complex.ofReal_mul]
      ring
  simpa only [add_comm] using (eq_sub_iff_add_eq.mp he).symm

theorem norm_pressurePair_le_local_commutator (i j : Fin 3) {h g : Space → ℝ}
    (hg : Integrable g volume) (hhg : MemLp (fun x => h x * g x) (6 / 5) volume)
    (ψ ψh : ComplexTest) :
    ‖pressurePair i j g ψh‖ ≤ comparisonLpNorm (6 / 5) (fun x => h x * g x) *
      comparisonLpNorm 6 (rieszTest i j ψ) + ‖commutatorPair i j h g ψ ψh‖ := by
  rw [pressurePair_decomposition i j hg hhg]
  exact (norm_add_le _ _).trans (add_le_add_left
    (norm_holder_pair_le hhg (RieszTestOperators.memLp_rieszTest_six i j ψ)) _)

/-- The fixed constant in the actual Riesz-test Sobolev inequality. -/
def rieszSobolevConstant : ℝ := 3 * WeightedSobolev.sobolevConstant

theorem rieszSobolevConstant_nonneg : 0 ≤ rieszSobolevConstant :=
  mul_nonneg (by norm_num) WeightedSobolev.sobolevConstant_nonneg

def localPairConstant : ℝ := rieszSobolevConstant * PressureFluxTest.cutoffDerivativeConstant

theorem localPairConstant_nonneg : 0 ≤ localPairConstant :=
  mul_nonneg rieszSobolevConstant_nonneg PressureFluxTest.cutoffDerivativeConstant_pos.le

theorem riesz_rTest_bound {R : ℝ} (hR : 0 < R) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hw2 : MemLp w 2 volume) (i j : Fin 3) :
    comparisonLpNorm 6 (rieszTest i j (rTest R hR w hw)) ≤ localPairConstant *
      (Real.sqrt (∫ x, ComparisonCutoffs.cutoff R x ^ 8 * gradientSq w x) / R +
        comparisonLpNorm 2 w / R ^ 2) := by
  calc
    _ ≤ rieszSobolevConstant * comparisonLpNorm 2 (fderiv ℝ (fun x => rTest R hR w hw x)) := by
      simpa only [rieszSobolevConstant, WeightedSobolev.sobolevConstant] using
        RieszTestOperators.lpNorm_six_rieszTest_le i j (rTest R hR w hw)
    _ = rieszSobolevConstant * comparisonLpNorm 2 (fderiv ℝ (PressureFluxTest.cutoffTest R w)) := by
      rw [lpNorm_fderiv_rTest]
    _ ≤ rieszSobolevConstant * ((PressureFluxTest.cutoffDerivativeConstant / R) *
        Real.sqrt (∫ x, ComparisonCutoffs.cutoff R x ^ 8 * gradientSq w x) +
          (PressureFluxTest.cutoffDerivativeConstant / R ^ 2) * comparisonLpNorm 2 w) :=
      mul_le_mul_of_nonneg_left (PressureFluxTest.cutoffTest_derivative_bound hR hw hw2).2
        rieszSobolevConstant_nonneg
    _ = _ := by unfold localPairConstant; ring

theorem rTest_four_bound {R : ℝ} (hR : 0 < R) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hw2 : MemLp w 2 volume) :
    comparisonLpNorm 4 (rTest R hR w hw : Space → ℂ) ≤
      (8 * ComparisonCutoffs.derivativeConstant 1 / R) * comparisonLpNorm 2 w ^ (1 / 4 : ℝ) *
        comparisonLpNorm 6 (fun x => ComparisonCutoffs.cutoff R x ^ 4 • w x) ^ (3 / 4 : ℝ) := by
  rw [lpNorm_rTest]
  exact (PressureFluxTest.cutoffTest_four_bound hR hw hw2).2

/-- The local part of one canonical pressure component is an actual integrable pairing. -/
theorem localized_pair_bound {R : ℝ} (hR : 0 < R) {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x)))
    (hw2 : MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hu3 : MemLp (fun x => u (t, x)) 3 volume) (i j : Fin 3) :
    Integrable (fun x => (ComparisonCutoffs.multiplier R x * tensorDiff u v t i j x : ℝ) *
      rieszTest i j (rTest R hR (fun x => (u - v) (t, x)) (hu.sub hv)) x) volume ∧
    ‖∫ x, (ComparisonCutoffs.multiplier R x * tensorDiff u v t i j x : ℝ) *
      rieszTest i j (rTest R hR (fun x => (u - v) (t, x)) (hu.sub hv)) x‖ ≤
      localPairConstant *
        (comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
            cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (1 / 2 : ℝ) +
          2 * comparisonLpNorm 2 (fun x => (u - v) (t, x)) * comparisonLpNorm 3 (fun x => u (t,
            x))) *
        (dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t / R +
          comparisonLpNorm 2 (fun x => (u - v) (t, x)) / R ^ 2) := by
  have ht := LocalizedTensorBounds.weighted_tensorDiff_bound
    (ComparisonCutoffs.cutoff_smooth R).continuous
    (ComparisonCutoffs.cutoff_hasCompactSupport hR) hu.continuous hv.continuous hw2 hu3
    (ComparisonCutoffs.cutoff_nonneg R) (ComparisonCutoffs.cutoff_le_one R) i j
  have hr := RieszTestOperators.memLp_rieszTest_six i j
    (rTest R hR (fun x => (u - v) (t, x)) (hu.sub hv))
  refine ⟨integrable_holder_pair ht.1 hr, ?_⟩
  have hM := LpNormTools.lpNorm_nonneg 2 (fun x => (u - v) (t, x))
  have hU := LpNormTools.lpNorm_nonneg 3 (fun x => u (t, x))
  have hB := LpNormTools.lpNorm_nonneg 6 (fun x => ComparisonCutoffs.cutoff R x ^ 4 • (u - v) (t,
    x))
  calc
    _ ≤ comparisonLpNorm (6 / 5) (fun x => ComparisonCutoffs.cutoff R x ^ 2 * tensorDiff u v t i j
      x) *
        comparisonLpNorm 6 (rieszTest i j (rTest R hR (fun x => (u - v) (t, x)) (hu.sub hv))) :=
      norm_holder_pair_le ht.1 hr
    _ ≤ (comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
            cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (1 / 2 : ℝ) +
          2 * comparisonLpNorm 2 (fun x => (u - v) (t, x)) * comparisonLpNorm 3 (fun x => u (t,
            x))) *
        (localPairConstant * (dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t / R +
          comparisonLpNorm 2 (fun x => (u - v) (t, x)) / R ^ 2)) := by
      apply mul_le_mul ht.2 (riesz_rTest_bound hR (hu.sub hv) hw2 i j)
        (LpNormTools.lpNorm_nonneg _ _)
      unfold cutoffL6
      positivity
    _ = _ := by ring

theorem norm_cutoff_pressurePair_le_local_commutator {R : ℝ} (hR : 0 < R)
    {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x)))
    (hw2 : MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hu3 : MemLp (fun x => u (t, x)) 3 volume) (i j : Fin 3)
    (hg : Integrable (tensorDiff u v t i j) volume) :
    ‖pressurePair i j (tensorDiff u v t i j)
      (fluxTest R hR (fun x => (u - v) (t, x)) (hu.sub hv))‖ ≤
      localPairConstant *
        (comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
            cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (1 / 2 : ℝ) +
          2 * comparisonLpNorm 2 (fun x => (u - v) (t, x)) * comparisonLpNorm 3 (fun x => u (t,
            x))) *
        (dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t / R +
          comparisonLpNorm 2 (fun x => (u - v) (t, x)) / R ^ 2) +
      ‖commutatorPair i j (ComparisonCutoffs.multiplier R) (tensorDiff u v t i j)
        (rTest R hR (fun x => (u - v) (t, x)) (hu.sub hv))
        (fluxTest R hR (fun x => (u - v) (t, x)) (hu.sub hv))‖ := by
  have ht := LocalizedTensorBounds.weighted_tensorDiff_bound
    (ComparisonCutoffs.cutoff_smooth R).continuous
    (ComparisonCutoffs.cutoff_hasCompactSupport hR) hu.continuous hv.continuous hw2 hu3
    (ComparisonCutoffs.cutoff_nonneg R) (ComparisonCutoffs.cutoff_le_one R) i j
  rw [pressurePair_decomposition i j hg ht.1]
  exact (norm_add_le _ _).trans (add_le_add_left (localized_pair_bound hR hu hv hw2 hu3 i j).2 _)

/-- The coefficient after fixing uniform bounds for the three data norms. -/
def uniformCoefficient (C₁ C₂ M₀ U₀ G₀ : ℝ) : ℝ :=
  C₁ * (M₀ ^ (3 / 2 : ℝ) + 2 * M₀ * U₀) * (M₀ + 1) +
    C₂ * G₀ * M₀ ^ (1 / 4 : ℝ)

theorem uniformCoefficient_nonneg {C₁ C₂ M₀ U₀ G₀ : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hM₀ : 0 ≤ M₀) (hU₀ : 0 ≤ U₀) (hG₀ : 0 ≤ G₀) :
    0 ≤ uniformCoefficient C₁ C₂ M₀ U₀ G₀ := by
  unfold uniformCoefficient
  positivity

/-- Collecting constants uses only the fixed data-norm bounds, not the radius. -/
theorem uniform_expression_bound {C₁ C₂ M₀ U₀ G₀ M U G A B R : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hM₀ : 0 ≤ M₀) (hU₀ : 0 ≤ U₀) (hG₀ : 0 ≤ G₀)
    (hM : 0 ≤ M) (hU : 0 ≤ U) (_hG : 0 ≤ G) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hMM : M ≤ M₀) (hUU : U ≤ U₀) (hGG : G ≤ G₀) (hR : 0 < R) :
    C₁ * (M ^ (3 / 2 : ℝ) * B ^ (1 / 2 : ℝ) + 2 * M * U) *
        (A / R + M / R ^ 2) +
      C₂ * G * M ^ (1 / 4 : ℝ) * R ^ (-(7 / 4 : ℝ)) * B ^ (3 / 4 : ℝ) ≤
    uniformCoefficient C₁ C₂ M₀ U₀ G₀ *
      ((B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2) +
        R ^ (-(7 / 4 : ℝ)) * B ^ (3 / 4 : ℝ)) := by
  have hMp := Real.rpow_le_rpow hM hMM (by norm_num : 0 ≤ (3 / 2 : ℝ))
  have hMp₄ := Real.rpow_le_rpow hM hMM (by norm_num : 0 ≤ (1 / 4 : ℝ))
  have hB₁ := Real.rpow_nonneg hB (1 / 2 : ℝ)
  have hB₃ := Real.rpow_nonneg hB (3 / 4 : ℝ)
  have hM₀p := Real.rpow_nonneg hM₀ (3 / 2 : ℝ)
  have hM₀p₄ := Real.rpow_nonneg hM₀ (1 / 4 : ℝ)
  have hRp := Real.rpow_nonneg hR.le (-(7 / 4 : ℝ))
  have hMU : 2 * M * U ≤ 2 * M₀ * U₀ :=
    mul_le_mul (mul_le_mul_of_nonneg_left hMM (by norm_num)) hUU hU (by positivity)
  have hT : M ^ (3 / 2 : ℝ) * B ^ (1 / 2 : ℝ) + 2 * M * U ≤
      (M₀ ^ (3 / 2 : ℝ) + 2 * M₀ * U₀) * (B ^ (1 / 2 : ℝ) + 1) := by
    have h := add_le_add (mul_le_mul_of_nonneg_right hMp hB₁) hMU
    have hm0u0 : 0 ≤ 2 * M₀ * U₀ := by positivity
    exact h.trans (by nlinarith only [hM₀p, mul_nonneg hm0u0 hB₁])
  have hAR : 0 ≤ A / R := div_nonneg hA hR.le
  have hInv : 0 ≤ 1 / R ^ 2 := by positivity
  have hD : A / R + M / R ^ 2 ≤ (M₀ + 1) * (A / R + 1 / R ^ 2) := by
    have hdiv := (div_le_div_iff_of_pos_right (sq_pos_of_pos hR)).2 hMM
    have hdiv' : M / R ^ 2 ≤ M₀ * (1 / R ^ 2) := by simpa only [mul_one_div] using hdiv
    nlinarith only [hdiv', mul_nonneg hM₀ hAR, hInv]
  have hlocal :
      C₁ * (M ^ (3 / 2 : ℝ) * B ^ (1 / 2 : ℝ) + 2 * M * U) * (A / R + M / R ^ 2) ≤
      (C₁ * (M₀ ^ (3 / 2 : ℝ) + 2 * M₀ * U₀) * (M₀ + 1)) *
        ((B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2)) := by
    calc
      _ ≤ (C₁ * ((M₀ ^ (3 / 2 : ℝ) + 2 * M₀ * U₀) * (B ^ (1 / 2 : ℝ) + 1))) *
          ((M₀ + 1) * (A / R + 1 / R ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hT hC₁) hD (by positivity) (by positivity)
      _ = _ := by ring
  have hcoeff : C₂ * G * M ^ (1 / 4 : ℝ) ≤ C₂ * G₀ * M₀ ^ (1 / 4 : ℝ) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hGG hC₂) hMp₄
      (Real.rpow_nonneg hM _) (mul_nonneg hC₂ hG₀)
  have hcomm : C₂ * G * M ^ (1 / 4 : ℝ) * R ^ (-(7 / 4 : ℝ)) * B ^ (3 / 4 : ℝ) ≤
      (C₂ * G₀ * M₀ ^ (1 / 4 : ℝ)) * (R ^ (-(7 / 4 : ℝ)) * B ^ (3 / 4 : ℝ)) := by
    calc
      _ = (C₂ * G * M ^ (1 / 4 : ℝ)) * (R ^ (-(7 / 4 : ℝ)) * B ^ (3 / 4 : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hRp hB₃)
  have hK₁ : 0 ≤ C₁ * (M₀ ^ (3 / 2 : ℝ) + 2 * M₀ * U₀) * (M₀ + 1) := by positivity
  have hK₂ : 0 ≤ C₂ * G₀ * M₀ ^ (1 / 4 : ℝ) := by positivity
  have hE₁ : 0 ≤ (B ^ (1 / 2 : ℝ) + 1) * (A / R + 1 / R ^ 2) := by positivity
  have hE₂ : 0 ≤ R ^ (-(7 / 4 : ℝ)) * B ^ (3 / 4 : ℝ) := mul_nonneg hRp hB₃
  unfold uniformCoefficient
  nlinarith only [add_le_add hlocal hcomm, mul_nonneg hK₁ hE₂, mul_nonneg hK₂ hE₁]

theorem rpow_three_fourths_div {R : ℝ} (hR : 0 < R) :
    R ^ (-(3 / 4 : ℝ)) / R = R ^ (-(7 / 4 : ℝ)) := by
  rw [div_eq_mul_inv, ← Real.rpow_neg_one R, ← Real.rpow_add hR]
  norm_num

/-- The fixed coefficient after combining the commutator and test-function bounds. -/
def commutatorConstant : ℝ :=
  (Comparison.rieszCommutatorConstant * max (2 * ComparisonCutoffs.derivativeConstant 1) 1) *
    (8 * ComparisonCutoffs.derivativeConstant 1)

theorem commutatorConstant_nonneg : 0 ≤ commutatorConstant := by
  have hH := Comparison.rieszCommutatorConstant_pos.le
  have hD := (ComparisonCutoffs.derivativeConstant_pos 1).le
  have hm : 0 ≤ max (2 * ComparisonCutoffs.derivativeConstant 1) 1 :=
    zero_le_one.trans (le_max_right _ _)
  unfold commutatorConstant
  positivity

theorem cutoff_commutator_bound {R : ℝ} (hR : 0 < R) {w : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hw2 : MemLp w 2 volume) {g : Space → ℝ}
    (hg : Integrable g volume) (i j : Fin 3) :
    ‖commutatorPair i j (ComparisonCutoffs.multiplier R) g
      (rTest R hR w hw) (fluxTest R hR w hw)‖ ≤
      commutatorConstant * comparisonLpNorm 1 g * comparisonLpNorm 2 w ^ (1 / 4 : ℝ) *
        R ^ (-(7 / 4 : ℝ)) *
          comparisonLpNorm 6 (fun x => ComparisonCutoffs.cutoff R x ^ 4 • w x) ^ (3 / 4 : ℝ) := by
  have h := Comparison.riesz_commutator_pair_bound i j hR
    (ComparisonCutoffs.cutoff_smooth R).continuous.measurable
    (ComparisonCutoffs.cutoff_mem_Icc R) (cutoff_lipschitz hR) hg
    (rTest R hR w hw) (fluxTest R hR w hw)
    (fluxTest_eq_multiplier_rTest R hR w hw) ((rTest R hR w hw).memLp 4)
  have hH := Comparison.rieszCommutatorConstant_pos.le
  have hD := (ComparisonCutoffs.derivativeConstant_pos 1).le
  have hm : 0 ≤ max (2 * ComparisonCutoffs.derivativeConstant 1) 1 :=
    zero_le_one.trans (le_max_right _ _)
  have hG := LpNormTools.lpNorm_nonneg 1 g
  have hRp := Real.rpow_nonneg hR.le (-(3 / 4 : ℝ))
  calc
    _ ≤ (Comparison.rieszCommutatorConstant * max (2 * ComparisonCutoffs.derivativeConstant 1) 1) *
        R ^ (-(3 / 4 : ℝ)) * comparisonLpNorm 1 g * comparisonLpNorm 4 (rTest R hR w hw : Space →
          ℂ) := h
    _ ≤ (Comparison.rieszCommutatorConstant * max (2 * ComparisonCutoffs.derivativeConstant 1) 1) *
        R ^ (-(3 / 4 : ℝ)) * comparisonLpNorm 1 g *
          ((8 * ComparisonCutoffs.derivativeConstant 1 / R) * comparisonLpNorm 2 w ^ (1 / 4 : ℝ) *
            comparisonLpNorm 6 (fun x => ComparisonCutoffs.cutoff R x ^ 4 • w x) ^ (3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (rTest_four_bound hR hw hw2) (by positivity)
    _ = _ := by
      rw [← rpow_three_fourths_div hR]
      unfold commutatorConstant
      ring

/-- One actual canonical pressure component, with the three data norms explicit. -/
theorem cutoff_pressurePair_bound {R : ℝ} (hR : 0 < R) {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x)))
    (hw2 : MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hu3 : MemLp (fun x => u (t, x)) 3 volume) (i j : Fin 3)
    (hg : Integrable (tensorDiff u v t i j) volume) :
    ‖pressurePair i j (tensorDiff u v t i j)
      (fluxTest R hR (fun x => (u - v) (t, x)) (hu.sub hv))‖ ≤
      localPairConstant *
        (comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
            cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (1 / 2 : ℝ) +
          2 * comparisonLpNorm 2 (fun x => (u - v) (t, x)) * comparisonLpNorm 3 (fun x => u (t,
            x))) *
        (dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t / R +
          comparisonLpNorm 2 (fun x => (u - v) (t, x)) / R ^ 2) +
      commutatorConstant * comparisonLpNorm 1 (tensorDiff u v t i j) *
        comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (1 / 4 : ℝ) * R ^ (-(7 / 4 : ℝ)) *
          cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (3 / 4 : ℝ) :=
  (norm_cutoff_pressurePair_le_local_commutator hR hu hv hw2 hu3 i j hg).trans
    (add_le_add_right (cutoff_commutator_bound hR (hu.sub hv) hw2 hg i j) _)

/-- The full canonical flux with an explicit bound on each tensor component's `L¹` norm. -/
theorem canonicalCutoffFlux_bound {R : ℝ} (hR : 0 < R) {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x)))
    (hw2 : MemLp (fun x => (u - v) (t, x)) 2 volume)
    (hu3 : MemLp (fun x => u (t, x)) 3 volume)
    (hg : ∀ i j : Fin 3, Integrable (tensorDiff u v t i j) volume)
    {G : ℝ} (hG : ∀ i j : Fin 3, comparisonLpNorm 1 (tensorDiff u v t i j) ≤ G) :
    ‖canonicalCutoffFlux R hR u v t hu hv‖ ≤ 9 *
      (localPairConstant *
        (comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (3 / 2 : ℝ) *
            cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (1 / 2 : ℝ) +
          2 * comparisonLpNorm 2 (fun x => (u - v) (t, x)) * comparisonLpNorm 3 (fun x => u (t,
            x))) *
        (dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t / R +
          comparisonLpNorm 2 (fun x => (u - v) (t, x)) / R ^ 2) +
      commutatorConstant * G * comparisonLpNorm 2 (fun x => (u - v) (t, x)) ^ (1 / 4 : ℝ) *
        R ^ (-(7 / 4 : ℝ)) * cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (3 / 4 : ℝ)) := by
  apply norm_canonicalCutoffFlux_le
  intro i j
  refine (cutoff_pressurePair_bound hR hu hv hw2 hu3 i j (hg i j)).trans (add_le_add_right ?_ _)
  have hM := Real.rpow_nonneg
    (LpNormTools.lpNorm_nonneg 2 (fun x => (u - v) (t, x))) (1 / 4 : ℝ)
  have hB := Real.rpow_nonneg
    (LpNormTools.lpNorm_nonneg 6 (fun x => ComparisonCutoffs.cutoff R x ^ 4 • (u - v) (t, x)))
    (3 / 4 : ℝ)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hG i j) commutatorConstant_nonneg) hM)
      (Real.rpow_nonneg hR.le _)) hB

/-- One constant works for all radii and all smooth slices satisfying the fixed norm bounds. -/
theorem exists_uniform_canonicalCutoffFlux_bound (M₀ U₀ G₀ : ℝ)
    (hM₀ : 0 ≤ M₀) (hU₀ : 0 ≤ U₀) (hG₀ : 0 ≤ G₀) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ (R : ℝ) (hR : 1 ≤ R) (u v : VelocityField) (t : ℝ)
      (hu : ContDiff ℝ ∞ (fun x => u (t, x))) (hv : ContDiff ℝ ∞ (fun x => v (t, x))),
      MemLp (fun x => (u - v) (t, x)) 2 volume →
      MemLp (fun x => u (t, x)) 3 volume →
      (∀ i j : Fin 3, Integrable (tensorDiff u v t i j) volume) →
      comparisonLpNorm 2 (fun x => (u - v) (t, x)) ≤ M₀ →
      comparisonLpNorm 3 (fun x => u (t, x)) ≤ U₀ →
      (∀ i j : Fin 3, comparisonLpNorm 1 (tensorDiff u v t i j) ≤ G₀) →
      ‖canonicalCutoffFlux R (zero_lt_one.trans_le hR) u v t hu hv‖ ≤ CP *
        ((cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (1 / 2 : ℝ) + 1) *
          (dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t / R + 1 / R ^ 2) +
          R ^ (-(7 / 4 : ℝ)) * cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (3 / 4 : ℝ)) := by
  refine ⟨9 * uniformCoefficient localPairConstant commutatorConstant M₀ U₀ G₀,
    mul_nonneg (by norm_num)
      (uniformCoefficient_nonneg localPairConstant_nonneg commutatorConstant_nonneg hM₀ hU₀ hG₀),
        ?_⟩
  intro R hR u v t hu hv hw2 hu3 hg hM hU hG
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hA : 0 ≤ dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t := Real.sqrt_nonneg _
  have hB : 0 ≤ cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t :=
    LpNormTools.lpNorm_nonneg _ _
  have hn := uniform_expression_bound localPairConstant_nonneg commutatorConstant_nonneg
    hM₀ hU₀ hG₀ (LpNormTools.lpNorm_nonneg 2 (fun x => (u - v) (t, x)))
    (LpNormTools.lpNorm_nonneg 3 (fun x => u (t, x))) hG₀ hA hB hM hU (le_refl G₀) hR0
  have hp := canonicalCutoffFlux_bound hR0 hu hv hw2 hu3 hg hG
  simpa only [mul_assoc] using hp.trans (mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 9))

/-- The physical pressure flux has a single bound uniform in time and cutoff radius.
All hypotheses on the pressure are exactly those already present in pressure recovery. -/
theorem exists_uniform_actual_pressure_flux_bound {T : ℝ} {u v : VelocityField}
    {p q : PressureField} (H : PressureRecovery.Hypotheses T u v p q)
    (M₀ U₀ G₀ : ℝ) (hM₀ : 0 ≤ M₀) (hU₀ : 0 ≤ U₀) (hG₀ : 0 ≤ G₀)
    (hM : ∀ t ∈ Icc 0 T, MemLp (fun x => (u - v) (t, x)) 2 volume ∧
      comparisonLpNorm 2 (fun x => (u - v) (t, x)) ≤ M₀)
    (hU : ∀ t ∈ Icc 0 T, MemLp (fun x => u (t, x)) 3 volume ∧
      comparisonLpNorm 3 (fun x => u (t, x)) ≤ U₀)
    (hG : ∀ t ∈ Icc 0 T, ∀ i j : Fin 3,
      Integrable (tensorDiff u v t i j) volume ∧ comparisonLpNorm 1 (tensorDiff u v t i j) ≤ G₀) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ R : ℝ, 1 ≤ R → ∀ t ∈ Ioo 0 T,
      |∫ x, (p - q) (t, x) * fderiv ℝ (ComparisonCutoffs.weight R) x ((u - v) (t, x))| ≤ CP *
        ((cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (1 / 2 : ℝ) + 1) *
          (dissipationRoot (ComparisonCutoffs.cutoff R) (u - v) t / R + 1 / R ^ 2) +
          R ^ (-(7 / 4 : ℝ)) * cutoffL6 (ComparisonCutoffs.cutoff R) (u - v) t ^ (3 / 4 : ℝ)) := by
  obtain ⟨CP, hCP, hbound⟩ := exists_uniform_canonicalCutoffFlux_bound M₀ U₀ G₀ hM₀ hU₀ hG₀
  refine ⟨CP, hCP, ?_⟩
  intro R hR t ht
  have ht' : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  have hu := NavierStokes.PeriodicUniqueness.spatial_smooth H.smooth_u ht'
  have hv := NavierStokes.PeriodicUniqueness.spatial_smooth H.smooth_v ht'
  exact (actual_flux_integrable_and_le_canonicalNorm H ht (zero_lt_one.trans_le hR) hu hv).2.trans
    (hbound R hR u v t hu hv (hM t ht').1 (hU t ht').1 (fun i j => (hG t ht' i j).1)
      (hM t ht').2 (hU t ht').2 (fun i j => (hG t ht' i j).2))

end NavierStokesR3.PressureFlux
