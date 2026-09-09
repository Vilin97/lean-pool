/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.CompactTimeIntegral
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonCutoffs
public import Mathlib.Analysis.Normed.Group.ZeroAtInfty
public import Mathlib.Topology.UniformSpace.UniformApproximation

@[expose] public section

/-!
# Weak time continuity from uniform spatial `L¹` bounds

A jointly continuous scalar field with uniformly bounded spatial `L¹` norm
has continuous pairings with every continuous test vanishing at infinity.
Only the test is approximated by compactly supported functions; no support or
derivative bound is imposed on the field.
-/


noncomputable section

open Set Filter MeasureTheory
open scoped Topology ZeroAtInfty

namespace NavierStokesR3.WeakTimeContinuity

open ProblemStatement ComparisonCutoffs

/-- A test function vanishing at infinity is bounded. -/
theorem exists_test_bound {ψ : Space → ℂ} (hψ : Continuous ψ)
    (hψzero : Tendsto ψ (cocompact Space) (𝓝 0)) :
    ∃ C : ℝ, ∀ x : Space, ‖ψ x‖ ≤ C := by
  let ψ₀ : C₀(Space, ℂ) :=
    { toFun := ψ, continuous_toFun := hψ, zero_at_infty' := hψzero }
  obtain ⟨C, hC⟩ := ψ₀.isBounded_range.exists_norm_le
  exact ⟨C, fun x => hC (ψ x) ⟨x, rfl⟩⟩

/-- Pairing an `L¹` scalar field with a bounded continuous complex test is
integrable. -/
theorem integrable_pairing_of_bounded {f : Space → ℝ} (hf : Integrable f volume)
    {ψ : Space → ℂ} (hψ : Continuous ψ) (hbound : ∃ C : ℝ, ∀ x, ‖ψ x‖ ≤ C) :
    Integrable (fun x : Space => (f x : ℂ) * ψ x) volume := by
  have hfC : Integrable (fun x : Space => (f x : ℂ)) volume := hf.ofReal
  obtain ⟨C, hC⟩ := hbound
  simpa only [mul_comm] using! hfC.bdd_mul hψ.aestronglyMeasurable (Filter.Eventually.of_forall hC)

/-- The original, untruncated pairing is a genuine Bochner integral. -/
theorem integrable_pairing {f : Space → ℝ} (hf : Integrable f volume)
    {ψ : Space → ℂ} (hψ : Continuous ψ)
    (hψzero : Tendsto ψ (cocompact Space) (𝓝 0)) :
    Integrable (fun x : Space => (f x : ℂ) * ψ x) volume :=
  integrable_pairing_of_bounded hf hψ (exists_test_bound hψ hψzero)

/-- The compact approximation to the spatial test. -/
def cutoffTest (R : ℝ) (ψ : Space → ℂ) (x : Space) : ℂ :=
  (cutoff R x : ℂ) * ψ x

theorem cutoffTest_continuous {ψ : Space → ℂ} (hψ : Continuous ψ) (R : ℝ) :
    Continuous (cutoffTest R ψ) :=
  (Complex.continuous_ofReal.comp (cutoff_smooth R).continuous).mul hψ

theorem norm_cutoffTest_le (R : ℝ) (ψ : Space → ℂ) (x : Space) :
    ‖cutoffTest R ψ x‖ ≤ ‖ψ x‖ := by
  simp only [cutoffTest, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (cutoff_nonneg R x)]
  exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one R x)

theorem integrable_cutoff_pairing {f : Space → ℝ} (hf : Integrable f volume)
    {ψ : Space → ℂ} (hψ : Continuous ψ)
    (hψzero : Tendsto ψ (cocompact Space) (𝓝 0)) (R : ℝ) :
    Integrable (fun x : Space => (f x : ℂ) * cutoffTest R ψ x) volume := by
  obtain ⟨C, hC⟩ := exists_test_bound hψ hψzero
  exact integrable_pairing_of_bounded hf (cutoffTest_continuous hψ R)
    ⟨C, fun x => (norm_cutoffTest_le R ψ x).trans (hC x)⟩

/-- Cutting off the test cannot enlarge its pointwise error beyond its norm. -/
theorem norm_sub_cutoffTest_le (R : ℝ) (ψ : Space → ℂ) (x : Space) :
    ‖ψ x - cutoffTest R ψ x‖ ≤ ‖ψ x‖ := by
  have heq : ψ x - cutoffTest R ψ x = ((1 - cutoff R x : ℝ) : ℂ) * ψ x := by
    simp only [cutoffTest, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (cutoff_le_one R x))]
  exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [cutoff_nonneg R x])

/-- The compact approximations converge uniformly on all of space. -/
theorem tendstoUniformly_cutoffTest {ψ : Space → ℂ} (hψ : Continuous ψ)
    (hψzero : Tendsto ψ (cocompact Space) (𝓝 0)) :
    TendstoUniformly (fun R : ℝ => cutoffTest R ψ) ψ atTop := by
  let ψ₀ : C₀(Space, ℂ) :=
    { toFun := ψ, continuous_toFun := hψ, zero_at_infty' := hψzero }
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  obtain ⟨A, hA⟩ := ZeroAtInftyContinuousMapClass.norm_le ψ₀ ε hε
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop A] with R hR hAR
  intro x
  rw [dist_eq_norm]
  by_cases hx : ‖x‖ ≤ R
  · simp only [cutoffTest, cutoff_eq_one hR hx, Complex.ofReal_one, one_mul,
      sub_self, norm_zero]
    exact hε
  · exact (norm_sub_cutoffTest_le R ψ x).trans_lt
      (hA x (lt_of_le_of_lt hAR (lt_of_not_ge hx)))

/-- Uniform error in the test controls error in its pairing by the `L¹`
norm of the scalar field. -/
theorem norm_pairing_sub_le {f : Space → ℝ} (hf : Integrable f volume)
    {ψ φ : Space → ℂ}
    (hψ : Integrable (fun x : Space => (f x : ℂ) * ψ x) volume)
    (hφ : Integrable (fun x : Space => (f x : ℂ) * φ x) volume)
    {ε : ℝ} (herror : ∀ x : Space, ‖ψ x - φ x‖ ≤ ε) :
    ‖(∫ x : Space, (f x : ℂ) * ψ x) - (∫ x : Space, (f x : ℂ) * φ x)‖ ≤
      ε * ∫ x : Space, ‖f x‖ := by
  rw [← integral_sub hψ hφ]
  calc
    ‖∫ x : Space, (f x : ℂ) * ψ x - (f x : ℂ) * φ x‖
        ≤ ∫ x : Space, ε * ‖f x‖ := by
      apply norm_integral_le_of_norm_le (hf.norm.const_mul ε)
      apply ae_of_all
      intro x
      rw [← mul_sub, norm_mul, Complex.norm_real]
      exact (mul_le_mul_of_nonneg_left (herror x) (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = ε * ∫ x : Space, ‖f x‖ := integral_const_mul _ _

/-- Compactly truncated pairings are continuous on an arbitrary time set. -/
theorem continuousOn_cutoff_pairing {s : Set ℝ} {g : SpaceTime → ℝ}
    (hg : ContinuousOn g (s ×ˢ univ)) {ψ : Space → ℂ} (hψ : Continuous ψ)
    {R : ℝ} (hR : 0 < R) :
    ContinuousOn (fun t => ∫ x : Space, (g (t, x) : ℂ) * cutoffTest R ψ x) s := by
  apply CompactTimeIntegral.continuousOn_integral
    (F := fun z : SpaceTime => (g z : ℂ) * cutoffTest R ψ z.2)
    (isCompact_closedBall (0 : Space) (2 * R))
  · exact (Complex.continuous_ofReal.comp_continuousOn hg).mul
      ((cutoffTest_continuous hψ R).comp continuous_snd).continuousOn
  · intro t _ x hx
    have hxnorm : 2 * R ≤ ‖x‖ := by
      have : ¬ ‖x‖ ≤ 2 * R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
      exact (lt_of_not_ge this).le
    simp only [cutoffTest, cutoff_eq_zero hR hxnorm, Complex.ofReal_zero, zero_mul, mul_zero]

/-- Uniform spatial `L¹` bounds upgrade compact-test continuity to continuity
for every continuous test vanishing at infinity. -/
theorem continuousOn_pairing {s : Set ℝ} {g : SpaceTime → ℝ} {M : ℝ}
    (hg : ContinuousOn g (s ×ˢ univ))
    (hints : ∀ t ∈ s, Integrable (fun x : Space => g (t, x)) volume)
    (hbound : ∀ t ∈ s, (∫ x : Space, ‖g (t, x)‖) ≤ M)
    {ψ : Space → ℂ} (hψ : Continuous ψ)
    (hψzero : Tendsto ψ (cocompact Space) (𝓝 0)) :
    ContinuousOn (fun t => ∫ x : Space, (g (t, x) : ℂ) * ψ x) s := by
  have happrox := tendstoUniformly_cutoffTest hψ hψzero
  have hpair : TendstoUniformlyOn
      (fun R : ℝ => fun t => ∫ x : Space, (g (t, x) : ℂ) * cutoffTest R ψ x)
      (fun t => ∫ x : Space, (g (t, x) : ℂ) * ψ x) atTop s := by
    apply Metric.tendstoUniformlyOn_iff.2
    intro ε hε
    have hden : 0 < max M 0 + 1 := by positivity
    have hδ : 0 < ε / (max M 0 + 1) := div_pos hε hden
    filter_upwards [Metric.tendstoUniformly_iff.1 happrox (ε / (max M 0 + 1)) hδ]
      with R hR
    intro t ht
    have herror := norm_pairing_sub_le (hints t ht)
      (integrable_pairing (hints t ht) hψ hψzero)
      (integrable_cutoff_pairing (hints t ht) hψ hψzero R)
      (fun x => (show ‖ψ x - cutoffTest R ψ x‖ < ε / (max M 0 + 1) by
        simpa only [dist_eq_norm] using hR x).le)
    calc
      dist (∫ x : Space, (g (t, x) : ℂ) * ψ x)
          (∫ x : Space, (g (t, x) : ℂ) * cutoffTest R ψ x)
          ≤ ε / (max M 0 + 1) * ∫ x : Space, ‖g (t, x)‖ := by
        simpa only [dist_eq_norm] using herror
      _ ≤ ε / (max M 0 + 1) * max M 0 :=
        mul_le_mul_of_nonneg_left ((hbound t ht).trans (le_max_left _ _)) hδ.le
      _ < ε / (max M 0 + 1) * (max M 0 + 1) :=
        mul_lt_mul_of_pos_left (lt_add_one _) hδ
      _ = ε := div_mul_cancel₀ ε hden.ne'
  exact hpair.continuousOn ((eventually_gt_atTop (0 : ℝ)).mono
    (fun _ hR => continuousOn_cutoff_pairing hg hψ hR)).frequently

end NavierStokesR3.WeakTimeContinuity
