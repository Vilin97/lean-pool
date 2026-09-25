/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Density and pairing helpers for Euclidean `Lᵖ`

This file records the approximation facts used when an operator is first
defined on its `L²` carrier and then extended to lower exponents.  The
approximants are continuous and compactly supported; in particular they are
in every finite `Lᵖ` space.  The pairing estimates are stated in the real
integral form supplied by Hölder's inequality, which is convenient when
passing a distributional identity to the limit.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology


noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic

/-- Every finite-exponent `Lᵖ` function has continuous compactly supported
approximants converging in `eLpNorm`.  Each approximant is also in `L²`. -/
theorem memLp_exists_compactSupportContinuous_approx
    {p : ℝ≥0∞} (hp : p ≠ ∞) {f : Vec3 → ℝ}
    (hf : MemLp f p volume) :
    ∃ g : ℕ → Vec3 → ℝ,
      (∀ n, HasCompactSupport (g n) ∧ Continuous (g n) ∧
        MemLp (g n) p volume ∧ MemLp (g n) 2 volume) ∧
      Tendsto (fun n => eLpNorm (f - g n) p volume) atTop (𝓝 0) := by
  let g : ℕ → Vec3 → ℝ := fun n =>
    Classical.choose (hf.exists_hasCompactSupport_eLpNorm_sub_le hp
      (ε := ENNReal.ofReal (1 / (n + 1 : ℝ))) (by
        simp only [one_div, ne_eq, ENNReal.ofReal_eq_zero, inv_nonpos, not_le]
        positivity))
  have hg : ∀ n, HasCompactSupport (g n) ∧
      eLpNorm (f - g n) p volume ≤ ENNReal.ofReal (1 / (n + 1 : ℝ)) ∧
      Continuous (g n) ∧ MemLp (g n) p volume := by
    intro n
    exact Classical.choose_spec (hf.exists_hasCompactSupport_eLpNorm_sub_le hp
      (ε := ENNReal.ofReal (1 / (n + 1 : ℝ))) (by
        simp only [one_div, ne_eq, ENNReal.ofReal_eq_zero, inv_nonpos, not_le]
        positivity))
  refine ⟨g, ?_, ?_⟩
  · intro n
    exact ⟨(hg n).1, (hg n).2.2.1, (hg n).2.2.2,
      (hg n).2.2.1.memLp_of_hasCompactSupport (hg n).1⟩
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop (𝓝 0) by
        have hreal : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) := by
          simpa [one_div] using
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        simpa using ENNReal.tendsto_ofReal hreal)
      (fun _ => bot_le) (fun n => (hg n).2.1)

/-- The preceding approximation theorem in the real-exponent notation used by
the pressure extension: `1 ≤ p < ∞` and `MemLp f (ENNReal.ofReal p)`. -/
theorem memLp_exists_compactSupportContinuous_approx_real
    {p : ℝ} (_ : 1 ≤ p) {f : Vec3 → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    ∃ g : ℕ → Vec3 → ℝ,
      (∀ n, HasCompactSupport (g n) ∧ Continuous (g n) ∧
        MemLp (g n) (ENNReal.ofReal p) volume ∧ MemLp (g n) 2 volume) ∧
      Tendsto (fun n => eLpNorm (f - g n) (ENNReal.ofReal p) volume)
        atTop (𝓝 0) := by
  simpa using
    (memLp_exists_compactSupportContinuous_approx
      (p := ENNReal.ofReal p) ENNReal.ofReal_ne_top hf)

/-- Hölder's estimate for the pairing against a fixed `Lq` test function. -/
theorem integral_mul_test_le {p q : ℝ} (hpq : p.HolderConjugate q)
    {g ψ : Vec3 → ℝ} (hg : MemLp g (ENNReal.ofReal p) volume)
    (hψ : MemLp ψ (ENNReal.ofReal q) volume) :
    ‖∫ x, g x * ψ x‖ ≤
      (∫ x, ‖g x‖ ^ p) ^ (1 / p) *
        (∫ x, ‖ψ x‖ ^ q) ^ (1 / q) := by
  have hp : 0 < p := hpq.left_pos
  have hq : 0 < q := hpq.right_pos
  let _ : (ENNReal.ofReal p).HolderTriple (ENNReal.ofReal q) 1 :=
    ENNReal.HolderTriple.of_toReal (by
      simpa [ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hq.le] using hpq)
  have hmul : Integrable (fun x => g x * ψ x) volume := by
    exact hg.integrable_mul hψ
  calc
    ‖∫ x, g x * ψ x‖ ≤ ∫ x, ‖g x * ψ x‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x, ‖g x‖ * ‖ψ x‖ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [norm_mul]
    _ ≤ _ := integral_mul_norm_le_Lp_mul_Lq hpq hg hψ

/-- Hölder's estimate for the difference of two pairings against a fixed
`Lq` test function.  This is the quantitative `Lᵖ` continuity used in the
distributional limit. -/
theorem integral_mul_test_sub_le {p q : ℝ} (hpq : p.HolderConjugate q)
    {g h ψ : Vec3 → ℝ} (hg : MemLp g (ENNReal.ofReal p) volume)
    (hh : MemLp h (ENNReal.ofReal p) volume)
    (hψ : MemLp ψ (ENNReal.ofReal q) volume) :
    ‖∫ x, (g x - h x) * ψ x‖ ≤
      (∫ x, ‖(g x - h x)‖ ^ p) ^ (1 / p) *
        (∫ x, ‖ψ x‖ ^ q) ^ (1 / q) := by
  exact integral_mul_test_le hpq (hg.sub hh) hψ

/-- The pairing estimate when the test is continuous and compactly supported.
Such a test is automatically in every finite `Lq` space. -/
theorem integral_mul_continuousCompactSupport_le {p q : ℝ}
    (hpq : p.HolderConjugate q) {g ψ : Vec3 → ℝ}
    (hg : MemLp g (ENNReal.ofReal p) volume) (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) :
    ‖∫ x, g x * ψ x‖ ≤
      (∫ x, ‖g x‖ ^ p) ^ (1 / p) *
        (∫ x, ‖ψ x‖ ^ q) ^ (1 / q) := by
  exact integral_mul_test_le hpq hg (hψc.memLp_of_hasCompactSupport hψs)

/-- A sequence converging in `Lᵖ` has a strictly increasing subsequence which
converges almost everywhere. -/
theorem ae_subsequence_of_eLpNorm_tendsto_zero
    {p : ℝ≥0∞} (hp : p ≠ 0) {f : ℕ → Vec3 → ℝ} {g : Vec3 → ℝ}
    (hfg : Tendsto (fun n => eLpNorm (f n - g) p volume) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂volume, Tendsto (fun n => f (ns n) x) atTop (𝓝 (g x)) := by
  exact (tendstoInMeasure_of_tendsto_eLpNorm hp hfg).exists_seq_tendsto_ae

/-- A Cauchy sequence of `Lᵖ` representatives has a representative of its
limit and converges to it in `eLpNorm`. -/
theorem memLp_limit_of_cauchy
    {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f : ℕ → Vec3 → ℝ}
    (hf : ∀ n, MemLp (f n) p volume)
    (hC : CauchySeq (fun n => (hf n).toLp (f n))) :
    ∃ g : Vec3 → ℝ, MemLp g p volume ∧
      Tendsto (fun n => eLpNorm (f n - g) p volume) atTop (𝓝 0) := by
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hC
  let g : Vec3 → ℝ := (Lp.aestronglyMeasurable u).mk u
  have hg : MemLp g p volume := by
    exact (Lp.memLp u).ae_eq (Lp.aestronglyMeasurable u).ae_eq_mk
  refine ⟨g, hg, ?_⟩
  have hgu : hg.toLp g = u := by
    rw [MemLp.toLp_congr hg (Lp.memLp u)
      (Lp.aestronglyMeasurable u).ae_eq_mk.symm]
    exact Lp.toLp_coeFn u (Lp.memLp u)
  have hu' : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
    rw [hgu]
    exact hu
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).mp hu'

end CKN.Foundation.Euclidean
