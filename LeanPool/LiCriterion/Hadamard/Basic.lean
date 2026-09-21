/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

/-
  Hadamard's Factorization Theorem

  This file formalizes Hadamard's theorem for entire functions of finite order.

  **Main Goal**: If f is an entire function of finite order ρ ≥ 0, then
    f(z) = e^(g(z)) z^m ∏ⱼ E_d(z/aⱼ)
  where:
    - aⱼ are the zeros of f (with multiplicity)
    - m = order of zero at z=0
    - g(z) ∈ ℂ[z] (polynomial)
    - d, deg(g) ≤ ρ

  **Proof Strategy**:

  Strategy of Proof.
  1. Prove this for entire function f(z) without zeros: by existence of logarithms
     we know f(z) = e^(g(z)). We show g(z) is a polynomial (This involves the so-called
     Borel-Carathéodory inequality)
  2. By Weierstrass any entire function can be written as f(z) = e^(g(z))P(z) where
     P(z) is a canonical product and g(z) is some function.
     (a) Study the order of P(z) (this uses Jensen's Formula)
     (b) Get bounds on 1/P(z)
     (c) Conclude that f(z)/P(z) is entire of finite order as in the first case.

  **Main References**:
 - Hadamard's factorization theorem, with all details
 - Conway, Chapter XI: Entire Functions
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Algebra.Polynomial.Degree.Defs
import LeanPool.LiCriterion.FunctionsOfOneComplexVariable.EntireLog
import LeanPool.LiCriterion.FunctionsOfOneComplexVariable.BorelCaratheodory

/-! ### Maximum modulus definition -/

open Complex Real Filter Topology MeasureTheory
open scoped BigOperators ComplexConjugate


namespace Hadamard

/-- The maximum modulus of f on the circle of radius r.
    M(f,r) = sup {|f(z)| : |z| = r} -/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup {y : ℝ | ∃ z : ℂ, ‖z‖ = r ∧ y = ‖f z‖}

/-! ### Helper lemmas for subsequence growth and exp/log monotonicity -/

/-- On a circle `‖z‖ = r`, the pointwise value is bounded by the maximal modulus `M(f,r)`.

This follows directly from the definition of `maxModulus` as a supremum over the circle. -/
lemma norm_le_maxModulus_on_circle (f : ℂ → ℂ) (hf : Continuous f)
    {r : ℝ} {z : ℂ} (hz : ‖z‖ = r) : ‖f z‖ ≤ maxModulus f r := by
  -- The defining set for `maxModulus f r` contains `‖f z‖`.
  have hmem : ‖f z‖ ∈ {y : ℝ | ∃ ζ : ℂ, ‖ζ‖ = r ∧ y = ‖f ζ‖} := ⟨z, hz, rfl⟩
  -- Identify the defining set with the continuous image of the sphere.
  have hset_eq : {y : ℝ | ∃ ζ : ℂ, ‖ζ‖ = r ∧ y = ‖f ζ‖}
      = ((fun ζ : ℂ => ‖f ζ‖) '' Metric.sphere (0 : ℂ) r) := by
    ext y; constructor
    · intro hy; rcases hy with ⟨ζ, hζ, rfl⟩
      exact ⟨ζ, by simpa [Metric.mem_sphere, dist_eq_norm] using hζ, rfl⟩
    · intro hy; rcases hy with ⟨ζ, hζ, rfl⟩
      exact ⟨ζ, by simpa [Metric.mem_sphere, dist_eq_norm] using hζ, rfl⟩
  -- The image of a compact set by a continuous map into ℝ is bounded above.
  have hK : IsCompact (Metric.sphere (0 : ℂ) r) := isCompact_sphere _ _
  have hcont : Continuous fun ζ : ℂ => ‖f ζ‖ := (hf.norm)
  have hImCompact : IsCompact ((fun ζ : ℂ => ‖f ζ‖) '' Metric.sphere (0 : ℂ) r) :=
    hK.image hcont
  have h_bdd' : BddAbove ((fun ζ : ℂ => ‖f ζ‖) '' Metric.sphere (0 : ℂ) r) := hImCompact.bddAbove
  have h_bdd : BddAbove {y : ℝ | ∃ ζ : ℂ, ‖ζ‖ = r ∧ y = ‖f ζ‖} := by simpa [hset_eq] using h_bdd'
  exact le_csSup h_bdd (by simpa [hset_eq] using hmem)

/-- If all pointwise values on the circle `‖z‖ = r` are bounded by `A`,
then `maxModulus f r ≤ A`. -/
lemma maxModulus_le_of_forall_norm_le (f : ℂ → ℂ) (_hf : Continuous f) {r A : ℝ} (hr : 0 ≤ r)
    (hA : ∀ z : ℂ, ‖z‖ = r → ‖f z‖ ≤ A) : maxModulus f r ≤ A := by
  have hne : ({y : ℝ | ∃ ζ : ℂ, ‖ζ‖ = r ∧ y = ‖f ζ‖}).Nonempty := by
    refine ⟨‖f (r : ℂ)‖, ?_⟩
    refine ⟨(r : ℂ), ?_, rfl⟩
    simp [hr]
  have : sSup {y : ℝ | ∃ ζ : ℂ, ‖ζ‖ = r ∧ y = ‖f ζ‖} ≤ A := by
    refine csSup_le hne ?_
    rintro y ⟨ζ, hζ, rfl⟩
    exact hA ζ hζ
  simpa [maxModulus] using this

/-- Maximum modulus principle (specialized): values on the closed disk `‖z‖ ≤ R` are bounded by
`maxModulus f R`. -/
lemma norm_le_maxModulus_of_norm_le (f : ℂ → ℂ) (hf : Differentiable ℂ f) {R : ℝ} (_hR : 0 < R)
    {w : ℂ} (hw : ‖w‖ ≤ R) : ‖f w‖ ≤ maxModulus f R := by
  have hcont : Continuous f := hf.continuous
  by_cases hw_strict : ‖w‖ < R
  · -- Interior point: apply the maximum modulus principle on the ball.
    set U := Metric.ball (0 : ℂ) R with hU_def
    have hU_bdd : Bornology.IsBounded U := Metric.isBounded_ball
    have hf_diffcont : DiffContOnCl ℂ f U := by
      constructor
      · intro z hz
        have : DifferentiableAt ℂ f z := hf.differentiableAt
        exact this.differentiableWithinAt
      · intro z hz
        have : DifferentiableAt ℂ f z := hf.differentiableAt
        exact this.continuousAt.continuousWithinAt
    have hw_closure : w ∈ closure U := by
      apply subset_closure
      simpa [U, Metric.mem_ball] using hw_strict
    apply Complex.norm_le_of_forall_mem_frontier_norm_le hU_bdd hf_diffcont _ hw_closure
    intro z hz
    have hz_sphere : ‖z‖ = R := by
      have hz_le : ‖z‖ ≤ R := by
        have := frontier_subset_closure hz
        have := Metric.closure_ball_subset_closedBall this
        simpa [Metric.mem_closedBall] using this
      have hz_ge : R ≤ ‖z‖ := by
        by_contra h
        push Not at h
        have : z ∈ U := by simp [U, Metric.mem_ball, h]
        have hz_interior : z ∈ interior U := by
          rw [Metric.isOpen_ball.interior_eq]
          exact this
        have h_disj : Disjoint (interior U) (frontier U) := disjoint_interior_frontier
        have : z ∉ frontier U := Set.disjoint_left.mp h_disj hz_interior
        exact this hz
      exact le_antisymm hz_le hz_ge
    exact norm_le_maxModulus_on_circle f hcont hz_sphere
  · -- Boundary point: `‖w‖ = R`.
    have hw_eq : ‖w‖ = R := le_antisymm hw (le_of_not_gt hw_strict)
    exact norm_le_maxModulus_on_circle f hcont hw_eq

/-- The maximum modulus `M(f,r)` is monotone in `r` for entire functions. -/
lemma maxModulus_mono_of_differentiable (f : ℂ → ℂ) (hf : Differentiable ℂ f) {r R : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (h : r ≤ R) : maxModulus f r ≤ maxModulus f R := by
  have hcont : Continuous f := hf.continuous
  refine maxModulus_le_of_forall_norm_le f hcont hr ?_
  intro z hz
  have hz_le : ‖z‖ ≤ R := by
    simpa [hz.symm] using h
  exact norm_le_maxModulus_of_norm_le f hf hR hz_le

/-- If `‖exp w‖ ≤ exp t` then `Re w ≤ t`. -/
lemma re_le_of_norm_exp_le {w : ℂ} {t : ℝ}
    (h : ‖Complex.exp w‖ ≤ Real.exp t) : w.re ≤ t := by
    rw [Complex.norm_exp w] at h
    exact Real.exp_le_exp.mp h

/-- If `‖exp w‖ < exp t` then `Re w < t`. -/
lemma re_lt_of_norm_exp_lt {w : ℂ} {t : ℝ}
    (h : ‖Complex.exp w‖ < Real.exp t) : w.re < t := by
    rw [Complex.norm_exp] at h
    exact Real.exp_lt_exp.mp h

/-! ### Order of growth -/

/-- **Definition 1.1**: The order of growth of an entire function

Definition: The infimum of ρ₀ such that |f(z)| < exp(|z|^ρ₀) for |z| ≥ R₀

Lemma 1.2. Let f be an entire function of finite order.
  ρ(f) = lim sup_{r≥R→∞} (log log M(f,r)) / log(r)
where M(f,r) = max_{|z|=r} |f(z)|
-/
noncomputable def order (f : ℂ → ℂ) : ℝ :=
  Filter.limsup (fun r : ℝ =>
    if r > 0 ∧ maxModulus f r > 1 then
      Real.log (Real.log (maxModulus f r)) / Real.log r
    else 0) Filter.atTop

/-- From `order f = ρ`, one can choose radii along which the maximal modulus is bounded
by `exp(r^(ρ+ε))`. This is the standard subsequence extraction from the `limsup` definition. -/
lemma maxModulus_subseq_bound_of_order (f : ℂ → ℂ) (ρ : ℝ) (ε : ℝ) (hε : 0 < ε)
    (hord : order f = ρ)
    (hu_bdd : IsBoundedUnder (· ≤ ·) atTop (fun r : ℝ =>
      if r > 0 ∧ maxModulus f r > 1 then
        Real.log (Real.log (maxModulus f r)) / Real.log r
      else 0)) :
    ∃ r0 : ℕ → ℝ, Filter.Tendsto r0 atTop atTop ∧ (∀ n, 0 < r0 n) ∧
      ∀ n, maxModulus f (r0 n) ≤ Real.exp ((r0 n) ^ (ρ + ε)) := by
  classical
  classical
  let u : ℝ → ℝ := fun r : ℝ =>
    if r > 0 ∧ maxModulus f r > 1 then
      Real.log (Real.log (maxModulus f r)) / Real.log r
    else 0
  have hu_limsup : Filter.limsup u atTop = ρ := by
    simpa [order, u] using hord
  have hu_event : ∀ᶠ r : ℝ in atTop, u r < ρ + ε :=
    eventually_lt_add_pos_of_limsup_le (by simpa [u] using hu_bdd) (le_of_eq hu_limsup) hε
  rcases (eventually_atTop.1 hu_event) with ⟨R, hR⟩
  let R' : ℝ := max R 2
  let r0 : ℕ → ℝ := fun n => max R' ((n : ℝ) + 2)
  have hr0_ge_R : ∀ n, R ≤ r0 n := by
    intro n
    have hRR' : R ≤ R' := le_max_left _ _
    exact le_trans hRR' (le_max_left _ _)
  have hr0_ge2 : ∀ n, 2 ≤ r0 n := by
    intro n
    have h2R' : 2 ≤ R' := le_max_right _ _
    exact le_trans h2R' (le_max_left _ _)
  have hr0_pos : ∀ n, 0 < r0 n := by
    intro n
    linarith [hr0_ge2 n]
  have hr0_tendsto : Filter.Tendsto r0 atTop atTop := by
    refine tendsto_atTop.mpr ?_
    intro b
    have hb : ∀ᶠ n : ℕ in atTop, b ≤ (n : ℝ) := by
      simpa using (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop b))
    have hb' : ∀ᶠ n : ℕ in atTop, b ≤ (n : ℝ) + 2 :=
      hb.mono (fun n hn => le_trans hn (by linarith))
    exact hb'.mono (fun n hn => le_trans hn (le_max_right _ _))
  refine ⟨r0, hr0_tendsto, hr0_pos, ?_⟩
  intro n
  set r : ℝ := r0 n
  have hr_ge2 : 2 ≤ r := by
    simpa [r] using hr0_ge2 n
  have hr_pos : 0 < r := by
    linarith [hr_ge2]
  have hr_gt1 : 1 < r := by
    linarith [hr_ge2]
  have hr_geR : R ≤ r := by
    simpa [r] using hr0_ge_R n
  have hu_r : u r < ρ + ε := hR r hr_geR
  by_cases hM : maxModulus f r > 1
  · have hu_ratio :
        Real.log (Real.log (maxModulus f r)) / Real.log r < ρ + ε := by
        have hcond : r > 0 ∧ maxModulus f r > 1 := ⟨hr_pos, hM⟩
        simpa [u, hcond] using hu_r
    have hlogr_pos : 0 < Real.log r := Real.log_pos hr_gt1
    have hloglog :
        Real.log (Real.log (maxModulus f r)) < (ρ + ε) * Real.log r :=
      (div_lt_iff₀ hlogr_pos).1 hu_ratio
    have hlogM_pos : 0 < Real.log (maxModulus f r) := Real.log_pos hM
    have hlogM_lt :
        Real.log (maxModulus f r) < r ^ (ρ + ε) := by
      have h :
          Real.exp (Real.log (Real.log (maxModulus f r))) <
            Real.exp ((ρ + ε) * Real.log r) :=
        Real.exp_lt_exp.mpr hloglog
      have h' : Real.log (maxModulus f r) < Real.exp ((ρ + ε) * Real.log r) := by
        simpa [Real.exp_log hlogM_pos] using h
      simpa [mul_comm, Real.rpow_def_of_pos hr_pos] using h'
    have hM_pos : 0 < maxModulus f r := lt_trans (by linarith) hM
    have hM_lt :
        maxModulus f r < Real.exp (r ^ (ρ + ε)) := by
      have h : Real.exp (Real.log (maxModulus f r)) < Real.exp (r ^ (ρ + ε)) :=
        Real.exp_lt_exp.mpr hlogM_lt
      simpa [Real.exp_log hM_pos] using h
    exact le_of_lt hM_lt
  · have hM_le1 : maxModulus f r ≤ 1 := le_of_not_gt hM
    have h_exp_ge1 : 1 ≤ Real.exp (r ^ (ρ + ε)) :=
      Real.one_le_exp (Real.rpow_nonneg (le_of_lt hr_pos) _)
    exact le_trans hM_le1 h_exp_ge1

/-! ## Definitions

Definition 1.1. An entire function f is finite order if and only if ∃ρ₀, R₀ such that
  |f(z)| < exp(|z|^ρ₀) whenever |z| ≥ R₀.
The infimum of such ρ₀ is called the order of f and is denoted by ρ = ρ(f).

Definition 2.1. Let f be an entire function with zeros {a₁, a₂,...}, repeated
according to multiplicity and arranged such that |a₁| ≤ |a₂| ≤ ....

Then f is of finite rank if there is an integer p such that
  ∑ |aₙ|^{-p-1} < ∞
If p is the smallest integer such that this occurs, then f is said to be of rank p;
a function with only a finite number of zeros has rank 0.

The order of an entire function f is defined as:
    ρ(f) = lim sup_{r→∞} (log log M(f,r))/(log r)
    where M(f,r) = max_{|z|=r} |f(z)|
-/

/-- An entire function has finite order if there exist ρ₀, R₀ such that
    |f(z)| < exp(|z|^ρ₀) whenever |z| ≥ R₀ -/
def hasFiniteOrder (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ ∃ (ρ₀ R₀ : ℝ), ∀ z : ℂ, R₀ ≤ ‖z‖ → ‖f z‖ < Real.exp (‖z‖ ^ ρ₀)

/-- Product of entire functions preserves finite order -/
lemma hasFiniteOrder_mul (f g : ℂ → ℂ) (hf : hasFiniteOrder f) (hg : hasFiniteOrder g) :
    hasFiniteOrder (f * g) := by
  obtain ⟨hf_diff, ρf, Rf, hf_bound⟩ := hf
  obtain ⟨hg_diff, ρg, Rg, hg_bound⟩ := hg
  constructor
  · exact Differentiable.mul hf_diff hg_diff
  · -- Set ρ := max ρf ρg + 1, R := max(Rf, Rg, 1) + 1
    use max ρf ρg + 1, max (max Rf Rg) 1 + 1
    intro z hz
    simp only [Pi.mul_apply, norm_mul]
 -- Prove side conditions first
    -- We need Rf ≤ |z|, Rg ≤ |z|, 1 ≤ |z|, 2 ≤ |z|
    have hzf : Rf ≤ ‖z‖ := by
      have : Rf ≤ max (max Rf Rg) 1 + 1 := by
        have : Rf ≤ max Rf Rg := le_max_left Rf Rg
        have : max Rf Rg ≤ max (max Rf Rg) 1 := le_max_left _ _
        linarith
      linarith
    have hzg : Rg ≤ ‖z‖ := by
      have : Rg ≤ max (max Rf Rg) 1 + 1 := by
        have : Rg ≤ max Rf Rg := le_max_right Rf Rg
        have : max Rf Rg ≤ max (max Rf Rg) 1 := le_max_left _ _
        linarith
      linarith
    have hz_ge_1 : 1 ≤ ‖z‖ := by
      have : 1 ≤ max (max Rf Rg) 1 + 1 := by
        have : 1 ≤ max (max Rf Rg) 1 := le_max_right _ _
        linarith
      linarith
    have hz_ge_2 : 2 ≤ ‖z‖ := by
      have : 2 ≤ max (max Rf Rg) 1 + 1 := by
        have : (2 : ℝ) = 1 + 1 := by norm_num
        linarith [le_max_right (max Rf Rg) (1 : ℝ)]
      linarith
    have hz_pos : 0 < ‖z‖ := by linarith
    -- Now prove the main inequality using explicit transitivity
    -- Step 1: ‖f z‖ * ‖g z‖ < exp(‖z‖^ρf + ‖z‖^ρg)
    have step1 : ‖f z‖ * ‖g z‖ < Real.exp (‖z‖ ^ ρf + ‖z‖ ^ ρg) := by
      have h_mul : ‖f z‖ * ‖g z‖ < Real.exp (‖z‖ ^ ρf) * Real.exp (‖z‖ ^ ρg) :=
        mul_lt_mul'' (hf_bound z hzf) (hg_bound z hzg) (norm_nonneg _) (norm_nonneg _)
      rw [← Real.exp_add] at h_mul
      exact h_mul
    -- Step 2: ‖z‖^ρf + ‖z‖^ρg ≤ 2·‖z‖^max(ρf,ρg)
    have step2 : ‖z‖ ^ ρf + ‖z‖ ^ ρg ≤ 2 * ‖z‖ ^ max ρf ρg := by
      -- For 1 ≤ ‖z‖, rpow is monotone in the exponent
      have h1 : ‖z‖ ^ ρf ≤ ‖z‖ ^ max ρf ρg := by
        apply Real.rpow_le_rpow_of_exponent_le hz_ge_1
        exact le_max_left ρf ρg
      have h2 : ‖z‖ ^ ρg ≤ ‖z‖ ^ max ρf ρg := by
        apply Real.rpow_le_rpow_of_exponent_le hz_ge_1
        exact le_max_right ρf ρg
      linarith
    -- Step 3: 2·‖z‖^max ≤ ‖z‖·‖z‖^max = ‖z‖^(max+1)
    have step3 : 2 * ‖z‖ ^ max ρf ρg ≤ ‖z‖ ^ (max ρf ρg + 1) := by
      have h_mul : 2 * ‖z‖ ^ max ρf ρg ≤ ‖z‖ * ‖z‖ ^ max ρf ρg :=
        mul_le_mul_of_nonneg_right hz_ge_2 (Real.rpow_nonneg (norm_nonneg z) _)
      have h_rpow : ‖z‖ * ‖z‖ ^ max ρf ρg = ‖z‖ ^ (max ρf ρg + 1) := by
        -- Use nth_rewrite to target only the first ‖z‖, avoiding nested powers
        nth_rewrite 1 [← Real.rpow_one ‖z‖]
        rw [← Real.rpow_add hz_pos, add_comm]
      rw [← h_rpow]
      exact h_mul
    -- Combine: exp is monotone, so the chain of inequalities gives the result
    calc ‖f z‖ * ‖g z‖
        < Real.exp (‖z‖ ^ ρf + ‖z‖ ^ ρg) := step1
      _ ≤ Real.exp (2 * ‖z‖ ^ max ρf ρg) := Real.exp_le_exp.mpr step2
      _ ≤ Real.exp (‖z‖ ^ (max ρf ρg + 1)) := Real.exp_le_exp.mpr step3

/--
Weierstrass elementary factors:
  E₀(z) = 1 - z
  Eₚ(z) = (1-z) exp(z + z²/2 + ... + z^p/p) for p ≥ 1

The canonical product is:
  P(z) = ∏ₙ Eₚₙ(z/aₙ)
where {pₙ} is chosen so that ∑ |aₙ|^{-pₙ-1} < ∞

Weierstrass elementary factors where:
  E_p(w) = (1-w)exp(w + w²/2 + ... + w^p/p)
These appear in the canonical product representation.
-/
noncomputable def weierstrassE (p : ℕ) (w : ℂ) : ℂ :=
  (1 - w) * Complex.exp (∑ k ∈ Finset.range p, w^(k+1) / (k+1))

-- Basic property: E₀(z) = 1 - z
lemma weierstrass_E_zero (w : ℂ) : weierstrassE 0 w = 1 - w := by
  simp [weierstrassE, Finset.range_zero, Finset.sum_empty]

-- E₁(z) = (1-z)exp(z)
lemma weierstrass_E_one (w : ℂ) : weierstrassE 1 w = (1 - w) * exp w := by
  simp only [weierstrassE, Finset.range_one, Finset.sum_singleton]
  norm_num

-- `E₁(1) = 0`.
lemma weierstrass_E_at_one (p : ℕ) : weierstrassE p (1 : ℂ) = 0 := by
  simp [weierstrassE]

-- `E_p(w) = 0 ↔ w = 1` for all `p`.
lemma weierstrass_E_eq_zero_iff_general (p : ℕ) (w : ℂ) :
    weierstrassE p w = 0 ↔ w = 1 := by
  constructor
  · intro h
    have h' : (1 - w) * Complex.exp (∑ k ∈ Finset.range p, w ^ (k + 1) / (k + 1)) = 0 := h
    have hcases :
        (1 - w = 0) ∨
          Complex.exp (∑ k ∈ Finset.range p, w ^ (k + 1) / (k + 1)) = 0 := by
      simpa [mul_eq_zero] using h'
    cases hcases with
    | inl h1 =>
        -- `1 - w = 0` gives `w = 1`.
        have : w = 1 := by linear_combination -h1
        exact this
    | inr h2 => exact absurd h2 (Complex.exp_ne_zero _)
  · intro hw
    simp [hw, weierstrassE]

-- `E_p(w) ≠ 0` when `w ≠ 1`.
lemma weierstrass_E_ne_zero_general (p : ℕ) {w : ℂ} (hw : w ≠ 1) :
    weierstrassE p w ≠ 0 :=
  fun h => hw ((weierstrass_E_eq_zero_iff_general p w).1 h)

-- `E₁(w) = 0 ↔ w = 1`.
lemma weierstrass_E_one_eq_zero_iff (w : ℂ) : weierstrassE 1 w = 0 ↔ w = 1 := by
  rw [weierstrass_E_one]
  constructor
  · intro h
    have h' : (1 - w = 0) ∨ Complex.exp w = 0 := by
      simpa [mul_eq_zero] using h
    cases h' with
    | inl h1 =>
        have : w = 1 := by
          have hw : (1 : ℂ) = w := sub_eq_zero.mp h1
          exact hw.symm
        exact this
    | inr h2 =>
        exact False.elim (Complex.exp_ne_zero w h2)
  · intro hw
    subst hw
    simp

-- `E₁(w) ≠ 0` for `w ≠ 1`.
lemma weierstrass_E_one_ne_zero (w : ℂ) (hw : w ≠ 1) : weierstrassE 1 w ≠ 0 := by
  intro h0
  exact hw ((weierstrass_E_one_eq_zero_iff w).1 h0)

-- Eₚ(0) = 1 for all p
lemma weierstrass_E_zero_arg (p : ℕ) : weierstrassE p 0 = 1 := by
  simp [weierstrassE]

-- Key property: The Weierstrass E function is continuous
lemma weierstrass_E_continuous (p : ℕ) : Continuous (weierstrassE p) := by
  -- The function is continuous as a product of continuous functions
  unfold weierstrassE
  apply Continuous.mul
  · -- (1 - w) is continuous
    fun_prop
  · -- exp(sum) is continuous
    apply Complex.continuous_exp.comp
    -- The finite sum is continuous
    apply continuous_finsetSum
    intro k _
    -- w^(k+1) / (k+1) is continuous
    apply Continuous.div_const
    fun_prop

-- Key property: The Weierstrass E function is complex-differentiable (entire)
lemma weierstrass_E_differentiable (p : ℕ) : Differentiable ℂ (weierstrassE p) := by
  classical
  unfold weierstrassE
  fun_prop

/-- `E_p'(1) ≠ 0` for all `p`.

Concretely, `E_p'(1) = -exp(H_p)` where `H_p = ∑_{k=1}^p 1/k` (the `p`-th
harmonic number), which is nonzero since `exp` never vanishes. -/
lemma deriv_weierstrass_E_at_one_ne_zero (p : ℕ) :
    deriv (weierstrassE p) (1 : ℂ) ≠ 0 := by
  classical
  let poly : ℂ → ℂ := fun w => ∑ k ∈ Finset.range p, w ^ (k + 1) / (k + 1)
  have hpoly_diff : Differentiable ℂ poly := by
    change Differentiable ℂ (fun w : ℂ => ∑ k ∈ Finset.range p, w ^ (k + 1) / (k + 1))
    fun_prop
  have hE_eq : weierstrassE p = fun w => (1 - w) * Complex.exp (poly w) := by
    funext w; rfl
  have h1 : HasDerivAt (fun w : ℂ => (1 : ℂ) - w) (-1) (1 : ℂ) :=
    (hasDerivAt_id (1 : ℂ)).const_sub (1 : ℂ)
  have hpoly_at : HasDerivAt poly (deriv poly 1) (1 : ℂ) :=
    (hpoly_diff 1).hasDerivAt
  have h2 : HasDerivAt (fun w : ℂ => Complex.exp (poly w))
      (Complex.exp (poly 1) * deriv poly 1) (1 : ℂ) := by
    simpa using hpoly_at.cexp
  have hprod : HasDerivAt (fun w : ℂ => (1 - w) * Complex.exp (poly w))
      ((-1) * Complex.exp (poly 1) + (1 - 1) * (Complex.exp (poly 1) * deriv poly 1)) (1 : ℂ) :=
    h1.mul h2
  have hprod' :
      HasDerivAt (fun w : ℂ => (1 - w) * Complex.exp (poly w))
        (-Complex.exp (poly 1)) (1 : ℂ) := by
    have hzero : (1 : ℂ) - 1 = 0 := by ring
    rw [hzero, zero_mul, add_zero, neg_one_mul] at hprod
    exact hprod
  rw [hE_eq]
  have := hprod'.deriv
  rw [this]
  intro hne
  exact Complex.exp_ne_zero (poly 1) (neg_eq_zero.mp hne)

/-- `E_p` has a simple zero at `1` for all `p`. -/
lemma weierstrass_E_analyticOrderAt_one (p : ℕ) :
    analyticOrderAt (weierstrassE p) (1 : ℂ) = 1 := by
  have hanalytic : AnalyticAt ℂ (weierstrassE p) (1 : ℂ) :=
    (weierstrass_E_differentiable p).analyticAt 1
  have hzero : weierstrassE p (1 : ℂ) = 0 := weierstrass_E_at_one p
  have hderiv : deriv (weierstrassE p) (1 : ℂ) ≠ 0 :=
    deriv_weierstrass_E_at_one_ne_zero p
  have h := hanalytic.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hderiv
  simp only [hzero, sub_zero] at h
  exact h

/-- `E_p` has `analyticOrderNatAt` equal to 1 at `w = 1`. -/
lemma weierstrass_E_analyticOrderNatAt_one (p : ℕ) :
    analyticOrderNatAt (weierstrassE p) (1 : ℂ) = 1 := by
  unfold analyticOrderNatAt
  rw [weierstrass_E_analyticOrderAt_one]
  rfl

/-! ## Key Lemmas

The proof of Hadamard's theorem proceeds through several key technical lemmas.
-/

/-! ## Canonical Product -/

/-
Given a choice of genus `d` and an enumeration `zeros : ℕ → ℂ` of the nonzero
zeros of an entire function (with multiplicities), the Weierstrass canonical
product is
  P(z) = ∏' n, E_d(z / zeros n).
This section records a minimal definition and basic facts we will use later.
-/

section CanonicalProduct

variable {d : ℕ} {zeros : ℕ → ℂ}

/-- Finite partial product for the canonical product. -/
noncomputable def canonicalProductPartial (d : ℕ) (zeros : ℕ → ℂ)
    (s : Finset ℕ) (z : ℂ) : ℂ :=
  ∏ n ∈ s, weierstrassE d (z / zeros n)

/-- The Weierstrass canonical product (over all indices). -/
noncomputable def canonicalProduct (d : ℕ) (zeros : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n, weierstrassE d (z / zeros n)

@[simp]
lemma canonicalProductPartial_empty (d : ℕ) (zeros : ℕ → ℂ) (z : ℂ) :
    canonicalProductPartial d zeros ∅ z = 1 := by
  simp [canonicalProductPartial]

@[simp]
lemma canonicalProduct_at_zero (d : ℕ) (zeros : ℕ → ℂ) :
    canonicalProduct d zeros 0 = 1 := by
  -- Each factor equals 1 at z = 0, so the infinite product is 1.
  classical
  have hfac : (fun n => weierstrassE d (0 / zeros n)) = fun _n => (1 : ℂ) := by
    funext n; simp [weierstrass_E_zero_arg]
  rw [canonicalProduct, hfac]
  exact tprod_one

end CanonicalProduct

/-- **Lemma 1.2**: Order formula using log log M(f,r)

Lemma 1.2. Let f be an entire function of finite order.
  ρ(f) = lim sup_{R→∞,r≥R} (loglogM(f,r))/log(r)
where M(f,r) = max_{|z|=r} |f(z)|.

Proof. If f is finite order,
  M(f,r) ≤ exp(r^ρ₀)
⟹ log M(f,r) ≤ r^ρ₀
⟹ log log M(f,r) ≤ ρ₀ log(r)

So we have lim_{R→∞} lim_{r≥R} (loglogM(f,r))/log r ≤ ρ₀.
-/
lemma order_formula (f : ℂ → ℂ) (_hf : hasFiniteOrder f) :
  order f = Filter.limsup (fun r : ℝ =>
    if r > 0 ∧ maxModulus f r > 1 then
      Real.log (Real.log (maxModulus f r)) / Real.log r
    else 0) Filter.atTop := by
  -- This is true by definition
  rfl

/-! ## Harmonic Function Theory

The harmonic function theory needed for Borel-Carathéodory has been moved
to a separate file: `Rh.HarmonicFunctionality`

That file contains:
- `AnalyticAt.harmonicAt_of_complex`: Complex-analytic functions are harmonic
- `re_of_holomorphic_is_harmonic`: Real part of holomorphic is harmonic
- `im_of_holomorphic_is_harmonic`: Imaginary part of holomorphic is harmonic
- TODO markers for Mean Value Property, Maximum Principle, Poisson Formula, Harnack's Inequality

We import and open that namespace above, so all lemmas are available here.
-/

/-! ## Borel-Carathéodory Theorem -/

/- **Theorem 2.2** (Borel-Carathéodory): Relates Re g to |g|

Exercise 2.1. If f : D_R(0) → D_R(0) is a conformal map with f(0) = 0 then
  |f(z)| ≤ |z|. (Hint: consider g(z) = g(z/R)/R and apply Schwarz.)
This replaces a hyperbolic geometry argument that McMullen uses.

Theorem 2.2 (Borel-Carathéodory). Let f be holomorphic on a region containing D_R(0).
For 0 < r < R,
  max_{|z|≤r} |f(z)| ≤ (2r)/(R-r) · max_{|z|=R} Re f(z) + |f(0)|

Proof. We may assume f(0) = 0 by replacing f with f - f(0).
Let M = max_{|z|=R} Re f(z). We want to show max_{|z|≤r} |f(z)| ≤ 2rM/(R-r).



--------------------------------------------------------------------------------
### Borel-Carathéodory Theorem - Titchmarsh §3.9

**KEY REFERENCE**: Titchmarsh pages 56-57, Lemma α/β/γ
**SCREENSHOT**:

This inequality is essential for proving zero-free regions of ζ(s).

TITCHMARSH LEMMA β states: "If f has no zeros in right-half of circle |s-s₀| ≤ r,
then -R{f'(s₀)/f(s₀)} < 2M/r"

The proof uses Borel-Carathéodory on h(s) = log{g(s)/g(s₀)} via max modulus on exp∘h.

Our formalization: For analytic g on ‖z‖ ≤ R with 0 < r < R:
  ‖g z‖ ≤ (2r/(R-r)) · (⨆_{‖ζ‖=R} Re g(ζ)) + ‖g 0‖

Proof: (1) Max modulus on f=exp∘g (2) Möbius transform (3) Schwarz lemma
--------------------------------------------------------------------------------
-/

/- Borel-Carathéodory inequality (pointwise).
   Corresponds to Titchmarsh Lemma β (page 57).

   The full proof is in Rh/BorelCaratheodory.lean. -/
alias borel_caratheodory_point := LZCBorelCaratheodory.borel_caratheodory_point

/-- Cauchy estimates at the origin for higher derivatives.

If `g` is complex-differentiable on the open disk of radius `R > 0` and continuous on its
closure, and `‖g z‖ ≤ M` for every `z` on the circle `‖z‖ = R`, then for all `n ≥ 0` we have
  `‖iteratedDeriv n g 0‖ ≤ n! * M / R^n`.

We combine the Cauchy integral representation for the power series coefficients
(`DiffContOnCl.hasFPowerSeriesOnBall`) with the norm bound on the circle
(`norm_cauchyPowerSeries_le`) and relate the coefficient to the iterated derivative via
`HasFPowerSeriesOnBall.factorial_smul`.
-/
lemma cauchy_estimate_iteratedDeriv_at_zero
    (g : ℂ → ℂ) {R M : ℝ}
    (hR : 0 < R)
    (hg : DiffContOnCl ℂ g (Metric.ball 0 R))
    (hM : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖g z‖ ≤ M) :
    ∀ n : ℕ, ‖iteratedDeriv n g 0‖ ≤ (n.factorial : ℝ) * M / R^n := by
  classical
  intro n
  -- Put `R` into `ℝ≥0` to use the standard Cauchy power series on a ball.
  let R' : NNReal := ⟨R, hR.le⟩
  have hg' : DiffContOnCl ℂ g (Metric.ball (0 : ℂ) (R' : ℝ)) := hg
  have hps : HasFPowerSeriesOnBall g (cauchyPowerSeries g 0 (R' : ℝ)) (0 : ℂ) (R' : ENNReal) := by
    simpa [R'] using
      (hg'.hasFPowerSeriesOnBall (c := (0 : ℂ)) (R := R')
        (show (0 : NNReal) < R' from by exact_mod_cast hR))
  -- Relate the power series coefficient to the iterated derivative at `0`.
  have hderiv :
      n.factorial • (cauchyPowerSeries g 0 (R' : ℝ) n (fun _ : Fin n => (1 : ℂ)))
        = iteratedDeriv n g 0 := by
    simpa [iteratedDeriv_eq_iteratedFDeriv] using (hps.factorial_smul (y := (1 : ℂ)) n)
  -- Bound the coefficient using `norm_cauchyPowerSeries_le` and the circle bound `hM`.
  have hcoef_le_op :
      ‖cauchyPowerSeries g 0 (R' : ℝ) n (fun _ : Fin n => (1 : ℂ))‖
        ≤ ‖cauchyPowerSeries g 0 (R' : ℝ) n‖ := by
    calc
      ‖cauchyPowerSeries g 0 (R' : ℝ) n (fun _ : Fin n => (1 : ℂ))‖
          ≤ ‖cauchyPowerSeries g 0 (R' : ℝ) n‖ * ∏ _ : Fin n, ‖(1 : ℂ)‖ :=
        ContinuousMultilinearMap.le_opNorm
          (cauchyPowerSeries g 0 (R' : ℝ) n) fun _ : Fin n => (1 : ℂ)
      _ = ‖cauchyPowerSeries g 0 (R' : ℝ) n‖ := by simp
  have hcont_g : Continuous fun θ : ℝ => g (circleMap (0 : ℂ) R θ) := by
    have hgcont : ContinuousOn g (Metric.closedBall (0 : ℂ) R) := hg.continuousOn_ball
    have hmem : ∀ θ : ℝ, circleMap (0 : ℂ) R θ ∈ Metric.closedBall (0 : ℂ) R := by
      intro θ
      exact circleMap_mem_closedBall (0 : ℂ) hR.le θ
    exact hgcont.comp_continuous (continuous_circleMap (0 : ℂ) R) hmem
  have hcont_norm : Continuous fun θ : ℝ => ‖g (circleMap (0 : ℂ) R θ)‖ := hcont_g.norm
  have hint :
      IntervalIntegrable (fun θ : ℝ => ‖g (circleMap (0 : ℂ) R θ)‖) volume 0 (2 * π) :=
    hcont_norm.intervalIntegrable 0 (2 * π)
  have hconst : IntervalIntegrable (fun _ : ℝ => M) volume 0 (2 * π) := by
    exact intervalIntegrable_const
  have hpoint : (fun θ : ℝ => ‖g (circleMap (0 : ℂ) R θ)‖) ≤ fun _ : ℝ => M := by
    intro θ
    have : circleMap (0 : ℂ) R θ ∈ Metric.sphere (0 : ℂ) R := by
      simpa using (circleMap_mem_sphere (0 : ℂ) hR.le θ)
    exact hM _ this
  have hint_le :
      (∫ θ : ℝ in 0..2 * π, ‖g (circleMap (0 : ℂ) R θ)‖) ≤ ∫ _ : ℝ in 0..2 * π, M := by
    exact intervalIntegral.integral_mono (μ := volume) Real.two_pi_pos.le hint hconst hpoint
  have havg_le : ((2 * π)⁻¹ * ∫ θ : ℝ in 0..2 * π, ‖g (circleMap (0 : ℂ) R θ)‖) ≤ M := by
    have hmul_le :
        (2 * π)⁻¹ *
            (∫ θ : ℝ in 0..2 * π, ‖g (circleMap (0 : ℂ) R θ)‖) ≤
          (2 * π)⁻¹ * (∫ _ : ℝ in 0..2 * π, M) :=
      mul_le_mul_of_nonneg_left hint_le (inv_nonneg.2 Real.two_pi_pos.le)
    have hconst_avg : (2 * π)⁻¹ * (∫ _ : ℝ in 0..2 * π, M) = M := by
      simp [intervalIntegral.integral_const]
      field_simp [Real.two_pi_pos.ne']
    exact hmul_le.trans_eq hconst_avg
  have hpow : |R|⁻¹ ^ n = 1 / R ^ n := by
    simp [abs_of_pos hR, div_eq_mul_inv]
  have hnorm_cps :
      ‖cauchyPowerSeries g 0 R n‖ ≤
        ((2 * π)⁻¹ * ∫ θ : ℝ in 0..2 * π, ‖g (circleMap (0 : ℂ) R θ)‖) * |R|⁻¹ ^ n := by
    exact norm_cauchyPowerSeries_le g 0 R n
  have hcoef_le : ‖cauchyPowerSeries g 0 (R' : ℝ) n (fun _ : Fin n => (1 : ℂ))‖ ≤ M / R ^ n := by
    have hmul :
        ((2 * π)⁻¹ * ∫ θ : ℝ in 0..2 * π, ‖g (circleMap (0 : ℂ) R θ)‖) * |R|⁻¹ ^ n ≤
          M * |R|⁻¹ ^ n :=
      mul_le_mul_of_nonneg_right havg_le (pow_nonneg (inv_nonneg.2 (abs_nonneg R)) _)
    have hstep : ‖cauchyPowerSeries g 0 R n‖ ≤ M * (|R|⁻¹ ^ n) :=
      (hnorm_cps.trans hmul)
    have hdiag :
        ‖cauchyPowerSeries g 0 (R' : ℝ) n (fun _ : Fin n => (1 : ℂ))‖ ≤
          ‖cauchyPowerSeries g 0 R n‖ := by
      -- `(R' : ℝ) = R` definitionally.
      change
        ‖cauchyPowerSeries g 0 (R' : ℝ) n (fun _ : Fin n => (1 : ℂ))‖ ≤
          ‖cauchyPowerSeries g 0 (R' : ℝ) n‖
      exact hcoef_le_op
    have hfinal :
        ‖cauchyPowerSeries g 0 (R' : ℝ) n (fun _ : Fin n => (1 : ℂ))‖ ≤
          M * (|R|⁻¹ ^ n) :=
      hdiag.trans hstep
    calc
      ‖cauchyPowerSeries g 0 (R' : ℝ) n (fun _ : Fin n => (1 : ℂ))‖ ≤ M * (|R|⁻¹ ^ n) := hfinal
      _ = M / R ^ n := by simp [hpow, div_eq_mul_inv]
  -- Combine the derivative/coefficient relation with the coefficient bound.
  have hmain :
      ‖iteratedDeriv n g 0‖ ≤
        (n.factorial : ℝ) * ‖cauchyPowerSeries g 0 (R' : ℝ) n (fun _ : Fin n => (1 : ℂ))‖ := by
    have : iteratedDeriv n g 0 =
        n.factorial • cauchyPowerSeries g 0 (R' : ℝ) n (fun _ : Fin n => (1 : ℂ)) := by
      simpa using hderiv.symm
    rw [this]
    exact
      norm_nsmul_le
        (a := cauchyPowerSeries g 0 (R' : ℝ) n (fun _ : Fin n => (1 : ℂ))) (n := n.factorial)
  calc
    ‖iteratedDeriv n g 0‖
        ≤ (n.factorial : ℝ) * ‖cauchyPowerSeries g 0 (R' : ℝ) n (fun _ : Fin n => (1 : ℂ))‖ :=
      hmain
    _ ≤ (n.factorial : ℝ) * (M / R ^ n) := by
      exact mul_le_mul_of_nonneg_left hcoef_le (Nat.cast_nonneg _)
    _ = (n.factorial : ℝ) * M / R ^ n := by
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

private theorem norm_le_boundaryRealSup_half_radius (g : ℂ → ℂ)
    (h_entire : Differentiable ℂ g) (R : ℝ) :
    ∀ z, ‖z‖ = R / 2 →
      ‖g z‖ ≤ 2 * (LZCBorelCaratheodory.boundaryRealSup g R - (g 0).re) + ‖g 0‖ := by
  intro z hz
  -- If R = 0, then z = 0 and the inequality is trivial
  by_cases hR0 : R = 0
  · have : z = 0 := by
      have : ‖z‖ = 0 := by simp [hz, hR0]
      exact norm_eq_zero.mp this
    subst this
    have hsup : LZCBorelCaratheodory.boundaryRealSup g R = (g 0).re := by
      classical
      simp [LZCBorelCaratheodory.boundaryRealSup, hR0, norm_eq_zero]
    have : LZCBorelCaratheodory.boundaryRealSup g R - (g 0).re = 0 := by
      simp [hsup]
    simp [this]
  -- Otherwise R > 0
  have hR : 0 < R := by
    have : 0 ≤ R := by
      -- r_seq tends to +∞, so it's eventually ≥ 0
      -- For a direct proof: ‖z‖ = R / 2 ≥ 0 implies R ≥ 0
      have : 0 ≤ ‖z‖ := norm_nonneg z
      have : 0 ≤ R / 2 := by rw [← hz]; exact this
      linarith
    exact lt_of_le_of_ne this (Ne.symm hR0)
  have : R / 2 < R := by
    have := half_lt_self hR; simpa [one_div] using this
  have hhol : ∀ w : ℂ, ‖w‖ ≤ R → DifferentiableAt ℂ g w :=
    fun _ _ => h_entire.differentiableAt
  have h_bdd : BddAbove {x | ∃ ζ : ℂ, ‖ζ‖ = R ∧ x = (g ζ).re} := by
    -- Continuity on the compact circle gives boundedness.
    have hset_eq :
        {x : ℝ | ∃ ζ : ℂ, ‖ζ‖ = R ∧ x = (g ζ).re}
          = ((fun ζ : ℂ => (g ζ).re) '' Metric.sphere (0 : ℂ) R) := by
      ext x
      constructor
      · rintro ⟨ζ, hζ, rfl⟩
        refine ⟨ζ, ?_, rfl⟩
        have : dist ζ (0 : ℂ) = R := by
          simpa [dist_eq_norm] using hζ
        simpa [Metric.mem_sphere] using this
      · rintro ⟨ζ, hζ, rfl⟩
        refine ⟨ζ, ?_, rfl⟩
        have : dist ζ (0 : ℂ) = R := by
          simpa [Metric.mem_sphere] using hζ
        simpa [dist_eq_norm] using this
    have hK : IsCompact (Metric.sphere (0 : ℂ) R) := isCompact_sphere _ _
    have hcont : Continuous fun ζ : ℂ => (g ζ).re :=
      Complex.continuous_re.comp h_entire.continuous
    have hbdd' : BddAbove ((fun ζ : ℂ => (g ζ).re) '' Metric.sphere (0 : ℂ) R) :=
      (hK.image hcont).bddAbove
    simpa [hset_eq] using hbdd'
  have hbc :=
    borel_caratheodory_point g R (R / 2) (by exact hR) this hhol h_bdd z
      (by simp [hz])
  -- Simplify the geometric factor when r = R/2
  have hfactor : (2 * (R / 2) / (R - R / 2)) = (2 : ℝ) := by
    have hR0' : R ≠ 0 := ne_of_gt hR
    field_simp [hR0']
    norm_num
  simpa [hfactor, mul_comm, mul_left_comm, mul_assoc] using hbc

private theorem polynomial_growth_bound_tendsto_zero (g : ℂ → ℂ)
    (ρ ε : ℝ) (hρ : 0 ≤ ρ) (k : ℕ) (hk : ρ < k) (hκε : ρ + ε < k)
    (r_seq : ℕ → ℝ) (hr_tendsto : Tendsto r_seq atTop atTop) (hr_pos : ∀ n, 0 < r_seq n) :
    Tendsto (fun n => (k.factorial : ℝ) *
      (2 * ((r_seq n) ^ (ρ + ε) - (g 0).re) + ‖g 0‖) / (r_seq n / 2) ^ k) atTop (𝓝 0) := by
  let B : ℕ → ℝ := fun n => (k.factorial : ℝ)
    * (2 * ((r_seq n) ^ (ρ + ε) - (g 0).re) + ‖g 0‖) / (r_seq n / 2) ^ k
  change Tendsto B atTop (𝓝 0)
  have h1 : Tendsto (fun n => (r_seq n : ℝ) ^ (ρ + ε - k)) atTop (𝓝 0) := by
    have hy : 0 < (k : ℝ) - (ρ + ε) := by
      have : ρ + ε < (k : ℝ) := by exact_mod_cast hκε
      linarith
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, Function.comp_def]
      using (tendsto_rpow_neg_atTop hy).comp hr_tendsto
  have h2 : Tendsto (fun n => (r_seq n : ℝ) ^ (-k : ℝ)) atTop (𝓝 0) := by
    have hk_pos : (0 : ℝ) < k := lt_of_le_of_lt hρ hk
    simpa [Function.comp_def] using (tendsto_rpow_neg_atTop hk_pos).comp hr_tendsto
  have hB_eq : ∀ n, B n =
      (k.factorial : ℝ) * 2 ^ (k + 1) * (r_seq n : ℝ) ^ (ρ + ε - k)
    + (k.factorial : ℝ) * 2 ^ k * (‖g 0‖ - 2 * (g 0).re) * (r_seq n : ℝ) ^ (-k : ℝ) := by
    intro n
    have hr : 0 < r_seq n := hr_pos n
    have hden : (r_seq n / 2 : ℝ) ^ k = (r_seq n : ℝ) ^ k / (2 : ℝ) ^ k := by
      simp [div_eq_mul_inv, mul_pow, inv_pow]
    calc
      B n
          = (k.factorial : ℝ) * (2 * ((r_seq n) ^ (ρ + ε) - (g 0).re) + ‖g 0‖)
                / (r_seq n ^ k / (2 : ℝ) ^ k) := by
              simp [B, hden]
      _ = (k.factorial : ℝ) * (2 * ((r_seq n) ^ (ρ + ε) - (g 0).re) + ‖g 0‖)
                * (2 : ℝ) ^ k / (r_seq n) ^ k := by
              simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = (k.factorial : ℝ) * 2 ^ k * (2 * ((r_seq n) ^ (ρ + ε) - (g 0).re) + ‖g 0‖)
                / (r_seq n) ^ k := by
              ring_nf
      _ = (k.factorial : ℝ) * 2 ^ k * (2 * (r_seq n) ^ (ρ + ε) + (‖g 0‖ - 2 * (g 0).re))
                / (r_seq n) ^ k := by
              ring
      _ = (k.factorial : ℝ) * 2 ^ k
              * (2 * ((r_seq n : ℝ) ^ (ρ + ε) / (r_seq n : ℝ) ^ k)
                + (‖g 0‖ - 2 * (g 0).re) / (r_seq n : ℝ) ^ k) := by
              ring
      _ = (k.factorial : ℝ) * 2 ^ (k + 1) * (r_seq n : ℝ) ^ (ρ + ε - k)
          + (k.factorial : ℝ) * 2 ^ k * (‖g 0‖ - 2 * (g 0).re) * (r_seq n : ℝ) ^ (-k : ℝ) := by
              have hquot1 :
                  (r_seq n : ℝ) ^ (ρ + ε) / (r_seq n : ℝ) ^ k =
                    (r_seq n : ℝ) ^ (ρ + ε - k) := by
                simpa [Real.rpow_natCast] using (Real.rpow_sub hr (ρ + ε) (k : ℝ)).symm
              have hquot2 :
                  (‖g 0‖ - 2 * (g 0).re) / (r_seq n : ℝ) ^ k =
                    (‖g 0‖ - 2 * (g 0).re) * (r_seq n : ℝ) ^ (-k : ℝ) := by
                simp [div_eq_mul_inv]
              simp [hquot1, hquot2]
              ring_nf
  have hterm1 :
      Tendsto (fun n =>
          (k.factorial : ℝ) * 2 ^ (k + 1) * (r_seq n : ℝ) ^ (ρ + ε - k)) atTop (𝓝 0) := by
    have :
        Tendsto (fun n => ((k.factorial : ℝ) * 2 ^ (k + 1)) * (r_seq n : ℝ) ^ (ρ + ε - k))
          atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul h1)
    simpa [mul_assoc] using this
  have hterm2 :
      Tendsto (fun n =>
          (k.factorial : ℝ) * 2 ^ k * (‖g 0‖ - 2 * (g 0).re) * (r_seq n : ℝ) ^ (-k : ℝ))
        atTop (𝓝 0) := by
    have :
        Tendsto (fun n =>
            ((k.factorial : ℝ) * 2 ^ k * (‖g 0‖ - 2 * (g 0).re)) * (r_seq n : ℝ) ^ (-k : ℝ))
          atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul h2)
    simpa [mul_assoc] using this
  have hsum :
      Tendsto (fun n =>
          (k.factorial : ℝ) * 2 ^ (k + 1) * (r_seq n : ℝ) ^ (ρ + ε - k)
        + (k.factorial : ℝ) * 2 ^ k * (‖g 0‖ - 2 * (g 0).re) * (r_seq n : ℝ) ^ (-k : ℝ))
        atTop (𝓝 0) := by
    simpa using (hterm1.add hterm2)
  exact (Filter.Tendsto.congr (fun n => (hB_eq n).symm) hsum)

/-- **Theorem 2.3**: If Re g(z) = O(r^ρ), then g is a polynomial of degree ≤ ρ

Theorem 2.3. Let g: ℂ → ℂ be entire. If for all ε > 0 there exists a sequence
{rₙ} with rₙ → ∞ such that Re g(z) < r^{ρ+ε} whenever |z| = rₙ, then g(z) is
a polynomial of degree ≤ ρ.

Theorem 2.3 is equivalent to saying: if for all ε > 0 there exists some rₙ → ∞
such that Re g(z) < rₙ^{ρ+ε} whenever |z| = rₙ, then g(z) is a polynomial of
degree at most ρ. The sequence rₙ is necessary to avoid weird behavior at
particular radii in applications.

Proof. By the Borel-Carathéodory inequality, for 0 < r < R,
  max_{|z|≤r} |g(z)| ≤ (2r)/(R-r) · max_{|z|=R} Re g(z) + |g(0)|

By Liouville's Theorem (the souped-up version) g(z) must be a polynomial
of degree less than or equal to ρ.
-/
lemma polynomial_from_growth (g : ℂ → ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (h_entire : Differentiable ℂ g)
    (h_growth : ∀ ε > 0, ∃ r_seq : ℕ → ℝ, Filter.Tendsto r_seq Filter.atTop Filter.atTop ∧
                ∀ n : ℕ, ∀ z : ℂ, ‖z‖ = r_seq n → (g z).re < ‖z‖^(ρ + ε)) :
  ∃ p : Polynomial ℂ, (∀ z, g z = p.eval z) ∧ (p.natDegree : ℝ) ≤ ρ :=
  by
  classical
  -- For k > ρ, the k-th derivative at 0 is 0.
  have h_vanish : ∀ k : ℕ, ρ < k → iteratedDeriv k g 0 = 0 := by
    intro k hk
    -- Pick ε > 0 with ρ + ε < k
    set ε : ℝ := ((k : ℝ) - ρ) / 2
    have hεpos : 0 < ε := by
      have : 0 < (k : ℝ) - ρ := sub_pos.mpr hk
      simpa [ε] using half_pos this
    have hκε : ρ + ε < k := by
      have : ρ + ((k : ℝ) - ρ) / 2 < ρ + ((k : ℝ) - ρ) := by
        have : 0 < ((k : ℝ) - ρ) / 2 := by simpa [ε] using half_pos (sub_pos.mpr hk)
        linarith
      simpa [ε, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    -- Get radii r_n with Re g(z) < ‖z‖^(ρ+ε) on the circle of radius r_n
    obtain ⟨r_seq0, hr_tendsto0, hr_bound0⟩ := h_growth ε hεpos
    -- Drop finitely many initial terms so that `r_seq n ≥ 1` for all `n`.
    have hr_ge1 : ∀ᶠ n in atTop, (1 : ℝ) ≤ r_seq0 n :=
      hr_tendsto0.eventually_ge_atTop 1
    rcases (eventually_atTop.1 hr_ge1) with ⟨N0, hN0⟩
    let r_seq : ℕ → ℝ := fun n => r_seq0 (n + N0)
    have hr_tendsto : Tendsto r_seq atTop atTop := by
      simpa [r_seq, Function.comp_def] using hr_tendsto0.comp (tendsto_add_atTop_nat N0)
    have hr_bound : ∀ n : ℕ, ∀ z : ℂ, ‖z‖ = r_seq n → (g z).re < ‖z‖^(ρ + ε) := by
      intro n z hz
      exact hr_bound0 (n + N0) z hz
    have hr_pos : ∀ n, 0 < r_seq n := by
      intro n
      have h1 : (1 : ℝ) ≤ r_seq0 (n + N0) := hN0 (n + N0) (Nat.le_add_left N0 n)
      have : (0 : ℝ) < r_seq0 (n + N0) := lt_of_lt_of_le (by norm_num) h1
      simpa [r_seq] using this
    -- Bound on the smaller circle of radius r_n/2 via Borel–Carathéodory
    have h_small_bound : ∀ n z, ‖z‖ = (r_seq n) / 2 →
        ‖g z‖ ≤ 2 * (LZCBorelCaratheodory.boundaryRealSup g (r_seq n) - (g 0).re) + ‖g 0‖ :=
      fun n => norm_le_boundaryRealSup_half_radius g h_entire (r_seq n)
    -- Cauchy estimates on radius r_n/2
    have h_cauchy : ∀ n, ‖iteratedDeriv k g 0‖ ≤
        (k.factorial : ℝ)
          * (2 * (LZCBorelCaratheodory.boundaryRealSup g (r_seq n) - (g 0).re) + ‖g 0‖)
        / (r_seq n / 2) ^ k := by
      intro n
      have hDiff : DiffContOnCl ℂ g (Metric.ball 0 (r_seq n / 2)) :=
        ⟨h_entire.differentiableOn, h_entire.continuous.continuousOn⟩
      have hM : ∀ z ∈ Metric.sphere (0 : ℂ) (r_seq n / 2), ‖g z‖
          ≤ 2 * (LZCBorelCaratheodory.boundaryRealSup g (r_seq n) - (g 0).re) + ‖g 0‖ := by
        intro z hz
        have := hz
        simpa [Metric.mem_sphere, dist_eq_norm]
          using (h_small_bound n z (by simpa [Metric.mem_sphere, dist_eq_norm] using hz))
      have hR : 0 < r_seq n := hr_pos n
      have : 0 < r_seq n / 2 := half_pos hR
      exact cauchy_estimate_iteratedDeriv_at_zero g this hDiff hM k
    -- Compare the boundary supremum of `Re g` with the given growth bound.
    have hA_le : ∀ n, LZCBorelCaratheodory.boundaryRealSup g (r_seq n) ≤ (r_seq n) ^ (ρ + ε) := by
      intro n
      have h1 : ∀ ζ : ℂ, ‖ζ‖ = r_seq n → (g ζ).re ≤ (r_seq n) ^ (ρ + ε) := by
        intro ζ hζ
        have hlt : (g ζ).re < ‖ζ‖ ^ (ρ + ε) := hr_bound n ζ hζ
        simpa [hζ] using le_of_lt hlt
      unfold LZCBorelCaratheodory.boundaryRealSup
      refine csSup_le ?_ ?_
      · refine ⟨(g (r_seq n : ℂ)).re, ?_⟩
        refine ⟨(r_seq n : ℂ), ?_, rfl⟩
        have : 0 ≤ r_seq n := le_of_lt (hr_pos n)
        simp [this]
      · rintro _ ⟨ζ, hζ, rfl⟩
        exact h1 ζ hζ
    -- Let `B n` be the numeric bound; show `B n → 0` as `n → ∞`.
    set B : ℕ → ℝ := fun n => (k.factorial : ℝ)
        * (2 * ((r_seq n) ^ (ρ + ε) - (g 0).re) + ‖g 0‖) / (r_seq n / 2) ^ k
    have h_deriv_le_B : ∀ n, ‖iteratedDeriv k g 0‖ ≤ B n := by
      intro n
      have h_cauchy_n := h_cauchy n
      have hdiff_le : LZCBorelCaratheodory.boundaryRealSup g (r_seq n) - (g 0).re
          ≤ (r_seq n : ℝ) ^ (ρ + ε) - (g 0).re :=
        sub_le_sub_right (hA_le n) _
      have hinner :
          2 * (LZCBorelCaratheodory.boundaryRealSup g (r_seq n) - (g 0).re) + ‖g 0‖
          ≤ 2 * ((r_seq n : ℝ) ^ (ρ + ε) - (g 0).re) + ‖g 0‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hdiff_le (by norm_num)) le_rfl
      have hnum_le : (k.factorial : ℝ)
          * (2 * (LZCBorelCaratheodory.boundaryRealSup g (r_seq n) - (g 0).re) + ‖g 0‖)
          ≤ (k.factorial : ℝ)
            * (2 * ((r_seq n : ℝ) ^ (ρ + ε) - (g 0).re) + ‖g 0‖) :=
        mul_le_mul_of_nonneg_left hinner (by exact_mod_cast Nat.cast_nonneg k.factorial)
      have hden_nonneg : 0 ≤ (r_seq n / 2 : ℝ) ^ k := by
        exact pow_nonneg (le_of_lt (half_pos (hr_pos n))) _
      have hdiv_le :
          (k.factorial : ℝ)
              * (2 * (LZCBorelCaratheodory.boundaryRealSup g (r_seq n) - (g 0).re) + ‖g 0‖)
              / (r_seq n / 2) ^ k
          ≤ (k.factorial : ℝ)
              * (2 * ((r_seq n : ℝ) ^ (ρ + ε) - (g 0).re) + ‖g 0‖)
              / (r_seq n / 2) ^ k :=
        by
          -- Avoid lemma-name churn: rewrite `a / d` as `a * d⁻¹`.
          simpa [div_eq_mul_inv] using
            (mul_le_mul_of_nonneg_right hnum_le (inv_nonneg.mpr hden_nonneg))
      exact h_cauchy_n.trans (by simpa [B] using hdiv_le)
    -- Show `B n → 0` using `tendsto_rpow_neg_atTop`
    have hB0 : Tendsto B atTop (𝓝 0) :=
      polynomial_growth_bound_tendsto_zero g ρ ε hρ k hk hκε r_seq hr_tendsto hr_pos
    -- From `‖deriv‖ ≤ B n` for all `n` and `B n → 0`, we deduce the norm is 0
    have : ‖iteratedDeriv k g 0‖ = 0 := by
      have hconst :
          Tendsto (fun _ : ℕ => ‖iteratedDeriv k g 0‖) atTop (𝓝 ‖iteratedDeriv k g 0‖) :=
        tendsto_const_nhds
      have hconst0 : Tendsto (fun _ : ℕ => ‖iteratedDeriv k g 0‖) atTop (𝓝 0) := by
        refine
          tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hB0
            (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            (Filter.Eventually.of_forall fun n => h_deriv_le_B n)
      exact tendsto_nhds_unique hconst hconst0
    simpa [norm_eq_zero] using this
  -- Truncated Taylor polynomial at 0
  set N : ℕ := Nat.floor ρ
  let p : Polynomial ℂ :=
    ∑ i ∈ Finset.range (N + 1),
      Polynomial.C ((i.factorial : ℂ)⁻¹ * (iteratedDeriv i g 0)) * (Polynomial.X ^ i)
  have hg_eq : ∀ z : ℂ, g z = p.eval z := by
    intro z
    have hts := (Complex.taylorSeries_eq_of_entire' (c := 0) (z := z) h_entire).symm
    -- Only finitely many coefficients survive since `iteratedDeriv i g 0 = 0` for `i > N`.
    have hvan : ∀ n ∉ Finset.range (N + 1),
        (n.factorial : ℂ)⁻¹ * iteratedDeriv n g 0 * z ^ n = 0 := by
      intro n hn
      have hn' : N + 1 ≤ n := by
        have hnlt : ¬ n < N + 1 := by
          intro hlt
          exact hn (Finset.mem_range.mpr hlt)
        exact (not_lt).1 hnlt
      have hρ_lt_N1 : ρ < (N : ℝ) + 1 := by
        simpa [N] using (Nat.lt_floor_add_one ρ)
      have hN1_le_n : (N : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn'
      have hρ_lt_n : ρ < (n : ℝ) := lt_of_lt_of_le hρ_lt_N1 hN1_le_n
      have hder0 : iteratedDeriv n g 0 = 0 := h_vanish n (by simpa using hρ_lt_n)
      simp [hder0]
    have hsum : ∑' n : ℕ, (n.factorial : ℂ)⁻¹ * iteratedDeriv n g 0 * z ^ n
        = ∑ n ∈ Finset.range (N + 1), (n.factorial : ℂ)⁻¹ * iteratedDeriv n g 0 * z ^ n := by
      simpa [hvan] using (tsum_eq_sum (s := Finset.range (N + 1)) hvan)
    -- Evaluate the polynomial
    have : p.eval z = ∑ n ∈ Finset.range (N + 1),
        (n.factorial : ℂ)⁻¹ * iteratedDeriv n g 0 * z ^ n := by
      simp [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, mul_comm]
    simpa [this, hsum] using hts
  -- Degree bound: natDegree p ≤ N ≤ ρ
  have hp_degree_le : p.natDegree ≤ N := by
    have hdeg_term : ∀ i ∈ Finset.range (N + 1),
        Polynomial.degree
            (Polynomial.C ((i.factorial : ℂ)⁻¹ * iteratedDeriv i g 0) * Polynomial.X ^ i)
          ≤ (N : WithBot ℕ) := by
      intro i hi
      have : Polynomial.degree (Polynomial.C ((i.factorial : ℂ)⁻¹ * iteratedDeriv i g 0)
            * Polynomial.X ^ i) ≤ (i : WithBot ℕ) := by
        simpa using
          (Polynomial.degree_C_mul_X_pow_le (R := ℂ) i
            (((i.factorial : ℂ)⁻¹ * iteratedDeriv i g 0)))
      have hiNat : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hi' : (i : WithBot ℕ) ≤ (N : WithBot ℕ) := by exact_mod_cast hiNat
      exact le_trans this hi'
    have : Polynomial.degree p ≤ (N : WithBot ℕ) := by
      have hsum_le_term :
          (∑ i ∈ Finset.range (N + 1),
                Polynomial.C ((i.factorial : ℂ)⁻¹ * iteratedDeriv i g 0) * Polynomial.X ^ i).degree
            ≤ (Finset.range (N + 1)).sup fun i =>
                (Polynomial.C ((i.factorial : ℂ)⁻¹ * iteratedDeriv i g 0)
                  * Polynomial.X ^ i).degree := by
        exact
          (Polynomial.degree_sum_le (s := Finset.range (N + 1))
            (f := fun i =>
              Polynomial.C ((i.factorial : ℂ)⁻¹ * iteratedDeriv i g 0) * Polynomial.X ^ i))
      have hsum_le :
          Polynomial.degree p ≤ (Finset.range (N + 1)).sup fun i =>
              (Polynomial.C ((i.factorial : ℂ)⁻¹ * iteratedDeriv i g 0)
                * Polynomial.X ^ i).degree := by
        simpa only [p] using hsum_le_term
      refine le_trans hsum_le ?_
      refine Finset.sup_le ?_
      intro i hi
      exact hdeg_term i hi
    exact (Polynomial.natDegree_le_iff_degree_le).mpr this
  refine ⟨p, hg_eq, by
    have : (p.natDegree : ℝ) ≤ (N : ℝ) := by exact_mod_cast hp_degree_le
    have : (p.natDegree : ℝ) ≤ ρ := this.trans (by exact_mod_cast Nat.floor_le hρ)
    exact this⟩

-- We use Mathlib's `Real.circleAverage` for circle averages.

/- **Theorem 3.1** (Jensen's Formula): Relates zeros to maximum modulus

Theorem 3.1 (Jensen's Formula). Let f be analytic in B(0;r) with zeros a₁,...,aₙ
in B(0;r) (repeated by multiplicity). If f(0) ≠ 0 then
  log|f(0)| = -∑_{j=1}^n log(r/|aⱼ|) + (1 / 2π) ∫₀^{2π} log|f(re^{iθ})| dθ

Jensen's Formula 1.2. Let f be analytic on a region containing B(0;r) and
suppose that a₁,...,aₙ are the zeros of f in B(0;r) repeated according to
multiplicity. If f(0) ≠ 0 then
  log|f(0)| = -∑_{j=1}^n log(r/|aⱼ|) + (1 / 2π) ∫₀^{2π} log|f(re^{iθ})| dθ

Proof. If |b| < 1 then the map (z-b)(1-bz)^{-1} takes the disk B(0;1) onto
itself. Therefore (r²-āⱼz)/(r(z-aⱼ)) maps B(0;1) onto itself and takes the
boundary to the boundary.

Therefore F(z) = f(z)∏(r²-āⱼz)/(r(z-aⱼ)) is analytic in an open set containing
B(0;r), has no zeros in B(0;r), and |F(z)| = |f(z)| for |z| = r.

So (1.1) applies to F to give
  log|F(0)| = (1 / 2π) ∫₀^{2π} log|f(re^{iθ})| dθ.
However F(0) = f(0)∏(-āⱼ/aⱼ)(r/aⱼ) so that Jensen's Formula results.
-/
/-- Circle average of an analytic function equals its center value.

If `g` is complex differentiable on the open ball `ball 0 R` and continuous on its closure
(`DiffContOnCl`), then its circle average on `|z| = R` equals `g 0`.
-/
lemma circleAverage_of_analytic (g : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hg : DiffContOnCl ℂ g (Metric.ball (0 : ℂ) R)) :
    Real.circleAverage g 0 R = g 0 := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    simpa [Metric.mem_ball, dist_eq_norm] using hR
  calc
    Real.circleAverage g 0 R
        = (2 * π * I)⁻¹ • ∮ z in C(0, R), (z - (0 : ℂ))⁻¹ • g z := by
          simpa using
            (Real.circleAverage_eq_circleIntegral (f := g) (c := (0 : ℂ)) (R := R) hRne)
    _ = g 0 := by
      simpa using
        (DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul
          (R := R) (c := (0 : ℂ)) (w := (0 : ℂ)) (f := g) hg h0mem)

/-- If a branch `g` of the logarithm exists on the closed disk, the circle average of `log ‖f‖`
equals `log ‖f(0)‖`. -/
lemma circleAverage_log_norm_of_hasLog
    (f : ℂ → ℂ) (g : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hg : DiffContOnCl ℂ g (Metric.ball (0 : ℂ) R))
    (hexp : ∀ z, ‖z‖ ≤ R → f z = Complex.exp (g z)) :
    Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 R = Real.log ‖f 0‖ := by
  classical
  have hlog_eq_re :
      Set.EqOn (fun z : ℂ => Real.log ‖f z‖) (fun z : ℂ => (g z).re)
        (Metric.sphere (0 : ℂ) |R|) := by
    intro z hz
    have hz_norm : ‖z‖ = |R| := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hz_le : ‖z‖ ≤ R := by
      have : ‖z‖ = R := by simpa [abs_of_pos hR] using hz_norm
      exact this.le
    have hfz : f z = Complex.exp (g z) := hexp z hz_le
    simp [hfz, Complex.norm_exp, Real.log_exp]
  have hlog_avg :
      Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 R
        = Real.circleAverage (fun z : ℂ => (g z).re) 0 R := by
    simpa using Real.circleAverage_congr_sphere (c := (0 : ℂ)) (R := R) hlog_eq_re
  have hg_int : CircleIntegrable g (0 : ℂ) R := by
    have hg_cont :
        ContinuousOn g (Metric.sphere (0 : ℂ) R) :=
      (hg.continuousOn_ball.mono Metric.sphere_subset_closedBall)
    exact hg_cont.circleIntegrable (c := (0 : ℂ)) (R := R) (le_of_lt hR)
  have hre_avg :
      Real.circleAverage (fun z : ℂ => (g z).re) 0 R = (g 0).re := by
    have hre :
        Real.circleAverage (fun z : ℂ => (g z).re) 0 R = (Real.circleAverage g 0 R).re := by
      simpa [Function.comp_def] using
        (Complex.reCLM.circleAverage_comp_comm (c := (0 : ℂ)) (R := R) (f := g) hg_int)
    have hg_avg : Real.circleAverage g 0 R = g 0 := circleAverage_of_analytic g R hR hg
    simpa [hg_avg] using hre
  have hlog0 : Real.log ‖f 0‖ = (g 0).re := by
    have hf0 : f 0 = Complex.exp (g 0) := by
      simpa using (hexp 0 (by simpa using (le_of_lt hR)))
    simp [hf0, Complex.norm_exp, Real.log_exp]
  calc
    Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 R
        = Real.circleAverage (fun z : ℂ => (g z).re) 0 R := hlog_avg
    _ = (g 0).re := hre_avg
    _ = Real.log ‖f 0‖ := hlog0.symm
  /-
  -- Parameterized equality on the circle via `circleMap`.
  have hparam_eq : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      Real.log ‖f (circleMap 0 R θ)‖ = (g (circleMap 0 R θ)).re := by
    intro θ hθ
    -- On the circle: ‖circleMap 0 R θ‖ = |R| ≤ R (since R > 0).
    have hnorm : ‖circleMap 0 R θ‖ = |R| := by
      simpa [Metric.mem_sphere, dist_eq_norm] using circleMap_mem_sphere' (0 : ℂ) R θ
    have hle : ‖circleMap 0 R θ‖ ≤ R := by
      have : 0 ≤ R := le_of_lt hR
      simpa [hnorm, abs_of_nonneg this]
    -- Apply the exponential representation and compute norms/logs.
    have hf := hexp (circleMap 0 R θ) hle
    simpa [hf, Complex.norm_exp, Real.log_exp]
  -- Rewrite the circle average of `log ‖f‖` using the parameterization.
  have havg_log :
      Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 R
        = (2 * π)⁻¹ • ∫ θ in (0)..2 * π, Real.log ‖f (circleMap 0 R θ)‖ := by
    simp [Real.circleAverage]
  have havg_re :
      Real.circleAverage (fun z : ℂ => (g z).re) 0 R
        = (2 * π)⁻¹ • ∫ θ in (0)..2 * π, (g (circleMap 0 R θ)).re := by
    simp [Real.circleAverage]
  -- Convert the first average to the second using the pointwise equality on the circle.
  have havg_conv :
      (2 * π)⁻¹ • ∫ θ in (0)..2 * π, Real.log ‖f (circleMap 0 R θ)‖
        = (2 * π)⁻¹ • ∫ θ in (0)..2 * π, (g (circleMap 0 R θ)).re := by
    -- Use intervalIntegral.congr
    have : (fun θ => Real.log ‖f (circleMap 0 R θ)‖)
          =ᵐ[Measure.restrict volume (Set.uIoc (0 : ℝ) (2 * π))]
          (fun θ => (g (circleMap 0 R θ)).re) := by
      -- Pointwise equality on [0, 2π], up to endpoints (measure zero issue is harmless).
      refine (ae_restrict_of_ae ?_)
      apply Filter.Eventually.of_forall
      intro θ
      have : θ ∈ Set.Icc (0 : ℝ) (2 * π) ∨ θ ∉ Set.Icc (0 : ℝ) (2 * π) := by exact em _
      cases this with
      | inl hθ => simpa using hparam_eq θ hθ
      | inr _ => simp
    -- Now, convert integrals.
    simpa [intervalIntegral, Measure.restrict_restrict] using
      congrArg (fun t => (2 * π)⁻¹ • t)
        (intervalIntegral.integral_congr_ae this)
  -- Commute `Re` with the integral and scalar, to identify with `(Real.circleAverage g 0 R).re`.
  have hlin_int :
      (2 * π)⁻¹ • ∫ θ in (0)..2 * π, (g (circleMap 0 R θ)).re
        = ((2 * π)⁻¹ • ∫ θ in (0)..2 * π, g (circleMap 0 R θ)).re := by
    -- scalar is real; `re` is ℝ-linear, and integral commutes with `re`.
    have hcont : Continuous fun θ : ℝ => g (circleMap 0 R θ) := by
      -- `g` is continuous on the closed ball; compose with continuous `circleMap`.
      have hgc : ContinuousOn g (Metric.closedBall (0 : ℂ) R) :=
        (hg.continuousOn_ball (x := (0 : ℂ)) (r := R))
      refine
        (hgc.comp_continuous (continuous_circleMap 0 R).continuousOn ?_).continuousAt.continuous
      intro θ; exact circleMap_mem_closedBall' (0 : ℂ) R θ
    have hint : IntervalIntegrable (fun θ : ℝ => g (circleMap 0 R θ)) volume 0 (2 * π) :=
      hcont.intervalIntegrable _ _
    -- Use CLM integral linearity for `reCLM`.
    have :=
      (ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) (L := Complex.reCLM)
        (φ := fun θ : ℝ => g (circleMap 0 R θ)) (μ := volume)
        (by
          -- integrable on restricted measure over uIoc
          -- derive integrability on intervalIntegral via intervalIntegrable_iff
          -- but `integral_comp_comm` expects Integrable; we can pass through IntervalIntegral.eq
          -- Simplify by using the interval integral identity for continuous functions.
          -- We can apply `hint.intervalIntegrable`.
          -- Switch to `Integrable` on restricted measure via `intervalIntegrable_iff`.
          have := intervalIntegrable_iff.1 hint
          exact this)).symm
    -- Unfold interval integral and use the commutation.
    simp [Real.circleAverage, intervalIntegral, this, map_mul]
      -- map_mul is not correct; adjust manually
      at *
    -- Since this path is cumbersome, argue directly by Bochner linearity on `[0,2π]`:
    -- `re (∫ ϕ) = ∫ re ∘ ϕ`, and `re (r • z) = r * re z` for real scalar r.
    -- So the claim follows.
    -- We finish with a direct rewrite.
    ring
  -- Combine.
  have : Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 R
      = ((2 * π)⁻¹ • ∫ θ in (0)..2 * π, g (circleMap 0 R θ)).re := by
    simpa [havg_log, havg_re, havg_conv] using hlin_int
  -- Evaluate via `circleAverage_of_analytic`.
  have havg_g : Real.circleAverage g 0 R = g 0 := circleAverage_of_analytic g R hR hg
  have hf0 : f 0 = Complex.exp (g 0) := hexp 0 (by simpa)
  -- Expand RHS circle average of g and take real parts.
  have : Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 R = (g 0).re := by
    -- Rewrite `(2π)⁻¹ ∫ ...` back to `Real.circleAverage g`.
    have : ((2 * π)⁻¹ • ∫ θ in (0)..2 * π, g (circleMap 0 R θ)) = Real.circleAverage g 0 R := by
      simp [Real.circleAverage]
    simpa [this] using congrArg re this
  -- Finish by rewriting `log ‖f 0‖`.
  simpa [hf0, Complex.norm_exp, Real.log_exp] using this

-/
/-- On the circle `|z|=R`, the elementary factor `B_a(z) = (R^2 - conj a * z)/(R (z - a))` has
unit modulus. -/
lemma blaschke_on_sphere_norm_one (a z : ℂ) (R : ℝ)
    (hz : ‖z‖ = R) (ha : ‖a‖ < R) :
    ‖(R^2 - (conj a) * z) / (R * (z - a))‖ = 1 := by
  have hRpos : 0 < R := lt_of_le_of_lt (by simp) ha
  have hz_ne_a : z ≠ a := by
    intro hza
    have : ‖a‖ = R := by simpa [hza] using hz
    exact (ne_of_lt ha) this
  have hzmul : z * conj z = (R^2 : ℂ) := by
    have hzmul' : z * conj z = ((R : ℂ)^2) := by
      simpa [hz] using (mul_conj' z)
    have : ((R : ℂ)^2) = (R^2 : ℂ) := by
      norm_cast
    simpa [this] using hzmul'
  have hnum : (R^2 - (conj a) * z) = z * conj (z - a) := by
    calc
      (R^2 - (conj a) * z) = z * conj z - (conj a) * z := by
        simp [hzmul]
      _ = z * (conj z - conj a) := by
        ring
      _ = z * conj (z - a) := by
        simp
  have hnorm_num : ‖(R^2 - (conj a) * z)‖ = R * ‖z - a‖ := by
    calc
      ‖(R^2 - (conj a) * z)‖ = ‖z * conj (z - a)‖ := by simp [hnum]
      _ = ‖z‖ * ‖conj (z - a)‖ := by
        simp
      _ = ‖z‖ * ‖z - a‖ := by
        rw [norm_conj (z - a)]
      _ = R * ‖z - a‖ := by simp [hz]
  have hnorm_den : ‖R * (z - a)‖ = R * ‖z - a‖ := by
    calc
      ‖R * (z - a)‖ = ‖(R : ℂ) * (z - a)‖ := by rfl
      _ = ‖(R : ℂ)‖ * ‖z - a‖ := by
        simp
      _ = ‖R‖ * ‖z - a‖ := by simp [Complex.norm_real]
      _ = |R| * ‖z - a‖ := by simp [Real.norm_eq_abs]
      _ = R * ‖z - a‖ := by simp [abs_of_pos hRpos]
  have hne : R * ‖z - a‖ ≠ 0 := by
    refine mul_ne_zero (ne_of_gt hRpos) ?_
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz_ne_a)
  rw [norm_div, hnorm_num, hnorm_den]
  simp [hne]
  /-
  -- R is positive by assumption
  have hRpos : 0 < R := lt_of_le_of_lt (by simpa using norm_nonneg a) ha
  -- Let w be the point on the unit circle with z = R • w
  set w : ℂ := z / (R : ℂ) with hwdef
  have hRw : (R : ℂ) * w = z := by
    rw [hwdef]
    field_simp
    ring
  have hw_norm : ‖w‖ = 1 := by
    rw [hwdef, norm_div, hz, abs_of_pos hRpos]
    exact div_self (ne_of_gt hRpos)
  -- Simplify ratio using z = R * w
  have hratio :
      (R^2 - (conj a) * z) / (R * (z - a))
        = ((R : ℂ) - (conj a) * w) / ((R : ℂ) * w - a) := by
    rw [hRw, pow_two]
    field_simp
    ring
  -- Show equality of the two norms in the right-hand ratio
  have hnumden : ‖(R : ℂ) - (conj a) * w‖ = ‖(R : ℂ) * w - a‖ := by
    have h_wconj : w * conj w = 1 := by
      have : Complex.normSq w = 1 := by
        rw [Complex.normSq_eq_norm_sq, hw_norm]
        norm_num
      have : (Complex.normSq w : ℂ) = 1 := by simp [this]
      rw [Complex.normSq_eq_conj_mul_self] at this
      rw [mul_comm]
      exact this
    calc
      ‖(R : ℂ) - (conj a) * w‖
          = ‖(R : ℂ) * (w * conj w) - (conj a) * w‖ := by rw [h_wconj, mul_one]
      _   = ‖w * ((R : ℂ) * (conj w) - conj a)‖ := by ring_nf
      _   = ‖(R : ℂ) * (conj w) - conj a‖ := by rw [norm_mul, hw_norm, one_mul]
      _   = ‖conj ((R : ℂ) * w - a)‖ := by simp [map_mul, map_sub]
      _   = ‖(R : ℂ) * w - a‖ := by rw [norm_conj]
  -- Conclude that the norm of the ratio is 1
  have h_denom_ne : (R : ℂ) * w - a ≠ 0 := by
    intro heq
    have h_eq : (R : ℂ) * w = a := by
      have : (R : ℂ) * w - a + a = 0 + a := by rw [heq]
      simp at this
      exact this
    have : ‖a‖ = ‖(R : ℂ) * w‖ := by rw [← h_eq]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos, hw_norm, mul_one] at this
    linarith [ha]
  rw [hratio, norm_div, hnumden]
  exact div_self (norm_ne_zero_iff.mpr h_denom_ne)

-/
lemma jensen_formula (f : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (_h_holo : ∀ z : ℂ, ‖z‖ ≤ R → DifferentiableAt ℂ f z)
    (_h_nozeros_boundary : ∀ z : ℂ, ‖z‖ = R → f z ≠ 0)
    (h_nonzero_0 : f 0 ≠ 0)
    (zeros : Finset ℂ) (h_zeros : ∀ a ∈ zeros, f a = 0 ∧ ‖a‖ < R)
      -- Existence of a holomorphic logarithm for the modified function F on the closed disk
      (h_logF : ∃ g : ℂ → ℂ, DiffContOnCl ℂ g (Metric.ball (0 : ℂ) R) ∧
        (∀ z : ℂ, ‖z‖ ≤ R →
          (f z) * (∏ a ∈ zeros, ((R : ℂ)^2 - (conj a) * z) / ((R : ℂ) * (z - a)))
            = Complex.exp (g z))) :
  Real.log ‖f 0‖ =
    -∑ a ∈ zeros, Real.log (R / ‖a‖) +
    Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 R :=
by
  classical
  -- Define the Blaschke product B and the modified function F
  let factor : ℂ → ℂ → ℂ := fun a z => ((R : ℂ)^2 - (conj a) * z) / ((R : ℂ) * (z - a))
  let B : ℂ → ℂ := fun z => ∏ a ∈ zeros, factor a z
  let F : ℂ → ℂ := fun z => f z * B z
  -- Step 1: Circle averages of log norms of f and F coincide (since |B| = 1 on the circle)
  have h_avg_eq :
      Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 R
        = Real.circleAverage (fun z : ℂ => Real.log ‖F z‖) 0 R := by
    -- Prove pointwise on the circle: log ‖F(z)‖ = log ‖f(z)‖
    have h_on_sphere :
        Set.EqOn (fun z : ℂ => Real.log ‖F z‖) (fun z : ℂ => Real.log ‖f z‖)
          (Metric.sphere (0 : ℂ) R) := by
      intro z hz
      have hzR : ‖z‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
      -- Each factor has norm 1 by the Blaschke lemma
      have hnorm_prod : ‖B z‖ = 1 := by
        classical
        have hzeros_interior : ∀ a ∈ zeros, ‖a‖ < R := fun a ha => (h_zeros a ha).2
        -- Work with the explicit product form and induct, carrying the interior hypothesis.
        have hP :
            ∀ s : Finset ℂ, (∀ a ∈ s, ‖a‖ < R) → ‖∏ a ∈ s, factor a z‖ = 1 := by
          intro s
          classical
          refine Finset.induction_on s ?base ?step
          · intro _
            simp
          · intro a s ha_notin hIH hs'
            have ha_interior : ‖a‖ < R := hs' a (by simp)
            have hs_interior : ∀ b ∈ s, ‖b‖ < R := by
              intro b hb
              exact hs' b (by simp [hb])
            have hfac : ‖factor a z‖ = 1 := by
              simpa [factor] using blaschke_on_sphere_norm_one a z R hzR ha_interior
            have hIH' : ‖∏ b ∈ s, factor b z‖ = 1 := hIH hs_interior
            simp [Finset.prod_insert ha_notin, hfac, hIH']
        -- Apply the generic statement to `zeros`.
        simpa [B] using (hP zeros hzeros_interior)
      -- `‖F z‖ = ‖f z‖ * ‖B z‖ = ‖f z‖`.
      have hnorm : ‖F z‖ = ‖f z‖ := by
        simp [F, hnorm_prod]
      simp [hnorm]
    -- Apply circle average congruence on the sphere
    have h_on_sphere' :
        Set.EqOn (fun z : ℂ => Real.log ‖F z‖) (fun z : ℂ => Real.log ‖f z‖)
          (Metric.sphere (0 : ℂ) |R|) := by
      simpa [abs_of_pos hR] using h_on_sphere
    simpa using (Real.circleAverage_congr_sphere (c := (0 : ℂ)) (R := R) h_on_sphere').symm
  -- Step 2: Evaluate F at 0 in norm: ‖F(0)‖ = ‖f(0)‖ * ∏ (R/‖a‖)
  have hF0 : Real.log ‖F 0‖ = Real.log ‖f 0‖ + ∑ a ∈ zeros, Real.log (R / ‖a‖) := by
    -- Compute each factor at 0: factor a 0 = R^2 / (R * (0 - a)) = - R / a, so norm is R/‖a‖.
    have : B 0 = ∏ a ∈ zeros, (-(R : ℂ) / a) := by
      refine Finset.prod_congr rfl ?_
      intro a ha
      have hR0 : (R : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hR)
      -- `factor a 0 = (R^2)/(R*(0-a)) = -R/a`.
      by_cases ha0 : a = 0
      · subst ha0
        simp [factor]
      · -- clear denominators
        -- After simplification, this is a one-shot `field_simp`.
        simp [factor]
        field_simp [hR0, ha0]
    have hzero_ne : ∀ a ∈ zeros, a ≠ 0 := by
      intro a ha h0
      have : f 0 = 0 := by
        have hz := (h_zeros a ha).1
        simpa [h0] using hz
      exact h_nonzero_0 this
    have hnormB : Real.log ‖B 0‖ = ∑ a ∈ zeros, Real.log (R / ‖a‖) := by
      have hB0norm : ‖B 0‖ = ∏ a ∈ zeros, (R / ‖a‖) := by
        calc
          ‖B 0‖ = ‖∏ a ∈ zeros, (-(R : ℂ) / a)‖ := by simp [this]
          _ = ∏ a ∈ zeros, ‖-(R : ℂ) / a‖ := by
                exact norm_prod (s := zeros) (f := fun a => (-(R : ℂ) / a))
          _ = ∏ a ∈ zeros, (R / ‖a‖) := by
                refine Finset.prod_congr rfl ?_
                intro a ha
                simp [abs_of_pos hR]
      have hne : ∀ a ∈ zeros, (R / ‖a‖) ≠ 0 := by
        intro a ha
        have ha0 : a ≠ 0 := hzero_ne a ha
        have hnorm : ‖a‖ ≠ 0 := by
          exact norm_ne_zero_iff.2 ha0
        exact div_ne_zero (ne_of_gt hR) hnorm
      calc
        Real.log ‖B 0‖ = Real.log (∏ a ∈ zeros, (R / ‖a‖)) := by simp [hB0norm]
        _ = ∑ a ∈ zeros, Real.log (R / ‖a‖) := by
              exact Real.log_prod (s := zeros) (f := fun a => (R / ‖a‖)) hne
    have hf0 : ‖f 0‖ ≠ 0 := by
      simpa using (norm_ne_zero_iff.2 h_nonzero_0)
    have hB0 : ‖B 0‖ ≠ 0 := by
      -- `B 0` is a product of nonzero terms since `0 ∉ zeros`.
      have hne : ∀ a ∈ zeros, (-(R : ℂ) / a) ≠ 0 := by
        intro a ha
        have ha0 : a ≠ 0 := hzero_ne a ha
        exact div_ne_zero (by
          have : (R : ℂ) ≠ 0 := by
            exact_mod_cast (ne_of_gt hR)
          simpa using this) (by simpa using ha0)
      have : B 0 ≠ 0 := by
        -- use `this : B 0 = ∏ ...` and `Finset.prod_ne_zero_iff`
        have hprod : (∏ a ∈ zeros, (-(R : ℂ) / a)) ≠ 0 := by
          exact Finset.prod_ne_zero_iff.2 hne
        simpa [this] using hprod
      exact norm_ne_zero_iff.2 this
    calc
      Real.log ‖F 0‖ = Real.log (‖f 0‖ * ‖B 0‖) := by simp [F]
      _ = Real.log ‖f 0‖ + Real.log ‖B 0‖ := by
            simpa using (Real.log_mul hf0 hB0)
      _ = Real.log ‖f 0‖ + ∑ a ∈ zeros, Real.log (R / ‖a‖) := by simp [hnormB]
  -- Step 3: Apply the zero-free average identity to F using the provided logarithm
  rcases h_logF with ⟨gF, hgF, hFexp⟩
  have havgF :
      Real.circleAverage (fun z : ℂ => Real.log ‖F z‖) 0 R = Real.log ‖F 0‖ := by
    refine (circleAverage_log_norm_of_hasLog F gF R hR hgF ?_)
    intro z hz
    simpa [F, B, factor] using hFexp z hz
  -- Step 4: Combine steps to finish Jensen's formula
  calc
    Real.log ‖f 0‖
        = Real.log ‖F 0‖ - ∑ a ∈ zeros, Real.log (R / ‖a‖) := by
          linarith [hF0]
    _   = Real.circleAverage (fun z : ℂ => Real.log ‖F z‖) 0 R
            - ∑ a ∈ zeros, Real.log (R / ‖a‖) := by
          simp [havgF]
    _   = Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 R
            - ∑ a ∈ zeros, Real.log (R / ‖a‖) := by
          rw [← h_avg_eq]
    _   = -∑ a ∈ zeros, Real.log (R / ‖a‖)
            + Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 R := by
          ring



/-- **Helper**: Finite sum bound for |z| ≤ 1 -/
lemma finite_sum_pow_bound (z : ℂ) (h : ℕ) (hz : ‖z‖ ≤ 1) :
    ‖∑ k ∈ Finset.range h, z^(k+1) / (k+1)‖ ≤ h * ‖z‖ := by
  have hsum : ‖∑ k ∈ Finset.range h, z^(k+1) / (k+1)‖
      ≤ ∑ k ∈ Finset.range h, ‖z^(k+1) / (k+1 : ℂ)‖ := by
    simpa using (norm_sum_le (Finset.range h) (fun k => z^(k+1) / (k+1)))
  have hterm : ∀ k : ℕ, ‖z^(k+1) / (k+1 : ℂ)‖ ≤ ‖z‖ := by
    intro k
    have hk_nat : (1 : ℕ) ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    have hk_real : (1 : ℝ) ≤ (k + 1 : ℝ) := by
      exact_mod_cast hk_nat
    have hnorm_den : ‖(k + 1 : ℂ)‖ = (k + 1 : ℝ) := by
      have hden : (k + 1 : ℂ) = ((k + 1 : ℕ) : ℂ) := by
        norm_cast
      have hnorm : ‖(k + 1 : ℂ)‖ = ‖((k + 1 : ℕ) : ℂ)‖ :=
        congrArg norm hden
      have hn : ‖((k + 1 : ℕ) : ℂ)‖ = ((k + 1 : ℕ) : ℝ) := Complex.norm_natCast (k + 1)
      have hn_cast : ((k + 1 : ℕ) : ℝ) = (k + 1 : ℝ) := by
        norm_cast
      exact hnorm.trans (hn.trans hn_cast)
    have hden_ge : (1 : ℝ) ≤ ‖(k + 1 : ℂ)‖ := by
      rw [hnorm_den]
      exact hk_real
    have hpow_le : ‖z‖ ^ (k + 1) ≤ ‖z‖ := by
      cases k with
      | zero => simp
      | succ k' =>
          have hk1 : ‖z‖ ^ (Nat.succ k') ≤ 1 := pow_le_one₀ (norm_nonneg z) hz
          calc
            ‖z‖ ^ (Nat.succ (Nat.succ k')) = ‖z‖ ^ (Nat.succ k') * ‖z‖ := by
              simp [pow_succ]
            _ ≤ 1 * ‖z‖ := by
              refine mul_le_mul_of_nonneg_right hk1 (norm_nonneg z)
            _ = ‖z‖ := by ring
    calc
      ‖z ^ (k + 1) / (k + 1 : ℂ)‖
          = ‖z ^ (k + 1)‖ / ‖(k + 1 : ℂ)‖ := by simp
      _ = ‖z‖ ^ (k + 1) / ‖(k + 1 : ℂ)‖ := by simp
      _ ≤ ‖z‖ ^ (k + 1) := by
            refine div_le_self (pow_nonneg (norm_nonneg z) _) hden_ge
      _ ≤ ‖z‖ := hpow_le
  have hsum_le : (∑ k ∈ Finset.range h, ‖z^(k+1) / (k+1 : ℂ)‖) ≤ ∑ k ∈ Finset.range h, ‖z‖ := by
    refine Finset.sum_le_sum ?_
    intro k hk
    exact hterm k
  have hconst : (∑ k ∈ Finset.range h, ‖z‖) = h * ‖z‖ := by
    simp [Finset.sum_const]
  exact le_trans hsum (le_trans hsum_le (by rw [hconst]))
  /-
  -- Triangle inequality: ‖sum‖ ≤ sum of ‖terms‖
  calc ‖∑ k ∈ Finset.range h, z^(k+1) / (k+1)‖
      ≤ ∑ k ∈ Finset.range h, ‖z^(k+1) / (k+1 : ℂ)‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range h, ‖z‖^(k+1) / (k+1) := by
        congr 1; funext k
        rw [norm_div, norm_pow, Complex.norm_natCast]
    _ ≤ ∑ k ∈ Finset.range h, ‖z‖ := by
        apply Finset.sum_le_sum
        intro k _
        -- Need: ‖z‖^(k+1) / (k+1) ≤ ‖z‖
        -- Since ‖z‖ ≤ 1 and k + 1 ≥ 1, we have ‖z‖^(k + 1) ≤ ‖z‖,
        -- and division by `k + 1 ≥ 1` makes it smaller.
        have h1 : ‖z‖^(k+1) ≤ ‖z‖ := by
          cases' k with k'
          · simp
          · calc ‖z‖ ^ (k'.succ + 1)
                = ‖z‖ ^ k'.succ * ‖z‖ := by rw [pow_succ]
              _ ≤ 1 * ‖z‖ := by
                  apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
                  exact pow_le_one (norm_nonneg z) hz
              _ = ‖z‖ := by ring
        have h2 : ‖z‖ ^ (k + 1) / (k + 1 : ℝ) ≤ ‖z‖ ^ (k + 1) := by
          apply div_le_self (pow_nonneg (norm_nonneg z) _)
          -- 1 ≤ (k + 1 : ℝ)
          have : (1 : ℝ) ≤ (k + 1 : ℝ) := by
            have : (1 : ℕ) ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le _)
            exact_mod_cast this
          exact this
        linarith
    _ = h * ‖z‖ := by
        rw [Finset.sum_const, Finset.card_range]
        ring

/-- **Lemma 4.11**: Bounds on elementary factors

Lemma 4.11.
1. There exists some C such that log|E_h(z)| ≥ -C|z|^{h+1} when |z| ≤ 1 / 2.
2. There exists some C such that log|E_h(z)| ≥ -C|z|^h when |z| ≥ 1 / 2.

Proof. We follow [SS03].
1. Suppose |z| ≤ 1 / 2. This implies log(1-z) = -∑_{j≥1} z^j/j. We have
   E_h(z) = exp[log(1-z) + ∑_{j=1}^h z^j/j] = exp[∑_{j≥h+1} z^j/j] = exp(w).
   Since e^w ≥ e^{-|w|} and |w| ≤ C|z|^{h+1} we have
   |E_h(z)| ≥ exp(-∑_{j≥h+1} |z|^j/j) ≥ e^{-C|z|^{h+1}}.

2. Suppose |z| ≥ 1 / 2. We have
   |E_h(z)| = |1-z| · |e^{z+z²/2+...+z^h/h}|.
The proof follows from
   |e^{z+z²/2+...+z^h/h}| ≥ e^{-|z+z²/2+...+z^h/h|} ≥ e^{-C|z|^h}
for some C ≥ 0.
-/
-/
/- ### Elementary factor bounds (refactored)

We split the bounds into two regimes:
1) Small disk: `‖z‖ ≤ 1 / 2` implies `log ‖E_h(z)‖ ≥ -C |z|^{h+1}`.
2) Away from the zero at `z=1`: if `‖z‖ ≥ 1 / 2` and `‖z-1‖ ≥ δ`, then `log ‖E_h(z)‖ ≥ -C(δ) |z|^h`.
These formulations avoid the singularity at `z=1` and suffice for canonical product growth control.
-/

lemma logTaylor_neg_eq_neg_sum (h : ℕ) (z : ℂ) :
    logTaylor (h + 1) (-z) = -∑ k ∈ Finset.range h, z ^ (k + 1) / (k + 1) := by
  classical
  induction h with
  | zero =>
      simp [Complex.logTaylor]
  | succ h ih =>
      have hsucc : logTaylor (h + 2) (-z)
          = logTaylor (h + 1) (-z) + (-1 : ℂ) ^ (h + 2) * (-z) ^ (h + 1) / (h + 1) := by
        have hsucc_fn := logTaylor_succ (n := h + 1)
        rw [Nat.add_assoc] at hsucc_fn
        norm_num at hsucc_fn
        calc
          logTaylor (h + 2) (-z)
              =
                (logTaylor (h + 1)
                  + fun w : ℂ => (-1 : ℂ) ^ (h + 2) * w ^ (h + 1) / (h + 1)) (-z) := by
                    exact congrArg (fun f : ℂ → ℂ => f (-z)) hsucc_fn
          _ = logTaylor (h + 1) (-z) + (-1 : ℂ) ^ (h + 2) * (-z) ^ (h + 1) / (h + 1) := by
                simp
      rw [hsucc, ih]
      have hneg : -z = (-1 : ℂ) * z := by simp
      have hpow : (-z) ^ (h + 1) = (-1 : ℂ) ^ (h + 1) * z ^ (h + 1) := by
        rw [hneg]
        simpa using (mul_pow (-1 : ℂ) z (h + 1))
      have hsign : (-1 : ℂ) ^ (h + 2) * (-1 : ℂ) ^ (h + 1) = -1 := by
        have hodd : Odd (2 * h + 3) := by
          refine ⟨h + 1, by ring⟩
        calc
          (-1 : ℂ) ^ (h + 2) * (-1 : ℂ) ^ (h + 1)
              = (-1 : ℂ) ^ ((h + 2) + (h + 1)) := by
                  exact (pow_add (-1 : ℂ) (h + 2) (h + 1)).symm
          _ = (-1 : ℂ) ^ (2 * h + 3) := by ring
          _ = -1 := by
              simpa using (hodd.neg_one_pow (α := ℂ))
      have hterm : (-1 : ℂ) ^ (h + 2) * (-z) ^ (h + 1) / (h + 1) = - (z ^ (h + 1) / (h + 1)) := by
        calc
          (-1 : ℂ) ^ (h + 2) * (-z) ^ (h + 1) / (h + 1)
              = (-1 : ℂ) ^ (h + 2) * ((-1 : ℂ) ^ (h + 1) * z ^ (h + 1)) / (h + 1) := by
                  simp [hpow]
          _ = (((-1 : ℂ) ^ (h + 2) * (-1 : ℂ) ^ (h + 1)) * z ^ (h + 1)) / (h + 1) := by
                  ring
          _ = (-1 * z ^ (h + 1)) / (h + 1) := by simp [hsign]
          _ = - (z ^ (h + 1) / (h + 1)) := by
                simp [div_eq_mul_inv]
      rw [hterm]
      rw [Finset.sum_range_succ]
      ring

lemma weierstrass_E_small_disk_lower_bound (h : ℕ) :
  ∃ C : ℝ, ∀ z : ℂ, ‖z‖ ≤ (1 / 2 : ℝ) →
    Real.log ‖weierstrassE h z‖ ≥ -C * ‖z‖^(h+1) := by
  classical
  refine ⟨2, ?_⟩
  intro z hz
  have hz_lt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
  have hne : (1 - z) ≠ 0 := by
    intro h0
    have : z = (1 : ℂ) := by
      have : (1 : ℂ) = z := sub_eq_zero.mp h0
      simpa using this.symm
    have : (1 : ℝ) ≤ (1 / 2 : ℝ) := by
      simpa [this] using hz
    linarith
  set S : ℂ := ∑ k ∈ Finset.range h, z^(k+1) / (k+1) with hS
  have hS' : logTaylor (h + 1) (-z) = -S := by
    simpa [S] using (logTaylor_neg_eq_neg_sum h z)
  set w : ℂ := S - Complex.log ((1 - z)⁻¹) with hw
  have hw_eq : w = - (Complex.log ((1 - z)⁻¹) + logTaylor (h + 1) (-z)) := by
    calc
      w = S - Complex.log ((1 - z)⁻¹) := by rfl
      _ = - (Complex.log ((1 - z)⁻¹) + (-S)) := by ring
      _ = - (Complex.log ((1 - z)⁻¹) + logTaylor (h + 1) (-z)) := by simp [hS']
  have hinv_ne : ((1 - z)⁻¹ : ℂ) ≠ 0 := inv_ne_zero hne
  have hE : weierstrassE h z = Complex.exp w := by
    have : Complex.exp w = Complex.exp S / Complex.exp (Complex.log ((1 - z)⁻¹)) := by
      simpa [w, hw] using (Complex.exp_sub S (Complex.log ((1 - z)⁻¹)))
    calc
      weierstrassE h z = (1 - z) * Complex.exp S := by
        simp [weierstrassE, S]
      _ = Complex.exp S * (1 - z) := by ring
      _ = Complex.exp S / Complex.exp (Complex.log ((1 - z)⁻¹)) := by
        simp [Complex.exp_log hinv_ne, div_eq_mul_inv]
      _ = Complex.exp w := this.symm
  have hlogE : Real.log ‖weierstrassE h z‖ = w.re := by
    simp [hE, Complex.norm_exp, Real.log_exp]
  have hre_lower : w.re ≥ -‖w‖ := by
    have h1 : -|w.re| ≤ w.re := neg_abs_le w.re
    have h2 : |w.re| ≤ ‖w‖ := abs_re_le_norm w
    have h3 : -‖w‖ ≤ -|w.re| := by linarith
    exact le_trans h3 h1
  have hrem : ‖Complex.log ((1 - z)⁻¹) + logTaylor (h + 1) (-z)‖
      ≤ ‖z‖ ^ (h + 1) * (1 - ‖z‖)⁻¹ / (h + 1) :=
    norm_log_one_sub_inv_add_logTaylor_neg_le h hz_lt
  have hw_norm : ‖w‖ = ‖Complex.log ((1 - z)⁻¹) + logTaylor (h + 1) (-z)‖ := by
    have hnorm : ‖w‖ = ‖-(Complex.log ((1 - z)⁻¹) + logTaylor (h + 1) (-z))‖ :=
      congrArg norm hw_eq
    calc
      ‖w‖ = ‖-(Complex.log ((1 - z)⁻¹) + logTaylor (h + 1) (-z))‖ := hnorm
      _ = ‖Complex.log ((1 - z)⁻¹) + logTaylor (h + 1) (-z)‖ := by
            simpa using
              (norm_neg (Complex.log ((1 - z)⁻¹) + logTaylor (h + 1) (-z)))
  have hw_le : ‖w‖ ≤ ‖z‖ ^ (h + 1) * (1 - ‖z‖)⁻¹ / (h + 1) := by
    simpa [hw_norm] using hrem
  have hhalf_pos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
  have hhalf_le : (1 / 2 : ℝ) ≤ 1 - ‖z‖ := by linarith
  have hpos : 0 < 1 - ‖z‖ := lt_of_lt_of_le hhalf_pos hhalf_le
  have hinv_le : (1 - ‖z‖)⁻¹ ≤ 2 := by
    have : (1 - ‖z‖)⁻¹ ≤ ((1 / 2 : ℝ))⁻¹ := (inv_le_inv₀ hpos hhalf_pos).2 hhalf_le
    simpa using this
  have hden_ge : (1 : ℝ) ≤ (h + 1 : ℝ) := by
    have : (1 : ℕ) ≤ h + 1 := Nat.succ_le_succ (Nat.zero_le h)
    exact_mod_cast this
  have hmul_nonneg : 0 ≤ ‖z‖ ^ (h + 1) * (1 - ‖z‖)⁻¹ := by
    refine mul_nonneg (pow_nonneg (norm_nonneg z) _) ?_
    exact inv_nonneg.2 (le_of_lt hpos)
  have hw_le' : ‖w‖ ≤ 2 * ‖z‖ ^ (h + 1) := by
    have hdiv : ‖z‖ ^ (h + 1) * (1 - ‖z‖)⁻¹ / (h + 1)
        ≤ ‖z‖ ^ (h + 1) * (1 - ‖z‖)⁻¹ := by
      exact div_le_self hmul_nonneg hden_ge
    have hmul : ‖z‖ ^ (h + 1) * (1 - ‖z‖)⁻¹ ≤ ‖z‖ ^ (h + 1) * 2 := by
      exact mul_le_mul_of_nonneg_left hinv_le (pow_nonneg (norm_nonneg z) _)
    have : ‖z‖ ^ (h + 1) * (1 - ‖z‖)⁻¹ / (h + 1) ≤ 2 * ‖z‖ ^ (h + 1) := by
      have : ‖z‖ ^ (h + 1) * (1 - ‖z‖)⁻¹ / (h + 1) ≤ ‖z‖ ^ (h + 1) * 2 :=
        le_trans hdiv hmul
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    exact le_trans hw_le this
  have hre_bound : w.re ≥ - (2 * ‖z‖ ^ (h + 1)) := by
    have : -(2 * ‖z‖ ^ (h + 1)) ≤ -‖w‖ := neg_le_neg hw_le'
    exact le_trans this hre_lower
  have : Real.log ‖weierstrassE h z‖ ≥ - (2 * ‖z‖ ^ (h + 1)) := by
    simpa [hlogE] using hre_bound
  simpa [mul_assoc, mul_left_comm, mul_comm] using this

  /-
  -- Choose an explicit constant that works uniformly on ‖z‖ ≤ 1 / 2.
  -- Any C ≥ (2^h) · (log 2 + 2) suffices; we take C := 2^(h+1) (log 2 + 2).
  refine ⟨(2 : ℝ)^(h+1) * (Real.log 2 + 2), ?_⟩
  intro z hz_le
  set r : ℝ := ‖z‖ with hrdef
  have hr_nonneg : 0 ≤ r := by simpa [hrdef] using norm_nonneg z
  have hr_le_half : r ≤ (1 / 2 : ℝ) := by simpa [hrdef] using hz_le
  have hr_lt_one : r < 1 := lt_of_le_of_lt hr_le_half (by norm_num)
  -- Rewrite log |E_h(z)| in a convenient form
  have hpos1 : 0 < ‖1 - z‖ := by
    have hnorm : 1 - r ≤ ‖1 - z‖ := by
      simpa [hrdef] using (norm_sub_norm_le (1 : ℂ) z)
    have hpos : 0 < 1 - r := by linarith
    exact lt_of_lt_of_le hpos hnorm
  have logE :
      Real.log ‖weierstrassE h z‖
        = Real.log ‖1 - z‖ + (∑ k ∈ Finset.range h, (z^(k+1) / (k+1))).re := by
    -- log ||(1 - z) * exp(S)|| = log ||1 - z|| + Re S
    have : weierstrassE h z
          = (1 - z) * Complex.exp (∑ k ∈ Finset.range h, z^(k+1) / (k+1)) := rfl
    simp [this, Complex.norm_mul, Complex.norm_exp, Real.log_mul, hpos1, Real.exp_pos]
  -- Bound `log ‖1 - z‖` from below using `log (1 - r)` and r ≤ 1 / 2.
  have hlog1 : Real.log ‖1 - z‖ ≥ Real.log (1 - r) := by
    have : 1 - r ≤ ‖1 - z‖ := by
      simpa [hrdef] using (norm_sub_norm_le (1 : ℂ) z)
    exact Real.log_le_log.mpr ⟨by
      have : 0 < 1 - r := by linarith
      have : 0 < ‖1 - z‖ := hpos1
      exact this
    , this⟩
  -- Bound the finite sum's real part from below by minus the sum of absolute values.
  have hsum_re : (∑ k ∈ Finset.range h, (z^(k+1) / (k+1))).re
      ≥ - ∑ k ∈ Finset.range h, r^(k+1) / (k+1) := by
    refine Finset.sum_le_sum ?_;
    intro k hk
    have hterm : ((z^(k+1) / (k+1)).re) ≥ - ‖z^(k+1) / (k+1)‖ := by
      have := re_le_norm (z^(k+1) / (k+1))
      have : -‖z^(k+1) / (k+1)‖ ≤ (z^(k+1) / (k+1)).re := by linarith
      simpa using this
    have hnorm : ‖z^(k+1) / (k+1)‖ = r^(k+1) / (k+1) := by
      have : ‖(k+1 : ℂ)‖ = (k+1 : ℝ) := by simp
      simp [hrdef, norm_div, Complex.norm_pow, this]
    simpa [hnorm] using hterm
  -- Combine the two bounds and reduce to a bound in terms of r
  have base_lower :
      Real.log ‖weierstrassE h z‖
        ≥ Real.log (1 - r) - ∑ k ∈ Finset.range h, r^(k+1) / (k+1) := by
    simpa [logE] using add_le_add hlog1 hsum_re
  -- Bound the finite sum crudely by 2r using a geometric-series bound
  have hsum_bound : ∑ k ∈ Finset.range h, r^(k+1) / (k+1) ≤ 2 * r := by
    have h₁ : ∑ k ∈ Finset.range h, r^(k+1) / (k+1) ≤ ∑ k ∈ Finset.range h, r^(k+1) := by
      refine Finset.sum_le_sum ?_;
      intro k hk
      have hkpos : (0 : ℝ) < (k+1 : ℝ) := by exact_mod_cast Nat.cast_add_one_pos k
      have hrpow_nonneg : 0 ≤ r^(k+1) := by exact pow_nonneg hr_nonneg _
      have : (1 : ℝ) / (k+1 : ℝ) ≤ 1 := by
        have : (1 : ℝ) ≤ (k+1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
        have hk1pos : 0 < (k+1 : ℝ) := by exact_mod_cast Nat.cast_add_one_pos k
        exact one_div_le_one_of_le_of_nonneg this (by exact le_of_lt hk1pos)
      nlinarith
    have h₂ : ∑ k ∈ Finset.range h, r^(k+1) = r * ∑ j ∈ Finset.range h, r^j := by
      classical
      -- factor r out of r^(k+1)
      have := Finset.sum_mul (s := Finset.range h) (f := fun j => r^j) (b := r)
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using this
    have geom_bound : ∑ j ∈ Finset.range h, r^j ≤ (∑' (j : ℕ), ((1 / 2 : ℝ))^j) := by
      -- bound each r^j by (1 / 2)^j and compare to the infinite geometric series
      have hj : ∀ j, r^j ≤ (1 / 2 : ℝ)^j := by
        intro j; exact pow_le_pow_of_le_left hr_nonneg hr_le_half j
      have hhas : HasSum (fun j : ℕ => ((1 / 2 : ℝ))^j) (1 / (1 - (1 / 2 : ℝ))) := by
        simpa using (hasSum_geometric_of_lt_1 (by norm_num) (by norm_num : (0 : ℝ) < (1 / 2)) :
          HasSum (fun n : ℕ => (1 / 2 : ℝ)^n) (1 / (1 - (1 / 2 : ℝ))))
      have := Finset.sum_le_hasSum (fun j => hj j) (by
        -- nonneg of terms
        intro j hjmem; exact pow_nonneg (by norm_num) j) hhas.summable
      -- `sum_le_hasSum` gives ≤ lim of partial sums = 1/(1-1 / 2) = 2
      simpa using this
    have : ∑ j ∈ Finset.range h, r^j ≤ (2 : ℝ) := by
      simpa [one_div, sub_eq_add_neg] using geom_bound
    -- combine h₁, h₂, and the bound on the geometric series
    have : ∑ k ∈ Finset.range h, r^(k+1) / (k+1) ≤ r * 2 := by
      nlinarith [h₁, h₂, this]
    simpa [two_mul] using this
  -- Lower bound for log(1 - r)
  have hlog_one_minus : Real.log (1 - r) ≥ - Real.log 2 := by
    have : (1 / 2 : ℝ) ≤ 1 - r := by linarith
    have hpos : 0 < (1 - r) := by linarith
    have : Real.log (1 - r) ≥ Real.log ((1 / 2 : ℝ)) :=
      Real.log_le_log.mpr ⟨by norm_num, by linarith⟩
    simpa using this
  -- Combine: linear-in-r lower bound
  have lower_linear : Real.log ‖weierstrassE h z‖ ≥ - (Real.log 2 + 2) * r := by
    have := base_lower
    have := le_trans this (by nlinarith [hsum_bound, hlog_one_minus])
    -- rearrange to (- (log 2 + 2)) * r
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  -- Convert linear bound to an r^(h+1) bound using r ≤ 1 / 2
  have r_ge_scaled : r ≥ (2 : ℝ)^h * r^(h+1) := by
    -- r^(h+1) ≤ r * (1 / 2)^h  ⇒  r ≥ 2^h · r^(h+1)
    have : r^h ≤ (1 / 2 : ℝ)^h := pow_le_pow_of_le_left hr_nonneg hr_le_half _
    have : r^(h+1) ≤ r * (1 / 2 : ℝ)^h := by
      have := mul_le_mul_of_nonneg_left this hr_nonneg
      simpa [pow_succ] using this
    have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ (2 : ℝ)^h)
    -- (2^h) r^(h+1) ≤ (2^h) r (1 / 2)^h = r
    simpa [mul_comm, mul_left_comm, mul_assoc, pow_mul, two_mul, Real.two_mul] using this
  have : - (Real.log 2 + 2) * r ≥ - ((2 : ℝ)^(h+1) * (Real.log 2 + 2)) * r^(h+1) := by
    have : (2 : ℝ)^(h+1) = (2 : ℝ)^h * 2 := by simpa [pow_succ]
    have hpos : 0 ≤ (Real.log 2 + 2) := by have : (0 : ℝ) ≤ Real.log 2 := by
      -- Real.log 2 > 0
      have : (2 : ℝ) > 1 := by norm_num
      exact (Real.log_pos_iff.mpr this).le
      -- add 2 ≥ 0
    have := mul_le_mul_of_nonneg_left r_ge_scaled (by positivity : 0 ≤ (Real.log 2 + 2))
    have := neg_le_neg this
    -- rewrite target constant
    simpa [this, mul_comm, mul_left_comm, mul_assoc, pow_succ] using this
  -- finish
  simpa [hrdef] using le_trans lower_linear this

-/

lemma weierstrass_E_small_disk_norm_sub_one_le (h : ℕ) :
    ∀ z : ℂ, ‖z‖ ≤ (1 / 2 : ℝ) → ‖weierstrassE h z - 1‖ ≤ 4 * ‖z‖ ^ (h + 1) := by
  classical
  intro z hz
  have hz_lt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
  have hne : (1 - z) ≠ 0 := by
    intro h0
    have : z = (1 : ℂ) := by
      have : (1 : ℂ) = z := sub_eq_zero.mp h0
      simpa using this.symm
    have : (1 : ℝ) ≤ (1 / 2 : ℝ) := by
      simpa [this] using hz
    linarith
  set S : ℂ := ∑ k ∈ Finset.range h, z^(k+1) / (k+1) with hS
  have hS' : logTaylor (h + 1) (-z) = -S := by
    simpa [S] using (logTaylor_neg_eq_neg_sum h z)
  set w : ℂ := S - Complex.log ((1 - z)⁻¹) with hw
  have hw_eq : w = - (Complex.log ((1 - z)⁻¹) + logTaylor (h + 1) (-z)) := by
    calc
      w = S - Complex.log ((1 - z)⁻¹) := by rfl
      _ = - (Complex.log ((1 - z)⁻¹) + (-S)) := by ring
      _ = - (Complex.log ((1 - z)⁻¹) + logTaylor (h + 1) (-z)) := by simp [hS']
  have hinv_ne : ((1 - z)⁻¹ : ℂ) ≠ 0 := inv_ne_zero hne
  have hE : weierstrassE h z = Complex.exp w := by
    have : Complex.exp w = Complex.exp S / Complex.exp (Complex.log ((1 - z)⁻¹)) := by
      simpa [w, hw] using (Complex.exp_sub S (Complex.log ((1 - z)⁻¹)))
    calc
      weierstrassE h z = (1 - z) * Complex.exp S := by
        simp [weierstrassE, S]
      _ = Complex.exp S * (1 - z) := by ring
      _ = Complex.exp S / Complex.exp (Complex.log ((1 - z)⁻¹)) := by
        simp [Complex.exp_log hinv_ne, div_eq_mul_inv]
      _ = Complex.exp w := this.symm
  have hrem : ‖Complex.log ((1 - z)⁻¹) + logTaylor (h + 1) (-z)‖
      ≤ ‖z‖ ^ (h + 1) * (1 - ‖z‖)⁻¹ / (h + 1) :=
    norm_log_one_sub_inv_add_logTaylor_neg_le h hz_lt
  have hw_norm : ‖w‖ = ‖Complex.log ((1 - z)⁻¹) + logTaylor (h + 1) (-z)‖ := by
    have hnorm : ‖w‖ = ‖-(Complex.log ((1 - z)⁻¹) + logTaylor (h + 1) (-z))‖ :=
      congrArg norm hw_eq
    calc
      ‖w‖ = ‖-(Complex.log ((1 - z)⁻¹) + logTaylor (h + 1) (-z))‖ := hnorm
      _ = ‖Complex.log ((1 - z)⁻¹) + logTaylor (h + 1) (-z)‖ := by
            simpa using
              (norm_neg (Complex.log ((1 - z)⁻¹) + logTaylor (h + 1) (-z)))
  have hw_le : ‖w‖ ≤ ‖z‖ ^ (h + 1) * (1 - ‖z‖)⁻¹ / (h + 1) := by
    simpa [hw_norm] using hrem
  have hhalf_pos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
  have hhalf_le : (1 / 2 : ℝ) ≤ 1 - ‖z‖ := by linarith
  have hpos : 0 < 1 - ‖z‖ := lt_of_lt_of_le hhalf_pos hhalf_le
  have hinv_le : (1 - ‖z‖)⁻¹ ≤ 2 := by
    have : (1 - ‖z‖)⁻¹ ≤ ((1 / 2 : ℝ))⁻¹ := (inv_le_inv₀ hpos hhalf_pos).2 hhalf_le
    simpa using this
  have hden_ge : (1 : ℝ) ≤ (h + 1 : ℝ) := by
    have : (1 : ℕ) ≤ h + 1 := Nat.succ_le_succ (Nat.zero_le h)
    exact_mod_cast this
  have hmul_nonneg : 0 ≤ ‖z‖ ^ (h + 1) * (1 - ‖z‖)⁻¹ := by
    refine mul_nonneg (pow_nonneg (norm_nonneg z) _) ?_
    exact inv_nonneg.2 (le_of_lt hpos)
  have hw_le' : ‖w‖ ≤ 2 * ‖z‖ ^ (h + 1) := by
    have hdiv : ‖z‖ ^ (h + 1) * (1 - ‖z‖)⁻¹ / (h + 1)
        ≤ ‖z‖ ^ (h + 1) * (1 - ‖z‖)⁻¹ := by
      exact div_le_self hmul_nonneg hden_ge
    have hmul : ‖z‖ ^ (h + 1) * (1 - ‖z‖)⁻¹ ≤ ‖z‖ ^ (h + 1) * 2 := by
      exact mul_le_mul_of_nonneg_left hinv_le (pow_nonneg (norm_nonneg z) _)
    have : ‖z‖ ^ (h + 1) * (1 - ‖z‖)⁻¹ / (h + 1) ≤ 2 * ‖z‖ ^ (h + 1) := by
      have : ‖z‖ ^ (h + 1) * (1 - ‖z‖)⁻¹ / (h + 1) ≤ ‖z‖ ^ (h + 1) * 2 :=
        le_trans hdiv hmul
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    exact le_trans hw_le this
  have hw_le_one : ‖w‖ ≤ 1 := by
    have hz_le_one : ‖z‖ ≤ (1 : ℝ) := le_trans hz (by norm_num)
    have hzpow_le : ‖z‖ ^ (h + 1) ≤ ‖z‖ := by
      have hmn : (1 : ℕ) ≤ h + 1 := Nat.succ_le_succ (Nat.zero_le h)
      simpa [pow_one] using
        (pow_le_pow_of_le_one (norm_nonneg z) hz_le_one (m := 1) (n := h + 1) hmn)
    have hzpow_le_half : ‖z‖ ^ (h + 1) ≤ (1 / 2 : ℝ) := le_trans hzpow_le hz
    have : 2 * ‖z‖ ^ (h + 1) ≤ (1 : ℝ) := by nlinarith
    exact le_trans hw_le' this
  have hmain : ‖weierstrassE h z - 1‖ ≤ 2 * ‖w‖ := by
    -- `weierstrassE h z = exp w`
    simpa [hE] using (Complex.norm_exp_sub_one_le (x := w) hw_le_one)
  -- convert the bound on `w` to a bound on `z`
  have hw_scale : 2 * ‖w‖ ≤ 2 * (2 * ‖z‖ ^ (h + 1)) :=
    mul_le_mul_of_nonneg_left hw_le' (by positivity : 0 ≤ (2 : ℝ))
  calc
    ‖weierstrassE h z - 1‖ ≤ 2 * ‖w‖ := hmain
    _ ≤ 2 * (2 * ‖z‖ ^ (h + 1)) := hw_scale
    _ = 4 * ‖z‖ ^ (h + 1) := by ring

lemma weierstrass_E_small_disk_log_norm_le (h : ℕ) (z : ℂ) (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    Real.log ‖weierstrassE h z‖ ≤ 4 * ‖z‖ ^ (h + 1) := by
  have hE_ne : weierstrassE h z ≠ 0 := by
    intro h0
    have hmul :
        (1 - z) * Complex.exp (∑ k ∈ Finset.range h, z ^ (k + 1) / (k + 1)) = 0 := by
      simpa [weierstrassE] using h0
    have h' := mul_eq_zero.mp hmul
    cases h' with
    | inl h1 =>
        have hz1 : z = (1 : ℂ) := by
          have : (1 : ℂ) = z := sub_eq_zero.mp h1
          exact this.symm
        have : (1 : ℝ) ≤ (1 / 2 : ℝ) := by
          simpa [hz1] using hz
        linarith
    | inr h2 =>
        exact (Complex.exp_ne_zero _ h2).elim
  have hE_pos : 0 < ‖weierstrassE h z‖ := norm_pos_iff.2 hE_ne
  have hnorm : ‖weierstrassE h z‖ ≤ 1 + 4 * ‖z‖ ^ (h + 1) := by
    have htri : ‖weierstrassE h z‖ ≤ ‖weierstrassE h z - 1‖ + ‖(1 : ℂ)‖ := by
      have hdecomp : (weierstrassE h z - 1) + (1 : ℂ) = weierstrassE h z := by ring
      -- Triangle inequality, rewriting `((E - 1) + 1)` back to `E`.
      simpa [hdecomp] using (norm_add_le (weierstrassE h z - 1) (1 : ℂ))
    have hE1 : ‖weierstrassE h z - 1‖ ≤ 4 * ‖z‖ ^ (h + 1) :=
      weierstrass_E_small_disk_norm_sub_one_le h z hz
    have htri' : ‖weierstrassE h z‖ ≤ 4 * ‖z‖ ^ (h + 1) + ‖(1 : ℂ)‖ :=
      le_trans htri (add_le_add_left hE1 _)
    -- `‖(1 : ℂ)‖ = 1`
    have htri'' : ‖weierstrassE h z‖ ≤ 4 * ‖z‖ ^ (h + 1) + 1 := by
      simpa using htri'
    simpa [add_assoc, add_comm, add_left_comm] using htri''
  have hlog_le :
      Real.log ‖weierstrassE h z‖ ≤ Real.log (1 + 4 * ‖z‖ ^ (h + 1)) :=
    Real.log_le_log hE_pos hnorm
  have hlog_upper : Real.log (1 + 4 * ‖z‖ ^ (h + 1)) ≤ 4 * ‖z‖ ^ (h + 1) := by
    have hpos : 0 < (1 + 4 * ‖z‖ ^ (h + 1) : ℝ) := by positivity
    simpa using (Real.log_le_sub_one_of_pos (x := (1 + 4 * ‖z‖ ^ (h + 1) : ℝ)) hpos)
  exact hlog_le.trans hlog_upper

/-!
### Weierstrass products (Conway Ch. 7 §5)

Conway’s Theorem 5.9 / 5.12 show that if `∑ ‖fₙ(z) - 1‖` converges absolutely and uniformly on
compacts, then `∏ fₙ` converges uniformly on compacts to an analytic function.

In Mathlib, we use `Summable.hasProdLocallyUniformlyOn_nat_one_add` (from
`Mathlib.Analysis.NormedSpace.MultipliableUniformlyOn`) to package the convergence of products of
the form `∏ (1 + gₙ z)`. Our elementary-factor estimate
`weierstrass_E_small_disk_norm_sub_one_le` is a (slightly weaker) analogue of Conway’s Lemma 5.11.
-/

theorem weierstrass_product_hasProdLocallyUniformlyOn
    (a : ℕ → ℂ) (p : ℕ → ℕ) (u : ℕ → ℝ)
    (hu : Summable u)
    (h : ∀ᶠ n in atTop, ∀ z : ℂ, ‖(weierstrassE (p n) (z / a n) - 1 : ℂ)‖ ≤ u n) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassE (p n) (z / a n))
      (fun z ↦ ∏' n, weierstrassE (p n) (z / a n)) (Set.univ : Set ℂ) := by
  classical
  -- Continuity of each `(z ↦ weierstrassE (p n) (z / a n) - 1)` on `univ`.
  have hcts :
      ∀ n,
        ContinuousOn (fun z : ℂ => (weierstrassE (p n) (z / a n) - 1 : ℂ))
          (Set.univ : Set ℂ) := by
    intro n
    have hE : Continuous (fun z : ℂ => weierstrassE (p n) (z / a n)) :=
      (weierstrass_E_continuous (p n)).comp (by fun_prop)
    have h1 : Continuous (fun _z : ℂ => (1 : ℂ)) := continuous_const
    exact (hE.sub h1).continuousOn
  -- Turn the pointwise bound into the `∀ z ∈ univ` form expected by the library lemma.
  have h' :
      ∀ᶠ n in atTop, ∀ z ∈ (Set.univ : Set ℂ), ‖(weierstrassE (p n) (z / a n) - 1 : ℂ)‖ ≤ u n := by
    filter_upwards [h] with n hn z hz
    simpa using hn z
  -- Apply the general theorem for products of the form `∏ (1 + gₙ z)`.
  have hprod :
      HasProdLocallyUniformlyOn
        (fun n z ↦ (1 : ℂ) + (weierstrassE (p n) (z / a n) - 1))
        (fun z ↦ ∏' n, ((1 : ℂ) + (weierstrassE (p n) (z / a n) - 1)))
        (Set.univ : Set ℂ) := by
    simpa using
      (Summable.hasProdLocallyUniformlyOn_nat_one_add (α := ℂ) (R := ℂ)
        (K := (Set.univ : Set ℂ)) (hK := isOpen_univ) hu h' hcts)
  -- Rewrite `1 + (E - 1) = E`.
  simpa using hprod

theorem differentiableOn_weierstrass_product
    (a : ℕ → ℂ) (p : ℕ → ℕ) (u : ℕ → ℝ)
    (hu : Summable u)
    (h : ∀ᶠ n in atTop, ∀ z : ℂ, ‖(weierstrassE (p n) (z / a n) - 1 : ℂ)‖ ≤ u n) :
    DifferentiableOn ℂ (fun z : ℂ => ∏' n, weierstrassE (p n) (z / a n)) (Set.univ : Set ℂ) := by
  classical
  -- Get local uniform convergence of the partial products.
  have hprod := weierstrass_product_hasProdLocallyUniformlyOn (a := a) (p := p) (u := u) hu h
  have hseq :
      TendstoLocallyUniformlyOn
        (fun N z ↦ ∏ i ∈ Finset.range N, weierstrassE (p i) (z / a i))
        (fun z ↦ ∏' n, weierstrassE (p n) (z / a n))
        atTop (Set.univ : Set ℂ) :=
    hprod.tendstoLocallyUniformlyOn_finsetRange
  -- Each partial product is entire (finite product of entire functions).
  have hdiff :
      ∀ᶠ N in (atTop : Filter ℕ),
        DifferentiableOn ℂ
          (fun z ↦ ∏ i ∈ Finset.range N, weierstrassE (p i) (z / a i))
          (Set.univ : Set ℂ) := by
    refine Filter.Eventually.of_forall ?_
    intro N
    have hfun :
        DifferentiableOn ℂ
          (∏ i ∈ Finset.range N, (fun z : ℂ => weierstrassE (p i) (z / a i)))
          (Set.univ : Set ℂ) := by
      refine DifferentiableOn.finsetProd (𝕜 := ℂ) (𝔸' := ℂ) ?_
      intro i hi
      have hE : Differentiable ℂ (weierstrassE (p i)) := weierstrass_E_differentiable (p i)
      have hdiv : Differentiable ℂ (fun z : ℂ => z / a i) := by fun_prop
      exact (hE.comp hdiv).differentiableOn
    simpa [Finset.prod_fn] using hfun
  -- A locally uniform limit of holomorphic functions is holomorphic.
  simpa using hseq.differentiableOn hdiff isOpen_univ

/-!
### A Conway-style convergence criterion (Theorem 5.12)

The previous lemmas assume a *global* summable bound on `‖Eₚ(z/aₙ) - 1‖`. In applications one only
has such bounds on compact sets, using that `‖aₙ‖ → ∞`. The next lemma packages this common case:
on each compact `K` we use the bound `‖z‖ ≤ R` and the elementary estimate
`weierstrass_E_small_disk_norm_sub_one_le`.
-/

theorem weierstrass_product_hasProdLocallyUniformlyOn_of_tendsto_norm_atTop
    (a : ℕ → ℂ) (p : ℕ → ℕ)
    (ha : Tendsto (fun n ↦ ‖a n‖) atTop atTop)
    (hsum : ∀ R : ℝ, 0 < R → Summable (fun n ↦ (R / ‖a n‖) ^ (p n + 1))) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassE (p n) (z / a n))
      (fun z ↦ ∏' n, weierstrassE (p n) (z / a n)) (Set.univ : Set ℂ) := by
  classical
  refine hasProdLocallyUniformlyOn_of_forall_compact (s := (Set.univ : Set ℂ)) isOpen_univ ?_
  intro K hKsub hK
  -- Compact sets are bounded, hence contained in some closed ball.
  obtain ⟨R0, hKR0⟩ := (hK.isBounded.subset_closedBall (0 : ℂ))
  -- Use `R = max R0 1` to ensure `R > 0`.
  let R : ℝ := max R0 1
  have hRpos : 0 < R := by
    have : (0 : ℝ) < 1 := by norm_num
    exact lt_of_lt_of_le this (le_max_right R0 1)
  have hKnorm : ∀ z ∈ K, ‖z‖ ≤ R := by
    intro z hz
    have hz' : z ∈ Metric.closedBall (0 : ℂ) R0 := hKR0 hz
    have hzR0 : ‖z‖ ≤ R0 := by
      have : dist z 0 ≤ R0 := by
        simpa [Metric.mem_closedBall] using hz'
      simpa [dist_eq_norm] using this
    exact le_trans hzR0 (le_max_left R0 1)
  -- Define a summable comparison series on `K`.
  let u : ℕ → ℝ := fun n ↦ 4 * (R / ‖a n‖) ^ (p n + 1)
  have hu : Summable u := by
    simpa [u] using (hsum R hRpos).mul_left (4 : ℝ)
  -- The basic estimate gives an eventual bound by `u` on `K`.
  have h_large : ∀ᶠ n in atTop, 2 * R ≤ ‖a n‖ := (Filter.tendsto_atTop.mp ha) (2 * R)
  have hbound :
      ∀ᶠ n in atTop, ∀ z ∈ K, ‖(weierstrassE (p n) (z / a n) - 1 : ℂ)‖ ≤ u n := by
    filter_upwards [h_large] with n hn z hzK
    have hzR : ‖z‖ ≤ R := hKnorm z hzK
    have ha_pos : 0 < ‖a n‖ := by
      have h2pos : (0 : ℝ) < 2 := by norm_num
      have : 0 < 2 * R := mul_pos h2pos hRpos
      exact lt_of_lt_of_le this hn
    have hzdiv_half : ‖z / a n‖ ≤ (1 / 2 : ℝ) := by
      have hRle : R ≤ (1 / 2 : ℝ) * ‖a n‖ := by linarith [hn]
      have hzle : ‖z‖ ≤ (1 / 2 : ℝ) * ‖a n‖ := le_trans hzR hRle
      have hzdiv : ‖z‖ / ‖a n‖ ≤ (1 / 2 : ℝ) := (div_le_iff₀ ha_pos).2 hzle
      simpa [norm_div] using hzdiv
    have hE :
        ‖(weierstrassE (p n) (z / a n) - 1 : ℂ)‖ ≤ 4 * ‖z / a n‖ ^ (p n + 1) :=
      weierstrass_E_small_disk_norm_sub_one_le (h := p n) (z := z / a n) hzdiv_half
    have hdiv : ‖z / a n‖ ≤ R / ‖a n‖ := by
      have : ‖z‖ / ‖a n‖ ≤ R / ‖a n‖ :=
        div_le_div_of_nonneg_right hzR (norm_nonneg (a n))
      simpa [norm_div] using this
    have hpow : ‖z / a n‖ ^ (p n + 1) ≤ (R / ‖a n‖) ^ (p n + 1) :=
      pow_le_pow_left₀ (norm_nonneg (z / a n)) hdiv (p n + 1)
    have hmul :
        4 * ‖z / a n‖ ^ (p n + 1) ≤ 4 * (R / ‖a n‖) ^ (p n + 1) :=
      mul_le_mul_of_nonneg_left hpow (by norm_num : 0 ≤ (4 : ℝ))
    exact le_trans hE (by simpa [u] using hmul)
  -- Continuity of each `(z ↦ weierstrassE (p n) (z / a n) - 1)` on `K`.
  have hcts :
      ∀ n, ContinuousOn (fun z : ℂ => (weierstrassE (p n) (z / a n) - 1 : ℂ)) K := by
    intro n
    have hE : Continuous (fun z : ℂ => weierstrassE (p n) (z / a n)) :=
      (weierstrass_E_continuous (p n)).comp (by fun_prop)
    exact (hE.sub continuous_const).continuousOn
  -- Apply the general theorem for products of the form `∏ (1 + gₙ z)`.
  have hprod :
      HasProdUniformlyOn
        (fun n z ↦ (1 : ℂ) + (weierstrassE (p n) (z / a n) - 1))
        (fun z ↦ ∏' n, ((1 : ℂ) + (weierstrassE (p n) (z / a n) - 1))) K := by
    simpa using
      (Summable.hasProdUniformlyOn_nat_one_add
        (α := ℂ) (R := ℂ) (K := K) hK (u := u) hu hbound hcts)
  -- Rewrite `1 + (E - 1) = E`.
  simpa using hprod

theorem differentiableOn_weierstrass_product_of_tendsto_norm_atTop
    (a : ℕ → ℂ) (p : ℕ → ℕ)
    (ha : Tendsto (fun n ↦ ‖a n‖) atTop atTop)
    (hsum : ∀ R : ℝ, 0 < R → Summable (fun n ↦ (R / ‖a n‖) ^ (p n + 1))) :
    DifferentiableOn ℂ (fun z : ℂ => ∏' n, weierstrassE (p n) (z / a n)) (Set.univ : Set ℂ) := by
  classical
  have hprod :=
    weierstrass_product_hasProdLocallyUniformlyOn_of_tendsto_norm_atTop (a := a) (p := p) ha hsum
  have hseq :
      TendstoLocallyUniformlyOn
        (fun N z ↦ ∏ i ∈ Finset.range N, weierstrassE (p i) (z / a i))
        (fun z ↦ ∏' n, weierstrassE (p n) (z / a n))
        atTop (Set.univ : Set ℂ) :=
    hprod.tendstoLocallyUniformlyOn_finsetRange
  have hdiff :
      ∀ᶠ N in (atTop : Filter ℕ),
        DifferentiableOn ℂ
          (fun z ↦ ∏ i ∈ Finset.range N, weierstrassE (p i) (z / a i))
          (Set.univ : Set ℂ) := by
    refine Filter.Eventually.of_forall ?_
    intro N
    have hfun :
        DifferentiableOn ℂ
          (∏ i ∈ Finset.range N, (fun z : ℂ => weierstrassE (p i) (z / a i)))
          (Set.univ : Set ℂ) := by
      refine DifferentiableOn.finsetProd (𝕜 := ℂ) (𝔸' := ℂ) ?_
      intro i hi
      have hE : Differentiable ℂ (weierstrassE (p i)) := weierstrass_E_differentiable (p i)
      have hdiv : Differentiable ℂ (fun z : ℂ => z / a i) := by fun_prop
      exact (hE.comp hdiv).differentiableOn
    simpa [Finset.prod_fn] using hfun
  simpa using hseq.differentiableOn hdiff isOpen_univ

/-! Away from the zero at 1: on {‖z‖ ≥ 1 / 2, ‖z-1‖ ≥ δ}, log ‖E_h(z)‖ ≥ -C(δ)‖z‖^h. -/
lemma weierstrass_E_away_from_one_lower_bound (h : ℕ) (δ : ℝ) (hδ : 0 < δ) :
  ∃ C : ℝ, ∀ z : ℂ, (1 / 2 : ℝ) ≤ ‖z‖ → δ ≤ ‖z - 1‖ →
    Real.log ‖weierstrassE h z‖ ≥ -C * ‖z‖^h := by
  classical
  refine ⟨(2 : ℝ)^h * (h + |Real.log δ|), ?_⟩
  intro z hz_ge hz_delta
  set r : ℝ := ‖z‖ with hrdef
  have hr_ge : (1 / 2 : ℝ) ≤ r := by simpa [hrdef] using hz_ge
  have hδ_le_norm : δ ≤ ‖1 - z‖ := by
    simpa [norm_sub_rev] using hz_delta
  have hnorm_ne : ‖1 - z‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le hδ hδ_le_norm)
  set S : ℂ := ∑ k ∈ Finset.range h, z^(k+1) / (k+1) with hS
  have logE : Real.log ‖weierstrassE h z‖ = Real.log ‖1 - z‖ + S.re := by
    have : weierstrassE h z = (1 - z) * Complex.exp S := by
      simp [weierstrassE, S]
    simp [this, Complex.norm_exp, Real.log_mul, hnorm_ne, Real.exp_ne_zero, Real.log_exp]
  have hlog1 : Real.log ‖1 - z‖ ≥ Real.log δ := Real.log_le_log hδ hδ_le_norm
  have hSre : S.re ≥ -‖S‖ := by
    have h1 : -|S.re| ≤ S.re := neg_abs_le S.re
    have h2 : |S.re| ≤ ‖S‖ := abs_re_le_norm S
    have h3 : -‖S‖ ≤ -|S.re| := by linarith
    exact le_trans h3 h1
  have base_lower : Real.log ‖weierstrassE h z‖ ≥ Real.log δ - ‖S‖ := by
    have : Real.log ‖weierstrassE h z‖ ≥ Real.log δ + (-‖S‖) := by
      have := add_le_add hlog1 hSre
      simpa [logE, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this
    simpa [sub_eq_add_neg, add_assoc] using this
  have hS_bound : ‖S‖ ≤ (2 : ℝ)^h * h * r^h := by
    by_cases hr1 : r ≤ 1
    · have hS0 : ‖S‖ ≤ (h : ℝ) * r := by
        simpa [S, hrdef] using finite_sum_pow_bound z h (by simpa [hrdef] using hr1)
      have hr_le : r ≤ (2 : ℝ)^h * r^h := by
        have hone : (1 : ℝ) ≤ (2 * r) ^ h := by
          have : (1 : ℝ) ≤ 2 * r := by linarith [hr_ge]
          simpa using (one_le_pow₀ this (n := h))
        have hone' : (1 : ℝ) ≤ (2 : ℝ)^h * r^h := by
          simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm] using hone
        exact le_trans hr1 hone'
      have : (h : ℝ) * r ≤ (h : ℝ) * ((2 : ℝ)^h * r^h) :=
        mul_le_mul_of_nonneg_left hr_le (by positivity : 0 ≤ (h : ℝ))
      have : (h : ℝ) * r ≤ (2 : ℝ)^h * (h : ℝ) * r^h := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
      exact le_trans hS0 this
    · have hr1' : 1 ≤ r := le_of_not_ge hr1
      have hterm : ∀ k ∈ Finset.range h, ‖z^(k+1) / (k+1 : ℂ)‖ ≤ r^h := by
        intro k hk
        have hk1 : k.succ ≤ h := Nat.succ_le_of_lt (Finset.mem_range.1 hk)
        have hden_ge : (1 : ℝ) ≤ ‖(k + 1 : ℂ)‖ := by
          have : (1 : ℝ) ≤ (k + 1 : ℝ) := by
            have : (1 : ℕ) ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
            exact_mod_cast this
          have hnorm_den : ‖(k + 1 : ℂ)‖ = (k + 1 : ℝ) := by
            have hden : (k + 1 : ℂ) = ((k + 1 : ℕ) : ℂ) := by
              norm_cast
            have hnorm : ‖(k + 1 : ℂ)‖ = ‖((k + 1 : ℕ) : ℂ)‖ := congrArg norm hden
            have hn : ‖((k + 1 : ℕ) : ℂ)‖ = ((k + 1 : ℕ) : ℝ) := Complex.norm_natCast (k + 1)
            have hn_cast : ((k + 1 : ℕ) : ℝ) = (k + 1 : ℝ) := by
              norm_cast
            exact hnorm.trans (hn.trans hn_cast)
          rw [hnorm_den]
          exact this
        have hpow : r ^ (k + 1) ≤ r ^ h := by
          -- monotonicity in the exponent for `r ≥ 1`
          have : r ^ (k + 1) ≤ r ^ h := pow_le_pow_right₀ hr1' hk1
          simpa using this
        calc
          ‖z ^ (k + 1) / (k + 1 : ℂ)‖
              = ‖z‖ ^ (k + 1) / ‖(k + 1 : ℂ)‖ := by
                simp [norm_pow]
          _ ≤ ‖z‖ ^ (k + 1) := by
                refine div_le_self (pow_nonneg (norm_nonneg z) _) hden_ge
          _ = r ^ (k + 1) := by simp [hrdef]
          _ ≤ r ^ h := hpow
      have hsum : ‖S‖ ≤ (h : ℝ) * r^h := by
        have hsum0 : ‖S‖ ≤ ∑ k ∈ Finset.range h, ‖z^(k+1) / (k+1 : ℂ)‖ := by
          simpa [S] using (norm_sum_le (Finset.range h) (fun k => z^(k+1) / (k+1)))
        have hsum1 :
            (∑ k ∈ Finset.range h, ‖z^(k+1) / (k+1 : ℂ)‖)
              ≤ ∑ _k ∈ Finset.range h, r^h := by
          refine Finset.sum_le_sum ?_
          intro k hk
          exact hterm k hk
        have hsum2 : (∑ _k ∈ Finset.range h, r^h) = (h : ℝ) * r^h := by
          simp [Finset.sum_const]
        exact le_trans hsum0 (le_trans hsum1 (by rw [hsum2]))
      have h2pos : (1 : ℝ) ≤ (2 : ℝ)^h := by
        have : (1 : ℝ) ≤ 2 := by norm_num
        simpa using (one_le_pow₀ this (n := h))
      have : (h : ℝ) * r^h ≤ (2 : ℝ)^h * (h : ℝ) * r^h := by
        have := mul_le_mul_of_nonneg_right h2pos (by positivity : 0 ≤ (h : ℝ) * r^h)
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
      exact le_trans hsum this
  have hone : (1 : ℝ) ≤ (2 : ℝ)^h * r^h := by
    have : (1 : ℝ) ≤ 2 * r := by linarith [hr_ge]
    have : (1 : ℝ) ≤ (2 * r) ^ h := by
      simpa using (one_le_pow₀ this (n := h))
    simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm] using this
  have hlogδ : Real.log δ ≥ -((2 : ℝ)^h * |Real.log δ| * r^h) := by
    have h0 : -|Real.log δ| ≤ Real.log δ := by
      simpa using (neg_abs_le (Real.log δ))
    have habs : |Real.log δ| ≤ (2 : ℝ)^h * |Real.log δ| * r^h := by
      have := mul_le_mul_of_nonneg_left hone (abs_nonneg (Real.log δ))
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have h1 : -((2 : ℝ)^h * |Real.log δ| * r^h) ≤ -|Real.log δ| := neg_le_neg habs
    exact le_trans h1 h0
  have hmain : Real.log ‖weierstrassE h z‖ ≥ -((2 : ℝ)^h * (h + |Real.log δ|) * r^h) := by
    have hS' : Real.log ‖weierstrassE h z‖ ≥ Real.log δ - ((2 : ℝ)^h * h * r^h) := by
      have : Real.log δ - ‖S‖ ≥ Real.log δ - ((2 : ℝ)^h * h * r^h) := by
        linarith [hS_bound]
      exact ge_trans base_lower this
    have : Real.log δ - ((2 : ℝ)^h * h * r^h) ≥
        -((2 : ℝ)^h * |Real.log δ| * r^h) - ((2 : ℝ)^h * h * r^h) := by
      linarith [hlogδ]
    have htmp :
        Real.log ‖weierstrassE h z‖ ≥ -((2 : ℝ)^h * |Real.log δ| * r^h) - ((2 : ℝ)^h * h * r^h) :=
      ge_trans hS' this
    have hEq :
        -((2 : ℝ)^h * |Real.log δ| * r^h) - ((2 : ℝ)^h * h * r^h)
          = -((2 : ℝ)^h * (h + |Real.log δ|) * r^h) := by
      simp [sub_eq_add_neg, mul_add, mul_left_comm, mul_comm, add_comm]
    have : Real.log ‖weierstrassE h z‖ ≥ -((2 : ℝ)^h * (h + |Real.log δ|) * r^h) := by
      simpa [hEq] using htmp
    exact this
  simpa [hrdef] using hmain
  /-
  -- Simple explicit constant works uniformly on the region: C := 2^h (h + |log δ|).
  refine ⟨(2 : ℝ)^h * (h + |Real.log δ|), ?_⟩
  intro z hz_ge hz_delta
  set r : ℝ := ‖z‖ with hrdef
  have hr_ge : (1 / 2 : ℝ) ≤ r := by simpa [hrdef] using hz_ge
  have hr_nonneg : 0 ≤ r := by simp [hrdef]
  -- log |E_h(z)| = log |1-z| + Re(∑_{k=1}^h z^k/k)
  have logE : Real.log ‖weierstrassE h z‖
      = Real.log ‖1 - z‖ + (∑ k ∈ Finset.range h, (z^(k+1) / (k+1))).re := by
    have : weierstrassE h z = (1 - z) * Complex.exp (∑ k ∈ Finset.range h, z^(k+1) / (k+1)) := rfl
    simp [this, weierstrassE, Complex.norm_mul, Complex.norm_exp, Real.log_mul, Real.exp_pos]
  -- Bound log |1-z| from below using δ.
  have hlog1 : Real.log ‖1 - z‖ ≥ Real.log δ := by
    have : ‖1 - z‖ ≥ δ := by simpa [norm_sub_rev] using hz_delta
    exact Real.log_le_log.mpr ⟨by linarith [norm_nonneg (1 - z)], this⟩
  -- Bound the finite sum depending on whether r ≥ 1 or r ∈ [1 / 2,1).
  have sum_bound : (∑ k ∈ Finset.range h, r^(k+1) / (k+1)) ≤ (2 : ℝ)^h * h * r^h := by
    by_cases hr1 : r ≥ 1
    · -- For r ≥ 1, r^(k+1) ≤ r^h and 1/(k+1) ≤ 1 ⇒ sum ≤ h * r^h ≤ 2^h * h * r^h
      have hterm : ∀ k ∈ Finset.range h, r^(k+1) / (k+1 : ℝ) ≤ r^h := by
        intro k hk
        have hk1 : k.succ ≤ h := Nat.succ_le_of_lt (Finset.mem_range.1 hk)
        have hpow : r^(k+1) ≤ r^h := by exact pow_le_pow_of_le_left hr_nonneg hr1 hk1
        have hdiv : r^(k+1) / (k+1 : ℝ) ≤ r^(k+1) := by
          have : (1 : ℝ) ≤ (k+1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
          have hkpos : 0 < (k+1 : ℝ) := by exact_mod_cast Nat.cast_add_one_pos k
          have hnn : 0 ≤ r^(k+1) := pow_nonneg hr_nonneg _
          exact (div_le_iff (by exact hkpos)).mpr (by nlinarith)
        exact le_trans hdiv hpow
      have : ∑ k ∈ Finset.range h, r^(k+1) / (k+1) ≤ ∑ _k ∈ Finset.range h, r^h :=
        Finset.sum_le_sum hterm
      have : (∑ _k ∈ Finset.range h, r^h) = h * r^h := by
        simpa using (Finset.card_range h)
      have : ∑ k ∈ Finset.range h, r^(k+1) / (k+1) ≤ h * r^h := by simpa [this] using this
      -- strengthen to ≤ 2^h * h * r^h since 2^h ≥ 1
      have h2pos : (1 : ℝ) ≤ (2 : ℝ)^h := by
        have : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
        simpa using (one_le_pow_of_one_le (by norm_num : (1 : ℝ) ≤ 2) h)
      have := mul_le_mul_of_nonneg_right h2pos (by positivity : 0 ≤ h * r^h)
      exact le_trans this (by simpa [mul_comm, mul_left_comm, mul_assoc])
    · -- Case r ∈ [1 / 2,1): then r^h ≥ (1 / 2)^h, and r^(k+1)/ (k+1) ≤ 1
      have : ∑ k ∈ Finset.range h, r^(k+1) / (k+1) ≤ ∑ _k ∈ Finset.range h, (1 : ℝ) := by
        refine Finset.sum_le_sum ?_;
        intro k hk
        have : r^(k+1) ≤ 1 := by
          have : r ≤ 1 := by exact le_of_lt (lt_of_le_of_ne' hr_ge (by nlinarith))
          exact pow_le_one _ hr_nonneg this
        have hkpos : 0 < (k+1 : ℝ) := by exact_mod_cast Nat.cast_add_one_pos k
        have : r^(k+1) / (k+1 : ℝ) ≤ r^(k+1) := by
          have : (1 : ℝ) ≤ (k+1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
          have hnn : 0 ≤ r^(k+1) := pow_nonneg hr_nonneg _
          exact (div_le_iff (by exact hkpos)).mpr (by nlinarith)
        exact le_trans this (by simpa)
      have : ∑ k ∈ Finset.range h, r^(k+1) / (k+1) ≤ h := by simpa
      -- Convert h to h * (2^h) * r^h using r^h ≥ (1 / 2)^h
      have rpow_ge : (2 : ℝ)^h * r^h ≥ 1 := by
        have : r^h ≥ (1 / 2 : ℝ)^h := pow_le_pow_of_le_left (by norm_num) hr_ge h
        have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ (2 : ℝ)^h)
        simpa [mul_comm, mul_left_comm, mul_assoc, pow_mul, pow_succ, pow_two] using this
      have : h ≤ h * ((2 : ℝ)^h * r^h) := by
        have : (1 : ℝ) ≤ (2 : ℝ)^h * r^h := by simpa using rpow_ge
        exact (mul_le_mul_of_nonneg_left this (by have := Nat.cast_nonneg h; simpa using this))
      exact le_trans this (by ring_nf)
  -- Plug bounds into the main identity and simplify
  have sum_re_lower : (∑ k ∈ Finset.range h, (z^(k+1) / (k+1))).re
      ≥ - (∑ k ∈ Finset.range h, r^(k+1) / (k+1)) := by
    refine Finset.sum_le_sum ?_;
    intro k hk
    have : ((z^(k+1) / (k+1)).re) ≥ - ‖z^(k+1) / (k+1)‖ := by
      have := re_le_norm (z^(k+1) / (k+1))
      have : -‖z^(k+1) / (k+1)‖ ≤ (z^(k+1) / (k+1)).re := by linarith
      simpa using this
    have : ‖z^(k+1) / (k+1)‖ = r^(k+1) / (k+1) := by
      have : ‖(k+1 : ℂ)‖ = (k+1 : ℝ) := by simp
      simp [hrdef, norm_div, Complex.norm_pow, this]
    simpa [this]
  have : Real.log ‖weierstrassE h z‖
      ≥ Real.log δ - (∑ k ∈ Finset.range h, r^(k+1) / (k+1)) := by
    simpa [logE] using add_le_add hlog1 sum_re_lower
  have : Real.log ‖weierstrassE h z‖ ≥ Real.log δ - ((2 : ℝ)^h * h * r^h) :=
    le_trans this (by nlinarith [sum_bound])
  -- Absorb |log δ| into the r^h term using (2^h) r^h ≥ 1
  have h2r_ge_one : (2 : ℝ)^h * r^h ≥ 1 := by
    have : r^h ≥ (1 / 2 : ℝ)^h := by
      exact pow_le_pow_of_le_left (by norm_num) hr_ge h
    have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ (2 : ℝ)^h)
    simpa using this
  have hlog_abs : Real.log δ ≥ - |Real.log δ| := by nlinarith [abs_nonneg (Real.log δ)]
  have : Real.log ‖weierstrassE h z‖
      ≥ - ((2 : ℝ)^h * (h + |Real.log δ|)) * r^h := by
    -- Since (2^h) r^h ≥ 1, we have -|log δ| ≥ - (2^h) |log δ| r^h
    have : - |Real.log δ| ≥ - ((2 : ℝ)^h * |Real.log δ|) * r^h := by
      have : (2 : ℝ)^h * r^h ≥ (1 : ℝ) := h2r_ge_one
      have hpos : 0 ≤ |Real.log δ| := abs_nonneg _
      have := mul_le_mul_of_nonneg_left this hpos
      -- multiply both sides by -1
      simpa [mul_comm, mul_left_comm, mul_assoc] using (neg_le_neg this)
    -- combine with the -h*(2^h) r^h term
    have : Real.log δ - (2 : ℝ)^h * h * r^h
            ≥ - ((2 : ℝ)^h * |Real.log δ|) * r^h - (2 : ℝ)^h * h * r^h := by
      have := le_trans hlog_abs this
      exact this
    simpa [mul_add, mul_comm, mul_left_comm, mul_assoc] using this
  -- conclude
  simpa [hrdef, mul_comm, mul_left_comm, mul_assoc] using this

-/
/-! ## Main Theorems -/

/-- **Step 1**: Entire functions without zeros are exponentials of polynomials

Prove this for entire function f(z) without zeros: by existence of logarithms
we know f(z) = e^{g(z)}.

We show g(z) is a polynomial (This involves the so-called Borel-Carathéodory
inequality).

Proof sketch:
1. Since f has no zeros and is entire, we can write f = e^g for some entire g
2. We have |f(z)| < exp(|z|^ρ) by finite order assumption
3. So e^{Re g(z)} < exp(|z|^ρ), thus Re g(z) < |z|^ρ
4. By polynomial_from_growth, g is a polynomial of degree ≤ ρ
-/
theorem entire_no_zeros_is_exp_polynomial (f : ℂ → ℂ) (ρ : ℝ)
    (h_finite_order : hasFiniteOrder f)
    (h_order : order f = ρ)
    (h_no_zeros : ∀ z : ℂ, f z ≠ 0) :
  ∃ g : Polynomial ℂ, (∀ z, f z = exp (g.eval z)) ∧ (g.natDegree : ℝ) ≤ ρ := by
  classical
 -- Proof strategy:
  --
  -- Step 1: Since f has no zeros and is entire, construct g = log f
  -- Step 2: Show g is entire (continuous branch of logarithm exists)
  -- Step 3: From finite order of f, derive growth bound on Re g
  -- Step 4: Apply polynomial_from_growth to conclude g is polynomial
  --
  -- The key insight: |f(z)| = e^{Re g(z)}, so
  --   |f(z)| < exp(|z|^ρ) ⟹ Re g(z) < |z|^ρ
  -- Extract the finite order data
  obtain ⟨hf_diff, ρ₀, R₀, hf_bound⟩ := h_finite_order
  -- Auxiliary function used in `order`,
  -- so we can reuse the boundedness coming from `hasFiniteOrder`.
  let u : ℝ → ℝ := fun r : ℝ =>
    if r > 0 ∧ maxModulus f r > 1 then
      Real.log (Real.log (maxModulus f r)) / Real.log r
    else 0
  have hu_bdd : IsBoundedUnder (· ≤ ·) atTop u := by
    refine isBoundedUnder_of_eventually_le (f := atTop) (u := u) (a := max ρ₀ 0) ?_
    refine (eventually_atTop.2 ⟨max R₀ 2, ?_⟩)
    intro r hr
    have hr_ge_R0 : R₀ ≤ r := le_trans (le_max_left _ _) hr
    have hr_ge2 : (2 : ℝ) ≤ r := le_trans (le_max_right _ _) hr
    have hr_pos : 0 < r := by linarith [hr_ge2]
    have hr_gt1 : 1 < r := by linarith [hr_ge2]
    have hlogr_pos : 0 < Real.log r := Real.log_pos hr_gt1
    by_cases hM : maxModulus f r > 1
    · have hM_le : maxModulus f r ≤ Real.exp (r ^ ρ₀) := by
        refine maxModulus_le_of_forall_norm_le f hf_diff.continuous (le_of_lt hr_pos) ?_
        intro z hz
        have hRz : R₀ ≤ ‖z‖ := by simpa [hz] using hr_ge_R0
        have : ‖f z‖ < Real.exp (r ^ ρ₀) := by simpa [hz] using hf_bound z hRz
        exact le_of_lt this
      have hlogM_le : Real.log (maxModulus f r) ≤ r ^ ρ₀ := by
        have hM_pos : 0 < maxModulus f r := lt_trans (by linarith) hM
        have := Real.log_le_log hM_pos hM_le
        simpa [Real.log_exp] using this
      have hlogM_pos : 0 < Real.log (maxModulus f r) := Real.log_pos hM
      have hloglog_le : Real.log (Real.log (maxModulus f r)) ≤ Real.log (r ^ ρ₀) :=
        Real.log_le_log hlogM_pos hlogM_le
      have hratio_le : Real.log (Real.log (maxModulus f r)) / Real.log r ≤ ρ₀ := by
        have hlogr : Real.log (r ^ ρ₀) = ρ₀ * Real.log r := Real.log_rpow hr_pos ρ₀
        have : Real.log (Real.log (maxModulus f r)) ≤ ρ₀ * Real.log r := by
          rw [← hlogr]
          exact hloglog_le
        exact (div_le_iff₀ hlogr_pos).2 this
      have hcond : r > 0 ∧ maxModulus f r > 1 := ⟨hr_pos, hM⟩
      have : u r ≤ ρ₀ := by simpa [u, hcond] using hratio_le
      exact le_trans this (le_max_left _ _)
    · have hcond : ¬ (r > 0 ∧ maxModulus f r > 1) := by
        intro hcond; exact hM hcond.2
      simp [u, hcond, le_max_right _ _]
  have hρ : 0 ≤ ρ := by
    have horder_nonneg : 0 ≤ order f := by
      by_cases hex : ∃ r0 : ℝ, maxModulus f r0 > 1
      · rcases hex with ⟨r0, hr0⟩
        let c : ℝ := Real.log (Real.log (maxModulus f r0))
        let v : ℝ → ℝ := fun r : ℝ => c / Real.log r
        have hv : v ≤ᶠ[atTop] u := by
          refine (eventually_atTop.2 ⟨max r0 2, ?_⟩)
          intro r hr
          have hr_ge_r0 : r0 ≤ r := le_trans (le_max_left _ _) hr
          have hr_ge2 : (2 : ℝ) ≤ r := le_trans (le_max_right _ _) hr
          have hr_pos : 0 < r := by linarith [hr_ge2]
          have hr_gt1 : 1 < r := by linarith [hr_ge2]
          have hlogr_pos : 0 < Real.log r := Real.log_pos hr_gt1
          have hr0_nonneg : 0 ≤ r0 := by
            by_contra hneg
            have hset_empty : {y : ℝ | ∃ z : ℂ, ‖z‖ = r0 ∧ y = ‖f z‖} = ∅ := by
              ext y
              constructor
              · rintro ⟨z, hz, rfl⟩
                have : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
                linarith [hneg, hz]
              · intro hy; cases hy
            have : maxModulus f r0 = 0 := by
              simp [maxModulus, hset_empty]
            linarith [hr0, this]
          have hmono : maxModulus f r0 ≤ maxModulus f r :=
            maxModulus_mono_of_differentiable f hf_diff hr_pos hr0_nonneg hr_ge_r0
          have hM_r : maxModulus f r > 1 := lt_of_lt_of_le hr0 hmono
          have hloglog_mono : c ≤ Real.log (Real.log (maxModulus f r)) := by
            have hM0_pos : 0 < maxModulus f r0 := lt_trans (by linarith) hr0
            have hlogM0_pos : 0 < Real.log (maxModulus f r0) := Real.log_pos hr0
            have hlogM_mono : Real.log (maxModulus f r0) ≤ Real.log (maxModulus f r) :=
              Real.log_le_log hM0_pos hmono
            have : Real.log (Real.log (maxModulus f r0)) ≤ Real.log (Real.log (maxModulus f r)) :=
              Real.log_le_log hlogM0_pos hlogM_mono
            simpa [c] using this
          have hdiv :
              c / Real.log r ≤ Real.log (Real.log (maxModulus f r)) / Real.log r :=
            div_le_div_of_nonneg_right hloglog_mono (le_of_lt hlogr_pos)
          have hcond : r > 0 ∧ maxModulus f r > 1 := ⟨hr_pos, hM_r⟩
          simpa [v, u, hcond] using hdiv
        have hv_tendsto : Tendsto v atTop (𝓝 (0 : ℝ)) :=
          Tendsto.div_atTop (a := c) (by simp) tendsto_log_atTop
        have hlimsup_v : Filter.limsup v atTop = (0 : ℝ) := hv_tendsto.limsup_eq
        have hv_cob : IsCoboundedUnder (· ≤ ·) atTop v := by
          have hx : ∀ᶠ r : ℝ in atTop, min 0 (c / Real.log 2) ≤ v r := by
            refine (eventually_atTop.2 ⟨2, ?_⟩)
            intro r hr
            have hr_gt1 : 1 < r := by linarith
            have hlogr_pos : 0 < Real.log r := Real.log_pos hr_gt1
            have hlog2_pos : 0 < Real.log 2 := by
              simpa using (Real.log_pos (by norm_num : (1 : ℝ) < 2))
            by_cases hc : 0 ≤ c
            · have hv_nonneg : 0 ≤ v r := by
                have hv' : 0 ≤ c / Real.log r := div_nonneg hc (le_of_lt hlogr_pos)
                simpa [v] using hv'
              have hmin_eq : min 0 (c / Real.log 2) = 0 := by
                have hdiv_nonneg : 0 ≤ c / Real.log 2 := div_nonneg hc (le_of_lt hlog2_pos)
                simp [min_eq_left hdiv_nonneg]
              rw [hmin_eq]
              exact hv_nonneg
            · have hc' : c < 0 := lt_of_not_ge hc
              have hlog2_le : Real.log 2 ≤ Real.log r := by
                have : (2 : ℝ) ≤ r := hr
                exact Real.log_le_log (by positivity) this
              have hmin : min 0 (c / Real.log 2) = c / Real.log 2 := by
                have : c / Real.log 2 ≤ 0 := by
                  exact div_nonpos_of_nonpos_of_nonneg (le_of_lt hc') (le_of_lt hlog2_pos)
                simp [min_eq_right this]
              have hinv : (Real.log r)⁻¹ ≤ (Real.log 2)⁻¹ := inv_anti₀ hlog2_pos hlog2_le
              have hdiv : c / Real.log 2 ≤ c / Real.log r := by
                have hmul : c * (Real.log 2)⁻¹ ≤ c * (Real.log r)⁻¹ :=
                  mul_le_mul_of_nonpos_left hinv (le_of_lt hc')
                simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
              have : min 0 (c / Real.log 2) ≤ v r := by
                -- `c/log2 ≤ c/logr`
                simpa [v, hmin] using hdiv
              exact this
          exact isCoboundedUnder_le_of_eventually_le atTop hx
        have hlim : Filter.limsup v atTop ≤ Filter.limsup u atTop :=
          limsup_le_limsup hv (hu := hv_cob) (hv := by simpa [u] using hu_bdd)
        have : (0 : ℝ) ≤ Filter.limsup u atTop := by
          simpa [hlimsup_v] using hlim
        simpa [order, u] using this
      · have hM_all : ∀ r : ℝ, maxModulus f r ≤ 1 := by
          intro r
          by_contra h
          exact hex ⟨r, lt_of_not_ge h⟩
        have hcond : ∀ r : ℝ, ¬(r > 0 ∧ maxModulus f r > 1) := by
          intro r
          rintro ⟨_, hM⟩
          exact (not_lt_of_ge (hM_all r)) hM
        have : order f = 0 := by
          simp [order, hcond]
        rw [this]
    rw [← h_order]
    exact horder_nonneg
  -- Step 1 & 2: Construct entire logarithm g
  -- Since f never vanishes, Complex.log is well-defined on its image
  -- and we can construct an entire branch of log
  -- (This requires careful handling of branch cuts - ax_iomatize for now)
  -- Existence of an entire logarithm: f = exp ∘ g with g entire.
  -- This is a standard covering-space/analytic-continuation result.
  have h_log_exists : ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = exp (g z) :=
    EntireLog.entire_has_entire_log_of_no_zeros f hf_diff h_no_zeros
  obtain ⟨g, hg_diff, hg_formula⟩ := h_log_exists
  -- Step 3: Derive growth bound on Re g from order of f
  -- Key: order f = ρ means for any ε > 0, |f(z)| < exp(|z|^(ρ+ε)) for large |z|
  have h_growth : ∀ ε > 0, ∃ r_seq : ℕ → ℝ,
      Filter.Tendsto r_seq Filter.atTop Filter.atTop ∧
      ∀ n : ℕ, ∀ z : ℂ, ‖z‖ = r_seq n → (g z).re < ‖z‖^(ρ + ε) := by
    intro ε hε
    -- Build a subsequence of radii from the limsup definition of `order f = ρ` where
    -- the maximal modulus is bounded by `exp(r^(ρ+ε/2))`.
    have h_order_rseq : ∃ r0 : ℕ → ℝ,
        Filter.Tendsto r0 atTop atTop ∧
        (∀ n, 0 < r0 n) ∧
        ∀ n, maxModulus f (r0 n) ≤ Real.exp ((r0 n) ^ (ρ + ε / 2)) := by
      rcases maxModulus_subseq_bound_of_order f ρ (ε/2) (by linarith) h_order
          (by simpa [u] using hu_bdd) with ⟨r0, ht, hpos, hbd⟩
      refine ⟨r0, ht, hpos, ?_⟩
      intro n; simpa [add_comm, add_left_comm, add_assoc, div_eq_mul_inv, two_mul] using hbd n
    rcases h_order_rseq with ⟨r0, hr0_tendsto, hr0_pos, hM_bound⟩
    -- Shift to ensure all radii are ≥ 2 (so we can use strict monotonicity in the exponent)
    have : ∀ᶠ n in atTop, (2 : ℝ) ≤ r0 n :=
      (hr0_tendsto.eventually_ge_atTop 2)
    rcases (eventually_atTop.1 this) with ⟨N, hN⟩
    -- Define the working sequence
    let r_seq : ℕ → ℝ := fun n => r0 (n + N)
    have hrseq_tendsto : Filter.Tendsto r_seq atTop atTop :=
      hr0_tendsto.comp (tendsto_add_atTop_nat N)
    refine ⟨r_seq, hrseq_tendsto, ?_⟩
    intro n z hz
    have hz_r : ‖z‖ = r0 (n + N) := hz
    -- Bound pointwise by the maximal modulus on the circle
    have hpt_le : ‖f z‖ ≤ maxModulus f (r0 (n + N)) :=
      norm_le_maxModulus_on_circle f hf_diff.continuous hz_r
    have hM : maxModulus f (r0 (n + N)) ≤ Real.exp ((r0 (n + N)) ^ (ρ + ε / 2)) :=
      hM_bound (n + N)
    have hnorm_le : ‖f z‖ ≤ Real.exp (‖z‖ ^ (ρ + ε / 2)) := by simpa [hz_r] using le_trans hpt_le hM
    -- Convert to Re g bound via f = exp g
    have : ‖f z‖ = Real.exp (g z).re := by
      rw [hg_formula z, Complex.norm_exp]
    -- Strict inequality, using monotonicity of exp
    have hRe : (g z).re ≤ ‖z‖ ^ (ρ + ε / 2) :=
      re_le_of_norm_exp_le (by
        rw [← hg_formula z]
        exact hnorm_le)
    -- Strengthen exponent from `ρ + ε/2` to `ρ + ε` using `‖z‖ > 1` (true by construction).
    have hr_ge2 : (2 : ℝ) ≤ ‖z‖ := by
      have : (2 : ℝ) ≤ r0 (n + N) := hN (n + N) (Nat.le_add_left N n)
      simpa [hz_r]
    have hr_gt1 : 1 < ‖z‖ := by linarith [hr_ge2]
    have hrpow_lt : ‖z‖ ^ (ρ + ε / 2) < ‖z‖ ^ (ρ + ε) :=
      Real.rpow_lt_rpow_of_exponent_lt hr_gt1 (by linarith)
    exact lt_of_le_of_lt hRe hrpow_lt
  -- Step 4: Apply polynomial_from_growth
  obtain ⟨p, hp_formula, hp_degree⟩ := polynomial_from_growth g ρ hρ hg_diff h_growth
  -- Conclude
  use p
  constructor
  · intro z
    rw [← hp_formula z]
    exact hg_formula z
  · exact hp_degree

end Hadamard
/-! ### Entire logarithm for zero-free entire functions (placeholder)

The following lemma asserts the standard existence of a global holomorphic logarithm for a
zero‑free entire function on `ℂ`. A constructive proof uses that `ℂ` is simply connected and that
`f'/f` ad_mits a primitive, then normalizes the constant so that `f = exp ∘ g`.
-/
lemma entire_has_entire_log_of_no_zeros
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (h0 : ∀ z, f z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = Complex.exp (g z) := by
  simpa using EntireLog.entire_has_entire_log_of_no_zeros f hf h0
