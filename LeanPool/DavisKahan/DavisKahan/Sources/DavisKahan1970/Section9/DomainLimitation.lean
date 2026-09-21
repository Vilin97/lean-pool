/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.WeinbergerAngle
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.DiagonalMultiplication
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Davis--Kahan 1970, Section 9: domain limitation example

The source displays a geometric trial sequence whose image under a diagonal
unbounded operator is the constant sequence, hence is not square summable.  It
then notes that an arbitrarily small modification repairs the domain issue.
Here the repair is made explicit by finite truncation.  The first group of
statements is sequence-level and avoids pretending that an undefined residual is
a vector of `ell^2`.

The file then carries the whole paragraph the source writes after (9.8):

* the operator itself, `diag(1, mu^-1, mu^-2, ...)` on its maximal domain, and
  the fact that it is self-adjoint there;
* the trial vector `e = (1, mu, mu^2, ...)`, which is *outside* the operator
  domain but inside the form domain;
* its Rayleigh quotient `alphaHat = e*(A+H)e / e*e = 1 + mu`;
* the angle `theta` between `e` and the first eigenvector, with `sin theta = mu`;
* Weinberger's estimate `sin^2 theta <= (1 + mu - alphaCheck_1)/(alphaCheck_2 -
  alphaCheck_1)` and its best-lower-bound form `sin theta <= mu / sqrt(1 - mu)`.

That is the contrast the paragraph exists to draw: every residual-based theorem
of the paper is silent here because the residual does not exist, while the
form/Rayleigh lower-bound method still gives a bound.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section9

/-- The geometric trial sequence. -/
def geometricTrialSequence (μ : ℝ) (n : ℕ) : ℝ := μ ^ n

/-- The diagonal multiplier used in the source example. -/
noncomputable def diagonalMultiplier (μ : ℝ) (n : ℕ) : ℝ := (μ ^ n)⁻¹

/-- The pointwise image of the geometric trial sequence. -/
noncomputable def geometricDiagonalImage (μ : ℝ) (n : ℕ) : ℝ :=
  diagonalMultiplier μ n * geometricTrialSequence μ n

/-- The diagonal multiplier exactly cancels the geometric trial sequence, so every entry of the
image is `1`.  This is why the partial energies grow like `N` and the raw sequence is outside the
domain. -/
lemma geometricDiagonalImage_eq_one {μ : ℝ} (hμ : μ ≠ 0) (n : ℕ) :
    geometricDiagonalImage μ n = 1 := by
  unfold geometricDiagonalImage diagonalMultiplier geometricTrialSequence
  exact inv_mul_cancel₀ (pow_ne_zero n hμ)

/-- Every length-`N` partial square energy of the raw image equals `N`; this is
the finite certificate of divergence used by the domain counterexample. -/
theorem geometricDiagonalImage_partial_energy
    {μ : ℝ} (hμ : μ ≠ 0) (N : ℕ) :
    ∑ n ∈ Finset.range N, geometricDiagonalImage μ n ^ 2 = N := by
  simp [geometricDiagonalImage_eq_one hμ]

/-- Finite truncation gives a concrete nearby sequence in the diagonal
operator's domain. -/
def truncatedTrialSequence (μ : ℝ) (N n : ℕ) : ℝ :=
  if n < N then μ ^ n else 0

/-- Image of the truncated trial sequence. -/
noncomputable def truncatedDiagonalImage (μ : ℝ) (N n : ℕ) : ℝ :=
  diagonalMultiplier μ n * truncatedTrialSequence μ N n

/-- Below the cut the truncation agrees with the raw sequence. -/
lemma truncatedTrialSequence_eq_geometric {μ : ℝ} {N n : ℕ} (hn : n < N) :
    truncatedTrialSequence μ N n = geometricTrialSequence μ n := by
  simp [truncatedTrialSequence, geometricTrialSequence, hn]

/-- Above the cut the truncation vanishes, which is what puts it in the domain. -/
lemma truncatedTrialSequence_eq_zero {μ : ℝ} {N n : ℕ} (hn : N ≤ n) :
    truncatedTrialSequence μ N n = 0 := by
  simp [truncatedTrialSequence, not_lt.mpr hn]

/-- Below the cut the truncated image is still `1`. -/
lemma truncatedDiagonalImage_eq_one
    {μ : ℝ} (hμ : μ ≠ 0) {N n : ℕ} (hn : n < N) :
    truncatedDiagonalImage μ N n = 1 := by
  simp [truncatedDiagonalImage, truncatedTrialSequence, diagonalMultiplier,
    hn, inv_mul_cancel₀ (pow_ne_zero n hμ)]

/-- Above the cut it vanishes, so the truncated image has finite energy `N` -- finite for each `N`,
unbounded in `N`, which is exactly the domain obstruction. -/
lemma truncatedDiagonalImage_eq_zero
    {μ : ℝ} {N n : ℕ} (hn : N ≤ n) :
    truncatedDiagonalImage μ N n = 0 := by
  simp [truncatedDiagonalImage, truncatedTrialSequence, not_lt.mpr hn]

/-- The corrected residual has exactly `N` units of square energy and finite
support. -/
theorem truncatedDiagonalImage_energy
    {μ : ℝ} (hμ : μ ≠ 0) (N : ℕ) :
    ∑ n ∈ Finset.range N, truncatedDiagonalImage μ N n ^ 2 = N := by
  -- the rewrite is conditional on `n < N`, so it has to happen under the
  -- membership hypothesis rather than in a bare `simp` set
  have hterm : ∀ n ∈ Finset.range N, truncatedDiagonalImage μ N n ^ 2 = 1 := by
    intro n hn
    rw [truncatedDiagonalImage_eq_one hμ (Finset.mem_range.mp hn), one_pow]
  rw [Finset.sum_congr rfl hterm]
  simp

/-- Outside the truncation range the corrected image vanishes. -/
theorem truncatedDiagonalImage_support
    (μ : ℝ) (N n : ℕ) (hn : N ≤ n) :
    truncatedDiagonalImage μ N n = 0 :=
  truncatedDiagonalImage_eq_zero hn

/-- Truncation changes only the geometric tail. -/
theorem geometricTrialSequence_sub_truncated
    (μ : ℝ) (N n : ℕ) :
    geometricTrialSequence μ n - truncatedTrialSequence μ N n =
      if n < N then 0 else μ ^ n := by
  by_cases hn : n < N
  · simp [geometricTrialSequence, truncatedTrialSequence, hn]
  · simp [geometricTrialSequence, truncatedTrialSequence, hn]

/-- On every fixed initial segment, sufficiently long truncations agree exactly
with the original trial sequence. -/
theorem truncation_eventually_agrees_on_prefix
    (μ : ℝ) (K N : ℕ) (hKN : K ≤ N) :
    ∀ n < K, truncatedTrialSequence μ N n = geometricTrialSequence μ n := by
  intro n hn
  exact truncatedTrialSequence_eq_geometric (lt_of_lt_of_le hn hKN)

/-! ## The example as an operator on `ℓ²`

The sequence lemmas above are the arithmetic of the source example.  This section
puts them where the source puts them: an honest unbounded diagonal operator on
`ℓ²(ℕ)`, its maximal domain, and a trial vector that is *in the space* and *in the
form domain* but *not in the operator domain*.

That is the whole point of the example.  A residual-based theorem needs `D x`,
which does not exist here; a form-based theorem needs `∑ dₙ |xₙ|²`, which is
finite.  So the two families of estimates are genuinely different in scope, and
the difference is not an artefact of how one states them. -/

open scoped ENNReal

/-- The ambient sequence space of the example. -/
abbrev DomainLimitationSpace : Type := lp (fun _ : ℕ => ℝ) 2

/-- **The maximal domain of the diagonal operator with multiplier `d`**: the
vectors whose scaled sequence is still square summable.

This is the reusable `TauCeti.LinearPMap.lpDiagonalDomain` at `𝕜 = ℝ`, `ι = ℕ`;
the paper-facing name is kept so the Section 9 statements read as the source
writes them. -/
noncomputable def diagonalDomain (d : ℕ → ℝ) : Submodule ℝ DomainLimitationSpace :=
  TauCeti.LinearPMap.lpDiagonalDomain d

/-- Membership in the diagonal operator's domain is square-summability of the
weighted coordinates. -/
theorem mem_diagonalDomain_iff (d : ℕ → ℝ) (x : DomainLimitationSpace) :
    x ∈ diagonalDomain d ↔ Memℓp (fun n => d n * (x : ℕ → ℝ) n) 2 :=
  TauCeti.LinearPMap.mem_lpDiagonalDomain_iff d x

/-- **The unbounded diagonal operator**, on its maximal domain.

This is the reusable `TauCeti.LinearPMap.lpDiagonal` at `𝕜 = ℝ`, `ι = ℕ`. -/
noncomputable def diagonalOperator (d : ℕ → ℝ) :
    DomainLimitationSpace →ₗ.[ℝ] DomainLimitationSpace :=
  TauCeti.LinearPMap.lpDiagonal d

/-- The operator's domain is the maximal domain, by construction. -/
@[simp]
theorem diagonalOperator_domain (d : ℕ → ℝ) :
    (diagonalOperator d).domain = diagonalDomain d := rfl

/-- The diagonal operator multiplies each coordinate by its weight. -/
@[simp]
theorem diagonalOperator_apply (d : ℕ → ℝ) (x : (diagonalOperator d).domain) (n : ℕ) :
    ((diagonalOperator d x : DomainLimitationSpace) : ℕ → ℝ) n
      = d n * ((x : DomainLimitationSpace) : ℕ → ℝ) n :=
  TauCeti.LinearPMap.lpDiagonal_apply d x n

/-- **The diagonal operator is self-adjoint on its maximal domain** whenever the
multiplier is real, which for `ℝ`-valued `d` is automatic.

This is what makes "the Rayleigh quotient of a trial vector is useful"
meaningful: without self-adjointness there is no spectral statement to compare
the quotient against.  It is the paper-facing instance of the reusable
`TauCeti.LinearPMap.lpDiagonal_isSelfAdjoint`. -/
theorem diagonalOperator_isSelfAdjoint (d : ℕ → ℝ) :
    IsSelfAdjoint (diagonalOperator d) :=
  TauCeti.LinearPMap.lpDiagonal_isSelfAdjoint d fun n => by simp

/-- Symmetry of the diagonal operator, the coordinatewise half of the previous
theorem. -/
theorem diagonalOperator_isSymmetric (d : ℕ → ℝ) :
    TauCeti.LinearPMap.IsSymmetric (diagonalOperator d) :=
  TauCeti.LinearPMap.lpDiagonal_isSymmetric d fun n => by simp

/-- The maximal domain is dense, so the adjoint of the diagonal operator is the
honest Hilbert-space adjoint rather than the junk value. -/
theorem dense_diagonalDomain (d : ℕ → ℝ) :
    Dense ((diagonalDomain d : Submodule ℝ DomainLimitationSpace) :
      Set DomainLimitationSpace) :=
  TauCeti.LinearPMap.dense_lpDiagonal_domain d

/-- The `ℓ²` membership criterion, with the exponent already evaluated. -/
theorem memℓp_two_of_summable_sq {f : ℕ → ℝ}
    (hf : Summable fun n => f n ^ 2) : Memℓp f 2 := by
  refine memℓp_gen ?_
  have h : (fun n => ‖f n‖ ^ ((2 : ℝ≥0∞).toReal)) = fun n => f n ^ 2 := by
    funext n
    rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) from by norm_num,
      Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
  rw [h]
  exact hf

/-- The converse reading of the same criterion. -/
theorem summable_sq_of_memℓp_two {f : ℕ → ℝ} (hf : Memℓp f 2) :
    Summable fun n => f n ^ 2 := by
  have h := (memℓp_gen_iff (p := 2) (f := f) (by norm_num)).1 hf
  have heq : (fun n => ‖f n‖ ^ ((2 : ℝ≥0∞).toReal)) = fun n => f n ^ 2 := by
    funext n
    rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) from by norm_num,
      Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
  rwa [heq] at h

/-- The geometric trial vector of the source example. -/
noncomputable def geometricTrial {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) :
    DomainLimitationSpace :=
  ⟨fun n => geometricTrialSequence μ n, by
    refine memℓp_two_of_summable_sq ?_
    have h : (fun n : ℕ => geometricTrialSequence μ n ^ 2) = fun n : ℕ => (μ ^ 2) ^ n := by
      funext n
      rw [geometricTrialSequence, ← pow_mul, ← pow_mul, mul_comm]
    rw [h]
    exact summable_geometric_of_lt_one (by positivity) (by nlinarith)⟩

/-- Coordinates of the geometric trial vector. -/
@[simp]
theorem geometricTrial_apply {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) (n : ℕ) :
    ((geometricTrial hμ0 hμ1 : DomainLimitationSpace) : ℕ → ℝ) n = μ ^ n := rfl

/-- **The trial vector is outside the operator domain.**  Its image is the
constant sequence `1`, whose squares are not summable. -/
theorem geometricTrial_notMem_diagonalDomain
    {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    geometricTrial hμ0.le hμ1 ∉ diagonalDomain (diagonalMultiplier μ) := by
  intro hmem
  rw [mem_diagonalDomain_iff] at hmem
  have himage : (fun n => diagonalMultiplier μ n *
      ((geometricTrial hμ0.le hμ1 : DomainLimitationSpace) : ℕ → ℝ) n)
      = fun _ : ℕ => (1 : ℝ) := by
    funext n
    rw [geometricTrial_apply]
    exact geometricDiagonalImage_eq_one (ne_of_gt hμ0) n
  rw [himage] at hmem
  have hsum : Summable fun _ : ℕ => (1 : ℝ) ^ 2 := summable_sq_of_memℓp_two hmem
  simp only [one_pow] at hsum
  have hzero : (0 : ℝ) = 1 :=
    tendsto_nhds_unique hsum.tendsto_atTop_zero tendsto_const_nhds
  exact zero_ne_one hzero

/-- **The trial vector is inside the form domain.**  The form sum `∑ dₙ |xₙ|²` is
the geometric series `∑ μⁿ`, which converges.

This is the asymmetry the source is pointing at: the same vector supplies a
useful Rayleigh quotient and no residual at all. -/
theorem geometricTrial_form_summable {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    Summable fun n => diagonalMultiplier μ n *
      ((geometricTrial hμ0.le hμ1 : DomainLimitationSpace) : ℕ → ℝ) n ^ 2 := by
  have h : (fun n => diagonalMultiplier μ n *
      ((geometricTrial hμ0.le hμ1 : DomainLimitationSpace) : ℕ → ℝ) n ^ 2)
      = fun n => μ ^ n := by
    funext n
    have hne : μ ^ n ≠ 0 := ne_of_gt (pow_pos hμ0 n)
    rw [geometricTrial_apply, diagonalMultiplier]
    field_simp
  rw [h]
  exact summable_geometric_of_lt_one hμ0.le hμ1

/-- The finite truncation, as a vector of the space. -/
noncomputable def truncatedTrial (μ : ℝ) (N : ℕ) : DomainLimitationSpace :=
  ⟨fun n => truncatedTrialSequence μ N n, by
    refine memℓp_two_of_summable_sq ?_
    refine summable_of_ne_finset_zero (s := Finset.range N) ?_
    intro n hn
    rw [truncatedTrialSequence_eq_zero (by simpa using hn), sq, mul_zero]⟩

/-- Coordinates of the truncated trial vector. -/
@[simp]
theorem truncatedTrial_apply (μ : ℝ) (N n : ℕ) :
    ((truncatedTrial μ N : DomainLimitationSpace) : ℕ → ℝ) n
      = truncatedTrialSequence μ N n := rfl

/-- **The truncation is inside the operator domain**: its image has finite
support.  This is the source's "arbitrarily small modification" that repairs the
domain obstruction. -/
theorem truncatedTrial_mem_diagonalDomain (μ : ℝ) (N : ℕ) :
    truncatedTrial μ N ∈ diagonalDomain (diagonalMultiplier μ) := by
  rw [mem_diagonalDomain_iff]
  refine memℓp_two_of_summable_sq ?_
  refine summable_of_ne_finset_zero (s := Finset.range N) ?_
  intro n hn
  rw [truncatedTrial_apply, truncatedTrialSequence_eq_zero (by simpa using hn),
    mul_zero, sq, mul_zero]

/-- On every prescribed prefix, long enough truncations agree with the trial
vector exactly. -/
theorem truncatedTrial_eq_geometricTrial_of_lt
    {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) {K N : ℕ} (hKN : K ≤ N) {n : ℕ} (hn : n < K) :
    ((truncatedTrial μ N : DomainLimitationSpace) : ℕ → ℝ) n
      = ((geometricTrial hμ0 hμ1 : DomainLimitationSpace) : ℕ → ℝ) n := by
  rw [truncatedTrial_apply, geometricTrial_apply,
    truncatedTrialSequence_eq_geometric (lt_of_lt_of_le hn hKN), geometricTrialSequence]

/-! ## The Rayleigh quotient of the trial vector

The source evaluates `α̂ = e*(A+H)e / e*e` for the geometric trial vector by two
geometric series: the numerator is `∑ μ⁻ⁿ(μⁿ)² = ∑ μⁿ = 1/(1-μ)`, the denominator
is `∑ (μⁿ)² = 1/(1-μ²)`, and the quotient is `(1-μ²)/(1-μ) = 1+μ`.

The numerator is the *quadratic form*, not an inner product against an operator
image: `(A+H)e` does not exist, which is the point of the example. -/

/-- The denominator `e*e` as a geometric series: `∑ (μⁿ)² = 1/(1-μ²)`. -/
theorem geometricTrial_hasSum_sq {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) :
    HasSum (fun n => ((geometricTrial hμ0 hμ1 : DomainLimitationSpace) : ℕ → ℝ) n ^ 2)
      (1 - μ ^ 2)⁻¹ := by
  have h : (fun n : ℕ => ((geometricTrial hμ0 hμ1 : DomainLimitationSpace) : ℕ → ℝ) n ^ 2)
      = fun n : ℕ => (μ ^ 2) ^ n := by
    funext n
    rw [geometricTrial_apply, ← pow_mul, ← pow_mul, mul_comm]
  rw [h]
  exact hasSum_geometric_of_lt_one (by positivity) (by nlinarith)

/-! ### The truncations repair the domain defect, and arbitrarily little is lost

The source's point is not merely that finite truncations lie in the domain, but
that the repair costs arbitrarily little: the trial vector can be replaced by one
inside the domain at any prescribed distance.  The truncations converge to it in
norm, because the discarded tail is a geometric series. -/

/-- Coordinates of the truncation error: zero below the cut, `-μⁿ` above it. -/
theorem truncatedTrial_sub_geometricTrial_apply {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1)
    (N n : ℕ) :
    ((truncatedTrial μ N - geometricTrial hμ0 hμ1 : DomainLimitationSpace) : ℕ → ℝ) n
      = if n < N then 0 else -(μ ^ n) := by
  rw [lp.coeFn_sub]
  by_cases hn : n < N <;>
    simp [hn, truncatedTrial_apply, geometricTrial_apply, truncatedTrialSequence]

/-- The truncation error has squared norm the geometric tail `μ^{2N}/(1-μ²)`. -/
theorem truncatedTrial_sub_geometricTrial_hasSum_sq {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1)
    (N : ℕ) :
    HasSum (fun n =>
        ((truncatedTrial μ N - geometricTrial hμ0 hμ1 : DomainLimitationSpace) : ℕ → ℝ) n ^ 2)
      ((μ ^ 2) ^ N * (1 - μ ^ 2)⁻¹) := by
  have hlt : μ ^ 2 < 1 := by nlinarith
  have hnn : (0 : ℝ) ≤ μ ^ 2 := by positivity
  set d : ℕ → ℝ := fun n => if n < N then 0 else (μ ^ 2) ^ n with hd
  have hcoord : (fun n =>
      ((truncatedTrial μ N - geometricTrial hμ0 hμ1 : DomainLimitationSpace) : ℕ → ℝ) n ^ 2)
      = d := by
    funext n
    rw [truncatedTrial_sub_geometricTrial_apply hμ0 hμ1 N n, hd]
    by_cases hn : n < N
    · simp [hn]
    · simp [hn, ← pow_mul, ← pow_mul, mul_comm]
  rw [hcoord]
  have hshift : HasSum (fun n => d (n + N)) ((μ ^ 2) ^ N * (1 - μ ^ 2)⁻¹) := by
    have hgeo := (hasSum_geometric_of_lt_one hnn hlt).mul_left ((μ ^ 2) ^ N)
    refine hgeo.congr_fun fun n => ?_
    rw [hd]
    simp only [ite_eq_right (by omega : ¬ n + N < N)]
    rw [pow_add, mul_comm]
  have hzero : ∑ i ∈ Finset.range N, d i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    simp [hd, Finset.mem_range.mp hi]
  have := (hasSum_nat_add_iff (f := d) N).mp hshift
  simpa [hzero] using this

/-- The truncation error's norm is `μ^N / sqrt(1-μ²)`, hence tends to zero. -/
theorem tendsto_norm_truncatedTrial_sub_geometricTrial {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) :
    Filter.Tendsto
      (fun N => ‖truncatedTrial μ N - geometricTrial hμ0 hμ1‖) Filter.atTop (nhds 0) := by
  have hlt : μ ^ 2 < 1 := by nlinarith
  have hnn : (0 : ℝ) ≤ μ ^ 2 := by positivity
  have hsq : ∀ N, ‖truncatedTrial μ N - geometricTrial hμ0 hμ1‖ ^ 2
      = (μ ^ 2) ^ N * (1 - μ ^ 2)⁻¹ := by
    intro N
    rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
    have h : (fun n : ℕ => inner ℝ
          (((truncatedTrial μ N - geometricTrial hμ0 hμ1 : DomainLimitationSpace) : ℕ → ℝ) n)
          (((truncatedTrial μ N - geometricTrial hμ0 hμ1 : DomainLimitationSpace) : ℕ → ℝ) n))
        = fun n : ℕ =>
          ((truncatedTrial μ N - geometricTrial hμ0 hμ1 : DomainLimitationSpace) : ℕ → ℝ) n ^ 2 := by
      funext n
      rw [RCLike.inner_apply', sq]
      simp
    rw [h]
    exact (truncatedTrial_sub_geometricTrial_hasSum_sq hμ0 hμ1 N).tsum_eq
  have hpow : Filter.Tendsto (fun N => (μ ^ 2) ^ N * (1 - μ ^ 2)⁻¹) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hnn hlt).mul_const (1 - μ ^ 2)⁻¹
  have hsqtend : Filter.Tendsto
      (fun N => ‖truncatedTrial μ N - geometricTrial hμ0 hμ1‖ ^ 2) Filter.atTop (nhds 0) := by
    simpa [hsq] using hpow
  have := hsqtend.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

/-- **The domain defect is repaired by an arbitrarily small modification.**

For every tolerance there is a truncation of the trial vector that lies in the
operator's domain and is within that tolerance of the trial vector.  This is the
source's own reading of the example: the vector's failure to lie in the domain is
not stable, so it obstructs the residual-based theorems without obstructing the
lower-bound methods. -/
theorem exists_truncatedTrial_mem_domain_and_dist_lt {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, truncatedTrial μ N ∈ diagonalDomain (diagonalMultiplier μ) ∧
      ‖truncatedTrial μ N - geometricTrial hμ0 hμ1‖ < ε := by
  obtain ⟨N, hN⟩ :=
    ((tendsto_norm_truncatedTrial_sub_geometricTrial hμ0 hμ1).eventually
      (eventually_lt_nhds hε)).exists
  exact ⟨N, truncatedTrial_mem_diagonalDomain μ N, hN⟩

/-- `e*e = ‖e‖² = 1/(1-μ²)`. -/
theorem geometricTrial_norm_sq {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) :
    ‖geometricTrial hμ0 hμ1‖ ^ 2 = (1 - μ ^ 2)⁻¹ := by
  rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
  have h : (fun n : ℕ => inner ℝ
        (((geometricTrial hμ0 hμ1 : DomainLimitationSpace) : ℕ → ℝ) n)
        (((geometricTrial hμ0 hμ1 : DomainLimitationSpace) : ℕ → ℝ) n))
      = fun n : ℕ => ((geometricTrial hμ0 hμ1 : DomainLimitationSpace) : ℕ → ℝ) n ^ 2 := by
    funext n
    rw [RCLike.inner_apply', sq]
    simp
  rw [h]
  exact (geometricTrial_hasSum_sq hμ0 hμ1).tsum_eq

/-- The numerator `e*(A+H)e` as a geometric series: `∑ μ⁻ⁿ(μⁿ)² = ∑ μⁿ = 1/(1-μ)`. -/
theorem geometricTrial_hasSum_form {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    HasSum (fun n => diagonalMultiplier μ n *
      ((geometricTrial hμ0.le hμ1 : DomainLimitationSpace) : ℕ → ℝ) n ^ 2) (1 - μ)⁻¹ := by
  have h : (fun n => diagonalMultiplier μ n *
      ((geometricTrial hμ0.le hμ1 : DomainLimitationSpace) : ℕ → ℝ) n ^ 2)
      = fun n => μ ^ n := by
    funext n
    have hne : μ ^ n ≠ 0 := ne_of_gt (pow_pos hμ0 n)
    rw [geometricTrial_apply, diagonalMultiplier]
    field_simp
  rw [h]
  exact hasSum_geometric_of_lt_one hμ0.le hμ1

/-- **The source's Rayleigh quotient**: `α̂ = e*(A+H)e / e*e = 1 + μ`.

This is the arithmetic the paragraph after (9.8) records, and it is the whole
reason the trial vector is useful despite not being in the operator domain. -/
theorem geometricTrial_rayleighQuotient {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    (∑' n, diagonalMultiplier μ n *
        ((geometricTrial hμ0.le hμ1 : DomainLimitationSpace) : ℕ → ℝ) n ^ 2)
      / ‖geometricTrial hμ0.le hμ1‖ ^ 2 = 1 + μ := by
  have h1 : (1 : ℝ) - μ ≠ 0 := ne_of_gt (by linarith)
  rw [(geometricTrial_hasSum_form hμ0 hμ1).tsum_eq, geometricTrial_norm_sq hμ0.le hμ1]
  have h2 : (1 : ℝ) - μ ^ 2 ≠ 0 := ne_of_gt (by nlinarith)
  field_simp
  ring

/-- The normalized coordinate energy `dₙ eₙ² / e*e` is `μⁿ(1-μ²)`. -/
theorem geometricTrial_normalizedForm_apply {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (n : ℕ) :
    diagonalMultiplier μ n *
        ((geometricTrial hμ0.le hμ1 : DomainLimitationSpace) : ℕ → ℝ) n ^ 2
      / ‖geometricTrial hμ0.le hμ1‖ ^ 2 = μ ^ n * (1 - μ ^ 2) := by
  have hne : μ ^ n ≠ 0 := ne_of_gt (pow_pos hμ0 n)
  have h2 : (1 : ℝ) - μ ^ 2 ≠ 0 := ne_of_gt (by nlinarith)
  rw [geometricTrial_norm_sq hμ0.le hμ1, geometricTrial_apply, diagonalMultiplier]
  field_simp

/-- The normalized form sums to the Rayleigh value `1 + μ`, coordinate by
coordinate. -/
theorem geometricTrial_hasSum_normalizedForm {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    HasSum (fun n : ℕ => μ ^ n * (1 - μ ^ 2)) (1 + μ) := by
  have h := (hasSum_geometric_of_lt_one hμ0.le hμ1).mul_right (1 - μ ^ 2)
  have h1 : (1 : ℝ) - μ ≠ 0 := ne_of_gt (by linarith)
  have hval : (1 - μ)⁻¹ * (1 - μ ^ 2) = 1 + μ := by
    field_simp
    ring
  rwa [hval] at h

/-- Every coordinate above the first carries normalized energy summing to
`μ + μ²`.  This is the `γ s²` side of the lower-bound estimate. -/
theorem geometricTrial_hasSum_normalizedFormTail {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    HasSum (fun n : ℕ => μ ^ (n + 1) * (1 - μ ^ 2)) (μ + μ ^ 2) := by
  have h := ((hasSum_geometric_of_lt_one hμ0.le hμ1).mul_left μ).mul_right (1 - μ ^ 2)
  have hfun : (fun n : ℕ => μ * μ ^ n * (1 - μ ^ 2))
      = fun n : ℕ => μ ^ (n + 1) * (1 - μ ^ 2) := by
    funext n
    rw [pow_succ]
    ring
  have h1 : (1 : ℝ) - μ ≠ 0 := ne_of_gt (by linarith)
  have hval : μ * (1 - μ)⁻¹ * (1 - μ ^ 2) = μ + μ ^ 2 := by
    field_simp
    ring
  rw [hfun, hval] at h
  exact h

/-- The first coordinate carries normalized energy `1 - μ²`. -/
theorem geometricTrial_normalizedForm_zero {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    diagonalMultiplier μ 0 *
        ((geometricTrial hμ0.le hμ1 : DomainLimitationSpace) : ℕ → ℝ) 0 ^ 2
      / ‖geometricTrial hμ0.le hμ1‖ ^ 2 = 1 - μ ^ 2 := by
  rw [geometricTrial_normalizedForm_apply hμ0 hμ1 0, pow_zero, one_mul]

/-- **The energy split the lower-bound method consumes**: the Rayleigh value is
the first-coordinate normalized energy plus the energy carried above it. -/
theorem geometricTrial_normalizedForm_split {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    (1 : ℝ) + μ
      = diagonalMultiplier μ 0 *
            ((geometricTrial hμ0.le hμ1 : DomainLimitationSpace) : ℕ → ℝ) 0 ^ 2
          / ‖geometricTrial hμ0.le hμ1‖ ^ 2
        + (μ + μ ^ 2) := by
  rw [geometricTrial_normalizedForm_zero hμ0 hμ1]
  ring

/-! ## The angle to the first eigenvector, and Weinberger's bound -/

/-- The first eigenvector `(1,0,0,…)` of `diag(1, μ⁻¹, μ⁻², …)`. -/
noncomputable def firstEigenvector : DomainLimitationSpace := lp.single 2 0 (1 : ℝ)

/-- Unfolding interface for `firstEigenvector`. -/
theorem firstEigenvector_def :
    (firstEigenvector : DomainLimitationSpace) = lp.single 2 0 (1 : ℝ) := rfl

/-- Coordinates of the first eigenvector. -/
@[simp]
theorem firstEigenvector_apply (n : ℕ) :
    ((firstEigenvector : DomainLimitationSpace) : ℕ → ℝ) n = if n = 0 then 1 else 0 := by
  rw [firstEigenvector_def]
  by_cases hn : n = 0
  · subst hn
    rw [lp.single_apply_self]
    simp
  · rw [lp.single_apply_ne _ _ _ hn]
    simp [hn]

/-- The first eigenvector is a unit vector. -/
theorem norm_firstEigenvector : ‖(firstEigenvector : DomainLimitationSpace)‖ = 1 := by
  rw [firstEigenvector_def, lp.norm_single (by norm_num), norm_one]

/-- Having one nonzero coordinate, the first eigenvector is in every diagonal
operator's domain. -/
theorem firstEigenvector_mem_diagonalDomain (d : ℕ → ℝ) :
    (firstEigenvector : DomainLimitationSpace) ∈ (diagonalOperator d).domain :=
  TauCeti.LinearPMap.single_mem_lpDiagonal_domain d 0 1

/-- `(1,0,0,…)` really is an eigenvector of the source's operator, with
eigenvalue `d₀ = 1`.  This is the `λ₁ = 1` against which the source's lower
bound `α̌₁ ≤ λ₁ = 1` is stated. -/
theorem diagonalOperator_firstEigenvector (μ : ℝ)
    (h : (firstEigenvector : DomainLimitationSpace)
      ∈ (diagonalOperator (diagonalMultiplier μ)).domain) :
    diagonalOperator (diagonalMultiplier μ) ⟨firstEigenvector, h⟩ = firstEigenvector := by
  apply lp.ext
  funext n
  rw [diagonalOperator_apply]
  by_cases hn : n = 0
  · subst hn
    simp [diagonalMultiplier]
  · simp [hn]

/-- The inner product of the trial vector with the first eigenvector is its first
coordinate, `μ⁰ = 1`. -/
theorem inner_geometricTrial_firstEigenvector {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) :
    inner ℝ (geometricTrial hμ0 hμ1) (firstEigenvector : DomainLimitationSpace) = 1 := by
  rw [firstEigenvector_def, lp.inner_single_right, RCLike.inner_apply', geometricTrial_apply]
  simp

/-- The cosine of the angle between the trial vector and the first eigenvector is
`√(1-μ²)`. -/
theorem cos_angle_geometricTrial {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    Real.cos (InnerProductGeometry.angle (geometricTrial hμ0.le hμ1)
        (firstEigenvector : DomainLimitationSpace))
      = Real.sqrt (1 - μ ^ 2) := by
  have hnorm : ‖geometricTrial hμ0.le hμ1‖ = Real.sqrt ((1 - μ ^ 2)⁻¹) := by
    calc ‖geometricTrial hμ0.le hμ1‖
        = Real.sqrt (‖geometricTrial hμ0.le hμ1‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt ((1 - μ ^ 2)⁻¹) := by rw [geometricTrial_norm_sq hμ0.le hμ1]
  rw [InnerProductGeometry.cos_angle, inner_geometricTrial_firstEigenvector,
    norm_firstEigenvector, mul_one, hnorm, Real.sqrt_inv, one_div, inv_inv]

/-- **`sin θ = μ`**, the source's `θ = arcsin μ` for the angle between the trial
vector and the first eigenvector. -/
theorem sin_angle_geometricTrial {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    Real.sin (InnerProductGeometry.angle (geometricTrial hμ0.le hμ1)
        (firstEigenvector : DomainLimitationSpace)) = μ := by
  have hpos : (0 : ℝ) ≤ 1 - μ ^ 2 := by nlinarith
  rw [Real.sin_eq_sqrt_one_sub_cos_sq (InnerProductGeometry.angle_nonneg _ _)
      (InnerProductGeometry.angle_le_pi _ _),
    cos_angle_geometricTrial hμ0 hμ1, Real.sq_sqrt hpos,
    show (1 : ℝ) - (1 - μ ^ 2) = μ ^ 2 from by ring, Real.sqrt_sq hμ0.le]

/-- **Weinberger's estimate for the source's `ℓ²` example.**

Residual-based theorems say nothing here: the residual `(A+H)e - e α̂` does not
exist, because `e` is outside the operator domain
(`geometricTrial_notMem_diagonalDomain`).  Weinberger's method needs only the
Rayleigh value `α̂ = 1+μ` and *independent* lower bounds `α̌₁ ≤ λ₁ = 1` and
`α̌₂ ≤ λ₂ = μ⁻¹`, all of which survive, and it delivers the source's

`sin²θ ≤ (1 + μ - α̌₁) / (α̌₂ - α̌₁)`.

The energy split fed to `weinberger_sine_sq_le_of_coupled_energy` is the genuine
one: `geometricTrial_normalizedForm_zero` and
`geometricTrial_hasSum_normalizedFormTail` evaluate the two energies. -/
theorem geometricTrial_weinberger_sin_sq_le {μ αcheck₁ αcheck₂ : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hlow : αcheck₁ ≤ 1) (hhigh : αcheck₂ ≤ μ⁻¹) (hgap : αcheck₁ < αcheck₂) :
    Real.sin (InnerProductGeometry.angle (geometricTrial hμ0.le hμ1)
        (firstEigenvector : DomainLimitationSpace)) ^ 2
      ≤ (1 + μ - αcheck₁) / (αcheck₂ - αcheck₁) := by
  have hsq : (0 : ℝ) ≤ 1 - μ ^ 2 := by nlinarith
  have hinvmul : μ⁻¹ * μ ^ 2 = μ := by
    field_simp
  have hhigh' : αcheck₂ * μ ^ 2 ≤ μ + μ ^ 2 := by
    have hstep : αcheck₂ * μ ^ 2 ≤ μ⁻¹ * μ ^ 2 :=
      mul_le_mul_of_nonneg_right hhigh (by positivity)
    nlinarith [sq_nonneg μ]
  rw [sin_angle_geometricTrial hμ0 hμ1]
  exact weinberger_sine_sq_le_of_coupled_energy (s := μ) (alphaCheck := αcheck₁)
    (alphaHat := 1 + μ) (gamma := αcheck₂) (lowEnergy := 1 - μ ^ 2)
    (highEnergy := μ + μ ^ 2) hgap (by ring) (by nlinarith) hhigh'

/-- **The source's best-lower-bound simplification, squared.**  With
`α̌₁ = λ₁ = 1` and `α̌₂ = λ₂ = μ⁻¹` the estimate reads `sin²θ ≤ μ²/(1-μ)`. -/
theorem geometricTrial_weinberger_best_sin_sq_le {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    Real.sin (InnerProductGeometry.angle (geometricTrial hμ0.le hμ1)
        (firstEigenvector : DomainLimitationSpace)) ^ 2
      ≤ μ ^ 2 / (1 - μ) := by
  have hmul : μ⁻¹ * μ = 1 := inv_mul_cancel₀ (ne_of_gt hμ0)
  have hinvpos : (0 : ℝ) < μ⁻¹ := inv_pos.mpr hμ0
  have hinv : (1 : ℝ) < μ⁻¹ := by nlinarith
  have h := geometricTrial_weinberger_sin_sq_le hμ0 hμ1 (αcheck₁ := 1) (αcheck₂ := μ⁻¹)
    le_rfl le_rfl hinv
  have h1 : (1 : ℝ) - μ ≠ 0 := ne_of_gt (by linarith)
  have hval : (1 + μ - 1) / (μ⁻¹ - 1) = μ ^ 2 / (1 - μ) := by
    field_simp
    ring
  rwa [hval] at h

/-- **The source's printed conclusion** `sin θ ≤ μ / √(1-μ)`.

The source annotates the left side with `(μ =)`: the true value of the sine is
exactly `μ` (`sin_angle_geometricTrial`), so the estimate is correct but not
sharp — which is precisely the contrast the paragraph is drawing, since no
residual-based theorem gives any bound at all here. -/
theorem geometricTrial_weinberger_best_sin_le {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    Real.sin (InnerProductGeometry.angle (geometricTrial hμ0.le hμ1)
        (firstEigenvector : DomainLimitationSpace))
      ≤ μ / Real.sqrt (1 - μ) := by
  set θ := InnerProductGeometry.angle (geometricTrial hμ0.le hμ1)
    (firstEigenvector : DomainLimitationSpace) with hθ
  have hpos : (0 : ℝ) < 1 - μ := by linarith
  have hb : (0 : ℝ) ≤ μ / Real.sqrt (1 - μ) := by positivity
  have hsq : (μ / Real.sqrt (1 - μ)) ^ 2 = μ ^ 2 / (1 - μ) := by
    rw [div_pow, Real.sq_sqrt hpos.le]
  calc Real.sin θ = Real.sqrt (Real.sin θ ^ 2) :=
        (Real.sqrt_sq (InnerProductGeometry.sin_angle_nonneg _ _)).symm
    _ ≤ Real.sqrt ((μ / Real.sqrt (1 - μ)) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [hsq]
        exact geometricTrial_weinberger_best_sin_sq_le hμ0 hμ1
    _ = μ / Real.sqrt (1 - μ) := Real.sqrt_sq hb

end Section9
end DavisKahan1970
end TauCeti
