/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.Separation.CompletelyRegular
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Distribution
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Periodicity

/-!
# Periodization and smooth-periodic Sobolev embeddings

Definitions and lemmas connecting smooth `2πℤⁿ`-periodic functions
on ℝⁿ to the momentum-side Sobolev structures of `DistributionSobolev`.

## Main contents

* `periodicExtension n φ` — `φ^per(x) = ∑_{k ∈ ℤⁿ} φ(x + 2πk)`.
* `periodicExtension_isPeriodic2Pi`, `periodicExtension_contDiff` —
  periodicity and smoothness of the periodic extension.
* `periodicExtension_re_nonneg`, `periodicExtension_im_zero` —
  real-part inequalities/equalities preserved by periodicization.
* `partialDeriv`, `laplacian` — coordinate partial derivatives and the
  flat Laplacian; smoothness and periodicity are preserved.
* `integral_partialDeriv_mul_fourierExp` — integration by parts on the
  period cube `[0,2π]ⁿ` (via the divergence theorem): for smooth periodic
  `g`, `∫ ∂ⱼg · e_c = -(i cⱼ) ∫ g · e_c`.
* `stdFourierCoeff_partialDeriv`, `stdFourierCoeff_laplacian`,
  `stdFourierCoeff_laplacian_iterate` — `∂ⱼ` and `Δ` act on standard
  Fourier coefficients as multiplication by `i mⱼ` and `-|m|²`.
* `norm_stdFourierCoeff_le` — a sup bound on the period cube bounds all
  Fourier coefficients.
* `stdFourierCoeff_rapid_decay` — Fourier coefficients of a smooth
  `2πℤⁿ`-periodic function decay faster than any polynomial.
* `memSobolev_of_rapid_decay` — a rapidly decaying ℤⁿ-sequence lies
  in every `MemSobolev n s`.
* `toUnitTorus`, `toUnitTorusFun`, `toUnitTorusCM` — transport of a
  `2πℤⁿ`-periodic function to Mathlib's unit torus `UnitAddTorus (Fin n)`;
  `mFourierCoeff_toUnitTorusCM` identifies Mathlib's multivariate Fourier
  coefficients with `stdFourierCoeff`.
* `integral_periodCube_add_right`, `integral_periodCube_translate` —
  translation invariance of `∫_{[0,2π]ⁿ}` for continuous periodic
  integrands (via Haar invariance on the unit torus).
* `fourierSynthesis_stdFourierCoeff_of_smoothPeriodic` — Fourier
  inversion for smooth periodic functions: `fourierSynthesis n
  (stdFourierCoeff n f) = f` (from rapid decay and Mathlib's
  `UnitAddTorus.hasSum_mFourier_series_apply_of_summable`).
* `smooth_periodic_memSobolevDistrib` — smooth `2πℤⁿ`-periodic ⟹
  in every `MemSobolevDistrib n s`.
-/

open scoped BigOperators ContDiff
open Complex Real MeasureTheory

noncomputable
section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-! ## Definition: periodic extension -/

/-- The periodic extension of `φ : ℝⁿ → ℂ`:
    `φ^per(x) = ∑_{k ∈ ℤⁿ} φ(x + 2πk)`.
    For `φ` with `supp(φ) ⊂ (-π, π)ⁿ`, at most one term is nonzero
    at each `x`. -/
def periodicExtension (n : ℕ) (φ : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  ∑' k : Fin n → ℤ, φ (x + periodicShift n k)

/-! ## Smoothness and periodicity of the periodic extension -/

/-
`periodicExtension n φ` is `2πℤⁿ`-periodic for any `φ`.
-/
lemma periodicExtension_isPeriodic2Pi (φ : (Fin n → ℝ) → ℂ) :
    IsPeriodic2Pi (periodicExtension n φ) := by
  unfold periodicExtension; intro x k; symm; simp +decide only ;
  rw [ ← Equiv.tsum_eq ( Equiv.addLeft k ) ]; simp +decide only [Equiv.coe_addLeft]; ring;
  unfold periodicShift; congr; ext; simp +decide only [Pi.add_apply, Int.cast_add, add_assoc] ;
  exact congr_arg _ ( by ext; simp +decide [ mul_add ] )

/-
For `φ ∈ C^∞_c(ℝⁿ; ℂ)`, `periodicExtension n φ` is `C^∞`.
-/
lemma periodicExtension_contDiff {φ : (Fin n → ℝ) → ℂ}
    (hsmooth : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) :
    ContDiff ℝ ∞ (periodicExtension n φ) := by
  have h_compact_support : ∃ R : ℝ, ∀ x : Fin n → ℝ, ‖x‖ ≥ R → φ x = 0 := by
    obtain ⟨ R, hR ⟩ := hsupp.exists_pos_le_norm;
    exact ⟨ R, hR.2 ⟩;
  -- Since the sum is locally finite, we can apply the fact that a locally finite sum of
  -- smooth functions is smooth.
  have h_locally_finite : ∀ x : Fin n → ℝ, ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x ∈ U ∧ Set.Finite
      {k : Fin n → ℤ | ∃ y ∈ U, φ (y + periodicShift n k) ≠ 0} := by
    intro x
    obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ x : Fin n → ℝ, ‖x‖ ≥ R → φ x = 0 := h_compact_support
    use Metric.ball x 1;
    refine ⟨ Metric.isOpen_ball, Metric.mem_ball_self zero_lt_one, ?_ ⟩;
    -- Since $\varphi$ has compact support, there exists $R > 0$ such that $\varphi(x) = 0$
    -- for all $x$ with $\|x\| \geq R$. Therefore, for any $y \in \text{ball}(x, 1)$, we
    -- have $\|y + \text{periodicShift}(n, k)\| \geq R$ implies $\varphi(y +
    -- \text{periodicShift}(n, k)) = 0$.
    have h_bound : ∀ k : Fin n → ℤ, (∃ y ∈ Metric.ball x 1, φ (y + periodicShift n k) ≠ 0) → ∀ i
        : Fin n, |(k i : ℝ)| ≤ (R + ‖x‖ + 1) / (2 * Real.pi) := by
      intros k hk i
      obtain ⟨y, hy_ball, hy_nonzero⟩ := hk
      have h_bound : ‖y + periodicShift n k‖ < R := by
        exact lt_of_not_ge fun h => hy_nonzero <| hR _ h;
      have h_bound : |(y i + 2 * Real.pi * (k i : ℝ))| ≤ R := by
        exact le_trans ( by simpa [Pi.add_apply, periodicShift] using norm_le_pi_norm ( y +
            periodicShift n k ) i ) h_bound.le;
      have h_bound : |y i| ≤ ‖x‖ + 1 := by
        have h_bound : |y i - x i| ≤ ‖y - x‖ := by
          exact norm_le_pi_norm ( y - x ) i;
        have hdist : ‖y - x‖ < 1 := by
          rw [← dist_eq_norm]
          exact hy_ball
        have hx := abs_le.mp (norm_le_pi_norm x i)
        exact abs_le.mpr ⟨by linarith [(abs_le.mp h_bound).1],
          by linarith [(abs_le.mp h_bound).2]⟩
      rw [ le_div_iff₀ ] <;> cases abs_cases ( k i : ℝ ) <;> cases abs_cases ( y i + 2 * Real.pi
          * ( k i : ℝ ) ) <;> cases abs_cases ( y i ) <;> nlinarith [ Real.pi_gt_three ];
    -- Since $|k_i| \leq \frac{R + \|x\| + 1}{2\pi}$ for all $i$, the set of such $k$ is finite.
    have h_finite_k : Set.Finite {k : Fin n → ℤ | ∀ i : Fin n, |(k i : ℝ)| ≤ (R + ‖x‖ + 1) / (2
        * Real.pi)} := by
      have h_finite_k : ∀ i : Fin n, Set.Finite {k : ℤ | |(k : ℝ)| ≤ (R + ‖x‖ + 1) / (2 *
          Real.pi)} := by
        intro i
        apply (Set.finite_Icc (-⌈(R + ‖x‖ + 1) / (2 * Real.pi)⌉)
          ⌈(R + ‖x‖ + 1) / (2 * Real.pi)⌉).subset
        intro k hk
        have hkceil : |k| ≤ ⌈(R + ‖x‖ + 1) / (2 * Real.pi)⌉ := by
          exact_mod_cast hk.out.trans (Int.le_ceil _)
        exact ⟨neg_le_of_abs_le hkceil, le_of_abs_le hkceil⟩
      exact Set.Finite.subset ( Set.Finite.pi fun i => h_finite_k i ) fun k hk => by simpa using hk;
    exact h_finite_k.subset fun k hk => h_bound k hk;
  have h_locally_finite_sum : ∀ x : Fin n → ℝ, ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x ∈ U ∧ ∃ S :
      Finset (Fin n → ℤ), ∀ y ∈ U, ∑' k : Fin n → ℤ, φ (y + periodicShift n k) = ∑ k ∈ S, φ (y +
      periodicShift n k) := by
    intro x
    obtain ⟨U, hU_open, hxU, hU_finite⟩ := h_locally_finite x
    use U, hU_open, hxU
    use hU_finite.toFinset
    intro y hy
    have h_sum_eq : ∑' k : Fin n → ℤ, φ (y + periodicShift n k) = ∑ k ∈ hU_finite.toFinset, φ (y
        + periodicShift n k) := by
      rw [ tsum_eq_sum ];
      simp +contextual only [ne_eq, hU_finite.mem_toFinset, Set.mem_ofPred_eq, not_exists,
        not_and, Decidable.not_not];
      exact fun k hk => hk y hy
    exact h_sum_eq;
  refine contDiff_iff_contDiffAt.mpr ?_;
  intro x
  obtain ⟨U, hU_open, hxU, S, hS⟩ := h_locally_finite_sum x
  have h_cont_diff : ContDiffOn ℝ ∞ (fun y => ∑ k ∈ S, φ (y + periodicShift n k)) U := by
    exact ContDiffOn.sum fun k hk => hsmooth.comp_contDiffOn ( contDiffOn_id.add contDiffOn_const );
  exact h_cont_diff.contDiffAt ( hU_open.mem_nhds hxU ) |> fun h => h.congr_of_eventuallyEq (
      Filter.eventuallyEq_of_mem ( hU_open.mem_nhds hxU ) fun y hy => hS y hy ▸ rfl )

/-
If `φ` has pointwise non-negative real part, its periodic extension does too.
The nonsummable case follows from the zero convention for `tsum`.
-/
lemma periodicExtension_re_nonneg {φ : (Fin n → ℝ) → ℂ}
     (hnn : ∀ x, 0 ≤ (φ x).re) :
    ∀ y, 0 ≤ (periodicExtension n φ y).re := by
  intro y
  unfold periodicExtension;
  by_cases h : Summable ( fun k : Fin n → ℤ => φ ( y + periodicShift n k ) );
  · convert Complex.re_tsum h |> fun h' => h'.symm ▸ tsum_nonneg fun k => hnn ( y +
      periodicShift n k ) using 1;
  · rw [ tsum_eq_zero_of_not_summable h ]; norm_num

/-
If `φ` has pointwise zero imaginary part (e.g.\ `φ`
    is `Complex.ofReal ∘ ψ` for real-valued `ψ`), then
    `periodicExtension n φ` has pointwise zero imaginary part.
-/
lemma periodicExtension_im_zero {φ : (Fin n → ℝ) → ℂ}
     (him : ∀ x, (φ x).im = 0) :
    ∀ y, (periodicExtension n φ y).im = 0 := by
  intro y
  unfold periodicExtension;
  by_cases h : Summable ( fun k : Fin n → ℤ => φ ( y + periodicShift n k ) );
  · have h_im_zero : Complex.im (∑' k : Fin n → ℤ, φ (y + periodicShift n k)) = ∑' k : Fin n →
      ℤ, Complex.im (φ (y + periodicShift n k)) := by
      convert Complex.im_tsum h;
    aesop;
  · rw [ tsum_eq_zero_of_not_summable h ]; norm_num

/-! ## Partial derivatives of periodic functions -/

/-- The partial derivative `∂ⱼ g (θ) = Dg(θ)[eⱼ]`. -/
def partialDeriv (j : Fin n) (g : (Fin n → ℝ) → ℂ) (θ : Fin n → ℝ) : ℂ :=
  fderiv ℝ g θ (Pi.single j 1)

lemma partialDeriv_contDiff {g : (Fin n → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) (j : Fin n) :
    ContDiff ℝ ∞ (partialDeriv j g) :=
  (hg.fderiv_right infty_add_one_le).clm_apply contDiff_const

lemma partialDeriv_isPeriodic2Pi {g : (Fin n → ℝ) → ℂ} (hper : IsPeriodic2Pi g) (j : Fin n) :
    IsPeriodic2Pi (partialDeriv j g) := by
  intro x k
  unfold partialDeriv
  have h : (fun y => g (y + periodicShift n k)) = g := funext fun y => hper y k
  rw [← fderiv_comp_add_right (periodicShift n k), h]

lemma hasDerivAt_fourierExp_update (c : Fin n → ℤ) (θ : Fin n → ℝ) (j : Fin n) :
    HasDerivAt (fun t : ℝ => fourierExp n c (Function.update θ j t))
      (Complex.I * (c j : ℂ) * fourierExp n c θ) (θ j) := by
  unfold fourierExp
  simp +decide only [Function.update_apply, mul_ite, Finset.sum_ite, Finset.filter_eq',
    Finset.mem_univ, ↓reduceIte, Finset.sum_singleton, Finset.filter_ne', Finset.sum_erase_eq_sub,
    ofReal_add, ofReal_mul, ofReal_intCast, ofReal_sub, ofReal_sum]
  convert HasDerivAt.comp ( θ j ) ( Complex.hasDerivAt_exp _ ) ( HasDerivAt.const_mul Complex.I
      <| HasDerivAt.add ( HasDerivAt.const_mul ( c j : ℂ ) <| hasDerivAt_id _ |>
      HasDerivAt.ofReal_comp ) <| hasDerivAt_const _ ((∑ x, ((c x : ℂ) * (θ x : ℂ))) - (c j : ℂ)
      * (θ j : ℂ)) ) using 1
  all_goals (first
    | rfl
    | (simp only [Pi.add_apply, id_eq]; push_cast; ring))

lemma fderiv_fourierExp_single (c : Fin n → ℤ) (θ : Fin n → ℝ) (j : Fin n) :
    fderiv ℝ (fourierExp n c) θ (Pi.single j 1) = Complex.I * (c j : ℂ) * fourierExp n c θ := by
  have hd : HasFDerivAt (fourierExp n c) (fderiv ℝ (fourierExp n c) θ) θ :=
    ((fourierExp_contDiff c).differentiable infty_ne_zero θ).hasFDerivAt
  exact (hasDerivAt_update_of_hasFDerivAt hd j).unique (hasDerivAt_fourierExp_update c θ j)

lemma fourierExp_isPeriodic2Pi (c : Fin n → ℤ) : IsPeriodic2Pi (fourierExp n c) := by
  intro x k
  unfold fourierExp periodicShift
  have h : (∑ i, (c i : ℝ) * (x i + 2 * π * (k i : ℝ)))
      = (∑ i, (c i : ℝ) * x i) + ((∑ i, c i * k i : ℤ) : ℝ) * (2 * π) := by
    push_cast
    simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring
  simp only [Pi.add_apply]
  rw [h]
  push_cast
  rw [mul_add, Complex.exp_add]
  have h2 : Complex.exp (Complex.I * ((∑ i, (c i : ℂ) * (k i : ℂ)) * (2 * π))) = 1 := by
    rw [show Complex.I * ((∑ i, (c i : ℂ) * (k i : ℂ)) * (2 * π))
        = ((∑ i, c i * k i : ℤ) : ℂ) * (2 * π * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [h2, mul_one]

/-- The product rule evaluated in direction `eⱼ`. -/
lemma fderiv_mul_fourierExp_single {g : (Fin n → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g)
    (c : Fin n → ℤ) (θ : Fin n → ℝ) (j : Fin n) :
    fderiv ℝ (fun θ => g θ * fourierExp n c θ) θ (Pi.single j 1)
      = partialDeriv j g θ * fourierExp n c θ
        + g θ * (Complex.I * (c j : ℂ) * fourierExp n c θ) := by
  have hF : HasFDerivAt (fun θ => g θ * fourierExp n c θ)
      (g θ • fderiv ℝ (fourierExp n c) θ + fourierExp n c θ • fderiv ℝ g θ) θ :=
    (hg.differentiable infty_ne_zero θ).hasFDerivAt.mul
      ((fourierExp_contDiff c).differentiable infty_ne_zero θ).hasFDerivAt
  rw [hF.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    fderiv_fourierExp_single, partialDeriv]
  ring

/-! ## Integration by parts on the period cube -/

/-- The shift by `2π` in the `j`-th slot of `insertNth`. -/
lemma insertNth_two_pi_eq {k : ℕ} (j : Fin (k + 1)) (x : Fin k → ℝ) :
    (j.insertNth (2 * π) x : Fin (k + 1) → ℝ)
      = j.insertNth 0 x + periodicShift (k + 1) (Pi.single j 1) := by
  funext i
  refine Fin.succAboveCases j ?_ ?_ i
  · simp [periodicShift]
  · intro i'
    simp [periodicShift, Fin.succAbove_ne j i']

/-- **Integration by parts on the period cube.** For smooth `2πℤⁿ`-periodic `g`,
`∫ ∂ⱼg · e_c = -(i cⱼ) ∫ g · e_c` over `[0,2π]ⁿ`. -/
theorem integral_partialDeriv_mul_fourierExp {k : ℕ} {g : (Fin (k + 1) → ℝ) → ℂ}
    (hg : ContDiff ℝ ∞ g) (hper : IsPeriodic2Pi g) (c : Fin (k + 1) → ℤ) (j : Fin (k + 1)) :
    ∫ θ in Set.Icc (0 : Fin (k + 1) → ℝ) (2 * π • (1 : Fin (k + 1) → ℝ)),
        partialDeriv j g θ * fourierExp (k + 1) c θ
      = -(Complex.I * (c j : ℂ)) *
        ∫ θ in Set.Icc (0 : Fin (k + 1) → ℝ) (2 * π • (1 : Fin (k + 1) → ℝ)),
          g θ * fourierExp (k + 1) c θ := by
  set P : (Fin (k + 1) → ℝ) → ℂ := fun θ => g θ * fourierExp (k + 1) c θ with hP
  have hPsmooth : ContDiff ℝ ∞ P := hg.mul (fourierExp_contDiff c)
  have hPper : IsPeriodic2Pi P := fun x l => by
    simp only [hP, hper x l, fourierExp_isPeriodic2Pi c x l]
  set F : (Fin (k + 1) → ℝ) → (Fin (k + 1) → ℂ) :=
    fun θ => ContinuousLinearMap.single ℝ (fun _ : Fin (k + 1) => ℂ) j (P θ) with hF
  set F' : (Fin (k + 1) → ℝ) → ((Fin (k + 1) → ℝ) →L[ℝ] (Fin (k + 1) → ℂ)) :=
    fun θ => (ContinuousLinearMap.single ℝ (fun _ : Fin (k + 1) => ℂ) j).comp (fderiv ℝ P θ)
    with hF'
  have hFc : Continuous F :=
    (ContinuousLinearMap.single ℝ (fun _ : Fin (k + 1) => ℂ) j).continuous.comp hPsmooth.continuous
  have hFd : ∀ θ, HasFDerivAt F (F' θ) θ := by
    intro θ
    have h1 : HasFDerivAt P (fderiv ℝ P θ) θ :=
      (hPsmooth.differentiable infty_ne_zero θ).hasFDerivAt
    exact (ContinuousLinearMap.single ℝ (fun _ : Fin (k + 1) => ℂ) j).hasFDerivAt.comp θ h1
  have hdiv : ∀ θ, ∑ i, F' θ (Pi.single i 1) i
      = partialDeriv j g θ * fourierExp (k + 1) c θ
        + g θ * (Complex.I * (c j : ℂ) * fourierExp (k + 1) c θ) := by
    intro θ
    rw [← fderiv_mul_fourierExp_single hg c θ j]
    simp only [hF', ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply]
    rw [Finset.sum_eq_single j]
    · simp [hP]
    · intro i _ hij
      simp [Pi.single_eq_of_ne hij]
    · simp
  have hle : (0 : Fin (k + 1) → ℝ) ≤ 2 * π • (1 : Fin (k + 1) → ℝ) := by
    intro i
    simp only [ Pi.mul_apply, Pi.ofNat_apply, Pi.smul_apply,
      smul_eq_mul, mul_one, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
    positivity
  have hAc : Continuous (fun θ => partialDeriv j g θ * fourierExp (k + 1) c θ) :=
    (partialDeriv_contDiff hg j).continuous.mul (fourierExp_contDiff c).continuous
  have hBc : Continuous (fun θ => g θ * (Complex.I * (c j : ℂ) * fourierExp (k + 1) c θ)) :=
    hg.continuous.mul (continuous_const.mul (fourierExp_contDiff c).continuous)
  have hint : IntegrableOn (fun θ => ∑ i, F' θ (Pi.single i 1) i)
      (Set.Icc (0 : Fin (k + 1) → ℝ) (2 * π • (1 : Fin (k + 1) → ℝ))) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    refine Continuous.continuousOn ?_
    rw [show (fun θ => ∑ i, F' θ (Pi.single i 1) i)
        = fun θ => partialDeriv j g θ * fourierExp (k + 1) c θ
          + g θ * (Complex.I * (c j : ℂ) * fourierExp (k + 1) c θ) from funext hdiv]
    exact hAc.add hBc
  have key := integral_divergence_of_hasFDerivAt_off_countable (0 : Fin (k + 1) → ℝ)
    (2 * π • (1 : Fin (k + 1) → ℝ)) hle F F' ∅ Set.countable_empty hFc.continuousOn
    (fun θ _ => hFd θ) hint
  -- the boundary terms vanish by periodicity
  have hface : ∀ i : Fin (k + 1), ∀ x : Fin k → ℝ,
      F (i.insertNth ((2 * π • (1 : Fin (k + 1) → ℝ)) i) x) i
        = F (i.insertNth ((0 : Fin (k + 1) → ℝ) i) x) i := by
    intro i x
    have h2 : ((2 : Fin (k + 1) → ℝ) * π • (1 : Fin (k + 1) → ℝ)) i = 2 * π := by simp
    simp only [hF, ContinuousLinearMap.single_apply, h2, Pi.zero_apply]
    by_cases hij : i = j
    · subst hij
      simp only [Pi.single_eq_same]
      rw [insertNth_two_pi_eq, hPper]
    · simp [Pi.single_eq_of_ne hij]
  rw [Finset.sum_eq_zero (fun i _ => by
    rw [sub_eq_zero]
    exact integral_congr_ae (Filter.Eventually.of_forall (hface i)))] at key
  simp only [hdiv] at key
  rw [integral_add (hAc.continuousOn.integrableOn_compact isCompact_Icc)
    (hBc.continuousOn.integrableOn_compact isCompact_Icc)] at key
  have hB' : ∫ θ in Set.Icc (0 : Fin (k + 1) → ℝ) (2 * π • (1 : Fin (k + 1) → ℝ)),
        g θ * (Complex.I * (c j : ℂ) * fourierExp (k + 1) c θ)
      = (Complex.I * (c j : ℂ)) *
        ∫ θ in Set.Icc (0 : Fin (k + 1) → ℝ) (2 * π • (1 : Fin (k + 1) → ℝ)),
          g θ * fourierExp (k + 1) c θ := by
    rw [← integral_const_mul]
    congr 1
    funext θ
    ring
  rw [hB'] at key
  linear_combination key

/-- `∂ⱼ` acts on standard Fourier coefficients as multiplication by `i mⱼ`. -/
theorem stdFourierCoeff_partialDeriv (hn : 0 < n) {g : (Fin n → ℝ) → ℂ}
    (hg : ContDiff ℝ ∞ g) (hper : IsPeriodic2Pi g) (j : Fin n) (m : Fin n → ℤ) :
    stdFourierCoeff n (partialDeriv j g) m = Complex.I * (m j : ℂ) * stdFourierCoeff n g m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  unfold stdFourierCoeff
  rw [integral_partialDeriv_mul_fourierExp hg hper (-m) j]
  simp only [Pi.neg_apply, Int.cast_neg]
  ring

/-! ## The Laplacian and iterated Fourier multipliers -/

/-- The (flat) Laplacian `Δg = ∑ⱼ ∂ⱼ∂ⱼ g`. -/
def laplacian (g : (Fin n → ℝ) → ℂ) : (Fin n → ℝ) → ℂ :=
  fun θ => ∑ j, partialDeriv j (partialDeriv j g) θ

lemma laplacian_contDiff {g : (Fin n → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (laplacian g) := by
  unfold laplacian
  exact ContDiff.sum fun j _ => partialDeriv_contDiff (partialDeriv_contDiff hg j) j

lemma laplacian_isPeriodic2Pi {g : (Fin n → ℝ) → ℂ} (hper : IsPeriodic2Pi g) :
    IsPeriodic2Pi (laplacian g) := by
  intro x k
  unfold laplacian
  exact Finset.sum_congr rfl fun j _ =>
    partialDeriv_isPeriodic2Pi (partialDeriv_isPeriodic2Pi hper j) j x k

lemma laplacian_iterate_contDiff {g : (Fin n → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) (N : ℕ) :
    ContDiff ℝ ∞ (laplacian^[N] g) := by
  induction N with
  | zero => simpa
  | succ N ih => rw [Function.iterate_succ_apply']; exact laplacian_contDiff ih

lemma laplacian_iterate_isPeriodic2Pi {g : (Fin n → ℝ) → ℂ} (hper : IsPeriodic2Pi g) (N : ℕ) :
    IsPeriodic2Pi (laplacian^[N] g) := by
  induction N with
  | zero => simpa
  | succ N ih => rw [Function.iterate_succ_apply']; exact laplacian_isPeriodic2Pi ih

lemma stdFourierCoeff_finset_sum {ι : Type*} (s : Finset ι) (g : ι → (Fin n → ℝ) → ℂ)
    (hg : ∀ i ∈ s, Continuous (g i)) (m : Fin n → ℤ) :
    stdFourierCoeff n (fun θ => ∑ i ∈ s, g i θ) m = ∑ i ∈ s, stdFourierCoeff n (g i) m := by
  unfold stdFourierCoeff
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum s (f := fun i θ => g i θ * fourierExp n (-m) θ) (fun i hi =>
    ((hg i hi).mul (fourierExp_contDiff _).continuous).continuousOn.integrableOn_compact
      isCompact_Icc), Finset.mul_sum]

/-- `Δ` acts on standard Fourier coefficients as multiplication by `-|m|²`. -/
theorem stdFourierCoeff_laplacian (hn : 0 < n) {g : (Fin n → ℝ) → ℂ}
    (hg : ContDiff ℝ ∞ g) (hper : IsPeriodic2Pi g) (m : Fin n → ℤ) :
    stdFourierCoeff n (laplacian g) m
      = -(∑ j, ((m j : ℂ)) ^ 2) * stdFourierCoeff n g m := by
  unfold laplacian
  rw [stdFourierCoeff_finset_sum Finset.univ _
    (fun j _ => (partialDeriv_contDiff (partialDeriv_contDiff hg j) j).continuous)]
  simp_rw [stdFourierCoeff_partialDeriv hn (partialDeriv_contDiff hg _)
    (partialDeriv_isPeriodic2Pi hper _), stdFourierCoeff_partialDeriv hn hg hper]
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  linear_combination ((m j : ℂ) ^ 2 * stdFourierCoeff n g m) * Complex.I_sq

theorem stdFourierCoeff_laplacian_iterate (hn : 0 < n) {g : (Fin n → ℝ) → ℂ}
    (hg : ContDiff ℝ ∞ g) (hper : IsPeriodic2Pi g) (N : ℕ) (m : Fin n → ℤ) :
    stdFourierCoeff n (laplacian^[N] g) m
      = (-(∑ j, ((m j : ℂ)) ^ 2)) ^ N * stdFourierCoeff n g m := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply', stdFourierCoeff_laplacian hn
      (laplacian_iterate_contDiff hg N) (laplacian_iterate_isPeriodic2Pi hper N), ih, pow_succ]
    ring

/-! ## The trivial sup bound -/

lemma volume_real_periodCube :
    volume.real (Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ))) = (2 * π) ^ n := by
  rw [measureReal_def, Real.volume_Icc_pi]
  have h : ∀ i : Fin n, ((2 : Fin n → ℝ) * π • (1 : Fin n → ℝ)) i - (0 : Fin n → ℝ) i = 2 * π := by
    intro i; simp
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]

/-- A sup bound on the period cube bounds all standard Fourier coefficients. -/
lemma norm_stdFourierCoeff_le {g : (Fin n → ℝ) → ℂ} {M : ℝ}
    (hM : ∀ θ ∈ Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ)), ‖g θ‖ ≤ M)
    (m : Fin n → ℤ) : ‖stdFourierCoeff n g m‖ ≤ M := by
  unfold stdFourierCoeff
  have hb : ‖∫ θ in Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ)),
      g θ * fourierExp n (-m) θ‖ ≤ M * (2 * π) ^ n := by
    rw [← volume_real_periodCube]
    apply norm_setIntegral_le_of_norm_le_const
    · exact isCompact_Icc.measure_lt_top
    · intro θ hθ
      rw [norm_mul, norm_fourierExp, mul_one]
      exact hM θ hθ
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc ((2 * π) ^ n)⁻¹ * ‖∫ θ in Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ)),
        g θ * fourierExp n (-m) θ‖
      ≤ ((2 * π) ^ n)⁻¹ * (M * (2 * π) ^ n) := by gcongr
    _ = M := by field_simp

/-! ## Smooth periodic Fourier coefficients -/

/-- Standard Fourier coefficients of a smooth `2πℤⁿ`-periodic function
    decay faster than any polynomial. -/
lemma stdFourierCoeff_rapid_decay (hn : 0 < n) {f : (Fin n → ℝ) → ℂ}
    (hsmooth : ContDiff ℝ ∞ f) (hper : IsPeriodic2Pi f) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : Fin n → ℤ,
      ‖stdFourierCoeff n f m‖ ≤ C * weight n (-(N / 2 : ℝ)) m := by
  obtain ⟨M0, hM0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hsmooth.continuous.continuousOn (s := Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ))))
  obtain ⟨MN, hMN⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((laplacian_iterate_contDiff hsmooth N).continuous.continuousOn
      (s := Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ))))
  refine ⟨2 ^ N * (|M0| + |MN|) + 1, by positivity, fun m => ?_⟩
  set S : ℝ := ∑ j, ((m j : ℝ)) ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  have h0 : ‖stdFourierCoeff n f m‖ ≤ |M0| :=
    norm_stdFourierCoeff_le (fun θ hθ => (hM0 θ hθ).trans (le_abs_self _)) m
  have hN : S ^ N * ‖stdFourierCoeff n f m‖ ≤ |MN| := by
    have h := norm_stdFourierCoeff_le (fun θ hθ => (hMN θ hθ).trans (le_abs_self _)) m
    rw [stdFourierCoeff_laplacian_iterate hn hsmooth hper N m, norm_mul, norm_pow, norm_neg] at h
    have hcast : ‖∑ j, ((m j : ℂ)) ^ 2‖ = S := by
      have : (∑ j, ((m j : ℂ)) ^ 2) = ((S : ℝ) : ℂ) := by simp [hS]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0]
    rwa [hcast] at h
  have hw : weight n (N / 2 : ℝ) m ≤ 2 ^ N * (1 + S ^ N) := by
    calc weight n (N / 2 : ℝ) m ≤ weight n (N : ℝ) m :=
          weight_mono (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]) m
      _ = (1 + S) ^ N := by unfold weight; rw [Real.rpow_natCast]
      _ ≤ (2 * max 1 S) ^ N :=
          pow_le_pow_left₀ (by positivity) (by linarith [le_max_left 1 S, le_max_right 1 S]) N
      _ = 2 ^ N * (max 1 S) ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + S ^ N) := by
          gcongr
          rcases le_total 1 S with h | h
          · rw [max_eq_right h]; linarith
          · rw [max_eq_left h, one_pow]; linarith [pow_nonneg hS0 N]
  have hkey : ‖stdFourierCoeff n f m‖ * weight n (N / 2 : ℝ) m ≤ 2 ^ N * (|M0| + |MN|) := by
    calc ‖stdFourierCoeff n f m‖ * weight n (N / 2 : ℝ) m
        ≤ ‖stdFourierCoeff n f m‖ * (2 ^ N * (1 + S ^ N)) := by gcongr
      _ = 2 ^ N * (‖stdFourierCoeff n f m‖ + S ^ N * ‖stdFourierCoeff n f m‖) := by ring
      _ ≤ 2 ^ N * (|M0| + |MN|) := by gcongr
  have hwinv : weight n (-(N / 2 : ℝ)) m = (weight n (N / 2 : ℝ) m)⁻¹ := by
    have h := weight_mul (-(N / 2 : ℝ)) (N / 2 : ℝ) m
    rw [neg_add_cancel, weight_zero] at h
    exact eq_inv_of_mul_eq_one_left h
  rw [hwinv, ← div_eq_mul_inv, le_div_iff₀ (weight_pos _ _)]
  linarith [hkey]

/-! ## Sobolev membership from rapid decay -/

/-
If a sequence has polynomial decay of every order, it belongs to
    `MemSobolev n s` for every `s ∈ ℝ`.
-/
lemma memSobolev_of_rapid_decay (hn : 0 < n) {a : (Fin n → ℤ) → ℂ}
    (h : ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ m, ‖a m‖ ≤ C * weight n (-(N / 2 : ℝ)) m)
    (s : ℝ) : MemSobolev n s a := by
  -- Choose N such that N/2 > s + n/2. This ensures that 2(N-s) > n.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N / 2 > s + n / 2 := by
    exact ⟨ ⌊s * 2 + n⌋₊ + 1, by push_cast; linarith [ Nat.lt_floor_add_one ( s * 2 + n ) ] ⟩;
  -- By hypothesis, there exists a constant C such that ‖a m‖ ≤ C * weight n (-(N / 2)) m for all m.
  obtain ⟨C, hC_pos, hC⟩ : ∃ C : ℝ, 0 < C ∧ ∀ m : Fin n → ℤ, ‖a m‖ ≤ C * weight n (-(N / 2 : ℝ))
      m := by
    exact h N;
  -- Then weight n s m * ‖a m‖^2 ≤ C^2 * weight n (s - N) m.
  have h_bound : ∀ m : Fin n → ℤ, weight n s m * ‖a m‖^2 ≤ C^2 * weight n (s - N) m := by
    intro m
    have h_bound_step : weight n s m * ‖a m‖^2 ≤ C^2 * weight n s m * weight n (-(N / 2 : ℝ))
        m^2 := by
      convert mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( norm_nonneg _ ) ( hC m ) 2 ) ( show
          0 ≤ weight n s m by exact le_of_lt ( weight_pos s m ) ) using 1
      all_goals (first | rfl | ring)
    have hXp : (0 : ℝ) < 1 + ∑ i : Fin n, ((m i : ℝ) ^ 2) :=
      add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have h_weight_split : weight n (s - ↑N) m = weight n s m * weight n (-(↑N / 2 : ℝ)) m ^ 2 := by
      unfold weight
      rw [pow_two, ← Real.rpow_add hXp, ← Real.rpow_add hXp]
      congr 1; ring
    calc weight n s m * ‖a m‖^2
        ≤ C^2 * weight n s m * weight n (-(↑N / 2 : ℝ)) m ^ 2 := h_bound_step
      _ = C^2 * weight n (s - ↑N) m := by rw [h_weight_split]; ring
  refine Summable.of_nonneg_of_le ( fun m => mul_nonneg ( weight_nonneg _ _ ) ( sq_nonneg _ ) )
      ( fun m => h_bound m ) ?_;
  refine Summable.mul_left _ ?_;
  have h_pos : (n : ℝ) < 2 * ((↑N : ℝ) - s) := by linarith
  have h_sum := summable_weight_neg (s := (↑N : ℝ) - s) hn h_pos
  convert h_sum using 1
  all_goals (first | rfl | (funext m; simp only [weight]; congr 1; ring))

/-! ## Transport to the unit torus -/

/-- The quotient map `ℝⁿ → (ℝ/ℤ)ⁿ`, coordinatewise. -/
def toUnitTorus (n : ℕ) (x : Fin n → ℝ) : UnitAddTorus (Fin n) :=
  fun i => ((x i : ℝ) : AddCircle (1 : ℝ))

lemma toUnitTorus_isOpenQuotientMap : IsOpenQuotientMap (toUnitTorus n) :=
  IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)

lemma continuous_toUnitTorus : Continuous (toUnitTorus n) :=
  toUnitTorus_isOpenQuotientMap.continuous

/-- Every point of `ℝⁿ` differs from the `Quotient.out` representative of its image by an
integer vector. -/
lemma exists_out_toUnitTorus_eq (x : Fin n → ℝ) :
    ∃ k : Fin n → ℤ, ∀ i, Quotient.out (toUnitTorus n x i) = x i - k i := by
  have h : ∀ i, ∃ k : ℤ, Quotient.out (toUnitTorus n x i) = x i - k := by
    intro i
    have h1 : ((Quotient.out (toUnitTorus n x i) : ℝ) : AddCircle (1 : ℝ)) = ((x i : ℝ) :
        AddCircle (1:ℝ)) :=
      QuotientAddGroup.out_eq' _
    rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff] at h1
    obtain ⟨k, hk⟩ := h1
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hk
    linarith
  choose k hk using h
  exact ⟨k, hk⟩

/-- `mFourier` at `toUnitTorus ((2π)⁻¹ • θ)` is `fourierExp n m θ`. -/
lemma mFourier_toUnitTorus (m : Fin n → ℤ) (θ : Fin n → ℝ) :
    UnitAddTorus.mFourier m (toUnitTorus n ((2 * π)⁻¹ • θ)) = fourierExp n m θ := by
  change ∏ i, fourier (m i) (((((2 * π)⁻¹ • θ) i : ℝ)) : AddCircle (1:ℝ)) = _
  simp only [fourier_coe_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Complex.exp_sum]
  unfold fourierExp
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- The descent of a `2πℤⁿ`-periodic function to the unit torus `(ℝ/ℤ)ⁿ`, via
`Quotient.out` representatives and the rescaling `x ↦ 2πx`. -/
def toUnitTorusFun (n : ℕ) (f : (Fin n → ℝ) → ℂ) (z : UnitAddTorus (Fin n)) : ℂ :=
  f (fun i => 2 * π * Quotient.out (z i))

lemma toUnitTorusFun_toUnitTorus {f : (Fin n → ℝ) → ℂ} (hper : IsPeriodic2Pi f)
    (x : Fin n → ℝ) :
    toUnitTorusFun n f (toUnitTorus n x) = f ((2 * π) • x) := by
  obtain ⟨k, hk⟩ := exists_out_toUnitTorus_eq x
  unfold toUnitTorusFun
  have h : (fun i => 2 * π * Quotient.out (toUnitTorus n x i))
      = (2 * π) • x + periodicShift n (-k) := by
    funext i
    simp only [hk i, Pi.add_apply, Pi.smul_apply, smul_eq_mul, periodicShift, Pi.neg_apply,
      Int.cast_neg]
    ring
  rw [h, hper]

lemma continuous_toUnitTorusFun {f : (Fin n → ℝ) → ℂ} (hf : Continuous f)
    (hper : IsPeriodic2Pi f) : Continuous (toUnitTorusFun n f) := by
  rw [toUnitTorus_isOpenQuotientMap.isQuotientMap.continuous_iff]
  have h : toUnitTorusFun n f ∘ toUnitTorus n = fun x => f ((2 * π) • x) :=
    funext fun x => toUnitTorusFun_toUnitTorus hper x
  rw [h]
  exact hf.comp (continuous_const_smul (2 * π))

/-- The descent as a continuous map on the unit torus. -/
def toUnitTorusCM (n : ℕ) (f : (Fin n → ℝ) → ℂ) (hf : Continuous f) (hper : IsPeriodic2Pi f) :
    C(UnitAddTorus (Fin n), ℂ) :=
  ⟨toUnitTorusFun n f, continuous_toUnitTorusFun hf hper⟩

/-! ## The torus integral as a cube integral -/

lemma measurePreserving_toUnitTorus :
    MeasurePreserving (toUnitTorus n)
      (volume.restrict (Set.pi Set.univ fun _ : Fin n => Set.Ioc (0 : ℝ) 1))
      (Measure.pi fun _ : Fin n => AddCircle.haarAddCircle) := by
  have h1 : ∀ _ : Fin n, MeasurePreserving (fun x : ℝ => (x : AddCircle (1 : ℝ)))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) AddCircle.haarAddCircle := by
    intro i
    have h := AddCircle.measurePreserving_mk (1 : ℝ) 0
    rw [zero_add] at h
    have hv : (volume : Measure (AddCircle (1 : ℝ))) = AddCircle.haarAddCircle := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]; simp
    rwa [hv] at h
  have h2 := measurePreserving_pi (fun _ : Fin n => volume.restrict (Set.Ioc (0 : ℝ) 1))
    (fun _ : Fin n => AddCircle.haarAddCircle) h1
  rw [← Measure.restrict_pi_pi, ← volume_pi] at h2
  exact h2

lemma integral_toUnitTorus (G : UnitAddTorus (Fin n) → ℂ) (hG : Continuous G) :
    ∫ z, G z ∂(Measure.pi fun _ : Fin n => AddCircle.haarAddCircle)
      = ∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Ioc (0 : ℝ) 1), G (toUnitTorus n x) := by
  rw [← measurePreserving_toUnitTorus.map_eq,
    integral_map continuous_toUnitTorus.aemeasurable hG.aestronglyMeasurable]

lemma integral_cube_scale (h : (Fin n → ℝ) → ℂ) :
    ∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Ioc (0 : ℝ) 1), h ((2 * π) • x)
      = ((2 * π) ^ n)⁻¹ • ∫ y in Set.pi Set.univ (fun _ : Fin n => Set.Ioc (0 : ℝ) (2 * π)), h y
          := by
  have hS : MeasurableSet (Set.pi Set.univ (fun _ : Fin n => Set.Ioc (0 : ℝ) 1)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioc
  have hS' : MeasurableSet (Set.pi Set.univ (fun _ : Fin n => Set.Ioc (0 : ℝ) (2 * π))) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioc
  rw [← integral_indicator hS, ← integral_indicator hS']
  have hind : ∀ x, (Set.pi Set.univ (fun _ : Fin n => Set.Ioc (0 : ℝ) 1)).indicator
        (fun x => h ((2 * π) • x)) x
      = (Set.pi Set.univ (fun _ : Fin n => Set.Ioc (0 : ℝ) (2 * π))).indicator h ((2 * π) • x) := by
    intro x
    have hmem : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Ioc (0 : ℝ) 1)
        ↔ (2 * π) • x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Ioc (0 : ℝ) (2 * π)) := by
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioc, Pi.smul_apply, smul_eq_mul]
      constructor <;> intro hx i <;> obtain ⟨h1, h2⟩ := hx i <;> constructor <;>
        nlinarith [Real.pi_pos]
    by_cases hx : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Ioc (0 : ℝ) 1)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mp hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (hmem.mpr h'))]
  simp_rw [hind]
  rw [Measure.integral_comp_smul_of_nonneg (μ := volume) _ (2 * π) (hR := by positivity),
    Module.finrank_fin_fun]

lemma integral_Ioc_cube_eq_Icc (h : (Fin n → ℝ) → ℂ) :
    ∫ y in Set.pi Set.univ (fun _ : Fin n => Set.Ioc (0 : ℝ) (2 * π)), h y
      = ∫ y in Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ)), h y := by
  apply setIntegral_congr_set
  have h1 : (Set.pi Set.univ (fun _ : Fin n => Set.Ioc (0 : ℝ) (2 * π)))
      = Set.pi Set.univ (fun i => Set.Ioc ((0 : Fin n → ℝ) i) ((2 * π • (1 : Fin n → ℝ)) i)) := by
    congr; funext i; simp
  have h2 : Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ))
      = Set.pi Set.univ (fun i => Set.Icc ((0 : Fin n → ℝ) i) ((2 * π • (1 : Fin n → ℝ)) i)) :=
    (Set.pi_univ_Icc _ _).symm
  rw [h1, h2, volume_pi]
  exact Measure.pi_Ioc_ae_eq_pi_Icc

/-- The multivariate Fourier coefficients of the descent are the standard Fourier coefficients. -/
lemma mFourierCoeff_toUnitTorusCM {f : (Fin n → ℝ) → ℂ} (hf : Continuous f)
    (hper : IsPeriodic2Pi f) (m : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff (⇑(toUnitTorusCM n f hf hper)) m = stdFourierCoeff n f m := by
  change ∫ z, UnitAddTorus.mFourier (-m) z • toUnitTorusFun n f z
      ∂(Measure.pi fun _ : Fin n => AddCircle.haarAddCircle) = _
  rw [integral_toUnitTorus (fun z => UnitAddTorus.mFourier (-m) z • toUnitTorusFun n f z)
    (by
      have hc := (UnitAddTorus.mFourier (-m)).continuous.smul
        (continuous_toUnitTorusFun hf hper)
      exact hc)]
  have hpt : ∀ x, UnitAddTorus.mFourier (-m) (toUnitTorus n x) • toUnitTorusFun n f (toUnitTorus
      n x)
      = (fun y => f y * fourierExp n (-m) y) ((2 * π) • x) := by
    intro x
    rw [toUnitTorusFun_toUnitTorus hper, smul_eq_mul, mul_comm]
    congr 1
    have h := mFourier_toUnitTorus (-m) ((2 * π) • x)
    rw [smul_smul, inv_mul_cancel₀ (by positivity), one_smul] at h
    exact h
  simp_rw [hpt]
  have hsc := integral_cube_scale (n := n) (fun y => f y * fourierExp n (-m) y)
  rw [hsc, integral_Ioc_cube_eq_Icc]
  unfold stdFourierCoeff
  rw [Complex.real_smul]
  push_cast
  rfl

/-! ## Translation invariance of the period-cube integral for periodic functions -/

/-- Additivity of `fourierExp` in the point variable. -/
lemma fourierExp_add_point (c : Fin n → ℤ) (a b : Fin n → ℝ) :
    fourierExp n c (a + b) = fourierExp n c a * fourierExp n c b := by
  unfold fourierExp
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply]
  push_cast
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Translating the domain of a set integral over a box. -/
lemma integral_Icc_comp_add_right (h : (Fin n → ℝ) → ℂ) (a b c : Fin n → ℝ) :
    ∫ x in Set.Icc b c, h (x + a) = ∫ x in Set.Icc (b + a) (c + a), h x := by
  rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Icc]
  have hpre : Set.Icc b c = (fun x => x + a) ⁻¹' Set.Icc (b + a) (c + a) := by
    rw [Set.preimage_add_const_Icc]; simp
  have hind : ∀ x, (Set.Icc b c).indicator (fun x => h (x + a)) x
      = (Set.Icc (b + a) (c + a)).indicator h (x + a) := by
    intro x
    rw [hpre]
    exact Set.indicator_comp_right (fun x => x + a) (g := h)
  simp_rw [hind]
  exact integral_add_right_eq_self _ a

/-- The period-cube integral of a continuous periodic function equals `(2π)ⁿ` times the
Haar integral of its descent to the unit torus. -/
lemma integral_periodCube_eq_torus {g : (Fin n → ℝ) → ℂ} (hg : Continuous g)
    (hper : IsPeriodic2Pi g) :
    ∫ θ in Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ)), g θ
      = ((2 * π) ^ n : ℝ) • ∫ z, toUnitTorusFun n g z
          ∂(Measure.pi fun _ : Fin n => AddCircle.haarAddCircle) := by
  rw [integral_toUnitTorus _ (continuous_toUnitTorusFun hg hper)]
  simp_rw [toUnitTorusFun_toUnitTorus hper]
  rw [integral_cube_scale, integral_Ioc_cube_eq_Icc, smul_smul,
    mul_inv_cancel₀ (by positivity), one_smul]

/-- Integers witnessing equality in `AddCircle 1`. -/
lemma exists_int_of_coe_eq {x y : ℝ} (h : ((x : ℝ) : AddCircle (1 : ℝ)) = (y : AddCircle (1 : ℝ))) :
    ∃ k : ℤ, y = x + k := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  simp only [zsmul_eq_mul, mul_one] at hk
  linarith

/-- The descent of a translate is the translate of the descent. -/
lemma toUnitTorusFun_comp_add {g : (Fin n → ℝ) → ℂ} (hper : IsPeriodic2Pi g)
    (a : Fin n → ℝ) (z : UnitAddTorus (Fin n)) :
    toUnitTorusFun n (fun θ => g (θ + a)) z
      = toUnitTorusFun n g (toUnitTorus n ((2 * π)⁻¹ • a) + z) := by
  unfold toUnitTorusFun
  have h : ∀ i, ∃ k : ℤ, Quotient.out ((toUnitTorus n ((2 * π)⁻¹ • a) + z) i)
      = Quotient.out (z i) + (2 * π)⁻¹ * a i + k := by
    intro i
    have h1 : ((Quotient.out (z i) + (2 * π)⁻¹ * a i : ℝ) : AddCircle (1:ℝ))
        = ((Quotient.out ((toUnitTorus n ((2 * π)⁻¹ • a) + z) i) : ℝ) : AddCircle (1:ℝ)) := by
      rw [QuotientAddGroup.out_eq', Pi.add_apply]
      unfold toUnitTorus
      rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', add_comm]
      simp only [Pi.smul_apply, smul_eq_mul]
    exact exists_int_of_coe_eq h1
  choose k hk using h
  have h2 : (fun i => 2 * π * Quotient.out ((toUnitTorus n ((2 * π)⁻¹ • a) + z) i))
      = (fun i => 2 * π * Quotient.out (z i)) + a + periodicShift n k := by
    funext i
    rw [hk i]
    simp only [Pi.add_apply, periodicShift]
    field_simp
  rw [h2, hper]

/-- Translation invariance of the period-cube integral for continuous periodic functions. -/
lemma integral_periodCube_add_right {g : (Fin n → ℝ) → ℂ} (hg : Continuous g)
    (hper : IsPeriodic2Pi g) (a : Fin n → ℝ) :
    ∫ θ in Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ)), g (θ + a)
      = ∫ θ in Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ)), g θ := by
  have hper' : IsPeriodic2Pi (fun θ => g (θ + a)) := by
    intro x k
    change g (x + periodicShift n k + a) = g (x + a)
    rw [add_right_comm, hper]
  rw [integral_periodCube_eq_torus (g := fun θ => g (θ + a))
    (hg.comp (continuous_id.add continuous_const)) hper', integral_periodCube_eq_torus hg hper]
  congr 1
  simp_rw [toUnitTorusFun_comp_add hper a]
  exact integral_add_left_eq_self (μ := Measure.pi fun _ : Fin n => AddCircle.haarAddCircle)
    (toUnitTorusFun n g) _

/-- Any translate of the period cube gives the same integral of a continuous periodic function. -/
lemma integral_periodCube_translate {g : (Fin n → ℝ) → ℂ} (hg : Continuous g)
    (hper : IsPeriodic2Pi g) (a : Fin n → ℝ) :
    ∫ θ in Set.Icc a (a + 2 * π • (1 : Fin n → ℝ)), g θ
      = ∫ θ in Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ)), g θ := by
  rw [← integral_periodCube_add_right hg hper a, integral_Icc_comp_add_right, zero_add, add_comm]

/-! ## Summability and inversion -/

lemma summable_stdFourierCoeff_of_smoothPeriodic (hn : 0 < n) {f : (Fin n → ℝ) → ℂ}
    (hsmooth : ContDiff ℝ ∞ f) (hper : IsPeriodic2Pi f) :
    Summable (stdFourierCoeff n f) := by
  obtain ⟨C, _, hbound⟩ := stdFourierCoeff_rapid_decay hn hsmooth hper (n + 1)
  refine Summable.of_norm_bounded (g := fun m => C * weight n (-(((n + 1 : ℕ) : ℝ) / 2)) m) ?_
      hbound
  refine Summable.mul_left C ?_
  apply summable_weight_neg hn
  push_cast
  linarith

/-! ## Fourier inversion for smooth periodic functions -/

/-- For a smooth `2πℤⁿ`-periodic complex-valued function `f`, Fourier
    synthesis applied to its standard Fourier coefficients recovers `f`. -/
lemma fourierSynthesis_stdFourierCoeff_of_smoothPeriodic
    (hn : 0 < n) {f : (Fin n → ℝ) → ℂ}
    (hsmooth : ContDiff ℝ ∞ f) (hper : IsPeriodic2Pi f) :
    ∀ y, fourierSynthesis n (stdFourierCoeff n f) y = f y := by
  intro y
  have hf := hsmooth.continuous
  have heq : UnitAddTorus.mFourierCoeff (⇑(toUnitTorusCM n f hf hper)) = stdFourierCoeff n f :=
    funext (mFourierCoeff_toUnitTorusCM hf hper)
  have hsum : Summable (UnitAddTorus.mFourierCoeff (⇑(toUnitTorusCM n f hf hper))) := by
    rw [heq]; exact summable_stdFourierCoeff_of_smoothPeriodic hn hsmooth hper
  have hx := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsum
    (toUnitTorus n ((2 * π)⁻¹ • y))
  rw [heq] at hx
  have hval : (toUnitTorusCM n f hf hper) (toUnitTorus n ((2 * π)⁻¹ • y)) = f y := by
    change toUnitTorusFun n f (toUnitTorus n ((2 * π)⁻¹ • y)) = f y
    rw [toUnitTorusFun_toUnitTorus hper, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
  rw [hval] at hx
  simp_rw [mFourier_toUnitTorus, smul_eq_mul] at hx
  unfold fourierSynthesis
  exact hx.tsum_eq

/-
A smooth `2πℤⁿ`-periodic function lies in `MemSobolevDistrib n s` for
    every `s ∈ ℝ`.
-/
lemma smooth_periodic_memSobolevDistrib (hn : 0 < n)
    {f : (Fin n → ℝ) → ℂ} (hsmooth : ContDiff ℝ ∞ f)
    (hper : IsPeriodic2Pi f) (s : ℝ) :
    MemSobolevDistrib n s (integrationEmbed n f) := by
  unfold MemSobolevDistrib
  rw [fourierCoeffDistrib_integrationEmbed]
  exact memSobolev_of_rapid_decay hn (stdFourierCoeff_rapid_decay hn hsmooth hper) s

end NashEmbedding.Sobolev

end
