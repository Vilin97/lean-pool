/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.HardyLittlewoodMaximal
import LeanPool.QuadraticCarleson.QuadraticCarleson.HilbertL2Fourier
import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticFixedHeightAveragingNorm

/-!
# Maximal tails of separated quadratic frequency pieces

This file isolates the frequency-projection part of the direct quadratic
one-node argument.  A finite tail is written as the total sum minus a
prefix.  If every prefix is a smooth low-pass projection of the total sum,
and the low-pass kernels are pointwise dominated by a fixed multiple of the
centered Hardy--Littlewood maximal function, then the whole family of tails
has a cardinality-free `L²` bound.

The application-specific input may be supplied either pointwise through
`HasLowPassPrefixControl` or almost everywhere through
`HasAELowPassPrefixControl`.  The latter is the natural interface for `L²`
Fourier multipliers.  No maximal-tail theorem or orthogonality principle is
assumed here.
-/

open Function MeasureTheory Set FourierTransform Metric
open scoped ENNReal NNReal ComplexConjugate

namespace QuadraticCarleson.KrauseLaceyQuadraticAnnularTail


noncomputable section

/-- The pointwise total of a finite sequence of frequency pieces. -/
def finitePieceTotal (N : ℕ) (u : ℕ → ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ j ∈ Finset.range N, u j x

/-- The prefix strictly below `n`. -/
def finitePiecePrefix (u : ℕ → ℝ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ Finset.range n, u j x

/-- The finite tail beginning at `n`, represented as total minus prefix.
For `n ≤ N` this is exactly `∑_{n ≤ j < N} u_j`. -/
def finitePieceTail (N : ℕ) (u : ℕ → ℝ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  finitePieceTotal N u x - finitePiecePrefix u n x

theorem finitePieceTail_eq_sum_Ico
    {N n : ℕ} (hn : n ≤ N) (u : ℕ → ℝ → ℂ) (x : ℝ) :
    finitePieceTail N u n x = ∑ j ∈ Finset.Ico n N, u j x := by
  have hsplit := Finset.sum_range_add_sum_Ico (fun j ↦ u j x) hn
  unfold finitePieceTail finitePieceTotal finitePiecePrefix
  rw [← hsplit]
  abel

/-- The maximum of the tails beginning at `0, ..., N`. -/
def finitePieceTailMax (N : ℕ) (u : ℕ → ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  (Finset.range (N + 1)).sup fun n ↦ ‖finitePieceTail N u n x‖ₑ

/-- The exact pointwise input supplied by smooth low-pass projections.
The constant is in `ℝ≥0∞` so it composes directly with the project's
maximal-function estimate. -/
def HasLowPassPrefixControl (N : ℕ) (u : ℕ → ℝ → ℂ) (A : ℝ≥0∞) : Prop :=
  ∀ n ≤ N, ∀ x,
    ‖finitePiecePrefix u n x‖ₑ ≤
      A * centeredHardyLittlewoodMaximal
        (fun y ↦ ‖finitePieceTotal N u y‖ₑ) x

/-- The measure-theoretically natural version of low-pass prefix control.
Fourier multiplier identities in `L²` determine representatives only almost
everywhere, and this is sufficient for every subsequent `lintegral` estimate. -/
def HasAELowPassPrefixControl (N : ℕ) (u : ℕ → ℝ → ℂ) (A : ℝ≥0∞) : Prop :=
  ∀ n ≤ N, ∀ᵐ x : ℝ ∂volume,
    ‖finitePiecePrefix u n x‖ₑ ≤
      A * centeredHardyLittlewoodMaximal
        (fun y ↦ ‖finitePieceTotal N u y‖ₑ) x

theorem HasLowPassPrefixControl.ae
    {N : ℕ} {u : ℕ → ℝ → ℂ} {A : ℝ≥0∞}
    (h : HasLowPassPrefixControl N u A) :
    HasAELowPassPrefixControl N u A := by
  intro n hn
  exact ae_of_all _ (h n hn)

/-- Convolution with a kernel supported in a centered rational interval and
bounded by `A / (2r)` is pointwise controlled by `A` times the centered
Hardy--Littlewood maximal function.  This is the basic estimate used for
each smooth low-pass cutoff after decomposing its rapidly decaying kernel
into centered dyadic shells. -/
theorem enorm_convolution_le_maximal_of_supported_kernel
    (q : PositiveRational) {A : ℝ≥0∞} {K f : ℝ → ℂ}
    (hf : Measurable f)
    (hKsupport : Function.support K ⊆ closedBall (0 : ℝ) (q : ℝ))
    (hKnorm : ∀ t, ‖K t‖ₑ ≤ A / ENNReal.ofReal (2 * (q : ℝ)))
    (x : ℝ) :
    ‖∫ y, K (x - y) * f y‖ₑ ≤
      A * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
  let r : ℝ := q
  let d : ℝ≥0∞ := ENNReal.ofReal (2 * r)
  have hr : 0 < r := by
    have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.property
    simpa only [r] using this
  have hd0 : d ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hdtop : d ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpoint (y : ℝ) :
      ‖K (x - y) * f y‖ₑ ≤
        (closedBall x r).indicator (fun z ↦ (A / d) * ‖f z‖ₑ) y := by
    by_cases hy : y ∈ closedBall x r
    · rw [indicator_of_mem hy, enorm_mul]
      exact mul_le_mul' (by simpa [d, r] using hKnorm (x - y)) le_rfl
    · rw [indicator_of_notMem hy]
      have hzero : K (x - y) = 0 := by
        by_contra hne
        have hb := hKsupport hne
        apply hy
        simpa only [mem_closedBall, Real.dist_eq, sub_zero, abs_sub_comm] using hb
      simp [hzero]
  calc
    ‖∫ y, K (x - y) * f y‖ₑ ≤ ∫⁻ y, ‖K (x - y) * f y‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y, (closedBall x r).indicator
        (fun z ↦ (A / d) * ‖f z‖ₑ) y := lintegral_mono hpoint
    _ = (A / d) * ∫⁻ y in closedBall x r, ‖f y‖ₑ := by
      rw [lintegral_indicator measurableSet_closedBall]
      exact lintegral_const_mul'' (A / d)
        (hf.enorm.aemeasurable.restrict)
    _ = A * centeredAverage r (fun y ↦ ‖f y‖ₑ) x := by
      simp only [centeredAverage]
      rw [show ENNReal.ofReal (2 * r) = d from rfl]
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ A * centeredHardyLittlewoodMaximal (fun y ↦ ‖f y‖ₑ) x := by
      apply mul_le_mul' le_rfl
      exact le_iSup (fun q' : PositiveRational ↦
        centeredAverage (q' : ℝ) (fun y ↦ ‖f y‖ₑ) x) q

/-- A concrete way to discharge `HasLowPassPrefixControl`: each prefix is
identified with convolution by a compact centered low-pass kernel with the
same uniform normalized size bound. -/
theorem hasLowPassPrefixControl_of_kernel_representation
    {N : ℕ} {u : ℕ → ℝ → ℂ} {A : ℝ≥0∞}
    (hu : ∀ j, Measurable (u j))
    (q : ℕ → PositiveRational) (K : ℕ → ℝ → ℂ)
    (hprefix : ∀ n ≤ N, ∀ x,
      finitePiecePrefix u n x =
        ∫ y, K n (x - y) * finitePieceTotal N u y)
    (hKsupport : ∀ n ≤ N,
      Function.support (K n) ⊆ closedBall (0 : ℝ) (q n : ℝ))
    (hKnorm : ∀ n ≤ N, ∀ t,
      ‖K n t‖ₑ ≤ A / ENNReal.ofReal (2 * (q n : ℝ))) :
    HasLowPassPrefixControl N u A := by
  intro n hn x
  rw [hprefix n hn x]
  have htotal : Measurable (finitePieceTotal N u) := by
    classical
    unfold finitePieceTotal
    exact Finset.measurable_sum _ fun j _ ↦ hu j
  exact enorm_convolution_le_maximal_of_supported_kernel (q n)
    htotal
    (hKsupport n hn) (hKnorm n hn) x

theorem finitePieceTailMax_le_total_add_maximal
    {N : ℕ} {u : ℕ → ℝ → ℂ} {A : ℝ≥0∞}
    (hprefix : HasLowPassPrefixControl N u A) (x : ℝ) :
    finitePieceTailMax N u x ≤
      ‖finitePieceTotal N u x‖ₑ +
        A * centeredHardyLittlewoodMaximal
          (fun y ↦ ‖finitePieceTotal N u y‖ₑ) x := by
  apply Finset.sup_le
  intro n hn
  have hnN : n ≤ N := by
    simpa only [Finset.mem_range] using Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  exact enorm_sub_le.trans
    (add_le_add le_rfl (hprefix n hnN x))

/-- Almost-everywhere tail domination from almost-everywhere prefix control.
The exceptional sets for the finitely many prefixes are intersected before
taking the finite supremum. -/
theorem finitePieceTailMax_le_total_add_maximal_ae
    {N : ℕ} {u : ℕ → ℝ → ℂ} {A : ℝ≥0∞}
    (hprefix : HasAELowPassPrefixControl N u A) :
    ∀ᵐ x : ℝ ∂volume,
      finitePieceTailMax N u x ≤
        ‖finitePieceTotal N u x‖ₑ +
          A * centeredHardyLittlewoodMaximal
            (fun y ↦ ‖finitePieceTotal N u y‖ₑ) x := by
  have hall : ∀ᵐ x : ℝ ∂volume,
      ∀ n ∈ Finset.range (N + 1),
        ‖finitePiecePrefix u n x‖ₑ ≤
          A * centeredHardyLittlewoodMaximal
            (fun y ↦ ‖finitePieceTotal N u y‖ₑ) x := by
    rw [Filter.eventually_all_finset]
    intro n hn
    exact hprefix n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
  filter_upwards [hall] with x hx
  apply Finset.sup_le
  intro n hn
  exact enorm_sub_le.trans (add_le_add le_rfl (hx n hn))

theorem measurable_finitePieceTotal {N : ℕ} {u : ℕ → ℝ → ℂ}
    (hu : ∀ j < N, Measurable (u j)) :
    Measurable (finitePieceTotal N u) := by
  classical
  unfold finitePieceTotal
  exact Finset.measurable_sum _ fun j hj ↦ hu j (Finset.mem_range.mp hj)

theorem measurable_finitePiecePrefix {u : ℕ → ℝ → ℂ}
    (hu : ∀ j, Measurable (u j)) (n : ℕ) :
    Measurable (finitePiecePrefix u n) := by
  classical
  unfold finitePiecePrefix
  exact Finset.measurable_sum _ fun j _ ↦ hu j

theorem measurable_finitePieceTail {N : ℕ} {u : ℕ → ℝ → ℂ}
    (hu : ∀ j, Measurable (u j)) (n : ℕ) :
    Measurable (finitePieceTail N u n) :=
  (measurable_finitePieceTotal fun j _ ↦ hu j).sub
    (measurable_finitePiecePrefix hu n)

theorem measurable_finitePieceTailMax {N : ℕ} {u : ℕ → ℝ → ℂ}
    (hu : ∀ j, Measurable (u j)) :
    Measurable (finitePieceTailMax N u) := by
  classical
  unfold finitePieceTailMax
  induction Finset.range (N + 1) using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
      simp only [Finset.sup_insert]
      exact (measurable_finitePieceTail hu n).enorm.max ih

/-- Almost-everywhere measurable version of
`measurable_finitePieceTailMax`, suitable for pieces represented in `L²`. -/
theorem aemeasurable_finitePieceTailMax {N : ℕ} {u : ℕ → ℝ → ℂ}
    (hu : ∀ j, AEMeasurable (u j) volume) :
    AEMeasurable (finitePieceTailMax N u) volume := by
  have htotal : AEMeasurable (finitePieceTotal N u) volume := by
    classical
    unfold finitePieceTotal
    exact (Finset.aemeasurable_sum (Finset.range N) fun j _ ↦ hu j).congr
      (ae_of_all _ fun x ↦ by simp only [Finset.sum_apply])
  have hprefix (n : ℕ) : AEMeasurable (finitePiecePrefix u n) volume := by
    classical
    unfold finitePiecePrefix
    exact (Finset.aemeasurable_sum (Finset.range n) fun j _ ↦ hu j).congr
      (ae_of_all _ fun x ↦ by simp only [Finset.sum_apply])
  have htail (n : ℕ) : AEMeasurable (finitePieceTail N u n) volume := by
    unfold finitePieceTail
    exact htotal.sub (hprefix n)
  classical
  unfold finitePieceTailMax
  induction Finset.range (N + 1) using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
      simp only [Finset.sup_insert]
      exact (htail n).enorm.max ih

private theorem ennreal_add_sq_le_four_sum_sq (a b : ℝ≥0∞) :
    (a + b) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by
  have hab : a + b ≤ 2 * max a b := by
    calc
      a + b ≤ max a b + max a b :=
        add_le_add (le_max_left a b) (le_max_right a b)
      _ = 2 * max a b := by ring
  have hmax : (max a b) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    by_cases h : a ≤ b
    · rw [max_eq_right h]
      exact le_add_left le_rfl
    · rw [max_eq_left (le_of_not_ge h)]
      exact le_add_right le_rfl
  calc
    (a + b) ^ 2 ≤ (2 * max a b) ^ 2 := pow_le_pow_left' hab 2
    _ = 4 * (max a b) ^ 2 := by ring
    _ ≤ 4 * (a ^ 2 + b ^ 2) := mul_le_mul' le_rfl hmax

/-- Cardinality-free maximal-tail `L²` estimate.  The explicit coefficient
is `4 + 128 A²`, coming from a top-safe ENNReal square estimate and the proved centered
Hardy--Littlewood constant `32`. -/
theorem finitePieceTailMax_sq_lintegral_le
    {N : ℕ} {u : ℕ → ℝ → ℂ} {A : ℝ≥0∞}
    (hu : ∀ j, Measurable (u j))
    (hprefix : HasLowPassPrefixControl N u A) :
    (∫⁻ x, finitePieceTailMax N u x ^ 2) ≤
      (4 + 128 * A ^ 2) *
        ∫⁻ x, ‖finitePieceTotal N u x‖ₑ ^ 2 := by
  let F : ℝ → ℝ≥0∞ := fun x ↦ ‖finitePieceTotal N u x‖ₑ
  let M : ℝ → ℝ≥0∞ := centeredHardyLittlewoodMaximal F
  have hF : Measurable F :=
    (measurable_finitePieceTotal fun j _ ↦ hu j).enorm
  have hpoint (x : ℝ) :
      finitePieceTailMax N u x ^ 2 ≤
        4 * (F x ^ 2 + (A * M x) ^ 2) := by
    exact (pow_le_pow_left' (finitePieceTailMax_le_total_add_maximal hprefix x) 2).trans
      (ennreal_add_sq_le_four_sum_sq (F x) (A * M x))
  calc
    (∫⁻ x, finitePieceTailMax N u x ^ 2) ≤
        ∫⁻ x, 4 * (F x ^ 2 + (A * M x) ^ 2) :=
      lintegral_mono hpoint
    _ = 4 * ((∫⁻ x, F x ^ 2) + A ^ 2 * ∫⁻ x, M x ^ 2) := by
      simp_rw [mul_pow]
      rw [lintegral_const_mul' _ _ (by norm_num),
        lintegral_add_left (hF.pow_const 2)]
      rw [lintegral_const_mul'' (A ^ 2)
        ((measurable_centeredHardyLittlewoodMaximal hF).pow_const 2).aemeasurable]
    _ ≤ 4 * ((∫⁻ x, F x ^ 2) + A ^ 2 * (32 * ∫⁻ x, F x ^ 2)) := by
      gcongr
      exact centeredHardyLittlewoodMaximal_sq_lintegral_le hF
    _ = (4 + 128 * A ^ 2) * ∫⁻ x, F x ^ 2 := by ring

/-- Cardinality-free maximal-tail `L²` estimate from almost-everywhere
low-pass prefix control.  This is the form used by Fourier multiplier
applications, whose canonical representatives agree only almost everywhere. -/
theorem finitePieceTailMax_sq_lintegral_le_ae
    {N : ℕ} {u : ℕ → ℝ → ℂ} {A : ℝ≥0∞}
    (hu : ∀ j, Measurable (u j))
    (hprefix : HasAELowPassPrefixControl N u A) :
    (∫⁻ x, finitePieceTailMax N u x ^ 2) ≤
      (4 + 128 * A ^ 2) *
        ∫⁻ x, ‖finitePieceTotal N u x‖ₑ ^ 2 := by
  let F : ℝ → ℝ≥0∞ := fun x ↦ ‖finitePieceTotal N u x‖ₑ
  let M : ℝ → ℝ≥0∞ := centeredHardyLittlewoodMaximal F
  have hF : Measurable F :=
    (measurable_finitePieceTotal fun j _ ↦ hu j).enorm
  have hpoint : ∀ᵐ x : ℝ ∂volume,
      finitePieceTailMax N u x ^ 2 ≤
        4 * (F x ^ 2 + (A * M x) ^ 2) := by
    filter_upwards [finitePieceTailMax_le_total_add_maximal_ae hprefix] with x hx
    exact (pow_le_pow_left' hx 2).trans
      (ennreal_add_sq_le_four_sum_sq (F x) (A * M x))
  calc
    (∫⁻ x, finitePieceTailMax N u x ^ 2) ≤
        ∫⁻ x, 4 * (F x ^ 2 + (A * M x) ^ 2) :=
      lintegral_mono_ae hpoint
    _ = 4 * ((∫⁻ x, F x ^ 2) + A ^ 2 * ∫⁻ x, M x ^ 2) := by
      simp_rw [mul_pow]
      rw [lintegral_const_mul' _ _ (by norm_num),
        lintegral_add_left (hF.pow_const 2)]
      rw [lintegral_const_mul'' (A ^ 2)
        ((measurable_centeredHardyLittlewoodMaximal hF).pow_const 2).aemeasurable]
    _ ≤ 4 * ((∫⁻ x, F x ^ 2) + A ^ 2 * (32 * ∫⁻ x, F x ^ 2)) := by
      gcongr
      exact centeredHardyLittlewoodMaximal_sq_lintegral_le hF
    _ = (4 + 128 * A ^ 2) * ∫⁻ x, F x ^ 2 := by ring

/-- Fourier separation formulated on the canonical measurable `L²`
representatives: different pieces have pointwise-zero Fourier inner product
almost everywhere. -/
def HasPairwiseSeparatedFourierSupport
    {ι : Type*} (v : ι → Lp (α := ℝ) ℂ 2 volume) : Prop :=
  ∀ i j, i ≠ j →
    ∀ᵐ ξ : ℝ ∂volume,
      inner ℂ ((Lp.fourierTransformₗᵢ ℝ ℂ (v i)) ξ)
        ((Lp.fourierTransformₗᵢ ℝ ℂ (v j)) ξ) = 0

/-- A canonical `L²` function has Fourier support in `E`, in the
measure-theoretically correct almost-everywhere sense. -/
def HasFourierSupportIn (v : Lp (α := ℝ) ℂ 2 volume) (E : Set ℝ) : Prop :=
  ∀ᵐ ξ : ℝ ∂volume, ξ ∉ E →
    (Lp.fourierTransformₗᵢ ℝ ℂ v) ξ = 0

/-- Pairwise disjoint measurable-frequency regions imply the Fourier
orthogonality predicate used below.  Thus callers may work with literal
annuli instead of proving inner products directly. -/
theorem hasPairwiseSeparatedFourierSupport_of_disjoint_regions
    {ι : Type*} (v : ι → Lp (α := ℝ) ℂ 2 volume) (E : ι → Set ℝ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j))
    (hsupport : ∀ i, HasFourierSupportIn (v i) (E i)) :
    HasPairwiseSeparatedFourierSupport v := by
  intro i j hij
  filter_upwards [hsupport i, hsupport j] with ξ hi hj
  by_cases hξ : ξ ∈ E i
  · have hξj : ξ ∉ E j := fun hξj ↦ Set.disjoint_left.mp (hdisj i j hij) hξ hξj
    rw [hj hξj, inner_zero_right]
  · rw [hi hξ, inner_zero_left]

theorem inner_eq_zero_of_separatedFourierSupport
    {ι : Type*} {v : ι → Lp (α := ℝ) ℂ 2 volume}
    (hsep : HasPairwiseSeparatedFourierSupport v)
    {i j : ι} (hij : i ≠ j) :
    inner ℂ (v i) (v j) = 0 := by
  rw [← Lp.inner_fourier_eq]
  rw [L2.inner_def]
  exact integral_eq_zero_of_ae (hsep i j hij)

/-- Pythagoras for a finite family with pairwise disjoint Fourier support.
This is the square-sum part of the annular argument, expressed directly in
the `L²` norm. -/
theorem norm_sum_sq_eq_sum_norm_sq_of_separatedFourierSupport
    {ι : Type*} (S : Finset ι)
    (v : ι → Lp (α := ℝ) ℂ 2 volume)
    (hsep : HasPairwiseSeparatedFourierSupport v) :
    ‖∑ i ∈ S, v i‖ ^ 2 = ∑ i ∈ S, ‖v i‖ ^ 2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      have hinner : inner ℂ (v a) (∑ i ∈ S, v i) = 0 := by
        rw [inner_sum]
        exact Finset.sum_eq_zero fun i hi ↦
          inner_eq_zero_of_separatedFourierSupport hsep
            (by intro hai; subst i; exact ha hi)
      calc
        ‖∑ i ∈ insert a S, v i‖ ^ 2 = ‖v a + ∑ i ∈ S, v i‖ ^ 2 := by
          rw [Finset.sum_insert ha]
        _ = ‖v a‖ ^ 2 + ‖∑ i ∈ S, v i‖ ^ 2 := by
          simpa only [pow_two] using
            norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
              (𝕜 := ℂ) (v a) (∑ i ∈ S, v i) hinner
        _ = ∑ i ∈ insert a S, ‖v i‖ ^ 2 := by rw [ih]; simp [ha]

private theorem toLp_finsetSum_eq_sum
    {ι : Type*} (S : Finset ι) {u : ι → ℝ → ℂ}
    (hu : ∀ i, MemLp (u i) 2 volume) :
    (memLp_finsetSum' S (fun i _ ↦ hu i)).toLp (∑ i ∈ S, u i) =
      ∑ i ∈ S, (hu i).toLp (u i) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact MemLp.toLp_zero _
  | @insert a S ha ih =>
      have hadd := MemLp.toLp_add (hu a)
        (memLp_finsetSum' S (fun i _ ↦ hu i))
      simpa only [Finset.sum_insert ha, ih] using hadd

theorem memLp_finitePieceTotal {N : ℕ} {u : ℕ → ℝ → ℂ}
    (hu : ∀ j, MemLp (u j) 2 volume) :
    MemLp (finitePieceTotal N u) 2 volume := by
  change MemLp (fun x ↦ ∑ j ∈ Finset.range N, u j x) 2 volume
  exact memLp_finsetSum (Finset.range N) fun j _ ↦ hu j

theorem toLp_finitePieceTotal_eq_sum {N : ℕ} {u : ℕ → ℝ → ℂ}
    (hu : ∀ j, MemLp (u j) 2 volume) :
    (memLp_finitePieceTotal hu).toLp (finitePieceTotal N u) =
      ∑ j ∈ Finset.range N, (hu j).toLp (u j) := by
  have hfun : finitePieceTotal N u = ∑ j ∈ Finset.range N, u j := by
    funext x
    simp only [finitePieceTotal, Finset.sum_apply]
  let hsum : MemLp (∑ j ∈ Finset.range N, u j) 2 volume :=
    memLp_finsetSum' (Finset.range N) fun j _ ↦ hu j
  exact (MemLp.toLp_congr (memLp_finitePieceTotal hu) hsum
      (ae_of_all _ fun x ↦ congrFun hfun x)).trans
    (toLp_finsetSum_eq_sum (Finset.range N) hu)

/-- Plancherel plus disjoint Fourier supports identifies the `L²` energy of
the total with the sum of the individual energies. -/
theorem eLpNorm_finitePieceTotal_sq_eq_sum
    {N : ℕ} {u : ℕ → ℝ → ℂ}
    (hu : ∀ j, MemLp (u j) 2 volume)
    (hsep : HasPairwiseSeparatedFourierSupport
      (fun j ↦ (hu j).toLp (u j))) :
    eLpNorm (finitePieceTotal N u) 2 volume ^ 2 =
      ∑ j ∈ Finset.range N, eLpNorm (u j) 2 volume ^ 2 := by
  let w : ℕ → Lp (α := ℝ) ℂ 2 volume := fun j ↦ (hu j).toLp (u j)
  have hnorm :
      ‖(memLp_finitePieceTotal hu).toLp (finitePieceTotal N u)‖ ^ 2 =
        ∑ j ∈ Finset.range N, ‖w j‖ ^ 2 := by
    rw [toLp_finitePieceTotal_eq_sum hu]
    exact norm_sum_sq_eq_sum_norm_sq_of_separatedFourierSupport
      (Finset.range N) w hsep
  calc
    eLpNorm (finitePieceTotal N u) 2 volume ^ 2 =
        ‖(memLp_finitePieceTotal hu).toLp (finitePieceTotal N u)‖ₑ ^ 2 := by
      rw [Lp.enorm_toLp]
    _ = ENNReal.ofReal
        (‖(memLp_finitePieceTotal hu).toLp (finitePieceTotal N u)‖ ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ = ENNReal.ofReal (∑ j ∈ Finset.range N, ‖w j‖ ^ 2) := by rw [hnorm]
    _ = ∑ j ∈ Finset.range N, ENNReal.ofReal (‖w j‖ ^ 2) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      exact fun _ _ ↦ sq_nonneg _
    _ = ∑ j ∈ Finset.range N, eLpNorm (u j) 2 volume ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, Lp.enorm_toLp]

theorem finitePieceTotal_sq_lintegral_eq_sum
    {N : ℕ} {u : ℕ → ℝ → ℂ}
    (hu : ∀ j, MemLp (u j) 2 volume)
    (hsep : HasPairwiseSeparatedFourierSupport
      (fun j ↦ (hu j).toLp (u j))) :
    (∫⁻ x, ‖finitePieceTotal N u x‖ₑ ^ 2) =
      ∑ j ∈ Finset.range N, ∫⁻ x, ‖u j x‖ₑ ^ 2 := by
  rw [← eLpNorm_two_sq_lintegral _ (memLp_finitePieceTotal hu).aestronglyMeasurable]
  simp_rw [← eLpNorm_two_sq_lintegral _ (hu _).aestronglyMeasurable]
  exact eLpNorm_finitePieceTotal_sq_eq_sum hu hsep

/-- Final modular maximal-tail theorem for a separated finite family.  Once
the smooth cutoff proves `HasLowPassPrefixControl`, the maximal tails are
bounded by the square-sum of the individual `L²` energies with no dependence
on the number of pieces. -/
theorem finitePieceTailMax_sq_lintegral_le_sum
    {N : ℕ} {u : ℕ → ℝ → ℂ} {A : ℝ≥0∞}
    (hmeas : ∀ j, Measurable (u j))
    (hu : ∀ j, MemLp (u j) 2 volume)
    (hsep : HasPairwiseSeparatedFourierSupport
      (fun j ↦ (hu j).toLp (u j)))
    (hprefix : HasLowPassPrefixControl N u A) :
    (∫⁻ x, finitePieceTailMax N u x ^ 2) ≤
      (4 + 128 * A ^ 2) *
        ∑ j ∈ Finset.range N, ∫⁻ x, ‖u j x‖ₑ ^ 2 := by
  calc
    _ ≤ (4 + 128 * A ^ 2) *
        ∫⁻ x, ‖finitePieceTotal N u x‖ₑ ^ 2 :=
      finitePieceTailMax_sq_lintegral_le hmeas hprefix
    _ = _ := by rw [finitePieceTotal_sq_lintegral_eq_sum hu hsep]

/-- Final modular maximal-tail theorem with the a.e. low-pass hypothesis
that is directly produced by `L²` Fourier projection identities. -/
theorem finitePieceTailMax_sq_lintegral_le_sum_ae
    {N : ℕ} {u : ℕ → ℝ → ℂ} {A : ℝ≥0∞}
    (hmeas : ∀ j, Measurable (u j))
    (hu : ∀ j, MemLp (u j) 2 volume)
    (hsep : HasPairwiseSeparatedFourierSupport
      (fun j ↦ (hu j).toLp (u j)))
    (hprefix : HasAELowPassPrefixControl N u A) :
    (∫⁻ x, finitePieceTailMax N u x ^ 2) ≤
      (4 + 128 * A ^ 2) *
        ∑ j ∈ Finset.range N, ∫⁻ x, ‖u j x‖ₑ ^ 2 := by
  calc
    _ ≤ (4 + 128 * A ^ 2) *
        ∫⁻ x, ‖finitePieceTotal N u x‖ₑ ^ 2 :=
      finitePieceTailMax_sq_lintegral_le_ae hmeas hprefix
    _ = _ := by rw [finitePieceTotal_sq_lintegral_eq_sum hu hsep]


end
end QuadraticCarleson.KrauseLaceyQuadraticAnnularTail
