/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
module


public import Mathlib.Analysis.Complex.ExponentialBounds
public import LeanPool.QuadraticCarleson.QuadraticCarleson.Definitions
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Kalton log-convexity at the weak `L^1` endpoint

The lacunary positive-endpoint argument in arXiv:2609.04101v1 uses Kalton's
log-convexity of weak `L^1` at exactly one point (lines 652--657 of the source
TeX). Its cited source is N. J. Kalton, *Convexity, type and the three space
problem*, Studia Math. 69 (1981), Theorems 3.4 and 3.6. Theorem 3.4 proves
that `L(1,∞)` is log-convex, and Theorem 3.6 gives the finite sequence form

`‖x₁ + ... + xₙ‖ ≤ C ∑ k, (1 + log k) ‖xₖ‖`.

Victor Lie, *On the boundedness of the Carleson operator near L¹*, Rev. Mat.
Iberoam. 29 (2013), equation (3.15), records the countable function-space
version subsequently used by the source paper.

Kalton states Theorem 3.4 on `[0,1]`. His proof only uses distribution
functions, restriction to measurable sets, and the layer-cake formula. The
development below therefore records the measure-space formulation directly;
in particular it applies to Lebesgue measure on `ℝ`, as required here.

The source paper writes `log₁(k+2)`, which under its convention is
`log (10 + (k+2)) = log (k+12)`. This is not definitionally Kalton's weight.
The comparison is proved explicitly below and is not silently identified.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace QuadraticCarleson
namespace KaltonEndpoint


/-- Distribution-function formulation of `‖f‖_{L^{1,∞}(μ)} ≤ A` for a
nonnegative real-valued function. This is the convention used in Kalton's
Theorem 3.4: `sup a * μ {a < f}`. -/
def HasWeakL1Bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (A : ℝ) (f : α → ℝ) : Prop :=
  0 ≤ A ∧ ∀ a : ℝ, 0 < a →
    ENNReal.ofReal a * μ {x | a < f x} ≤ ENNReal.ofReal A

theorem HasWeakL1Bound.measure_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {A : ℝ} {f : α → ℝ} (hf : HasWeakL1Bound μ A f)
    {a : ℝ} (ha : 0 < a) :
    μ {x | a < f x} ≤ ENNReal.ofReal (A / a) := by
  rw [ENNReal.ofReal_div_of_pos ha]
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by simp [ENNReal.ofReal_eq_zero, not_le, ha]))
    (Or.inl ENNReal.ofReal_ne_top)).2
  simpa [mul_comm] using hf.2 a ha

theorem HasWeakL1Bound.measure_ne_top {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {A : ℝ} {f : α → ℝ} (hf : HasWeakL1Bound μ A f)
    {a : ℝ} (ha : 0 < a) : μ {x | a < f x} ≠ ∞ := by
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hf.measure_le ha)

theorem HasWeakL1Bound.measureReal_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {A : ℝ} {f : α → ℝ} (hf : HasWeakL1Bound μ A f)
    {a : ℝ} (ha : 0 < a) : μ.real {x | a < f x} ≤ A / a := by
  rw [measureReal_def]
  have h := hf.measure_le ha
  have h' := (ENNReal.toReal_le_toReal (hf.measure_ne_top ha) ENNReal.ofReal_ne_top).2 h
  rw [ENNReal.toReal_ofReal (div_nonneg hf.1 ha.le)] at h'
  exact h'

theorem HasWeakL1Bound.mono {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {A B : ℝ} {f : α → ℝ} (hf : HasWeakL1Bound μ A f)
    (hAB : A ≤ B) : HasWeakL1Bound μ B f := by
  constructor
  · exact hf.1.trans hAB
  intro a ha
  exact (hf.2 a ha).trans (ENNReal.ofReal_le_ofReal hAB)

theorem HasWeakL1Bound.restrict_measureReal_le_two_div
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {A : ℝ} {f : α → ℝ}
    (hf : HasWeakL1Bound μ A f) (s : Set α) {t : ℝ} (ht : 0 < t) :
    (μ.restrict s).real {x | t ≤ f x} ≤ 2 * A / t := by
  let u : ℝ := t / 2
  have hu : 0 < u := by dsimp [u]; linarith
  let small : Set α := {x | t ≤ f x}
  let big : Set α := {x | u < f x}
  have hsub : small ⊆ big := by
    intro x hx
    dsimp [small, big] at hx ⊢
    exact lt_of_lt_of_le (by dsimp [u]; linarith) hx
  have hmeasure : (μ.restrict s) small ≤ μ big :=
    ((Measure.restrict_le_self (μ := μ) (s := s)) small).trans (measure_mono hsub)
  have hbigtop : μ big ≠ ∞ := by
    dsimp [big]
    exact hf.measure_ne_top hu
  have hsmalltop : (μ.restrict s) small ≠ ∞ :=
    ne_top_of_le_ne_top hbigtop hmeasure
  have hreal := (ENNReal.toReal_le_toReal hsmalltop hbigtop).2 hmeasure
  have hweak := hf.measureReal_le hu
  dsimp [small, big] at hreal
  dsimp [u] at hweak
  calc
    (μ.restrict s).real {x | t ≤ f x} ≤ μ.real {x | t / 2 < f x} := hreal
    _ ≤ A / (t / 2) := hweak
    _ = 2 * A / t := by field_simp

/-- Restricted-integral estimate used in Kalton's proof. The cutoff
`q = 2A/m` is chosen so that the constant part of the layer-cake integral is
exactly `2A`. -/
theorem integralOn_le_of_weakL1Bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A m M : ℝ} {f : α → ℝ} {s : Set α}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hweak : HasWeakL1Bound μ A f) (hs : MeasurableSet s)
    (hsfinite : μ s ≠ ∞) (hsm : μ.real s ≤ m)
    (hcap : ∀ x ∈ s, f x ≤ M) (hA : 0 < A) (hm : 0 < m)
    (hqM : 2 * A / m ≤ M) :
    ∫ x in s, f x ∂μ ≤ 2 * A + 2 * A * Real.log (M * m / (2 * A)) := by
  let ν : Measure α := μ.restrict s
  let q : ℝ := 2 * A / m
  have hq : 0 < q := by dsimp [q]; positivity
  have hM : 0 < M := lt_of_lt_of_le hq hqM
  let : IsFiniteMeasure ν :=
    IsFiniteMeasure.mk (by
      dsimp [ν]
      rw [Measure.restrict_apply_univ]
      exact lt_top_iff_ne_top.mpr hsfinite)
  have hfint : Integrable f ν := by
    apply Integrable.of_bound hf.aestronglyMeasurable M
    rw [ae_restrict_iff' hs]
    exact Eventually.of_forall fun x hx ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
      exact hcap x hx
  have hlayer := hfint.integral_eq_integral_Ioc_meas_le
    (Eventually.of_forall hf0)
    (show f ≤ᵐ[ν] (fun _ ↦ M) by
      exact ae_restrict_of_forall_mem hs hcap)
  let g : ℝ → ℝ := fun t ↦ ν.real {x | t ≤ f x}
  have hgmeas : StronglyMeasurable g := by
    apply Measurable.stronglyMeasurable
    apply Measurable.ennreal_toReal
    exact Antitone.measurable fun a b hab ↦
      measure_mono fun x hx ↦ le_trans hab hx
  have glow : ∀ t ∈ Ioc (0 : ℝ) q, g t ≤ m := by
    intro t ht
    calc
      g t ≤ ν.real univ := measureReal_mono (subset_univ _) (measure_ne_top ν univ)
      _ = μ.real s := by simp [ν, measureReal_def]
      _ ≤ m := hsm
  have ghigh : ∀ t ∈ Ioc q M, g t ≤ 2 * A / t := by
    intro t ht
    dsimp [g, ν]
    exact hweak.restrict_measureReal_le_two_div s (hq.trans ht.1)
  have hconst_int : IntegrableOn (fun _ : ℝ ↦ m) (Ioc 0 q) volume :=
    integrableOn_const (by simp [Real.volume_Ioc] : volume (Ioc (0 : ℝ) q) ≠ ∞)
  have hg_low : IntegrableOn g (Ioc (0 : ℝ) q) volume := by
    apply Integrable.mono' hconst_int
    · exact hgmeas.aestronglyMeasurable.restrict
    · rw [ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun t ht ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact glow t ht
        · exact measureReal_nonneg
  have htail_cont : ContinuousOn (fun t : ℝ ↦ 2 * A / t) (uIcc q M) := by
    apply continuousOn_const.div continuousOn_id
    intro t ht t0
    have htq : q ≤ t := by
      rw [uIcc_of_le hqM] at ht
      exact ht.1
    dsimp only [id_eq] at t0
    linarith
  have htail_int : IntegrableOn (fun t : ℝ ↦ 2 * A / t) (Ioc q M) volume :=
    (htail_cont.intervalIntegrable).1
  have hg_high : IntegrableOn g (Ioc q M) volume := by
    apply Integrable.mono' htail_int
    · exact hgmeas.aestronglyMeasurable.restrict
    · rw [ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun t ht ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact ghigh t ht
        · exact measureReal_nonneg
  have hsplit : Ioc (0 : ℝ) M = Ioc 0 q ∪ Ioc q M :=
    (Ioc_union_Ioc_eq_Ioc hq.le hqM).symm
  have hgintegrable : IntegrableOn g (Ioc (0 : ℝ) M) volume := by
    rw [hsplit]
    exact hg_low.union hg_high
  rw [show (∫ x in s, f x ∂μ) = ∫ x, f x ∂ν by rfl, hlayer]
  rw [hsplit, setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
    hg_low hg_high]
  calc
    (∫ t in Ioc 0 q, g t) + ∫ t in Ioc q M, g t ≤
        (∫ _t in Ioc 0 q, m) + ∫ t in Ioc q M, 2 * A / t :=
      add_le_add
        (setIntegral_mono_on hg_low hconst_int measurableSet_Ioc glow)
        (setIntegral_mono_on hg_high htail_int measurableSet_Ioc ghigh)
    _ = m * q + 2 * A * Real.log (M / q) := by
      rw [show (∫ _t in Ioc (0 : ℝ) q, m) = m * q by
        rw [setIntegral_const, measureReal_def, Real.volume_Ioc,
          ENNReal.toReal_ofReal (by linarith)]
        simp [smul_eq_mul, mul_comm]]
      rw [← intervalIntegral.integral_of_le hqM]
      rw [show (fun t : ℝ ↦ 2 * A / t) = fun t ↦ (2 * A) * (1 / t) by
        funext t
        ring]
      rw [intervalIntegral.integral_const_mul]
      rw [integral_one_div_of_pos hq hM]
    _ = 2 * A + 2 * A * Real.log (M * m / (2 * A)) := by
      dsimp [q]
      congr 1
      · field_simp
      · congr 2
        field_simp

/-- The original finite-sequence weight in Kalton's Theorem 3.6, with a
zero-based Lean index corresponding to the paper index `k = i+1`. -/
noncomputable def kaltonWeight (i : ℕ) : ℝ :=
  1 + Real.log (i + 1 : ℝ)

theorem kaltonWeight_nonneg (i : ℕ) : 0 ≤ kaltonWeight i := by
  unfold kaltonWeight
  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have hlog : 0 ≤ Real.log ((i : ℝ) + 1) := Real.log_nonneg (by linarith)
  linarith

theorem kaltonWeight_one_le (i : ℕ) : 1 ≤ kaltonWeight i := by
  unfold kaltonWeight
  have hi : (1 : ℝ) ≤ (i : ℝ) + 1 := by norm_num
  exact le_add_of_nonneg_right (Real.log_nonneg hi)

/-- The weight occurring in the quadratic-Carleson source after translating
its `log₁` notation literally. -/
theorem paper_outer_weight_eq (i : ℕ) :
    paperLog 1 ((i : ℝ) + 2) = Real.log ((i : ℝ) + 12) := by
  simp [paperLog]
  ring_nf

/-- Kalton's weight is bounded by twice the paper's outer weight. The factor
two keeps separate the two logarithm conventions in the cited arguments. -/
theorem kaltonWeight_le_two_paperLog (i : ℕ) :
    kaltonWeight i ≤ 2 * paperLog 1 ((i : ℝ) + 2) := by
  rw [paper_outer_weight_eq]
  unfold kaltonWeight
  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have hone : 1 ≤ Real.log ((i : ℝ) + 12) := by
    rw [← Real.exp_le_exp]
    rw [Real.exp_log (by linarith : 0 < (i : ℝ) + 12)]
    have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hi' : (3 : ℝ) ≤ (i : ℝ) + 12 := by linarith
    exact le_trans he.le hi'
  have hlog : Real.log ((i : ℝ) + 1) ≤ Real.log ((i : ℝ) + 12) := by
    apply Real.log_le_log
    · linarith
    · linarith
  linarith

/-- The entropy summand in Kalton's equivalent form (3.3.2). Its value at
`A = 0` is the continuous value zero, rather than the raw expression
`0 * log (S / 0)`. -/
noncomputable def entropySummand (S A : ℝ) : ℝ :=
  if A = 0 then 0 else A * Real.log (S / A)

theorem entropySummand_zero (S : ℝ) : entropySummand S 0 = 0 := by
  simp [entropySummand]

theorem entropySummand_eq {S A : ℝ} (hA : A ≠ 0) :
    entropySummand S A = A * Real.log (S / A) := by
  simp [entropySummand, hA]

/-- The elementary pointwise estimate behind Kalton's Lemma 3.5. We use
`q_i = (i+1)⁻²`; the inequality is the tangent bound
`-x log x ≤ 1-x`, applied to `x = (A/S)/q_i`. -/
theorem entropySummand_le_index {S A : ℝ} (i : ℕ)
    (hS : 0 < S) (hA : 0 ≤ A) :
    entropySummand S A ≤
      S / ((i : ℝ) + 1) ^ 2 - A + 2 * A * Real.log ((i : ℝ) + 1) := by
  by_cases hA0 : A = 0
  · subst A
    simp only [entropySummand, ↓reduceIte, sub_zero, mul_zero, zero_mul, add_zero]
    positivity
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  let p : ℝ := A / S
  let q : ℝ := 1 / ((i : ℝ) + 1) ^ 2
  have hp : 0 < p := div_pos hApos hS
  have hq : 0 < q := by dsimp [q]; positivity
  have ht := Real.negMulLog_le_one_sub_self (div_nonneg hp.le hq.le)
  have hlogp : Real.log (S / A) = -Real.log p := by
    dsimp [p]
    rw [show S / A = (A / S)⁻¹ by field_simp, Real.log_inv]
  have hlogq : Real.log q = -2 * Real.log ((i : ℝ) + 1) := by
    dsimp [q]
    rw [one_div, Real.log_inv, Real.log_pow]
    ring
  have hrewrite :
      S * q * Real.negMulLog (p / q) =
        entropySummand S A + A * Real.log q := by
    rw [entropySummand_eq hA0]
    rw [Real.negMulLog]
    rw [Real.log_div hp.ne' hq.ne']
    dsimp [p]
    field_simp [hS.ne', hq.ne']
    rw [hlogp]
    ring
  have hscaled := mul_le_mul_of_nonneg_left ht (mul_nonneg hS.le hq.le)
  have hcancel : S * q * (p / q) = A := by
    dsimp [p]
    field_simp [hS.ne', hq.ne']
  rw [hrewrite, mul_sub, hcancel] at hscaled
  rw [hlogq] at hscaled
  dsimp [q] at hscaled
  have hden : 0 < ((i : ℝ) + 1) ^ 2 := by positivity
  rw [div_eq_mul_inv] at hscaled ⊢
  ring_nf at hscaled ⊢
  linarith

theorem sum_fin_inv_sq_le_two (n : ℕ) :
    (∑ i : Fin n, (((i : ℝ) + 1) ^ 2)⁻¹) ≤ 2 := by
  have aux : ∀ m : ℕ,
      (∑ i ∈ Finset.range m, (((i : ℝ) + 1) ^ 2)⁻¹) ≤
        2 - 2 / ((m : ℝ) + 1) := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
        rw [Finset.sum_range_succ]
        have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        have hstep :
            (((m : ℝ) + 1) ^ 2)⁻¹ ≤
              2 / ((m : ℝ) + 1) - 2 / ((m : ℝ) + 2) := by
          field_simp
          nlinarith
        calc
          (∑ i ∈ Finset.range m, (((i : ℝ) + 1) ^ 2)⁻¹) +
              (((m : ℝ) + 1) ^ 2)⁻¹ ≤
              (2 - 2 / ((m : ℝ) + 1)) +
                (2 / ((m : ℝ) + 1) - 2 / ((m : ℝ) + 2)) :=
            add_le_add ih hstep
          _ = 2 - 2 / (((m + 1 : ℕ) : ℝ) + 1) := by
            push_cast
            ring
  calc
    (∑ i : Fin n, (((i : ℝ) + 1) ^ 2)⁻¹) =
        ∑ i ∈ Finset.range n, (((i : ℝ) + 1) ^ 2)⁻¹ := by
      exact Fin.sum_univ_eq_sum_range
        (fun j : ℕ => (((j : ℝ) + 1) ^ 2)⁻¹) n
    _ ≤ 2 - 2 / ((n : ℝ) + 1) := aux n
    _ ≤ 2 := by
      have : 0 ≤ 2 / ((n : ℝ) + 1) := by positivity
      linarith

/-- Kalton's entropy budget is controlled by his exact finite index weight.
This is the finite form of the scalar reduction in Theorem 3.6. -/
theorem sum_entropySummand_le_kaltonWeight {n : ℕ} (A : Fin n → ℝ)
    (hA : ∀ i, 0 ≤ A i) :
    let S := ∑ i, A i
    ∑ i, entropySummand S (A i) ≤
      2 * ∑ i, kaltonWeight i.val * A i := by
  dsimp only
  let S : ℝ := ∑ i, A i
  by_cases hS0 : S = 0
  · have hz : ∀ i, A i = 0 := by
      intro i
      have hle : A i ≤ S := by
        dsimp [S]
        exact Finset.single_le_sum (fun j _ ↦ hA j) (Finset.mem_univ i)
      rw [hS0] at hle
      exact le_antisymm hle (hA i)
    simp [hz, entropySummand, kaltonWeight]
  have hS : 0 < S := lt_of_le_of_ne (Finset.sum_nonneg fun i _ ↦ hA i) (Ne.symm hS0)
  have hpoint := fun i : Fin n => entropySummand_le_index i hS (hA i)
  have hsum := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.univ) ↦ hpoint i)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  have hrecip := sum_fin_inv_sq_le_two n
  have hSrecip :
      (∑ i : Fin n, S / ((i : ℝ) + 1) ^ 2) ≤ 2 * S := by
    rw [show (∑ i : Fin n, S / ((i : ℝ) + 1) ^ 2) =
        S * ∑ i : Fin n, (((i : ℝ) + 1) ^ 2)⁻¹ by
      simp only [div_eq_mul_inv, Finset.mul_sum]]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hrecip hS.le
  dsimp [S] at hsum hSrecip ⊢
  have hdouble :
      (∑ i : Fin n, 2 * A i * Real.log ((i : ℝ) + 1)) =
        2 * ∑ i : Fin n, A i * Real.log ((i : ℝ) + 1) := by
    rw [Finset.mul_sum]
    ring_nf
  rw [hdouble] at hsum
  have hrhs :
      2 * ∑ i : Fin n, kaltonWeight i.val * A i =
        2 * ∑ i : Fin n, A i +
          2 * ∑ i : Fin n, A i * Real.log ((i : ℝ) + 1) := by
    calc
      2 * ∑ i : Fin n, kaltonWeight i.val * A i =
          2 * ((∑ i : Fin n, A i) +
            ∑ i : Fin n, A i * Real.log ((i : ℝ) + 1)) := by
        congr 1
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        unfold kaltonWeight
        ring
      _ = 2 * ∑ i : Fin n, A i +
          2 * ∑ i : Fin n, A i * Real.log ((i : ℝ) + 1) := by ring
  rw [hrhs]
  nlinarith

/-- Finite Kalton inequality when the individual weak bounds are positive.
The proof follows Theorem 3.4: remove the union of the high-value sets,
integrate on the remaining part of a level set, and use the layer-cake bound.
The entropy-to-index conversion is the preceding formal version of Theorem
3.6. -/
theorem hasWeakL1Bound_finset_sum_of_pos
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    (f : Fin n → α → ℝ) (A : Fin n → ℝ)
    (hf : ∀ i, Measurable (f i)) (hf0 : ∀ i x, 0 ≤ f i x)
    (hweak : ∀ i, HasWeakL1Bound μ (A i) (f i))
    (hA : ∀ i, 0 < A i) :
    HasWeakL1Bound μ
      (12 * ∑ i, kaltonWeight i.val * A i)
      (fun x ↦ ∑ i, f i x) := by
  constructor
  · have hw : 0 ≤ ∑ i, kaltonWeight i.val * A i :=
      Finset.sum_nonneg fun i _ ↦ mul_nonneg (kaltonWeight_nonneg i.val) (hA i).le
    positivity
  intro a ha
  by_cases hn : n = 0
  · subst n
    simp [not_lt.mpr ha.le]
  let F : α → ℝ := fun x ↦ ∑ i, f i x
  let E : Set α := {x | a < F x}
  have hFmeas : Measurable F := Finset.measurable_sum _ fun i _ ↦ hf i
  have hEmeas : MeasurableSet E := hFmeas measurableSet_Ioi
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let u : ℝ := a / n
  have hu : 0 < u := div_pos ha (by exact_mod_cast hnpos)
  have hEsub : E ⊆ ⋃ i : Fin n, {x | u < f i x} := by
    intro x hx
    by_contra hxall
    simp only [mem_iUnion, not_exists, mem_ofPred_eq] at hxall
    have hsum : F x ≤ ∑ _i : Fin n, u := by
      dsimp [F]
      exact Finset.sum_le_sum fun i _ ↦ le_of_not_gt (hxall i)
    have hconst : (∑ _i : Fin n, u) = a := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [u]
      field_simp
    exact (not_lt_of_ge (hsum.trans_eq hconst)) hx
  have huniontop : μ (⋃ i : Fin n, {x | u < f i x}) ≠ ∞ := by
    apply ne_top_of_le_ne_top (b := ∑' i : Fin n, μ {x | u < f i x})
    · rw [tsum_fintype]
      exact ENNReal.sum_ne_top.mpr fun i _ ↦ (hweak i).measure_ne_top hu
    · exact measure_iUnion_le _
  have hEtop : μ E ≠ ∞ := ne_top_of_le_ne_top huniontop (measure_mono hEsub)
  let m : ℝ := μ.real E
  by_cases hm0 : m = 0
  · have hμE : μ E = 0 := by
      have hz : (μ E).toReal = 0 := by simpa [m, measureReal_def] using hm0
      exact (ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right hEtop
    change ENNReal.ofReal a * μ E ≤ _
    simp [hμE]
  have hm : 0 < m := lt_of_le_of_ne measureReal_nonneg (Ne.symm hm0)
  let S : ℝ := ∑ i, A i
  have hS : 0 < S := by
    let i₀ : Fin n := ⟨0, hnpos⟩
    have hsingle : A i₀ ≤ ∑ i, A i :=
      Finset.single_le_sum (fun i _ ↦ (hA i).le) (Finset.mem_univ i₀)
    dsimp [S]
    exact (hA i₀).trans_le hsingle
  let M : ℝ := 2 * S / m
  have hM : 0 < M := by dsimp [M]; positivity
  let B : Set α := ⋃ i : Fin n, {x | M < f i x}
  have hBmeas : MeasurableSet B := MeasurableSet.iUnion fun i ↦ (hf i) measurableSet_Ioi
  have hBreal : μ.real B ≤ m / 2 := by
    calc
      μ.real B ≤ ∑ i : Fin n, μ.real {x | M < f i x} :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ i : Fin n, A i / M := by
        exact Finset.sum_le_sum fun i _ ↦ (hweak i).measureReal_le hM
      _ = m / 2 := by
        dsimp [M, S]
        rw [← Finset.sum_div]
        field_simp [hS.ne']
        exact div_self (by simpa [S] using hS.ne')
  let D : Set α := E \ B
  have hDmeas : MeasurableSet D := hEmeas.diff hBmeas
  have hDtop : μ D ≠ ∞ := ne_top_of_le_ne_top hEtop (measure_mono sdiff_subset)
  have hBtop : μ B ≠ ∞ := by
    apply ne_top_of_le_ne_top (b := ∑' i : Fin n, μ {x | M < f i x})
    · rw [tsum_fintype]
      exact ENNReal.sum_ne_top.mpr fun i _ ↦ (hweak i).measure_ne_top hM
    · exact measure_iUnion_le _
  have hDreal : m / 2 ≤ μ.real D := by
    have hinter : E ∩ B ⊆ E := inter_subset_left
    have hintermeas : MeasurableSet (E ∩ B) := hEmeas.inter hBmeas
    have hdiff : μ.real (E \ (E ∩ B)) = μ.real E - μ.real (E ∩ B) :=
      measureReal_sdiff hinter hintermeas hEtop
    have hDB : E \ (E ∩ B) = D := by ext x; simp [D]
    rw [hDB] at hdiff
    rw [hdiff]
    have hiB : μ.real (E ∩ B) ≤ μ.real B :=
      measureReal_mono inter_subset_right hBtop
    dsimp [m]
    linarith
  have hcap : ∀ i x, x ∈ D → f i x ≤ M := by
    intro i x hx
    exact le_of_not_gt fun hi ↦ hx.2 (Set.mem_iUnion.2 ⟨i, hi⟩)
  have hAD : ∀ i, IntegrableOn (f i) D μ := by
    intro i
    apply Integrable.mono'
      (integrableOn_const hDtop : IntegrableOn (fun _ : α ↦ M) D μ)
    · exact (hf i).aestronglyMeasurable.restrict
    · rw [ae_restrict_iff' hDmeas]
      exact Eventually.of_forall fun x hx ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 i x)]
        exact hcap i x hx
  have hsumint : IntegrableOn F D μ := by
    dsimp [F]
    exact integrable_finsetSum _ fun i _ ↦ hAD i
  have hlower : a * μ.real D ≤ ∫ x in D, F x ∂μ := by
    rw [← show (∫ _x in D, a ∂μ) = a * μ.real D by
      rw [setIntegral_const]
      simp [smul_eq_mul, mul_comm]]
    apply setIntegral_mono_on integrableOn_const hsumint hDmeas
    intro x hx
    exact (show x ∈ E from hx.1).le
  have hupper :
      (∫ x in D, F x ∂μ) ≤
        ∑ i : Fin n, (2 * A i + 2 * A i * Real.log (S / A i)) := by
    rw [show (∫ x in D, F x ∂μ) = ∑ i : Fin n, ∫ x in D, f i x ∂μ by
      dsimp [F]
      exact integral_finsetSum Finset.univ fun i _ ↦ hAD i]
    apply Finset.sum_le_sum
    intro i _hi
    have hAiS : A i ≤ S := by
      dsimp [S]
      exact Finset.single_le_sum (fun j _ ↦ (hA j).le) (Finset.mem_univ i)
    have hqM : 2 * A i / m ≤ M := by dsimp [M]; gcongr
    have hi := integralOn_le_of_weakL1Bound (hf i) (hf0 i) (hweak i)
      hDmeas hDtop (measureReal_mono sdiff_subset hEtop) (hcap i) (hA i) hm hqM
    have hratio : M * m / (2 * A i) = S / A i := by
      dsimp [M]
      field_simp [hm.ne', (hA i).ne']
    rw [hratio] at hi
    exact hi
  have hentropy := sum_entropySummand_le_kaltonWeight A fun i ↦ (hA i).le
  have hrewrite :
      (∑ i : Fin n, (2 * A i + 2 * A i * Real.log (S / A i))) =
        2 * S + 2 * ∑ i : Fin n, entropySummand S (A i) := by
    simp_rw [entropySummand_eq (hA _).ne']
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    dsimp [S]
    ring
  have hweightS : S ≤ ∑ i : Fin n, kaltonWeight i.val * A i := by
    dsimp [S]
    apply Finset.sum_le_sum
    intro i _hi
    have hw := kaltonWeight_nonneg i.val
    have hw1 : 1 ≤ kaltonWeight i.val := by
      unfold kaltonWeight
      have hone : (1 : ℝ) ≤ (i.val : ℝ) + 1 := by norm_num
      have : 0 ≤ Real.log ((i.val : ℝ) + 1) := Real.log_nonneg hone
      linarith
    nlinarith [hA i]
  have ham : a * m ≤ 12 * ∑ i : Fin n, kaltonWeight i.val * A i := by
    have := hlower.trans (hupper.trans_eq hrewrite)
    dsimp [m] at hDreal
    nlinarith
  have hreal : μ.real E ≤
      (12 * ∑ i : Fin n, kaltonWeight i.val * A i) / a := by
    dsimp [m] at ham ⊢
    exact (le_div_iff₀ ha).2 (by simpa [mul_comm] using ham)
  have hμE : μ E ≤ ENNReal.ofReal
      ((12 * ∑ i : Fin n, kaltonWeight i.val * A i) / a) := by
    apply (ENNReal.toReal_le_toReal hEtop ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal]
    · exact hreal
    · exact div_nonneg (mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun i _ ↦
          mul_nonneg (kaltonWeight_nonneg i.val) (hA i).le)) ha.le
  rw [ENNReal.ofReal_div_of_pos ha] at hμE
  simpa [F, E, mul_comm] using
    (ENNReal.le_div_iff_mul_le
      (Or.inl (by simp [ENNReal.ofReal_eq_zero, not_le, ha]))
      (Or.inl ENNReal.ofReal_ne_top)).1 hμE

/-- Finite Kalton inequality on an arbitrary measure space. Zero individual
weak bounds are handled by positive regularization and passage to the exact
endpoint; they are not excluded by an extra hypothesis. -/
theorem hasWeakL1Bound_finset_sum
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    (f : Fin n → α → ℝ) (A : Fin n → ℝ)
    (hf : ∀ i, Measurable (f i)) (hf0 : ∀ i x, 0 ≤ f i x)
    (hweak : ∀ i, HasWeakL1Bound μ (A i) (f i)) :
    HasWeakL1Bound μ
      (12 * ∑ i, kaltonWeight i.val * A i)
      (fun x ↦ ∑ i, f i x) := by
  let W : ℝ := ∑ i : Fin n, kaltonWeight i.val
  let K : ℝ := 12 * ∑ i : Fin n, kaltonWeight i.val * A i
  have hA : ∀ i, 0 ≤ A i := fun i ↦ (hweak i).1
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ ↦
      mul_nonneg (kaltonWeight_nonneg i.val) (hA i))
  constructor
  · exact hK
  intro a ha
  by_cases hn : n = 0
  · subst n
    simp [not_lt.mpr ha.le]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hW : 0 < W := by
    let i₀ : Fin n := ⟨0, hnpos⟩
    have hsingle : kaltonWeight i₀.val ≤ W := by
      dsimp [W]
      exact Finset.single_le_sum (fun i _ ↦ kaltonWeight_nonneg i.val)
        (Finset.mem_univ i₀)
    exact lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one (kaltonWeight_one_le i₀.val)) hsingle
  let E : Set α := {x | a < ∑ i, f i x}
  have regularized (ε : ℝ) (hε : 0 < ε) :
      HasWeakL1Bound μ
        (12 * ∑ i : Fin n, kaltonWeight i.val * (A i + ε))
        (fun x ↦ ∑ i, f i x) := by
    apply hasWeakL1Bound_finset_sum_of_pos f (fun i ↦ A i + ε) hf hf0
    · intro i
      exact (hweak i).mono (by linarith [hA i])
    · intro i
      linarith [hA i]
  have hEtop : μ E ≠ ∞ := by
    simpa [E] using (regularized 1 one_pos).measure_ne_top ha
  have hreal : a * μ.real E ≤ K := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    let ε : ℝ := δ / (12 * W)
    have hε : 0 < ε := div_pos hδ (mul_pos (by norm_num) hW)
    have hr := (regularized ε hε).measureReal_le ha
    have hsum_expand :
        (∑ i : Fin n, kaltonWeight i.val * (A i + ε)) =
          (∑ i : Fin n, kaltonWeight i.val * A i) + ε * W := by
      calc
        (∑ i : Fin n, kaltonWeight i.val * (A i + ε)) =
            ∑ i : Fin n, (kaltonWeight i.val * A i +
              ε * kaltonWeight i.val) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = (∑ i : Fin n, kaltonWeight i.val * A i) +
            ∑ i : Fin n, ε * kaltonWeight i.val := Finset.sum_add_distrib
        _ = (∑ i : Fin n, kaltonWeight i.val * A i) + ε * W := by
          rw [Finset.mul_sum]
    have herr : 12 * ε * W = δ := by
      dsimp [ε]
      field_simp [hW.ne']
    have hbudget :
        12 * ∑ i : Fin n, kaltonWeight i.val * (A i + ε) = K + δ := by
      rw [hsum_expand, mul_add, ← mul_assoc, herr]
    rw [hbudget] at hr
    simpa [E, mul_comm] using (le_div_iff₀ ha).mp hr
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEtop) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha.le,
    ENNReal.toReal_ofReal hK]
  simpa [E, measureReal_def] using hreal

/-- The finite estimate in the logarithmic convention used by the source
paper. The factor `24 = 12 · 2` displays the explicit comparison with
Kalton's original `1 + log (i+1)` weight. -/
theorem hasWeakL1Bound_finset_sum_paperLog
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    (f : Fin n → α → ℝ) (A : Fin n → ℝ)
    (hf : ∀ i, Measurable (f i)) (hf0 : ∀ i x, 0 ≤ f i x)
    (hweak : ∀ i, HasWeakL1Bound μ (A i) (f i)) :
    HasWeakL1Bound μ
      (24 * ∑ i, paperLog 1 ((i.val : ℝ) + 2) * A i)
      (fun x ↦ ∑ i, f i x) := by
  apply (hasWeakL1Bound_finset_sum f A hf hf0 hweak).mono
  have hsum :
      (∑ i : Fin n, kaltonWeight i.val * A i) ≤
        2 * ∑ i : Fin n, paperLog 1 ((i.val : ℝ) + 2) * A i := by
    calc
      (∑ i : Fin n, kaltonWeight i.val * A i) ≤
          ∑ i : Fin n, (2 * paperLog 1 ((i.val : ℝ) + 2)) * A i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (kaltonWeight_le_two_paperLog i.val)
          (hweak i).1
      _ = 2 * ∑ i : Fin n, paperLog 1 ((i.val : ℝ) + 2) * A i := by
        rw [Finset.mul_sum]
        ring_nf
  linarith

/-- Countable form recorded by Lie, obtained exactly as in the source paper:
apply the finite estimate to partial sums and then use continuity from below of
measure. Pointwise summability names the real-valued infinite sum and rules
out the non-summable convention `tsum = 0`. -/
theorem hasWeakL1Bound_tsum
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : ℕ → α → ℝ) (A : ℕ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hf0 : ∀ i x, 0 ≤ f i x)
    (hweak : ∀ i, HasWeakL1Bound μ (A i) (f i))
    (hAf : Summable (fun i ↦ kaltonWeight i * A i))
    (hfsum : ∀ x, Summable (fun i ↦ f i x)) :
    HasWeakL1Bound μ
      (12 * ∑' i, kaltonWeight i * A i)
      (fun x ↦ ∑' i, f i x) := by
  let b : ℕ → ℝ := fun i ↦ kaltonWeight i * A i
  have hb0 : ∀ i, 0 ≤ b i := fun i ↦
    mul_nonneg (kaltonWeight_nonneg i) (hweak i).1
  have hbudget0 : 0 ≤ 12 * ∑' i, b i :=
    mul_nonneg (by norm_num) (tsum_nonneg hb0)
  constructor
  · simpa [b] using hbudget0
  intro a ha
  let P : ℕ → α → ℝ := fun n x ↦ ∑ i ∈ Finset.range n, f i x
  let E : ℕ → Set α := fun n ↦ {x | a < P n x}
  have hPmono : Monotone P := by
    intro n m hnm x
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm)
      (fun i _ _ ↦ hf0 i x)
  have hEmono : Monotone E := fun n m hnm x hx ↦
    lt_of_lt_of_le hx (hPmono hnm x)
  have hEunion : (⋃ n, E n) = {x | a < ∑' i, f i x} := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      exact lt_of_lt_of_le hn ((hfsum x).sum_le_tsum (Finset.range n)
        (fun i _ ↦ hf0 i x))
    · intro hx
      have hlim : Tendsto (fun n : ℕ ↦ ∑ i ∈ Finset.range n, f i x) atTop
          (𝓝 (∑' i, f i x)) :=
        (hasSum_iff_tendsto_nat_of_nonneg (fun i ↦ hf0 i x) _).mp (hfsum x).hasSum
      obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).1 a hx).exists
      exact Set.mem_iUnion.mpr ⟨n, hn⟩
  have hpartial : ∀ n, HasWeakL1Bound μ (12 * ∑' i, b i) (P n) := by
    intro n
    have hn := hasWeakL1Bound_finset_sum
      (fun i : Fin n ↦ f i.val) (fun i : Fin n ↦ A i.val)
      (fun i ↦ hf i.val) (fun i x ↦ hf0 i.val x) (fun i ↦ hweak i.val)
    have hfin : (∑ i : Fin n, kaltonWeight i.val * A i.val) ≤ ∑' i, b i := by
      calc
        (∑ i : Fin n, kaltonWeight i.val * A i.val) =
            ∑ i ∈ Finset.range n, b i := by
          exact Fin.sum_univ_eq_sum_range b n
        _ ≤ ∑' i, b i := hAf.sum_le_tsum (Finset.range n) (fun i _ ↦ hb0 i)
    have hfunc : (fun x ↦ ∑ i : Fin n, f i.val x) = P n := by
      funext x
      dsimp [P]
      simpa only [Finset.sum_apply] using
        congrFun (Fin.sum_univ_eq_sum_range (fun i ↦ f i) n) x
    rw [hfunc] at hn
    exact hn.mono (mul_le_mul_of_nonneg_left hfin (by norm_num))
  have hmeasure : μ (⋃ n, E n) ≤ ENNReal.ofReal
      ((12 * ∑' i, b i) / a) := by
    rw [hEmono.measure_iUnion]
    exact iSup_le fun n ↦ by
      simpa [E] using (hpartial n).measure_le ha
  rw [hEunion] at hmeasure
  rw [ENNReal.ofReal_div_of_pos ha] at hmeasure
  simpa [b, mul_comm] using
    (ENNReal.le_div_iff_mul_le
      (Or.inl (by simp [ENNReal.ofReal_eq_zero, not_le, ha]))
      (Or.inl ENNReal.ofReal_ne_top)).1 hmeasure

/-- Countable endpoint inequality in precisely the source paper's outer
`log₁(k+2) = log(k+12)` convention. -/
theorem hasWeakL1Bound_tsum_paperLog
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : ℕ → α → ℝ) (A : ℕ → ℝ)
    (hf : ∀ i, Measurable (f i)) (hf0 : ∀ i x, 0 ≤ f i x)
    (hweak : ∀ i, HasWeakL1Bound μ (A i) (f i))
    (hAp : Summable (fun i : ℕ ↦ paperLog 1 ((i : ℝ) + 2) * A i))
    (hfsum : ∀ x, Summable (fun i ↦ f i x)) :
    HasWeakL1Bound μ
      (24 * ∑' i : ℕ, paperLog 1 ((i : ℝ) + 2) * A i)
      (fun x ↦ ∑' i, f i x) := by
  let p : ℕ → ℝ := fun i ↦ paperLog 1 ((i : ℝ) + 2) * A i
  let k : ℕ → ℝ := fun i ↦ kaltonWeight i * A i
  have hp0 : ∀ i, 0 ≤ p i := fun i ↦ by
    change 0 ≤ paperLog 1 ((i : ℝ) + 2) * A i
    exact mul_nonneg (by
      rw [paper_outer_weight_eq]
      exact Real.log_nonneg (by
        have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
        linarith)) (hweak i).1
  have hk0 : ∀ i, 0 ≤ k i := fun i ↦
    mul_nonneg (kaltonWeight_nonneg i) (hweak i).1
  have hkp : ∀ i, k i ≤ 2 * p i := fun i ↦ by
    dsimp only [k, p]
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_right (kaltonWeight_le_two_paperLog i) (hweak i).1
  have hp : Summable p := by simpa [p] using hAp
  have h2p : Summable (fun i ↦ 2 * p i) := by
    exact hp.mul_left 2
  have hk : Summable k := Summable.of_nonneg_of_le hk0 hkp h2p
  have hmain := hasWeakL1Bound_tsum f A hf hf0 hweak (by simpa [k] using hk) hfsum
  apply hmain.mono
  have htsum : (∑' i, k i) ≤ 2 * ∑' i, p i := by
    calc
      (∑' i, k i) ≤ ∑' i, 2 * p i := hk.tsum_le_tsum hkp h2p
      _ = 2 * ∑' i, p i := hp.tsum_mul_left 2
  dsimp [k, p] at htsum ⊢
  linarith

end KaltonEndpoint
end QuadraticCarleson
