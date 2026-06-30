/-
Copyright (c) 2026 Daniel Smania. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Smania
-/

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import LeanPool.Burkholder.Majorants

/-!
# Martingale transforms and the Lp Burkholder inequality

Defines the discrete martingale transform and proves the sharp `Lp` Burkholder
inequality for martingale transforms by a predictable multiplier bounded by `1`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace Burkholder

/-- The conjugate exponent helper, re-exported in the `Burkholder` namespace. -/
def q (p : ℝ) : ℝ :=
  Majorants.q p

/-- `pStar = max p q`, re-exported in the `Burkholder` namespace. -/
def pStar (p : ℝ) : ℝ :=
  Majorants.pStar p

/-- The Burkholder function `v`, imported from the majorant development. -/
def v (p x y : ℝ) : ℝ :=
  Majorants.v p x y

/-- The package of properties saying that `u` is a Burkholder majorant for exponent `p`. -/
private def IsMajorant (p : ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  (∀ x y, ∃ d_u_dx d_u_dy : ℝ,
    ∀ h k, h * k ≤ 0 →
      u (x + h) (y + k) ≤ u x y + d_u_dx * h + d_u_dy * k) ∧
  (∀ x y, v p x y ≤ u x y) ∧
  (∀ x y, x * y ≤ 0 → u x y ≤ 0) ∧
  (∀ x y, p ≠ 2 ∧ x * y = 0 ∧ (x, y) ≠ (0, 0) → u x y < 0)



private noncomputable def u (p : ℝ) (hp : p > 1) : ℝ → ℝ → ℝ :=
  Classical.choose (Majorants.exists_majorant_p_g_1 p hp)

private noncomputable def du_dx (p : ℝ) (hp : p > 1) : ℝ → ℝ → ℝ :=
  Classical.choose
    (Classical.choose_spec (Majorants.exists_majorant_p_g_1 p hp))

private noncomputable def du_dy (p : ℝ) (hp : p > 1) : ℝ → ℝ → ℝ :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec (Majorants.exists_majorant_p_g_1 p hp)))

private noncomputable def C (p : ℝ) (hp : p > 1) : ℝ :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec (Majorants.exists_majorant_p_g_1 p hp))))


private lemma du_dx_continuousOn (p : ℝ) (hp : p > 1) :
    ContinuousOn
      (fun z : ℝ × ℝ => Burkholder.du_dx p hp z.1 z.2) Set.univ := by
  rcases
    Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          (Classical.choose_spec
            (Majorants.exists_majorant_p_g_1 p hp)))) with
    ⟨hC_nonneg,
      hu_cont, hdu_dx_cont, hdu_dy_cont,
      hu_growth, hdu_dx_growth, hdu_dy_growth,
      htangent, hmajor, hnonpos, haxis⟩
  exact hdu_dx_cont

private lemma du_dx_growth_bound (p : ℝ) (hp : p > 1) :
    ∀ x y,
      |Burkholder.du_dx p hp x y|
        ≤ Burkholder.C p hp *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) := by
  rcases
    Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          (Classical.choose_spec
            (Majorants.exists_majorant_p_g_1 p hp)))) with
    ⟨hC_nonneg,
      hu_cont, hdu_dx_cont, hdu_dy_cont,
      hu_growth, hdu_dx_growth, hdu_dy_growth,
      htangent, hmajor, hnonpos, haxis⟩
  exact hdu_dx_growth

private lemma du_dy_continuousOn (p : ℝ) (hp : p > 1) :
    ContinuousOn
      (fun z : ℝ × ℝ => Burkholder.du_dy p hp z.1 z.2) Set.univ := by
  rcases
    Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          (Classical.choose_spec
            (Majorants.exists_majorant_p_g_1 p hp)))) with
    ⟨hC_nonneg,
      hu_cont, hdu_dx_cont, hdu_dy_cont,
      hu_growth, hdu_dx_growth, hdu_dy_growth,
      htangent, hmajor, hnonpos, haxis⟩
  exact hdu_dy_cont

private lemma du_dy_growth_bound (p : ℝ) (hp : p > 1) :
    ∀ x y,
      |Burkholder.du_dy p hp x y|
        ≤ Burkholder.C p hp *
          (Real.rpow |x| (p - 1) + Real.rpow |y| (p - 1)) := by
  rcases
    Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          (Classical.choose_spec
            (Majorants.exists_majorant_p_g_1 p hp)))) with
    ⟨hC_nonneg,
      hu_cont, hdu_dx_cont, hdu_dy_cont,
      hu_growth, hdu_dx_growth, hdu_dy_growth,
      htangent, hmajor, hnonpos, haxis⟩
  exact hdu_dy_growth



private lemma u_isMajorant (p : ℝ) (hp : p > 1) :
    IsMajorant p (u p hp) := by
  rcases Classical.choose_spec (Majorants.exists_majorant_p_g_1 p hp) with
    ⟨du_dx, du_dy, C, hC_nonneg,
      hu_cont, hdu_dx_cont, hdu_dy_cont,
      hu_growth, hdu_dx_growth, hdu_dy_growth,
      htangent, hmajor, hnonpos, haxis⟩
  constructor
  · intro x y
    exact ⟨du_dx x y, du_dy x y, htangent x y⟩
  constructor
  · simpa [v, u] using hmajor
  constructor
  · simpa [u] using hnonpos
  · simpa [u] using haxis

end Burkholder

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/--
The martingale difference sequence associated to a discrete real-valued process.

With this convention, `martingaleDiff f 0 = f 0` and
`martingaleDiff f (n + 1) = f (n + 1) - f n`.
-/
def martingaleDiff (f : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => f 0
  | n + 1 => f (n + 1) - f n

/--
The discrete martingale transform of `f` by the multiplier process `v`.

If `f` has difference sequence `d`, then the transformed process has
difference sequence `v n * d n`.
-/
def martingaleTransform (v f : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n => (Finset.range (n + 1)).sum fun i => v i * martingaleDiff f i

/-- Notation `v ⋆ₘ f` for the discrete martingale transform of `f` by `v`. -/
scoped infixl:70 " ⋆ₘ " => martingaleTransform

/--
`g` is the martingale transform of the martingale `f` by a strongly predictable multiplier `v`,
relative to the filtration `ℱ` and measure `μ`.
-/
def IsMartingaleTransform (ℱ : Filtration ℕ mΩ) (μ : Measure Ω)
    (v f g : ℕ → Ω → ℝ) : Prop :=
  IsStronglyPredictable ℱ v ∧ Martingale f ℱ μ ∧ g = v ⋆ₘ f

@[simp]
private lemma martingaleTransform_zero (v f : ℕ → Ω → ℝ) :
    (v ⋆ₘ f) 0 = v 0 * f 0 := by
  ext ω
  simp [martingaleTransform, martingaleDiff]

private lemma martingaleTransform_succ_sub (v f : ℕ → Ω → ℝ) (n : ℕ) :
    (v ⋆ₘ f) (n + 1) - (v ⋆ₘ f) n =
      v (n + 1) * (f (n + 1) - f n) := by
  ext ω
  simp [martingaleTransform, martingaleDiff, Finset.sum_range_succ]

/--
A strongly predictable transform of a martingale is a martingale, once the usual
integrability and adaptedness hypotheses for the transformed process are available.

The only integrability assumption specific to the multiplier is that each product
`v (n+1) * (f (n+1) - f n)` is integrable; predictability then pulls `v (n+1)`
out of the conditional expectation.
-/
theorem martingaleTransform_martingale {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℕ mΩ} {v f : ℕ → Ω → ℝ}
  (hv : IsStronglyPredictable ℱ v) (hf : Martingale f ℱ μ)
  (hbounded : ∃ C, ∀ n ω, |v n ω| ≤ C) :
  Martingale (v ⋆ₘ f) ℱ μ := by
  rcases hbounded with ⟨C, hC⟩
  have hv_bound : ∀ n ω, ‖v n ω‖ ≤ |C| := by
    intro n ω
    simpa [Real.norm_eq_abs] using (hC n ω).trans (le_abs_self C)
  have hv_adapted : StronglyAdapted ℱ v := IsStronglyPredictable.stronglyAdapted hv
  have hdiff_integrable : ∀ n, Integrable (martingaleDiff f n) μ := by
    intro n
    cases n with
    | zero =>
        simpa [martingaleDiff] using hf.integrable 0
    | succ n =>
        simpa [martingaleDiff] using (hf.integrable (n + 1)).sub (hf.integrable n)
  have hdiff_measurable_le :
      ∀ {i n : ℕ}, i ≤ n → StronglyMeasurable[ℱ n] (martingaleDiff f i) := by
    intro i n hin
    cases i with
    | zero =>
        simpa [martingaleDiff] using
          hf.stronglyAdapted.stronglyMeasurable_le (Nat.zero_le n)
    | succ i =>
        have hi_succ : i + 1 ≤ n := hin
        have hi : i ≤ n := Nat.le_trans (Nat.le_succ i) hi_succ
        simpa [martingaleDiff] using
          (hf.stronglyAdapted.stronglyMeasurable_le hi_succ).sub
            (hf.stronglyAdapted.stronglyMeasurable_le hi)
  have hprod_all : ∀ n, Integrable (v n * martingaleDiff f n) μ := by
    intro n
    have hv_meas : AEStronglyMeasurable (v n) μ :=
      ((hv_adapted n).mono (ℱ.le n)).aestronglyMeasurable
    have hb : ∀ᵐ ω ∂μ, ‖v n ω‖ ≤ |C| := ae_of_all _ (hv_bound n)
    simpa [Pi.smul_apply, smul_eq_mul] using
      (hdiff_integrable n).bdd_smul |C| hv_meas hb
  have hadapt : StronglyAdapted ℱ (v ⋆ₘ f) := by
    intro n
    simpa [martingaleTransform, Finset.sum_apply] using
      (Finset.stronglyMeasurable_sum (Finset.range (n + 1)) fun i hi => by
        have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact (hv_adapted.stronglyMeasurable_le hin).mul (hdiff_measurable_le hin))
  have hint : ∀ n, Integrable ((v ⋆ₘ f) n) μ := by
    intro n
    simpa [martingaleTransform, Finset.sum_apply] using
      (integrable_finsetSum' (Finset.range (n + 1)) fun i _ => hprod_all i)
  have hprod : ∀ n, Integrable (v (n + 1) * (f (n + 1) - f n)) μ := by
    intro n
    simpa [martingaleDiff] using hprod_all (n + 1)
  refine martingale_of_condExp_sub_eq_zero_nat hadapt hint ?_
  intro n
  have hvmeas : StronglyMeasurable[ℱ n] (v (n + 1)) :=
    IsStronglyPredictable.measurable_add_one hv n
  have hdiff_int : Integrable (f (n + 1) - f n) μ :=
    (hf.integrable (n + 1)).sub (hf.integrable n)
  have hdiff_zero :
      μ[f (n + 1) - f n | ℱ n] =ᵐ[μ] 0 := by
    have hnext : μ[f (n + 1) | ℱ n] =ᵐ[μ] f n :=
      hf.condExp_ae_eq (Nat.le_succ n)
    have hcurr : μ[f n | ℱ n] =ᵐ[μ] f n := by
      rw [condExp_of_stronglyMeasurable (ℱ.le n) (hf.stronglyMeasurable n) (hf.integrable n)]
    calc
      μ[f (n + 1) - f n | ℱ n]
          =ᵐ[μ] μ[f (n + 1) | ℱ n] - μ[f n | ℱ n] :=
            condExp_sub (hf.integrable (n + 1)) (hf.integrable n) (ℱ n)
      _ =ᵐ[μ] f n - f n := hnext.sub hcurr
      _ =ᵐ[μ] 0 := by simp
  have hpull :
      μ[v (n + 1) * (f (n + 1) - f n) | ℱ n]
        =ᵐ[μ] v (n + 1) * μ[f (n + 1) - f n | ℱ n] :=
    condExp_mul_of_stronglyMeasurable_left hvmeas (hprod n) hdiff_int
  calc
    μ[(v ⋆ₘ f) (n + 1) - (v ⋆ₘ f) n | ℱ n]
        =ᵐ[μ] μ[v (n + 1) * (f (n + 1) - f n) | ℱ n] := by
          rw [martingaleTransform_succ_sub]
    _ =ᵐ[μ] v (n + 1) * μ[f (n + 1) - f n | ℱ n] := hpull
    _ =ᵐ[μ] 0 := by
      filter_upwards [hdiff_zero] with ω hω
      simp [hω]

/--
Theorem 2.2, inequality (2.13): martingale transforms by strongly predictable
multipliers bounded by `1` are bounded on `L^p`, for `1 < p < ∞`.

This is stated at each finite time `n` for the discrete transform `v ⋆ₘ f`.
-/
private def plusOne (w : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n ω => w n ω + 1

private def minusOne (w : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n ω => w n ω - 1






/-- Notation `X_{n}[w,f]` for the `n`-th term of the transform of `f` by `plusOne w`. -/
scoped notation "X_{" n "}[" w "," f "]" => ((plusOne w) ⋆ₘ f) n
/-- Notation `Y_{n}[w,f]` for the `n`-th term of the transform of `f` by `minusOne w`. -/
scoped notation "Y_{" n "}[" w "," f "]" => ((minusOne w) ⋆ₘ f) n

/--
Common assumptions for Burkholder-type martingale transform inequalities.
-/
private structure BurkholderAssumptions (p : ℝ≥0∞) (Ω : Type*)
  [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
  [IsFiniteMeasure μ] (ℱ : Filtration ℕ mΩ) (w f : ℕ → Ω → ℝ) : Prop where
  hp_one : 1 < p.toReal
  hp_top : p ≠ ∞
  hstrong : IsStronglyPredictable ℱ w
  hmart : Martingale f ℱ μ
  hLp : ∀ n, MemLp (f n) p μ
  hbound : ∀ n, ∀ᵐ ω ∂μ, |w n ω| ≤ 1








private lemma inequality_for_transform_differences
    {p : ℝ≥0∞} {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ mΩ} {w f : ℕ → Ω → ℝ}
    (h : BurkholderAssumptions p Ω μ ℱ w f) :
        (∀ n, ∀ᵐ ω ∂μ,
          (X_{n+1}[w, f] ω -X_{n}[w, f] ω) * (Y_{n+1}[w, f] ω -Y_{n}[w, f] ω) ≤ 0) ∧
        (∀ᵐ ω ∂μ,
          (X_{0}[w, f] ω *
              Y_{0}[w, f] ω ≤ 0)) := by
  constructor
  · intro n
    filter_upwards [h.hbound (n + 1)] with ω hwω
    have hplus :
        X_{n+1}[w, f] ω - X_{n}[w, f] ω =
          (w (n + 1) ω + 1) * (f (n + 1) ω - f n ω) := by
      simpa [plusOne] using congrFun (martingaleTransform_succ_sub (plusOne w) f n) ω
    have hminus :
        Y_{n+1}[w, f] ω - Y_{n}[w, f] ω =
          (w (n + 1) ω - 1) * (f (n + 1) ω - f n ω) := by
      simpa [minusOne] using congrFun (martingaleTransform_succ_sub (minusOne w) f n) ω
    have hsq_nonneg : 0 ≤ (f (n + 1) ω - f n ω) ^ 2 :=
      sq_nonneg (f (n + 1) ω - f n ω)
    have hw_sq_succ : w (n + 1) ω ^ 2 ≤ 1 := by
      have hneg : -1 ≤ w (n + 1) ω := (abs_le.mp hwω).1
      have hpos : w (n + 1) ω ≤ 1 := (abs_le.mp hwω).2
      nlinarith [sq_nonneg (w (n + 1) ω - 1),
        sq_nonneg (w (n + 1) ω + 1)]
    calc
      (X_{n+1}[w, f] ω - X_{n}[w, f] ω) *
          (Y_{n+1}[w, f] ω - Y_{n}[w, f] ω)
          = ((w (n + 1) ω) ^ 2 - 1) *
              ((f (n + 1) ω - f n ω) ^ 2) := by
            rw [hplus, hminus]
            ring
      _ ≤ 0 := by nlinarith
  · filter_upwards [h.hbound 0] with ω hwω
    have hw_sq : w 0 ω ^ 2 ≤ 1 := by
      have hneg : -1 ≤ w 0 ω := (abs_le.mp hwω).1
      have hpos : w 0 ω ≤ 1 := (abs_le.mp hwω).2
      nlinarith [sq_nonneg (w 0 ω - 1), sq_nonneg (w 0 ω + 1)]
    have hsq_nonneg : 0 ≤ f 0 ω ^ 2 := sq_nonneg (f 0 ω)
    calc
      X_{0}[w, f] ω *
          Y_{0}[w, f] ω
          = ((w 0 ω) ^ 2 - 1) * (f 0 ω ^ 2) := by
            simp [plusOne, minusOne, martingaleTransform, martingaleDiff]
            ring
      _ ≤ 0 := by nlinarith

private lemma burkholder_martingaleDiff_memLp
    {p : ℝ≥0∞} {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ mΩ} {w f : ℕ → Ω → ℝ}
    (h : BurkholderAssumptions p Ω μ ℱ w f) (n : ℕ) :
    MemLp (martingaleDiff f n) p μ := by
  cases n with
  | zero =>
      simpa [martingaleDiff] using h.hLp 0
  | succ n =>
      simpa [martingaleDiff] using (h.hLp (n + 1)).sub (h.hLp n)

private lemma burkholder_plusOne_mul_martingaleDiff_memLp
    {p : ℝ≥0∞} {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ mΩ} {w f : ℕ → Ω → ℝ}
    (h : BurkholderAssumptions p Ω μ ℱ w f) (n : ℕ) :
    MemLp (fun ω => plusOne w n ω * martingaleDiff f n ω) p μ := by
  have hw_adapted : StronglyAdapted ℱ w :=
    IsStronglyPredictable.stronglyAdapted h.hstrong
  have hw_meas : AEStronglyMeasurable (w n) μ :=
    ((hw_adapted n).mono (ℱ.le n)).aestronglyMeasurable
  have hcoeff_meas : AEStronglyMeasurable (plusOne w n) μ := by
    exact hw_meas.add aestronglyMeasurable_const
  refine MemLp.of_le_mul (c := (2 : ℝ)) (burkholder_martingaleDiff_memLp h n)
    (hcoeff_meas.mul (burkholder_martingaleDiff_memLp h n).1) ?_
  filter_upwards [h.hbound n] with ω hwω
  have hcoeff : |plusOne w n ω| ≤ 2 := by
    rw [plusOne, abs_le]
    have hw := abs_le.mp hwω
    constructor <;> linarith
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hcoeff (abs_nonneg (martingaleDiff f n ω))

private lemma burkholder_minusOne_mul_martingaleDiff_memLp
    {p : ℝ≥0∞} {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ mΩ} {w f : ℕ → Ω → ℝ}
    (h : BurkholderAssumptions p Ω μ ℱ w f) (n : ℕ) :
    MemLp (fun ω => minusOne w n ω * martingaleDiff f n ω) p μ := by
  have hw_adapted : StronglyAdapted ℱ w :=
    IsStronglyPredictable.stronglyAdapted h.hstrong
  have hw_meas : AEStronglyMeasurable (w n) μ :=
    ((hw_adapted n).mono (ℱ.le n)).aestronglyMeasurable
  have hcoeff_meas : AEStronglyMeasurable (minusOne w n) μ := by
    exact hw_meas.sub aestronglyMeasurable_const
  refine MemLp.of_le_mul (c := (2 : ℝ)) (burkholder_martingaleDiff_memLp h n)
    (hcoeff_meas.mul (burkholder_martingaleDiff_memLp h n).1) ?_
  filter_upwards [h.hbound n] with ω hwω
  have hcoeff : |minusOne w n ω| ≤ 2 := by
    rw [minusOne, abs_le]
    have hw := abs_le.mp hwω
    constructor <;> linarith
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hcoeff (abs_nonneg (martingaleDiff f n ω))


/-- Lp integrability of X_n, Y_n, v(X_n,Y_n). -/
private lemma burkholder_X_memLp
    {p : ℝ≥0∞} {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ mΩ} {w f : ℕ → Ω → ℝ}
    (h : BurkholderAssumptions p Ω μ ℱ w f) (n : ℕ) :
    MemLp (X_{n}[w, f]) p μ := by
  rw [martingaleTransform]
  exact memLp_finsetSum' (Finset.range (n + 1))
    (fun i _hi => burkholder_plusOne_mul_martingaleDiff_memLp h i)

private lemma burkholder_Y_memLp
    {p : ℝ≥0∞} {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ mΩ} {w f : ℕ → Ω → ℝ}
    (h : BurkholderAssumptions p Ω μ ℱ w f) (n : ℕ) :
    MemLp (Y_{n}[w, f]) p μ := by
  rw [martingaleTransform]
  exact memLp_finsetSum' (Finset.range (n + 1))
    (fun i _hi => burkholder_minusOne_mul_martingaleDiff_memLp h i)



private lemma burkholder_v_XY_integrable
  {p : ℝ≥0∞} {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℕ mΩ} {w f : ℕ → Ω → ℝ}
  (h : BurkholderAssumptions p Ω μ ℱ w f) (n : ℕ) :
  Integrable
    (fun ω => Burkholder.v p.toReal (X_{n}[w, f] ω) (Y_{n}[w, f] ω)) μ := by
  have hX : MemLp (X_{n}[w, f]) p μ := burkholder_X_memLp h n
  have hY : MemLp (Y_{n}[w, f]) p μ := burkholder_Y_memLp h n
  have hsum : MemLp
      (fun ω => (X_{n}[w, f] ω + Y_{n}[w, f] ω) / 2) p μ := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (hX.add hY).const_mul (1 / 2 : ℝ)
  have hdiff : MemLp
      (fun ω => (X_{n}[w, f] ω - Y_{n}[w, f] ω) / 2) p μ := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (hX.sub hY).const_mul (1 / 2 : ℝ)
  have hsum_pow :
      Integrable
        (fun ω => Real.rpow (|(X_{n}[w, f] ω + Y_{n}[w, f] ω)| / 2) p.toReal) μ := by
    simpa [Real.norm_eq_abs] using hsum.integrable_norm_rpow'
  have hdiff_pow :
      Integrable
        (fun ω => Real.rpow (|(X_{n}[w, f] ω - Y_{n}[w, f] ω)| / 2) p.toReal) μ := by
    simpa [Real.norm_eq_abs] using hdiff.integrable_norm_rpow'
  have hterm := hsum_pow.sub
    (hdiff_pow.const_mul
      (Real.rpow (|Majorants.pStar p.toReal - 1|) p.toReal))
  simp only [Burkholder.v, Majorants.v, abs_div, abs_two] at hterm ⊢
  exact hterm

/-- Lp integrability of `u(X_n,Y_n)`. -/
private lemma burkholder_u_Xn_Yn_integrable
  {p : ℝ≥0∞} {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℕ mΩ} {w f : ℕ → Ω → ℝ}
  (h : BurkholderAssumptions p Ω μ ℱ w f) (n : ℕ) :
  Integrable
    (fun ω =>
      Burkholder.u p.toReal h.hp_one
        (X_{n}[w, f] ω) (Y_{n}[w, f] ω)) μ := by
  rcases Classical.choose_spec
      (Majorants.exists_majorant_p_g_1 p.toReal h.hp_one) with
    ⟨du_dx, du_dy, C, hC_nonneg,
      hu_cont, hdu_dx_cont, hdu_dy_cont,
      hu_growth, hdu_dx_growth, hdu_dy_growth,
      htangent, hmajor, hnonpos, haxis⟩
  have hX : MemLp (X_{n}[w, f]) p μ :=
    burkholder_X_memLp h n
  have hY : MemLp (Y_{n}[w, f]) p μ :=
    burkholder_Y_memLp h n
  have hXpow :
      Integrable
        (fun ω => Real.rpow |X_{n}[w, f] ω| p.toReal) μ := by
    simpa [Real.norm_eq_abs] using hX.integrable_norm_rpow'
  have hYpow :
      Integrable
        (fun ω => Real.rpow |Y_{n}[w, f] ω| p.toReal) μ := by
    simpa [Real.norm_eq_abs] using hY.integrable_norm_rpow'
  have hdom :
      Integrable
        (fun ω =>
          C *
            (Real.rpow |X_{n}[w, f] ω| p.toReal
              + Real.rpow |Y_{n}[w, f] ω| p.toReal)) μ := by
    simpa using (hXpow.add hYpow).const_mul C
  have hu_cont_global :
      Continuous
        (fun z : ℝ × ℝ =>
          Burkholder.u p.toReal h.hp_one z.1 z.2) := by
    rw [← continuousOn_univ]
    simpa [Burkholder.u] using hu_cont
  have hpair_meas :
      AEStronglyMeasurable
        (fun ω => (X_{n}[w, f] ω, Y_{n}[w, f] ω)) μ :=
    hX.1.prodMk hY.1
  have hu_meas :
      AEStronglyMeasurable
        (fun ω =>
          Burkholder.u p.toReal h.hp_one
            (X_{n}[w, f] ω) (Y_{n}[w, f] ω)) μ := by
    simpa using hu_cont_global.comp_aestronglyMeasurable hpair_meas
  exact hdom.mono' hu_meas <| by
    filter_upwards with ω
    simpa [Real.norm_eq_abs, Burkholder.u] using
      hu_growth (X_{n}[w, f] ω) (Y_{n}[w, f] ω)

/-- `du_dx(X_n,Y_n)` belongs to `L^q`, where `q = p/(p-1)`. -/
private lemma burkholder_du_dx_Xn_Yn_Lq
  {p : ℝ≥0∞} {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℕ mΩ} {w f : ℕ → Ω → ℝ}
  (h : BurkholderAssumptions p Ω μ ℱ w f) (n : ℕ) :
  MemLp
    (fun ω =>
      Burkholder.du_dx p.toReal h.hp_one
        (X_{n}[w, f] ω) (Y_{n}[w, f] ω))
    (ENNReal.ofReal (Burkholder.q p.toReal)) μ := by
  let r : ℝ := p.toReal - 1
  let q : ℝ := Burkholder.q p.toReal
  change
    MemLp
      (fun ω =>
        Burkholder.du_dx p.toReal h.hp_one
          (X_{n}[w, f] ω) (Y_{n}[w, f] ω))
      (ENNReal.ofReal q) μ
  have hr_pos : 0 < r := by
    dsimp [r]
    linarith [h.hp_one]
  have hp_toReal_pos : 0 < p.toReal := by
    linarith [h.hp_one]
  have hp_eq_ofReal : p = ENNReal.ofReal p.toReal := by
    exact (ENNReal.ofReal_toReal h.hp_top).symm
  have hq_eq :
      ENNReal.ofReal q = p / ENNReal.ofReal r := by
    rw [hp_eq_ofReal]
    dsimp [q, r, Burkholder.q, Majorants.q]
    rw [if_neg (by linarith [h.hp_one])]
    rw [ENNReal.ofReal_div_of_pos]
    exact hr_pos
  have hX : MemLp (X_{n}[w, f]) p μ :=
    burkholder_X_memLp h n
  have hY : MemLp (Y_{n}[w, f]) p μ :=
    burkholder_Y_memLp h n
  have hXpow₀ :
      MemLp
        (fun ω => ‖X_{n}[w, f] ω‖ ^ (ENNReal.ofReal r).toReal)
        (p / ENNReal.ofReal r) μ :=
    hX.norm_rpow_div (ENNReal.ofReal r)
  have hYpow₀ :
      MemLp
        (fun ω => ‖Y_{n}[w, f] ω‖ ^ (ENNReal.ofReal r).toReal)
        (p / ENNReal.ofReal r) μ :=
    hY.norm_rpow_div (ENNReal.ofReal r)
  have hXpow :
      MemLp
        (fun ω => Real.rpow |X_{n}[w, f] ω| r)
        (ENNReal.ofReal q) μ := by
    rw [hq_eq]
    simpa [r, Real.norm_eq_abs, ENNReal.toReal_ofReal hr_pos.le] using hXpow₀
  have hYpow :
      MemLp
        (fun ω => Real.rpow |Y_{n}[w, f] ω| r)
        (ENNReal.ofReal q) μ := by
    rw [hq_eq]
    simpa [r, Real.norm_eq_abs, ENNReal.toReal_ofReal hr_pos.le] using hYpow₀
  have hsum :
      MemLp
        (fun ω =>
          Real.rpow |X_{n}[w, f] ω| r
            + Real.rpow |Y_{n}[w, f] ω| r)
        (ENNReal.ofReal q) μ := by
    exact hXpow.add hYpow
  have hpair_meas :
      AEStronglyMeasurable
        (fun ω => (X_{n}[w, f] ω, Y_{n}[w, f] ω)) μ :=
    hX.aestronglyMeasurable.prodMk hY.aestronglyMeasurable
  have hdu_cont_global :
      Continuous
        (fun z : ℝ × ℝ =>
          Burkholder.du_dx p.toReal h.hp_one z.1 z.2) := by
    rw [← continuousOn_univ]
    exact Burkholder.du_dx_continuousOn p.toReal h.hp_one
  have hdu_meas :
      AEStronglyMeasurable
        (fun ω =>
          Burkholder.du_dx p.toReal h.hp_one
            (X_{n}[w, f] ω) (Y_{n}[w, f] ω)) μ := by
    simpa using hdu_cont_global.comp_aestronglyMeasurable hpair_meas
  have hbound :
      ∀ᵐ ω ∂μ,
        ‖Burkholder.du_dx p.toReal h.hp_one
            (X_{n}[w, f] ω) (Y_{n}[w, f] ω)‖
          ≤
        Burkholder.C p.toReal h.hp_one *
          ‖Real.rpow |X_{n}[w, f] ω| r
            + Real.rpow |Y_{n}[w, f] ω| r‖ := by
    filter_upwards with ω
    have hsum_nonneg :
        0 ≤
          Real.rpow |X_{n}[w, f] ω| r
            + Real.rpow |Y_{n}[w, f] ω| r := by
      exact add_nonneg
        (Real.rpow_nonneg (abs_nonneg _) r)
        (Real.rpow_nonneg (abs_nonneg _) r)
    have hnorm :
        ‖Real.rpow |X_{n}[w, f] ω| r
            + Real.rpow |Y_{n}[w, f] ω| r‖ =
          Real.rpow |X_{n}[w, f] ω| r
            + Real.rpow |Y_{n}[w, f] ω| r := by
      simpa [Real.norm_eq_abs] using abs_of_nonneg hsum_nonneg
    rw [hnorm]
    simpa [r, Real.norm_eq_abs] using
      Burkholder.du_dx_growth_bound p.toReal h.hp_one
        (X_{n}[w, f] ω) (Y_{n}[w, f] ω)
  exact hsum.of_le_mul hdu_meas hbound

/-- `du_dy(X_n,Y_n)` belongs to `L^q`, where `q = p/(p-1)`. -/
private lemma burkholder_du_dy_Xn_Yn_Lq
  {p : ℝ≥0∞} {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℕ mΩ} {w f : ℕ → Ω → ℝ}
  (h : BurkholderAssumptions p Ω μ ℱ w f) (n : ℕ) :
  MemLp
    (fun ω =>
      Burkholder.du_dy p.toReal h.hp_one
        (X_{n}[w, f] ω) (Y_{n}[w, f] ω))
    (ENNReal.ofReal (Burkholder.q p.toReal)) μ := by
  let r : ℝ := p.toReal - 1
  let q : ℝ := Burkholder.q p.toReal
  change
    MemLp
      (fun ω =>
        Burkholder.du_dy p.toReal h.hp_one
          (X_{n}[w, f] ω) (Y_{n}[w, f] ω))
      (ENNReal.ofReal q) μ
  have hr_pos : 0 < r := by
    dsimp [r]
    linarith [h.hp_one]
  have hp_eq_ofReal : p = ENNReal.ofReal p.toReal := by
    exact (ENNReal.ofReal_toReal h.hp_top).symm
  have hq_eq :
      ENNReal.ofReal q = p / ENNReal.ofReal r := by
    rw [hp_eq_ofReal]
    dsimp [q, r, Burkholder.q, Majorants.q]
    rw [if_neg (by linarith [h.hp_one])]
    rw [ENNReal.ofReal_div_of_pos]
    exact hr_pos
  have hX : MemLp (X_{n}[w, f]) p μ :=
    burkholder_X_memLp h n
  have hY : MemLp (Y_{n}[w, f]) p μ :=
    burkholder_Y_memLp h n
  have hXpow₀ :
      MemLp
        (fun ω => ‖X_{n}[w, f] ω‖ ^ (ENNReal.ofReal r).toReal)
        (p / ENNReal.ofReal r) μ :=
    hX.norm_rpow_div (ENNReal.ofReal r)
  have hYpow₀ :
      MemLp
        (fun ω => ‖Y_{n}[w, f] ω‖ ^ (ENNReal.ofReal r).toReal)
        (p / ENNReal.ofReal r) μ :=
    hY.norm_rpow_div (ENNReal.ofReal r)
  have hXpow :
      MemLp
        (fun ω => Real.rpow |X_{n}[w, f] ω| r)
        (ENNReal.ofReal q) μ := by
    rw [hq_eq]
    simpa [r, Real.norm_eq_abs, ENNReal.toReal_ofReal hr_pos.le] using hXpow₀
  have hYpow :
      MemLp
        (fun ω => Real.rpow |Y_{n}[w, f] ω| r)
        (ENNReal.ofReal q) μ := by
    rw [hq_eq]
    simpa [r, Real.norm_eq_abs, ENNReal.toReal_ofReal hr_pos.le] using hYpow₀
  have hsum :
      MemLp
        (fun ω =>
          Real.rpow |X_{n}[w, f] ω| r
            + Real.rpow |Y_{n}[w, f] ω| r)
        (ENNReal.ofReal q) μ := by
    exact hXpow.add hYpow
  have hpair_meas :
      AEStronglyMeasurable
        (fun ω => (X_{n}[w, f] ω, Y_{n}[w, f] ω)) μ :=
    hX.aestronglyMeasurable.prodMk hY.aestronglyMeasurable
  have hdu_cont_global :
      Continuous
        (fun z : ℝ × ℝ =>
          Burkholder.du_dy p.toReal h.hp_one z.1 z.2) := by
    rw [← continuousOn_univ]
    exact Burkholder.du_dy_continuousOn p.toReal h.hp_one
  have hdu_meas :
      AEStronglyMeasurable
        (fun ω =>
          Burkholder.du_dy p.toReal h.hp_one
            (X_{n}[w, f] ω) (Y_{n}[w, f] ω)) μ := by
    simpa using hdu_cont_global.comp_aestronglyMeasurable hpair_meas
  have hbound :
      ∀ᵐ ω ∂μ,
        ‖Burkholder.du_dy p.toReal h.hp_one
            (X_{n}[w, f] ω) (Y_{n}[w, f] ω)‖
          ≤
        Burkholder.C p.toReal h.hp_one *
          ‖Real.rpow |X_{n}[w, f] ω| r
            + Real.rpow |Y_{n}[w, f] ω| r‖ := by
    filter_upwards with ω
    have hsum_nonneg :
        0 ≤
          Real.rpow |X_{n}[w, f] ω| r
            + Real.rpow |Y_{n}[w, f] ω| r := by
      exact add_nonneg
        (Real.rpow_nonneg (abs_nonneg _) r)
        (Real.rpow_nonneg (abs_nonneg _) r)
    have hnorm :
        ‖Real.rpow |X_{n}[w, f] ω| r
            + Real.rpow |Y_{n}[w, f] ω| r‖ =
          Real.rpow |X_{n}[w, f] ω| r
            + Real.rpow |Y_{n}[w, f] ω| r := by
      simpa [Real.norm_eq_abs] using abs_of_nonneg hsum_nonneg
    rw [hnorm]
    simpa [r, Real.norm_eq_abs] using
      Burkholder.du_dy_growth_bound p.toReal h.hp_one
        (X_{n}[w, f] ω) (Y_{n}[w, f] ω)
  exact hsum.of_le_mul hdu_meas hbound

private lemma burkholder_du_dx_Xn_Yn_integrable_mul_diff
  {p : ℝ≥0∞} {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℕ mΩ} {w f : ℕ → Ω → ℝ}
  (h : BurkholderAssumptions p Ω μ ℱ w f) (n : ℕ) :
  Integrable (fun ω => Burkholder.du_dx p.toReal h.hp_one
        (X_{n}[w, f] ω) (Y_{n}[w, f] ω) *
            (X_{n+1}[w, f] ω - X_{n}[w, f] ω)) μ ∧
            ∫ ω, Burkholder.du_dx p.toReal h.hp_one
        (X_{n}[w, f] ω) (Y_{n}[w, f] ω) *
            (X_{n+1}[w, f] ω - X_{n}[w, f] ω) ∂μ = 0 := by
  let q : ℝ := Burkholder.q p.toReal
  have hpq_real : q.HolderConjugate p.toReal := by
    dsimp [q, Burkholder.q, Majorants.q]
    rw [if_neg (by linarith [h.hp_one])]
    exact (Real.HolderConjugate.conjExponent h.hp_one).symm
  have hpq : ENNReal.HolderConjugate (ENNReal.ofReal q) (ENNReal.ofReal p.toReal) := by
    rw [ENNReal.holderConjugate_iff]
    have hp_pos : 0 < p.toReal := by linarith [h.hp_one]
    have hq_pos : 0 < q := zero_lt_one.trans (Real.holderConjugate_iff.mp hpq_real).1
    rw [← ENNReal.ofReal_inv_of_pos hq_pos]
    rw [← ENNReal.ofReal_inv_of_pos hp_pos]
    rw [← ENNReal.ofReal_add]
    · rw [hpq_real.inv_add_inv_eq_one]
      simp
    · exact inv_nonneg.mpr hq_pos.le
    · exact inv_nonneg.mpr hp_pos.le
  have hdu : MemLp
      (fun ω =>
        Burkholder.du_dx p.toReal h.hp_one
          (X_{n}[w, f] ω) (Y_{n}[w, f] ω))
      (ENNReal.ofReal q) μ := by
    simpa [q] using burkholder_du_dx_Xn_Yn_Lq h n
  have hXdiff_memLp : MemLp
      (fun ω => X_{n+1}[w, f] ω - X_{n}[w, f] ω) p μ := by
    have hXdiff_eq :
        (fun ω => X_{n+1}[w, f] ω - X_{n}[w, f] ω) =
          fun ω => plusOne w (n + 1) ω * martingaleDiff f (n + 1) ω := by
      funext ω
      simpa [martingaleDiff] using congrFun (martingaleTransform_succ_sub (plusOne w) f n) ω
    rw [hXdiff_eq]
    exact burkholder_plusOne_mul_martingaleDiff_memLp h (n + 1)
  have hp_eq_ofReal : p = ENNReal.ofReal p.toReal := by
    exact (ENNReal.ofReal_toReal h.hp_top).symm
  have hmul_int : Integrable
      (fun ω =>
        Burkholder.du_dx p.toReal h.hp_one
          (X_{n}[w, f] ω) (Y_{n}[w, f] ω) *
            (X_{n+1}[w, f] ω - X_{n}[w, f] ω)) μ := by
    rw [hp_eq_ofReal] at hXdiff_memLp
    letI : ENNReal.HolderTriple (ENNReal.ofReal q) (ENNReal.ofReal p.toReal) 1 := hpq
    exact MemLp.integrable_mul hdu hXdiff_memLp
  constructor
  · exact hmul_int
  · have hw_adapted : StronglyAdapted ℱ w :=
      IsStronglyPredictable.stronglyAdapted h.hstrong
    have hdiff_measurable_le :
        ∀ {i n : ℕ}, i ≤ n → StronglyMeasurable[ℱ n] (martingaleDiff f i) := by
      intro i n hin
      cases i with
      | zero =>
          simpa [martingaleDiff] using
            h.hmart.stronglyAdapted.stronglyMeasurable_le (Nat.zero_le n)
      | succ i =>
          have hi_succ : i + 1 ≤ n := hin
          have hi : i ≤ n := Nat.le_trans (Nat.le_succ i) hi_succ
          simpa [martingaleDiff] using
            (h.hmart.stronglyAdapted.stronglyMeasurable_le hi_succ).sub
              (h.hmart.stronglyAdapted.stronglyMeasurable_le hi)
    have hplus_meas_le :
        ∀ {i n : ℕ}, i ≤ n → StronglyMeasurable[ℱ n] (plusOne w i) := by
      intro i n hin
      have hw_meas : StronglyMeasurable[ℱ n] (w i) :=
        hw_adapted.stronglyMeasurable_le hin
      exact
        hw_meas.add (measurable_const.stronglyMeasurable)
    have hminus_meas_le :
        ∀ {i n : ℕ}, i ≤ n → StronglyMeasurable[ℱ n] (minusOne w i) := by
      intro i n hin
      have hw_meas : StronglyMeasurable[ℱ n] (w i) :=
        hw_adapted.stronglyMeasurable_le hin
      exact
        hw_meas.sub (measurable_const.stronglyMeasurable)
    have hX_meas : StronglyMeasurable[ℱ n] (X_{n}[w, f]) := by
      rw [martingaleTransform]
      exact Finset.stronglyMeasurable_sum (Finset.range (n + 1)) fun i hi => by
        have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact (hplus_meas_le hin).mul (hdiff_measurable_le hin)
    have hY_meas : StronglyMeasurable[ℱ n] (Y_{n}[w, f]) := by
      rw [martingaleTransform]
      exact Finset.stronglyMeasurable_sum (Finset.range (n + 1)) fun i hi => by
        have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact (hminus_meas_le hin).mul (hdiff_measurable_le hin)
    have hdu_cont_global :
        Continuous
          (fun z : ℝ × ℝ =>
            Burkholder.du_dx p.toReal h.hp_one z.1 z.2) := by
      rw [← continuousOn_univ]
      exact Burkholder.du_dx_continuousOn p.toReal h.hp_one
    have hA_meas :
        StronglyMeasurable[ℱ n]
          (fun ω =>
            Burkholder.du_dx p.toReal h.hp_one
              (X_{n}[w, f] ω) (Y_{n}[w, f] ω)) := by
      simpa using hdu_cont_global.comp_stronglyMeasurable
        (hX_meas.prodMk hY_meas)
    have hp_one_en : (1 : ℝ≥0∞) ≤ p := by
      rw [hp_eq_ofReal]
      simpa using ENNReal.ofReal_le_ofReal h.hp_one.le
    have hXdiff_int :
        Integrable (fun ω => X_{n+1}[w, f] ω - X_{n}[w, f] ω) μ :=
      hXdiff_memLp.integrable hp_one_en
    have hfdiff_int : Integrable (fun ω => f (n + 1) ω - f n ω) μ :=
      (h.hmart.integrable (n + 1)).sub (h.hmart.integrable n)
    have hfdiff_zero :
        μ[f (n + 1) - f n | ℱ n] =ᵐ[μ] 0 := by
      have hnext : μ[f (n + 1) | ℱ n] =ᵐ[μ] f n :=
        h.hmart.condExp_ae_eq (Nat.le_succ n)
      have hcurr : μ[f n | ℱ n] =ᵐ[μ] f n := by
        rw [condExp_of_stronglyMeasurable (ℱ.le n)
          (h.hmart.stronglyMeasurable n) (h.hmart.integrable n)]
      calc
        μ[f (n + 1) - f n | ℱ n]
            =ᵐ[μ] μ[f (n + 1) | ℱ n] - μ[f n | ℱ n] :=
              condExp_sub (h.hmart.integrable (n + 1)) (h.hmart.integrable n) (ℱ n)
        _ =ᵐ[μ] f n - f n := hnext.sub hcurr
        _ =ᵐ[μ] 0 := by simp
    have hplus_succ_meas : StronglyMeasurable[ℱ n] (plusOne w (n + 1)) := by
      exact
        (IsStronglyPredictable.measurable_add_one h.hstrong n).add
          (measurable_const.stronglyMeasurable)
    have hXdiff_eq :
        (fun ω => X_{n+1}[w, f] ω - X_{n}[w, f] ω) =
          fun ω => plusOne w (n + 1) ω * (f (n + 1) ω - f n ω) := by
      funext ω
      simpa [plusOne, martingaleDiff] using
        congrFun (martingaleTransform_succ_sub (plusOne w) f n) ω
    have hplus_fdiff_int :
        Integrable
          (fun ω => plusOne w (n + 1) ω * (f (n + 1) ω - f n ω)) μ := by
      simpa [plusOne, martingaleDiff] using
        (burkholder_plusOne_mul_martingaleDiff_memLp h (n + 1)).integrable hp_one_en
    have hXdiff_zero :
        μ[(fun ω => X_{n+1}[w, f] ω - X_{n}[w, f] ω) | ℱ n] =ᵐ[μ] 0 := by
      have hpull :
          μ[(fun ω => plusOne w (n + 1) ω * (f (n + 1) ω - f n ω)) | ℱ n]
            =ᵐ[μ]
          (fun ω => plusOne w (n + 1) ω *
            μ[f (n + 1) - f n | ℱ n] ω) :=
        condExp_mul_of_stronglyMeasurable_left
          hplus_succ_meas hplus_fdiff_int hfdiff_int
      calc
        μ[(fun ω => X_{n+1}[w, f] ω - X_{n}[w, f] ω) | ℱ n]
            =ᵐ[μ]
          μ[(fun ω => plusOne w (n + 1) ω * (f (n + 1) ω - f n ω)) | ℱ n] := by
            rw [hXdiff_eq]
        _ =ᵐ[μ]
          (fun ω => plusOne w (n + 1) ω *
            μ[f (n + 1) - f n | ℱ n] ω) := hpull
        _ =ᵐ[μ] 0 := by
          filter_upwards [hfdiff_zero] with ω hω
          simp [hω]
    have hpull :
        μ[(fun ω =>
          Burkholder.du_dx p.toReal h.hp_one
            (X_{n}[w, f] ω) (Y_{n}[w, f] ω) *
              (X_{n+1}[w, f] ω - X_{n}[w, f] ω)) | ℱ n]
          =ᵐ[μ]
        (fun ω =>
          Burkholder.du_dx p.toReal h.hp_one
            (X_{n}[w, f] ω) (Y_{n}[w, f] ω) *
              μ[(fun ω => X_{n+1}[w, f] ω - X_{n}[w, f] ω) | ℱ n] ω) :=
      condExp_mul_of_stronglyMeasurable_left hA_meas hmul_int hXdiff_int
    calc
      (∫ ω, Burkholder.du_dx p.toReal h.hp_one
        (X_{n}[w, f] ω) (Y_{n}[w, f] ω) *
            (X_{n+1}[w, f] ω - X_{n}[w, f] ω) ∂μ)
          = ∫ ω, μ[(fun ω =>
              Burkholder.du_dx p.toReal h.hp_one
                (X_{n}[w, f] ω) (Y_{n}[w, f] ω) *
                  (X_{n+1}[w, f] ω - X_{n}[w, f] ω)) | ℱ n] ω ∂μ := by
            exact (integral_condExp (ℱ.le n)).symm
      _ = ∫ ω,
          Burkholder.du_dx p.toReal h.hp_one
            (X_{n}[w, f] ω) (Y_{n}[w, f] ω) *
              μ[(fun ω => X_{n+1}[w, f] ω - X_{n}[w, f] ω) | ℱ n] ω ∂μ := by
            exact integral_congr_ae hpull
      _ = 0 := by
        refine integral_eq_zero_of_ae ?_
        filter_upwards [hXdiff_zero] with ω hω
        simp [hω]

private lemma burkholder_du_dy_Xn_Yn_integrable_mul_diff
  {p : ℝ≥0∞} {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℕ mΩ} {w f : ℕ → Ω → ℝ}
  (h : BurkholderAssumptions p Ω μ ℱ w f) (n : ℕ) :
  Integrable (fun ω => Burkholder.du_dy p.toReal h.hp_one
        (X_{n}[w, f] ω) (Y_{n}[w, f] ω) *
            (Y_{n+1}[w, f] ω - Y_{n}[w, f] ω)) μ ∧
            ∫ ω, Burkholder.du_dy p.toReal h.hp_one
        (X_{n}[w, f] ω) (Y_{n}[w, f] ω) *
            (Y_{n+1}[w, f] ω - Y_{n}[w, f] ω) ∂μ = 0 := by
  let q : ℝ := Burkholder.q p.toReal
  have hpq_real : q.HolderConjugate p.toReal := by
    dsimp [q, Burkholder.q, Majorants.q]
    rw [if_neg (by linarith [h.hp_one])]
    exact (Real.HolderConjugate.conjExponent h.hp_one).symm
  have hpq : ENNReal.HolderConjugate (ENNReal.ofReal q) (ENNReal.ofReal p.toReal) := by
    rw [ENNReal.holderConjugate_iff]
    have hp_pos : 0 < p.toReal := by linarith [h.hp_one]
    have hq_pos : 0 < q := zero_lt_one.trans (Real.holderConjugate_iff.mp hpq_real).1
    rw [← ENNReal.ofReal_inv_of_pos hq_pos]
    rw [← ENNReal.ofReal_inv_of_pos hp_pos]
    rw [← ENNReal.ofReal_add]
    · rw [hpq_real.inv_add_inv_eq_one]
      simp
    · exact inv_nonneg.mpr hq_pos.le
    · exact inv_nonneg.mpr hp_pos.le
  have hdu : MemLp
      (fun ω =>
        Burkholder.du_dy p.toReal h.hp_one
          (X_{n}[w, f] ω) (Y_{n}[w, f] ω))
      (ENNReal.ofReal q) μ := by
    simpa [q] using burkholder_du_dy_Xn_Yn_Lq h n
  have hYdiff_memLp : MemLp
      (fun ω => Y_{n+1}[w, f] ω - Y_{n}[w, f] ω) p μ := by
    have hYdiff_eq :
        (fun ω => Y_{n+1}[w, f] ω - Y_{n}[w, f] ω) =
          fun ω => minusOne w (n + 1) ω * martingaleDiff f (n + 1) ω := by
      funext ω
      simpa [martingaleDiff] using congrFun (martingaleTransform_succ_sub (minusOne w) f n) ω
    rw [hYdiff_eq]
    exact burkholder_minusOne_mul_martingaleDiff_memLp h (n + 1)
  have hp_eq_ofReal : p = ENNReal.ofReal p.toReal := by
    exact (ENNReal.ofReal_toReal h.hp_top).symm
  have hmul_int : Integrable
      (fun ω =>
        Burkholder.du_dy p.toReal h.hp_one
          (X_{n}[w, f] ω) (Y_{n}[w, f] ω) *
            (Y_{n+1}[w, f] ω - Y_{n}[w, f] ω)) μ := by
    rw [hp_eq_ofReal] at hYdiff_memLp
    letI : ENNReal.HolderTriple (ENNReal.ofReal q) (ENNReal.ofReal p.toReal) 1 := hpq
    exact MemLp.integrable_mul hdu hYdiff_memLp
  constructor
  · exact hmul_int
  · have hw_adapted : StronglyAdapted ℱ w :=
      IsStronglyPredictable.stronglyAdapted h.hstrong
    have hdiff_measurable_le :
        ∀ {i n : ℕ}, i ≤ n → StronglyMeasurable[ℱ n] (martingaleDiff f i) := by
      intro i n hin
      cases i with
      | zero =>
          simpa [martingaleDiff] using
            h.hmart.stronglyAdapted.stronglyMeasurable_le (Nat.zero_le n)
      | succ i =>
          have hi_succ : i + 1 ≤ n := hin
          have hi : i ≤ n := Nat.le_trans (Nat.le_succ i) hi_succ
          simpa [martingaleDiff] using
            (h.hmart.stronglyAdapted.stronglyMeasurable_le hi_succ).sub
              (h.hmart.stronglyAdapted.stronglyMeasurable_le hi)
    have hplus_meas_le :
        ∀ {i n : ℕ}, i ≤ n → StronglyMeasurable[ℱ n] (plusOne w i) := by
      intro i n hin
      have hw_meas : StronglyMeasurable[ℱ n] (w i) :=
        hw_adapted.stronglyMeasurable_le hin
      exact
        hw_meas.add (measurable_const.stronglyMeasurable)
    have hminus_meas_le :
        ∀ {i n : ℕ}, i ≤ n → StronglyMeasurable[ℱ n] (minusOne w i) := by
      intro i n hin
      have hw_meas : StronglyMeasurable[ℱ n] (w i) :=
        hw_adapted.stronglyMeasurable_le hin
      exact
        hw_meas.sub (measurable_const.stronglyMeasurable)
    have hX_meas : StronglyMeasurable[ℱ n] (X_{n}[w, f]) := by
      rw [martingaleTransform]
      exact Finset.stronglyMeasurable_sum (Finset.range (n + 1)) fun i hi => by
        have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact (hplus_meas_le hin).mul (hdiff_measurable_le hin)
    have hY_meas : StronglyMeasurable[ℱ n] (Y_{n}[w, f]) := by
      rw [martingaleTransform]
      exact Finset.stronglyMeasurable_sum (Finset.range (n + 1)) fun i hi => by
        have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact (hminus_meas_le hin).mul (hdiff_measurable_le hin)
    have hdu_cont_global :
        Continuous
          (fun z : ℝ × ℝ =>
            Burkholder.du_dy p.toReal h.hp_one z.1 z.2) := by
      rw [← continuousOn_univ]
      exact Burkholder.du_dy_continuousOn p.toReal h.hp_one
    have hA_meas :
        StronglyMeasurable[ℱ n]
          (fun ω =>
            Burkholder.du_dy p.toReal h.hp_one
              (X_{n}[w, f] ω) (Y_{n}[w, f] ω)) := by
      simpa using hdu_cont_global.comp_stronglyMeasurable
        (hX_meas.prodMk hY_meas)
    have hp_one_en : (1 : ℝ≥0∞) ≤ p := by
      rw [hp_eq_ofReal]
      simpa using ENNReal.ofReal_le_ofReal h.hp_one.le
    have hYdiff_int :
        Integrable (fun ω => Y_{n+1}[w, f] ω - Y_{n}[w, f] ω) μ :=
      hYdiff_memLp.integrable hp_one_en
    have hfdiff_int : Integrable (fun ω => f (n + 1) ω - f n ω) μ :=
      (h.hmart.integrable (n + 1)).sub (h.hmart.integrable n)
    have hfdiff_zero :
        μ[f (n + 1) - f n | ℱ n] =ᵐ[μ] 0 := by
      have hnext : μ[f (n + 1) | ℱ n] =ᵐ[μ] f n :=
        h.hmart.condExp_ae_eq (Nat.le_succ n)
      have hcurr : μ[f n | ℱ n] =ᵐ[μ] f n := by
        rw [condExp_of_stronglyMeasurable (ℱ.le n)
          (h.hmart.stronglyMeasurable n) (h.hmart.integrable n)]
      calc
        μ[f (n + 1) - f n | ℱ n]
            =ᵐ[μ] μ[f (n + 1) | ℱ n] - μ[f n | ℱ n] :=
              condExp_sub (h.hmart.integrable (n + 1)) (h.hmart.integrable n) (ℱ n)
        _ =ᵐ[μ] f n - f n := hnext.sub hcurr
        _ =ᵐ[μ] 0 := by simp
    have hminus_succ_meas : StronglyMeasurable[ℱ n] (minusOne w (n + 1)) := by
      exact
        (IsStronglyPredictable.measurable_add_one h.hstrong n).sub
          (measurable_const.stronglyMeasurable)
    have hYdiff_eq :
        (fun ω => Y_{n+1}[w, f] ω - Y_{n}[w, f] ω) =
          fun ω => minusOne w (n + 1) ω * (f (n + 1) ω - f n ω) := by
      funext ω
      simpa [minusOne, martingaleDiff] using
        congrFun (martingaleTransform_succ_sub (minusOne w) f n) ω
    have hminus_fdiff_int :
        Integrable
          (fun ω => minusOne w (n + 1) ω * (f (n + 1) ω - f n ω)) μ := by
      simpa [minusOne, martingaleDiff] using
        (burkholder_minusOne_mul_martingaleDiff_memLp h (n + 1)).integrable hp_one_en
    have hYdiff_zero :
        μ[(fun ω => Y_{n+1}[w, f] ω - Y_{n}[w, f] ω) | ℱ n] =ᵐ[μ] 0 := by
      have hpull :
          μ[(fun ω => minusOne w (n + 1) ω * (f (n + 1) ω - f n ω)) | ℱ n]
            =ᵐ[μ]
          (fun ω => minusOne w (n + 1) ω *
            μ[f (n + 1) - f n | ℱ n] ω) :=
        condExp_mul_of_stronglyMeasurable_left
          hminus_succ_meas hminus_fdiff_int hfdiff_int
      calc
        μ[(fun ω => Y_{n+1}[w, f] ω - Y_{n}[w, f] ω) | ℱ n]
            =ᵐ[μ]
          μ[(fun ω => minusOne w (n + 1) ω * (f (n + 1) ω - f n ω)) | ℱ n] := by
            rw [hYdiff_eq]
        _ =ᵐ[μ]
          (fun ω => minusOne w (n + 1) ω *
            μ[f (n + 1) - f n | ℱ n] ω) := hpull
        _ =ᵐ[μ] 0 := by
          filter_upwards [hfdiff_zero] with ω hω
          simp [hω]
    have hpull :
        μ[(fun ω =>
          Burkholder.du_dy p.toReal h.hp_one
            (X_{n}[w, f] ω) (Y_{n}[w, f] ω) *
              (Y_{n+1}[w, f] ω - Y_{n}[w, f] ω)) | ℱ n]
          =ᵐ[μ]
        (fun ω =>
          Burkholder.du_dy p.toReal h.hp_one
            (X_{n}[w, f] ω) (Y_{n}[w, f] ω) *
              μ[(fun ω => Y_{n+1}[w, f] ω - Y_{n}[w, f] ω) | ℱ n] ω) :=
      condExp_mul_of_stronglyMeasurable_left hA_meas hmul_int hYdiff_int
    calc
      (∫ ω, Burkholder.du_dy p.toReal h.hp_one
        (X_{n}[w, f] ω) (Y_{n}[w, f] ω) *
            (Y_{n+1}[w, f] ω - Y_{n}[w, f] ω) ∂μ)
          = ∫ ω, μ[(fun ω =>
              Burkholder.du_dy p.toReal h.hp_one
                (X_{n}[w, f] ω) (Y_{n}[w, f] ω) *
                  (Y_{n+1}[w, f] ω - Y_{n}[w, f] ω)) | ℱ n] ω ∂μ := by
            exact (integral_condExp (ℱ.le n)).symm
      _ = ∫ ω,
          Burkholder.du_dy p.toReal h.hp_one
            (X_{n}[w, f] ω) (Y_{n}[w, f] ω) *
              μ[(fun ω => Y_{n+1}[w, f] ω - Y_{n}[w, f] ω) | ℱ n] ω ∂μ := by
            exact integral_congr_ae hpull
      _ = 0 := by
        refine integral_eq_zero_of_ae ?_
        filter_upwards [hYdiff_zero] with ω hω
        simp [hω]

/-- The chosen majorant dominates the Burkholder function `v`. -/
private lemma burkholder_v_le_u (p : ℝ) (hp : p > 1) (x y : ℝ) :
    Burkholder.v p x y ≤ Burkholder.u p hp x y :=
  (Burkholder.u_isMajorant p hp).2.1 x y

/-- The chosen majorant is nonpositive on the region `x * y ≤ 0`. -/
private lemma burkholder_u_nonpos_of_mul_nonpos (p : ℝ) (hp : p > 1)
    {x y : ℝ} (hxy : x * y ≤ 0) :
    Burkholder.u p hp x y ≤ 0 :=
  (Burkholder.u_isMajorant p hp).2.2.1 x y hxy

/--
The tangency/concavity property of the chosen majorant. This is the formal
version of the step
`u(x + h, y + k) ≤ u(x, y) + u_x(x,y) h + u_y(x,y) k`
when `h * k <= 0`.
-/
private lemma burkholder_u_tangent_step (p : ℝ) (hp : p > 1) (x y h k : ℝ)
    (hhk : h * k ≤ 0) :
    ∃ d_u_dx d_u_dy : ℝ,
      Burkholder.u p hp (x + h) (y + k) ≤
        Burkholder.u p hp x y + d_u_dx * h + d_u_dy * k := by
  rcases (Burkholder.u_isMajorant p hp).1 x y with ⟨d_u_dx, d_u_dy, htangent⟩
  exact ⟨d_u_dx, d_u_dy, htangent h k hhk⟩

/--
Pointwise choice of the `x`-coefficient in the Burkholder tangent inequality.

Given the transformed pair `(X_n, Y_n)`, this simply evaluates the selected
partial derivative `du_dx` at that point.
-/
private noncomputable def burkholder_tangentDx (p : ℝ) (hp : p > 1)
    {w f : ℕ → Ω → ℝ} (n : ℕ)
    (_hcross : ∀ ω,
      (X_{n + 1}[w,f] ω - X_{n}[w,f] ω) *
        (Y_{n + 1}[w,f] ω - Y_{n}[w,f] ω) ≤ 0) :
    Ω → ℝ :=
  fun ω =>
    Burkholder.du_dx p hp (X_{n}[w,f] ω) (Y_{n}[w,f] ω)

/--
Pointwise choice of the `y`-coefficient in the Burkholder tangent inequality.

This is the companion to `burkholder_tangentDx`, using `du_dy` evaluated at the
current transformed state `(X_n, Y_n)`.
-/
private noncomputable def burkholder_tangentDy (p : ℝ) (hp : p > 1)
    {w f : ℕ → Ω → ℝ} (n : ℕ)
    (_hcross : ∀ ω,
      (X_{n + 1}[w,f] ω - X_{n}[w,f] ω) *
        (Y_{n + 1}[w,f] ω - Y_{n}[w,f] ω) ≤ 0) :
    Ω → ℝ :=
  fun ω =>
    Burkholder.du_dy p hp (X_{n}[w,f] ω) (Y_{n}[w,f] ω)

private lemma burkholder_u_n_nplus1 (p : ℝ) (hp : p > 1)
    {w f : ℕ → Ω → ℝ} (n : ℕ)
    (hcross : ∀ ω,
      (X_{n + 1}[w,f] ω - X_{n}[w,f] ω) *
        (Y_{n + 1}[w,f] ω - Y_{n}[w,f] ω) ≤ 0) :
    ∀ ω,
      Burkholder.u p hp (X_{n + 1}[w,f] ω) (Y_{n + 1}[w,f] ω) ≤
        Burkholder.u p hp (X_{n}[w,f] ω) (Y_{n}[w,f] ω) +
          Burkholder.du_dx p hp (X_{n}[w,f] ω) (Y_{n}[w,f] ω) *
            (X_{n + 1}[w,f] ω - X_{n}[w,f] ω) +
          Burkholder.du_dy p hp (X_{n}[w,f] ω) (Y_{n}[w,f] ω) *
            (Y_{n + 1}[w,f] ω - Y_{n}[w,f] ω) := by
  intro ω
  rcases
    Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec
          (Classical.choose_spec
            (Majorants.exists_majorant_p_g_1 p hp)))) with
    ⟨hC_nonneg,
      hu_cont, hdu_dx_cont, hdu_dy_cont,
      hu_growth, hdu_dx_growth, hdu_dy_growth,
      htangent, hmajor, hnonpos, haxis⟩
  simpa [Burkholder.u, Burkholder.du_dx, Burkholder.du_dy, sub_add_cancel] using
    htangent
      (X_{n}[w, f] ω) (Y_{n}[w, f] ω)
      (X_{n+1}[w, f] ω - X_{n}[w, f] ω)
      (Y_{n+1}[w, f] ω - Y_{n}[w, f] ω) (hcross ω)

private lemma burkholder_u_XY_integral_succ_le
    {p : ℝ≥0∞} {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ mΩ} {w f : ℕ → Ω → ℝ}
    (h : BurkholderAssumptions p Ω μ ℱ w f) (n : ℕ) :
    (∫ ω,
      Burkholder.u p.toReal h.hp_one
        (X_{n+1}[w, f] ω) (Y_{n+1}[w, f] ω) ∂μ) ≤
      ∫ ω,
        Burkholder.u p.toReal h.hp_one
          (X_{n}[w, f] ω) (Y_{n}[w, f] ω) ∂μ := by
  let linear : Ω → ℝ := fun ω =>
    Burkholder.du_dx p.toReal h.hp_one (X_{n}[w, f] ω) (Y_{n}[w, f] ω) *
      (X_{n+1}[w, f] ω - X_{n}[w, f] ω) +
    Burkholder.du_dy p.toReal h.hp_one (X_{n}[w, f] ω) (Y_{n}[w, f] ω) *
      (Y_{n+1}[w, f] ω - Y_{n}[w, f] ω)
  have hu_succ_int :
      Integrable
        (fun ω =>
          Burkholder.u p.toReal h.hp_one
            (X_{n+1}[w, f] ω) (Y_{n+1}[w, f] ω)) μ :=
    burkholder_u_Xn_Yn_integrable h (n + 1)
  have hu_int :
      Integrable
        (fun ω =>
          Burkholder.u p.toReal h.hp_one
            (X_{n}[w, f] ω) (Y_{n}[w, f] ω)) μ :=
    burkholder_u_Xn_Yn_integrable h n
  have hdx := burkholder_du_dx_Xn_Yn_integrable_mul_diff h n
  have hdy := burkholder_du_dy_Xn_Yn_integrable_mul_diff h n
  have hlinear_int : Integrable linear μ := by
    dsimp [linear]
    exact hdx.1.add hdy.1
  have hlinear_zero : ∫ ω, linear ω ∂μ = 0 := by
    dsimp [linear]
    rw [integral_add hdx.1 hdy.1, hdx.2, hdy.2, add_zero]
  have hbound : ∀ᵐ ω ∂μ,
      Burkholder.u p.toReal h.hp_one
        (X_{n+1}[w, f] ω) (Y_{n+1}[w, f] ω) ≤
        Burkholder.u p.toReal h.hp_one
          (X_{n}[w, f] ω) (Y_{n}[w, f] ω) + linear ω := by
    filter_upwards [(inequality_for_transform_differences h).1 n] with ω hcrossω
    rcases
      Classical.choose_spec
        (Classical.choose_spec
          (Classical.choose_spec
            (Classical.choose_spec
              (Majorants.exists_majorant_p_g_1 p.toReal h.hp_one)))) with
      ⟨hC_nonneg,
        hu_cont, hdu_dx_cont, hdu_dy_cont,
        hu_growth, hdu_dx_growth, hdu_dy_growth,
        htangent, hmajor, hnonpos, haxis⟩
    have hpoint :
        Burkholder.u p.toReal h.hp_one
          (X_{n+1}[w, f] ω) (Y_{n+1}[w, f] ω) ≤
        Burkholder.u p.toReal h.hp_one
          (X_{n}[w, f] ω) (Y_{n}[w, f] ω) +
          Burkholder.du_dx p.toReal h.hp_one
            (X_{n}[w, f] ω) (Y_{n}[w, f] ω) *
              (X_{n+1}[w, f] ω - X_{n}[w, f] ω) +
          Burkholder.du_dy p.toReal h.hp_one
            (X_{n}[w, f] ω) (Y_{n}[w, f] ω) *
              (Y_{n+1}[w, f] ω - Y_{n}[w, f] ω) := by
      simpa [Burkholder.u, Burkholder.du_dx, Burkholder.du_dy, sub_add_cancel] using
        htangent
          (X_{n}[w, f] ω) (Y_{n}[w, f] ω)
          (X_{n+1}[w, f] ω - X_{n}[w, f] ω)
          (Y_{n+1}[w, f] ω - Y_{n}[w, f] ω) hcrossω
    dsimp [linear]
    linarith
  have hright_int : Integrable
      (fun ω =>
        Burkholder.u p.toReal h.hp_one
          (X_{n}[w, f] ω) (Y_{n}[w, f] ω) + linear ω) μ :=
    hu_int.add hlinear_int
  calc
    (∫ ω,
      Burkholder.u p.toReal h.hp_one
        (X_{n+1}[w, f] ω) (Y_{n+1}[w, f] ω) ∂μ)
        ≤ ∫ ω,
          Burkholder.u p.toReal h.hp_one
            (X_{n}[w, f] ω) (Y_{n}[w, f] ω) + linear ω ∂μ :=
          integral_mono_ae hu_succ_int hright_int hbound
    _ = (∫ ω,
          Burkholder.u p.toReal h.hp_one
            (X_{n}[w, f] ω) (Y_{n}[w, f] ω) ∂μ) +
          ∫ ω, linear ω ∂μ := by
            rw [integral_add hu_int hlinear_int]
    _ ≤ ∫ ω,
        Burkholder.u p.toReal h.hp_one
          (X_{n}[w, f] ω) (Y_{n}[w, f] ω) ∂μ := by
      rw [hlinear_zero, add_zero]

/-- Applying `v ≤ u` pointwise to the transform variables `X_n,Y_n`. -/
private lemma burkholder_v_XY_le_u_XY_pointwise (p : ℝ) (hp : p > 1)
    {w f : ℕ → Ω → ℝ} (n : ℕ) (ω : Ω) :
    Burkholder.v p (X_{n}[w, f] ω) (Y_{n}[w, f] ω) ≤
      Burkholder.u p hp (X_{n}[w, f] ω) (Y_{n}[w, f] ω) :=
  burkholder_v_le_u p hp _ _

/-- Applying `v ≤ u` after taking averages. -/
private lemma burkholder_v_XY_le_u_XY (p : ℝ) (hp : p > 1)
    {μ : Measure Ω} {w f : ℕ → Ω → ℝ} (n : ℕ)
    (hv_int : Integrable
      (fun ω => Burkholder.v p (X_{n}[w,f] ω) (Y_{n}[w,f] ω)) μ)
    (hu_int : Integrable
      (fun ω => Burkholder.u p hp (X_{n}[w,f] ω) (Y_{n}[w,f] ω)) μ) :
    (∫ ω, Burkholder.v p (X_{n}[w, f] ω) (Y_{n}[w, f] ω) ∂μ) ≤
      ∫ ω, Burkholder.u p hp (X_{n}[w, f] ω) (Y_{n}[w, f] ω) ∂μ := by
  exact integral_mono_ae hv_int hu_int
    (ae_of_all _ fun ω => burkholder_v_XY_le_u_XY_pointwise p hp n ω)





/-- The initial inequality `u(X_0,Y_0) ≤ 0` from `X_0 Y_0 ≤ 0` a.s. -/
private lemma burkholder_u_X0Y0_nonpos_ae (p : ℝ) (hp : p > 1)
    {μ : Measure Ω} {w f : ℕ → Ω → ℝ}
    (hXY0 : ∀ᵐ ω ∂μ, X_{0}[w,f] ω * Y_{0}[w,f] ω ≤ 0) :
    ∀ᵐ ω ∂μ,
      Burkholder.u p hp (X_{0}[w, f] ω) (Y_{0}[w, f] ω) ≤ 0 := by
  filter_upwards [hXY0] with ω hxy
  exact burkholder_u_nonpos_of_mul_nonpos p hp hxy

/-- Under the Burkholder package of hypotheses, the Burkholder function has
nonpositive expectation along the transformed pair `(X_n,Y_n)`. -/
private lemma burkholder_integral_v_XY_nonpos
    {p : ℝ≥0∞} {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ mΩ} {w f : ℕ → Ω → ℝ}
    (h : BurkholderAssumptions p Ω μ ℱ w f)
    (n : ℕ) :
    (∫ ω, Burkholder.v p.toReal (X_{n}[w, f] ω) (Y_{n}[w, f] ω) ∂μ) ≤ 0 := by
  have hdiffs := inequality_for_transform_differences h
  have hu_nonpos : ∀ n,
      (∫ ω, Burkholder.u p.toReal h.hp_one
        (X_{n}[w, f] ω) (Y_{n}[w, f] ω) ∂μ) ≤ 0 := by
    intro n
    induction n with
    | zero =>
        exact integral_nonpos_of_ae
          (burkholder_u_X0Y0_nonpos_ae p.toReal h.hp_one hdiffs.2)
    | succ n ih =>
        exact (burkholder_u_XY_integral_succ_le h n).trans ih
  exact (burkholder_v_XY_le_u_XY p.toReal h.hp_one n
    (burkholder_v_XY_integrable h n)
    (burkholder_u_Xn_Yn_integrable h n)).trans (hu_nonpos n)







/--
Burkholder's `L^p` inequality for discrete martingale transforms.

If `f` is a martingale and `w` is a strongly predictable
multiplier uniformly bounded by `1`, then transforming `f` by `w` does not blow
up its `L^p` size by more than the Burkholder factor `pStar(p)-1`.

The statement is pointwise in time `n` and is written using `eLpNorm`:
`‖(w ⋆ₘ f)_n‖_p ≤ (pStar(p)-1) * ‖f_n‖_p`.
-/
theorem Lp_Burkholder_inequality_martingaleTransform (p : ℝ≥0∞) (Ω : Type*)
  [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
  [IsFiniteMeasure μ] (ℱ : Filtration ℕ mΩ) (w f : ℕ → Ω → ℝ)
  (hp_one : 1 < p)
  (hfin : p ≠ ∞)
  (hstrong : IsStronglyPredictable ℱ w)
  (hmart : Martingale f ℱ μ)
  (hLp : ∀ n, MemLp (f n) p μ)
  (hbound : ∀ n, ∀ᵐ ω ∂μ, |w n ω| ≤ 1) :
        ∀ n, eLpNorm ((w ⋆ₘ f) n) p μ ≤
          ENNReal.ofReal (Burkholder.pStar p.toReal - 1) * eLpNorm (f n) p μ := by
  have hp_toReal : 1 < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hfin).2 hp_one
  have hp_ne_zero : p ≠ 0 := by
    exact (zero_lt_one.trans hp_one).ne'
  let h : BurkholderAssumptions p Ω μ ℱ w f :=
    { hp_one := hp_toReal
      hp_top := hfin
      hstrong := hstrong
      hmart := hmart
      hLp := hLp
      hbound := hbound }
  intro n
  let A : Ω → ℝ := fun ω => (X_{n}[w, f] ω + Y_{n}[w, f] ω) / 2
  let B : Ω → ℝ := fun ω => (X_{n}[w, f] ω - Y_{n}[w, f] ω) / 2
  let c : ℝ := Burkholder.pStar p.toReal - 1
  have hA_eq : A = (w ⋆ₘ f) n := by
    funext ω
    dsimp [A]
    simp only [martingaleTransform, Finset.sum_apply]
    rw [← Finset.sum_add_distrib]
    calc
      ((Finset.range (n + 1)).sum fun i =>
          plusOne w i ω * martingaleDiff f i ω +
            minusOne w i ω * martingaleDiff f i ω) / 2
          = ((Finset.range (n + 1)).sum fun i =>
              2 * (w i ω * martingaleDiff f i ω)) / 2 := by
              congr 1
              apply Finset.sum_congr rfl
              intro i hi
              simp [plusOne, minusOne]
              ring
      _ = (Finset.range (n + 1)).sum (fun i => w i ω * martingaleDiff f i ω) := by
          rw [← Finset.mul_sum]
          ring
  have hB_eq : B = f n := by
    funext ω
    dsimp [B]
    simp only [martingaleTransform, Finset.sum_apply]
    rw [← Finset.sum_sub_distrib]
    clear A B hA_eq
    have hsum_diff :
        (Finset.range (n + 1)).sum (fun i => martingaleDiff f i ω) = f n ω := by
      induction n with
      | zero =>
          simp [martingaleDiff]
      | succ n ih =>
          rw [Finset.sum_range_succ, ih]
          simp [martingaleDiff]
    calc
      ((Finset.range (n + 1)).sum fun i =>
          plusOne w i ω * martingaleDiff f i ω -
            minusOne w i ω * martingaleDiff f i ω) / 2
          = ((Finset.range (n + 1)).sum fun i =>
              2 * martingaleDiff f i ω) / 2 := by
              congr 1
              apply Finset.sum_congr rfl
              intro i hi
              simp [plusOne, minusOne]
              ring
      _ = (Finset.range (n + 1)).sum (fun i => martingaleDiff f i ω) := by
          rw [← Finset.mul_sum]
          ring
      _ = f n ω := hsum_diff
  have hA_mem : MemLp A p μ := by
    change MemLp
      (fun ω => (X_{n}[w, f] ω + Y_{n}[w, f] ω) / 2) p μ
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      ((burkholder_X_memLp h n).add (burkholder_Y_memLp h n)).const_mul (1 / 2 : ℝ)
  have hB_mem : MemLp B p μ := by
    rw [hB_eq]
    exact hLp n
  have hc_nonneg : 0 ≤ c := by
    dsimp [c, Burkholder.pStar, Majorants.pStar]
    have hp_le_max : p.toReal ≤ max p.toReal (Majorants.q p.toReal) := le_max_left _ _
    linarith
  have hv_nonpos := burkholder_integral_v_XY_nonpos h n
  have hA_int :
      Integrable (fun ω => Real.rpow |A ω| p.toReal) μ := by
    simpa [Real.norm_eq_abs] using hA_mem.integrable_norm_rpow'
  have hB_int :
      Integrable (fun ω => Real.rpow |B ω| p.toReal) μ := by
    simpa [Real.norm_eq_abs] using hB_mem.integrable_norm_rpow'
  have hpow_int_le :
      (∫ ω, Real.rpow |A ω| p.toReal ∂μ) ≤
        Real.rpow c p.toReal *
          ∫ ω, Real.rpow |B ω| p.toReal ∂μ := by
    have hc_abs : |Majorants.pStar p.toReal - 1| = c := by
      simpa [c, Burkholder.pStar] using abs_of_nonneg hc_nonneg
    have hv_nonpos' :
        (∫ ω,
          Real.rpow |A ω| p.toReal -
            Real.rpow c p.toReal * Real.rpow |B ω| p.toReal ∂μ) ≤ 0 := by
      simpa [A, B, c, Burkholder.v, Majorants.v, Burkholder.pStar,
        hc_abs] using hv_nonpos
    rw [integral_sub hA_int (hB_int.const_mul (Real.rpow c p.toReal)),
      integral_const_mul] at hv_nonpos'
    linarith
  have hA_int_nonneg : 0 ≤ ∫ ω, Real.rpow |A ω| p.toReal ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have hB_int_nonneg : 0 ≤ ∫ ω, Real.rpow |B ω| p.toReal ∂μ :=
    integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have hlp_real :
      lpNorm A p μ ≤ c * lpNorm B p μ := by
    rw [lpNorm_eq_integral_norm_rpow_toReal hp_ne_zero hfin hA_mem.aestronglyMeasurable,
      lpNorm_eq_integral_norm_rpow_toReal hp_ne_zero hfin hB_mem.aestronglyMeasurable]
    have hroot := Real.rpow_le_rpow hA_int_nonneg hpow_int_le
      (inv_nonneg.mpr (le_trans zero_le_one hp_toReal.le))
    calc
      (∫ x, ‖A x‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹
          = (∫ x, Real.rpow |A x| p.toReal ∂μ) ^ p.toReal⁻¹ := by
              simp [Real.norm_eq_abs]
      _ ≤ (Real.rpow c p.toReal *
            ∫ x, Real.rpow |B x| p.toReal ∂μ) ^ p.toReal⁻¹ := hroot
      _ = c * (∫ x, Real.rpow |B x| p.toReal ∂μ) ^ p.toReal⁻¹ := by
          change
            Real.rpow
              (Real.rpow c p.toReal *
                (∫ x, Real.rpow |B x| p.toReal ∂μ)) p.toReal⁻¹ =
              c * Real.rpow (∫ x, Real.rpow |B x| p.toReal ∂μ) p.toReal⁻¹
          have hc_root : Real.rpow (Real.rpow c p.toReal) p.toReal⁻¹ = c := by
            have hmul_root :
                Real.rpow c (p.toReal * p.toReal⁻¹) =
                  Real.rpow (Real.rpow c p.toReal) p.toReal⁻¹ :=
              Real.rpow_mul hc_nonneg p.toReal p.toReal⁻¹
            rw [← hmul_root, mul_inv_cancel₀ (ne_of_gt (zero_lt_one.trans hp_toReal))]
            change c ^ (1 : ℝ) = c
            exact Real.rpow_one c
          have hmul :
              Real.rpow
                (Real.rpow c p.toReal *
                  (∫ x, Real.rpow |B x| p.toReal ∂μ)) p.toReal⁻¹ =
                Real.rpow (Real.rpow c p.toReal) p.toReal⁻¹ *
                  Real.rpow (∫ x, Real.rpow |B x| p.toReal ∂μ) p.toReal⁻¹ :=
            Real.mul_rpow
              (x := Real.rpow c p.toReal)
              (y := ∫ x, Real.rpow |B x| p.toReal ∂μ)
              (z := p.toReal⁻¹)
              (Real.rpow_nonneg hc_nonneg p.toReal) hB_int_nonneg
          rw [hmul, hc_root]
      _ = c * (∫ x, ‖B x‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹ := by
          simp [Real.norm_eq_abs]
  rw [← hA_eq, ← hB_eq]
  rw [← MeasureTheory.ofReal_lpNorm hA_mem, ← MeasureTheory.ofReal_lpNorm hB_mem]
  exact (ENNReal.ofReal_le_ofReal hlp_real).trans_eq (by
    rw [ENNReal.ofReal_mul hc_nonneg])

end MeasureTheory
