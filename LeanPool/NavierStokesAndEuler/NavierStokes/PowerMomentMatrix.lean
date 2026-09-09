/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Average

/-!
# Generalized-power evaluation matrices

Rolle induction proves uniqueness of an exponential sum at as many ordered
nodes as there are distinct real exponents. Taking logarithms gives the
generalized-power evaluation-matrix part of manuscript Lemma 3.6.
-/

@[expose] public section


noncomputable section

open scoped BigOperators
open MeasureTheory

namespace NavierStokes.PowerMomentMatrix

/-- A finite exponential sum with arbitrary real exponents. -/
def expSum {n : ℕ} (a c : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ j, c j * Real.exp (a j * t)

theorem expSum_hasDerivAt {n : ℕ} (a c : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (expSum a c) (expSum a (fun j => c j * a j) t) t := by
  apply HasDerivAt.fun_sum
  intro j _
  convert! (((hasDerivAt_id t).const_mul (a j)).exp).const_mul (c j) using 1
  simp only [id_eq]
  ring

/-- Shifting all exponents multiplies the exponential sum by a nonzero factor. -/
theorem expSum_shift {n : ℕ} (a c : Fin n → ℝ) (s t : ℝ) :
    expSum (fun j => a j - s) c t = expSum a c t * Real.exp (-s * t) := by
  unfold expSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (a j - s) * t = a j * t + (-s * t) by ring, Real.exp_add]
  ring

/-- Consecutive equal values yield strictly ordered derivative zeros. -/
theorem exists_ordered_derivative_zeros {n : ℕ} (f f' : ℝ → ℝ)
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (x : Fin (n + 1) → ℝ) (hx : StrictMono x) (hz : ∀ j, f (x j) = 0) :
    ∃ y : Fin n → ℝ, StrictMono y ∧
      (∀ j, x j.castSucc < y j ∧ y j < x j.succ) ∧ (∀ j, f' (y j) = 0) := by
  have hex : ∀ j : Fin n, ∃ t, t ∈ Set.Ioo (x j.castSucc) (x j.succ) ∧ f' t = 0 := by
    intro j
    apply exists_hasDerivAt_eq_zero (f := f) (f' := f') (hx j.castSucc_lt_succ)
    · exact (continuous_iff_continuousAt.mpr fun t => (hf t).continuousAt).continuousOn
    · rw [hz, hz]
    · intro t _
      exact hf t
  choose y hy hzero using hex
  refine ⟨y, ?_, hy, hzero⟩
  intro i j hij
  exact lt_trans (lt_of_lt_of_le (hy i).2 (hx.monotone (Fin.succ_le_castSucc_iff.mpr hij)))
    (hy j).1

/--
An exponential sum with `n` distinct real exponents which vanishes at `n`
strictly ordered nodes has all coefficients zero. This is the full finite
Rolle induction, with no nonsingularity premise.
-/
theorem expSum_coefficients_zero :
    ∀ (n : ℕ) (a c x : Fin n → ℝ), Function.Injective a → StrictMono x →
      (∀ j, expSum a c (x j) = 0) → c = 0 := by
  intro n
  induction n with
  | zero =>
      intro a c x ha hx hz
      ext j
      exact Fin.elim0 j
  | succ n ih =>
      intro a c x ha hx hz
      let a' : Fin n → ℝ := fun j => a j.succ - a 0
      let d : Fin n → ℝ := fun j => c j.succ * (a j.succ - a 0)
      let g : ℝ → ℝ := expSum (fun j => a j - a 0) c
      have hgzero : ∀ j, g (x j) = 0 := by
        intro j
        dsimp [g]
        rw [expSum_shift, hz, zero_mul]
      have hgderiv : ∀ t, HasDerivAt g (expSum a' d t) t := by
        intro t
        convert! expSum_hasDerivAt (fun j => a j - a 0) c t using 1
        simp [expSum, Fin.sum_univ_succ, a', d]
      obtain ⟨y, hy, _, hyzero⟩ := exists_ordered_derivative_zeros g (expSum a' d)
        hgderiv x hx hgzero
      have ha' : Function.Injective a' := by
        intro i j hij
        have hij' : a i.succ = a j.succ := by
          dsimp [a'] at hij
          linarith
        exact Fin.succ_inj.mp (ha hij')
      have hd : d = 0 := ih a' d y ha' hy hyzero
      have htail : ∀ j : Fin n, c j.succ = 0 := by
        intro j
        have hj := congrFun hd j
        change c j.succ * (a j.succ - a 0) = 0 at hj
        apply (mul_eq_zero.mp hj).resolve_right
        intro heq
        have hindex := ha (sub_eq_zero.mp heq)
        exact Fin.succ_ne_zero j hindex
      have hhead : c 0 = 0 := by
        have h := hz 0
        simpa [expSum, Fin.sum_univ_succ, htail, Real.exp_ne_zero] using h
      ext j
      exact Fin.cases hhead htail j

/-- The evaluation matrix, with exponents indexing rows and nodes indexing columns. -/
def expEvaluationMatrix {n : ℕ} (a x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Real.exp (a i * x j)

theorem expEvaluationMatrix_det_ne_zero {n : ℕ} (a x : Fin n → ℝ)
    (ha : Function.Injective a) (hx : StrictMono x) :
    (expEvaluationMatrix a x).det ≠ 0 := by
  apply IsUnit.ne_zero
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.vecMul_injective_iff_isUnit.mp
  intro c d hcd
  dsimp only at hcd
  have hzero : (expEvaluationMatrix a x).vecMul (c - d) = 0 := by
    rw [Matrix.sub_vecMul, hcd, sub_self]
  have hz : ∀ j, expSum a (c - d) (x j) = 0 := by
    intro j
    exact congrFun hzero j
  exact sub_eq_zero.mp (expSum_coefficients_zero n a (c - d) x ha hx hz)

/-- Real powers; the row exponents are not restricted to natural numbers. -/
def powerEvaluationMatrix {n : ℕ} (a x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (x j) ^ (a i)

/-- The generalized-power evaluation determinant is nonzero at positive ordered nodes. -/
theorem powerEvaluationMatrix_det_ne_zero {n : ℕ} (a x : Fin n → ℝ)
    (ha : Function.Injective a) (hx : StrictMono x) (hpos : ∀ j, 0 < x j) :
    (powerEvaluationMatrix a x).det ≠ 0 := by
  have hlog : StrictMono (fun j => Real.log (x j)) := by
    intro i j hij
    exact Real.log_lt_log (hpos i) (hx hij)
  have hmat : powerEvaluationMatrix a x = expEvaluationMatrix a (fun j => Real.log (x j)) := by
    ext i j
    simp only [powerEvaluationMatrix, expEvaluationMatrix, Real.rpow_def_of_pos (hpos j)]
    rw [mul_comm]
  rw [hmat]
  exact expEvaluationMatrix_det_ne_zero a _ ha hlog

/-- A continuous function with zero integral against a positive finite measure
of nonzero mass on an interval has a zero in that interval. -/
theorem exists_zero_of_setIntegral_eq_zero
    (μ : Measure ℝ) [IsFiniteMeasure μ] (l u : ℝ) (f : ℝ → ℝ)
    (hmass : μ (Set.Icc l u) ≠ 0) (hf : ContinuousOn f (Set.Icc l u))
    (hzero : ∫ t in Set.Icc l u, f t ∂μ = 0) :
    ∃ t ∈ Set.Icc l u, f t = 0 := by
  have hμ : μ.restrict (Set.Icc l u) ≠ 0 := by
    intro h
    exact hmass (Measure.restrict_eq_zero.mp h)
  have hint : Integrable f (μ.restrict (Set.Icc l u)) := hf.integrableOn_Icc
  have hnull : (μ.restrict (Set.Icc l u)) (Set.Icc l u)ᶜ = 0 := by simp
  have havg : ⨍ t in Set.Icc l u, f t ∂μ = 0 := by
    rw [average_eq, hzero, smul_zero]
  obtain ⟨x, hx, hfx⟩ := exists_notMem_null_le_average hμ hint hnull
  obtain ⟨y, hy, hfy⟩ := exists_notMem_null_average_le hμ hint hnull
  have hx' : x ∈ Set.Icc l u := by simpa using hx
  have hy' : y ∈ Set.Icc l u := by simpa using hy
  rw [havg] at hfx hfy
  exact isPreconnected_Icc.intermediate_value hx' hy' hf ⟨hfx, hfy⟩

/-- A finite linear combination of arbitrary real powers. -/
def powerSum {n : ℕ} (a c : Fin n → ℝ) (t : ℝ) : ℝ := ∑ i, c i * t ^ a i

theorem continuousOn_powerSum {n : ℕ} (a c : Fin n → ℝ) (l u : ℝ) (hl : 0 < l) :
    ContinuousOn (powerSum a c) (Set.Icc l u) := by
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_const.mul
  apply continuousOn_id.rpow_const
  intro t ht
  exact Or.inl (ne_of_gt (lt_of_lt_of_le hl ht.1))

/-- Columns integrate the real powers over separated intervals against finite
positive measures. Positivity is intrinsic in the type `Measure`. -/
def intervalMomentMatrix {n : ℕ} (a l u : Fin n → ℝ) (μ : Fin n → Measure ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ t in Set.Icc (l j) (u j), t ^ a i ∂μ j

theorem integral_powerSum {n : ℕ} (a c : Fin n → ℝ) (l u : ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hl : 0 < l) :
    (∫ t in Set.Icc l u, powerSum a c t ∂μ) =
      ∑ i, c i * ∫ t in Set.Icc l u, t ^ a i ∂μ := by
  unfold powerSum
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro i _
    apply ContinuousOn.integrableOn_Icc
    apply continuousOn_const.mul
    apply continuousOn_id.rpow_const
    intro t ht
    exact Or.inl (ne_of_gt (lt_of_lt_of_le hl ht.1))

/--
The integrated generalized-power matrix is nonsingular for any finite positive
measures with nonzero mass on strictly separated compact positive intervals.
This proves the moment-matrix mechanism without assuming determinant sign or
invertibility. A zero linear combination of columns supplies one function zero
in each interval; the Rolle theorem above then forces all coefficients to vanish.
-/
theorem intervalMomentMatrix_det_ne_zero {n : ℕ} (a l u : Fin n → ℝ)
    (μ : Fin n → Measure ℝ) [∀ j, IsFiniteMeasure (μ j)]
    (ha : Function.Injective a) (hl : ∀ j, 0 < l j)
    (hsep : ∀ i j, i < j → u i < l j)
    (hmass : ∀ j, μ j (Set.Icc (l j) (u j)) ≠ 0) :
    (intervalMomentMatrix a l u μ).det ≠ 0 := by
  apply IsUnit.ne_zero
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.vecMul_injective_iff_isUnit.mp
  intro c d hcd
  dsimp only at hcd
  have hzero : (intervalMomentMatrix a l u μ).vecMul (c - d) = 0 := by
    rw [Matrix.sub_vecMul, hcd, sub_self]
  have hroots : ∀ j, ∃ t ∈ Set.Icc (l j) (u j), powerSum a (c - d) t = 0 := by
    intro j
    apply exists_zero_of_setIntegral_eq_zero (μ j) (l j) (u j) _ (hmass j)
      (continuousOn_powerSum a (c - d) (l j) (u j) (hl j))
    rw [integral_powerSum a (c - d) (l j) (u j) (μ j) (hl j)]
    exact congrFun hzero j
  choose x hx hroot using hroots
  have hxmono : StrictMono x := by
    intro i j hij
    exact lt_of_le_of_lt (hx i).2 (lt_of_lt_of_le (hsep i j hij) (hx j).1)
  have hxpos : ∀ j, 0 < x j := fun j => lt_of_lt_of_le (hl j) (hx j).1
  have hcoeff : c - d = 0 := by
    have hunit : IsUnit (powerEvaluationMatrix a x) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr
        (powerEvaluationMatrix_det_ne_zero a x ha hxmono hxpos))
    apply Matrix.vecMul_injective_iff_isUnit.mpr hunit
    dsimp only
    rw [Matrix.zero_vecMul]
    ext j
    exact hroot j
  exact sub_eq_zero.mp hcoeff

/-- The manuscript's matrix of ordinary Lebesgue integrals against bump profiles. -/
def bumpMomentMatrix {n : ℕ} (a : Fin n → ℝ) (β : Fin n → ℝ → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => ∫ t, t ^ a i * β j t

/--
The ordered bump moment matrix is nonsingular. The bump hypotheses are stated
using explicit separated compact intervals; continuity suffices, so smoothness
is unnecessary. All finite sizes and arbitrary distinct real exponents are
covered. No moment-determinant or inverse estimate is assumed.
-/
theorem bumpMomentMatrix_det_ne_zero {n : ℕ} (a l u : Fin n → ℝ)
    (β : Fin n → ℝ → ℝ) (ha : Function.Injective a)
    (hl : ∀ j, 0 < l j) (hsep : ∀ i j, i < j → u i < l j)
    (hcont : ∀ j, Continuous (β j)) (hnonneg : ∀ j t, 0 ≤ β j t)
    (hnonzero : ∀ j, ∃ t, β j t ≠ 0)
    (hsupp : ∀ j, Function.support (β j) ⊆ Set.Icc (l j) (u j)) :
    (bumpMomentMatrix a β).det ≠ 0 := by
  have hcompact : ∀ j, HasCompactSupport (β j) := fun j =>
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (hsupp j)
  have hintegrable : ∀ j, Integrable (β j) := fun j =>
    (hcont j).integrable_of_hasCompactSupport (hcompact j)
  have hout : ∀ j t, t ∉ Set.Icc (l j) (u j) → β j t = 0 := by
    intro j t ht
    by_contra h
    exact ht (hsupp j h)
  let μ : Fin n → Measure ℝ := fun j => volume.withDensity (fun t => ENNReal.ofReal (β j t))
  let : ∀ j, IsFiniteMeasure (μ j) := fun j =>
    isFiniteMeasure_withDensity_ofReal (hintegrable j).2
  have hdensity : ∀ j (f : ℝ → ℝ),
      (∫ t in Set.Icc (l j) (u j), f t ∂μ j) =
        ∫ t in Set.Icc (l j) (u j), β j t * f t := by
    intro j f
    dsimp [μ]
    rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
      (hcont j).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun t => ENNReal.ofReal_lt_top) f measurableSet_Icc]
    simp only [ENNReal.toReal_ofReal (hnonneg j _), smul_eq_mul]
  have hmass : ∀ j, μ j (Set.Icc (l j) (u j)) ≠ 0 := by
    intro j hzero
    have hr : (μ j).restrict (Set.Icc (l j) (u j)) = 0 :=
      Measure.restrict_eq_zero.mpr hzero
    have heq := hdensity j (fun _ => (1 : ℝ))
    rw [hr, integral_zero_measure] at heq
    simp only [mul_one] at heq
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hout j)] at heq
    obtain ⟨t, ht⟩ := hnonzero j
    have hpos : 0 < ∫ t, β j t := (hcont j).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hcompact j) (hnonneg j) ht
    linarith
  have hmatrix : bumpMomentMatrix a β = intervalMomentMatrix a l u μ := by
    ext i j
    change (∫ t, t ^ a i * β j t) = ∫ t in Set.Icc (l j) (u j), t ^ a i ∂μ j
    rw [hdensity]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => by rw [hout j t ht, zero_mul])]
    congr 1
    ext t
    exact mul_comm _ _
  rw [hmatrix]
  exact intervalMomentMatrix_det_ne_zero a l u μ ha hl hsep hmass

end NavierStokes.PowerMomentMatrix
