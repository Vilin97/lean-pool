/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothCutoffs
import LeanPool.NavierStokesAndEuler.NavierStokes.MomentRepair
import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Average

/-!
# Constructed smooth moment repairs

The correction profiles are explicit affine rescalings of the constructed
smooth cutoff. Their supports lie strictly inside the supplied positive
intervals. The generalized-power determinant theorem then gives exact
finite-moment repair by an actual compactly supported smooth function.
-/

section

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

end
end

end

@[expose] public section

noncomputable section

open scoped BigOperators ContDiff
open Set Function MeasureTheory

namespace NavierStokes.LocalizedMomentRepair

/-- Inner lower, given by `(3 * l + u) / 4`. -/
def innerLower (l u : ℝ) : ℝ := (3 * l + u) / 4
/-- Inner upper, given by `(l + 3 * u) / 4`. -/
def innerUpper (l u : ℝ) : ℝ := (l + 3 * u) / 4

/-- A concrete smooth bump in the middle half of `(l,u)`. -/
def bump (l u : ℝ) (t : ℝ) : ℝ :=
  SmoothCutoffs.cutoff ((t - (l + u) / 2) / ((u - l) / 4))

theorem bump_contDiff (l u : ℝ) : ContDiff ℝ ∞ (bump l u) :=
  SmoothCutoffs.cutoff_contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem bump_nonneg (l u t : ℝ) : 0 ≤ bump l u t :=
  (SmoothCutoffs.cutoff_mem_Icc _).1

theorem bump_le_one (l u t : ℝ) : bump l u t ≤ 1 :=
  (SmoothCutoffs.cutoff_mem_Icc _).2

theorem bump_at_center (l u : ℝ) : bump l u ((l + u) / 2) = 1 := by
  apply SmoothCutoffs.cutoff_one_of_abs_le
  simp

theorem bump_support_subset (l u : ℝ) (hlu : l < u) :
    support (bump l u) ⊆ Icc (innerLower l u) (innerUpper l u) := by
  intro t ht
  have hs : (t - (l + u) / 2) / ((u - l) / 4) ∈ Ioo (-1 : ℝ) 1 := by
    rw [← SmoothCutoffs.cutoff_support]
    exact ht
  have hr : 0 < (u - l) / 4 := by linarith
  have hlo := (lt_div_iff₀ hr).mp hs.1
  have hup := (div_lt_iff₀ hr).mp hs.2
  constructor <;> dsimp [innerLower, innerUpper] <;> linarith

theorem bump_tsupport_subset (l u : ℝ) (hlu : l < u) :
    tsupport (bump l u) ⊆ Icc (innerLower l u) (innerUpper l u) :=
  closure_minimal (bump_support_subset l u hlu) isClosed_Icc

theorem bump_hasCompactSupport (l u : ℝ) (hlu : l < u) :
    HasCompactSupport (bump l u) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (bump_support_subset l u hlu)

theorem innerInterval_subset_open (l u : ℝ) (hlu : l < u) :
    Icc (innerLower l u) (innerUpper l u) ⊆ Ioo l u := by
  intro t ht
  dsimp [innerLower, innerUpper] at ht
  constructor <;> linarith [ht.1, ht.2]

theorem bump_tsupport_subset_open (l u : ℝ) (hlu : l < u) :
    tsupport (bump l u) ⊆ Ioo l u :=
  (bump_tsupport_subset l u hlu).trans (innerInterval_subset_open l u hlu)

section Family

variable {n : ℕ}

/-- A fixed compact set, independent of the moment debt. -/
def repairRegion (l u : Fin n → ℝ) : Set ℝ :=
  ⋃ j, Icc (innerLower (l j) (u j)) (innerUpper (l j) (u j))

theorem repairRegion_isCompact (l u : Fin n → ℝ) : IsCompact (repairRegion l u) :=
  isCompact_iUnion fun _ => isCompact_Icc

theorem repairRegion_subset_open (l u : Fin n → ℝ) (hlu : ∀ j, l j < u j) :
    repairRegion l u ⊆ ⋃ j, Ioo (l j) (u j) := by
  intro t ht
  obtain ⟨j, hj⟩ := mem_iUnion.mp ht
  exact mem_iUnion.mpr ⟨j, innerInterval_subset_open _ _ (hlu j) hj⟩

/-- The actual generalized-power moment matrix of the constructed profiles. -/
def matrix (a l u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  PowerMomentMatrix.bumpMomentMatrix a (fun j => bump (l j) (u j))

theorem matrix_det_ne_zero (a l u : Fin n → ℝ) (ha : Injective a)
    (hl : ∀ j, 0 < l j) (hlu : ∀ j, l j < u j)
    (hsep : ∀ i j, i < j → u i ≤ l j) : (matrix a l u).det ≠ 0 := by
  apply PowerMomentMatrix.bumpMomentMatrix_det_ne_zero a
    (fun j => innerLower (l j) (u j)) (fun j => innerUpper (l j) (u j))
    (fun j => bump (l j) (u j)) ha
  · intro j
    dsimp [innerLower]
    linarith [hl j, hlu j]
  · intro i j hij
    dsimp [innerLower, innerUpper]
    linarith [hlu i, hlu j, hsep i j hij]
  · intro j
    exact (bump_contDiff _ _).continuous
  · exact fun j t => bump_nonneg _ _ t
  · intro j
    exact ⟨(l j + u j) / 2, by rw [bump_at_center]; norm_num⟩
  · exact fun j => bump_support_subset _ _ (hlu j)

/-- Coefficients are computed from the proved nonsingular moment matrix. -/
def coefficients (a l u d : Fin n → ℝ) : Fin n → ℝ := (matrix a l u)⁻¹.mulVec d

/-- The constructed smooth correction for the prescribed finite vector of debts. -/
def repair (a l u d : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ j, coefficients a l u d j * bump (l j) (u j) t

theorem repair_contDiff (a l u d : Fin n → ℝ) : ContDiff ℝ ∞ (repair a l u d) := by
  apply ContDiff.sum
  intro j _
  exact contDiff_const.mul (bump_contDiff _ _)

theorem repair_support_subset (a l u d : Fin n → ℝ) (hlu : ∀ j, l j < u j) :
    support (repair a l u d) ⊆ repairRegion l u := by
  intro t ht
  by_contra hnot
  apply ht
  apply Finset.sum_eq_zero
  intro j _
  have hb : bump (l j) (u j) t = 0 := by
    by_contra hb
    exact hnot (mem_iUnion.mpr ⟨j, bump_support_subset _ _ (hlu j) hb⟩)
  rw [hb, mul_zero]

theorem repair_tsupport_subset (a l u d : Fin n → ℝ) (hlu : ∀ j, l j < u j) :
    tsupport (repair a l u d) ⊆ repairRegion l u :=
  closure_minimal (repair_support_subset a l u d hlu) (repairRegion_isCompact l u).isClosed

theorem repair_hasCompactSupport (a l u d : Fin n → ℝ) (hlu : ∀ j, l j < u j) :
    HasCompactSupport (repair a l u d) :=
  HasCompactSupport.of_support_subset_isCompact (repairRegion_isCompact l u)
    (repair_support_subset a l u d hlu)

theorem repair_tsupport_subset_open (a l u d : Fin n → ℝ) (hlu : ∀ j, l j < u j) :
    tsupport (repair a l u d) ⊆ ⋃ j, Ioo (l j) (u j) :=
  (repair_tsupport_subset a l u d hlu).trans (repairRegion_subset_open l u hlu)

theorem integrable_power_mul_bump (p l u : ℝ) (hl : 0 < l) (hlu : l < u) :
    Integrable (fun t => t ^ p * bump l u t) := by
  have hs : support (fun t => t ^ p * bump l u t) ⊆
      Icc (innerLower l u) (innerUpper l u) := by
    intro t ht
    apply bump_support_subset l u hlu
    intro hb
    exact ht (by simp [hb])
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply ContinuousOn.integrableOn_Icc
  apply ContinuousOn.mul _ (bump_contDiff l u).continuous.continuousOn
  apply continuousOn_id.rpow_const
  intro t ht
  apply Or.inl
  have hlo : 0 < innerLower l u := by dsimp [innerLower]; linarith
  exact ne_of_gt (lt_of_lt_of_le hlo ht.1)

/-- The prescribed moments hold as exact ordinary Lebesgue integral identities. -/
theorem repair_exact (a l u d : Fin n → ℝ) (ha : Injective a)
    (hl : ∀ j, 0 < l j) (hlu : ∀ j, l j < u j)
    (hsep : ∀ i j, i < j → u i ≤ l j) (i : Fin n) :
    (∫ t, t ^ a i * repair a l u d t) = d i := by
  have hfun : (fun t => t ^ a i * repair a l u d t) =
      (fun t => ∑ j, coefficients a l u d j * (t ^ a i * bump (l j) (u j) t)) := by
    ext t
    simp only [repair, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfun, integral_finsetSum]
  · simp only [integral_const_mul]
    have h := MomentRepair.matrix_mul_coefficients (matrix a l u)
      (matrix_det_ne_zero a l u ha hl hlu hsep) d
    have hi := congrFun h i
    simpa only [matrix, PowerMomentMatrix.bumpMomentMatrix, MomentRepair.coefficients,
      coefficients, Matrix.mulVec, dotProduct, mul_comm] using hi
  · intro j _
    exact (integrable_power_mul_bump (a i) (l j) (u j) (hl j) (hlu j)).const_mul _

/-- Existence from exponents and intervals alone, with an actual function witness. -/
theorem exists_smooth_compact_repair (a l u d : Fin n → ℝ) (ha : Injective a)
    (hl : ∀ j, 0 < l j) (hlu : ∀ j, l j < u j)
    (hsep : ∀ i j, i < j → u i ≤ l j) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ ⋃ j, Ioo (l j) (u j) ∧ ∀ i, (∫ t, t ^ a i * f t) = d i :=
  ⟨repair a l u d, repair_contDiff a l u d, repair_hasCompactSupport a l u d hlu,
    repair_tsupport_subset_open a l u d hlu, repair_exact a l u d ha hl hlu hsep⟩

theorem repair_add (a l u d e : Fin n → ℝ) :
    repair a l u (d + e) = repair a l u d + repair a l u e := by
  ext t
  simp only [repair, coefficients, Matrix.mulVec_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem repair_smul (a l u d : Fin n → ℝ) (r : ℝ) :
    repair a l u (r • d) = r • repair a l u d := by
  ext t
  simp only [repair, coefficients, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc]

theorem repair_sub (a l u d e : Fin n → ℝ) :
    repair a l u (d - e) = repair a l u d - repair a l u e := by
  ext t
  simp only [repair, coefficients, Matrix.mulVec_sub, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- The fixed-interval, fixed-exponent repair depends linearly on the moment debt. -/
def repairLinearMap (a l u : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] (ℝ → ℝ) where
  toFun := repair a l u
  map_add' := repair_add a l u
  map_smul' r d := repair_smul a l u d r

theorem continuous_repair_eval (a l u : Fin n → ℝ) (t : ℝ) :
    Continuous (fun d => repair a l u d t) := by
  unfold repair coefficients Matrix.mulVec dotProduct
  apply continuous_finsetSum
  intro j _
  apply Continuous.mul _ continuous_const
  apply continuous_finsetSum
  intro k _
  exact continuous_const.mul (continuous_apply k)

/-- Continuity in the pointwise function topology; the later jet bounds are stronger. -/
theorem continuous_repair (a l u : Fin n → ℝ) : Continuous (repair a l u) :=
  continuous_pi (continuous_repair_eval a l u)

/-- Decomposition into the finite family of repairs of coordinate debts. -/
theorem repair_eq_sum_coordinate (a l u d : Fin n → ℝ) :
    repair a l u d = fun t => ∑ j, d j * repair a l u (Pi.single j 1) t := by
  have hdecomp : (∑ j, d j • (Pi.single j (1 : ℝ) : Fin n → ℝ)) = d := by
    ext k
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  have h := congrArg (repairLinearMap a l u) hdecomp
  rw [map_sum] at h
  simp only [map_smul] at h
  symm
  convert! h using 1
  ext t
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, repairLinearMap, LinearMap.coe_mk,
    AddHom.coe_mk]

end Family

section Jets

/-- Iterated differentiation commutes with finite sums of smooth real functions. -/
theorem iteratedDeriv_finite_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun x => ∑ i ∈ s, f i x) t = ∑ i ∈ s, iteratedDeriv k (f i) t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      cases k with
      | zero => rfl
      | succ k => rw [SmoothCutoffs.iteratedDeriv_const_succ]
  | @insert i s his ih =>
      simp only [Finset.sum_insert his]
      have hi : ContDiffAt ℝ k (f i) t :=
        ((hf i).of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt
      have hs : ContDiffAt ℝ k (fun x => ∑ j ∈ s, f j x) t :=
        ((ContDiff.sum (fun j _ => hf j)).of_le
          (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt
      change iteratedDeriv k (f i + (fun x => ∑ j ∈ s, f j x)) t = _
      rw [iteratedDeriv_add hi hs, ih]

/-- Every derivative of a smooth compactly supported function has a global finite bound. -/
theorem smooth_compact_derivative_bound (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |iteratedDeriv k f t| ≤ C := by
  have hcompact : ∀ j, HasCompactSupport (iteratedDeriv j f) := by
    intro j
    induction j with
    | zero => simpa using hc
    | succ j ih =>
        rw [iteratedDeriv_succ]
        exact ih.deriv
  obtain ⟨C, hC⟩ := (hcompact k).exists_bound_of_continuous
    (hf.continuous_iteratedDeriv k (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)))
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  have ht : |iteratedDeriv k f t| ≤ C := by simpa only [Real.norm_eq_abs] using hC t
  exact ht.trans (le_max_left _ _)

variable {n : ℕ}

/-- Every derivative of the repair is the same linear combination of fixed coordinate repairs. -/
theorem repair_iteratedDeriv_coordinate (a l u d : Fin n → ℝ) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (repair a l u d) t =
      ∑ j, d j * iteratedDeriv k (repair a l u (Pi.single j 1)) t := by
  rw [repair_eq_sum_coordinate a l u d]
  rw [iteratedDeriv_finite_sum Finset.univ
    (fun j x => d j * repair a l u (Pi.single j 1) x)
    (fun j => contDiff_const.mul (repair_contDiff a l u (Pi.single j 1))) k t]
  apply Finset.sum_congr rfl
  intro j _
  exact iteratedDeriv_const_mul (d j)
    ((repair_contDiff a l u (Pi.single j 1)).of_le
      (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt

/-- A uniform-in-space linear estimate for each derivative, with all geometric data fixed. -/
theorem repair_derivative_bound (a l u : Fin n → ℝ) (hlu : ∀ j, l j < u j) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : Fin n → ℝ) (t : ℝ),
      |iteratedDeriv k (repair a l u d) t| ≤ C * ‖d‖ := by
  have hb : ∀ j : Fin n, ∃ C : ℝ, 0 ≤ C ∧ ∀ t,
      |iteratedDeriv k (repair a l u (Pi.single j 1)) t| ≤ C := fun j =>
    smooth_compact_derivative_bound _ (repair_contDiff a l u (Pi.single j 1))
      (repair_hasCompactSupport a l u (Pi.single j 1) hlu) k
  choose C hC hbound using hb
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => hC j), fun d t => ?_⟩
  rw [repair_iteratedDeriv_coordinate]
  calc
    |∑ j, d j * iteratedDeriv k (repair a l u (Pi.single j 1)) t| ≤
        ∑ j, |d j * iteratedDeriv k (repair a l u (Pi.single j 1)) t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ‖d‖ * C j := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      apply mul_le_mul _ (hbound j t) (abs_nonneg _) (norm_nonneg _)
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm d j
    _ = (∑ j, C j) * ‖d‖ := by rw [← Finset.mul_sum, mul_comm]

/-- All derivatives through any prescribed finite order depend Lipschitz-continuously
on the moment debt, uniformly over the spatial coordinate. -/
theorem repair_finite_jet_bound (a l u : Fin n → ℝ) (hlu : ∀ j, l j < u j) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ N, ∀ (d e : Fin n → ℝ) (t : ℝ),
      |iteratedDeriv k (repair a l u d) t - iteratedDeriv k (repair a l u e) t| ≤
        C * ‖d - e‖ := by
  choose C hC hbound using repair_derivative_bound a l u hlu
  refine ⟨∑ k ∈ Finset.range (N + 1), C k, Finset.sum_nonneg (fun k _ => hC k), ?_⟩
  intro k hk d e t
  have hsub : iteratedDeriv k (repair a l u (d - e)) t =
      iteratedDeriv k (repair a l u d) t - iteratedDeriv k (repair a l u e) t := by
    rw [repair_sub]
    exact iteratedDeriv_sub
      ((repair_contDiff a l u d).of_le
        (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt
      ((repair_contDiff a l u e).of_le
        (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt
  rw [← hsub]
  apply (hbound k (d - e) t).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact Finset.single_le_sum (fun j _ => hC j)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

end Jets

end NavierStokes.LocalizedMomentRepair
