/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.UniformSpace.Matrix
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Data.Matrix.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Lp.PiLp

import Mathlib.NumberTheory.FrobeniusNumber
import LeanPool.RlTheoryInLean.Data.Matrix.Mul

open Finset NNReal WithLp Matrix PiLp Nat ContractingWith Metric Bornology Filter Function
open scoped BigOperators
open scoped Topology

namespace StochasticMatrix

universe u
variable {S : Type u} [Fintype S]
/-- The finite-dimensional `L¹` space of real-valued functions on `S`. -/
abbrev l1Space (S : Type u) := WithLp 1 (S → ℝ)

local notation "‖"x"‖₁" => (nnnorm (E := l1Space S) x)
local notation "d₁("x","y")" => edist (α := l1Space S) x y

/-- A nonnegative vector whose entries sum to one. -/
class StochasticVec (x : S → ℝ) where
  nonneg : ∀ s, 0 ≤ x s
  rowsum : ∑ s, x s = 1

lemma StochasticVec.le_one (x : S → ℝ) [StochasticVec x] (s : S) :
  x s ≤ 1 := by
  rw [← (inferInstance : StochasticVec x).rowsum]
  apply single_le_sum (fun z _ => (inferInstance : StochasticVec x).nonneg z)
  simp

section simplex

/-- The probability simplex, represented inside finite-dimensional `L¹`. -/
abbrev Simplex (S : Type u) [Fintype S] := {x : l1Space S | StochasticVec x.ofLp}

instance (x : ↑(Simplex S)) : @StochasticVec S _ x.val.ofLp := x.property

instance : IsClosed (Simplex S) := by
  let l1Space := l1Space S
  have hcont : ∀ s : S, Continuous (fun f : l1Space => f.ofLp s) :=
    fun s => (continuous_apply s).comp (PiLp.continuous_ofLp 1 _)
  have h1 : IsClosed {f : l1Space | ∀ s, 0 ≤ f.ofLp s} := by
    simpa [Set.setOf_forall] using isClosed_iInter fun s =>
      (isClosed_le continuous_const continuous_id).preimage (hcont s)
  have h2 : IsClosed {f : l1Space | (∑ s, f.ofLp s) = 1} := by
    have : IsClosed ({1} : Set ℝ) := isClosed_singleton
    simpa using this.preimage (continuous_finset_sum _ fun s _ => hcont s)
  have h := IsClosed.inter h1 h2
  rw [← Set.setOf_and] at h
  have : {x : l1Space | StochasticVec x.ofLp} =
    {x | (∀ s, 0 ≤ x.ofLp s) ∧ (∑ s, x.ofLp s = 1)} := by
    ext1; simp only [Set.mem_setOf_eq]
    exact ⟨fun h => ⟨h.nonneg, h.rowsum⟩, fun h => ⟨h.1, h.2⟩⟩
  unfold Simplex
  rw [this]
  exact h

instance : CompleteSpace (Simplex S) := IsClosed.completeSpace_coe

lemma l1_norm_eq_sum (f : l1Space S) : ‖f‖ = ∑ s, |f.ofLp s| := by
  simpa using (PiLp.norm_eq_sum (f := f))

lemma l1_norm_eq_one (x : l1Space S) [StochasticVec x.ofLp]
  : ‖x‖₊ = 1 := by
  apply NNReal.eq
  simp only [coe_nnnorm, NNReal.coe_one, l1_norm_eq_sum]
  have hx := (inferInstance : StochasticVec x.ofLp)
  rw [← hx.rowsum]
  exact sum_congr rfl fun s _ => abs_of_nonneg (hx.nonneg s)

lemma simplex_subset_closedBall :
  (Simplex S) ⊆ closedBall (0 : l1Space S) 1 := by
  intro x hx
  simp only [mem_closedBall, dist_zero_right, l1_norm_eq_sum, ← hx.rowsum]
  exact sum_le_sum fun i _ => (abs_of_nonneg (hx.nonneg i)).le

lemma simples_is_compact : IsCompact (Simplex S) :=
  isCompact_of_isClosed_isBounded inferInstance
    ((isBounded_iff_subset_closedBall (s := Simplex S) (0 : l1Space S)).mpr
      ⟨1, simplex_subset_closedBall⟩)

end simplex

/-- A matrix whose rows are stochastic vectors. -/
class RowStochastic (P : Matrix S S ℝ) where
  stochastic : ∀ s, StochasticVec (P s)

lemma sum_svec_mul_smat_eq_one
  (μ : S → ℝ) [StochasticVec μ] (P : Matrix S S ℝ) [RowStochastic P]
  : ∑ i, ∑ j, μ i * P i j = 1 := by
  have hP := (inferInstance : RowStochastic P).stochastic
  simp_rw [← mul_sum, (fun i => (hP i).rowsum), mul_one]
  exact (inferInstance : StochasticVec μ).rowsum

instance svec_mul_smat_is_svec
  (μ : S → ℝ) [StochasticVec μ] (P : Matrix S S ℝ) [RowStochastic P] :
  StochasticVec (μ ᵥ* P) := by
  have hμ := (inferInstance : StochasticVec μ)
  have hP := (inferInstance : RowStochastic P).stochastic
  refine ⟨fun j => ?_, ?_⟩
  · simpa [Matrix.vecMul] using sum_nonneg fun i _ => mul_nonneg (hμ.nonneg i) ((hP i).nonneg j)
  · simp only [Matrix.vecMul, dotProduct]
    rw [sum_comm]
    exact sum_svec_mul_smat_eq_one μ P

instance smat_mul_smat_is_smat
  (P Q : Matrix S S ℝ) [RowStochastic P] [RowStochastic Q] :
  RowStochastic (P * Q) := by
  have hP := (inferInstance : RowStochastic P).stochastic
  have hQ := (inferInstance : RowStochastic Q).stochastic
  refine ⟨fun i => ⟨fun j => ?_, ?_⟩⟩
  · simpa [Matrix.mul_apply] using
      sum_nonneg fun k _ => mul_nonneg ((hP i).nonneg k) ((hQ k).nonneg j)
  · have : ∑ j, (P * Q) i j = 1 := by
      calc ∑ j, (P * Q) i j
          = ∑ j, ∑ k, P i k * Q k j := by simp [Matrix.mul_apply]
        _ = ∑ k, ∑ j, P i k * Q k j := Finset.sum_comm
        _ = ∑ k, P i k * ∑ j, Q k j := by simp [Finset.mul_sum]
        _ = ∑ k, P i k * 1 := by
            apply sum_congr rfl; intro j _; simp [(hQ j).rowsum]
        _ = 1 := by simp [(hP i).rowsum]
    exact this

instance smat_pow_is_smat [DecidableEq S]
  (P : Matrix S S ℝ) [RowStochastic P] (n : ℕ) :
  RowStochastic (P ^ n) := by
  induction n with
  | zero =>
    refine ⟨fun i => ⟨fun j => ?_, ?_⟩⟩
    · by_cases h : i = j
      · simp [h]
      · exact (Matrix.one_apply_ne (α := ℝ) h).ge
    · simp [Matrix.one_apply]
  | succ n ih =>
    simp_rw [pow_add, pow_one]
    exact smat_mul_smat_is_smat (P ^ n) P

lemma chapman_kolmogorov_eq_ge [DecidableEq S]
  (P : Matrix S S ℝ) [RowStochastic P] (m n : ℕ) (i j : S) :
  ∀ k, (P ^ (m + n)) i j ≥ (P ^ m) i k * (P ^ n) k j := by
  intro k
  rw [pow_add]
  simp only [ge_iff_le, Matrix.mul_apply, ← sum_erase_add (a := k) (h := mem_univ k)]
  apply sub_nonneg.mp
  rw [add_sub_cancel_right]
  exact sum_nonneg fun l _ => mul_nonneg
    (RowStochastic.stochastic (P := P ^ m) i |>.nonneg l)
    (RowStochastic.stochastic (P := P ^ n) l |>.nonneg j)

section minorization

variable [DecidableEq S]

/-- Irreducibility of a finite stochastic matrix. -/
class Irreducible (P : Matrix S S ℝ) [RowStochastic P] where
  irreducible : ∀ i j, ∃ n : ℕ, 0 < (P ^ n) i j

/-- The set of positive return times for state i -/
noncomputable def return_times (P : Matrix S S ℝ) (i : S)
  : Set ℕ := {n : ℕ | 1 ≤ n ∧ 0 < (P ^ n) i i}

/-- Return times are closed under addition (used via AddSubmonoid.closure) -/
lemma return_times_add_mem (P : Matrix S S ℝ) [RowStochastic P] (i : S)
    {a b : ℕ} (ha : a ∈ return_times P i) (hb : b ∈ return_times P i) :
    a + b ∈ return_times P i := by
  simp only [return_times, Set.mem_setOf_eq] at ha hb ⊢
  exact ⟨by linarith [ha.1, hb.1],
    (mul_pos ha.2 hb.2).trans_le (chapman_kolmogorov_eq_ge P a b i i i).le⟩

/-- A stochastic matrix is aperiodic if for each state, the GCD of return times is 1 -/
class Aperiodic (P : Matrix S S ℝ) [RowStochastic P] where
  aperiodic : ∀ i, Nat.setGcd (return_times P i) = 1

theorem eventually_positive [Nonempty S] (P : Matrix S S ℝ) [RowStochastic P]
  [Irreducible P] [Aperiodic P] :
  ∃ N, ∀ n i j, N ≤ n → 0 < (P ^ n) i j := by
  have h_ni : ∀ i, ∃ n₀, ∀ n, n₀ ≤ n → n ∈ return_times P i ∨ n = 0 := fun i => by
    have hcl : ∀ x, x ∈ AddSubmonoid.closure (return_times P i) → x ∈ return_times P i ∨ x = 0 := by
      intro x hx; induction hx using AddSubmonoid.closure_induction with
      | mem _ hy => exact Or.inl hy
      | zero => exact Or.inr rfl
      | add _ _ _ _ iha ihb =>
        rcases iha with ha | ha0 <;> rcases ihb with hb | hb0
        · exact Or.inl (return_times_add_mem P i ha hb)
        all_goals simp_all
    obtain ⟨n₀, hn₀⟩ := Nat.exists_mem_closure_of_ge (return_times P i)
    refine ⟨n₀, fun n hn => ?_⟩
    rcases eq_or_ne n 0 with rfl | hn0; · exact Or.inr rfl
    rcases hcl n (hn₀ n hn (by simp [Aperiodic.aperiodic (P := P) i])) with h | h
    · exact Or.inl h
    · exact (hn0 h).elim
  let ni := fun i => (h_ni i).choose
  let n₀ := sup' _ univ_nonempty ni + 1
  have hn₀ : ∀ n i, n₀ ≤ n → 0 < (P ^ n) i i := fun n i hn => by
    have hni : ni i ≤ n := by have := le_sup' ni (mem_univ i); omega
    rcases (h_ni i).choose_spec n hni with h | h
    · exact h.2
    · omega
  let nij := fun ij : S × S => (Irreducible.irreducible (P := P) ij.1 ij.2).choose
  let n₁ := sup' _ (by simp : (univ (α := S × S)).Nonempty) nij
  refine ⟨n₀ + n₁, fun n i j hn => ?_⟩
  have hnij_le : nij (i, j) ≤ n₁ := le_sup' nij (mem_univ (i, j))
  have hle : nij (i, j) ≤ n := by omega
  calc 0 < (P ^ nij (i,j)) i j * (P ^ (n - nij (i,j))) j j :=
        mul_pos (Irreducible.irreducible (P := P) i j).choose_spec (hn₀ _ j (by omega))
    _ ≤ (P ^ n) i j := by
      have := chapman_kolmogorov_eq_ge P (nij (i,j)) (n - nij (i,j)) i j j
      simp only [Nat.add_sub_cancel' hle] at this; exact this

/-- A Doeblin minorization for a finite stochastic matrix. -/
class DoeblinMinorization (P : Matrix S S ℝ) [RowStochastic P] where
  minorize : ∃ (ε : ℝ) (ν : S → ℝ),
    0 < ε ∧ ε < 1 ∧ StochasticVec ν ∧ ∀ i j, P i j ≥ ε * ν j

theorem smat_minorizable_with_large_pow
  [Nonempty S] (P : Matrix S S ℝ)
  [RowStochastic P] [Irreducible P] [Aperiodic P] :
  ∃ N, 1 ≤ N ∧ DoeblinMinorization (P ^ N) := by
  obtain ⟨n₀, hn₀⟩ := eventually_positive P
  let n₁ := n₀ + 1
  have hn₀ := hn₀ n₁
  let hnij := fun ij : S × S => hn₀ ij.1 ij.2 (by unfold n₁; simp)
  have : (Finset.univ (α := S × S)).Nonempty := by simp
  let δij := fun ij : S × S => (P ^ n₁) ij.1 ij.2
  let δ := inf' (Finset.univ (α := S × S)) this δij
  have hδinf : ∀ ij, δ ≤ δij ij :=
    fun ij => inf'_le (f := δij) (by simp)
  have hδrange : 0 < δ ∧ δ ≤ 1:= by
    obtain ⟨ij, _hij, hijinf⟩ := exists_mem_eq_inf' this δij
    have hδdef : δ = δij ij := by unfold δ; simp [hijinf]
    constructor
    · linarith [hnij ij]
    · obtain ⟨nonneg, rowsum⟩ := RowStochastic.stochastic (P := P ^ n₁) (ij.1)
      rw [hδdef, ← rowsum, ← sum_erase_add (a := ij.2) (h := by simp)]
      unfold δij
      apply sub_nonneg.mp
      rw [add_sub_cancel_right]
      exact sum_nonneg fun j _ => nonneg j
  let δ' := δ * 1 / 2 * 1 / Fintype.card S
  refine ⟨n₁, by unfold n₁; simp, ?_⟩
  refine ⟨⟨δ' * Fintype.card S, fun j => 1 / Fintype.card S,
    by unfold δ'; simp; linarith,
    by unfold δ'; simp; linarith,
    ⟨fun s => by simp, by simp [Finset.sum_const, Finset.card_univ]⟩,
    fun i j => ?_⟩⟩
  have hcard : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hδ'le : δ' ≤ δ := by
    have hδ0 : 0 ≤ δ := hδrange.1.le
    have hcard1 : (1 : ℝ) ≤ Fintype.card S := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
    have h1 : δ * 1 / 2 * 1 / Fintype.card S ≤ δ * 1 / 2 * 1 :=
      div_le_self (by positivity) hcard1
    have h2 : δ * 1 / 2 * 1 ≤ δ := by nlinarith
    exact h1.trans h2
  rw [ge_iff_le]; field_simp
  linarith [hδinf (i, j)]

end minorization

section contraction

private def broadcast (ν : S → ℝ) : Matrix S S ℝ :=
  Matrix.of (fun _ s' => ν s')

private lemma vecMul_broadcast (v : S → ℝ) (ν : S → ℝ) [StochasticVec ν] :
    v ᵥ* broadcast ν = fun j => (∑ i, v i) * ν j := by
  classical
  funext j
  simp [broadcast, Matrix.vecMul, Finset.sum_mul, dotProduct]

theorem smat_nonexpansive_in_l1 (Q : Matrix S S ℝ) [RowStochastic Q] :
    ∀ (x y : S → ℝ),
      ‖WithLp.toLp 1 (x ᵥ* Q - y ᵥ* Q)‖₊ ≤ ‖WithLp.toLp 1 (x - y)‖₊ := by
  intro x y
  have hQ := (inferInstance : RowStochastic Q).stochastic
  have hxy : x ᵥ* Q - y ᵥ* Q = fun j => ∑ i, (x i - y i) * Q i j :=
    funext fun j => by simp [Matrix.vecMul, sub_eq_add_neg, sum_add_distrib, add_mul, dotProduct]
  have hnorm : (‖WithLp.toLp 1 (x ᵥ* Q - y ᵥ* Q)‖₊ : ℝ) = ∑ j, |∑ i, (x i - y i) * Q i j| := by
    rw [coe_nnnorm]
    convert l1_norm_eq_sum (WithLp.toLp 1 (x ᵥ* Q - y ᵥ* Q)) using 2 with j
    simp [congrFun hxy j]
  have hnorm2 : (‖WithLp.toLp 1 (x - y)‖₊ : ℝ) = ∑ i, |x i - y i| := by
    rw [coe_nnnorm]
    exact l1_norm_eq_sum (WithLp.toLp 1 (x - y))
  apply NNReal.coe_le_coe.mp
  rw [hnorm, hnorm2]
  calc ∑ j, |∑ i, (x i - y i) * Q i j|
      ≤ ∑ j, ∑ i, |x i - y i| * Q i j := by
        apply sum_le_sum; intro j _
        calc |∑ i, (x i - y i) * Q i j|
            ≤ ∑ i, |(x i - y i) * Q i j| := abs_sum_le_sum_abs _ _
          _ ≤ _ := sum_le_sum fun i _ => by
                rw [abs_mul, abs_of_nonneg ((hQ i).nonneg j)]
    _ = ∑ i, |x i - y i| := by
        rw [Finset.sum_comm]
        apply sum_congr rfl; intro i _
        rw [show ∑ j, |x i - y i| * Q i j = |x i - y i| * ∑ j, Q i j by
          simp [Finset.mul_sum], (hQ i).rowsum, mul_one]

theorem smat_pow_nonexpansive_in_l1 [DecidableEq S] (Q : Matrix S S ℝ) [RowStochastic Q] :
    ∀ n (x y : S → ℝ),
      ‖WithLp.toLp 1 (x ᵥ* Q ^ n - y ᵥ* Q ^ n)‖₊ ≤ ‖WithLp.toLp 1 (x - y)‖₊ := by
  intro n x y
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [pow_succ, ←Matrix.vecMul_vecMul]
    have := smat_nonexpansive_in_l1 Q (x ᵥ* Q ^ n) (y ᵥ* Q ^ n)
    exact this.trans ih

/-- The affine action of a stochastic matrix on the probability simplex. -/
def smat_as_operator (P : Matrix S S ℝ) [RowStochastic P] :
  ↑(Simplex S) → ↑(Simplex S) :=
  fun μ => ⟨WithLp.toLp 1 (μ.val.ofLp ᵥ* P), by
    exact svec_mul_smat_is_svec μ.val.ofLp P
  ⟩

lemma smat_as_operator_iter [DecidableEq S]
  (P : Matrix S S ℝ) [RowStochastic P] (n : ℕ)
  : (smat_as_operator P)^[n] = fun μ => ⟨WithLp.toLp 1 (μ.val.ofLp ᵥ* (P ^ n)), by
    exact svec_mul_smat_is_svec μ.val.ofLp (P ^ n)
  ⟩ := by
  induction n with
  | zero => funext μ; simp only [Function.iterate_zero, id_eq, pow_zero, Matrix.vecMul_one]
  | succ n ih =>
    funext μ
    simp only [Function.iterate_succ, Function.comp_apply, ih, smat_as_operator]
    congr 1
    simp only [Matrix.vecMul_vecMul]
    rw [(pow_succ' P n).symm]

theorem smat_contraction_in_simplex
  (P : Matrix S S ℝ) [RowStochastic P] [DoeblinMinorization P] :
    ∃ K, 0 < K ∧ ContractingWith K (smat_as_operator P)
  := by
    have hP := (inferInstance : RowStochastic P).stochastic
    obtain ⟨ε, ν, hεpos, hεlt1, hν, h_minorization⟩
      := (inferInstance : DoeblinMinorization P).minorize
    have hnonzero: 1 - ε ≠ 0 := by linarith
    let Q := (1 - ε)⁻¹ • (P - ε • broadcast ν)
    have h_decomp : P = ε • (broadcast ν) + (1 - ε) • Q := by
      unfold Q; simp [hnonzero];
    have hε0 : 0 ≤ 1 - ε := by linarith
    have hQ : RowStochastic Q := by
      refine ⟨fun i => ⟨fun j => ?_, ?_⟩⟩
      · simp only [Q, broadcast, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, smul_eq_mul]
        exact mul_nonneg (inv_nonneg.mpr hε0) (sub_nonneg.mpr (h_minorization i j))
      · have hval : ∀ x, Q i x = (1 - ε)⁻¹ * (P i x - ε * ν x) := fun x => by
          simp only [Q, broadcast, Matrix.smul_apply, Matrix.sub_apply,
            Matrix.of_apply, smul_eq_mul]
        rw [Finset.sum_congr rfl (fun x _ => hval x), ← Finset.mul_sum,
            Finset.sum_sub_distrib, ← Finset.mul_sum, (hP i).rowsum, hν.rowsum]
        field_simp
    let K : ℝ≥0 := ⟨1 - ε, hε0⟩
    refine ⟨K, by exact_mod_cast (show 0 < 1 - ε by linarith), ?_⟩
    refine ⟨by exact_mod_cast (show 1 - ε < 1 by linarith), fun x y => ?_⟩
    simp only [Set.coe_setOf, Set.mem_setOf_eq, smat_as_operator]
    have hxB : x.val.ofLp ᵥ* broadcast ν = ν :=
      funext fun j => by simp [vecMul_broadcast, x.property.rowsum]
    have hyB : y.val.ofLp ᵥ* broadcast ν = ν :=
      funext fun j => by simp [vecMul_broadcast, y.property.rowsum]
    have hxP : x.val.ofLp ᵥ* P =
        ε • (x.val.ofLp ᵥ* broadcast ν) + (1 - ε) • (x.val.ofLp ᵥ* Q) := by
      rw [h_decomp]; simp [Matrix.vecMul_add, Matrix.vecMul_smul]
    have hyP : y.val.ofLp ᵥ* P =
        ε • (y.val.ofLp ᵥ* broadcast ν) + (1 - ε) • (y.val.ofLp ᵥ* Q) := by
      rw [h_decomp]; simp [Matrix.vecMul_add, Matrix.vecMul_smul]
    have diff_eq :
        (x.val.ofLp ᵥ* P) - (y.val.ofLp ᵥ* P)
        = (1 - ε) • ((x.val.ofLp ᵥ* Q) - (y.val.ofLp ᵥ* Q)) := by
      rw [hxP, hyP, hxB, hyB]
      simp [smul_sub, add_sub_add_left_eq_sub]
    have hxynorm : ‖WithLp.toLp 1 (x.val.ofLp ᵥ* P - y.val.ofLp ᵥ* P)‖₊
        ≤ K * ‖x.val - y.val‖₊ := by
      rw [show WithLp.toLp 1 (x.val.ofLp ᵥ* P - y.val.ofLp ᵥ* P) =
          (1 - ε) • WithLp.toLp 1 (x.val.ofLp ᵥ* Q - y.val.ofLp ᵥ* Q) from
            by simp only [diff_eq, ← WithLp.toLp_smul],
          nnnorm_smul,
          show ‖(1 - ε : ℝ)‖₊ = K from
            NNReal.eq (by rw [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hε0]; rfl)]
      exact mul_le_mul_right (@smat_nonexpansive_in_l1 S _ Q hQ x.val.ofLp y.val.ofLp) K
    calc edist (smat_as_operator P x) (smat_as_operator P y)
        = edist (WithLp.toLp 1 (x.val.ofLp ᵥ* P)) (WithLp.toLp 1 (y.val.ofLp ᵥ* P)) := rfl
      _ = ‖WithLp.toLp 1 (x.val.ofLp ᵥ* P - y.val.ofLp ᵥ* P)‖₊ := by
            rw [edist_nndist]; simp only [nndist_eq_nnnorm, ← WithLp.toLp_sub]
      _ ≤ K * ‖x.val - y.val‖₊ := by exact_mod_cast hxynorm
      _ = K * edist x.val y.val := by simp [edist_nndist, nndist_eq_nnnorm]
      _ = K * edist x y := by rfl

end contraction

section stationary_distribution

/-- A stationary distribution for a matrix. -/
class Stationary (μ : S → ℝ) (P : Matrix S S ℝ) : Prop where
  stationary : μ ᵥ* P = μ

variable [DecidableEq S]

lemma multi_step_stationary
  (μ : S → ℝ) [StochasticVec μ]
  (P : Matrix S S ℝ) [RowStochastic P]
  (n : ℕ) [Stationary μ P] :
  Stationary μ (P ^ n) := by
  refine ⟨?_⟩
  induction n with
  | zero => simp [Matrix.vecMul_one]
  | succ n ih => rw [pow_succ, ← vecMul_vecMul, ih, (inferInstance : Stationary μ P).stationary]

theorem pos_of_stationary
  (μ : S → ℝ) [StochasticVec μ]
  (P : Matrix S S ℝ) [RowStochastic P] [Irreducible P]
  [Stationary μ P] :
  ∀ s, 0 < μ s := by
  by_contra h
  rw [not_forall] at h
  obtain ⟨s, hsle⟩ := h
  rw [not_lt] at hsle
  have hμ := (inferInstance : StochasticVec μ)
  have hs : μ s = 0 := le_antisymm hsle (hμ.nonneg s)
  have hμ0 : ∀ s', μ s' = 0 := by
    intro s'
    obtain ⟨n, hn⟩ := (inferInstance : Irreducible P).irreducible s' s
    have hPn := (multi_step_stationary μ P n).stationary
    have hsum : ∑ i, μ i * (P ^ n) i s = 0 := by
      have := congrFun hPn s
      simp only [Matrix.vecMul, dotProduct] at this
      simpa [hs] using this
    have hterm : ∀ i ∈ Finset.univ, 0 ≤ μ i * (P ^ n) i s :=
      fun i _ => mul_nonneg (hμ.nonneg i) ((RowStochastic.stochastic (P := P ^ n) i).nonneg s)
    rcases mul_eq_zero.mp
        ((Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsum s' (Finset.mem_univ s')) with h0 | h0
    · exact h0
    · exact absurd h0 (ne_of_gt hn)
  have := hμ.rowsum
  simp_rw [hμ0] at this
  simp at this


/-- The Cesaro average of the first `n + 1` iterates of a stochastic vector. -/
noncomputable def cesaro_average
  (x₀ : S → ℝ)
  (P : Matrix S S ℝ) (n : ℕ)
  : S → ℝ :=
  (n + 1 : ℝ)⁻¹ • ∑ k ∈ Finset.range (n + 1), x₀ ᵥ* (P ^ k)

lemma cesaro_average_is_svec
  (x₀ : S → ℝ) [StochasticVec x₀]
  (P : Matrix S S ℝ) [RowStochastic P] (n : ℕ)
  : StochasticVec (cesaro_average x₀ P n) := by
  have hval : ∀ i, (cesaro_average x₀ P n) i =
      (n + 1 : ℝ)⁻¹ * ∑ k ∈ Finset.range (n + 1), (x₀ ᵥ* (P ^ k)) i :=
    fun i => by simp only [cesaro_average, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  refine ⟨fun i => ?_, ?_⟩
  · rw [hval]
    exact mul_nonneg (inv_nonneg.mpr (by linarith))
      (sum_nonneg fun k _ => (svec_mul_smat_is_svec x₀ (P ^ k)).nonneg i)
  · rw [Finset.sum_congr rfl (fun i _ => hval i), ← mul_sum, Finset.sum_comm]
    simp_rw [fun k => (svec_mul_smat_is_svec x₀ (P ^ k)).rowsum, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp

lemma cesaro_average_almost_invariant
  (x₀ : S → ℝ) [StochasticVec x₀] (P : Matrix S S ℝ) [RowStochastic P]
  : ∀ n, ‖WithLp.toLp 1 ((cesaro_average x₀ P n) ᵥ* P - cesaro_average x₀ P n)‖ ≤ 2 / (n + 1)  := by
    intro n
    unfold cesaro_average
    have hn : 0 < (n : ℝ) + 1 := by linarith
    have hstep : ∀ k, (x₀ ᵥ* P ^ k) ᵥ* P - x₀ ᵥ* P ^ k = x₀ ᵥ* P ^ (k + 1) - x₀ ᵥ* P ^ k :=
      fun k => by rw [Matrix.vecMul_vecMul, ← pow_succ]
    calc
        ‖WithLp.toLp 1 (((n + 1 : ℝ)⁻¹ • ∑ k ∈ Finset.range (n + 1), x₀ ᵥ* P ^ k) ᵥ* P -
          (n + 1 : ℝ)⁻¹ • ∑ k ∈ Finset.range (n + 1), x₀ ᵥ* P ^ k)‖
      _ = ‖WithLp.toLp 1 ((n + 1 : ℝ)⁻¹ • (∑ k ∈ Finset.range (n + 1),
          ((x₀ ᵥ* P ^ k) ᵥ* P - x₀ ᵥ* P ^ k)))‖ := by
        rw [Matrix.smul_vecMul, ← smul_sub]
        congr 3
        rw [Finset.sum_sub_distrib, Matrix.sum_vecMul]
      _ = ‖WithLp.toLp 1 ((n + 1 : ℝ)⁻¹ • (x₀ ᵥ* P ^ (n + 1) - x₀ ᵥ* P ^ 0))‖ := by
        congr 3
        conv_lhs => rw [Finset.sum_congr rfl fun k _ => hstep k]
        rw [Finset.sum_range_sub (f := fun k => x₀ ᵥ* P ^ k)]
      _ = ‖(n + 1 : ℝ)⁻¹ • WithLp.toLp 1 (x₀ ᵥ* P ^ (n + 1) - x₀)‖ := by
        rw [← WithLp.toLp_smul]; congr 2; simp [pow_zero]
      _ = (n + 1 : ℝ)⁻¹ * ‖WithLp.toLp 1 (x₀ ᵥ* P ^ (n + 1) - x₀)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
      _ ≤ (n + 1 : ℝ)⁻¹ * 2 := by
          gcongr
          have : ‖WithLp.toLp 1 (x₀ ᵥ* P ^ (n + 1) - x₀)‖₊ ≤ 2 := by
            have := nnnorm_sub_le (WithLp.toLp 1 (x₀ ᵥ* P ^ (n + 1))) (WithLp.toLp 1 x₀)
            rw [← WithLp.toLp_sub] at this
            calc ‖WithLp.toLp 1 (x₀ ᵥ* P ^ (n + 1) - x₀)‖₊
                ≤ ‖WithLp.toLp 1 (x₀ ᵥ* P ^ (n + 1))‖₊ + ‖WithLp.toLp 1 x₀‖₊ := this
              _ = 2 := by
                  rw [l1_norm_eq_one (WithLp.toLp 1 (x₀ ᵥ* P ^ (n + 1))),
                      l1_norm_eq_one (WithLp.toLp 1 x₀)]
                  norm_num
          exact_mod_cast this
      _ = 2 / (n + 1) := by ring

variable [Nonempty S]

/-- The uniform probability distribution on a nonempty finite type. -/
noncomputable abbrev uniform_distribution : S → ℝ :=
  Function.const S (1 / Fintype.card S)

instance : StochasticVec (S := S) uniform_distribution :=
  ⟨fun s => by simp [uniform_distribution],
   by simp [uniform_distribution, Finset.sum_const, Finset.card_univ]⟩

instance : Nonempty ↑(Simplex S) :=
  ⟨⟨WithLp.toLp 1 uniform_distribution, by
    change StochasticVec (WithLp.toLp 1 uniform_distribution).ofLp
    rw [WithLp.ofLp_toLp]
    infer_instance⟩⟩

omit [DecidableEq S] in
theorem stationary_distribution_exists (P : Matrix S S ℝ) [RowStochastic P]
  : ∃ μ : S → ℝ, StochasticVec μ ∧ Stationary μ P := by
  classical
  let x₀ := uniform_distribution (S := S)
  let xn : ℕ → l1Space S := fun n => WithLp.toLp 1 (cesaro_average x₀ P n)
  have hx : ∀ n, xn n ∈ (Simplex S) := fun n => by
    change StochasticVec (WithLp.toLp 1 (cesaro_average x₀ P n)).ofLp
    rw [WithLp.ofLp_toLp]; exact cesaro_average_is_svec x₀ P n
  obtain ⟨μ, hμ, hstationary⟩ := IsCompact.tendsto_subseq (simples_is_compact (S := S)) hx
  refine ⟨μ.ofLp, hμ, ?_⟩
  refine ⟨?_⟩
  obtain ⟨nk, hn_increasing, hn_lim⟩ := hstationary
  have halmostinv : ∀ n, ‖WithLp.toLp 1 ((xn n).ofLp ᵥ* P - (xn n).ofLp)‖₁ ≤ 2 / (n + 1) :=
    fun n => cesaro_average_almost_invariant x₀ P n
  have hb : Tendsto (fun n => ‖WithLp.toLp 1 ((xn (nk n)).ofLp ᵥ* P - (xn (nk n)).ofLp)‖₁)
    atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    case hg => exact tendsto_const_nhds
    case hgf => intro n; positivity
    case hfh => exact fun n => halmostinv (nk n)
    case hh =>
      apply Metric.tendsto_atTop'.mpr
      intro ε hε
      obtain ⟨N, hN⟩ :=
        (hn_increasing.tendsto_atTop.eventually_ge_atTop
        (Nat.ceil (2 / ε))).exists
      refine ⟨N, fun n hnge => ?_⟩
      have hnkn : 0 < (nk n + 1 : ℝ) := by
        have : (0 : ℝ) ≤ nk n := Nat.cast_nonneg _
        linarith
      have hpos : (0 : ℝ) < 2 / (nk n + 1) := div_pos two_pos hnkn
      change dist (2 / ((nk n : ℝ) + 1)) 0 < ε
      rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
      have := hn_increasing hnge
      have hNle : (nk N : ℝ) < nk n := by exact_mod_cast this
      have : 2 / ε ≤ nk n := by
        have := Nat.ceil_le.mp hN
        linarith
      exact (div_lt_comm₀ (a := 2) (hb := hnkn) hε.lt).mpr (by linarith)
  let f := fun v : l1Space S => WithLp.toLp 1 (v.ofLp ᵥ* P)
  have hfcont : Continuous f :=
    (PiLp.continuous_toLp 1 _).comp ((PiLp.continuous_ofLp 1 _).matrix_vecMul continuous_const)
  have hc : Tendsto (fun n => f (xn (nk n)) - xn (nk n)) atTop (𝓝 (f μ - μ)) :=
    (hfcont.tendsto μ |>.comp hn_lim).sub hn_lim
  have hd : Tendsto (fun n => ‖f (xn (nk n)) - xn (nk n)‖) atTop (𝓝 0) := by
    simp_rw [show ∀ n, ‖f (xn (nk n)) - xn (nk n)‖ =
        (‖WithLp.toLp 1 ((xn (nk n)).ofLp ᵥ* P - (xn (nk n)).ofLp)‖₁ : ℝ) from fun _ => rfl]
    exact NNReal.tendsto_coe.mpr hb
  have he : ‖f μ - μ‖ = 0 := tendsto_nhds_unique (continuous_norm.tendsto _ |>.comp hc) hd
  have hfμ : f μ = μ := by rwa [norm_eq_zero, sub_eq_zero] at he
  simp only [f] at hfμ
  exact (WithLp.toLp_injective 1).eq_iff.mp hfμ

theorem stationary_distribution_uniquely_exists
  (P : Matrix S S ℝ) [RowStochastic P] [Aperiodic P] [Irreducible P]
  : ∃! μ : S → ℝ, StochasticVec μ ∧ Stationary μ P := by
  obtain ⟨μ, hμ, hμstationary⟩ := stationary_distribution_exists P
  refine ⟨μ, ⟨hμ, hμstationary⟩, fun ν hν => ?_⟩
  obtain ⟨hν, hνstationary⟩ := hν
  obtain ⟨N, _, hN⟩ := smat_minorizable_with_large_pow P
  let f := smat_as_operator (P ^ N)
  obtain ⟨K, _, hf⟩ := smat_contraction_in_simplex (P ^ N)
  have toFixed : ∀ v : S → ℝ, (hv : StochasticVec v) → [Stationary v P] →
      IsFixedPt f ⟨WithLp.toLp 1 v, hv⟩ := fun v _ _ => by
    simp only [IsFixedPt, f, smat_as_operator, Subtype.mk.injEq]
    exact (WithLp.toLp_injective 1).eq_iff.mpr (multi_step_stationary v P N).stationary
  haveI : Stationary ν P := hνstationary
  have hμfixed := fixedPoint_unique hf (toFixed μ hμ)
  have hνfixed := fixedPoint_unique hf (toFixed ν hν)
  have := hνfixed.trans hμfixed.symm
  simp only [Subtype.mk.injEq] at this
  exact (WithLp.toLp_injective 1).eq_iff.mp this

/-- Geometric convergence to stationarity in total variation/L¹ distance. -/
class GeometricMixing
  (P : Matrix S S ℝ) [RowStochastic P]
  : Prop where
  mixing : ∃ (C : ℝ) (ρ : ℝ) (μ : S → ℝ),
    0 < C ∧ 0 < ρ ∧ ρ < 1 ∧ StochasticVec μ ∧ Stationary μ P ∧
    ∀ (x : S → ℝ) [StochasticVec x] (n : ℕ),
      ‖WithLp.toLp 1 (x ᵥ* (P ^ n) - μ)‖₁ ≤ C * ρ ^ n

instance (P : Matrix S S ℝ) [RowStochastic P] [Aperiodic P] [Irreducible P]
  : GeometricMixing P := by
  obtain ⟨μ, hμ, hμstationary⟩ := stationary_distribution_exists P
  obtain ⟨N, hNge1, hN⟩ := smat_minorizable_with_large_pow P
  have hNpos : 0 < N := by linarith
  obtain ⟨K, hKpos, hf⟩ := smat_contraction_in_simplex (P ^ N)
  have hμfixed : ⟨WithLp.toLp 1 μ, hμ⟩ = fixedPoint (smat_as_operator (P ^ N)) hf :=
    fixedPoint_unique hf (by
      simp only [IsFixedPt, smat_as_operator, Subtype.mk.injEq]
      exact (WithLp.toLp_injective 1).eq_iff.mpr (multi_step_stationary μ P N).stationary)
  have hKle1 : (K : ℝ) ≤ 1 := NNReal.coe_le_one.mpr hf.1.le
  refine ⟨⟨2 / K / (1 - K), K ^ (1 / (N : ℝ)), μ,
    mul_pos (by simp [hKpos]) (by simp [hf.1]),
    Real.rpow_pos_of_pos hKpos _,
    Real.rpow_lt_one (by simp) (by simp [hf.1]) (by simp [hNpos]),
    hμ, hμstationary, ?_⟩⟩
  intro x₀ hx₀ n
  have hrate := apriori_dist_iterate_fixedPoint_le hf
    ⟨WithLp.toLp 1 x₀, hx₀⟩ (n / N)
  rw [← hμfixed] at hrate
  simp only [smat_as_operator] at hrate
  rw [smat_as_operator_iter (P ^ N) (n / N)] at hrate
  have hbnd2 : ‖WithLp.toLp 1 (x₀ - x₀ ᵥ* P ^ N)‖₁ ≤ 2 := by
    rw [WithLp.toLp_sub]
    calc ‖WithLp.toLp 1 x₀ - WithLp.toLp 1 (x₀ ᵥ* P ^ N)‖₁
        ≤ ‖WithLp.toLp 1 x₀‖₁ + ‖WithLp.toLp 1 (x₀ ᵥ* P ^ N)‖₁ := norm_sub_le _ _
      _ = 2 := by
          rw [l1_norm_eq_one (WithLp.toLp 1 x₀), l1_norm_eq_one (WithLp.toLp 1 (x₀ ᵥ* P ^ N))]
          norm_num
  calc
      toReal ‖WithLp.toLp 1 (x₀ ᵥ* P ^ n - μ)‖₁
    _ ≤ toReal ‖WithLp.toLp 1 (x₀ ᵥ* (P ^ N) ^ (n / N) - μ)‖₁ := by
        have hPn : P ^ n = (P ^ N) ^ (n / N) * P ^ (n % N) := by
          conv_lhs => rw [← Nat.div_add_mod n N, pow_add, pow_mul]
        conv_lhs =>
          rw [hPn, ← vecMul_vecMul, ← (multi_step_stationary μ P (n % N)).stationary]
        exact smat_nonexpansive_in_l1 (P ^ (n % N)) (x₀ ᵥ* (P ^ N) ^ (n / N)) μ
    _ ≤ toReal ‖WithLp.toLp 1 (x₀ - x₀ ᵥ* P ^ N)‖₁ * K ^ (n / N) / (1 - K) := hrate
    _ ≤ 2 * K ^ (n / N) / (1 - K) := by
        gcongr
        · linarith
        · exact_mod_cast hbnd2
      _ ≤ 2 * K ^ (((n : ℝ) / N) - 1) / (1 - K) := by
        set z : ℕ := n / N
        set z' : ℝ := (n : ℝ) / N
        have : z ≥ z' - 1 := by
          have : n < (z + 1) * N := by calc
              n
            _ = z * N + n % N := (Nat.div_add_mod' n N).symm
            _ < z * N + N := by
              have := Nat.mod_lt n hNpos.gt
              linarith
            _ = (z + 1) * N := by
              simp [Nat.succ_mul, Nat.add_comm]
          have : (n : ℝ) ≤ (z + 1) * (N : ℝ) := by
            exact_mod_cast (Nat.le_of_lt this)
          rw [mul_comm] at this
          have := (div_le_iff₀' (c := (N : ℝ)) (a := (z + 1 : ℝ)) (b := (n : ℝ))
            (by exact_mod_cast hNpos)).mpr this
          linarith
        have : (K : ℝ) ^ z ≤ (K : ℝ) ^ (z' - 1) := by
          have := Real.rpow_le_rpow_of_exponent_le_or_ge
            (x := (K : ℝ)) (y := (z : ℝ)) (z := z' - 1) (h := by
            apply Or.inr; refine ⟨hKpos, hKle1, this.le⟩)
          exact_mod_cast this
        gcongr
        case hc => linarith
      _ = (2 / K / (1 - K)) * (K ^ (1 / (N : ℝ))) ^ n := by
        have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast hKpos.ne'
        have hsub : (K : ℝ) ^ ((n : ℝ) / N - 1) = (K : ℝ) ^ ((n : ℝ) / N) / K :=
          Real.rpow_sub_one hKne _
        have hpow : ((K : ℝ) ^ (1 / (N : ℝ))) ^ n = (K : ℝ) ^ ((n : ℝ) / N) := by
          rw [← Real.rpow_natCast ((K : ℝ) ^ (1 / (N : ℝ))) n,
            ← Real.rpow_mul (NNReal.coe_nonneg K)]
          congr 1
          field_simp
        rw [hsub, hpow]
        ring

end stationary_distribution

end StochasticMatrix
