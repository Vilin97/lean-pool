/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.Random.ReducibleSpan
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.LeibnizRemainder
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPoint
public import LeanPool.ConwayRefinement.ConwayRefinement.LinearAlgebra.FiniteSpanRelation

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPointCofinality
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueImage
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The successor step `(*)_α ⇒ (*)_{α+1}` and `(*)_n` for finite `n`

Fornasiero, Lavi, L'Innocente and Mantova, *Irreducibility in generalized power series* (2024),
Proposition 4.4, and Corollary 4.5 for `α = n < ω` (Remark 4.6).

Suppose `b = ∑ λ_j b_j ∈ A_{n+1}` with `Q(b_1, …, b_m)` and `λ ≠ 0`; write
`b = ∑ μ_k p_k q_k + r` with `p_k, q_k` of positive degrees `β_k + γ_k = n + 1` and
`r ∈ J_{n+1}`. For `γ < 0` close to zero, Berarducci's Leibniz rule (Proposition 2.10) gives
`b^{|γ} ≡ ∑ μ_k (p_k^{|γ} q_k + p_k q_k^{|γ})` modulo `J_n`, and each term `p_k^{|γ} q_k` lies in
`K q_k + A_n`: its class is `k · rv_J(q_k)` when `p_k^{|γ} ∈ J + K`, and a product of two classes
of positive grades otherwise. So the classes of the `b^{|γ}` lie, modulo `D_n`, in the span of
`2m` fixed vectors. The residual points of `b` are cofinal at zero (Berarducci, Lemma 6.8), so
`2m + 1` of them close to zero give a nontrivial relation `∑ δ_i b^{|γ_i} ∈ A_n`. Expanding
`b^{|γ_i} = ∑ λ_j b_j^{|γ_i}` and discarding the truncations of degree below `n`, Axiom 2 of
`Q(b_1, …, b_m)` makes the remaining truncations hereditarily `rv_J`-independent at degree `n`,
so `(*)_n` forces every coefficient `δ_i λ_j` with `deg_J(b_j^{|γ_i}) = n` to vanish; since each
residual point `γ_i` has some `j` with `λ_j ≠ 0` and `deg_J(b_j^{|γ_i}) = n`, this contradicts
`δ ≠ 0`.

The source applies `(*)_n` to the translated truncations `b_j^{|γ_i}`, which are not principal
in general; `(*)_n` is therefore stated here for all series of degree `n`, as explained in
`ConwayRefinement.HahnSeries.Factorization.Random.ReducibleSpan`. The representatives `p_k, q_k`
of the classes generating `D_{n+1}` need not be principal either: the Leibniz rule is available
for every series of the relevant ordinal-value cuts.
-/

open Filter Topology
open scoped DirectSum HahnSeries NatOrdinal

universe v

public noncomputable section

namespace FLLM24

open Berarducci

variable {K : Type v} [Field K]

/-- A positive natural ordinal bounded by a natural number has positive constant coefficient. -/
theorem _root_.NatOrdinal.constantCoeff_pos_of_pos_of_le_natCast {β : NatOrdinal} {m : ℕ}
    (hpos : 0 < β) (hle : β ≤ m) : 0 < β.constantCoeff := by
  obtain ⟨k, rfl⟩ := NatOrdinal.lt_omega0.mp (hle.trans_lt (NatOrdinal.natCast_lt_omega0 m))
  rw [NatOrdinal.constantCoeff_natCast]
  exact Nat.cast_pos.mp hpos

/-- Translated truncation of a `K`-linear combination of series. -/
theorem translatedTruncation_sum_C_mul {ι : Type*} (s : Finset ι) (g : ι → K) (b : ι → Series K)
    (γ : ℝ) :
    translatedTruncation ((∑ i ∈ s, (HahnSeries.Nonpositive.C : K →+* Series K) (g i) * b i :
      Series K) : K⟦ℝ⟧) γ =
      ∑ i ∈ s, (HahnSeries.Nonpositive.C : K →+* Series K) (g i) *
        translatedTruncation (b i : K⟦ℝ⟧) γ := by
  rw [← translatedTruncationAddMonoidHom_apply, AddSubmonoidClass.coe_finsetSum, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [translatedTruncationAddMonoidHom_apply, Subring.coe_mul, HahnSeries.Nonpositive.coe_C,
    translatedTruncation_C_mul]

/-- FLLM24, proof of Proposition 4.4: if `deg_J(p) = β ≥ 1`, `deg_J(q) = γ ≥ 1` and
`(β - 1) + γ = n`, then for `γ' < 0` close to zero the grade-`n` class of `p^{|γ'} q` lies in
`K · rv_J(q) + D_n`: when `p^{|γ'} ∈ J + K` it is a scalar multiple of the class of `q`, and
otherwise it is a product of two classes of positive grades. -/
theorem eventually_gradeClass_translatedTruncation_mul_mem {n : ℕ} {β γ : NatOrdinal}
    (hβ : 0 < β.constantCoeff) (hγ : 0 < γ) (hsum : β.removeNat 1 + γ = n)
    {p q : Series K} (hp : ordinalValue p < ω^ (β + 1)) (hq : ordinalValue q < ω^ (γ + 1)) :
    ∀ᶠ γ' in 𝓝[<] (0 : ℝ),
      gradeClass (n : NatOrdinal) (translatedTruncation (p : K⟦ℝ⟧) γ' * q) ∈
        (K ∙ gradeClass (n : NatOrdinal) q) ⊔ decomposableSpan K (n : NatOrdinal) := by
  have hβ' : β.removeNat 1 + 1 = β := by
    simpa using NatOrdinal.removeNat_add_natCast hβ
  have hdrop := eventually_ordinalValue_translatedTruncation_lt_wpow_of_ordinalValue_lt_wpow_add_one
    β p hp
  filter_upwards [hdrop] with γ' hγ'
  set w := translatedTruncation (p : K⟦ℝ⟧) γ' with hw
  rw [← hβ'] at hγ'
  rcases eq_or_ne (β.removeNat 1) 0 with hzero | hpos
  · -- `w ∈ J + K`: the class of `w q` is a scalar multiple of the class of `q`.
    rw [hzero, zero_add] at hsum hγ'
    rw [← hsum]
    have hwNear : w ∈ nearConstantSubgroup K := by
      by_contra hnot
      have hlt := one_lt_ordinalValue_iff.mpr hnot
      rcases ordinalValue_eq_or_lt_of_lt_wpow_add_one
        (α := 0) (by rwa [zero_add]) with hone | hzero'
      · rw [NatOrdinal.wpow_zero] at hone
        exact absurd hone hlt.ne'
      · rw [NatOrdinal.wpow_zero] at hzero'
        exact absurd (hzero'.trans hlt) (lt_irrefl _)
    obtain ⟨j, hj, k, hjk⟩ := mem_nearConstantSubgroup_iff.mp hwNear
    have hjq : gradeClass γ (j * q) = 0 := by
      apply gradeClass_eq_zero_of_lt
      rw [ordinalValue_of_mem_negativeMonomialIdeal (Ideal.mul_mem_right q _ hj)]
      exact NatOrdinal.wpow_pos γ
    have hjqcut : ordinalValue (j * q) < ω^ (γ + 1) := by
      rw [ordinalValue_of_mem_negativeMonomialIdeal (Ideal.mul_mem_right q _ hj)]
      exact NatOrdinal.wpow_pos _
    have hkq : ordinalValue ((HahnSeries.Nonpositive.C : K →+* Series K) k * q) < ω^ (γ + 1) := by
      simpa only [zero_add] using
        ordinalValue_mul_lt_wpow_add_one (ordinalValue_C_lt_wpow_one k) hq
    rw [← hjk, add_mul, gradeClass_add hjqcut hkq, hjq, zero_add, gradeClass_C_mul k hq]
    exact Submodule.mem_sup_left (Submodule.mem_span_singleton.mpr ⟨k, rfl⟩)
  · -- `w` has positive degree `β - 1`: the class of `w q` is decomposable.
    have hmem := gradeClass_mul_mem_decomposableSpan (pos_iff_ne_zero.mpr hpos) hγ hγ' hq
    rw [hsum] at hmem
    exact Submodule.mem_sup_right hmem

/-- Berarducci, Lemma 6.8, as used in FLLM24, Proposition 4.4: a series of ordinal value
`ω^(α+1)` has, in every interval `(η, 0)`, as many residual points as desired; at a residual
point the translated truncation has ordinal value `ω^α`. -/
theorem exists_finset_residualPoints {α : NatOrdinal} {b : Series K}
    (hb : ordinalValue b = ω^ (α + 1)) {η : ℝ} (hη : η < 0) (N : ℕ) :
    ∃ Γ : Finset ℝ, Γ.card = N ∧
      ∀ γ ∈ Γ, η < γ ∧ γ < 0 ∧ ordinalValue (translatedTruncation (b : K⟦ℝ⟧) γ) = ω^ α := by
  have hone : 1 < ordinalValue b := by
    rw [hb]
    calc (1 : NatOrdinal) = ω^ (0 : NatOrdinal) := NatOrdinal.wpow_zero.symm
      _ < ω^ (α + 1) := NatOrdinal.wpow_lt_wpow.mpr
        (lt_of_lt_of_le (lt_add_one (0 : NatOrdinal))
          (add_le_add (bot_le : (0 : NatOrdinal) ≤ α) le_rfl))
  let b' : SeriesWithOrdinalValueAboveOne K := ⟨b, hone⟩
  have hres : b'.residualValue = ω^ α := by
    have hcoeff : 0 < (α + 1).constantCoeff := by
      have h := NatOrdinal.constantCoeff_add_natCast α 1
      rw [Nat.cast_one] at h
      rw [h]
      exact Nat.succ_pos _
    rw [b'.residualValue_eq_wpow_removeNat_of_ordinalValue_eq_wpow (α + 1) hcoeff hb]
    congr 1
    have h := NatOrdinal.removeNat_add_natCast (a := α + 1) (n := 1) (by
      have h := NatOrdinal.constantCoeff_add_natCast α 1
      rw [Nat.cast_one] at h
      rw [h]; exact Nat.le_add_left 1 _)
    rw [Nat.cast_one] at h
    exact add_right_cancel h
  have hLUB := residualPointSet_isLUB_zero b'
  -- Residual points in `(η, 0)` form an infinite set.
  have hinf : (residualPointSet b' ∩ Set.Ioo η 0).Infinite := by
    intro hfin
    let S := residualPointSet b' ∩ Set.Ioo η 0 ∪ {η}
    have hSfin : S.Finite := hfin.union (Set.finite_singleton η)
    have hSne : S.Nonempty := ⟨η, Set.mem_union_right _ rfl⟩
    have hmem := hSne.csSup_mem hSfin
    have hneg : sSup S < 0 := by
      rcases hmem with hmem | hmem
      · exact hmem.2.2
      · rw [Set.mem_singleton_iff] at hmem
        rw [hmem]; exact hη
    have hηle : η ≤ sSup S := le_csSup hSfin.bddAbove (Set.mem_union_right _ rfl)
    obtain ⟨c, hc, hlt, hc0⟩ := hLUB.exists_between' (zero_not_mem_residualPointSet b') hneg
    have hcS : c ∈ S := Set.mem_union_left _ ⟨hc, hηle.trans_lt hlt, hc0⟩
    exact absurd (le_csSup hSfin.bddAbove hcS) (not_le.mpr hlt)
  obtain ⟨Γ, hΓ, hcard⟩ := hinf.exists_subset_card_eq N
  refine ⟨Γ, hcard, fun γ hγ ↦ ?_⟩
  have hγ' := hΓ hγ
  refine ⟨hγ'.2.1, hγ'.2.2, ?_⟩
  rw [← hres]
  exact (mem_residualPointSet_iff.mp hγ'.1).2

/-- The quotient map by `D` sends `(K · v) + D` into `K · (v mod D)`. -/
private theorem mkQ_mem_span_singleton_of_mem_sup {V : Type*} [AddCommGroup V] [Module K V]
    {D : Submodule K V} {x v : V} (h : x ∈ (K ∙ v) ⊔ D) : D.mkQ x ∈ K ∙ D.mkQ v := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp h
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hz0 : D.mkQ z = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hz
  rw [map_add, map_smul, hz0, add_zero]
  exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩

/-- FLLM24, Proposition 4.4, at finite degrees: `(*)_n` implies `(*)_{n+1}` for `n ≥ 1`. -/
theorem independentModuloDecomposable_succ {n : ℕ} (hn : 1 ≤ n)
    (hstar : IndependentModuloDecomposable K n) :
    IndependentModuloDecomposable K (n + 1) := by
  classical
  refine IndependentModuloDecomposable.of fun {ι} b hQ ↦ ?_
  rw [Nat.cast_succ, linearIndependent_iff']
  intro s g hsum i₀ hi₀
  by_contra hg₀
  set N : NatOrdinal := (n : NatOrdinal) + 1 with hN
  have hNcast : ((n + 1 : ℕ) : NatOrdinal) = N := Nat.cast_succ n
  have hval : ∀ i, ordinalValue (b i) = ω^ N := fun i ↦ by
    rw [← hNcast]; exact hQ.ordinalValue_eq i
  have hcut : ∀ i, ordinalValue (b i) < ω^ (N + 1) := fun i ↦ by
    rw [hval i]; exact NatOrdinal.wpow_lt_wpow.mpr (lt_add_one N)
  -- The support `T` of the coefficients `g` inside `s`.
  set T := s.filter (fun i ↦ g i ≠ 0) with hT
  have hi₀T : i₀ ∈ T := Finset.mem_filter.mpr ⟨hi₀, hg₀⟩
  have hgT : ∀ i ∈ T, g i ≠ 0 := fun i hi ↦ (Finset.mem_filter.mp hi).2
  have hsumT : ∑ i ∈ T, g i • (decomposableSpan K N).mkQ (rvJ (b i)) = 0 := by
    rw [hT, Finset.sum_filter_of_ne]
    · exact hsum
    · intro x _ hx hgx
      exact hx (by rw [hgx, zero_smul])
  have hrel : ∑ i ∈ T, g i • rvJ (b i) ∈ decomposableSpan K N := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sum]
    simpa only [map_smul] using hsumT
  -- The series `B = ∑ g i • b i` has ordinal value `ω^N` and class in `D_N`.
  set B : Series K := ∑ i ∈ T, (HahnSeries.Nonpositive.C : K →+* Series K) (g i) * b i with hB
  have hCcut : ∀ i ∈ T,
      ordinalValue ((HahnSeries.Nonpositive.C : K →+* Series K) (g i) * b i) < ω^ (N + 1) :=
    fun i _ ↦ by
      simpa only [zero_add] using
        ordinalValue_mul_lt_wpow_add_one (ordinalValue_C_lt_wpow_one (g i)) (hcut i)
  have hBcut : ordinalValue B < ω^ (N + 1) := ordinalValue_sum_lt_wpow_add_one T _ hCcut
  have hBclass : gradeClass N B = ∑ i ∈ T, g i • rvJ (b i) := by
    rw [hB, gradeClass_sum T _ hCcut]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [gradeClass_C_mul (g i) (hcut i), rvJ_eq_gradeClass (hval i)]
  have hBne : gradeClass N B ≠ 0 := by
    intro hzero
    rw [hBclass] at hzero
    exact hg₀ (linearIndependent_iff'.mp hQ.linearIndependent T g hzero i₀ hi₀T)
  have hBval : ordinalValue B = ω^ N := ordinalValue_eq_of_gradeClass_ne_zero hBcut hBne
  -- The decomposition `B = ∑ μ_k u_k w_k + r` with `r ∈ J_N`.
  have hBmem : gradeClass N B ∈ decomposableSpan K N := by rw [hBclass]; exact hrel
  obtain ⟨m, μ, β, γ, u, w, hk, hdecomp⟩ := exists_sum_of_mem_decomposableSpan hBmem
  have hNle : ∀ k, β k ≤ ((n + 1 : ℕ) : NatOrdinal) ∧ γ k ≤ ((n + 1 : ℕ) : NatOrdinal) := by
    intro k
    rw [hNcast, ← (hk k).2.2.1]
    exact ⟨NatOrdinal.le_add_right, NatOrdinal.le_add_left⟩
  have hβc : ∀ k, 0 < (β k).constantCoeff := fun k ↦
    NatOrdinal.constantCoeff_pos_of_pos_of_le_natCast (hk k).1 (hNle k).1
  have hγc : ∀ k, 0 < (γ k).constantCoeff := fun k ↦
    NatOrdinal.constantCoeff_pos_of_pos_of_le_natCast (hk k).2.1 (hNle k).2
  have hβγ : ∀ k, (β k).removeNat 1 + γ k = n := by
    intro k
    have h1 : (β k).removeNat 1 + 1 = β k := by
      simpa using NatOrdinal.removeNat_add_natCast (hβc k)
    apply add_right_cancel (b := (1 : NatOrdinal))
    rw [add_right_comm, h1, (hk k).2.2.1]
  have hγβ : ∀ k, (γ k).removeNat 1 + β k = n := by
    intro k
    have h1 : (γ k).removeNat 1 + 1 = γ k := by
      simpa using NatOrdinal.removeNat_add_natCast (hγc k)
    apply add_right_cancel (b := (1 : NatOrdinal))
    rw [add_right_comm, h1, add_comm, (hk k).2.2.1]
  have huw : ∀ k, ordinalValue (u k * w k) < ω^ (N + 1) := fun k ↦ by
    have h := ordinalValue_mul_lt_wpow_add_one (hk k).2.2.2.1 (hk k).2.2.2.2
    rwa [(hk k).2.2.1] at h
  have hCuw : ∀ k ∈ (Finset.univ : Finset (Fin m)),
      ordinalValue ((HahnSeries.Nonpositive.C : K →+* Series K) (μ k) * (u k * w k)) <
        ω^ (N + 1) := fun k _ ↦ by
    simpa only [zero_add] using
      ordinalValue_mul_lt_wpow_add_one (ordinalValue_C_lt_wpow_one (μ k)) (huw k)
  set P : Series K :=
    ∑ k, (HahnSeries.Nonpositive.C : K →+* Series K) (μ k) * (u k * w k) with hP
  have hPcut : ordinalValue P < ω^ (N + 1) := ordinalValue_sum_lt_wpow_add_one _ _ hCuw
  have hPclass : gradeClass N P = ∑ k, μ k • gradeClass N (u k * w k) := by
    rw [hP, gradeClass_sum _ _ hCuw]
    exact Finset.sum_congr rfl fun k _ ↦ gradeClass_C_mul (μ k) (huw k)
  set r : Series K := B - P with hr
  have hrlt : ordinalValue r < ω^ N := by
    rw [← gradeClass_eq_zero_iff (by
      rw [hr, sub_eq_add_neg]
      exact (ordinalValue_add_le_max B (-P)).trans_lt
        (max_lt hBcut (by rwa [ordinalValue_neg]))), hr, gradeClass_sub hBcut hPcut, hPclass,
      ← hdecomp, sub_self]
  have hBPr : B = P + r := by rw [hr]; abel
  -- The eventual statements near zero.
  have hev : ∀ᶠ γ' in 𝓝[<] (0 : ℝ),
      (∀ k, ordinalValue (translatedTruncation ((u k * w k : Series K) : K⟦ℝ⟧) γ' -
          translatedTruncation (u k : K⟦ℝ⟧) γ' * w k - u k * translatedTruncation (w k : K⟦ℝ⟧) γ')
          < ω^ (n : NatOrdinal)) ∧
      (∀ k, gradeClass (n : NatOrdinal) (translatedTruncation (u k : K⟦ℝ⟧) γ' * w k) ∈
          (K ∙ gradeClass (n : NatOrdinal) (w k)) ⊔ decomposableSpan K (n : NatOrdinal)) ∧
      (∀ k, gradeClass (n : NatOrdinal) (translatedTruncation (w k : K⟦ℝ⟧) γ' * u k) ∈
          (K ∙ gradeClass (n : NatOrdinal) (u k)) ⊔ decomposableSpan K (n : NatOrdinal)) ∧
      (∀ k, ordinalValue (translatedTruncation (u k : K⟦ℝ⟧) γ') < ω^ (β k)) ∧
      (∀ k, ordinalValue (translatedTruncation (w k : K⟦ℝ⟧) γ') < ω^ (γ k)) ∧
      (∀ k, ordinalValue (translatedTruncation ((u k * w k : Series K) : K⟦ℝ⟧) γ') < ω^ N) ∧
      ordinalValue (translatedTruncation (r : K⟦ℝ⟧) γ') < ω^ (n : NatOrdinal) ∧
      (∀ i ∈ T, ordinalValue (translatedTruncation (b i : K⟦ℝ⟧) γ') < ω^ N) := by
    refine Filter.Eventually.and (Filter.eventually_all.mpr fun k ↦ ?_)
      (Filter.Eventually.and (Filter.eventually_all.mpr fun k ↦ ?_)
      (Filter.Eventually.and (Filter.eventually_all.mpr fun k ↦ ?_)
      (Filter.Eventually.and (Filter.eventually_all.mpr fun k ↦ ?_)
      (Filter.Eventually.and (Filter.eventually_all.mpr fun k ↦ ?_)
      (Filter.Eventually.and (Filter.eventually_all.mpr fun k ↦ ?_)
      (Filter.Eventually.and ?_ ((Filter.eventually_all_finset T).mpr fun i _ ↦ ?_)))))))
    · have h := eventually_ordinalValue_leibnizRemainder_lt (hβc k) (u k) (w k)
        (hk k).2.2.2.1 (hk k).2.2.2.2
      rwa [hβγ k] at h
    · exact eventually_gradeClass_translatedTruncation_mul_mem (hβc k) (hk k).2.1 (hβγ k)
        (hk k).2.2.2.1 (hk k).2.2.2.2
    · exact eventually_gradeClass_translatedTruncation_mul_mem (hγc k) (hk k).1 (hγβ k)
        (hk k).2.2.2.2 (hk k).2.2.2.1
    · exact eventually_ordinalValue_translatedTruncation_lt_wpow_of_ordinalValue_lt_wpow_add_one
        (β k) (u k) (hk k).2.2.2.1
    · exact eventually_ordinalValue_translatedTruncation_lt_wpow_of_ordinalValue_lt_wpow_add_one
        (γ k) (w k) (hk k).2.2.2.2
    · exact eventually_ordinalValue_translatedTruncation_lt_wpow_of_ordinalValue_lt_wpow_add_one
        N (u k * w k) (huw k)
    · exact eventually_ordinalValue_translatedTruncation_lt_wpow_of_ordinalValue_lt_wpow_add_one
        (n : NatOrdinal) r hrlt
    · exact eventually_ordinalValue_translatedTruncation_lt_wpow_of_ordinalValue_lt_wpow_add_one
        N (b i) (hcut i)
  obtain ⟨η, hη, hη'⟩ := eventually_nhdsLT_iff_exists.mp hev
  obtain ⟨δQ, hδQ, hQ2⟩ := hQ.truncations hn
  -- Residual points of `B` above both thresholds.
  obtain ⟨Γ, hΓcard, hΓ⟩ :=
    exists_finset_residualPoints (α := (n : NatOrdinal)) hBval (max_lt hη hδQ) (2 * m + 1)
  set π := (decomposableSpan K (n : NatOrdinal)).mkQ with hπ
  -- For a residual point `γ'`, the class of `B^{|γ'}` expands along `T` and along the
  -- Leibniz rule.
  have hBtrunc : ∀ γ' ∈ Γ,
      gradeClass (n : NatOrdinal) (translatedTruncation (B : K⟦ℝ⟧) γ') =
        ∑ i ∈ T, g i • gradeClass (n : NatOrdinal) (translatedTruncation (b i : K⟦ℝ⟧) γ') := by
    intro γ' hγ'
    obtain ⟨hηγ, hγ0, -⟩ := hΓ γ' hγ'
    have hE := hη' γ' ((le_max_left η δQ).trans_lt hηγ) hγ0
    rw [hB, translatedTruncation_sum_C_mul, gradeClass_sum]
    · exact Finset.sum_congr rfl fun i hi ↦ gradeClass_C_mul (g i) (hE.2.2.2.2.2.2.2 i hi)
    · intro i hi
      simpa only [zero_add] using ordinalValue_mul_lt_wpow_add_one
        (ordinalValue_C_lt_wpow_one (g i)) (hE.2.2.2.2.2.2.2 i hi)
  have hBleib : ∀ γ' ∈ Γ,
      gradeClass (n : NatOrdinal) (translatedTruncation (B : K⟦ℝ⟧) γ') =
        ∑ k, μ k • (gradeClass (n : NatOrdinal) (translatedTruncation (u k : K⟦ℝ⟧) γ' * w k) +
          gradeClass (n : NatOrdinal) (translatedTruncation (w k : K⟦ℝ⟧) γ' * u k)) := by
    intro γ' hγ'
    obtain ⟨hηγ, hγ0, -⟩ := hΓ γ' hγ'
    obtain ⟨hE1, -, -, hE8, hE9, hE4, hE5, -⟩ := hη' γ' ((le_max_left η δQ).trans_lt hηγ) hγ0
    have hYcut : ∀ k,
        ordinalValue (translatedTruncation (u k : K⟦ℝ⟧) γ' * w k) < ω^ N := fun k ↦ by
      have h1 : ordinalValue (translatedTruncation (u k : K⟦ℝ⟧) γ') <
          ω^ ((β k).removeNat 1 + 1) := by
        rw [show (β k).removeNat 1 + 1 = β k by
          simpa using NatOrdinal.removeNat_add_natCast (hβc k)]
        exact hE8 k
      have h := ordinalValue_mul_lt_wpow_add_one h1 (hk k).2.2.2.2
      rwa [hβγ k] at h
    have hZcut : ∀ k,
        ordinalValue (translatedTruncation (w k : K⟦ℝ⟧) γ' * u k) < ω^ N := fun k ↦ by
      have h1 : ordinalValue (translatedTruncation (w k : K⟦ℝ⟧) γ') <
          ω^ ((γ k).removeNat 1 + 1) := by
        rw [show (γ k).removeNat 1 + 1 = γ k by
          simpa using NatOrdinal.removeNat_add_natCast (hγc k)]
        exact hE9 k
      have h := ordinalValue_mul_lt_wpow_add_one h1 (hk k).2.2.2.1
      rwa [hγβ k] at h
    have hCtrunc : ∀ k ∈ (Finset.univ : Finset (Fin m)),
        ordinalValue ((HahnSeries.Nonpositive.C : K →+* Series K) (μ k) *
          translatedTruncation ((u k * w k : Series K) : K⟦ℝ⟧) γ') < ω^ N := fun k _ ↦ by
      simpa only [zero_add] using
        ordinalValue_mul_lt_wpow_add_one (ordinalValue_C_lt_wpow_one (μ k)) (hE4 k)
    have hPtrunc : ordinalValue (translatedTruncation (P : K⟦ℝ⟧) γ') < ω^ N := by
      rw [hP, translatedTruncation_sum_C_mul]
      exact ordinalValue_sum_lt_wpow_add_one _ _ hCtrunc
    have hrtrunc : ordinalValue (translatedTruncation (r : K⟦ℝ⟧) γ') < ω^ N :=
      hE5.trans (NatOrdinal.wpow_lt_wpow.mpr (lt_add_one _))
    rw [hBPr, Subring.coe_add, translatedTruncation_add, gradeClass_add hPtrunc hrtrunc,
      gradeClass_eq_zero_of_lt hE5, add_zero, hP, translatedTruncation_sum_C_mul,
      gradeClass_sum _ _ hCtrunc]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [gradeClass_C_mul (μ k) (hE4 k)]
    congr 1
    rw [← gradeClass_add (hYcut k) (hZcut k)]
    apply gradeClass_eq_of_sub_lt (hE4 k)
      ((ordinalValue_add_le_max _ _).trans_lt (max_lt (hYcut k) (hZcut k)))
    rw [mul_comm (translatedTruncation (w k : K⟦ℝ⟧) γ') (u k), ← sub_sub]
    exact hE1 k
  -- The classes of the `B^{|γ'}`, modulo `D_n`, lie in the span of `2m` vectors.
  let gens : Fin m ⊕ Fin m → PrincipalSubring K ⧸ decomposableSpan K (n : NatOrdinal) :=
    Sum.elim (fun k ↦ π (gradeClass (n : NatOrdinal) (u k)))
      (fun k ↦ π (gradeClass (n : NatOrdinal) (w k)))
  have hspan : ∀ γ' : Γ,
      π (gradeClass (n : NatOrdinal) (translatedTruncation (B : K⟦ℝ⟧) γ')) ∈
        Submodule.span K (Set.range gens) := by
    intro γ'
    obtain ⟨hηγ, hγ0, -⟩ := hΓ γ' γ'.2
    obtain ⟨-, hE2, hE3, -⟩ := hη' γ' ((le_max_left η δQ).trans_lt hηγ) hγ0
    rw [hBleib γ' γ'.2, map_sum]
    refine Submodule.sum_mem _ fun k _ ↦ ?_
    rw [map_smul, map_add]
    refine Submodule.smul_mem _ _ (Submodule.add_mem _ ?_ ?_)
    · refine Submodule.span_mono ?_ (mkQ_mem_span_singleton_of_mem_sup (hE2 k))
      exact Set.singleton_subset_iff.mpr ⟨Sum.inr k, rfl⟩
    · refine Submodule.span_mono ?_ (mkQ_mem_span_singleton_of_mem_sup (hE3 k))
      exact Set.singleton_subset_iff.mpr ⟨Sum.inl k, rfl⟩
  have hcard : Fintype.card (Fin m ⊕ Fin m) < Fintype.card Γ := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe, hΓcard]
    omega
  obtain ⟨sΓ, δ, hδrel, γ₀, hγ₀, hδ₀⟩ :=
    Module.exists_nontrivial_relation_of_mem_span_range gens
      (fun γ' : Γ ↦ π (gradeClass (n : NatOrdinal) (translatedTruncation (B : K⟦ℝ⟧) γ')))
      hspan hcard
  -- The relation, expanded along `T` and restricted to the truncations of degree `n`.
  have hδmem : ∑ γ' ∈ sΓ, δ γ' • gradeClass (n : NatOrdinal)
      (translatedTruncation (B : K⟦ℝ⟧) γ') ∈ decomposableSpan K (n : NatOrdinal) := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sum]
    simpa only [map_smul] using hδrel
  have hcutT : ∀ γ' ∈ sΓ, ∀ i ∈ T,
      ordinalValue (translatedTruncation (b i : K⟦ℝ⟧) γ') < ω^ ((n : NatOrdinal) + 1) := by
    intro γ' _ i hi
    obtain ⟨hηγ, hγ0, -⟩ := hΓ γ' γ'.2
    exact (hη' γ' ((le_max_left η δQ).trans_lt hηγ) hγ0).2.2.2.2.2.2.2 i hi
  set S₁ := (sΓ ×ˢ T).filter (fun p : Γ × ι ↦
    ordinalValue (translatedTruncation (b p.2 : K⟦ℝ⟧) p.1) = ω^ (n : NatOrdinal)) with hS₁
  have hrelS₁ : ∑ p ∈ S₁, (δ p.1 * g p.2) • rvJ (translatedTruncation (b p.2 : K⟦ℝ⟧) p.1) ∈
      decomposableSpan K (n : NatOrdinal) := by
    have hexpand : ∑ γ' ∈ sΓ, δ γ' • gradeClass (n : NatOrdinal)
        (translatedTruncation (B : K⟦ℝ⟧) γ') =
        ∑ p ∈ sΓ ×ˢ T, (δ p.1 * g p.2) •
          gradeClass (n : NatOrdinal) (translatedTruncation (b p.2 : K⟦ℝ⟧) p.1) := by
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl fun γ' _ ↦ ?_
      rw [hBtrunc γ' γ'.2, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_smul]
    rw [hexpand, ← Finset.sum_filter_add_sum_filter_not (sΓ ×ˢ T) (fun p : Γ × ι ↦
      ordinalValue (translatedTruncation (b p.2 : K⟦ℝ⟧) p.1) = ω^ (n : NatOrdinal))] at hδmem
    have hzero : ∑ p ∈ (sΓ ×ˢ T).filter (fun p : Γ × ι ↦
        ¬ ordinalValue (translatedTruncation (b p.2 : K⟦ℝ⟧) p.1) = ω^ (n : NatOrdinal)),
        (δ p.1 * g p.2) • gradeClass (n : NatOrdinal) (translatedTruncation (b p.2 : K⟦ℝ⟧) p.1)
          = 0 := by
      refine Finset.sum_eq_zero fun p hp ↦ ?_
      obtain ⟨hp, hne⟩ := Finset.mem_filter.mp hp
      obtain ⟨hγ', hi⟩ := Finset.mem_product.mp hp
      rcases ordinalValue_eq_or_lt_of_lt_wpow_add_one (hcutT p.1 hγ' p.2 hi) with heq | hlt
      · exact absurd heq hne
      · rw [gradeClass_eq_zero_of_lt hlt, smul_zero]
    rw [hzero, add_zero] at hδmem
    convert hδmem using 2 with p hp
    rw [rvJ_eq_gradeClass (Finset.mem_filter.mp hp).2]
  -- Axiom 2 makes the surviving truncations hereditarily `rv_J`-independent at degree `n`.
  have hQS₁ : HereditarilyRVIndependent n
      (fun p : S₁ ↦ translatedTruncation (b p.1.2 : K⟦ℝ⟧) (p.1.1 : ℝ)) := by
    refine hQ2 S₁ (fun p ↦ p.1.2) (fun p ↦ (p.1.1 : ℝ)) ?_ ?_ ?_ ?_
    · intro p q hpq
      have h1 : p.1.2 = q.1.2 := congrArg Prod.fst hpq
      have h2 : (p.1.1 : ℝ) = (q.1.1 : ℝ) := congrArg Prod.snd hpq
      exact Subtype.ext (Prod.ext (Subtype.ext h2) h1)
    · intro p
      obtain ⟨hηγ, -, -⟩ := hΓ p.1.1 p.1.1.2
      exact ((le_max_right η δQ).trans_lt hηγ).le
    · intro p
      exact (hΓ p.1.1 p.1.1.2).2.1.le
    · intro p
      exact (Finset.mem_filter.mp p.2).2
  have hlin := hstar.linearIndependent hQS₁
  rw [Fintype.linearIndependent_iff] at hlin
  have hcoeff : ∀ p : S₁, δ p.1.1 * g p.1.2 = 0 := by
    refine hlin (fun p ↦ δ p.1.1 * g p.1.2) ?_
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sum] at hrelS₁
    rw [← Finset.sum_coe_sort S₁] at hrelS₁
    simpa only [map_smul] using hrelS₁
  -- At the residual point `γ₀` some `b i^{|γ₀}` with `g i ≠ 0` has degree `n`.
  have hBγ₀ : gradeClass (n : NatOrdinal) (translatedTruncation (B : K⟦ℝ⟧) γ₀) ≠ 0 := by
    have hres := (hΓ γ₀ γ₀.2).2.2
    rw [← rvJ_eq_gradeClass hres]
    exact rvJ_ne_zero_of_eq hres
  rw [hBtrunc γ₀ γ₀.2] at hBγ₀
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hBγ₀
  have hgc : gradeClass (n : NatOrdinal) (translatedTruncation (b i : K⟦ℝ⟧) γ₀) ≠ 0 :=
    fun h ↦ hne (by rw [h, smul_zero])
  have hdeg : ordinalValue (translatedTruncation (b i : K⟦ℝ⟧) γ₀) = ω^ (n : NatOrdinal) :=
    ordinalValue_eq_of_gradeClass_ne_zero (hcutT γ₀ hγ₀ i hi) hgc
  have hpS₁ : (γ₀, i) ∈ S₁ := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hγ₀, hi⟩, hdeg⟩
  exact mul_ne_zero hδ₀ (hgT i hi) (hcoeff ⟨(γ₀, i), hpS₁⟩)

/-- FLLM24, Corollary 4.5 for `α = n < ω` (Remark 4.6): `(*)_n` holds for every `n ≥ 1`, by
induction from Proposition 4.3 through Proposition 4.4. -/
theorem independentModuloDecomposable_of_pos {n : ℕ} (hn : 1 ≤ n) :
    IndependentModuloDecomposable K n := by
  induction n with
  | zero => exact absurd hn (by decide)
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact independentModuloDecomposable_one
      · exact independentModuloDecomposable_succ hpos (ih hpos)

end FLLM24

end
