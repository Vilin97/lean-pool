/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import LeanPool.BollobasNikiforov.Basic.Graph
public import LeanPool.BollobasNikiforov.Basic.Inner
public import LeanPool.BollobasNikiforov.CP.Basic
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Algebra.Order.Star.Real

/-!
# Motzkin–Straus

The Motzkin–Straus theorem bounds the adjacency quadratic form on the
nonnegative orthant by the Turán factor `1 - 1/ω(G)`, and the same bound
passes to the Frobenius pairing against a completely positive matrix.
-/

@[expose] public section

namespace BollobasNikiforov

open Matrix
open scoped Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### MS05 — Cauchy–Schwarz on a block of size `k` -/

lemma sum_sq_le_card_mul_sum_sq_finset {ι : Type*} (s : Finset ι) (y : ι → ℝ) :
    (∑ i ∈ s, y i) ^ 2 ≤ s.card * ∑ i ∈ s, y i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) s y fun _ => (1 : ℝ)
  simp only [mul_one, one_pow] at h
  have h1 : ∑ i ∈ s, (1 : ℝ) = s.card := by
    simp [Finset.sum_const, nsmul_eq_mul]
  simpa [h1, mul_comm] using h

/-- **MS05.** Cauchy–Schwarz against the all-ones vector:
`(∑ y)² ≤ k ∑ yᵢ²`. -/
lemma sum_sq_le_card_mul_sum_sq {ι : Type*} [Fintype ι] (y : ι → ℝ) :
    (∑ i, y i) ^ 2 ≤ Fintype.card ι * ∑ i, y i ^ 2 :=
  sum_sq_le_card_mul_sum_sq_finset Finset.univ y

lemma sum_sq_sub_sum_sq_le_finset {ι : Type*} (s : Finset ι) (y : ι → ℝ)
    (hk : 1 ≤ s.card) :
    (∑ i ∈ s, y i) ^ 2 - ∑ i ∈ s, y i ^ 2 ≤
      (1 - 1 / (s.card : ℝ)) * (∑ i ∈ s, y i) ^ 2 := by
  have hkpos : (0 : ℝ) < s.card := Nat.cast_pos.mpr (Nat.succ_le_iff.mp hk)
  have hcs := sum_sq_le_card_mul_sum_sq_finset s y
  have hdiv : (1 / (s.card : ℝ)) * (∑ i ∈ s, y i) ^ 2 ≤ ∑ i ∈ s, y i ^ 2 := by
    rw [one_div, mul_comm, ← div_eq_mul_inv]
    exact (div_le_iff₀ hkpos).mpr (hcs.trans_eq (mul_comm _ _))
  have hring :
      (1 - 1 / (s.card : ℝ)) * (∑ i ∈ s, y i) ^ 2 =
        (∑ i ∈ s, y i) ^ 2 - (1 / (s.card : ℝ)) * (∑ i ∈ s, y i) ^ 2 := by ring
  rw [hring]
  exact sub_le_sub_left hdiv _

/-- **MS05.** If `k ≥ 1` then `(∑ y)² - ∑ y² ≤ (1 - 1/k) (∑ y)²`. -/
lemma sum_sq_sub_sum_sq_le {ι : Type*} [Fintype ι] (y : ι → ℝ)
    (hk : 1 ≤ Fintype.card ι) :
    (∑ i, y i) ^ 2 - ∑ i, y i ^ 2 ≤
      (1 - 1 / (Fintype.card ι : ℝ)) * (∑ i, y i) ^ 2 :=
  sum_sq_sub_sum_sq_le_finset Finset.univ y hk

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### MS01 — quadratic form as an edge sum -/

omit [DecidableEq V] in
/-- **MS01.** The adjacency quadratic form expands as a sum over edges. -/
lemma mulVec_adjMatrix_dotProduct (y : V → ℝ) :
    mulVec (G.adjMatrix ℝ) y ⬝ᵥ y =
      ∑ i, ∑ j, (if G.Adj i j then y i * y j else 0) := by
  rw [dotProduct_comm]
  exact G.dotProduct_mulVec_adjMatrix y y

omit [DecidableEq V] in
lemma continuous_adjMatrix_quadratic :
    Continuous fun y : V → ℝ => y ⬝ᵥ G.adjMatrix ℝ *ᵥ y :=
  continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)

/-! ### MS02 — affinity along a nonedge -/

omit [Fintype V] in
lemma add_smul_e_sub_e_apply {i j : V} (hne : i ≠ j) (y : V → ℝ) (t : ℝ) (k : V) :
    (y + t • (e i - e j)) k =
      if k = i then y i + t else if k = j then y j - t else y k := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [sub_single_apply hne]
  split_ifs with hki hkj
  · subst hki; ring
  · subst hkj; ring
  · simp

lemma sum_e_sub_e {i j : V} :
    ∑ k, (e i - e j) k = 0 := by
  simp only [e, Pi.sub_apply]
  rw [Finset.sum_sub_distrib, Fintype.sum_pi_single', Fintype.sum_pi_single']
  simp

lemma add_smul_e_sub_e_mem_stdSimplex {i j : V} (hne : i ≠ j)
    {y : V → ℝ} (hy : y ∈ stdSimplex ℝ V) {t : ℝ}
    (hti : 0 ≤ y i + t) (htj : 0 ≤ y j - t) :
    y + t • (e i - e j) ∈ stdSimplex ℝ V := by
  refine ⟨fun k => ?_, ?_⟩
  · rw [add_smul_e_sub_e_apply hne]
    split_ifs
    · exact hti
    · exact htj
    · exact hy.1 k
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hy.2, sum_e_sub_e, mul_zero, add_zero]

/-- The second-difference coefficient along a nonedge vanishes:
`Aᵢᵢ = Aⱼⱼ = Aᵢⱼ = 0`. -/
lemma adjMatrix_quadratic_e_sub_e {i j : V} (hij : ¬ G.Adj i j) (_hne : i ≠ j) :
    (e i - e j) ⬝ᵥ G.adjMatrix ℝ *ᵥ (e i - e j) = 0 := by
  have hji : ¬ G.Adj j i := fun h => hij h.symm
  have hvec : G.adjMatrix ℝ *ᵥ (e i - e j) =
      (G.adjMatrix ℝ *ᵥ e i - G.adjMatrix ℝ *ᵥ e j) := mulVec_sub _ _ _
  rw [hvec, sub_dotProduct]
  have hi :
      e i ⬝ᵥ (G.adjMatrix ℝ *ᵥ e i - G.adjMatrix ℝ *ᵥ e j) =
        (G.adjMatrix ℝ *ᵥ e i) i - (G.adjMatrix ℝ *ᵥ e j) i := by
    rw [dotProduct_sub]
    simp [e, single_dotProduct]
  have hj :
      e j ⬝ᵥ (G.adjMatrix ℝ *ᵥ e i - G.adjMatrix ℝ *ᵥ e j) =
        (G.adjMatrix ℝ *ᵥ e i) j - (G.adjMatrix ℝ *ᵥ e j) j := by
    rw [dotProduct_sub]
    simp [e, single_dotProduct]
  have hcol (k l : V) : (G.adjMatrix ℝ *ᵥ e l) k = (G.adjMatrix ℝ) k l := by
    simp [e]
  rw [hi, hj]
  simp [hcol, hij, hji]

lemma adjMatrix_dotProduct_e_sub_e (y : V → ℝ) {i j : V} :
    (e i - e j) ⬝ᵥ G.adjMatrix ℝ *ᵥ y =
      (G.adjMatrix ℝ *ᵥ y) i - (G.adjMatrix ℝ *ᵥ y) j := by
  rw [sub_dotProduct]
  simp only [e, single_dotProduct, one_mul]

omit [DecidableEq V] in
lemma adjMatrix_quadratic_symm (y d : V → ℝ) :
    y ⬝ᵥ G.adjMatrix ℝ *ᵥ d = d ⬝ᵥ G.adjMatrix ℝ *ᵥ y := by
  rw [dotProduct_mulVec, ← mulVec_transpose, G.transpose_adjMatrix, dotProduct_comm]

/-- **MS02.** Along a nonedge the adjacency quadratic is affine in the
transfer parameter `t`. The inequalities keep the perturbation
nonnegative and are used in MS03. -/
lemma adjMatrix_quadratic_add_smul_single_sub_single
    {i j : V} (hij : ¬ G.Adj i j) (hne : i ≠ j) (y : V → ℝ) (t : ℝ)
    (hti : 0 ≤ y i + t) (htj : 0 ≤ y j - t) :
    (y + t • (e i - e j)) ⬝ᵥ G.adjMatrix ℝ *ᵥ (y + t • (e i - e j)) =
      y ⬝ᵥ G.adjMatrix ℝ *ᵥ y +
        2 * t * ((G.adjMatrix ℝ *ᵥ y) i - (G.adjMatrix ℝ *ᵥ y) j) := by
  set d := e i - e j
  have hi : 0 ≤ (y + t • (e i - e j)) i := by
    simpa [add_smul_e_sub_e_apply hne, hne] using hti
  have hj : 0 ≤ (y + t • (e i - e j)) j := by
    rw [add_smul_e_sub_e_apply hne, ite_eq_right hne.symm, ite_eq_left rfl]
    exact htj
  have _ := hi
  have _ := hj
  have hmul :
      G.adjMatrix ℝ *ᵥ (y + t • d) = G.adjMatrix ℝ *ᵥ y + t • G.adjMatrix ℝ *ᵥ d := by
    rw [mulVec_add, mulVec_smul]
  calc
    (y + t • d) ⬝ᵥ G.adjMatrix ℝ *ᵥ (y + t • d)
      = (y + t • d) ⬝ᵥ (G.adjMatrix ℝ *ᵥ y + t • G.adjMatrix ℝ *ᵥ d) := by
          rw [hmul]
    _ = y ⬝ᵥ (G.adjMatrix ℝ *ᵥ y + t • G.adjMatrix ℝ *ᵥ d) +
          (t • d) ⬝ᵥ (G.adjMatrix ℝ *ᵥ y + t • G.adjMatrix ℝ *ᵥ d) :=
          add_dotProduct _ _ _
    _ = y ⬝ᵥ G.adjMatrix ℝ *ᵥ y + y ⬝ᵥ (t • G.adjMatrix ℝ *ᵥ d) +
          ((t • d) ⬝ᵥ G.adjMatrix ℝ *ᵥ y + (t • d) ⬝ᵥ (t • G.adjMatrix ℝ *ᵥ d)) := by
          simp only [dotProduct_add, add_assoc]
    _ = y ⬝ᵥ G.adjMatrix ℝ *ᵥ y + t * (y ⬝ᵥ G.adjMatrix ℝ *ᵥ d) +
          (t * (d ⬝ᵥ G.adjMatrix ℝ *ᵥ y) + t * t * (d ⬝ᵥ G.adjMatrix ℝ *ᵥ d)) := by
          simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul, mul_assoc]
    _ = y ⬝ᵥ G.adjMatrix ℝ *ᵥ y + t * (d ⬝ᵥ G.adjMatrix ℝ *ᵥ y) +
          (t * (d ⬝ᵥ G.adjMatrix ℝ *ᵥ y) + t * t * 0) := by
          rw [adjMatrix_quadratic_symm y d, adjMatrix_quadratic_e_sub_e hij hne]
    _ = y ⬝ᵥ G.adjMatrix ℝ *ᵥ y +
          2 * t * ((G.adjMatrix ℝ *ᵥ y) i - (G.adjMatrix ℝ *ᵥ y) j) := by
          rw [adjMatrix_dotProduct_e_sub_e]
          ring

/-! ### MS03 — a maximizer with clique support -/

omit [DecidableEq V] in
lemma stdSimplex_nonempty [Nonempty V] : (stdSimplex ℝ V).Nonempty := by
  classical
  exact ⟨Pi.single (Classical.arbitrary V) 1, single_mem_stdSimplex ℝ _⟩

omit [DecidableEq V] in
lemma exists_isMaxOn_adjMatrix_quadratic [Nonempty V] :
    ∃ y, y ∈ stdSimplex ℝ V ∧
      IsMaxOn (fun y : V → ℝ => y ⬝ᵥ G.adjMatrix ℝ *ᵥ y) (stdSimplex ℝ V) y :=
  (isCompact_stdSimplex ℝ V).exists_isMaxOn stdSimplex_nonempty
    continuous_adjMatrix_quadratic.continuousOn

omit [DecidableEq V] in
/-- **MS03.** The adjacency quadratic attains its maximum on the simplex, and
some maximizer is supported on a clique. -/
lemma exists_isMaxOn_adjMatrix_quadratic_isClique_support [Nonempty V] :
    ∃ y, y ∈ stdSimplex ℝ V ∧
      IsMaxOn (fun y : V → ℝ => y ⬝ᵥ G.adjMatrix ℝ *ᵥ y) (stdSimplex ℝ V) y ∧
      G.IsClique {v | y v ≠ 0} := by
  classical
  set f : (V → ℝ) → ℝ := fun y => y ⬝ᵥ G.adjMatrix ℝ *ᵥ y
  obtain ⟨y0, hy0, hmax0⟩ := exists_isMaxOn_adjMatrix_quadratic (G := G)
  have hind : ∀ n : ℕ, ∀ y : V → ℝ, y ∈ stdSimplex ℝ V → IsMaxOn f (stdSimplex ℝ V) y →
      (Finset.univ.filter (fun v => y v ≠ 0)).card = n →
      ∃ z, z ∈ stdSimplex ℝ V ∧ IsMaxOn f (stdSimplex ℝ V) z ∧
        G.IsClique {v | z v ≠ 0} := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro y hy hmax hn
      by_cases hc : G.IsClique {v | y v ≠ 0}
      · exact ⟨y, hy, hmax, hc⟩
      · obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, hne₀, hnad⟩ :=
          (_root_.SimpleGraph.not_isClique_iff (G := G) (s := {v | y v ≠ 0})).mp hc
        have hi : y i ≠ 0 := hi
        have hj : y j ≠ 0 := hj
        have hne : i ≠ j := Subtype.coe_ne_coe.mpr hne₀
        have hyi : 0 < y i := lt_of_le_of_ne (hy.1 i) hi.symm
        have hyj : 0 < y j := lt_of_le_of_ne (hy.1 j) hj.symm
        set δ := (G.adjMatrix ℝ *ᵥ y) i - (G.adjMatrix ℝ *ᵥ y) j
        set t := if 0 ≤ δ then y j else -y i
        have hti : 0 ≤ y i + t := by
          by_cases hδ : 0 ≤ δ
          · simp only [hδ, ↓reduceIte, t]
            exact add_nonneg (hy.1 i) (hy.1 j)
          · simp [t, hδ]
        have htj : 0 ≤ y j - t := by
          by_cases hδ : 0 ≤ δ
          · simp [t, hδ]
          · simp only [hδ, ↓reduceIte, sub_neg_eq_add, t]
            exact add_nonneg (hy.1 j) (hy.1 i)
        have ht_mul : 0 ≤ t * δ := by
          by_cases hδ : 0 ≤ δ
          · rw [show t = y j from ite_eq_left hδ]
            exact mul_nonneg hyj.le hδ
          · rw [show t = -y i from ite_eq_right hδ]
            exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.2 hyi.le) (le_of_not_ge hδ)
        have ht_ne : t ≠ 0 := by
          by_cases hδ : 0 ≤ δ
          · rw [show t = y j from ite_eq_left hδ]
            exact hyj.ne'
          · rw [show t = -y i from ite_eq_right hδ]
            exact neg_ne_zero.2 hyi.ne'
        have hy' : y + t • (e i - e j) ∈ stdSimplex ℝ V :=
          add_smul_e_sub_e_mem_stdSimplex hne hy hti htj
        have hquad :=
          adjMatrix_quadratic_add_smul_single_sub_single hnad hne y t hti htj
        have hf' : f (y + t • (e i - e j)) = f y + 2 * t * δ := by
          simpa [f, δ] using hquad
        have hfyle : f (y + t • (e i - e j)) ≤ f y := hmax hy'
        have hinc0 : 2 * t * δ = 0 := by
          have : 0 ≤ 2 * (t * δ) :=
            mul_nonneg (by positivity : (0 : ℝ) ≤ 2) ht_mul
          linarith
        have hδ0 : δ = 0 := by
          have : t * δ = 0 := by nlinarith
          exact (mul_eq_zero.mp this).resolve_left ht_ne
        have htj0 : t = y j := by simp [t, hδ0]
        have hyj' : (y + t • (e i - e j)) j = 0 := by
          rw [add_smul_e_sub_e_apply hne, ite_eq_right hne.symm, ite_eq_left rfl, htj0]
          ring
        have hmax' : IsMaxOn f (stdSimplex ℝ V) (y + t • (e i - e j)) := by
          intro z hz
          have heq : f (y + t • (e i - e j)) = f y := by
            simp [hf', hδ0]
          rw [heq]
          exact hmax hz
        set y' := y + t • (e i - e j)
        set s := Finset.univ.filter (fun v => y v ≠ 0)
        set s' := Finset.univ.filter (fun v => y' v ≠ 0)
        have hsubset : s' ⊆ s := by
          intro v hv
          simp only [s', s, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
          by_cases hvi : v = i
          · subst hvi
            exact hi
          · by_cases hvj : v = j
            · subst hvj
              exact (hv hyj').elim
            · have : y' v = y v := by
                simp [y', add_smul_e_sub_e_apply hne, hvi, hvj]
              rwa [this] at hv
        have hjmem : j ∈ s := by simp [s, hj]
        have hjnot : j ∉ s' := by
          simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and, Decidable.not_not, s']
          exact hyj'
        have hss : s' ⊂ s :=
          Finset.ssubset_iff_subset_ne.2 ⟨hsubset, fun h => hjnot (h ▸ hjmem)⟩
        have hn' : s'.card < n := by
          rw [← hn]
          exact Finset.card_lt_card hss
        exact ih s'.card hn' y' hy' hmax' rfl
  exact hind _ y0 hy0 hmax0 rfl

/-! ### MS04 — clique computation -/

omit [DecidableEq V] in
/-- **MS04.** On a clique the adjacency quadratic is `(∑ y)² - ∑ y²`. -/
lemma adjMatrix_quadratic_eq_sum_sq_sub_of_isClique
    {s : Set V} (hs : G.IsClique s) {y : V → ℝ}
    (hsupp : ∀ v, y v ≠ 0 → v ∈ s) :
    y ⬝ᵥ G.adjMatrix ℝ *ᵥ y = (∑ i, y i) ^ 2 - ∑ i, y i ^ 2 := by
  classical
  have hprod : ∀ i j, ¬ G.Adj i j → i ≠ j → y i * y j = 0 := by
    intro i j hAdj hne
    by_contra h0
    exact hAdj (hs (hsupp i (left_ne_zero_of_mul h0))
      (hsupp j (right_ne_zero_of_mul h0)) hne)
  have hterm : ∀ i j,
      y i * y j =
        (if G.Adj i j then y i * y j else 0) + if i = j then y i * y j else 0 := by
    intro i j
    by_cases hAdj : G.Adj i j
    · have hne : i ≠ j := hAdj.ne
      rw [ite_eq_left hAdj, ite_eq_right hne]
      ring
    · by_cases hij : i = j
      · subst hij
        rw [ite_eq_right hAdj, ite_eq_left rfl]
        ring
      · rw [ite_eq_right hAdj, ite_eq_right hij, hprod i j hAdj hij]
        ring
  apply eq_sub_of_add_eq
  calc
    y ⬝ᵥ G.adjMatrix ℝ *ᵥ y + ∑ i, y i ^ 2
      = (∑ i, ∑ j, if G.Adj i j then y i * y j else 0) +
          ∑ i, ∑ j, if i = j then y i * y j else 0 := by
          rw [G.dotProduct_mulVec_adjMatrix]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [pow_two]
    _ = ∑ i, ∑ j, y i * y j := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => (hterm i j).symm
    _ = (∑ i, y i) ^ 2 := by
          rw [pow_two, Finset.sum_mul_sum]

/-! ### MS06 — Motzkin–Straus -/

omit [DecidableEq V] in
lemma adjMatrix_quadratic_le_turanFactor_of_isClique_support
    {y : V → ℝ} (hy : y ∈ stdSimplex ℝ V)
    (hc : G.IsClique {v | y v ≠ 0}) :
    y ⬝ᵥ G.adjMatrix ℝ *ᵥ y ≤ turanFactor G := by
  set s := Finset.univ.filter (fun v => y v ≠ 0)
  have hs_set : (s : Set V) = {v | y v ≠ 0} := by ext; simp [s]
  have hs : G.IsClique (s : Set V) := by simpa [hs_set] using hc
  have hsupp : ∀ v, y v ≠ 0 → v ∈ s := by intro v hv; simp [s, hv]
  have hquad := adjMatrix_quadratic_eq_sum_sq_sub_of_isClique hs hsupp
  have hsne : s.Nonempty := by
    have h1 : ∑ i, y i = 1 := hy.2
    have : ∃ i, y i ≠ 0 := by
      by_contra h
      push Not at h
      simp [h] at h1
    obtain ⟨i, hi⟩ := this
    exact ⟨i, by simp [s, hi]⟩
  have hk : 1 ≤ s.card := Finset.one_le_card.mpr hsne
  have hsum : ∑ i, y i = ∑ i ∈ s, y i :=
    (Finset.sum_subset (Finset.subset_univ s) fun i _ hi => by
        simp [s] at hi; simp [hi]).symm
  have hsq : ∑ i, y i ^ 2 = ∑ i ∈ s, y i ^ 2 :=
    (Finset.sum_subset (Finset.subset_univ s) fun i _ hi => by
        simp [s] at hi; simp [hi]).symm
  have hcs := sum_sq_sub_sum_sq_le_finset s y hk
  have hω : s.card ≤ G.cliqueNum := hs.card_le_cliqueNum
  have hkpos : (0 : ℝ) < s.card := Nat.cast_pos.mpr (Nat.succ_le_iff.mp hk)
  have hinv : 1 / (G.cliqueNum : ℝ) ≤ 1 / (s.card : ℝ) :=
    one_div_le_one_div_of_le hkpos (Nat.cast_le.mpr hω)
  have hy1s : ∑ i ∈ s, y i = 1 := by rw [← hsum, hy.2]
  calc
    y ⬝ᵥ G.adjMatrix ℝ *ᵥ y
      = (∑ i, y i) ^ 2 - ∑ i, y i ^ 2 := hquad
    _ = (∑ i ∈ s, y i) ^ 2 - ∑ i ∈ s, y i ^ 2 := by rw [hsum, hsq]
    _ ≤ (1 - 1 / (s.card : ℝ)) * (∑ i ∈ s, y i) ^ 2 := hcs
    _ = (1 - 1 / (s.card : ℝ)) * 1 ^ 2 := by rw [hy1s]
    _ = 1 - 1 / (s.card : ℝ) := by ring
    _ ≤ 1 - 1 / (G.cliqueNum : ℝ) := sub_le_sub_left hinv _
    _ = turanFactor G := rfl

omit [DecidableEq V] in
lemma adjMatrix_quadratic_le_turanFactor_of_mem_stdSimplex
    [Nonempty V] {y : V → ℝ} (hy : y ∈ stdSimplex ℝ V) :
    y ⬝ᵥ G.adjMatrix ℝ *ᵥ y ≤ turanFactor G := by
  obtain ⟨z, hz, hmax, hc⟩ := exists_isMaxOn_adjMatrix_quadratic_isClique_support (G := G)
  exact (hmax hy).trans (adjMatrix_quadratic_le_turanFactor_of_isClique_support hz hc)

omit [DecidableEq V] in
lemma adjMatrix_quadratic_smul (c : ℝ) (y : V → ℝ) :
    (c • y) ⬝ᵥ G.adjMatrix ℝ *ᵥ (c • y) =
      c ^ 2 * (y ⬝ᵥ G.adjMatrix ℝ *ᵥ y) := by
  simp [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, pow_two, mul_assoc]

omit [DecidableEq V] in
/-- **MS06.** Motzkin–Straus: `yᵀ A_G y ≤ (1 - 1/ω(G)) (1ᵀ y)²` for `y ≥ 0`. -/
lemma motzkinStraus {y : V → ℝ} (hy : ∀ i, 0 ≤ y i) :
    y ⬝ᵥ G.adjMatrix ℝ *ᵥ y ≤ turanFactor G * (∑ i, y i) ^ 2 := by
  by_cases h0 : ∑ i, y i = 0
  · have hy0 : y = 0 := by
      ext i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hy j)).1 h0 i (Finset.mem_univ i)
    simp [hy0]
  · have hV : Nonempty V := by
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
      exact ⟨i⟩
    have := hV
    set σ := ∑ i, y i
    have hσpos : 0 < σ :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ => hy i) (Ne.symm h0)
    set z : V → ℝ := σ⁻¹ • y
    have hz : z ∈ stdSimplex ℝ V := by
      refine ⟨fun i => mul_nonneg (inv_nonneg.2 hσpos.le) (hy i), ?_⟩
      change ∑ i, σ⁻¹ * y i = 1
      rw [← Finset.mul_sum, inv_mul_cancel₀ h0]
    have hzle := adjMatrix_quadratic_le_turanFactor_of_mem_stdSimplex (G := G) hz
    have hscale : z ⬝ᵥ G.adjMatrix ℝ *ᵥ z = σ⁻¹ ^ 2 * (y ⬝ᵥ G.adjMatrix ℝ *ᵥ y) :=
      adjMatrix_quadratic_smul σ⁻¹ y
    have : y ⬝ᵥ G.adjMatrix ℝ *ᵥ y = σ ^ 2 * (z ⬝ᵥ G.adjMatrix ℝ *ᵥ z) := by
      rw [hscale]
      field_simp [h0]
    rw [this]
    exact (mul_le_mul_of_nonneg_left hzle (sq_nonneg σ)).trans_eq (mul_comm _ _)

/-! ### MS07 — completely positive Motzkin–Straus -/

omit [DecidableEq V] in
lemma inner_sum {ι : Type*} (s : Finset ι) (B : Matrix V V ℝ)
    (C : ι → Matrix V V ℝ) :
    inner B (∑ a ∈ s, C a) = ∑ a ∈ s, inner B (C a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [inner]
  | insert a s ha ih => simp [Finset.sum_insert ha, inner_add_right, ih]

omit [DecidableEq V] in
lemma inner_vecMulVec (B : Matrix V V ℝ) (p : V → ℝ) :
    inner B (vecMulVec p p) = p ⬝ᵥ B *ᵥ p := by
  rw [inner_eq_sum, dot_mulVec_eq_sum_sum]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_)
  simp [vecMulVec_apply]
  ring

omit [DecidableEq V] in
lemma inner_one_vecMulVec (p : V → ℝ) :
    inner (of fun _ _ => (1 : ℝ)) (vecMulVec p p) = (∑ i, p i) ^ 2 := by
  rw [inner_eq_sum]
  simp only [of_apply, vecMulVec_apply]
  simp_rw [one_mul]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, pow_two]

omit [DecidableEq V] in
/-- **MS07.** Completely positive Motzkin–Straus:
`⟨A_G, C⟩ ≤ (1 - 1/ω(G)) ⟨J, C⟩` for `C` completely positive. -/
lemma inner_adjMatrix_le_turanFactor_inner {C : Matrix V V ℝ}
    (hC : IsCompletelyPositive C) :
    inner (G.adjMatrix ℝ) C ≤
      turanFactor G * inner (of fun _ _ => (1 : ℝ)) C := by
  obtain ⟨q, p, hp, rfl⟩ := hC
  rw [inner_sum Finset.univ (G.adjMatrix ℝ) (fun a => vecMulVec (p a) (p a))]
  rw [inner_sum Finset.univ (of fun _ _ => (1 : ℝ)) (fun a => vecMulVec (p a) (p a))]
  have hA : ∀ a, inner (G.adjMatrix ℝ) (vecMulVec (p a) (p a)) =
      p a ⬝ᵥ G.adjMatrix ℝ *ᵥ p a := fun a => inner_vecMulVec _ _
  have hJ : ∀ a, inner (of fun _ _ => (1 : ℝ)) (vecMulVec (p a) (p a)) =
      (∑ i, p a i) ^ 2 := fun a => inner_one_vecMulVec _
  simp_rw [hA, hJ]
  have hle : ∀ a, p a ⬝ᵥ G.adjMatrix ℝ *ᵥ p a ≤
      turanFactor G * (∑ i, p a i) ^ 2 := fun a => motzkinStraus (hp a)
  calc
    ∑ a, p a ⬝ᵥ G.adjMatrix ℝ *ᵥ p a
      ≤ ∑ a, turanFactor G * (∑ i, p a i) ^ 2 := Finset.sum_le_sum fun a _ => hle a
    _ = turanFactor G * ∑ a, (∑ i, p a i) ^ 2 := by rw [← Finset.mul_sum]

end BollobasNikiforov
