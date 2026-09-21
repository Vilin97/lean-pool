/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.NearCase
import LeanPool.BeyondBethe.BeyondBethe.NumericalWitness
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Greedy Row Matching -/

namespace BeyondBethe

/-!
# Greedy row matchings

The algorithmic certificate does not need an exact maximum-weight matching.
After retaining all row pairs whose directed lower gain exceeds a fixed
threshold, it is enough to construct any maximal matching in that graph.
The elementary cardinality lemma below shows that such a matching has at
least half as many edges as every other matching in the retained graph.
-/

/-- Every successful clean factor already has a large explicit finite-witness
value.  No optimized pair capacity and no input-matrix data enter this fact. -/
theorem successfulCleanCycle_explicitWitnessGain
    {n : ℕ} {κ₀ ξ₀ γ₀ ell ξ τ η : ℝ}
    (hgain : ExplicitPairWitnessGainGuarantee κ₀ ξ₀ γ₀)
    (hell : 1 ≤ ell) (hlogn : Real.log n ≤ ell * Real.log 2)
    (hξ : 0 < ξ) (hξ₀ : ξ ≤ ξ₀) (hτscale : τ = ξ / (4 * ell))
    {P X : Matrix (Fin n) (Fin n) ℝ}
    (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (f g : Equiv.Perm (Fin n))
    (c : cleanCycleFactors η P (alternatingRowPerm f g))
    (hc : c ∈ successfulCleanCycles κ₀ τ η P X f g) :
    γ₀ ≤ explicitPairWitnessLogGain τ X
      (cleanCycleRow c 0) (cleanCycleRow c 1)
      (f (cleanCycleRow c 0)) (g (cleanCycleRow c 0)) := by
  have hcost : fourCoreTransferCost τ X
      (cleanCycleRow c 0) (cleanCycleRow c 1)
      (f (cleanCycleRow c 0)) (g (cleanCycleRow c 0)) ≤ κ₀ := by
    have hnot : ¬ κ₀ < fourCoreTransferCost τ X
        (cleanCycleRow c 0) (cleanCycleRow c 1)
        (f (cleanCycleRow c 0)) (g (cleanCycleRow c 0)) := by
      simpa [successfulCleanCycles, failedCleanCycles] using hc
    exact le_of_not_gt hnot
  have hcols := cleanCycle_core_columns c
  exact hgain hell hlogn hξ hξ₀ hτscale hX hXint
    hcols.1 hcols.2.1 hcost

/-- `M` is a maximal matching relative to the available row pairs `E`.
The last field is the useful certificate form of maximality: every available
edge meets an edge already selected by `M`. -/
structure IsMaximalRowMatching {n : ℕ}
    (E M : Finset (RowPair n)) : Prop where
  subset : M ⊆ E
  matching : IsRowMatching M
  covered : ∀ q ∈ E, ∃ r ∈ M, ¬Disjoint q.1 r.1

/-- The vertices covered by a row matching. -/
def rowMatchingVertices {n : ℕ} (M : Finset (RowPair n)) : Finset (Fin n) :=
  M.biUnion fun q ↦ q.1

theorem rowMatchingVertices_card_le_two_mul {n : ℕ}
    (M : Finset (RowPair n)) :
    (rowMatchingVertices M).card ≤ 2 * M.card := by
  rw [show 2 * M.card = M.card * 2 by omega]
  exact Finset.card_biUnion_le_card_mul M (fun q ↦ q.1) 2
    (fun q _ ↦ q.2.le)

/-- A maximal matching is a factor-two approximation to maximum cardinality.
This proof uses only the fact that the competing edges are disjoint: choose,
for each competing edge, a covered endpoint.  Those choices are injective,
and the selected matching covers at most two vertices per edge. -/
theorem card_le_two_mul_of_maximalRowMatching {n : ℕ}
    {E M S : Finset (RowPair n)}
    (hM : IsMaximalRowMatching E M)
    (hS : IsRowMatching S) (hSE : S ⊆ E) :
    S.card ≤ 2 * M.card := by
  classical
  let V := rowMatchingVertices M
  have hinter : ∀ q : S, ∃ v : Fin n, v ∈ q.1.1 ∧ v ∈ V := by
    intro q
    obtain ⟨r, hrM, hqr⟩ := hM.covered q.1 (hSE q.2)
    obtain ⟨v, hvq, hvr⟩ := Finset.not_disjoint_iff.mp hqr
    refine ⟨v, hvq, ?_⟩
    exact Finset.mem_biUnion.mpr ⟨r, hrM, hvr⟩
  let chosen : S → Fin n := fun q ↦ (hinter q).choose
  have hchosen_mem_edge (q : S) : chosen q ∈ q.1.1 :=
    (hinter q).choose_spec.1
  have hchosen_mem_V (q : S) : chosen q ∈ V :=
    (hinter q).choose_spec.2
  let intoV : S → V := fun q ↦ ⟨chosen q, hchosen_mem_V q⟩
  have hinjective : Function.Injective intoV := by
    intro q q' heq
    apply Subtype.ext
    by_contra hqq'
    have hdisj : Disjoint q.1.1 q'.1.1 :=
      hS q.2 q'.2 hqq'
    have hval : chosen q = chosen q' := congrArg Subtype.val heq
    exact (Finset.disjoint_left.mp hdisj)
      (hchosen_mem_edge q) (hval ▸ hchosen_mem_edge q')
  calc
    S.card ≤ V.card := Finset.card_le_card_of_injective hinjective
    _ ≤ 2 * M.card := rowMatchingVertices_card_le_two_mul M

/-- Greedily scan a list of available row pairs.  An edge is inserted exactly
when it is disjoint from all edges selected later in the list.  (Thus the
recursion fixes a deterministic reverse-list scan.) -/
def greedyRowMatchingList {n : ℕ} :
    List (RowPair n) → Finset (RowPair n)
  | [] => ∅
  | q :: qs =>
      let M := greedyRowMatchingList qs
      if ∀ r ∈ M, Disjoint q.1 r.1 then insert q M else M

theorem greedyRowMatchingList_isMaximal {n : ℕ}
    (edges : List (RowPair n)) :
    IsMaximalRowMatching edges.toFinset (greedyRowMatchingList edges) := by
  induction edges with
  | nil =>
      refine ⟨by simp [greedyRowMatchingList], by simp [greedyRowMatchingList,
        IsRowMatching], ?_⟩
      simp
  | cons q qs ih =>
      rw [greedyRowMatchingList]
      split_ifs with hdisj
      · refine ⟨?_, ?_, ?_⟩
        · intro r hr
          simp only [List.toFinset_cons, Finset.mem_insert] at hr ⊢
          exact hr.elim Or.inl (fun hrM ↦ Or.inr (ih.subset hrM))
        · rw [IsRowMatching, Finset.coe_insert]
          exact ih.matching.insert fun r hr _ ↦ hdisj r hr
        · intro e he
          simp only [List.toFinset_cons, Finset.mem_insert] at he
          rcases he with heq | he
          · have hecard := e.2
            have hepos : 0 < e.1.card := by omega
            obtain ⟨v, hv⟩ := Finset.card_pos.mp hepos
            exact ⟨e, by simpa [heq],
              Finset.not_disjoint_iff.mpr ⟨v, hv, hv⟩⟩
          · obtain ⟨r, hr, her⟩ := ih.covered e he
            exact ⟨r, Finset.mem_insert_of_mem hr, her⟩
      · refine ⟨?_, ih.matching, ?_⟩
        · exact ih.subset.trans (by simp)
        · intro e he
          simp only [List.toFinset_cons, Finset.mem_insert] at he
          rcases he with heq | he
          · subst e
            push Not at hdisj
            exact hdisj
          · exact ih.covered e he

/-- Gain form of the cardinality lemma.  If every selected edge has gain at
least `a`, a maximal matching collects at least one half of `a` times the
cardinality of any competing matching in the threshold graph. -/
theorem half_card_mul_le_sum_of_maximalRowMatching {n : ℕ}
    {E M S : Finset (RowPair n)} (w : RowPair n → ℝ) {a : ℝ}
    (ha : 0 ≤ a) (hM : IsMaximalRowMatching E M)
    (hS : IsRowMatching S) (hSE : S ⊆ E)
    (hweight : ∀ q ∈ M, a ≤ w q) :
    ((S.card : ℝ) * a) / 2 ≤ ∑ q ∈ M, w q := by
  have hcard : (S.card : ℝ) ≤ 2 * M.card := by
    exact_mod_cast card_le_two_mul_of_maximalRowMatching hM hS hSE
  have hcardGain : ((S.card : ℝ) * a) / 2 ≤ (M.card : ℝ) * a := by
    have := mul_le_mul_of_nonneg_right hcard ha
    norm_num at this ⊢
    linarith
  refine hcardGain.trans ?_
  calc
    (M.card : ℝ) * a = ∑ _q ∈ M, a := by simp
    _ ≤ ∑ q ∈ M, w q := Finset.sum_le_sum hweight

/-- The unordered row pair associated with two rows in increasing order. -/
def rowPairOfLT {n : ℕ} (i j : Fin n) (hij : i < j) : RowPair n :=
  ⟨{i, j}, by simp [ne_of_lt hij]⟩

@[simp] theorem rowPairRow_rowPairOfLT_zero {n : ℕ}
    (i j : Fin n) (hij : i < j) :
    rowPairRow (rowPairOfLT i j hij) 0 = i := by
  let q := rowPairOfLT i j hij
  have hzero := rowPairRow_mem q 0
  have hone := rowPairRow_mem q 1
  have hlt : rowPairRow q 0 < rowPairRow q 1 := by
    exact (q.1.orderIsoOfFin q.2).lt_iff_lt.mpr (by decide)
  dsimp only [q] at hlt
  change rowPairRow (rowPairOfLT i j hij) 0 ∈ ({i, j} : Finset (Fin n)) at hzero
  change rowPairRow (rowPairOfLT i j hij) 1 ∈ ({i, j} : Finset (Fin n)) at hone
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzero hone
  rcases hzero with hzero | hzero
  · exact hzero
  · rcases hone with hone | hone
    · rw [hzero, hone] at hlt
      exact False.elim ((not_lt_of_ge hij.le) hlt)
    · rw [hzero, hone] at hlt
      exact False.elim ((lt_irrefl j) hlt)

@[simp] theorem rowPairRow_rowPairOfLT_one {n : ℕ}
    (i j : Fin n) (hij : i < j) :
    rowPairRow (rowPairOfLT i j hij) 1 = j := by
  let q := rowPairOfLT i j hij
  have hzero := rowPairRow_mem q 0
  have hone := rowPairRow_mem q 1
  have hlt : rowPairRow q 0 < rowPairRow q 1 := by
    exact (q.1.orderIsoOfFin q.2).lt_iff_lt.mpr (by decide)
  dsimp only [q] at hlt
  change rowPairRow (rowPairOfLT i j hij) 0 ∈ ({i, j} : Finset (Fin n)) at hzero
  change rowPairRow (rowPairOfLT i j hij) 1 ∈ ({i, j} : Finset (Fin n)) at hone
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzero hone
  rcases hone with hone | hone
  · rcases hzero with hzero | hzero
    · rw [hzero, hone] at hlt
      exact False.elim ((lt_irrefl i) hlt)
    · rw [hzero, hone] at hlt
      exact False.elim ((not_lt_of_ge hij.le) hlt)
  · exact hone

/-- Explicit lexicographic enumeration of every unordered row pair.  Unlike
`Finset.toList`, this definition carries no classical choice and is executable. -/
def allRowPairsList (n : ℕ) : List (RowPair n) :=
  (List.finRange n).flatMap fun i ↦
    (List.finRange n).filterMap fun j ↦
      if hij : i < j then some (rowPairOfLT i j hij) else none

theorem rowPairOfLT_mem_allRowPairsList {n : ℕ}
    (i j : Fin n) (hij : i < j) :
    rowPairOfLT i j hij ∈ allRowPairsList n := by
  rw [allRowPairsList, List.mem_flatMap]
  refine ⟨i, List.mem_finRange i, ?_⟩
  rw [List.mem_filterMap]
  refine ⟨j, List.mem_finRange j, ?_⟩
  simp [hij]

theorem mem_allRowPairsList {n : ℕ} (q : RowPair n) :
    q ∈ allRowPairsList n := by
  obtain ⟨i, j, hij, hq⟩ := Finset.card_eq_two.mp q.2
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hmem := rowPairOfLT_mem_allRowPairsList i j hlt
    have heq : q = rowPairOfLT i j hlt := by
      apply Subtype.ext
      simpa [rowPairOfLT] using hq
    rwa [heq]
  · have hmem := rowPairOfLT_mem_allRowPairsList j i hgt
    have heq : q = rowPairOfLT j i hgt := by
      apply Subtype.ext
      simpa [rowPairOfLT, Finset.pair_comm] using hq
    rwa [heq]

/-- Retain exactly the row pairs whose rational certified weight reaches the
given rational threshold. -/
def thresholdRowPairsList {n : ℕ} (w : RowPair n → ℚ) (a : ℚ) :
    List (RowPair n) :=
  (allRowPairsList n).filter fun q ↦ decide (a ≤ w q)

theorem mem_thresholdRowPairsList_iff {n : ℕ}
    (w : RowPair n → ℚ) (a : ℚ) (q : RowPair n) :
    q ∈ thresholdRowPairsList w a ↔ a ≤ w q := by
  simp [thresholdRowPairsList, mem_allRowPairsList]

/-- Executable threshold-and-greedy row matching. -/
def greedyThresholdRowMatching {n : ℕ}
    (w : RowPair n → ℚ) (a : ℚ) : Finset (RowPair n) :=
  greedyRowMatchingList (thresholdRowPairsList w a)

theorem greedyThresholdRowMatching_isMaximal {n : ℕ}
    (w : RowPair n → ℚ) (a : ℚ) :
    IsMaximalRowMatching
      (thresholdRowPairsList w a).toFinset
      (greedyThresholdRowMatching w a) := by
  exact greedyRowMatchingList_isMaximal _

theorem greedyThresholdRowMatching_weight {n : ℕ}
    (w : RowPair n → ℚ) {a : ℚ}
    {S : Finset (RowPair n)} (ha : 0 ≤ a)
    (hS : IsRowMatching S) (hqualifies : ∀ q ∈ S, a ≤ w q) :
    ((S.card : ℝ) * (a : ℝ)) / 2 ≤
      ∑ q ∈ greedyThresholdRowMatching w a, (w q : ℝ) := by
  let E := (thresholdRowPairsList w a).toFinset
  let M := greedyThresholdRowMatching w a
  have hmax : IsMaximalRowMatching E M :=
    greedyThresholdRowMatching_isMaximal w a
  have hSE : S ⊆ E := by
    intro q hq
    simp only [E, List.mem_toFinset, mem_thresholdRowPairsList_iff]
    exact hqualifies q hq
  have hweight : ∀ q ∈ M, (a : ℝ) ≤ (w q : ℝ) := by
    intro q hq
    have hqE := hmax.subset hq
    have hqrat : a ≤ w q := by
      simpa only [E, List.mem_toFinset, mem_thresholdRowPairsList_iff] using hqE
    exact_mod_cast hqrat
  exact half_card_mul_le_sum_of_maximalRowMatching
    (fun q ↦ (w q : ℝ)) (by exact_mod_cast ha) hmax hS hSE hweight

/-- Rational gain collected by the executable threshold matching. -/
def greedyCertifiedMatchingGain {n : ℕ}
    (w : RowPair n → ℚ) (a : ℚ) : ℚ :=
  ∑ q ∈ greedyThresholdRowMatching w a, w q

theorem cast_greedyCertifiedMatchingGain {n : ℕ}
    (w : RowPair n → ℚ) (a : ℚ) :
    (greedyCertifiedMatchingGain w a : ℝ) =
      ∑ q ∈ greedyThresholdRowMatching w a, (w q : ℝ) := by
  simp [greedyCertifiedMatchingGain]

theorem greedyCertifiedMatchingGain_structural_lower {n : ℕ}
    (w : RowPair n → ℚ) {a : ℚ}
    {S : Finset (RowPair n)} (ha : 0 ≤ a)
    (hS : IsRowMatching S) (hqualifies : ∀ q ∈ S, a ≤ w q) :
    ((S.card : ℝ) * (a : ℝ)) / 2 ≤
      (greedyCertifiedMatchingGain w a : ℝ) := by
  rw [cast_greedyCertifiedMatchingGain]
  exact greedyThresholdRowMatching_weight w ha hS hqualifies

/-- The threshold-greedy routine captures half of the certified gain carried
by the disjoint successful clean pairs.  This is the exact replacement for
the maximum-weight-matching domination used in the nonalgorithmic proof. -/
theorem greedyCertifiedMatchingGain_ge_successfulCleanCycles
    {n : ℕ} {κ τ η : ℝ} {P X : Matrix (Fin n) (Fin n) ℝ}
    (f g : Equiv.Perm (Fin n)) (w : RowPair n → ℚ) {a : ℚ}
    (ha : 0 ≤ a)
    (hqualifies : ∀ c ∈ successfulCleanCycles κ τ η P X f g,
      a ≤ w (cleanCycleRowPair c)) :
    (((successfulCleanCycles κ τ η P X f g).card : ℝ) * (a : ℝ)) / 2 ≤
      (greedyCertifiedMatchingGain w a : ℝ) := by
  let S := successfulRowPairs κ τ η P X f g
  have hS : IsRowMatching S := successfulRowPairs_isRowMatching κ τ η P X f g
  have hSq : ∀ q ∈ S, a ≤ w q := by
    intro q hq
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hq
    exact hqualifies c hc
  have hcard : S.card = (successfulCleanCycles κ τ η P X f g).card := by
    exact Finset.card_image_iff.mpr cleanCycleRowPair_injective.injOn
  have h := greedyCertifiedMatchingGain_structural_lower w ha hS hSq
  rwa [hcard] at h

/-- Every directed lower estimate selected by the greedy routine remains a
valid permanent certificate.  Exact maximum-weight matching is unnecessary:
the paired certificate applies to the selected matching itself, and
monotonicity of `exp` permits replacing its true gain by any rational lower
sum. -/
theorem exp_betheObjective_add_greedyCertifiedMatchingGain_le_permanent
    {n : ℕ}
    (stableCoefficient : AnariOveisGharanStableCoefficient.{0})
    {A X : Matrix (Fin n) (Fin n) ℝ}
    (w : RowPair n → ℚ) {a : ℚ} (ha : 0 < a)
    (hlower : ∀ q ∈ greedyThresholdRowMatching w a, (w q : ℝ) ≤
      Real.log (pairGain A X (rowPairRow q 0) (rowPairRow q 1)))
    (hcard : 2 ≤ n) (hA : Matrix.Positive A)
    (hX : IsDoublyStochastic X) (hXpos : ∀ i j, 0 < X i j) :
    Real.exp (betheObjective A X +
        (greedyCertifiedMatchingGain w a : ℝ)) ≤
      Matrix.permanent A := by
  let M := greedyThresholdRowMatching w a
  have hmax : IsMaximalRowMatching
      (thresholdRowPairsList w a).toFinset M :=
    greedyThresholdRowMatching_isMaximal w a
  have hselected : ∀ q ∈ M, a ≤ w q := by
    intro q hq
    have hqE := hmax.subset hq
    simpa only [List.mem_toFinset, mem_thresholdRowPairsList_iff] using hqE
  have hpositive : ∀ q ∈ M, 0 < Real.log
      (pairGain A X (rowPairRow q 0) (rowPairRow q 1)) := by
    intro q hq
    have hcast : (a : ℝ) ≤ (w q : ℝ) := by
      exact_mod_cast hselected q hq
    have hareal : 0 < (a : ℝ) := by exact_mod_cast ha
    exact hareal.trans_le (hcast.trans (hlower q hq))
  have hsum : (greedyCertifiedMatchingGain w a : ℝ) ≤
      rowMatchingWeight A X M := by
    rw [cast_greedyCertifiedMatchingGain, rowMatchingWeight]
    exact Finset.sum_le_sum fun q hq ↦ by
      rw [rowPairWeight, max_eq_right (le_of_lt (hpositive q hq))]
      exact hlower q hq
  have hexp : Real.exp (betheObjective A X +
      (greedyCertifiedMatchingGain w a : ℝ)) ≤
      Real.exp (betheObjective A X + rowMatchingWeight A X M) := by
    exact Real.exp_le_exp.mpr (by linarith)
  exact hexp.trans
    (exp_betheObjective_add_rowMatchingWeight_le_permanent
      stableCoefficient hmax.matching hcard hA hX hXpos hpositive)

end BeyondBethe
