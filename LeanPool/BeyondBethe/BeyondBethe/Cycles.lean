/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.RowStability
import LeanPool.BeyondBethe.BeyondBethe.CoreEncoding
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

/-! # Cycles -/

namespace BeyondBethe

/-- The Riemann-sum error `e(a,x)` from paper (27).  Lean's conventions
`a / 0 = 0` and `log 1 = 0` make the displayed formula agree with the paper's
boundary convention `e(a,0)=a`. -/
noncomputable def suffixError (a x : ℝ) : ℝ :=
  a - x * Real.log (1 + a / x)

/-- An antiderivative of `log` with its continuous value at zero. -/
noncomputable def logIntegralPrimitive (x : ℝ) : ℝ :=
  x * Real.log x - x

/-- Suffix score for a list written in the chosen order. -/
noncomputable def listSuffixScore : List ℝ → ℝ
  | [] => 0
  | a :: l => a * Real.log (a + l.sum) + listSuffixScore l

noncomputable def listSuffixErrorSum : List ℝ → ℝ
  | [] => 0
  | a :: l => suffixError a l.sum + listSuffixErrorSum l

theorem listSuffixScore_ofFn
    {n : ℕ} (f : Fin n → ℝ) :
    listSuffixScore (List.ofFn f) =
      ∑ t, f t * Real.log (∑ k, if t ≤ k then f k else 0) := by
  induction n with
  | zero => simp [listSuffixScore]
  | succ n ih =>
      rw [List.ofFn_succ, listSuffixScore, Fin.sum_univ_succ,
        ih (fun k ↦ f k.succ)]
      congr 1
      · congr 2
        rw [List.sum_ofFn, Fin.sum_univ_succ]
        simp
      · apply Finset.sum_congr rfl
        intro i _
        congr 2
        rw [Fin.sum_univ_succ]
        simp

/-- Reindexing bridge between the paper's ordered-list Riemann sum and the
permutation-indexed suffix score used in `rowT`. -/
theorem listSuffixScore_ofFn_eq_ordered_score
    {n : ℕ} (p : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    listSuffixScore (List.ofFn (fun t ↦ p (π t))) =
      ∑ j, p j * Real.log (suffixMass p π j) := by
  calc
    listSuffixScore (List.ofFn (fun t ↦ p (π t))) =
        ∑ t, p (π t) * Real.log
          (∑ k, if t ≤ k then p (π k) else 0) := by
      exact listSuffixScore_ofFn (fun t ↦ p (π t))
    _ = ∑ t, p (π t) * Real.log (suffixMass p π (π t)) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [← orderedSuffixWeight_eq_suffixMass
        (fun _ j ↦ p j) π t]
      rfl
    _ = ∑ j, p j * Real.log (suffixMass p π j) :=
      Equiv.sum_comp π (fun j ↦ p j * Real.log (suffixMass p π j))

/-- One interval in the telescoping Riemann-sum calculation. -/
theorem suffix_step_identity {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) :
    a * Real.log (a + x) =
      logIntegralPrimitive (a + x) - logIntegralPrimitive x + suffixError a x := by
  by_cases hx0 : x = 0
  · subst x
    simp [logIntegralPrimitive, suffixError]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hsum : a + x ≠ 0 := (add_pos_of_nonneg_of_pos ha hxpos).ne'
    have hratio : 1 + a / x = (a + x) / x := by
      field_simp
      ring
    simp only [suffixError, logIntegralPrimitive]
    rw [hratio, Real.log_div hsum hx0]
    ring

/-- The error term is nonnegative, including at the boundary `x=0`. -/
theorem suffixError_nonneg {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) :
    0 ≤ suffixError a x := by
  by_cases hx0 : x = 0
  · subst x
    simpa [suffixError] using ha
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have harg : 0 < 1 + a / x := by positivity
    have hlog := Real.log_le_sub_one_of_pos harg
    have hmul := mul_le_mul_of_nonneg_left hlog hx
    have hsimplify : x * ((1 + a / x) - 1) = a := by
      field_simp
      ring
    rw [hsimplify] at hmul
    rw [suffixError]
    linarith

/-- For fixed nonnegative `a`, the Riemann-sum error is nonincreasing in the
suffix mass, as asserted in paper Lemma 11. -/
theorem suffixError_anti {a x y : ℝ}
    (ha : 0 ≤ a) (hx : 0 ≤ x) (hxy : x ≤ y) :
    suffixError a y ≤ suffixError a x := by
  have hy : 0 ≤ y := hx.trans hxy
  by_cases hy0 : y = 0
  · have hx0 : x = 0 := le_antisymm (hxy.trans_eq hy0) hx
    simp [hx0, hy0]
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  by_cases hx0 : x = 0
  · subst x
    have harg : 1 ≤ 1 + a / y := by
      exact le_add_of_nonneg_right (div_nonneg ha hy)
    have hlog : 0 ≤ Real.log (1 + a / y) := Real.log_nonneg harg
    have hprod : 0 ≤ y * Real.log (1 + a / y) := mul_nonneg hy hlog
    simp only [suffixError, zero_mul, div_zero, add_zero, Real.log_one, sub_zero]
    linarith
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    let lam : ℝ := x / y
    have hlam0 : 0 ≤ lam := div_nonneg hx hy
    have hlam1 : lam ≤ 1 := (div_le_one hypos).2 hxy
    have hfirst : 0 < 1 + a / x := by positivity
    have hone : (1 : ℝ) ∈ Set.Ioi 0 := by norm_num
    have hconc := strictConcaveOn_log_Ioi.concaveOn.2
      (show 1 + a / x ∈ Set.Ioi (0 : ℝ) from hfirst)
      hone hlam0 (sub_nonneg.mpr hlam1) (by ring : lam + (1 - lam) = 1)
    have hcombo :
        lam * (1 + a / x) + (1 - lam) * (1 : ℝ) = 1 + a / y := by
      dsimp [lam]
      field_simp
      ring
    have hlogs :
        lam * Real.log (1 + a / x) ≤ Real.log (1 + a / y) := by
      simpa only [smul_eq_mul, Real.log_one, mul_zero, add_zero, hcombo] using hconc
    have hmul := mul_le_mul_of_nonneg_left hlogs hy
    have hlam_mul : y * (lam * Real.log (1 + a / x)) =
        x * Real.log (1 + a / x) := by
      dsimp [lam]
      field_simp
    rw [hlam_mul] at hmul
    rw [suffixError, suffixError]
    linarith

/-- Finite telescoping form of the suffix Riemann-sum identity, before
normalizing the total mass to one. -/
theorem listSuffixScore_identity (p : List ℝ)
    (hp : ∀ x ∈ p, 0 ≤ x) :
    listSuffixScore p =
      logIntegralPrimitive p.sum + listSuffixErrorSum p := by
  induction p with
  | nil => simp [listSuffixScore, listSuffixErrorSum, logIntegralPrimitive]
  | cons a p ih =>
      have ha : 0 ≤ a := hp a (by simp)
      have hp' : ∀ x ∈ p, 0 ≤ x := by
        intro x hx
        exact hp x (by simp [hx])
      have hsum : 0 ≤ p.sum := List.sum_nonneg hp'
      rw [listSuffixScore, listSuffixErrorSum, ih hp']
      rw [suffix_step_identity ha hsum]
      simp only [List.sum_cons]
      ring

/-- Paper Lemma 11 in ordered-list form. -/
theorem listSuffixScore_eq_neg_one_add_errors (p : List ℝ)
    (hp : ∀ x ∈ p, 0 ≤ x) (hsum : p.sum = 1) :
    listSuffixScore p = -1 + listSuffixErrorSum p := by
  rw [listSuffixScore_identity p hp, hsum]
  simp [logIntegralPrimitive]

theorem listSuffixErrorSum_nonneg (p : List ℝ)
    (hp : ∀ x ∈ p, 0 ≤ x) :
    0 ≤ listSuffixErrorSum p := by
  induction p with
  | nil => simp [listSuffixErrorSum]
  | cons a p ih =>
      have ha : 0 ≤ a := hp a (by simp)
      have hp' : ∀ x ∈ p, 0 ≤ x := by
        intro x hx
        exact hp x (by simp [hx])
      simp only [listSuffixErrorSum]
      exact add_nonneg (suffixError_nonneg ha (List.sum_nonneg hp')) (ih hp')

/-- The coarse consequence `T(p) ≥ -1` used for bad rows, stated for an
arbitrary fixed ordering. -/
theorem listSuffixScore_ge_neg_one (p : List ℝ)
    (hp : ∀ x ∈ p, 0 ≤ x) (hsum : p.sum = 1) :
    -1 ≤ listSuffixScore p := by
  rw [listSuffixScore_eq_neg_one_add_errors p hp hsum]
  linarith [listSuffixErrorSum_nonneg p hp]

theorem fixed_order_suffixScore_ge_neg_one
    {n : ℕ} {p : Fin n → ℝ}
    (hp : IsProbabilityVector p) (π : Equiv.Perm (Fin n)) :
    -1 ≤ ∑ j, p j * Real.log (suffixMass p π j) := by
  rw [← listSuffixScore_ofFn_eq_ordered_score]
  apply listSuffixScore_ge_neg_one
  · intro x hx
    simp only [List.mem_ofFn] at hx
    obtain ⟨t, rfl⟩ := hx
    exact hp.nonnegative (π t)
  · rw [List.sum_ofFn]
    exact (Equiv.sum_comp π p).trans hp.sum_eq_one

/-- The coarse part of paper Lemma 12: every row has suffix score at least
`-1`. -/
theorem rowT_ge_neg_one
    {n : ℕ} {p : Fin n → ℝ} (hp : IsProbabilityVector p) :
    -1 ≤ rowT p := by
  rw [rowT, ← uniformAverage_const
    (α := Equiv.Perm (Fin n)) (-1)]
  unfold uniformAverage
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun π _ ↦ fixed_order_suffixScore_ge_neg_one hp π)
    (Nat.cast_nonneg _)

theorem rowScore_ge_entropy_sub_one
    {n : ℕ} {p : Fin n → ℝ} (hp : IsProbabilityVector p) :
    shannonEntropy p - 1 ≤ rowScore p := by
  rw [rowScore]
  linarith [rowT_ge_neg_one hp]

theorem fourthRoot_pow_four {d : ℝ} (hd : 0 ≤ d) :
    fourthRoot d ^ 4 = d := by
  rw [fourthRoot]
  have hsqrt : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  calc
    Real.sqrt (Real.sqrt d) ^ 4 =
        (Real.sqrt (Real.sqrt d) ^ 2) ^ 2 := by ring
    _ = (Real.sqrt d) ^ 2 := by rw [Real.sq_sqrt hsqrt]
    _ = d := Real.sq_sqrt hd

/-- A row is good when one of the half--half vectors is within the selected
`L¹` threshold. -/
def IsGoodRow {n : ℕ} (eta : ℝ) (p : Fin n → ℝ) : Prop :=
  ∃ a b : Fin n, a ≠ b ∧ halfHalfL1Distance p a b ≤ eta

/-- The rows that fail the preceding structural test. -/
noncomputable def badRows
    {n : ℕ} (eta : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i ↦ ¬ IsGoodRow eta (P i)

/-- Paper (22): a good row has two heavy coordinates and little mass outside
them. -/
theorem goodRow_heavy_coordinates
    {n : ℕ} {eta : ℝ} {p : Fin n → ℝ}
    (hp : IsProbabilityVector p) (hgood : IsGoodRow eta p) :
    ∃ a b : Fin n, a ≠ b ∧
      1 / 2 - eta ≤ p a ∧ 1 / 2 - eta ≤ p b ∧
      1 - p a - p b ≤ eta := by
  obtain ⟨a, b, hab, hdist⟩ := hgood
  have hsum : |p a - 1 / 2| + |p b - 1 / 2| + (1 - p a - p b) ≤ eta := by
    simpa [halfHalfL1Distance_eq hp hab] using hdist
  have htail : 0 ≤ 1 - p a - p b := by
    rw [← sum_away_from_two hp hab]
    exact Finset.sum_nonneg (fun j _ ↦ by
      by_cases h : a ≠ j ∧ b ≠ j <;> simp [h, hp.nonnegative j])
  refine ⟨a, b, hab, ?_, ?_, ?_⟩
  · have habs := neg_le_abs (p a - 1 / 2)
    have hbabs := abs_nonneg (p b - 1 / 2)
    linarith
  · have habs := neg_le_abs (p b - 1 / 2)
    have haabs := abs_nonneg (p a - 1 / 2)
    linarith
  · have haabs := abs_nonneg (p a - 1 / 2)
    have hbabs := abs_nonneg (p b - 1 / 2)
    linarith

/-- Heavy coordinates of one row, equivalently its neighbors in the heavy
bipartite graph. -/
noncomputable def heavyCoordinates
    {n : ℕ} (eta : ℝ) (p : Fin n → ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j ↦ 1 / 2 - eta ≤ p j

/-- Paper's degree-at-most-two assertion for the heavy graph. -/
theorem heavyCoordinates_card_le_two
    {n : ℕ} {eta : ℝ} {p : Fin n → ℝ}
    (hp : IsProbabilityVector p) (heta : eta ≤ 1 / 10) :
    (heavyCoordinates eta p).card ≤ 2 := by
  by_contra h
  have hcardNat : 3 ≤ (heavyCoordinates eta p).card := by omega
  have hcardReal : (3 : ℝ) ≤ (heavyCoordinates eta p).card := by
    exact_mod_cast hcardNat
  have hsumLower :
      ((heavyCoordinates eta p).card : ℝ) * (1 / 2 - eta) ≤
        ∑ j ∈ heavyCoordinates eta p, p j := by
    calc
      ((heavyCoordinates eta p).card : ℝ) * (1 / 2 - eta) =
          ∑ j ∈ heavyCoordinates eta p, (1 / 2 - eta) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ heavyCoordinates eta p, p j := by
        apply Finset.sum_le_sum
        intro j hj
        simpa [heavyCoordinates] using hj
  have hsumUpper : (∑ j ∈ heavyCoordinates eta p, p j) ≤ 1 := by
    rw [← hp.sum_eq_one]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ ↦ hp.nonnegative j)
  have hfactor : (2 / 5 : ℝ) ≤ 1 / 2 - eta := by linarith
  have hmul := mul_le_mul hcardReal hfactor (by norm_num) (by positivity)
  nlinarith

/-- A good row has exactly two heavy coordinates. -/
theorem goodRow_has_exactly_two_heavyCoordinates
    {n : ℕ} {eta : ℝ} {p : Fin n → ℝ}
    (hp : IsProbabilityVector p) (heta : eta ≤ 1 / 10)
    (hgood : IsGoodRow eta p) :
    (heavyCoordinates eta p).card = 2 := by
  obtain ⟨a, b, hab, ha, hb, _⟩ := goodRow_heavy_coordinates hp hgood
  have haMem : a ∈ heavyCoordinates eta p := by
    simpa [heavyCoordinates] using ha
  have hbMem : b ∈ heavyCoordinates eta p := by
    simpa [heavyCoordinates] using hb
  have htwo : ({a, b} : Finset (Fin n)).card ≤
      (heavyCoordinates eta p).card :=
    Finset.card_le_card (by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact haMem
      · exact hbMem)
  have habCard : ({a, b} : Finset (Fin n)).card = 2 := by simp [hab]
  rw [habCard] at htwo
  exact le_antisymm (heavyCoordinates_card_le_two hp heta) htwo

noncomputable def heavyRows
    {n : ℕ} (eta : ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (j : Fin n) : Finset (Fin n) :=
  heavyCoordinates eta (fun i ↦ P i j)

/-- Both sides of the heavy bipartite graph have degree at most two. -/
theorem heavy_graph_degree_bounds
    {n : ℕ} {eta : ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsDoublyStochastic P) (heta : eta ≤ 1 / 10) :
    (∀ i, (heavyCoordinates eta (P i)).card ≤ 2) ∧
      ∀ j, (heavyRows eta P j).card ≤ 2 := by
  constructor
  · intro i
    exact heavyCoordinates_card_le_two (hP.row_probability i) heta
  · intro j
    apply heavyCoordinates_card_le_two
    · exact ⟨fun i ↦ hP.nonnegative i j, hP.col_sum j⟩
    · exact heta

/-- Missing half-edges at row vertices of the heavy graph. -/
abbrev RowStub
    {n : ℕ} (eta : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) :=
  Σ i : Fin n, Fin (2 - (heavyCoordinates eta (P i)).card)

/-- Missing half-edges at column vertices of the heavy graph. -/
abbrev ColumnStub
    {n : ℕ} (eta : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) :=
  Σ j : Fin n, Fin (2 - (heavyRows eta P j).card)

/-- The two sides of the bipartite heavy graph have the same total degree. -/
theorem sum_heavy_degrees
    {n : ℕ} (eta : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, (heavyCoordinates eta (P i)).card) =
      ∑ j, (heavyRows eta P j).card := by
  classical
  simp only [heavyCoordinates, heavyRows, Finset.card_filter]
  rw [Finset.sum_comm]

theorem stub_card_eq
    {n : ℕ} {eta : ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsDoublyStochastic P) (heta : eta ≤ 1 / 10) :
    Fintype.card (RowStub eta P) = Fintype.card (ColumnStub eta P) := by
  have hdegree := sum_heavy_degrees eta P
  have hbounds := heavy_graph_degree_bounds hP heta
  have hrow : (∑ i, ((2 - (heavyCoordinates eta (P i)).card) +
      (heavyCoordinates eta (P i)).card)) = ∑ _i : Fin n, 2 := by
    apply Finset.sum_congr rfl
    intro i _
    exact Nat.sub_add_cancel (hbounds.1 i)
  have hcol : (∑ j, ((2 - (heavyRows eta P j).card) +
      (heavyRows eta P j).card)) = ∑ _j : Fin n, 2 := by
    apply Finset.sum_congr rfl
    intro j _
    exact Nat.sub_add_cancel (hbounds.2 j)
  rw [Finset.sum_add_distrib] at hrow hcol
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hrow hcol
  simp only [RowStub, ColumnStub, Fintype.card_sigma, Fintype.card_fin]
  omega

/-- The formal content of "pair the row stubs arbitrarily with the column
stubs": such a pairing exists because the cardinalities agree.  Each paired
stub is an added edge, with parallel edges allowed. -/
noncomputable def completeHeavyGraphStubEquiv
    {n : ℕ} {eta : ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsDoublyStochastic P) (heta : eta ≤ 1 / 10) :
    RowStub eta P ≃ ColumnStub eta P :=
  Fintype.equivOfCardEq (stub_card_eq hP heta)

/-- The two edge slots at a row, split into existing heavy edges and missing
stubs. -/
noncomputable def heavyRowSlotEquiv
    {n : ℕ} {eta : ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsDoublyStochastic P) (heta : eta ≤ 1 / 10) (i : Fin n) :
    Fin 2 ≃ (heavyCoordinates eta (P i) : Type) ⊕
      Fin (2 - (heavyCoordinates eta (P i)).card) := by
  apply Fintype.equivOfCardEq
  simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_coe]
  simpa [Nat.add_comm] using
    (Nat.sub_add_cancel (heavy_graph_degree_bounds hP heta |>.1 i)).symm

/-- The analogous two-slot decomposition at a column. -/
noncomputable def heavyColumnSlotEquiv
    {n : ℕ} {eta : ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsDoublyStochastic P) (heta : eta ≤ 1 / 10) (j : Fin n) :
    Fin 2 ≃ (heavyRows eta P j : Type) ⊕
      Fin (2 - (heavyRows eta P j).card) := by
  apply Fintype.equivOfCardEq
  simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_coe]
  simpa [Nat.add_comm] using
    (Nat.sub_add_cancel (heavy_graph_degree_bounds hP heta |>.2 j)).symm

/-- Reindex an existing heavy edge by its column rather than its row. -/
noncomputable def heavyEdgeTranspose
    {n : ℕ} (eta : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) :
    (Σ i, (heavyCoordinates eta (P i) : Type)) ≃
      Σ j, (heavyRows eta P j : Type) where
  toFun e := ⟨e.2.1, ⟨e.1, by
    simpa [heavyRows, heavyCoordinates] using e.2.2⟩⟩
  invFun e := ⟨e.2.1, ⟨e.1, by
    simpa [heavyRows, heavyCoordinates] using e.2.2⟩⟩
  left_inv e := by rcases e with ⟨i, j, h⟩; rfl
  right_inv e := by rcases e with ⟨j, i, h⟩; rfl

/-- The stub completion as an explicit bijection from row edge-slots to
column edge-slots.  On existing heavy edges it transposes the endpoints; on
new edges it uses the arbitrary stub pairing. -/
noncomputable def heavyCompletionSlotEquiv
    {n : ℕ} {eta : ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsDoublyStochastic P) (heta : eta ≤ 1 / 10) :
    (Σ _i : Fin n, Fin 2) ≃ Σ _j : Fin n, Fin 2 :=
  (Equiv.sigmaCongrRight fun i ↦ heavyRowSlotEquiv hP heta i) |>.trans
    (Equiv.sigmaSumDistrib
      (fun i ↦ (heavyCoordinates eta (P i) : Type))
      (fun i ↦ Fin (2 - (heavyCoordinates eta (P i)).card))) |>.trans
    (Equiv.sumCongr (heavyEdgeTranspose eta P)
      (completeHeavyGraphStubEquiv hP heta)) |>.trans
    (Equiv.sigmaSumDistrib
      (fun j ↦ (heavyRows eta P j : Type))
      (fun j ↦ Fin (2 - (heavyRows eta P j).card))).symm |>.trans
    (Equiv.sigmaCongrRight fun j ↦ (heavyColumnSlotEquiv hP heta j).symm)

/-- The completed heavy graph, now packaged as a spanning two-regular
bipartite multigraph. -/
noncomputable def completedHeavyMultigraph
    {n : ℕ} {eta : ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsDoublyStochastic P) (heta : eta ≤ 1 / 10) :
    TwoRegularBipartiteMultigraph (Fin n) where
  edge i k := (heavyCompletionSlotEquiv hP heta ⟨i, k⟩).1
  columnDegree j := by
    let E := heavyCompletionSlotEquiv hP heta
    calc
      (∑ i, ∑ k : Fin 2,
          if (E ⟨i, k⟩).1 = j then 1 else 0) =
          ∑ e : Σ _i : Fin n, Fin 2,
            if (E e).1 = j then 1 else 0 := by
        rw [Fintype.sum_sigma]
      _ = ∑ e : Σ _j : Fin n, Fin 2,
            if e.1 = j then 1 else 0 :=
        E.sum_comp (fun e ↦ if e.1 = j then 1 else 0)
      _ = 2 := by
        rw [Fintype.sum_sigma]
        calc
          (∑ x : Fin n, ∑ _y : Fin 2,
              if x = j then 1 else 0) =
              ∑ x : Fin n, if x = j then 2 else 0 := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : x = j <;> simp [hx]
          _ = 2 := by
            rw [Finset.sum_ite_eq' Finset.univ j]
            simp

/-- The stub completion retains every original heavy edge. -/
theorem heavyEdge_mem_completedHeavyMultigraph
    {n : ℕ} {eta : ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsDoublyStochastic P) (heta : eta ≤ 1 / 10)
    {i j : Fin n} (hij : j ∈ heavyCoordinates eta (P i)) :
    ∃ k : Fin 2, (completedHeavyMultigraph hP heta).edge i k = j := by
  let k := (heavyRowSlotEquiv hP heta i).symm (Sum.inl ⟨j, hij⟩)
  refine ⟨k, ?_⟩
  simp [completedHeavyMultigraph, heavyCompletionSlotEquiv, k]
  rfl

/-- The paper's completed heavy graph admits a two-perfect-matching
presentation, and every original heavy edge belongs to one of those
matchings. -/
theorem exists_heavyCompletion_twoMatchings
    {n : ℕ} {eta : ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsDoublyStochastic P) (heta : eta ≤ 1 / 10) :
    ∃ f g : Equiv.Perm (Fin n),
      ∀ i j, j ∈ heavyCoordinates eta (P i) →
        j = f i ∨ j = g i := by
  let K := completedHeavyMultigraph hP heta
  obtain ⟨f, g, _, hcover⟩ := K.exists_twoMatching_decomposition
  refine ⟨f, g, ?_⟩
  intro i j hij
  obtain ⟨k, hk⟩ := heavyEdge_mem_completedHeavyMultigraph hP heta hij
  rcases hcover i k with h | h
  · exact Or.inl (hk.symm.trans h)
  · exact Or.inr (hk.symm.trans h)

/-- Entropic core of paper Lemma 9.  Once the graph argument proves that each
encoding fiber has at most `2^m` assignments, the desired one-bit-per-cycle
bound follows without any further probabilistic input. -/
theorem coreEncoding_of_fiber_bound
    {Ω Y : Type*} [Fintype Ω] [Fintype Y]
    [DecidableEq Ω] [DecidableEq Y]
    {μ : Ω → ℝ} (hμ : IsProbabilityVector μ) (encode : Ω → Y)
    (m : ℕ)
    (hfiber : ∀ y, (Finset.univ.filter fun x ↦ encode x = y).card ≤ 2 ^ m) :
    shannonEntropy μ ≤
      shannonEntropy (pushforwardMass μ encode) + m * Real.log 2 := by
  have h := entropy_le_pushforward_add_log_fiberBound hμ encode (2 ^ m)
    (Nat.one_le_pow m 2 (by norm_num)) hfiber
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h
  simpa [Nat.cast_ofNat] using h

/-- Paper Lemma 9 for a completed two-regular bipartite multigraph presented
as the union of two perfect matchings.  The nontrivial cycles of the
alternating row permutation are exactly the components with at least two
rows; doubled one-row components contribute no bit. -/
theorem twoMatching_coreEncoding
    {α : Type*} [Fintype α] [DecidableEq α]
    {μ : Equiv.Perm α → ℝ} (hμ : IsProbabilityVector μ)
    (f g : Equiv.Perm α) :
    shannonEntropy μ ≤
      shannonEntropy
        (pushforwardMass μ (twoMatchingEncoding f g)) +
      (alternatingRowPerm f g).cycleFactorsFinset.card * Real.log 2 := by
  apply coreEncoding_of_fiber_bound hμ (twoMatchingEncoding f g)
    (alternatingRowPerm f g).cycleFactorsFinset.card
  exact twoMatchingEncoding_fiber_card_le f g

/-- Core-encoding entropy bound for an actual stub completion of the paper's
heavy graph.  The witnesses `f,g` contain every heavy edge, and the cycle
count is therefore the number of nontrivial components of this completed
two-matching presentation. -/
theorem exists_heavyCompletion_coreEncoding
    {n : ℕ} {eta : ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsDoublyStochastic P) (heta : eta ≤ 1 / 10)
    {μ : Equiv.Perm (Fin n) → ℝ} (hμ : IsProbabilityVector μ) :
    ∃ f g : Equiv.Perm (Fin n),
      (∀ i j, j ∈ heavyCoordinates eta (P i) →
        j = f i ∨ j = g i) ∧
      shannonEntropy μ ≤
        shannonEntropy
          (pushforwardMass μ (twoMatchingEncoding f g)) +
        (alternatingRowPerm f g).cycleFactorsFinset.card * Real.log 2 := by
  obtain ⟨f, g, hheavy⟩ := exists_heavyCompletion_twoMatchings hP heta
  exact ⟨f, g, hheavy, twoMatching_coreEncoding hμ f g⟩

/-- Contrapositive of explicit row stability: a bad row pays a definite
fourth-power deficit. -/
theorem bad_row_deficit_lower
    (hrow : AnariRezaeiRowInequality)
    {n : ℕ} (hn : 2 ≤ n) {eta : ℝ} (heta : 0 ≤ eta)
    {p : Fin n → ℝ} (hp : IsStrictProbabilityVector p)
    (hbad : ¬ IsGoodRow eta p) :
    (eta / 3074) ^ 4 < rowDeficit p := by
  obtain ⟨a, b, hab, hdist⟩ := row_stability_explicit hrow hn p hp
  have hetaDist : eta < halfHalfL1Distance p a b := by
    by_contra h
    exact hbad ⟨a, b, hab, le_of_not_gt h⟩
  have hroot : eta < 3074 * fourthRoot (rowDeficit p) :=
    hetaDist.trans_le hdist
  have hd0 := hrow hn p hp.1
  have hbase : eta / 3074 < fourthRoot (rowDeficit p) := by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 3074)]
    simpa [mul_comm] using hroot
  have hpow : (eta / 3074) ^ 4 < fourthRoot (rowDeficit p) ^ 4 :=
    pow_lt_pow_left₀ hbase (div_nonneg heta (by norm_num)) (by omega)
  rw [fourthRoot_pow_four hd0] at hpow
  exact hpow

/-- Summed form of paper (21): bad rows consume the row-deficit part of the
Bethe slack. -/
theorem badRow_count_mul_le_sum_deficit
    (hrow : AnariRezaeiRowInequality)
    {n : ℕ} (hn : 2 ≤ n) {eta : ℝ} (heta : 0 ≤ eta)
    {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ i, IsStrictProbabilityVector (P i)) :
    ((badRows eta P).card : ℝ) * (eta / 3074) ^ 4 ≤
      ∑ i, rowDeficit (P i) := by
  calc
    ((badRows eta P).card : ℝ) * (eta / 3074) ^ 4 =
        ∑ i ∈ badRows eta P, (eta / 3074) ^ 4 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ badRows eta P, rowDeficit (P i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hbad : ¬ IsGoodRow eta (P i) := by
        simpa [badRows] using hi
      exact (bad_row_deficit_lower hrow hn heta (hP i) hbad).le
    _ ≤ ∑ i, rowDeficit (P i) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i _ _
      exact hrow hn (P i) (hP i).1

theorem badRow_count_le_slack
    (hrow : AnariRezaeiRowInequality)
    {n : ℕ} (hn : 2 ≤ n) {eta Delta : ℝ} (heta : 0 < eta)
    {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ i, IsStrictProbabilityVector (P i))
    (hsum : (∑ i, rowDeficit (P i)) ≤ Delta) :
    ((badRows eta P).card : ℝ) ≤ Delta / (eta / 3074) ^ 4 := by
  have hcost := badRow_count_mul_le_sum_deficit hrow hn heta.le hP
  apply (le_div_iff₀ (pow_pos (div_pos heta (by norm_num)) 4)).2
  exact hcost.trans hsum

/-- Scalar assembly in paper Lemma 13.  The two hypotheses are respectively
the entropy-score estimate (29) and the component accounting estimate (30). -/
theorem robust_cycle_information_of_accounting
    {D G components N bad n ω : ℝ}
    (hω : 0 ≤ ω) (hG : G ≤ n)
    (hscore :
      G * (Real.log 2 / 2 - ω) - bad - components * Real.log 2 ≤ D)
    (haccount : N / 6 - bad / 2 ≤ G / 2 - components) :
    Real.log 2 / 6 * N -
        (1 + Real.log 2 / 2) * bad - n * ω ≤ D := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have haccount' := mul_le_mul_of_nonneg_left haccount hlog
  have hωG := mul_le_mul_of_nonneg_right hG hω
  nlinarith

/-- A component contributes one ambiguity bit exactly when it has at least
two rows. -/
def nontrivialComponentCount (k : ℕ) : ℕ :=
  if 2 ≤ k then 1 else 0

/-- Good rows belonging to components with at least three rows. -/
def longComponentGoodRows (k g : ℕ) : ℕ :=
  if 3 ≤ k then g else 0

/-- The component-by-component inequality behind paper (30).  It includes
one-row doubled components explicitly: such a component must contain no good
row and contributes no ambiguity bit. -/
theorem component_accounting
    {C : Type*} [Fintype C]
    (k g b : C → ℕ)
    (hpos : ∀ c, 1 ≤ k c)
    (hpartition : ∀ c, g c + b c = k c)
    (hone : ∀ c, k c = 1 → g c = 0) :
    (∑ c, (g c : ℝ)) / 2 -
        ∑ c, (nontrivialComponentCount (k c) : ℝ) ≥
      (∑ c, (longComponentGoodRows (k c) (g c) : ℝ)) / 6 -
        (∑ c, (b c : ℝ)) / 2 := by
  have hpoint : ∀ c,
      (longComponentGoodRows (k c) (g c) : ℝ) / 6 - (b c : ℝ) / 2 ≤
        (g c : ℝ) / 2 - (nontrivialComponentCount (k c) : ℝ) := by
    intro c
    have hpartR : (g c : ℝ) + b c = k c := by exact_mod_cast hpartition c
    by_cases hk3 : 3 ≤ k c
    · have hk2 : 2 ≤ k c := by omega
      simp only [longComponentGoodRows, if_pos hk3,
        nontrivialComponentCount, if_pos hk2, Nat.cast_one]
      have hk3R : (3 : ℝ) ≤ k c := by exact_mod_cast hk3
      nlinarith
    · have hklt : k c < 3 := by omega
      have hkpos := hpos c
      have hkcases : k c = 1 ∨ k c = 2 := by omega
      rcases hkcases with hk1 | hk2eq
      · have hgzero := hone c hk1
        simp [longComponentGoodRows, nontrivialComponentCount, hk1, hgzero]
        positivity
      · have hk2 : 2 ≤ k c := by omega
        simp only [longComponentGoodRows, if_neg hk3,
          nontrivialComponentCount, if_pos hk2, Nat.cast_zero, zero_div,
          Nat.cast_one]
        have hk2R : (k c : ℝ) = 2 := by exact_mod_cast hk2eq
        nlinarith
  calc
    (∑ c, (longComponentGoodRows (k c) (g c) : ℝ)) / 6 -
          (∑ c, (b c : ℝ)) / 2 =
        ∑ c, ((longComponentGoodRows (k c) (g c) : ℝ) / 6 -
          (b c : ℝ) / 2) := by
            rw [Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_div]
    _ ≤ ∑ c, ((g c : ℝ) / 2 -
          (nontrivialComponentCount (k c) : ℝ)) :=
      Finset.sum_le_sum fun c _ ↦ hpoint c
    _ = (∑ c, (g c : ℝ)) / 2 -
          ∑ c, (nontrivialComponentCount (k c) : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_div]

/-- Clean two-row components contain at least `n - 2b - N` good rows,
hence half as many disjoint clean pairs. -/
theorem clean_pair_count
    {cleanPairs n bad long : ℕ}
    (hrows : n - 2 * bad - long ≤ 2 * cleanPairs) :
    ((n - 2 * bad - long : ℕ) : ℝ) / 2 ≤ cleanPairs := by
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  have hr : ((n - 2 * bad - long : ℕ) : ℝ) ≤ ((2 * cleanPairs : ℕ) : ℝ) := by
    exact_mod_cast hrows
  simpa [mul_comm] using hr

/-- Markov-counting step used after (44): if every failed clean pair costs at
least `a`, total cost `R` permits at most `R/a` failures. -/
theorem costly_pair_count
    {failed : ℕ} {a R : ℝ} (ha : 0 < a)
    (hcost : (failed : ℝ) * a ≤ R) :
    (failed : ℝ) ≤ R / a := by
  exact (le_div_iff₀ ha).2 hcost

end BeyondBethe
