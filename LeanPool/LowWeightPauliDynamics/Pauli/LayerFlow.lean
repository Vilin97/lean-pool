/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/
import LeanPool.LowWeightPauliDynamics.Pauli.Flow
import LeanPool.LowWeightPauliDynamics.Pauli.LayerWitness
import LeanPool.LowWeightPauliDynamics.Schur

/-!
# The `j`-jump decomposition of a Pauli layer and the layer-inflow bound

This file formalizes `apd:thm:layer_inflow`. For a finite ordered list `L` of Pauli rotations
`(G, θ)`, the coefficient action `layerAct L` of the matrix conjugation `layerConj L` is expanded
by the number `j` of sine branches taken, `layerAct L = ∑ j, layerJump L j`. If the generators
have pairwise disjoint supports and weight at most `k_h` (`IsLayer`), then the block
`layerInflowMatrix L w j` of the exactly-`j` component that maps Pauli weights `≤ w` to Pauli
weights `> w` has `ℓ²` operator norm at most

  `C(w + j (k_h - 1), j) σ^j ≤ ((w + j (k_h - 1)) σ)^j / j!`   (`apd:eq:layer_inflow`),

where `σ` is any bound on `|sin θ|` over the layer. The norm bound is the Schur test
`Lean4LPD.l2_opNorm_le_of_row_col_bound` applied to absolute row and column sums.

## Main definitions

* `stayAct`, `jumpAct`: the cosine/identity branch and the sine branch of a single rotation;
  they add up to `rotAct` (`rotAct_eq_stay_add_jump`).
* `layerAct`, `layerConj`: a finite ordered layer as a map on coefficient vectors and as matrix
  conjugation, related by `coeffVec_layerConj`.
* `layerJump L j`: the component of `layerAct L` with exactly `j` sine branches.
* `antiLayer L p`, `layerAntiCount L p`: the generators of `L` that anticommute with the Pauli
  `p`, as a finset and as a count with list multiplicity.
* `layerSigma L`: the largest `|sin θ|` in the layer.
* `layerJumpMatrix L j`, `layerInflowMatrix L w j`: the matrix of `layerJump L j` and its
  high-from-low block `A^{(j)}`.

## Main results

* `layerAct_eq_sum_layerJump`: the finite expansion of a layer by number of sine branches.
* `layerJump_apply_eq_zero_of_weight_lt`: `j` sine branches raise the Pauli weight by at most
  `j (k_h - 1)`.
* `card_antiLayer_le_weight`: in a disjoint-support layer at most `|p|` generators anticommute
  with `p`.
* `row_sum_norm_layerJumpMatrix_le`, `col_sum_norm_layerJumpMatrix_le`: binomial bounds on the
  absolute row and column sums of `layerJumpMatrix L j`.
* `norm_layerInflowMatrix_le`, `norm_layerInflowMatrix_le_factorial`,
  `norm_layerInflowMatrix_le_layerSigma`: the layer-inflow bound in binomial form, in factorial
  form, and with `σ = layerSigma L`.
* `restr_layerAct_low_eq_sum_inflow`, `norm_restr_layerAct_le_sum_inflow`: on low-weight inputs
  the high-weight part of the layer output is `∑ j, A^{(j)}`, and the high-weight norm after a
  layer is at most the high-weight norm before it plus the norms of the inflows.
* `layerInflowMatrix_clm_restr`, `norm_layerInflowMatrix_clm_le_restr`: a `j`-jump inflow into
  weights above `w` only sees input weights above `w'` whenever `w' + j (k_h - 1) ≤ w`, the form
  needed for `apd:rmk:multijump`.

## Implementation notes

The layer action is built from the conjugation action `rotAct` of `Flow.lean`, so every statement
is about the Pauli coefficients of `layerConj L O`. The expansion and the weight bound hold for
arbitrary ordered lists. The row and column estimates need only pairwise commutation of the
generators; disjointness of supports enters when the number of anticommuting generators is
bounded by the Pauli weight. The row and column sums are bounded by induction on the list, using
Pascal's rule and the fact that a rotation whose generator commutes with `G` preserves the
commutation class with `G`. Distinct branch choices are not claimed to give distinct nonzero
matrix entries: cancellations are allowed, and only upper bounds are asserted.

The small parameter is a bound `σ` on the absolute sines, so the angles are arbitrary real
numbers. This is more general than the paper's statement: neither positivity of the sines nor
monotonicity of sine on an interval of angles is used.

No `MultiLadder` is constructed here; the passage from the finite inflow sum to the recurrence
with the infinite entry factor is in `LayerLadder.lean`.
-/

namespace Lean4LPD.PauliString

open Finset Matrix
open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

/-- The unchanged branch of a rotation: identity on commuting coordinates and cosine on
anticommuting coordinates (`apd:thm:layer_inflow`). -/
noncomputable def stayAct (G : PauliString n) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) : EuclideanSpace ℂ (PauliIndex n) :=
  WithLp.toLp 2 fun p =>
    if sympForm G (herm p) = 0 then y.ofLp p else (Real.cos θ : ℂ) * y.ofLp p

/-- The sine branch, with the coefficient-side partner sign fixed by `coeffVec_conj`.
Supporting definition for `apd:thm:layer_inflow`. -/
noncomputable def jumpAct (G : PauliString n) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) : EuclideanSpace ℂ (PauliIndex n) :=
  WithLp.toLp 2 fun p =>
    if sympForm G (herm p) = 0 then 0
    else -(Real.sin θ : ℂ) * (partnerSign G p * y.ofLp (partner G p))

/-- Coefficient formula for the unchanged branch; supporting lemma for
`apd:thm:layer_inflow`. -/
@[simp] theorem stayAct_apply (G : PauliString n) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) (p : PauliIndex n) :
    (stayAct G θ y).ofLp p =
      if sympForm G (herm p) = 0 then y.ofLp p else (Real.cos θ : ℂ) * y.ofLp p := rfl

/-- Coefficient formula for the sine branch; supporting lemma for
`apd:thm:layer_inflow`. -/
@[simp] theorem jumpAct_apply (G : PauliString n) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) (p : PauliIndex n) :
    (jumpAct G θ y).ofLp p =
      if sympForm G (herm p) = 0 then 0
      else -(Real.sin θ : ℂ) * (partnerSign G p * y.ofLp (partner G p)) := rfl

/-- The two branches add up to the rotation action `rotAct`, which `coeffVec_conj` identifies
with conjugation by the rotation. Supporting lemma for `apd:thm:layer_inflow`. -/
theorem rotAct_eq_stay_add_jump (G : PauliString n) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    rotAct G θ y = stayAct G θ y + jumpAct G θ y := by
  ext p
  simp only [rotAct_apply, stayAct_apply, jumpAct_apply, WithLp.ofLp_add, Pi.add_apply]
  split <;> ring

/-- Additivity of the unchanged branch, supporting finite expansion in
`apd:thm:layer_inflow`. -/
theorem stayAct_add (G : PauliString n) (θ : ℝ)
    (y z : EuclideanSpace ℂ (PauliIndex n)) :
    stayAct G θ (y + z) = stayAct G θ y + stayAct G θ z := by
  ext p
  simp only [stayAct_apply, WithLp.ofLp_add, Pi.add_apply]
  split <;> ring

/-- Additivity of the sine branch, supporting finite expansion in
`apd:thm:layer_inflow`. -/
theorem jumpAct_add (G : PauliString n) (θ : ℝ)
    (y z : EuclideanSpace ℂ (PauliIndex n)) :
    jumpAct G θ (y + z) = jumpAct G θ y + jumpAct G θ z := by
  ext p
  simp only [jumpAct_apply, WithLp.ofLp_add, Pi.add_apply]
  split <;> ring

/-- Zero is preserved by the unchanged branch; supporting lemma for
`apd:thm:layer_inflow`. -/
@[simp] theorem stayAct_zero (G : PauliString n) (θ : ℝ) : stayAct G θ 0 = 0 := by
  ext p
  simp [stayAct_apply]

/-- Zero is preserved by the sine branch; supporting lemma for
`apd:thm:layer_inflow`. -/
@[simp] theorem jumpAct_zero (G : PauliString n) (θ : ℝ) : jumpAct G θ 0 = 0 := by
  ext p
  simp [jumpAct_apply]

/-- Coefficient action of a finite ordered list of rotations, the composition of their `rotAct`
(the head of the list acts last). For disjoint supports this is the layer of
`apd:thm:layer_inflow`. -/
noncomputable def layerAct : List (PauliString n × ℝ) →
    EuclideanSpace ℂ (PauliIndex n) → EuclideanSpace ℂ (PauliIndex n)
  | [], y => y
  | (G, θ) :: L, y => rotAct G θ (layerAct L y)

/-- Matrix conjugation by the rotations of a list, in the same order as `layerAct`. It is
defined from the rotation matrices `rot`, independently of the branch expansion
(`apd:thm:layer_inflow`). -/
noncomputable def layerConj : List (PauliString n × ℝ) →
    Matrix (Bits n) (Bits n) ℂ → Matrix (Bits n) (Bits n) ℂ
  | [], O => O
  | (G, θ) :: L, O => rot (toMatrix G) θ * layerConj L O * rot (toMatrix G) (-θ)

/-- For Hermitian generators, `layerAct L` is the action of the matrix conjugation `layerConj L`
on coefficient vectors. Supporting lemma for `apd:thm:layer_inflow`. -/
theorem coeffVec_layerConj (L : List (PauliString n × ℝ))
    (hL : ∀ g ∈ L, IsSelfAdjoint g.1) (O : Matrix (Bits n) (Bits n) ℂ) :
    coeffVec (layerConj L O) = layerAct L (coeffVec O) := by
  induction L with
  | nil => rfl
  | cons g L ih =>
    rcases g with ⟨G, θ⟩
    rw [layerConj, layerAct, coeffVec_conj (hL (G, θ) (by simp)),
      ih (fun g hg => hL g (by simp [hg]))]

/-- A finite layer of Hermitian generators preserves the coefficient `ℓ²` norm. This gives the
contraction of the diagonal (high-to-high) block; the off-diagonal block is handled by the Schur
bound of `apd:thm:layer_inflow` below. -/
theorem norm_layerAct (L : List (PauliString n × ℝ))
    (hL : ∀ g ∈ L, IsSelfAdjoint g.1) (y : EuclideanSpace ℂ (PauliIndex n)) :
    ‖layerAct L y‖ = ‖y‖ := by
  induction L with
  | nil => rfl
  | cons g L ih =>
    rcases g with ⟨G, θ⟩
    rw [layerAct, norm_rotAct (hL (G, θ) (by simp)),
      ih (fun g hg => hL g (by simp [hg]))]

/-- The component of `layerAct L` in which exactly `j` rotations take their sine branch, defined
by recursion on the list: the head rotation either stays, or takes its sine branch and leaves
`j - 1` sine branches to the tail. Rotations that stay keep their cosine or identity factor.
Supporting definition for `A^{(j)}` in `apd:thm:layer_inflow`. -/
noncomputable def layerJump : List (PauliString n × ℝ) → ℕ →
    EuclideanSpace ℂ (PauliIndex n) → EuclideanSpace ℂ (PauliIndex n)
  | [], 0, y => y
  | [], _ + 1, _ => 0
  | (G, θ) :: L, 0, y => stayAct G θ (layerJump L 0 y)
  | (G, θ) :: L, j + 1, y =>
      stayAct G θ (layerJump L (j + 1) y) + jumpAct G θ (layerJump L j y)

/-- A layer cannot take more sine branches than it has rotations.
Supporting lemma for the finite form of `apd:thm:layer_inflow`. -/
theorem layerJump_eq_zero_of_length_lt (L : List (PauliString n × ℝ))
    (j : ℕ) (hj : L.length < j) (y : EuclideanSpace ℂ (PauliIndex n)) :
    layerJump L j y = 0 := by
  induction L generalizing j with
  | nil => cases j <;> simp_all [layerJump]
  | cons g L ih =>
    rcases g with ⟨G, θ⟩
    cases j with
    | zero => simp at hj
    | succ j =>
      simp only [List.length_cons] at hj
      rw [layerJump, ih (j + 1) (by omega), ih j (by omega)]
      simp

/-- The unchanged branch distributes over finite coefficient sums; supporting lemma for
`apd:thm:layer_inflow`. -/
theorem stayAct_sum {ι : Type*} (s : Finset ι) (G : PauliString n) (θ : ℝ)
    (f : ι → EuclideanSpace ℂ (PauliIndex n)) :
    stayAct G θ (∑ i ∈ s, f i) = ∑ i ∈ s, stayAct G θ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, stayAct_add, ih]

/-- The sine branch distributes over finite coefficient sums; supporting lemma for
`apd:thm:layer_inflow`. -/
theorem jumpAct_sum {ι : Type*} (s : Finset ι) (G : PauliString n) (θ : ℝ)
    (f : ι → EuclideanSpace ℂ (PauliIndex n)) :
    jumpAct G θ (∑ i ∈ s, f i) = ∑ i ∈ s, jumpAct G θ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, jumpAct_add, ih]

/-- **Expansion of a layer by number of sine branches.** `layerAct L` is the finite sum of its
exactly-`j` components, `0 ≤ j ≤ L.length`; this is the expansion used in
`apd:thm:layer_inflow`. It is an identity for arbitrary ordered lists of rotations: disjointness
and commutation are needed only for the binomial counting estimates below. -/
theorem layerAct_eq_sum_layerJump (L : List (PauliString n × ℝ))
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    layerAct L y = ∑ j ∈ range (L.length + 1), layerJump L j y := by
  induction L with
  | nil => simp [layerAct, layerJump]
  | cons g L ih =>
    rcases g with ⟨G, θ⟩
    have hshift : (∑ j ∈ range (L.length + 1), layerJump L (j + 1) y)
        + layerJump L 0 y = layerAct L y := by
      rw [← Finset.sum_range_succ' (fun j => layerJump L j y), Finset.sum_range_succ,
        layerJump_eq_zero_of_length_lt L (L.length + 1) (by omega), add_zero, ← ih]
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [layerJump, Finset.sum_add_distrib]
    rw [← stayAct_sum, ← jumpAct_sum, ← ih, layerAct, rotAct_eq_stay_add_jump]
    calc stayAct G θ (layerAct L y) + jumpAct G θ (layerAct L y)
        = stayAct G θ ((∑ j ∈ range (L.length + 1), layerJump L (j + 1) y)
            + layerJump L 0 y) + jumpAct G θ (layerAct L y) := by rw [hshift]
      _ = _ := by rw [stayAct_add]; abel

/-- A zero input coordinate stays zero in the unchanged branch; supporting lemma for
`apd:thm:layer_inflow`. -/
theorem stayAct_apply_eq_zero (G : PauliString n) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) (p : PauliIndex n) (hy : y.ofLp p = 0) :
    (stayAct G θ y).ofLp p = 0 := by
  simp [stayAct_apply, hy]

/-- **Exactly `j` sine branches raise the Pauli weight by at most `j (k_h - 1)`.**
If the input has no coefficient above weight `w`, then `layerJump L j` of it has none above
`w + j (k_h - 1)`; this is the weight bookkeeping of `apd:thm:layer_inflow`. Cancellations can
remove coefficients, so only support containment is asserted. No disjointness is needed. -/
theorem layerJump_apply_eq_zero_of_weight_lt (L : List (PauliString n × ℝ))
    {kh w : ℕ} (hk : ∀ g ∈ L, weight g.1 ≤ kh)
    (y : EuclideanSpace ℂ (PauliIndex n))
    (hy : ∀ p : PauliIndex n, w < wt p → y.ofLp p = 0)
    (j : ℕ) (p : PauliIndex n) (hp : w + j * (kh - 1) < wt p) :
    (layerJump L j y).ofLp p = 0 := by
  induction L generalizing j p with
  | nil =>
    cases j with
    | zero => exact hy p (by simpa using hp)
    | succ j => rfl
  | cons g L ih =>
    rcases g with ⟨G, θ⟩
    have hkL : ∀ g ∈ L, weight g.1 ≤ kh := fun g hg => hk g (by simp [hg])
    cases j with
    | zero => exact stayAct_apply_eq_zero G θ _ p (ih hkL 0 p hp)
    | succ j =>
      simp only [layerJump, WithLp.ofLp_add, Pi.add_apply]
      rw [stayAct_apply_eq_zero G θ _ p (ih hkL (j + 1) p hp), zero_add,
        jumpAct_apply]
      split
      · rfl
      next h =>
        have hanti : sympForm G (herm p) = 1 :=
          (sympForm_eq_zero_or_one G (herm p)).resolve_left h
        have hwt : wt p ≤ wt (partner G p) + (kh - 1) := by
          rw [wt_partner]
          exact weight_le_weight_mul_add_kh (hk (G, θ) (by simp)) hanti
        rw [ih hkL j (partner G p) (by
          rw [Nat.add_mul, Nat.one_mul] at hp
          omega), mul_zero, mul_zero]

/-- Finite-support transfer in a `j`-branch matrix column: the input basis vector at `q` can
reach only coordinates of weight at most `wt q + j(k_h-1)`.
Supporting lemma for the row bound of `apd:thm:layer_inflow`. -/
theorem layerJump_single_eq_zero_of_weight_lt (L : List (PauliString n × ℝ))
    {kh : ℕ} (hk : ∀ g ∈ L, weight g.1 ≤ kh) (j : ℕ) (p q : PauliIndex n)
    (hp : wt q + j * (kh - 1) < wt p) :
    (layerJump L j (WithLp.toLp 2 (Pi.single q (1 : ℂ)))).ofLp p = 0 := by
  apply layerJump_apply_eq_zero_of_weight_lt L hk _ ?_ j p hp
  intro r hr
  have hne : r ≠ q := by intro heq; subst heq; omega
  simp [hne]

/-- The set `𝒜(p)` of generators of a finite layer that anticommute with the Pauli `p`.
Supporting definition for `apd:thm:layer_inflow`. -/
def antiLayer (L : List (PauliString n)) (p : PauliIndex n) : Finset (PauliString n) :=
  L.toFinset.filter fun G => sympForm G (herm p) = 1

/-- Membership in the layer's anticommuting generator set; supporting lemma for
`apd:thm:layer_inflow`. -/
@[simp] theorem mem_antiLayer (L : List (PauliString n)) (p : PauliIndex n)
    (G : PauliString n) : G ∈ antiLayer L p ↔ G ∈ L ∧ sympForm G (herm p) = 1 := by
  simp [antiLayer]

/-- **Disjoint supports bound the number of anticommuting generators by the Pauli weight.**
This is the combinatorial statement `|𝒜(p)| ≤ |p|` in `apd:thm:layer_inflow`: every
anticommuting generator meets the support of `p`, and distinct generators of a layer meet it in
disjoint sets of sites. -/
theorem card_antiLayer_le_weight (L : List (PauliString n)) {kh : ℕ}
    (hL : IsLayer kh L) (p : PauliIndex n) : (antiLayer L p).card ≤ wt p := by
  have hdisj : ∀ G ∈ antiLayer L p, ∀ H ∈ antiLayer L p, G ≠ H →
      Disjoint (antiSites G (herm p)) (antiSites H (herm p)) := by
    intro G hG H hH hne
    apply Finset.disjoint_of_subset_left
      ((antiSites_subset_inter G (herm p)).trans Finset.inter_subset_left)
    apply Finset.disjoint_of_subset_right
      ((antiSites_subset_inter H (herm p)).trans Finset.inter_subset_left)
    exact hL.disjoint_of_mem (mem_antiLayer L p G |>.1 hG).1
      (mem_antiLayer L p H |>.1 hH).1 hne
  have hsub : (antiLayer L p).biUnion (fun G => antiSites G (herm p)) ⊆ support (herm p) := by
    intro i hi
    obtain ⟨G, _, hiG⟩ := Finset.mem_biUnion.1 hi
    exact ((antiSites_subset_inter G (herm p)).trans Finset.inter_subset_right) hiG
  calc (antiLayer L p).card
      = ∑ _G ∈ antiLayer L p, 1 := by simp
    _ ≤ ∑ G ∈ antiLayer L p, (antiSites G (herm p)).card := by
        apply Finset.sum_le_sum
        intro G hG
        exact one_le_card_antiSites (mem_antiLayer L p G |>.1 hG).2
    _ = ((antiLayer L p).biUnion (fun G => antiSites G (herm p))).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ wt p := Finset.card_le_card hsub

/-- The number of `j`-element subsets of `𝒜(p)` is at most `C(|p|, j)`. This is the
subset-counting part of the row and column estimates in `apd:thm:layer_inflow`. The matrix
entries themselves are bounded in `row_sum_norm_layerJumpMatrix_le` and
`col_sum_norm_layerJumpMatrix_le`, through `layerAntiCount`. -/
theorem card_antiLayer_powersetCard_le (L : List (PauliString n)) {kh : ℕ}
    (hL : IsLayer kh L) (p : PauliIndex n) (j : ℕ) :
    ((antiLayer L p).powersetCard j).card ≤ (wt p).choose j := by
  rw [Finset.card_powersetCard]
  exact Nat.choose_le_choose j (card_antiLayer_le_weight L hL p)

/-- Commuting with a generator makes its partner translation preserve the symplectic test
against another generator. Supporting lemma for the fixed `𝒜(p)` in
`apd:thm:layer_inflow`. -/
theorem sympForm_herm_partner_of_commute (G H : PauliString n)
    (hGH : sympForm G H = 0) (p : PauliIndex n) :
    sympForm G (herm (partner H p)) = sympForm G (herm p) := by
  change sympForm G (H * herm p) = _
  rw [sympForm_mul_right, hGH, zero_add]

/-- Taking any generator in a commuting layer leaves the entire anticommutation set unchanged.
Supporting lemma for `apd:thm:layer_inflow`. Disjointness is a sufficient
condition, but pairwise commutation is exactly what this identity needs. -/
theorem antiLayer_partner (L : List (PauliString n)) (H : PauliString n)
    (hH : ∀ G ∈ L, sympForm G H = 0) (p : PauliIndex n) :
    antiLayer L (partner H p) = antiLayer L p := by
  ext G
  simp only [mem_antiLayer]
  constructor <;> rintro ⟨hG, hp⟩ <;> refine ⟨hG, ?_⟩
  · rwa [sympForm_herm_partner_of_commute G H (hH G hG)] at hp
  · rwa [sympForm_herm_partner_of_commute G H (hH G hG)]

/-- The largest absolute sine `max_l |sin θ_l|` of a layer, with value `0` for the empty layer.
Stating `apd:thm:layer_inflow` with this parameter makes the bound valid for arbitrary angles:
monotonicity of sine on an interval of angles is never needed. -/
noncomputable def layerSigma : List (PauliString n × ℝ) → ℝ
  | [] => 0
  | g :: L => max |Real.sin g.2| (layerSigma L)

/-- The layer's largest absolute sine is nonnegative; supporting lemma for
`apd:thm:layer_inflow` with the parameter `σ = layerSigma L`. -/
theorem layerSigma_nonneg (L : List (PauliString n × ℝ)) : 0 ≤ layerSigma L := by
  cases L with
  | nil => exact le_rfl
  | cons g L => exact (abs_nonneg _).trans (le_max_left _ _)

/-- Every individual sine magnitude is bounded by the layer parameter.
Supporting lemma for `apd:thm:layer_inflow`. -/
theorem abs_sin_le_layerSigma (L : List (PauliString n × ℝ))
    (g : PauliString n × ℝ) (hg : g ∈ L) : |Real.sin g.2| ≤ layerSigma L := by
  induction L with
  | nil => simp at hg
  | cons h L ih =>
    rcases List.mem_cons.1 hg with rfl | hg
    · exact le_max_left _ _
    · exact (ih hg).trans (le_max_right _ _)

/-- The matrix of the exactly-`j` component `layerJump L j`: its column `q` is the image of the
basis vector at `q`. Supporting definition for `A^{(j)}` in `apd:thm:layer_inflow`; the
restriction to high-weight rows and low-weight columns is `layerInflowMatrix`. -/
noncomputable def layerJumpMatrix (L : List (PauliString n × ℝ)) (j : ℕ) :
    Matrix (PauliIndex n) (PauliIndex n) ℂ := fun p q =>
  (layerJump L j (WithLp.toLp 2 (Pi.single q (1 : ℂ)))).ofLp p

/-- `layerJumpMatrix L j` acts on an arbitrary coefficient vector as `layerJump L j` does, not
only on basis vectors. Supporting lemma for `apd:thm:layer_inflow`. -/
theorem layerJump_apply_eq_sum_matrix (L : List (PauliString n × ℝ)) (j : ℕ)
    (y : EuclideanSpace ℂ (PauliIndex n)) (p : PauliIndex n) :
    (layerJump L j y).ofLp p = ∑ q, layerJumpMatrix L j p q * y.ofLp q := by
  classical
  simp only [layerJumpMatrix]
  induction L generalizing j p with
  | nil =>
    cases j with
    | zero => simp [layerJump]
    | succ j => simp [layerJump]
  | cons g L ih =>
    rcases g with ⟨G, θ⟩
    cases j with
    | zero =>
      by_cases h : sympForm G (herm p) = 0
      · simpa only [layerJump, stayAct_apply, h, ↓reduceIte] using ih 0 p
      · simp only [layerJump, stayAct_apply, h, ↓reduceIte]
        rw [ih, Finset.mul_sum]
        exact Finset.sum_congr rfl fun q _ => by ring
    | succ j =>
      by_cases h : sympForm G (herm p) = 0
      · simpa only [layerJump, WithLp.ofLp_add, Pi.add_apply, stayAct_apply, jumpAct_apply,
          h, ↓reduceIte, add_zero] using ih (j + 1) p
      · simp only [layerJump, WithLp.ofLp_add, Pi.add_apply, stayAct_apply, jumpAct_apply,
          h, ↓reduceIte]
        rw [ih, ih, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun q _ => by ring

/-- The number of anticommuting rotations, retaining list multiplicity. In a disjoint layer
this equals `|𝒜(p)|`; in a merely commuting layer it may be system-size dependent.
Supporting definition for `apd:thm:layer_inflow`. -/
def layerAntiCount (L : List (PauliString n)) (p : PauliIndex n) : ℕ :=
  L.countP fun G => sympForm G (herm p) = 1

/-- Partner translation in a commuting layer preserves its anticommuting-rotation count.
Supporting lemma for `apd:thm:layer_inflow`. -/
theorem layerAntiCount_partner (L : List (PauliString n)) (G : PauliString n)
    (hG : ∀ H ∈ L, sympForm H G = 0) (p : PauliIndex n) :
    layerAntiCount L (partner G p) = layerAntiCount L p := by
  induction L with
  | nil => rfl
  | cons H L ih =>
    simp only [layerAntiCount, List.countP_cons]
    rw [sympForm_herm_partner_of_commute H G (hG H (by simp))]
    change layerAntiCount L (partner G p) + _ = layerAntiCount L p + _
    rw [ih (fun H hH => hG H (by simp [hH]))]

/-- Branches through generators that commute with `G` preserve the commutation class with `G`:
the entry `(p, q)` of `layerJumpMatrix L j` vanishes unless `p` and `q` have the same symplectic
form with `G`. Supporting lemma for the column estimate of `apd:thm:layer_inflow`. This is
finer than support containment: it shows that an input Pauli commuting with `G` never takes the
sine branch of `G`. -/
theorem layerJumpMatrix_eq_zero_of_sympForm_ne (L : List (PauliString n × ℝ))
    (G : PauliString n) (hG : ∀ g ∈ L, sympForm G g.1 = 0)
    (j : ℕ) (p q : PauliIndex n)
    (hpq : sympForm G (herm p) ≠ sympForm G (herm q)) :
    layerJumpMatrix L j p q = 0 := by
  induction L generalizing j p with
  | nil =>
    cases j with
    | zero =>
      have hne : p ≠ q := by intro h; subst h; exact hpq rfl
      simp [layerJumpMatrix, layerJump, hne]
    | succ j => rfl
  | cons g L ih =>
    rcases g with ⟨H, θ⟩
    have hGL : ∀ g ∈ L, sympForm G g.1 = 0 := fun g hg => hG g (by simp [hg])
    have hpartner : sympForm G (herm (partner H p)) ≠ sympForm G (herm q) := by
      rwa [sympForm_herm_partner_of_commute G H (hG (H, θ) (by simp))]
    cases j with
    | zero =>
      change (stayAct H θ _).ofLp p = 0
      exact stayAct_apply_eq_zero H θ _ p (ih hGL 0 p hpq)
    | succ j =>
      change (stayAct H θ _ + jumpAct H θ _).ofLp p = 0
      simp only [WithLp.ofLp_add, Pi.add_apply, stayAct_apply, jumpAct_apply]
      change (if _ then layerJumpMatrix L (j + 1) p q
          else _ * layerJumpMatrix L (j + 1) p q)
        + (if _ then 0 else _ * (_ * layerJumpMatrix L j (partner H p) q)) = 0
      rw [ih hGL (j + 1) p hpq, ih hGL j (partner H p) hpartner]
      split <;> simp

/-- The unchanged branch is a contraction in each coefficient magnitude.
Supporting lemma for `apd:thm:layer_inflow`. -/
theorem norm_stayAct_apply_le (G : PauliString n) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) (p : PauliIndex n) :
    ‖(stayAct G θ y).ofLp p‖ ≤ ‖y.ofLp p‖ := by
  rw [stayAct_apply]
  split
  · exact le_rfl
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one θ)

/-- The sine-branch coefficient is bounded by the absolute sine times its partner coefficient.
Supporting lemma for `apd:thm:layer_inflow`. No Hermitian hypothesis is needed
for this magnitude statement: `partnerSign` is always a fourth root of unity. -/
theorem norm_jumpAct_apply_le (G : PauliString n) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) (p : PauliIndex n) :
    ‖(jumpAct G θ y).ofLp p‖ ≤ |Real.sin θ| * ‖y.ofLp (partner G p)‖ := by
  rw [jumpAct_apply]
  split
  · simp only [norm_zero]
    positivity
  · simp only [norm_mul, norm_neg, partnerSign, norm_iPow, one_mul,
      Complex.norm_real, Real.norm_eq_abs, le_refl]

/-- The unchanged branch contracts the coefficient `ℓ¹` norm. Supporting lemma for the
column estimate of `apd:thm:layer_inflow`. -/
theorem sum_norm_stayAct_le (G : PauliString n) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    ∑ p, ‖(stayAct G θ y).ofLp p‖ ≤ ∑ p, ‖y.ofLp p‖ :=
  Finset.sum_le_sum fun p _ => norm_stayAct_apply_le G θ y p

/-- The sine branch contracts the coefficient `ℓ¹` norm by its absolute sine. Supporting
lemma for the column estimate of `apd:thm:layer_inflow`. -/
theorem sum_norm_jumpAct_le (G : PauliString n) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    ∑ p, ‖(jumpAct G θ y).ofLp p‖ ≤ |Real.sin θ| * ∑ p, ‖y.ofLp p‖ := by
  have hsum : ∑ p : PauliIndex n, ‖y.ofLp (partner G p)‖ = ∑ p, ‖y.ofLp p‖ :=
    Finset.sum_nbij' (partner G) (partner G) (by simp) (by simp)
      (fun p _ => partner_partner G p) (fun p _ => partner_partner G p) (fun _ _ => rfl)
  calc ∑ p, ‖(jumpAct G θ y).ofLp p‖
      ≤ ∑ p, |Real.sin θ| * ‖y.ofLp (partner G p)‖ :=
        Finset.sum_le_sum fun p _ => norm_jumpAct_apply_le G θ y p
    _ = _ := by rw [← Finset.mul_sum, hsum]

/-- In a disjoint layer the list count has no anticommuting duplicates, so it is exactly the
finite-set cardinality `|𝒜(p)|`. Supporting lemma for `apd:thm:layer_inflow`.
Repeated scalar generators are harmless because they never anticommute. -/
theorem layerAntiCount_eq_card_antiLayer (L : List (PauliString n)) {kh : ℕ}
    (hL : IsLayer kh L) (p : PauliIndex n) :
    layerAntiCount L p = (antiLayer L p).card := by
  let pred : PauliString n → Bool := fun G => sympForm G (herm p) = 1
  have hnodup : (L.filter pred).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_filter]
    apply hL.disjoint.imp
    intro G H hd hG _ hGH
    subst H
    have hanti : sympForm G (herm p) = 1 := by simpa [pred] using hG
    obtain ⟨i, hi⟩ := inter_support_nonempty_of_sympForm hanti
    exact Finset.disjoint_left.1 hd (Finset.mem_inter.1 hi).1 (Finset.mem_inter.1 hi).1
  change L.countP pred = _
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup hnodup,
    List.toFinset_filter]
  simp [pred, antiLayer]

/-- The anticommuting-rotation list count is bounded by Pauli weight for a disjoint layer.
Supporting lemma for `apd:thm:layer_inflow`. -/
theorem layerAntiCount_le_weight (L : List (PauliString n)) {kh : ℕ}
    (hL : IsLayer kh L) (p : PauliIndex n) : layerAntiCount L p ≤ wt p := by
  rw [layerAntiCount_eq_card_antiLayer L hL]
  exact card_antiLayer_le_weight L hL p

/-- **Absolute row sums of the exactly-`j` matrix.** Row `p` of `layerJumpMatrix L j` has
absolute sum at most `C(c, j) σ^j`, where `c` is the number of rotations of the layer that
anticommute with `p`. Supporting theorem for the Schur step in `apd:thm:layer_inflow`.
Pairwise commutation suffices for this estimate; disjoint supports are used afterwards, to bound
`layerAntiCount` by the Pauli weight of `p`. -/
theorem row_sum_norm_layerJumpMatrix_le (L : List (PauliString n × ℝ))
    (hcomm : ∀ g ∈ L, ∀ h ∈ L, sympForm g.1 h.1 = 0)
    {σ : ℝ} (hσ : 0 ≤ σ) (hsin : ∀ g ∈ L, |Real.sin g.2| ≤ σ)
    (j : ℕ) (p : PauliIndex n) :
    ∑ q, ‖layerJumpMatrix L j p q‖
      ≤ ((layerAntiCount (L.map Prod.fst) p).choose j : ℝ) * σ ^ j := by
  classical
  induction L generalizing j p with
  | nil =>
    cases j with
    | zero => simp [layerJumpMatrix, layerJump, layerAntiCount, apply_ite]
    | succ j => simp [layerJumpMatrix, layerJump, layerAntiCount]
  | cons g L ih =>
    rcases g with ⟨G, θ⟩
    have hcL : ∀ g ∈ L, ∀ h ∈ L, sympForm g.1 h.1 = 0 :=
      fun g hg h hh => hcomm g (by simp [hg]) h (by simp [hh])
    have hsL : ∀ g ∈ L, |Real.sin g.2| ≤ σ := fun g hg => hsin g (by simp [hg])
    have hs : |Real.sin θ| ≤ σ := hsin (G, θ) (by simp)
    cases j with
    | zero =>
      calc ∑ q, ‖layerJumpMatrix ((G, θ) :: L) 0 p q‖
          ≤ ∑ q, ‖layerJumpMatrix L 0 p q‖ :=
            Finset.sum_le_sum fun q _ => norm_stayAct_apply_le G θ _ p
        _ ≤ _ := by simpa using ih hcL hsL 0 p
    | succ j =>
      by_cases hp : sympForm G (herm p) = 0
      · have hcount : layerAntiCount (((G, θ) :: L).map Prod.fst) p
            = layerAntiCount (L.map Prod.fst) p := by simp [layerAntiCount, hp]
        rw [hcount]
        simpa [layerJumpMatrix, layerJump, stayAct_apply, jumpAct_apply, hp]
          using ih hcL hsL (j + 1) p
      · have hp1 : sympForm G (herm p) = 1 :=
          (sympForm_eq_zero_or_one G (herm p)).resolve_left hp
        have hcount : layerAntiCount (((G, θ) :: L).map Prod.fst) p
            = layerAntiCount (L.map Prod.fst) p + 1 := by simp [layerAntiCount, hp1]
        have hpart : layerAntiCount (L.map Prod.fst) (partner G p)
            = layerAntiCount (L.map Prod.fst) p := by
          apply layerAntiCount_partner
          intro H hH
          obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hH
          exact hcomm g (by simp [hg]) (G, θ) (by simp)
        have hprev := ih hcL hsL j (partner G p)
        rw [hpart] at hprev
        rw [hcount]
        calc ∑ q, ‖layerJumpMatrix ((G, θ) :: L) (j + 1) p q‖
            ≤ ∑ q, (‖layerJumpMatrix L (j + 1) p q‖
                + |Real.sin θ| * ‖layerJumpMatrix L j (partner G p) q‖) := by
              apply Finset.sum_le_sum
              intro q _
              exact (norm_add_le _ _).trans
                (add_le_add (norm_stayAct_apply_le G θ _ p)
                  (norm_jumpAct_apply_le G θ _ p))
          _ = (∑ q, ‖layerJumpMatrix L (j + 1) p q‖)
                + |Real.sin θ| * ∑ q, ‖layerJumpMatrix L j (partner G p) q‖ := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
          _ ≤ ((layerAntiCount (L.map Prod.fst) p).choose (j + 1) : ℝ) * σ ^ (j + 1)
                + σ * (((layerAntiCount (L.map Prod.fst) p).choose j : ℝ) * σ ^ j) :=
              add_le_add (ih hcL hsL (j + 1) p)
                (mul_le_mul hs hprev (Finset.sum_nonneg fun _ _ => norm_nonneg _) hσ)
          _ = _ := by rw [Nat.choose_succ_succ, Nat.cast_add, pow_succ]; ring

/-- If the input Pauli `q` commutes with `G`, and `G` commutes with every generator of `L`, then
the sine branch of `G` annihilates `layerJump L j` of the basis vector at `q`.
Supporting lemma for the column estimate of `apd:thm:layer_inflow`. -/
theorem jumpAct_layerJump_single_eq_zero (L : List (PauliString n × ℝ))
    (G : PauliString n) (θ : ℝ) (hG : ∀ g ∈ L, sympForm G g.1 = 0)
    (j : ℕ) (q : PauliIndex n) (hq : sympForm G (herm q) = 0) :
    jumpAct G θ (layerJump L j (WithLp.toLp 2 (Pi.single q (1 : ℂ)))) = 0 := by
  ext p
  rw [jumpAct_apply]
  split
  · rfl
  next hp =>
    have hz : layerJumpMatrix L j (partner G p) q = 0 :=
      layerJumpMatrix_eq_zero_of_sympForm_ne L G hG j (partner G p) q (by
        rw [sympForm_herm_partner, hq]
        exact hp)
    change -(Real.sin θ : ℂ) * (partnerSign G p * layerJumpMatrix L j (partner G p) q) = 0
    rw [hz, mul_zero, mul_zero]

/-- **Absolute column sums of the exactly-`j` matrix.** Column `q` of `layerJumpMatrix L j` has
absolute sum at most `C(c, j) σ^j`, where `c` is the number of rotations of the layer that
anticommute with `q`. Supporting theorem for the Schur step in `apd:thm:layer_inflow`.
The proof uses preservation of the commutation class (`jumpAct_layerJump_single_eq_zero`) and
Pascal's rule; it does not assume that distinct choices of branches give distinct nonzero
entries. -/
theorem col_sum_norm_layerJumpMatrix_le (L : List (PauliString n × ℝ))
    (hcomm : ∀ g ∈ L, ∀ h ∈ L, sympForm g.1 h.1 = 0)
    {σ : ℝ} (hσ : 0 ≤ σ) (hsin : ∀ g ∈ L, |Real.sin g.2| ≤ σ)
    (j : ℕ) (q : PauliIndex n) :
    ∑ p, ‖layerJumpMatrix L j p q‖
      ≤ ((layerAntiCount (L.map Prod.fst) q).choose j : ℝ) * σ ^ j := by
  classical
  induction L generalizing j with
  | nil =>
    cases j with
    | zero => simp [layerJumpMatrix, layerJump, layerAntiCount, apply_ite]
    | succ j => simp [layerJumpMatrix, layerJump, layerAntiCount]
  | cons g L ih =>
    rcases g with ⟨G, θ⟩
    have hcL : ∀ g ∈ L, ∀ h ∈ L, sympForm g.1 h.1 = 0 :=
      fun g hg h hh => hcomm g (by simp [hg]) h (by simp [hh])
    have hGL : ∀ g ∈ L, sympForm G g.1 = 0 :=
      fun g hg => hcomm (G, θ) (by simp) g (by simp [hg])
    have hsL : ∀ g ∈ L, |Real.sin g.2| ≤ σ := fun g hg => hsin g (by simp [hg])
    have hs : |Real.sin θ| ≤ σ := hsin (G, θ) (by simp)
    cases j with
    | zero =>
      calc ∑ p, ‖layerJumpMatrix ((G, θ) :: L) 0 p q‖
          ≤ ∑ p, ‖layerJumpMatrix L 0 p q‖ := sum_norm_stayAct_le G θ _
        _ ≤ _ := by simpa using ih hcL hsL 0
    | succ j =>
      by_cases hq : sympForm G (herm q) = 0
      · have hcount : layerAntiCount (((G, θ) :: L).map Prod.fst) q
            = layerAntiCount (L.map Prod.fst) q := by simp [layerAntiCount, hq]
        rw [hcount]
        have hz := jumpAct_layerJump_single_eq_zero L G θ hGL j q hq
        calc ∑ p, ‖layerJumpMatrix ((G, θ) :: L) (j + 1) p q‖
            = ∑ p, ‖(stayAct G θ
                (layerJump L (j + 1) (WithLp.toLp 2 (Pi.single q (1 : ℂ))))).ofLp p‖ := by
              simp only [layerJumpMatrix, layerJump, hz, add_zero]
          _ ≤ ∑ p, ‖layerJumpMatrix L (j + 1) p q‖ := sum_norm_stayAct_le G θ _
          _ ≤ _ := ih hcL hsL (j + 1)
      · have hq1 : sympForm G (herm q) = 1 :=
          (sympForm_eq_zero_or_one G (herm q)).resolve_left hq
        have hcount : layerAntiCount (((G, θ) :: L).map Prod.fst) q
            = layerAntiCount (L.map Prod.fst) q + 1 := by simp [layerAntiCount, hq1]
        rw [hcount]
        calc ∑ p, ‖layerJumpMatrix ((G, θ) :: L) (j + 1) p q‖
            ≤ (∑ p, ‖(stayAct G θ
                (layerJump L (j + 1) (WithLp.toLp 2 (Pi.single q (1 : ℂ))))).ofLp p‖)
                + ∑ p, ‖(jumpAct G θ
                  (layerJump L j (WithLp.toLp 2 (Pi.single q (1 : ℂ))))).ofLp p‖ := by
              rw [← Finset.sum_add_distrib]
              exact Finset.sum_le_sum fun p _ => norm_add_le _ _
          _ ≤ (∑ p, ‖layerJumpMatrix L (j + 1) p q‖)
                + |Real.sin θ| * ∑ p, ‖layerJumpMatrix L j p q‖ :=
              add_le_add (sum_norm_stayAct_le G θ _) (sum_norm_jumpAct_le G θ _)
          _ ≤ ((layerAntiCount (L.map Prod.fst) q).choose (j + 1) : ℝ) * σ ^ (j + 1)
                + σ * (((layerAntiCount (L.map Prod.fst) q).choose j : ℝ) * σ ^ j) :=
              add_le_add (ih hcL hsL (j + 1))
                (mul_le_mul hs (ih hcL hsL j)
                  (Finset.sum_nonneg fun _ _ => norm_nonneg _) hσ)
          _ = _ := by rw [Nat.choose_succ_succ, Nat.cast_add, pow_succ]; ring

/-- Disjoint supports imply the pairwise commutation used by the exactly-`j` row and column
estimates. Supporting lemma for `apd:thm:layer_inflow`. -/
theorem layer_sympForm_eq_zero (L : List (PauliString n × ℝ)) {kh : ℕ}
    (hL : IsLayer kh (L.map Prod.fst)) :
    ∀ g ∈ L, ∀ h ∈ L, sympForm g.1 h.1 = 0 := by
  intro g hg h hh
  by_cases hgh : g.1 = h.1
  · rw [hgh, sympForm_self]
  · exact sympForm_eq_zero_of_disjoint_support
      (hL.disjoint_of_mem (List.mem_map_of_mem hg) (List.mem_map_of_mem hh) hgh)

/-- The exactly-`j` matrix restricted to rows of weight `> w` and columns of weight `≤ w`.
This is `A^{(j)}` in `apd:thm:layer_inflow`, represented on the full coefficient
space by filling the other blocks with zeros. -/
noncomputable def layerInflowMatrix (L : List (PauliString n × ℝ)) (w j : ℕ) :
    Matrix (PauliIndex n) (PauliIndex n) ℂ := fun p q =>
  if w < wt p ∧ wt q ≤ w then layerJumpMatrix L j p q else 0

/-- **Row bound for the high-from-low exactly-`j` block.**
Formalizes the row estimate of `apd:thm:layer_inflow`: a nonzero row has weight at most
`w + j (k_h - 1)` by `layerJump_single_eq_zero_of_weight_lt`, and in a disjoint-support layer at
most that many generators anticommute with it. -/
theorem row_sum_norm_layerInflowMatrix_le (L : List (PauliString n × ℝ)) {kh : ℕ}
    (hL : IsLayer kh (L.map Prod.fst)) {σ : ℝ} (hσ : 0 ≤ σ)
    (hsin : ∀ g ∈ L, |Real.sin g.2| ≤ σ) (w j : ℕ) (p : PauliIndex n) :
    ∑ q, ‖layerInflowMatrix L w j p q‖
      ≤ ((w + j * (kh - 1)).choose j : ℝ) * σ ^ j := by
  by_cases hp : w + j * (kh - 1) < wt p
  · have hz : ∀ q, layerInflowMatrix L w j p q = 0 := by
      intro q
      unfold layerInflowMatrix
      split
      next h =>
        exact layerJump_single_eq_zero_of_weight_lt L
          (fun g hg => hL.weight_le g.1 (List.mem_map_of_mem hg)) j p q
          (lt_of_le_of_lt (Nat.add_le_add_right h.2 _) hp)
      · rfl
    simp only [hz, norm_zero, Finset.sum_const_zero]
    positivity
  · have hc : layerAntiCount (L.map Prod.fst) p ≤ w + j * (kh - 1) :=
      (layerAntiCount_le_weight _ hL p).trans (Nat.le_of_not_gt hp)
    calc ∑ q, ‖layerInflowMatrix L w j p q‖
        ≤ ∑ q, ‖layerJumpMatrix L j p q‖ := by
          apply Finset.sum_le_sum
          intro q _
          unfold layerInflowMatrix
          split
          · exact le_rfl
          · simpa only [norm_zero] using norm_nonneg (layerJumpMatrix L j p q)
      _ ≤ ((layerAntiCount (L.map Prod.fst) p).choose j : ℝ) * σ ^ j :=
          row_sum_norm_layerJumpMatrix_le L (layer_sympForm_eq_zero L hL) hσ hsin j p
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_choose j hc)
          (pow_nonneg hσ j)

/-- **Column bound for the high-from-low exactly-`j` block.**
Formalizes the column estimate of `apd:thm:layer_inflow`: a nonzero column has weight at most
`w`. The angles are unrestricted and enter only through the bound `σ` on their absolute sines. -/
theorem col_sum_norm_layerInflowMatrix_le (L : List (PauliString n × ℝ)) {kh : ℕ}
    (hL : IsLayer kh (L.map Prod.fst)) {σ : ℝ} (hσ : 0 ≤ σ)
    (hsin : ∀ g ∈ L, |Real.sin g.2| ≤ σ) (w j : ℕ) (q : PauliIndex n) :
    ∑ p, ‖layerInflowMatrix L w j p q‖ ≤ (w.choose j : ℝ) * σ ^ j := by
  by_cases hq : wt q ≤ w
  · have hc : layerAntiCount (L.map Prod.fst) q ≤ w :=
      (layerAntiCount_le_weight _ hL q).trans hq
    calc ∑ p, ‖layerInflowMatrix L w j p q‖
        ≤ ∑ p, ‖layerJumpMatrix L j p q‖ := by
          apply Finset.sum_le_sum
          intro p _
          unfold layerInflowMatrix
          split
          · exact le_rfl
          · simpa only [norm_zero] using norm_nonneg (layerJumpMatrix L j p q)
      _ ≤ ((layerAntiCount (L.map Prod.fst) q).choose j : ℝ) * σ ^ j :=
          col_sum_norm_layerJumpMatrix_le L (layer_sympForm_eq_zero L hL) hσ hsin j q
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_choose j hc)
          (pow_nonneg hσ j)
  · simp only [layerInflowMatrix, hq, and_false, ↓reduceIte, norm_zero, Finset.sum_const_zero]
    positivity

/-- **Layer inflow, binomial form.** Formalizes the first inequality of `apd:eq:layer_inflow` in
`apd:thm:layer_inflow`, for any `σ` dominating every absolute sine and an arbitrary threshold
`w`. The Schur test combines the row bound with the (smaller) column bound. The matrix is built
from the rotations themselves, so no flow inequality is assumed.
At `w = w_m`, the upper weight is `w_m + j (k_h - 1) = w_{m+j}` for `m ≥ 1`. -/
theorem norm_layerInflowMatrix_le (L : List (PauliString n × ℝ)) {kh : ℕ}
    (hL : IsLayer kh (L.map Prod.fst)) {σ : ℝ} (hσ : 0 ≤ σ)
    (hsin : ∀ g ∈ L, |Real.sin g.2| ≤ σ) (w j : ℕ) :
    ‖layerInflowMatrix L w j‖ ≤ ((w + j * (kh - 1)).choose j : ℝ) * σ ^ j := by
  apply Lean4LPD.l2_opNorm_le_of_row_col_bound _ (by positivity)
  · exact row_sum_norm_layerInflowMatrix_le L hL hσ hsin w j
  · intro q
    exact (col_sum_norm_layerInflowMatrix_le L hL hσ hsin w j q).trans
      (mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.choose_le_choose j (Nat.le_add_right w (j * (kh - 1))))
        (pow_nonneg hσ j))

/-- The layer-inflow bound with no hypothesis on the angles: `apd:eq:layer_inflow` with
`σ = max_l |sin θ_l|`. Neither positivity of the sines nor monotonicity of sine on an interval of
angles is required, which is more general than the paper's statement. -/
theorem norm_layerInflowMatrix_le_layerSigma (L : List (PauliString n × ℝ)) {kh : ℕ}
    (hL : IsLayer kh (L.map Prod.fst)) (w j : ℕ) :
    ‖layerInflowMatrix L w j‖
      ≤ ((w + j * (kh - 1)).choose j : ℝ) * layerSigma L ^ j :=
  norm_layerInflowMatrix_le L hL (layerSigma_nonneg L) (abs_sin_le_layerSigma L) w j

/-- **Layer inflow, factorial form.** Formalizes the second inequality of
`apd:eq:layer_inflow`, `C(W, j) σ^j ≤ (W σ)^j / j!` with `W = w + j (k_h - 1)`, for the
absolute-sine parameter `σ` and an arbitrary natural weight threshold `w`. -/
theorem norm_layerInflowMatrix_le_factorial (L : List (PauliString n × ℝ)) {kh : ℕ}
    (hL : IsLayer kh (L.map Prod.fst)) {σ : ℝ} (hσ : 0 ≤ σ)
    (hsin : ∀ g ∈ L, |Real.sin g.2| ≤ σ) (w j : ℕ) :
    ‖layerInflowMatrix L w j‖
      ≤ (((w + j * (kh - 1) : ℕ) : ℝ) * σ) ^ j / (Nat.factorial j : ℝ) := by
  calc ‖layerInflowMatrix L w j‖
      ≤ ((w + j * (kh - 1)).choose j : ℝ) * σ ^ j :=
        norm_layerInflowMatrix_le L hL hσ hsin w j
    _ ≤ (((w + j * (kh - 1) : ℕ) : ℝ) ^ j / (Nat.factorial j : ℝ)) * σ ^ j :=
        mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div j (w + j * (kh - 1)))
          (pow_nonneg hσ j)
    _ = _ := by rw [mul_pow]; ring

/-- `layerInflowMatrix L w j` acts as `layerJump L j` restricted to low-weight inputs and
high-weight outputs. This connects the Schur bound to the Pauli coefficients of the conjugated
operator in `apd:thm:layer_inflow`. -/
theorem layerInflowMatrix_mulVec (L : List (PauliString n × ℝ)) (w j : ℕ)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    WithLp.toLp 2 (layerInflowMatrix L w j *ᵥ y.ofLp)
      = restr (highSet n w) (layerJump L j (restr (highSet n w)ᶜ y)) := by
  classical
  ext p
  simp only [Matrix.mulVec, dotProduct, layerInflowMatrix, restr_apply,
    mem_highSet]
  by_cases hp : w < wt p
  · simp only [hp, true_and, ↓reduceIte, layerJump_apply_eq_sum_matrix, restr_apply,
      Finset.mem_compl, mem_highSet, not_lt]
    exact Finset.sum_congr rfl fun q _ => by split <;> simp_all
  · simp [hp]

/-- The zero-sine branch is diagonal, so its high-from-low block vanishes.
Supporting lemma for `A_RB = ∑_{j≥1} A^{(j)}` in `apd:thm:layer_inflow`. -/
theorem layerInflowMatrix_zero (L : List (PauliString n × ℝ)) (w : ℕ) :
    layerInflowMatrix L w 0 = 0 := by
  ext p q
  unfold layerInflowMatrix
  split
  next h =>
    exact layerJump_single_eq_zero_of_weight_lt L
      (kh := n) (fun g _ => by simpa [weight] using Finset.card_le_univ (support g.1)) 0 p q
      (by simpa using lt_of_le_of_lt h.2 h.1)
  · rfl

/-- Additivity of the layer action on coefficient vectors. Supporting lemma for the high/low
split in `apd:thm:layer_inflow`. -/
theorem layerAct_add (L : List (PauliString n × ℝ))
    (y z : EuclideanSpace ℂ (PauliIndex n)) :
    layerAct L (y + z) = layerAct L y + layerAct L z := by
  induction L with
  | nil => rfl
  | cons g L ih =>
    rcases g with ⟨G, θ⟩
    rw [layerAct, ih, rotAct_add]
    rfl

/-- Finite-sum compatibility of coefficient projection. Supporting lemma for
`A_RB = ∑_{j≥1} A^{(j)}` in `apd:thm:layer_inflow`. -/
theorem restr_sum {ι : Type*} (s : Finset ι) (R : Finset (PauliIndex n))
    (f : ι → EuclideanSpace ℂ (PauliIndex n)) :
    restr R (∑ i ∈ s, f i) = ∑ i ∈ s, restr R (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext p; simp [restr_apply]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, restr_add, ih]

/-- **The high-from-low block of a layer is the sum of its exactly-`j` blocks.**
This is the action form of `A_RB = ∑_{j≥1} A^{(j)}` in `apd:thm:layer_inflow`. The finite sum
runs over `0 ≤ j ≤ L.length`; its `j = 0` term vanishes by `layerInflowMatrix_zero`. -/
theorem restr_layerAct_low_eq_sum_inflow (L : List (PauliString n × ℝ)) (w : ℕ)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    restr (highSet n w) (layerAct L (restr (highSet n w)ᶜ y))
      = ∑ j ∈ range (L.length + 1), Lean4LPD.clm (layerInflowMatrix L w j) y := by
  rw [layerAct_eq_sum_layerJump, restr_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (layerInflowMatrix_mulVec L w j y).symm

/-- **High-weight norm after a layer: the previous high-weight norm plus the inflows.**
The triangle inequality applied to the block decomposition of `apd:thm:layer_inflow`: the
high-to-high block is a contraction because the layer is an isometry (`norm_layerAct`), and the
high-from-low block is the sum of the `A^{(j)}`. Both facts are proved above from the rotations,
so no flow inequality is assumed. -/
theorem norm_restr_layerAct_le_sum_inflow (L : List (PauliString n × ℝ))
    (hL : ∀ g ∈ L, IsSelfAdjoint g.1) (w : ℕ)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    ‖restr (highSet n w) (layerAct L y)‖ ≤ ‖restr (highSet n w) y‖
      + ∑ j ∈ range (L.length + 1), ‖Lean4LPD.clm (layerInflowMatrix L w j) y‖ := by
  have hsplit : restr (highSet n w) (layerAct L y)
      = restr (highSet n w) (layerAct L (restr (highSet n w) y))
        + restr (highSet n w) (layerAct L (restr (highSet n w)ᶜ y)) := by
    rw [← restr_add, ← layerAct_add, restr_add_restr_compl]
  rw [hsplit]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (norm_restr_le _ _).trans_eq (norm_layerAct L hL _)
  · rw [restr_layerAct_low_eq_sum_inflow]
    exact norm_sum_le _ _

/-- A `j`-jump inflow into weights above `w` only uses the input's coefficients of weight above
`w'`, for any `w'` with `w' + j (k_h - 1) ≤ w`. This localizes the inflow on the lower rung, as
needed by `apd:rmk:multijump`; it follows from the coefficient support bound in
`apd:thm:layer_inflow`. -/
theorem layerInflowMatrix_clm_restr (L : List (PauliString n × ℝ)) {kh w w' j : ℕ}
    (hk : ∀ g ∈ L, weight g.1 ≤ kh) (hw : w' + j * (kh - 1) ≤ w)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    Lean4LPD.clm (layerInflowMatrix L w j) y
      = Lean4LPD.clm (layerInflowMatrix L w j) (restr (highSet n w') y) := by
  classical
  ext p
  change (∑ q, layerInflowMatrix L w j p q * y.ofLp q)
    = ∑ q, layerInflowMatrix L w j p q * (restr (highSet n w') y).ofLp q
  apply Finset.sum_congr rfl
  intro q _
  rw [restr_apply]
  by_cases hq : w' < wt q
  · rw [ite_eq_left (mem_highSet.2 hq)]
  · rw [ite_eq_right (fun h => hq (mem_highSet.1 h)), mul_zero]
    have hz : layerInflowMatrix L w j p q = 0 := by
      unfold layerInflowMatrix
      split
      next h =>
        exact layerJump_single_eq_zero_of_weight_lt L hk j p q
          (lt_of_le_of_lt ((Nat.add_le_add_right (Nat.le_of_not_gt hq) _).trans hw) h.1)
      · rfl
    rw [hz, zero_mul]

/-- The `j`-jump inflow of a coefficient vector is bounded by the factorial inflow factor times
the norm of the vector. Supporting theorem for `apd:thm:layer_inflow`
and the multi-jump recursion in `apd:rmk:multijump`. -/
theorem norm_layerInflowMatrix_clm_le (L : List (PauliString n × ℝ)) {kh : ℕ}
    (hL : IsLayer kh (L.map Prod.fst)) {σ : ℝ} (hσ : 0 ≤ σ)
    (hsin : ∀ g ∈ L, |Real.sin g.2| ≤ σ) (w j : ℕ)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    ‖Lean4LPD.clm (layerInflowMatrix L w j) y‖
      ≤ ((((w + j * (kh - 1) : ℕ) : ℝ) * σ) ^ j / (Nat.factorial j : ℝ)) * ‖y‖ := by
  apply (ContinuousLinearMap.le_opNorm _ y).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg y)
  exact norm_layerInflowMatrix_le_factorial L hL hσ hsin w j

/-- The `j`-jump inflow bounded by the input's norm above the lower threshold `w'`, where
`w' + j (k_h - 1) ≤ w`. Supporting theorem for `apd:rmk:multijump`; the coefficient is the one
proved in `apd:thm:layer_inflow`. -/
theorem norm_layerInflowMatrix_clm_le_restr (L : List (PauliString n × ℝ)) {kh w w' j : ℕ}
    (hL : IsLayer kh (L.map Prod.fst)) {σ : ℝ} (hσ : 0 ≤ σ)
    (hsin : ∀ g ∈ L, |Real.sin g.2| ≤ σ) (hw : w' + j * (kh - 1) ≤ w)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    ‖Lean4LPD.clm (layerInflowMatrix L w j) y‖
      ≤ ((((w + j * (kh - 1) : ℕ) : ℝ) * σ) ^ j / (Nat.factorial j : ℝ))
        * ‖restr (highSet n w') y‖ := by
  rw [layerInflowMatrix_clm_restr L (fun g hg => hL.weight_le g.1 (List.mem_map_of_mem hg)) hw]
  exact norm_layerInflowMatrix_clm_le L hL hσ hsin w j _

end Lean4LPD.PauliString
