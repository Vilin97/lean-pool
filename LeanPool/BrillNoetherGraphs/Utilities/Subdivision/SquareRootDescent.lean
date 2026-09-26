/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.OddSubdivisionDescent
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.LaplacianEquiv
public import LeanPool.BrillNoetherGraphs.Utilities.Gonality.GonalityTransport
public import Mathlib.Tactic

/-!
# Descending a doubled degree-two divisor from an odd subdivision

`Utilities/Subdivision/OddSubdivisionDescent.lean` rounds each fine chip to its
nearest coarse vertex, at a cost of at most `(N - 1) / 2` per chip.  That budget
allows only two chips on an odd `N`-fold refinement.  This file treats a
different — and for the genus-six programme more useful — configuration: a fine
divisor of the form `2 • C` with `C` effective of degree two.

Write `C = y₁ + y₂`.  Each `yᵢ` is either the image `fineOf xᵢ` of a coarse
vertex, in which case `2 • yᵢ = embed (2 • xᵢ)` costs nothing, or an interior
fine point at offset `o` (with `0 < o < N`) inside a coarse step.  In the latter
case `2 • yᵢ` is a *pair* of chips at one and the same fine position, and the
two chips may be rounded to opposite ends.  With `k ∈ {0, 1, 2}` of them rounded
to the right end, the signed cost of the pair is `k * N - 2 * o`, so the pair
can be charged

  `dist(2 * o, N * ℤ) = min_k |k * N - 2 * o| ≤ N / 2`,

and for odd `N` this reads `≤ (N - 1) / 2`.  Concretely
`Chip.double` rounds both chips left when `4 * o ≤ N`, both right when
`3 * N ≤ 4 * o`, and splits them otherwise.  Two interior points therefore
contribute at most `2 * ((N - 1) / 2) = N - 1 < N` to the signed budget
`∑ step, |stepCost step|` of
`Spec.rank_ge_of_rank_scale_ge_cost` — including when they share a coarse step,
since `stepCost` only sees the sum of the signed costs and
`|a + b| ≤ |a| + |b|`.  The bookkeeping is done by
`Spec.sum_abs_stepCost_le_sum_abs_group`, which charges a family of chips
group by group whenever each group lies inside a single coarse step.

The conclusion `Spec.rank_ge_of_rank_scale_two_smul_two` is that a rank bound
for `2 • C` on the fine graph descends to a coarse *degree-four* divisor with
the same rank bound, and
`Utilities.Gonality.bnExists_one_four_of_effective_square_root` packages the
case `r = 1` as `BNExists G 1 4`.

## Why this is wanted

For a genus-six graph whose specialized tetragonal class `A` satisfies
`5 • A = 2 • K`, the class `K - 2 • A` has degree `2`, and any degree-two class
`C` with `2 • C ∼ A` is a "square root" of `A`.  If such a `C` is effective on
some odd regular subdivision, the theorem below converts the pencil
`rank (2 • C) ≥ 1` into an honest `w^1_4 ≥ 1` on the original graph.

This is a *partial* mechanism, not a complete one: a computational scan on
2026-09-05 found effective square roots for 91% of the relevant classes, not
for all of them.  Nothing in this file asserts that the square root exists; it
only exploits one when it does.
-/

@[expose] public section

namespace Utilities.Certificate.SubdivisionGraph.Spec

open Finset

variable {n p : ℕ} (spec : Spec n p) (N : ℕ) (hN : 0 < N)

/-! ## Grouping chips that share a coarse step -/

/-- **Grouped signed budget.**  If a family of chips is partitioned by `g` into
groups, each of which lies inside a single coarse step, then the signed budget
`∑ step, |stepCost step|` of `rank_ge_of_rank_scale_ge_cost` is at most the sum
over groups of the absolute value of the group's total signed cost.  Chips of
one group rounded in opposite directions therefore cancel, and groups sharing a
coarse step are charged separately (by the triangle inequality). -/
theorem sum_abs_stepCost_le_sum_abs_group {ι J : Type*} [Fintype ι] [Fintype J]
    [DecidableEq J] (chips : ι → spec.Chip N) (g : ι → J)
    (hg : ∀ i i' : ι, g i = g i' → (chips i).coarseStep = (chips i').coarseStep) :
    (∑ step : spec.Step, |spec.stepCost N chips step|) ≤
      ∑ j : J, |∑ i ∈ Finset.univ.filter (fun i => g i = j), (chips i).signedCost| := by
  -- Split each step's cost into the contributions of the groups.
  have hstep : ∀ step : spec.Step,
      |spec.stepCost N chips step| ≤
        ∑ j : J, |∑ i ∈ (spec.stepChips N chips step).filter (fun i => g i = j),
          (chips i).signedCost| := by
    intro step
    have hfib := Finset.sum_fiberwise (spec.stepChips N chips step) g
      (fun i => (chips i).signedCost)
    unfold stepCost
    rw [← hfib]
    exact Finset.abs_sum_le_sum_abs _ _
  refine le_trans (Finset.sum_le_sum fun step _ => hstep step) ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun j _ => ?_
  -- For a fixed group, at most one coarse step sees it.
  by_cases hemp : (Finset.univ.filter (fun i => g i = j)) = ∅
  · have hz : ∀ step : spec.Step,
        (spec.stepChips N chips step).filter (fun i => g i = j) = ∅ := by
      intro step
      rw [Finset.eq_empty_iff_forall_notMem] at hemp ⊢
      intro i hi
      exact hemp i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩)
    simp only [hz, Finset.sum_empty, abs_zero, Finset.sum_const_zero]
    exact abs_nonneg _
  · obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
    have hgi₀ : g i₀ = j := (Finset.mem_filter.mp hi₀).2
    have hmem : ∀ {step : spec.Step} {i : ι},
        i ∈ (spec.stepChips N chips step).filter (fun i => g i = j) →
          (chips i).coarseStep = step ∧ g i = j := by
      intro step i hi
      obtain ⟨hi1, hi2⟩ := Finset.mem_filter.mp hi
      exact ⟨(Finset.mem_filter.mp hi1).2, hi2⟩
    have hother : ∀ step : spec.Step, step ≠ (chips i₀).coarseStep →
        |∑ i ∈ (spec.stepChips N chips step).filter (fun i => g i = j),
          (chips i).signedCost| = 0 := by
      intro step hne
      have : (spec.stepChips N chips step).filter (fun i => g i = j) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro i hi
        obtain ⟨h1, h2⟩ := hmem hi
        exact hne (h1 ▸ hg i i₀ (h2.trans hgi₀.symm))
      rw [this, Finset.sum_empty, abs_zero]
    have hmain : (spec.stepChips N chips ((chips i₀).coarseStep)).filter (fun i => g i = j)
        = Finset.univ.filter (fun i => g i = j) := by
      ext i
      constructor
      · intro hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (hmem hi).2⟩
      · intro hi
        have h2 : g i = j := (Finset.mem_filter.mp hi).2
        refine Finset.mem_filter.mpr ⟨?_, h2⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hg i i₀ (h2.trans hgi₀.symm)⟩
    rw [Finset.sum_eq_single ((chips i₀).coarseStep)
      (fun step _ hne => hother step hne)
      (fun hc => absurd (Finset.mem_univ ((chips i₀).coarseStep)) hc), hmain]

/-! ## Splitting a doubled interior point -/

namespace Chip

/-- Re-round a chip to a prescribed end of its coarse step. -/
def reround {n p : ℕ} {spec : Spec n p} {N : ℕ} (c : spec.Chip N) (b : Bool) : spec.Chip N :=
  { c with toRight := b }

@[simp] theorem reround_edge {n p : ℕ} {spec : Spec n p} {N : ℕ}
    (c : spec.Chip N) (b : Bool) : (c.reround b).edge = c.edge := rfl

@[simp] theorem reround_step {n p : ℕ} {spec : Spec n p} {N : ℕ}
    (c : spec.Chip N) (b : Bool) : (c.reround b).step = c.step := rfl

@[simp] theorem reround_offset {n p : ℕ} {spec : Spec n p} {N : ℕ}
    (c : spec.Chip N) (b : Bool) : (c.reround b).offset = c.offset := rfl

@[simp] theorem reround_toRight {n p : ℕ} {spec : Spec n p} {N : ℕ}
    (c : spec.Chip N) (b : Bool) : (c.reround b).toRight = b := rfl

@[simp] theorem reround_coarseStep {n p : ℕ} {spec : Spec n p} {N : ℕ}
    (c : spec.Chip N) (b : Bool) : (c.reround b).coarseStep = c.coarseStep := rfl

@[simp] theorem reround_fineVertex {n p : ℕ} {spec : Spec n p} {N : ℕ} (hN : 0 < N)
    (c : spec.Chip N) (b : Bool) : (c.reround b).fineVertex hN = c.fineVertex hN := rfl

/-- The two chips of a doubled interior point, rounded so that their total
signed cost is the distance from `2 * offset` to `N * ℤ`: both left when
`4 * offset ≤ N`, both right when `3 * N ≤ 4 * offset`, and split otherwise. -/
def double {n p : ℕ} {spec : Spec n p} {N : ℕ} (c : spec.Chip N) (k : Fin 2) : spec.Chip N :=
  c.reround (if k.val = 0 then decide (3 * N ≤ 4 * c.offset) else decide (N < 4 * c.offset))

@[simp] theorem double_coarseStep {n p : ℕ} {spec : Spec n p} {N : ℕ}
    (c : spec.Chip N) (k : Fin 2) : (c.double k).coarseStep = c.coarseStep := rfl

@[simp] theorem double_fineVertex {n p : ℕ} {spec : Spec n p} {N : ℕ} (hN : 0 < N)
    (c : spec.Chip N) (k : Fin 2) : (c.double k).fineVertex hN = c.fineVertex hN := rfl

/-- **The per-point cost bound.**  On an odd refinement `N = 2 * m + 1` the two
chips of a doubled interior point have total signed cost at most `m = (N-1)/2`
in absolute value. -/
theorem abs_sum_signedCost_double {n p : ℕ} {spec : Spec n p} {N m : ℕ}
    (hm : N = 2 * m + 1) (c : spec.Chip N) :
    |∑ k : Fin 2, (c.double k).signedCost| ≤ (m : ℤ) := by
  have hpos := c.offset_pos
  have hlt := c.offset_lt
  have h0 : (c.double 0).signedCost
      = if 3 * N ≤ 4 * c.offset then (N : ℤ) - (c.offset : ℤ) else -(c.offset : ℤ) := by
    simp only [double, signedCost, reround_toRight, reround_offset]
    norm_num
  have h1 : (c.double 1).signedCost
      = if N < 4 * c.offset then (N : ℤ) - (c.offset : ℤ) else -(c.offset : ℤ) := by
    simp only [double, signedCost, reround_toRight, reround_offset]
    norm_num
  rw [Fin.sum_univ_two, h0, h1, abs_le]
  split_ifs <;> omega

end Chip

/-! ## Descending a doubled degree-two divisor -/

private theorem embed_sum {n p : ℕ} (spec : Spec n p) (N : ℕ) (hN : 0 < N)
    {ι : Type*} [Fintype ι] (f : ι → CFDiv spec.graph) :
    spec.embed N hN (∑ i, f i) = ∑ i, spec.embed N hN (f i) := by
  funext y
  simp only [embed, Finset.sum_apply]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with h
  · rfl
  · exact Finset.sum_const_zero.symm

private theorem effective_sum_one_chip {G : CFGraph} {ι : Type*} [Fintype ι] (v : ι → G.V) :
    effective (∑ i, oneChip (v i) : CFDiv G) := by
  intro w
  rw [Finset.sum_apply]
  exact Finset.sum_nonneg fun i _ => eff_one_chip (v i) w

private theorem deg_sum_one_chip {G : CFGraph} {ι : Type*} [Fintype ι] (v : ι → G.V) :
    deg (∑ i, oneChip (v i) : CFDiv G) = (Fintype.card ι : ℤ) := by
  rw [map_sum]
  simp

private theorem sum_prod_fin_two {M : Type*} [AddCommMonoid M] {S : Type*} [Fintype S]
    (f : S → M) :
    (∑ q : S × Fin 2, f q.1) = (∑ i : S, f i) + ∑ i : S, f i := by
  rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Fin.sum_univ_two]

/-- **Descent of a doubled degree-two fine divisor, split form.**  The two fine
points have been separated into those that are images of coarse vertices (with
`lefts` the coarse preimages) and those that are genuine interior chips (with
`chips0` the chips).  Each interior point is doubled by `Chip.double`, and the
hypothesis `hbudget` is exactly the grouped signed budget. -/
private theorem exists_coarse_double_of_split {n p : ℕ} (spec : Spec n p) (N : ℕ) (hN : 0 < N)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ys : ι → (spec.scale N hN).Vertex) (r : ℤ)
    (P : ι → Prop) [DecidablePred P]
    (chips0 : {i : ι // P i} → spec.Chip N) (lefts : {i : ι // ¬ P i} → spec.Vertex)
    (hchips : ∀ i : {i : ι // P i}, ys i.1 = (chips0 i).fineVertex hN)
    (hlefts : ∀ i : {i : ι // ¬ P i}, ys i.1 = spec.fineOf N hN (lefts i))
    (hbudget : (∑ i : {i : ι // P i},
      |∑ k : Fin 2, ((chips0 i).double k).signedCost|) < (N : ℤ))
    (hrank : rank (spec.scale N hN).graph
      ((∑ i, oneChip (ys i)) + ∑ i, oneChip (ys i)) ≥ r) :
    ∃ D : CFDiv spec.graph, effective D ∧ deg D = 2 * (Fintype.card ι : ℤ) ∧
      rank spec.graph D ≥ r := by
  refine ⟨(∑ q : {i : ι // ¬ P i} × Fin 2, (oneChip (lefts q.1) : CFDiv spec.graph))
      + spec.coarseChips N (fun q : {i : ι // P i} × Fin 2 => (chips0 q.1).double q.2),
    ?_, ?_, ?_⟩
  · have h₁ := effective_sum_one_chip (G := spec.graph)
      (fun q : {i : ι // ¬ P i} × Fin 2 => lefts q.1)
    have h₂ := effective_sum_one_chip (G := spec.graph)
      (fun q : {i : ι // P i} × Fin 2 => ((chips0 q.1).double q.2).coarseVertex)
    exact fun v => add_nonneg (h₁ v) (h₂ v)
  · have hcard : (Fintype.card {i : ι // P i} : ℤ) + (Fintype.card {i : ι // ¬ P i} : ℤ)
        = (Fintype.card ι : ℤ) := by
      have h := Fintype.sum_subtype_add_sum_subtype P (fun _ : ι => (1 : ℤ))
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
      exact h
    have h₁ : deg (∑ q : {i : ι // ¬ P i} × Fin 2, (oneChip (lefts q.1) : CFDiv spec.graph))
        = (Fintype.card ({i : ι // ¬ P i} × Fin 2) : ℤ) :=
      deg_sum_one_chip (G := spec.graph) (fun q : {i : ι // ¬ P i} × Fin 2 => lefts q.1)
    have h₂ : deg (spec.coarseChips N
          (fun q : {i : ι // P i} × Fin 2 => (chips0 q.1).double q.2))
        = (Fintype.card ({i : ι // P i} × Fin 2) : ℤ) :=
      deg_sum_one_chip (G := spec.graph)
        (fun q : {i : ι // P i} × Fin 2 => ((chips0 q.1).double q.2).coarseVertex)
    rw [map_add, h₁, h₂, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
    push_cast
    linarith
  · -- The grouped budget.
    have hgroup : ∀ q q' : {i : ι // P i} × Fin 2, q.1 = q'.1 →
        ((chips0 q.1).double q.2).coarseStep = ((chips0 q'.1).double q'.2).coarseStep := by
      rintro ⟨i, k⟩ ⟨i', k'⟩ (h : i = i')
      subst h
      rfl
    have hfilter : ∀ i : {i : ι // P i},
        (∑ q ∈ Finset.univ.filter (fun q : {i : ι // P i} × Fin 2 => q.1 = i),
            ((chips0 q.1).double q.2).signedCost)
          = ∑ k : Fin 2, ((chips0 i).double k).signedCost := by
      intro i
      rw [Finset.sum_filter, Fintype.sum_prod_type]
      refine (Finset.sum_eq_single i (fun b _ hb => Finset.sum_eq_zero fun k _ => ite_eq_right hb)
        (fun hc => absurd (Finset.mem_univ i) hc)).trans ?_
      exact Finset.sum_congr rfl fun k _ => ite_eq_left rfl
    have hcost : (∑ step : spec.Step, |spec.stepCost N
        (fun q : {i : ι // P i} × Fin 2 => (chips0 q.1).double q.2) step|) < (N : ℤ) := by
      refine lt_of_le_of_lt
        (spec.sum_abs_stepCost_le_sum_abs_group N
          (fun q : {i : ι // P i} × Fin 2 => (chips0 q.1).double q.2) Prod.fst hgroup) ?_
      refine lt_of_le_of_lt (le_of_eq ?_) hbudget
      exact Finset.sum_congr rfl fun i _ => by rw [hfilter i]
    -- The fine divisor is the embedding of the padding plus the chips.
    have hE : spec.embed N hN (∑ q : {i : ι // ¬ P i} × Fin 2, (oneChip (lefts q.1) : CFDiv
      spec.graph))
        = ∑ q : {i : ι // ¬ P i} × Fin 2, oneChip (ys q.1.1) := by
      rw [embed_sum]
      exact Finset.sum_congr rfl fun q _ => by
        rw [spec.embed_one_chip N hN, ← hlefts q.1]
    have hF : spec.fineChips N hN
          (fun q : {i : ι // P i} × Fin 2 => (chips0 q.1).double q.2)
        = ∑ q : {i : ι // P i} × Fin 2, oneChip (ys q.1.1) := by
      unfold fineChips
      exact Finset.sum_congr rfl fun q _ => by
        rw [Chip.double_fineVertex, ← hchips q.1]
    have hfine : spec.embed N hN (∑ q : {i : ι // ¬ P i} × Fin 2, (oneChip (lefts q.1) : CFDiv
      spec.graph))
          + spec.fineChips N hN
            (fun q : {i : ι // P i} × Fin 2 => (chips0 q.1).double q.2)
        = (∑ i, oneChip (ys i)) + ∑ i, oneChip (ys i) := by
      have hsplit := Fintype.sum_subtype_add_sum_subtype P
        (fun i => (oneChip (ys i) : CFDiv (spec.scale N hN).graph))
      rw [hE, hF,
        sum_prod_fin_two (M := CFDiv (spec.scale N hN).graph)
          (fun i : {i : ι // ¬ P i} => oneChip (ys i.1)),
        sum_prod_fin_two (M := CFDiv (spec.scale N hN).graph)
          (fun i : {i : ι // P i} => oneChip (ys i.1)), ← hsplit]
      abel
    exact spec.rank_ge_of_rank_scale_ge_cost N hN
      (fun q : {i : ι // P i} × Fin 2 => (chips0 q.1).double q.2) _ r hcost
      (by rw [hfine]; exact hrank)

/-- **Descent of a doubled degree-two divisor from an odd refinement.**  If `C`
is effective of degree two on the `N`-fold refinement with `N` odd, and
`rank (2 • C) ≥ r` there, then the coarse graph carries an effective divisor of
degree four with rank at least `r`.  Each of the two points of `C` is doubled,
and the doubled pair is rounded so that its signed cost is at most `(N-1)/2`. -/
theorem rank_ge_of_rank_scale_two_smul_two (hodd : Odd N)
    (C : CFDiv (spec.scale N hN).graph) (hC : effective C) (hdeg : deg C = 2) (r : ℤ)
    (hrank : rank (spec.scale N hN).graph (2 • C) ≥ r) :
    ∃ D : CFDiv spec.graph, effective D ∧ deg D = 4 ∧ rank spec.graph D ≥ r := by
  classical
  obtain ⟨m, hm⟩ := hodd
  obtain ⟨y₁, y₂, hCeq⟩ := exists_chip_pair_of_effective_deg_two _ C hC hdeg
  set ys : Fin 2 → (spec.scale N hN).Vertex := ![y₁, y₂] with hysdef
  have hsum : (∑ i : Fin 2, oneChip (ys i) : CFDiv (spec.scale N hN).graph) = C := by
    rw [Fin.sum_univ_two, hCeq, hysdef]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hrank2 : rank (spec.scale N hN).graph
      ((∑ i : Fin 2, oneChip (ys i)) + ∑ i : Fin 2, oneChip (ys i)) ≥ r := by
    rw [hsum, ← two_nsmul]
    exact hrank
  set P : Fin 2 → Prop := fun i => (spec.roundData N hN (ys i)).isRight = true with hP
  set chips0 : {i : Fin 2 // P i} → spec.Chip N :=
    fun i => (spec.roundData N hN (ys i.1)).getRight i.2 with hchips0
  set lefts : {i : Fin 2 // ¬ P i} → spec.Vertex :=
    fun i => (spec.roundData N hN (ys i.1)).getLeft (Sum.not_isRight.mp i.2) with hleftsdef
  have hchips : ∀ i : {i : Fin 2 // P i}, ys i.1 = (chips0 i).fineVertex hN := fun i =>
    spec.eq_fineVertex_of_roundData_eq_inr N hN
      (Sum.eq_right_iff_getRight_eq.mpr ⟨i.2, rfl⟩)
  have hlefts : ∀ i : {i : Fin 2 // ¬ P i}, ys i.1 = spec.fineOf N hN (lefts i) := fun i =>
    spec.eq_fineOf_of_roundData_eq_inl N hN
      (Sum.eq_left_iff_getLeft_eq.mpr ⟨Sum.not_isRight.mp i.2, rfl⟩)
  have hcardle : Fintype.card {i : Fin 2 // P i} ≤ 2 := by
    have := Fintype.card_subtype_le P
    simpa using this
  have hbudget : (∑ i : {i : Fin 2 // P i},
      |∑ k : Fin 2, ((chips0 i).double k).signedCost|) < (N : ℤ) := by
    have hterm : ∀ i : {i : Fin 2 // P i},
        |∑ k : Fin 2, ((chips0 i).double k).signedCost| ≤ (m : ℤ) := fun i =>
      Chip.abs_sum_signedCost_double (by omega) (chips0 i)
    have hle : (∑ i : {i : Fin 2 // P i},
        |∑ k : Fin 2, ((chips0 i).double k).signedCost|)
        ≤ (Fintype.card {i : Fin 2 // P i} : ℤ) * (m : ℤ) := by
      calc (∑ i : {i : Fin 2 // P i}, |∑ k : Fin 2, ((chips0 i).double k).signedCost|)
          ≤ ∑ _i : {i : Fin 2 // P i}, (m : ℤ) := Finset.sum_le_sum fun i _ => hterm i
        _ = (Fintype.card {i : Fin 2 // P i} : ℤ) * (m : ℤ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            rfl
    have hcard' : (Fintype.card {i : Fin 2 // P i} : ℤ) ≤ 2 := by exact_mod_cast hcardle
    have hmul : (Fintype.card {i : Fin 2 // P i} : ℤ) * (m : ℤ) ≤ 2 * (m : ℤ) :=
      mul_le_mul_of_nonneg_right hcard' (by positivity)
    have hfinal : (2 : ℤ) * (m : ℤ) < (N : ℤ) := by omega
    linarith
  obtain ⟨D, hDeff, hDdeg, hDrank⟩ :=
    exists_coarse_double_of_split spec N hN ys r P chips0 lefts hchips hlefts hbudget hrank2
  refine ⟨D, hDeff, ?_, hDrank⟩
  rw [hDdeg]
  simp

end Utilities.Certificate.SubdivisionGraph.Spec

namespace Utilities.Gonality

open Utilities.Certificate Utilities.Certificate.SubdivisionGraph

/-- **An effective square root on an odd subdivision gives `w^1_4 ≥ 1`.**  If
some odd regular subdivision of `G` carries an effective degree-two divisor `C`
with `rank (2 • C) ≥ 1`, then `G` itself carries a divisor of degree four and
rank at least one.  For a genus-six graph this applies to any degree-two class
`C` with `2 • C` linearly equivalent to a specialized tetragonal class. -/
theorem bnExists_one_four_of_effective_square_root (G : CFGraph) {N : ℕ} (hN : 0 < N)
    (hodd : Odd N) (C : CFDiv (regularSubdivision G N hN)) (hC : effective C)
    (hdeg : deg C = 2) (hrank : rank (regularSubdivision G N hN) (2 • C) ≥ 1) :
    BNExists G 1 4 := by
  obtain ⟨D, _hDeff, hDdeg, hDrank⟩ :=
    (UnitSubdivisionPresentation.spec G).rank_ge_of_rank_scale_two_smul_two N hN hodd
      C hC hdeg 1 hrank
  exact ((UnitSubdivisionPresentation.laplacianEquiv G).bnExists_iff 1 4).mpr
    ⟨D, hDdeg, hDrank⟩

end Utilities.Gonality
