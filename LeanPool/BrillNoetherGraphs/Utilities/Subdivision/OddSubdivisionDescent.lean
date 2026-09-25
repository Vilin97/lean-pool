/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionChipDescentMain
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.UnitSubdivisionPresentation
public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.BrillNoetherRank
public import Mathlib.Tactic

/-!
# Odd subdivision descent for Brill--Noether rank

`Utilities/Subdivision/SubdivisionChipDescent.lean` rounds finitely many
moving chips on an `N`-fold refinement to chosen ends of their coarse steps,
provided the total rounding distance is less than `N`.  This file chooses the
ends: every fine vertex is rounded to its *nearest* coarse vertex, at distance
at most `N / 2`, and strictly less than `N / 2` when `N` is odd.  Two chips on
an odd refinement therefore always fit the budget.

The consequence for the discrete Brill--Noether rank `w^r_d` of
`Utilities/Foundations/BrillNoetherRank.lean` is:

* `bnRankGe_of_bnRankGe_scale_two`: if `d = r + k + 2` and `N` is odd, then
  `w^r_d(σ_N G) ≥ k` implies `w^r_d(G) ≥ k`, for a subdivision-presented `G`;
* `Utilities.Gonality.bnRankGe_of_bnRankGe_regularSubdivision`: the same for
  an arbitrary finite loopless multigraph and its regular subdivision
  `σ_N G`;
* `Utilities.Gonality.bnRankGe_one_four_of_exists_odd_regularSubdivision`:
  the genus-five-relevant instance
  `(∃ odd N, w^1_4(σ_N G) ≥ 1) → w^1_4(G) ≥ 1`;
* `Utilities.Gonality.bnRankGe_one_four_of_oddPairWitness`: the pairwise
  form, in which the odd scale may depend on the prescribed pair of vertices
  and only the pencil through that pair is required on the refinement.

None of this needs a genus hypothesis or any algebraic-geometric input.  The
*production* of an odd refinement carrying `w^1_4 ≥ 1` (or of the pairwise
witnesses) for a genus-five graph is a separate matter, discussed in the
private research notes; this file proves only the descent.
-/

@[expose] public section

namespace Utilities.Certificate.SubdivisionGraph.Spec

open Finset

variable {n p : ℕ} (spec : Spec n p) (N : ℕ) (hN : 0 < N)

/-! ## Rounding every fine vertex to its nearest coarse vertex -/

/-- Classify a fine vertex: either it is the image of a coarse vertex, or it
is a chip strictly inside a coarse step, rounded to the nearer end (ties go
left). -/
def roundData : (spec.scale N hN).Vertex → spec.Vertex ⊕ spec.Chip N
  | Sum.inl vertex => Sum.inl (Sum.inl vertex)
  | Sum.inr ⟨edge, j⟩ =>
      if hr : (j.val + 1) % N = 0 then
        Sum.inl (spec.interiorVertex edge ⟨(j.val + 1) / N - 1, by
          have hlt : j.val + 1 < N * spec.length edge := by
            have := j.isLt
            simp only [scale_length] at this
            omega
          have hdiv : (j.val + 1) / N < spec.length edge :=
            (Nat.div_lt_iff_lt_mul hN).mpr (by rw [Nat.mul_comm]; exact hlt)
          have hpos : 0 < (j.val + 1) / N := by
            rcases Nat.eq_zero_or_pos ((j.val + 1) / N) with h | h
            · have := Nat.mod_add_div (j.val + 1) N
              rw [hr, h] at this
              omega
            · exact h
          omega⟩)
      else
        Sum.inr
          { edge := edge
            step := (j.val + 1) / N
            step_lt := by
              have hlt : j.val + 1 < N * spec.length edge := by
                have := j.isLt
                simp only [scale_length] at this
                omega
              exact (Nat.div_lt_iff_lt_mul hN).mpr (by rw [Nat.mul_comm]; exact hlt)
            offset := (j.val + 1) % N
            offset_pos := Nat.pos_of_ne_zero hr
            offset_lt := Nat.mod_lt _ hN
            toRight := decide (N < 2 * ((j.val + 1) % N)) }

/-- The nearest coarse vertex of a fine vertex (ties rounded to the left). -/
def nearest (y : (spec.scale N hN).Vertex) : spec.Vertex :=
  Sum.elim id Chip.coarseVertex (spec.roundData N hN y)

/-- The fine distance from a fine vertex to its nearest coarse vertex. -/
def roundDist (y : (spec.scale N hN).Vertex) : ℕ :=
  Sum.elim (fun _ => 0) Chip.distance (spec.roundData N hN y)

/-- The fine vertex of a chip, read off as an interior vertex of the refinement:
the chip at fine offset `N * step + offset` is the interior vertex indexed by
`N * step + offset - 1`. -/
private theorem fineVertex_eq_inr (c : spec.Chip N)
    (k : Fin ((spec.scale N hN).length c.edge - 1))
    (hk : k.val + 1 = N * c.step + c.offset) :
    c.fineVertex hN = Sum.inr ⟨c.edge, k⟩ := by
  have hoffpos := c.offset_pos
  have hofflt := c.offset_lt
  have hposlt : N * c.step + c.offset < N * spec.length c.edge := by
    have h1 : N * (c.step + 1) ≤ N * spec.length c.edge :=
      Nat.mul_le_mul_left N c.step_lt
    rw [Nat.mul_succ] at h1
    omega
  unfold Chip.fineVertex pathVertex
  rw [dite_eq_right (by show ¬ N * c.step + c.offset = 0; omega),
    dite_eq_right (by show ¬ N * c.step + c.offset = N * spec.length c.edge; omega)]
  simp only [interiorVertex, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq, true_and]
  apply Fin.ext
  show N * c.step + c.offset - 1 = k.val
  omega

/-- A chip whose `toRight` flag is the nearest-end decision is within `N / 2`
of the end it is rounded to. -/
private theorem two_mul_distance_le_of_toRight (c : spec.Chip N)
    (h : c.toRight = decide (N < 2 * c.offset)) : 2 * c.distance ≤ N := by
  have hlt := c.offset_lt
  unfold Chip.distance
  split_ifs with hif
  · rw [h] at hif
    have hgt : N < 2 * c.offset := of_decide_eq_true hif
    omega
  · rw [h] at hif
    have hle : ¬ N < 2 * c.offset := fun hc => hif (decide_eq_true hc)
    omega

theorem eq_fineOf_of_roundData_eq_inl {y : (spec.scale N hN).Vertex} {x : spec.Vertex}
    (h : spec.roundData N hN y = Sum.inl x) : y = spec.fineOf N hN x := by
  rcases y with v | ⟨e, j⟩
  · have hx : Sum.inl v = x := Sum.inl.inj h
    subst hx
    rfl
  · simp only [roundData] at h
    by_cases hr : (j.val + 1) % N = 0
    · rw [dite_eq_left hr] at h
      have hx := Sum.inl.inj h
      subst hx
      have hdvd : N ∣ (j.val + 1) := Nat.dvd_of_mod_eq_zero hr
      have hmul : N * ((j.val + 1) / N) = j.val + 1 := Nat.mul_div_cancel' hdvd
      have hpos : 0 < (j.val + 1) / N := by
        rcases Nat.eq_zero_or_pos ((j.val + 1) / N) with h0 | h0
        · rw [h0] at hmul; omega
        · exact h0
      simp only [interiorVertex, fineOf, Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq, true_and]
      apply Fin.ext
      show j.val = N * ((j.val + 1) / N - 1 + 1) - 1
      rw [Nat.sub_add_cancel hpos, hmul]
      omega
    · rw [dite_eq_right hr] at h
      exact absurd h Sum.inr_ne_inl

theorem eq_fineVertex_of_roundData_eq_inr {y : (spec.scale N hN).Vertex} {c : spec.Chip N}
    (h : spec.roundData N hN y = Sum.inr c) : y = c.fineVertex hN := by
  rcases y with v | ⟨e, j⟩
  · exact absurd h Sum.inl_ne_inr
  · simp only [roundData] at h
    by_cases hr : (j.val + 1) % N = 0
    · rw [dite_eq_left hr] at h
      exact absurd h Sum.inl_ne_inr
    · rw [dite_eq_right hr] at h
      have hc := Sum.inr.inj h
      subst hc
      symm
      apply spec.fineVertex_eq_inr
      exact (Nat.div_add_mod (j.val + 1) N).symm

theorem two_mul_distance_le_of_roundData_eq_inr {y : (spec.scale N hN).Vertex}
    {c : spec.Chip N} (h : spec.roundData N hN y = Sum.inr c) :
    2 * c.distance ≤ N := by
  rcases y with v | ⟨e, j⟩
  · exact absurd h Sum.inl_ne_inr
  · simp only [roundData] at h
    by_cases hr : (j.val + 1) % N = 0
    · rw [dite_eq_left hr] at h
      exact absurd h Sum.inl_ne_inr
    · rw [dite_eq_right hr] at h
      have hc := Sum.inr.inj h
      subst hc
      exact spec.two_mul_distance_le_of_toRight N _ rfl

theorem two_mul_roundDist_le (y : (spec.scale N hN).Vertex) :
    2 * spec.roundDist N hN y ≤ N := by
  unfold roundDist
  cases hcase : spec.roundData N hN y with
  | inl x => simp only [Sum.elim_inl]; omega
  | inr c =>
      simp only [Sum.elim_inr]
      exact spec.two_mul_distance_le_of_roundData_eq_inr N hN hcase

theorem two_mul_roundDist_lt (hodd : Odd N) (y : (spec.scale N hN).Vertex) :
    2 * spec.roundDist N hN y < N := by
  obtain ⟨m, hm⟩ := hodd
  have hle := spec.two_mul_roundDist_le N hN y
  omega

theorem embed_one_chip (x : spec.Vertex) :
    spec.embed N hN (oneChip x) = oneChip (spec.fineOf N hN x) := by
  classical
  funext y
  unfold embed
  rw [Finset.sum_eq_single x]
  · by_cases hxy : spec.fineOf N hN x = y
    · rw [ite_eq_left hxy, one_chip_apply_v, ← hxy, one_chip_apply_v]
    · rw [ite_eq_right hxy]
      exact (one_chip_apply_other' _ _ (fun hc => hxy hc.symm)).symm
  · intro x' _ hne
    have hzero : (oneChip x : CFDiv spec.graph) x' = 0 := by
      simp only [oneChip]
      rw [ite_eq_right hne]
    rw [hzero]
    split_ifs <;> rfl
  · intro hmem
    exact absurd (Finset.mem_univ x) hmem

private theorem embed_zero : spec.embed N hN 0 = 0 := by
  funext y
  unfold embed
  simp

private theorem embed_finset_sum {ι : Type*} (s : Finset ι) (D : ι → CFDiv spec.graph) :
    spec.embed N hN (∑ i ∈ s, D i) = ∑ i ∈ s, spec.embed N hN (D i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using spec.embed_zero N hN
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, spec.embed_add N hN, ih]

/-- The descent with nearest rounding, once the index type has been split into
the fine vertices that already come from the coarse graph and those that are
genuine chips. -/
private theorem rank_ge_nearest_of_split {ι : Type*} [Fintype ι]
    (ys : ι → (spec.scale N hN).Vertex) (D₀ : CFDiv spec.graph) (r : ℤ)
    (P : ι → Prop) [DecidablePred P]
    (chips : {i : ι // P i} → spec.Chip N) (lefts : {i : ι // ¬ P i} → spec.Vertex)
    (hchips : ∀ i : {i : ι // P i}, spec.roundData N hN (ys i.1) = Sum.inr (chips i))
    (hlefts : ∀ i : {i : ι // ¬ P i}, spec.roundData N hN (ys i.1) = Sum.inl (lefts i))
    (hbudget : (∑ i, (spec.roundDist N hN (ys i) : ℤ)) < N)
    (hrank : rank (spec.scale N hN).graph
      (spec.embed N hN D₀ + ∑ i, oneChip (ys i)) ≥ r) :
    rank spec.graph (D₀ + ∑ i, oneChip (spec.nearest N hN (ys i))) ≥ r := by
  have hys_right : ∀ i : {i : ι // P i}, ys i.1 = (chips i).fineVertex hN :=
    fun i => spec.eq_fineVertex_of_roundData_eq_inr N hN (hchips i)
  have hys_left : ∀ i : {i : ι // ¬ P i}, ys i.1 = spec.fineOf N hN (lefts i) :=
    fun i => spec.eq_fineOf_of_roundData_eq_inl N hN (hlefts i)
  have hnear_right : ∀ i : {i : ι // P i},
      spec.nearest N hN (ys i.1) = (chips i).coarseVertex := by
    intro i
    unfold nearest
    rw [hchips i]
    rfl
  have hnear_left : ∀ i : {i : ι // ¬ P i},
      spec.nearest N hN (ys i.1) = lefts i := by
    intro i
    unfold nearest
    rw [hlefts i]
    rfl
  have hdist_right : ∀ i : {i : ι // P i},
      spec.roundDist N hN (ys i.1) = (chips i).distance := by
    intro i
    unfold roundDist
    rw [hchips i]
    rfl
  have hdist_left : ∀ i : {i : ι // ¬ P i}, spec.roundDist N hN (ys i.1) = 0 := by
    intro i
    unfold roundDist
    rw [hlefts i]
    rfl
  -- The rounding budget is carried entirely by the genuine chips.
  have hbudget' : (∑ i : {i : ι // P i}, ((chips i).distance : ℤ)) < N := by
    rw [← Fintype.sum_subtype_add_sum_subtype P
      (fun i => (spec.roundDist N hN (ys i) : ℤ))] at hbudget
    have h1 : (∑ i : {i : ι // P i}, (spec.roundDist N hN (ys i.1) : ℤ))
        = ∑ i : {i : ι // P i}, ((chips i).distance : ℤ) :=
      Finset.sum_congr rfl (fun i _ => by rw [hdist_right i])
    have h2 : (∑ i : {i : ι // ¬ P i}, (spec.roundDist N hN (ys i.1) : ℤ)) = 0 :=
      Finset.sum_eq_zero (fun i _ => by rw [hdist_left i]; norm_num)
    rw [h1, h2, add_zero] at hbudget
    exact hbudget
  -- The fine divisor is the embedding of the padded coarse divisor plus the chips.
  have hfineEq : spec.embed N hN D₀ + ∑ i, oneChip (ys i)
      = spec.embed N hN (D₀ + ∑ i : {i : ι // ¬ P i}, oneChip (lefts i))
        + spec.fineChips N hN chips := by
    have hE : (∑ i : {i : ι // ¬ P i}, spec.embed N hN (oneChip (lefts i)))
        = ∑ i : {i : ι // ¬ P i}, oneChip (ys i.1) :=
      Finset.sum_congr rfl (fun i _ => by
        rw [spec.embed_one_chip N hN, ← hys_left i])
    have hF : spec.fineChips N hN chips = ∑ i : {i : ι // P i}, oneChip (ys i.1) := by
      unfold fineChips
      exact Finset.sum_congr rfl (fun i _ => by rw [hys_right i])
    have hsplit := Fintype.sum_subtype_add_sum_subtype P
      (fun i => (oneChip (ys i) : CFDiv (spec.scale N hN).graph))
    rw [spec.embed_add N hN, spec.embed_finset_sum N hN, hE, hF, ← hsplit]
    abel
  -- The coarse divisor is the padded coarse divisor plus the rounded chips.
  have hcoarseEq : D₀ + ∑ i, oneChip (spec.nearest N hN (ys i))
      = (D₀ + ∑ i : {i : ι // ¬ P i}, oneChip (lefts i))
        + spec.coarseChips N chips := by
    have hC : spec.coarseChips N chips
        = ∑ i : {i : ι // P i}, oneChip (spec.nearest N hN (ys i.1)) := by
      unfold coarseChips
      exact Finset.sum_congr rfl (fun i _ => by rw [hnear_right i])
    have hL : (∑ i : {i : ι // ¬ P i}, oneChip (lefts i) : CFDiv spec.graph)
        = ∑ i : {i : ι // ¬ P i}, oneChip (spec.nearest N hN (ys i.1)) :=
      Finset.sum_congr rfl (fun i _ => by rw [hnear_left i])
    have hsplit := Fintype.sum_subtype_add_sum_subtype P
      (fun i => (oneChip (spec.nearest N hN (ys i)) : CFDiv spec.graph))
    rw [hC, hL, ← hsplit]
    abel
  rw [hcoarseEq]
  refine spec.rank_ge_of_rank_scale_ge N hN chips _ r hbudget' ?_
  rw [← hfineEq]
  exact hrank

/-- **Descent of rank with nearest rounding.**  Any family of fine chips whose
total nearest-rounding distance is less than `N` may be rounded to nearest
coarse vertices without lowering any rank bound of the embedded divisor plus
the chips. -/
theorem rank_ge_of_rank_scale_ge_nearest {ι : Type*} [Fintype ι]
    (ys : ι → (spec.scale N hN).Vertex) (D₀ : CFDiv spec.graph) (r : ℤ)
    (hbudget : (∑ i, (spec.roundDist N hN (ys i) : ℤ)) < N)
    (hrank : rank (spec.scale N hN).graph
      (spec.embed N hN D₀ + ∑ i, oneChip (ys i)) ≥ r) :
    rank spec.graph (D₀ + ∑ i, oneChip (spec.nearest N hN (ys i))) ≥ r :=
  spec.rank_ge_nearest_of_split N hN ys D₀ r
    (fun i => (spec.roundData N hN (ys i)).isRight = true)
    (fun i => (spec.roundData N hN (ys i.1)).getRight i.2)
    (fun i => (spec.roundData N hN (ys i.1)).getLeft (Sum.not_isRight.mp i.2))
    (fun i => Sum.eq_right_iff_getRight_eq.mpr ⟨i.2, rfl⟩)
    (fun i => Sum.eq_left_iff_getLeft_eq.mpr ⟨Sum.not_isRight.mp i.2, rfl⟩)
    hbudget hrank

/-! ## Brill--Noether rank descends along odd refinements -/

/-- **Rounding a fine degree-two completion.**  An effective degree-two fine
divisor completing `embed E` to rank at least `r` rounds to an effective
degree-two coarse divisor completing `E` to rank at least `r`, whenever `N` is
odd. -/
private theorem exists_coarse_completion_two (hodd : Odd N) {r : ℤ}
    (E : CFDiv spec.graph) (F : CFDiv (spec.scale N hN).graph)
    (hFeff : effective F) (hFdeg : deg F = 2)
    (hrank : rank (spec.scale N hN).graph (spec.embed N hN E + F) ≥ r) :
    ∃ B : CFDiv spec.graph, effective B ∧ deg B = 2 ∧ rank spec.graph (E + B) ≥ r := by
  obtain ⟨y₁, y₂, hF⟩ := exists_chip_pair_of_effective_deg_two _ F hFeff hFdeg
  subst hF
  have hsum2 : (∑ i : Fin 2, oneChip (![y₁, y₂] i) : CFDiv (spec.scale N hN).graph)
      = oneChip y₁ + oneChip y₂ := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hrank2 : rank (spec.scale N hN).graph
      (spec.embed N hN E + ∑ i : Fin 2, oneChip (![y₁, y₂] i)) ≥ r := by
    rw [hsum2]
    exact hrank
  have hbudget : (∑ i : Fin 2, (spec.roundDist N hN (![y₁, y₂] i) : ℤ)) < N := by
    have h1 := spec.two_mul_roundDist_lt N hN hodd y₁
    have h2 := spec.two_mul_roundDist_lt N hN hodd y₂
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have hcoarse := spec.rank_ge_of_rank_scale_ge_nearest N hN ![y₁, y₂] E r hbudget hrank2
  rw [Fin.sum_univ_two] at hcoarse
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hcoarse
  have heff : effective (oneChip (spec.nearest N hN y₁) + oneChip (spec.nearest N hN y₂)
      : CFDiv spec.graph) := by
    intro v
    exact add_nonneg (eff_one_chip (spec.nearest N hN y₁) v)
      (eff_one_chip (spec.nearest N hN y₂) v)
  have hdegB : deg (oneChip (spec.nearest N hN y₁) + oneChip (spec.nearest N hN y₂)
      : CFDiv spec.graph) = 2 := by
    rw [deg.map_add, deg_one_chip, deg_one_chip]
    norm_num
  exact ⟨_, heff, hdegB, hcoarse⟩

/-- **Rounding a fine degree-one completion.**  A single fine chip completing
`embed E` to rank at least `r` rounds to a single coarse chip, for every
`N ≥ 1`. -/
private theorem exists_coarse_completion_one {r : ℤ}
    (E : CFDiv spec.graph) (F : CFDiv (spec.scale N hN).graph)
    (hFeff : effective F) (hFdeg : deg F = 1)
    (hrank : rank (spec.scale N hN).graph (spec.embed N hN E + F) ≥ r) :
    ∃ B : CFDiv spec.graph, effective B ∧ deg B = 1 ∧ rank spec.graph (E + B) ≥ r := by
  obtain ⟨y, hF⟩ := effective_degree_one_eq_one_chip hFeff hFdeg
  subst hF
  have hsum1 : (∑ i : Fin 1, oneChip (![y] i) : CFDiv (spec.scale N hN).graph)
      = oneChip y := by
    rw [Fin.sum_univ_one]
    simp only [Matrix.cons_val_zero]
  have hrank1 : rank (spec.scale N hN).graph
      (spec.embed N hN E + ∑ i : Fin 1, oneChip (![y] i)) ≥ r := by
    rw [hsum1]
    exact hrank
  have hbudget : (∑ i : Fin 1, (spec.roundDist N hN (![y] i) : ℤ)) < N := by
    have h1 := spec.two_mul_roundDist_le N hN y
    rw [Fin.sum_univ_one]
    simp only [Matrix.cons_val_zero]
    omega
  have hcoarse := spec.rank_ge_of_rank_scale_ge_nearest N hN ![y] E r hbudget hrank1
  rw [Fin.sum_univ_one] at hcoarse
  simp only [Matrix.cons_val_zero] at hcoarse
  exact ⟨oneChip (spec.nearest N hN y), eff_one_chip _, deg_one_chip _, hcoarse⟩

/-- **Two residual chips, odd scale.**  If `d = r + k + 2` and `N` is odd, then
`w^r_d(σ_N) ≥ k` implies `w^r_d ≥ k` on the coarse graph. -/
theorem bnRankGe_of_bnRankGe_scale_two (hodd : Odd N) {r d k : ℤ} (hd : d = r + k + 2)
    (h : BNRankGe (spec.scale N hN).graph r d k) : BNRankGe spec.graph r d k := by
  intro E hE hdeg
  obtain ⟨D', _hD'eff, hD'deg, hD'rank, hres⟩ :=
    (bnRankGe_iff_contained _ r d k).mp h (spec.embed N hN E)
      (spec.effective_embed N hN hE) (by rw [spec.deg_embed N hN, hdeg])
  have hFdeg : deg (D' - spec.embed N hN E) = 2 := by
    rw [deg.map_sub, hD'deg, spec.deg_embed N hN, hdeg, hd]
    ring
  have hrank' : rank (spec.scale N hN).graph
      (spec.embed N hN E + (D' - spec.embed N hN E)) ≥ r := by
    rw [show spec.embed N hN E + (D' - spec.embed N hN E) = D' by abel]
    exact hD'rank
  obtain ⟨B, hBeff, hBdeg, hBrank⟩ :=
    spec.exists_coarse_completion_two N hN hodd E _ hres hFdeg hrank'
  refine ⟨E + B, ?_, hBrank, ?_⟩
  · rw [deg.map_add, hdeg, hBdeg, hd]
  · rw [show E + B - E = B by abel]
    exact winnable_of_effective spec.graph _ hBeff

/-- **One residual chip, any scale.**  If `d = r + k + 1`, then `w^r_d(σ_N) ≥ k`
implies `w^r_d ≥ k` on the coarse graph for every `N ≥ 1`. -/
theorem bnRankGe_of_bnRankGe_scale_one {r d k : ℤ} (hd : d = r + k + 1)
    (h : BNRankGe (spec.scale N hN).graph r d k) : BNRankGe spec.graph r d k := by
  intro E hE hdeg
  obtain ⟨D', _hD'eff, hD'deg, hD'rank, hres⟩ :=
    (bnRankGe_iff_contained _ r d k).mp h (spec.embed N hN E)
      (spec.effective_embed N hN hE) (by rw [spec.deg_embed N hN, hdeg])
  have hFdeg : deg (D' - spec.embed N hN E) = 1 := by
    rw [deg.map_sub, hD'deg, spec.deg_embed N hN, hdeg, hd]
    ring
  have hrank' : rank (spec.scale N hN).graph
      (spec.embed N hN E + (D' - spec.embed N hN E)) ≥ r := by
    rw [show spec.embed N hN E + (D' - spec.embed N hN E) = D' by abel]
    exact hD'rank
  obtain ⟨B, hBeff, hBdeg, hBrank⟩ :=
    spec.exists_coarse_completion_one N hN E _ hres hFdeg hrank'
  refine ⟨E + B, ?_, hBrank, ?_⟩
  · rw [deg.map_add, hdeg, hBdeg, hd]
  · rw [show E + B - E = B by abel]
    exact winnable_of_effective spec.graph _ hBeff

end Utilities.Certificate.SubdivisionGraph.Spec

namespace Utilities.Gonality

open Utilities.Certificate Utilities.Certificate.SubdivisionGraph

/-- The image of an original vertex of `G` in its regular subdivision
`σ_N G`. -/
noncomputable def regularSubdivisionVertex (G : CFGraph) (N : ℕ) (hN : 0 < N)
    (v : G.V) : (regularSubdivision G N hN).V :=
  (UnitSubdivisionPresentation.spec G).fineOf N hN
    (UnitSubdivisionPresentation.graphVertexEquiv G v)

/-- **Odd subdivision descent for Brill--Noether rank, two residual chips.**
For every finite loopless multigraph `G`, odd `N`, and `d = r + k + 2`,
`w^r_d(σ_N G) ≥ k` implies `w^r_d(G) ≥ k`. -/
theorem bnRankGe_of_bnRankGe_regularSubdivision (G : CFGraph) {N : ℕ} (hN : 0 < N)
    (hodd : Odd N) {r d k : ℤ} (hd : d = r + k + 2)
    (h : BNRankGe (regularSubdivision G N hN) r d k) : BNRankGe G r d k := by
  have hspec : BNRankGe ((UnitSubdivisionPresentation.spec G).scale N hN).graph r d k := h
  have hcoarse :=
    (UnitSubdivisionPresentation.spec G).bnRankGe_of_bnRankGe_scale_two N hN hodd hd hspec
  exact ((UnitSubdivisionPresentation.laplacianEquiv G).bnRankGe_iff r d k).mp hcoarse

/-- **The genus-five descent statement.**  If some odd regular subdivision of
`G` has `w^1_4 ≥ 1`, so does `G` itself.  No genus hypothesis is needed. -/
theorem bnRankGe_one_four_of_exists_odd_regularSubdivision (G : CFGraph)
    (h : ∃ (N : ℕ) (hN : 0 < N), Odd N ∧ BNRankGe (regularSubdivision G N hN) 1 4 1) :
    BNRankGe G 1 4 1 := by
  obtain ⟨N, hN, hodd, hrank⟩ := h
  exact bnRankGe_of_bnRankGe_regularSubdivision G hN hodd (by norm_num) hrank

/-- **The odd pair witness.**  Every pair of original vertices `x, y` (equal
or not) admits, on some odd regular subdivision depending on the pair, an
effective degree-two completion of `x + y` to a divisor of rank at least
one.  This is the exact combinatorial input that the algebraic degree-five
argument of the research notes is meant to produce for genus-five graphs. -/
def OddPairWitness (G : CFGraph) : Prop :=
  ∀ x y : G.V, ∃ (N : ℕ) (hN : 0 < N), Odd N ∧
    ∃ F : CFDiv (regularSubdivision G N hN), effective F ∧ deg F = 2 ∧
      rank (regularSubdivision G N hN)
        (oneChip (regularSubdivisionVertex G N hN x) +
          oneChip (regularSubdivisionVertex G N hN y) + F) ≥ 1

/-- **The pairwise form of the descent.**  An odd pair witness already gives
`w^1_4(G) ≥ 1`; the odd scale may depend on the pair, and only the pencil
through that pair is required on the refinement. -/
theorem bnRankGe_one_four_of_oddPairWitness (G : CFGraph) (h : OddPairWitness G) :
    BNRankGe G 1 4 1 := by
  refine ((UnitSubdivisionPresentation.laplacianEquiv G).bnRankGe_iff 1 4 1).mp ?_
  intro E hE hdeg
  obtain ⟨a, b, hEab⟩ :=
    exists_chip_pair_of_effective_deg_two _ E hE (by rw [hdeg]; norm_num)
  obtain ⟨N, hN, hodd, F, hFeff, hFdeg, hFrank⟩ :=
    h ((UnitSubdivisionPresentation.graphVertexEquiv G).symm a)
      ((UnitSubdivisionPresentation.graphVertexEquiv G).symm b)
  have hva : regularSubdivisionVertex G N hN
      ((UnitSubdivisionPresentation.graphVertexEquiv G).symm a)
      = (UnitSubdivisionPresentation.spec G).fineOf N hN a := by
    unfold regularSubdivisionVertex
    rw [Equiv.apply_symm_apply]
  have hvb : regularSubdivisionVertex G N hN
      ((UnitSubdivisionPresentation.graphVertexEquiv G).symm b)
      = (UnitSubdivisionPresentation.spec G).fineOf N hN b := by
    unfold regularSubdivisionVertex
    rw [Equiv.apply_symm_apply]
  rw [hva, hvb] at hFrank
  have hembed : (UnitSubdivisionPresentation.spec G).embed N hN E
      = oneChip ((UnitSubdivisionPresentation.spec G).fineOf N hN a)
        + oneChip ((UnitSubdivisionPresentation.spec G).fineOf N hN b) := by
    rw [hEab, Spec.embed_add, Spec.embed_one_chip, Spec.embed_one_chip]
  obtain ⟨B, hBeff, hBdeg, hBrank⟩ :=
    (UnitSubdivisionPresentation.spec G).exists_coarse_completion_two N hN hodd
      (r := 1) E F hFeff hFdeg (by rw [hembed]; exact hFrank)
  refine ⟨E + B, ?_, hBrank, ?_⟩
  · rw [deg.map_add, hdeg, hBdeg]
    norm_num
  · rw [show E + B - E = B by abel]
    exact winnable_of_effective _ _ hBeff

end Utilities.Gonality
