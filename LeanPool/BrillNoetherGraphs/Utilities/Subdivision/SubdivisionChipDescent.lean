/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SlopeScript
public import LeanPool.BrillNoetherGraphs.Utilities.Gonality.GonalityTransport
public import LeanPool.BrillNoetherGraphs.Utilities.Foundations.CommonOffsetRounding
public import Mathlib.Tactic

/-!
# Descent of winnability and rank from a regular subdivision

Let `spec` present a finite loopless multigraph with positive integral slot
lengths, and let `spec.scale N` be its uniform `N`-fold refinement: every unit
step of `spec` becomes a block of `N` unit steps.  A divisor supported on the
coarse vertices embeds into the fine graph, and this file studies what happens
to a fine divisor of the form

  `embed D₀ + x₁ + ⋯ + xₘ`

whose extra chips `xᵢ` sit at fine vertices strictly inside coarse steps.
Each such chip is *rounded* to one end of its coarse step, at a cost equal to
its fine distance to that end.

**Theorem (`winnable_of_winnable_scale`).**  If the total rounding cost is
less than `N`, then winnability of the fine divisor implies winnability of the
rounded coarse divisor `D₀ + z₁ + ⋯ + zₘ`.  The same holds for every rank
lower bound (`rank_ge_of_rank_scale_ge`), because the coarse rank tests embed
into fine rank tests.  The sharper forms `winnable_of_winnable_scale_cost` and
`rank_ge_of_rank_scale_ge_cost` charge each coarse step only the absolute
value of the *signed* sum of its chips' costs (`stepCost`), so chips on one
step rounded in opposite directions cancel each other.

Two chips on an *odd* refinement always satisfy the budget: each is within
`(N - 1) / 2` of its nearest coarse vertex, so the total cost is at most
`N - 1`.  That is the odd-subdivision descent used by
`Utilities/Subdivision/OddSubdivisionDescent.lean` for Brill--Noether rank.

## The proof

Let `σ` be a fine winning script.  Along each coarse step, the fine slopes of
`σ` are nondecreasing except that they may drop by the number of chips at a
fine vertex (`prin_interiorVertex_eq_slopeDifference`).  Consequently the
height difference `B - A` of `σ` across the step, corrected by the signed
rounding cost `δ` of the chips in that step, lies between `N * (s₁ - cL)` and
`N * (s_N + cR)`, where `s₁, s_N` are the first and last fine slopes and
`cL, cR` count the chips rounded to the left and right ends
(`Utilities.BlockSlopeRounding`).

Because `∑ |δ| < N`, `CommonOffsetRounding.exists_common_offset` gives one
residue `κ` with `round κ (B + δ) = round κ B` for every step at once.  The
coarse script `g v := round κ (σ (fineOf v))` therefore has, on every step, a
slope between `s₁ - cL` and `s_N + cR` (`round_sub_bounds`).  Summing the
endpoint slopes at a coarse vertex shows that `g` loses, relative to `σ`, at
most the number of chips rounded to that vertex — exactly what the rounded
chips supply.  No total unimodularity, period lattice, or cycle space is
involved; the argument is one-dimensional on each step.

The proof is a genuine descent theorem and not the "prove it metrically, then
round" fallacy recorded in the research notes: the rounding is justified step
by step from the fine script, and the budget hypothesis is exactly what fails
for two chips at the midpoints of an even refinement.
-/

@[expose] public section

namespace Utilities.Certificate.SubdivisionGraph.Spec

open Finset Utilities.CommonOffsetRounding

variable {n p : ℕ} (spec : Spec n p) (N : ℕ) (hN : 0 < N)

/-! ## Coarse vertices inside the fine graph -/

/-- The fine vertex at fine offset `N * k` of slot `edge`, for a coarse path
position `k`. -/
def scaledPosition (edge : Fin p) (position : spec.PathPosition edge) :
    (spec.scale N hN).PathPosition edge :=
  ⟨N * position.val, by
    have hle : position.val ≤ spec.length edge := by
      have := position.isLt
      omega
    have := Nat.mul_le_mul_left N hle
    simp only [scale_length]
    omega⟩

@[simp] theorem scaledPosition_val (edge : Fin p)
    (position : spec.PathPosition edge) :
    (spec.scaledPosition N hN edge position).val = N * position.val := rfl

/-- The embedding of the coarse vertices into the fine graph: core vertices go
to core vertices, and the interior vertex at coarse offset `j + 1` of a slot
goes to fine offset `N * (j + 1)`. -/
def fineOf : spec.Vertex → (spec.scale N hN).Vertex
  | Sum.inl vertex => Sum.inl vertex
  | Sum.inr ⟨edge, offset⟩ =>
      Sum.inr ⟨edge, ⟨N * (offset.val + 1) - 1, by
        have hlt := offset.isLt
        have h2 : offset.val + 2 ≤ spec.length edge := by omega
        have h3 : N * (offset.val + 1) + N ≤ N * spec.length edge := by
          have := Nat.mul_le_mul_left N h2
          rw [show N * (offset.val + 2) = N * (offset.val + 1) + N by ring] at this
          exact this
        have h5 : N * (offset.val + 1) < N * spec.length edge := by omega
        have h6 : 1 ≤ N * (offset.val + 1) := Nat.mul_pos hN (Nat.succ_pos _)
        show N * (offset.val + 1) - 1 < N * spec.length edge - 1
        omega⟩⟩

@[simp] theorem fineOf_coreVertex (vertex : Fin n) :
    spec.fineOf N hN (spec.coreVertex vertex) =
      (spec.scale N hN).coreVertex vertex := rfl

theorem fineOf_injective : Function.Injective (spec.fineOf N hN) := by
  intro x y hxy
  rcases x with x | ⟨e, j⟩ <;> rcases y with y | ⟨e', j'⟩
  · exact congrArg Sum.inl (Sum.inl.inj hxy)
  · exact absurd hxy Sum.inl_ne_inr
  · exact absurd hxy Sum.inr_ne_inl
  · have hSigma := Sum.inr.inj hxy
    have hEdge : e = e' := congrArg Sigma.fst hSigma
    subst hEdge
    have hVal : N * (j.val + 1) - 1 = N * (j'.val + 1) - 1 :=
      congrArg (fun s : (spec.scale N hN).Interior => s.2.val) hSigma
    have hEq : j.val = j'.val := by
      have hpos : 1 ≤ N * (j.val + 1) := Nat.mul_pos hN (Nat.succ_pos _)
      have hpos' : 1 ≤ N * (j'.val + 1) := Nat.mul_pos hN (Nat.succ_pos _)
      have h1 : N * (j.val + 1) = N * (j'.val + 1) := by omega
      have := Nat.eq_of_mul_eq_mul_left hN h1
      omega
    rw [Fin.ext hEq]

/-- The embedding sends the coarse path vertex at position `k` to the fine
path vertex at position `N * k`. -/
theorem fineOf_pathVertex (edge : Fin p) (position : spec.PathPosition edge) :
    spec.fineOf N hN (spec.pathVertex edge position) =
      (spec.scale N hN).pathVertex edge (spec.scaledPosition N hN edge position) := by
  have hle : position.val ≤ spec.length edge := by
    have := position.isLt
    omega
  by_cases h0 : position.val = 0
  · have hNpos : (spec.scaledPosition N hN edge position).val = 0 := by
      simp [h0]
    unfold pathVertex
    rw [dite_eq_left h0, dite_eq_left hNpos]
    rfl
  · by_cases hlen : position.val = spec.length edge
    · have hNlen : (spec.scaledPosition N hN edge position).val =
          (spec.scale N hN).length edge := by
        simp [hlen]
      unfold pathVertex
      rw [dite_eq_right h0, dite_eq_left hlen, dite_eq_right (by
        rw [hNlen]; exact (Nat.mul_pos hN (spec.length_pos edge)).ne'),
        dite_eq_left hNlen]
      rfl
    · have hpos0 : 0 < position.val := Nat.pos_of_ne_zero h0
      have hposlt : position.val < spec.length edge := lt_of_le_of_ne hle hlen
      have hNpos0 : (spec.scaledPosition N hN edge position).val ≠ 0 := by
        simp only [scaledPosition_val]
        exact (Nat.mul_pos hN hpos0).ne'
      have hNposlen : (spec.scaledPosition N hN edge position).val ≠
          (spec.scale N hN).length edge := by
        simp only [scaledPosition_val, scale_length]
        intro h
        have := Nat.eq_of_mul_eq_mul_left hN h
        omega
      unfold pathVertex
      rw [dite_eq_right h0, dite_eq_right hlen, dite_eq_right hNpos0, dite_eq_right hNposlen]
      simp only [interiorVertex, fineOf, scaledPosition_val, Sum.inr.injEq, Sigma.mk.injEq,
        heq_eq_eq, true_and]
      apply Fin.ext
      show N * (position.val - 1 + 1) - 1 = N * position.val - 1
      rw [Nat.sub_add_cancel hpos0]

/-! ## Embedding coarse divisors -/

/-- Push a coarse divisor forward along `fineOf`: the chips stay on the images
of the coarse vertices and every other fine vertex carries none. -/
def embed (D : CFDiv spec.graph) : CFDiv (spec.scale N hN).graph :=
  fun y => ∑ x : spec.Vertex, if spec.fineOf N hN x = y then D x else 0

theorem embed_apply_fineOf (D : CFDiv spec.graph) (x : spec.Vertex) :
    spec.embed N hN D (spec.fineOf N hN x) = D x := by
  classical
  unfold embed
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hyx
    rw [ite_eq_right]
    intro h
    exact hyx (spec.fineOf_injective N hN h)
  · intro h
    exact absurd (Finset.mem_univ x) h

theorem embed_apply_of_not_mem_range (D : CFDiv spec.graph)
    (y : (spec.scale N hN).Vertex) (hy : y ∉ Set.range (spec.fineOf N hN)) :
    spec.embed N hN D y = 0 := by
  unfold embed
  apply Finset.sum_eq_zero
  intro x _
  rw [ite_eq_right]
  intro h
  exact hy ⟨x, h⟩

theorem embed_add (D E : CFDiv spec.graph) :
    spec.embed N hN (D + E) = spec.embed N hN D + spec.embed N hN E := by
  funext y
  simp only [embed, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

theorem embed_sub (D E : CFDiv spec.graph) :
    spec.embed N hN (D - E) = spec.embed N hN D - spec.embed N hN E := by
  funext y
  simp only [embed, Pi.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

theorem effective_embed {D : CFDiv spec.graph} (hD : effective D) :
    effective (spec.embed N hN D) := by
  intro y
  unfold embed
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact hD x
  · exact le_rfl

theorem deg_embed (D : CFDiv spec.graph) :
    deg (spec.embed N hN D) = deg D := by
  classical
  change (∑ y, ∑ x : spec.Vertex, if spec.fineOf N hN x = y then D x else 0) =
    ∑ x, D x
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_ite_eq]
  simp

/-! ## Moving chips and their rounding -/

/-- A chip strictly inside a coarse step, together with the end of that step it
is rounded to.  The chip sits at fine offset `N * step + offset` of its slot,
with `0 < offset < N`. -/
structure Chip where
  /-- The slot of the coarse graph. -/
  edge : Fin p
  /-- The coarse unit step of the slot, `0 ≤ step < length edge`. -/
  step : ℕ
  step_lt : step < spec.length edge
  /-- The fine offset inside the coarse step. -/
  offset : ℕ
  offset_pos : 0 < offset
  offset_lt : offset < N
  /-- `true` rounds to the right end of the coarse step, `false` to the left. -/
  toRight : Bool

namespace Chip

variable {spec N}

/-- The fine position of a chip: offset `N * step + offset` along its slot. -/
def finePosition (c : spec.Chip N) : (spec.scale N hN).PathPosition c.edge :=
  ⟨N * c.step + c.offset, by
    have h1 : N * (c.step + 1) ≤ N * spec.length c.edge :=
      Nat.mul_le_mul_left N c.step_lt
    rw [Nat.mul_succ] at h1
    have := c.offset_lt
    simp only [scale_length]
    omega⟩

/-- The fine vertex carrying the chip. -/
def fineVertex (c : spec.Chip N) : (spec.scale N hN).Vertex :=
  (spec.scale N hN).pathVertex c.edge (c.finePosition hN)

/-- The coarse step containing the chip. -/
def coarseStep (c : spec.Chip N) : spec.Step :=
  ⟨c.edge, ⟨c.step, c.step_lt⟩⟩

/-- The coarse vertex the chip is rounded to. -/
def coarseVertex (c : spec.Chip N) : spec.Vertex :=
  if c.toRight then spec.stepRight c.edge ⟨c.step, c.step_lt⟩
  else spec.stepLeft c.edge ⟨c.step, c.step_lt⟩

/-- The fine distance from the chip to the coarse vertex it is rounded to. -/
def distance (c : spec.Chip N) : ℕ :=
  if c.toRight then N - c.offset else c.offset

/-- The signed rounding cost: positive when rounding right, negative when
rounding left.  Adding it to the fine height at the right end of the step
plays the role of moving the chip. -/
def signedCost (c : spec.Chip N) : ℤ :=
  if c.toRight then (N : ℤ) - (c.offset : ℤ) else -(c.offset : ℤ)

theorem abs_signedCost_le (c : spec.Chip N) :
    |c.signedCost| ≤ (c.distance : ℤ) := by
  unfold signedCost distance
  have := c.offset_lt
  split_ifs
  · rw [abs_of_nonneg (by omega)]
    push_cast [Nat.cast_sub this.le]
    exact le_rfl
  · rw [abs_neg, abs_of_nonneg (by positivity)]

/-- A chip is never at a fine vertex in the image of the coarse graph. -/
theorem fineVertex_not_mem_range (c : spec.Chip N) :
    c.fineVertex hN ∉ Set.range (spec.fineOf N hN) := by
  rintro ⟨x, hx⟩
  have hoffpos := c.offset_pos
  have hofflt := c.offset_lt
  have hposlt : N * c.step + c.offset < N * spec.length c.edge := by
    have h1 : N * (c.step + 1) ≤ N * spec.length c.edge :=
      Nat.mul_le_mul_left N c.step_lt
    rw [Nat.mul_succ] at h1
    omega
  have hfv : c.fineVertex hN =
      Sum.inr ⟨c.edge, ⟨N * c.step + c.offset - 1, by
        show N * c.step + c.offset - 1 < N * spec.length c.edge - 1
        omega⟩⟩ := by
    unfold fineVertex pathVertex
    rw [dite_eq_right (by show ¬ N * c.step + c.offset = 0; omega),
      dite_eq_right (by show ¬ N * c.step + c.offset = N * spec.length c.edge; omega)]
    rfl
  rcases x with v | ⟨e, j⟩
  · rw [hfv] at hx
    exact Sum.inl_ne_inr hx
  · rw [hfv] at hx
    have hSigma := Sum.inr.inj hx
    have hedge : e = c.edge := congrArg Sigma.fst hSigma
    subst hedge
    have hval : N * (j.val + 1) - 1 = N * c.step + c.offset - 1 :=
      congrArg (fun s : (spec.scale N hN).Interior => s.2.val) hSigma
    have hpos : 1 ≤ N * (j.val + 1) := Nat.mul_pos hN (Nat.succ_pos _)
    have h1 : N * (j.val + 1) = N * c.step + c.offset := by omega
    have hmod : (N * (j.val + 1)) % N = 0 := Nat.mul_mod_right N _
    rw [h1, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hofflt] at hmod
    omega

end Chip

/-- The fine divisor of a family of chips. -/
def fineChips {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N) :
    CFDiv (spec.scale N hN).graph :=
  ∑ i, oneChip ((chips i).fineVertex hN)

/-- The rounded coarse divisor of a family of chips. -/
def coarseChips {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N) : CFDiv spec.graph :=
  ∑ i, oneChip (chips i).coarseVertex

/-! ## Slot values of a fine script -/

/-- The value of a fine script at fine offset `j` of slot `edge` (and `0`
beyond the head, which is never used). -/
def fineValue (σ : firingScript (spec.scale N hN).graph) (edge : Fin p) (j : ℕ) : ℤ :=
  if h : j ≤ N * spec.length edge then
    σ ((spec.scale N hN).pathVertex edge ⟨j, by simp only [scale_length]; omega⟩)
  else 0

/-- The fine slope across fine step `j` of slot `edge`. -/
def fineSlope (σ : firingScript (spec.scale N hN).graph) (edge : Fin p) (j : ℕ) : ℤ :=
  spec.fineValue N hN σ edge (j + 1) - spec.fineValue N hN σ edge j

theorem isStepSlope_fineSlope (σ : firingScript (spec.scale N hN).graph) :
    (spec.scale N hN).IsStepSlope σ (spec.fineSlope N hN σ) := by
  intro edge offset
  have hlt : offset.val < N * spec.length edge := offset.isLt
  unfold fineSlope fineValue
  rw [dite_eq_left (by omega), dite_eq_left (by omega),
    ← (spec.scale N hN).pathVertex_stepRightPosition edge offset,
    ← (spec.scale N hN).pathVertex_stepLeftPosition edge offset]
  rfl

/-- The rounded coarse script: common-offset rounding of the fine values at
the images of the coarse vertices. -/
def roundedScript (κ : Fin N) (σ : firingScript (spec.scale N hN).graph) :
    firingScript spec.graph :=
  fun v => round N κ (σ (spec.fineOf N hN v))

/-- The coarse slope of the rounded script across coarse step `k` of slot
`edge`. -/
def roundedSlope (κ : Fin N) (σ : firingScript (spec.scale N hN).graph)
    (edge : Fin p) (k : ℕ) : ℤ :=
  round N κ (spec.fineValue N hN σ edge (N * (k + 1))) -
    round N κ (spec.fineValue N hN σ edge (N * k))

theorem isStepSlope_roundedSlope (κ : Fin N)
    (σ : firingScript (spec.scale N hN).graph) :
    spec.IsStepSlope (spec.roundedScript N hN κ σ) (spec.roundedSlope N hN κ σ) := by
  intro edge offset
  have hk : offset.val < spec.length edge := offset.isLt
  unfold roundedScript roundedSlope fineValue
  rw [dite_eq_left (Nat.mul_le_mul_left N hk), dite_eq_left (Nat.mul_le_mul_left N hk.le),
    ← spec.pathVertex_stepRightPosition edge offset,
    ← spec.pathVertex_stepLeftPosition edge offset,
    spec.fineOf_pathVertex, spec.fineOf_pathVertex]
  rfl

/-! ## The step inequality -/

/-- The chips of a family lying in a given coarse step. -/
def stepChips {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N) (step : spec.Step) :
    Finset ι :=
  Finset.univ.filter fun i => (chips i).coarseStep = step

/-- The number of chips of a step rounded to its left end. -/
def leftCount {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N) (step : spec.Step) : ℤ :=
  ((spec.stepChips N chips step).filter fun i => (chips i).toRight = false).card

/-- The number of chips of a step rounded to its right end. -/
def rightCount {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N) (step : spec.Step) : ℤ :=
  ((spec.stepChips N chips step).filter fun i => (chips i).toRight = true).card

/-- The total signed rounding cost of the chips of a step. -/
def stepCost {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N) (step : spec.Step) : ℤ :=
  ∑ i ∈ spec.stepChips N chips step, (chips i).signedCost

end Utilities.Certificate.SubdivisionGraph.Spec
