/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionChipDescentStep
import Mathlib.Tactic

/-!
# Descent of winnability and rank along a regular subdivision

The vertex inequalities for the rounded script, and the descent theorems
`winnable_of_winnable_scale` and `rank_ge_of_rank_scale_ge`.  See
`Utilities/Subdivision/SubdivisionChipDescent.lean` for the definitions and
the overall argument.
-/

namespace Utilities.Certificate.SubdivisionGraph.Spec

open Finset Utilities.CommonOffsetRounding

variable {n p : ℕ} (spec : Spec n p) (N : ℕ) (hN : 0 < N)

/-! ## Counting the rounded chips at a coarse vertex

The rounded chip divisor `coarseChips` is a sum of one-chip divisors, and the
counters `leftCount`/`rightCount` are cardinalities of filters of the chip
index type.  Both are rewritten as sums of indicators, after which every
vertex identity reduces to a single statement about one chip.
-/

/-- An indicator sum guarded by a side condition. -/
private theorem ite_sum_ite {ι : Type*} [Fintype ι] (P : Prop) [Decidable P]
    (Q : ι → Prop) [DecidablePred Q] :
    (if P then ∑ i, (if Q i then (1 : ℤ) else 0) else 0) =
      ∑ i, (if P ∧ Q i then (1 : ℤ) else 0) := by
  by_cases h : P
  · rw [if_pos h]
    exact Finset.sum_congr rfl fun i _ => (if_congr (and_iff_right h) rfl rfl).symm
  · rw [if_neg h]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    exact if_neg fun hc => h hc.1

/-- Membership in a coarse step, with the dependent index unpacked. -/
private theorem coarseStep_eq_iff (c : spec.Chip N) (e : Fin p)
    (o : Fin (spec.length e)) :
    c.coarseStep = ⟨e, o⟩ ↔ c.edge = e ∧ c.step = o.val := by
  constructor
  · intro h
    have he : c.edge = e := congrArg Sigma.fst h
    subst he
    exact ⟨rfl, congrArg (fun s : spec.Step => s.2.val) h⟩
  · rintro ⟨he, hs⟩
    subst he
    show (⟨c.edge, ⟨c.step, c.step_lt⟩⟩ : spec.Step) = ⟨c.edge, o⟩
    have hfin : (⟨c.step, c.step_lt⟩ : Fin (spec.length c.edge)) = o := Fin.ext hs
    rw [hfin]

private theorem coarseVertex_of_false {c : spec.Chip N} (h : c.toRight = false) :
    c.coarseVertex = spec.stepLeft c.edge ⟨c.step, c.step_lt⟩ := by
  simp only [Chip.coarseVertex, h, Bool.false_eq_true, if_false]

private theorem coarseVertex_of_true {c : spec.Chip N} (h : c.toRight = true) :
    c.coarseVertex = spec.stepRight c.edge ⟨c.step, c.step_lt⟩ := by
  simp only [Chip.coarseVertex, h, if_true]

/-- The rounded chip divisor as a sum of indicators. -/
private theorem coarseChips_apply {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N)
    (v : spec.Vertex) :
    spec.coarseChips N chips v =
      ∑ i, (if (chips i).coarseVertex = v then (1 : ℤ) else 0) := by
  show (∑ i, oneChip ((chips i).coarseVertex) : CFDiv spec.graph) v = _
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (chips i).coarseVertex = v
  · subst h
    simp
  · rw [one_chip_apply_other _ _ h, if_neg h]

/-- The left counter of a step as a sum of indicators. -/
private theorem leftCount_eq_sum {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N)
    (e : Fin p) (o : Fin (spec.length e)) (k : ℕ) (hk : o.val = k) :
    spec.leftCount N chips ⟨e, o⟩ =
      ∑ i, (if (chips i).edge = e ∧ (chips i).step = k ∧
        (chips i).toRight = false then (1 : ℤ) else 0) := by
  subst hk
  rw [← Finset.natCast_card_filter]
  unfold leftCount stepChips
  rw [Finset.filter_filter]
  congr 2
  apply Finset.filter_congr
  intro i _
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨h1a, h1b⟩ := (spec.coarseStep_eq_iff N (chips i) e o).mp h1
    exact ⟨h1a, h1b, h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(spec.coarseStep_eq_iff N (chips i) e o).mpr ⟨h1, h2⟩, h3⟩

/-- The right counter of a step as a sum of indicators. -/
private theorem rightCount_eq_sum {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N)
    (e : Fin p) (o : Fin (spec.length e)) (k : ℕ) (hk : o.val = k) :
    spec.rightCount N chips ⟨e, o⟩ =
      ∑ i, (if (chips i).edge = e ∧ (chips i).step = k ∧
        (chips i).toRight = true then (1 : ℤ) else 0) := by
  subst hk
  rw [← Finset.natCast_card_filter]
  unfold rightCount stepChips
  rw [Finset.filter_filter]
  congr 2
  apply Finset.filter_congr
  intro i _
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨h1a, h1b⟩ := (spec.coarseStep_eq_iff N (chips i) e o).mp h1
    exact ⟨h1a, h1b, h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(spec.coarseStep_eq_iff N (chips i) e o).mpr ⟨h1, h2⟩, h3⟩

/-! ### The two per-chip identities -/

/-- A single chip is rounded to the core vertex `u` exactly when it sits in the
first step of a slot with tail `u` and rounds left, or in the last step of a
slot with head `u` and rounds right. -/
private theorem chip_core_sum (c : spec.Chip N) (u : Fin n) :
    (∑ e : Fin p,
      ((if spec.core.tail e = u ∧ c.edge = e ∧ c.step = 0 ∧ c.toRight = false
          then (1 : ℤ) else 0) +
        (if spec.core.head e = u ∧ c.edge = e ∧ c.step = spec.length e - 1 ∧
            c.toRight = true then (1 : ℤ) else 0))) =
      if c.coarseVertex = spec.coreVertex u then (1 : ℤ) else 0 := by
  classical
  have hlt := c.step_lt
  have hpos := spec.length_pos c.edge
  rw [Finset.sum_add_distrib]
  have hleft :
      (∑ e : Fin p, if spec.core.tail e = u ∧ c.edge = e ∧ c.step = 0 ∧
          c.toRight = false then (1 : ℤ) else 0) =
        if spec.core.tail c.edge = u ∧ c.step = 0 ∧ c.toRight = false then
          (1 : ℤ) else 0 := by
    rw [Fintype.sum_eq_single c.edge]
    · by_cases h : spec.core.tail c.edge = u ∧ c.step = 0 ∧ c.toRight = false
      · rw [if_pos ⟨h.1, rfl, h.2.1, h.2.2⟩, if_pos h]
      · rw [if_neg, if_neg h]
        rintro ⟨h1, -, h3, h4⟩
        exact h ⟨h1, h3, h4⟩
    · intro e he
      rw [if_neg]
      rintro ⟨-, h2, -, -⟩
      exact he h2.symm
  have hright :
      (∑ e : Fin p, if spec.core.head e = u ∧ c.edge = e ∧
          c.step = spec.length e - 1 ∧ c.toRight = true then (1 : ℤ) else 0) =
        if spec.core.head c.edge = u ∧ c.step = spec.length c.edge - 1 ∧
          c.toRight = true then (1 : ℤ) else 0 := by
    rw [Fintype.sum_eq_single c.edge]
    · by_cases h : spec.core.head c.edge = u ∧ c.step = spec.length c.edge - 1 ∧
          c.toRight = true
      · rw [if_pos ⟨h.1, rfl, h.2.1, h.2.2⟩, if_pos h]
      · rw [if_neg, if_neg h]
        rintro ⟨h1, -, h3, h4⟩
        exact h ⟨h1, h3, h4⟩
    · intro e he
      rw [if_neg]
      rintro ⟨-, h2, -, -⟩
      exact he h2.symm
  rw [hleft, hright]
  cases hb : c.toRight
  · have hfalse : ¬ (spec.core.head c.edge = u ∧ c.step = spec.length c.edge - 1 ∧
        ((false : Bool) = true)) := by
      rintro ⟨-, -, h⟩
      exact Bool.noConfusion h
    rw [if_neg hfalse, add_zero]
    refine if_congr ?_ rfl rfl
    rw [spec.coarseVertex_of_false N hb, spec.stepLeft_eq_coreVertex_iff]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, rfl⟩
  · have hfalse : ¬ (spec.core.tail c.edge = u ∧ c.step = 0 ∧
        ((true : Bool) = false)) := by
      rintro ⟨-, -, h⟩
      exact Bool.noConfusion h
    rw [if_neg hfalse, zero_add]
    refine if_congr ?_ rfl rfl
    rw [spec.coarseVertex_of_true N hb, spec.stepRight_eq_coreVertex_iff]
    constructor
    · rintro ⟨h1, h2, -⟩
      refine ⟨?_, h1⟩
      show c.step + 1 = spec.length c.edge
      omega
    · rintro ⟨h1, h2⟩
      have h1' : c.step + 1 = spec.length c.edge := h1
      exact ⟨h2, by omega, rfl⟩

/-- A single chip is rounded to the interior vertex `interiorVertex e j`
exactly when it sits in the following step and rounds left, or in the
preceding step and rounds right. -/
private theorem chip_interior_sum (c : spec.Chip N) (e : Fin p)
    (j : Fin (spec.length e - 1)) :
    ((if c.edge = e ∧ c.step = j.val + 1 ∧ c.toRight = false then (1 : ℤ) else 0) +
      (if c.edge = e ∧ c.step = j.val ∧ c.toRight = true then (1 : ℤ) else 0)) =
      if c.coarseVertex = spec.interiorVertex e j then (1 : ℤ) else 0 := by
  classical
  cases hb : c.toRight
  · have hfalse : ¬ (c.edge = e ∧ c.step = j.val ∧ ((false : Bool) = true)) := by
      rintro ⟨-, -, h⟩
      exact Bool.noConfusion h
    rw [if_neg hfalse, add_zero]
    refine if_congr ?_ rfl rfl
    rw [spec.coarseVertex_of_false N hb]
    have hiff := spec.stepLeft_eq_interiorVertex_iff
      (⟨c.edge, ⟨c.step, c.step_lt⟩⟩ : spec.Step) e j
    rw [show spec.stepLeft c.edge ⟨c.step, c.step_lt⟩ =
      spec.stepLeft (⟨c.edge, ⟨c.step, c.step_lt⟩⟩ : spec.Step).1
        (⟨c.edge, ⟨c.step, c.step_lt⟩⟩ : spec.Step).2 from rfl, hiff,
      show (⟨c.edge, ⟨c.step, c.step_lt⟩⟩ : spec.Step) = c.coarseStep from rfl,
      spec.coarseStep_eq_iff N c e (spec.nextStep e j)]
    simp [nextStep]
  · have hfalse : ¬ (c.edge = e ∧ c.step = j.val + 1 ∧ ((true : Bool) = false)) := by
      rintro ⟨-, -, h⟩
      exact Bool.noConfusion h
    rw [if_neg hfalse, zero_add]
    refine if_congr ?_ rfl rfl
    rw [spec.coarseVertex_of_true N hb]
    have hiff := spec.stepRight_eq_interiorVertex_iff
      (⟨c.edge, ⟨c.step, c.step_lt⟩⟩ : spec.Step) e j
    rw [show spec.stepRight c.edge ⟨c.step, c.step_lt⟩ =
      spec.stepRight (⟨c.edge, ⟨c.step, c.step_lt⟩⟩ : spec.Step).1
        (⟨c.edge, ⟨c.step, c.step_lt⟩⟩ : spec.Step).2 from rfl, hiff,
      show (⟨c.edge, ⟨c.step, c.step_lt⟩⟩ : spec.Step) = c.coarseStep from rfl,
      spec.coarseStep_eq_iff N c e (spec.previousStep e j)]
    simp [previousStep]

/-! ### The two vertex counts -/

/-- The chips rounded to a core vertex are exactly the left chips of the first
steps of the slots with that tail and the right chips of the last steps of the
slots with that head. -/
private theorem core_chip_count {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N)
    (u : Fin n) :
    (∑ e : Fin p,
      ((if spec.core.tail e = u then
          spec.leftCount N chips ⟨e, ⟨0, spec.length_pos e⟩⟩ else 0) +
        (if spec.core.head e = u then
          spec.rightCount N chips
            ⟨e, ⟨spec.length e - 1, by have := spec.length_pos e; omega⟩⟩
          else 0))) =
      spec.coarseChips N chips (spec.coreVertex u) := by
  classical
  rw [spec.coarseChips_apply N chips]
  have hstep : ∀ e : Fin p,
      ((if spec.core.tail e = u then
          spec.leftCount N chips ⟨e, ⟨0, spec.length_pos e⟩⟩ else 0) +
        (if spec.core.head e = u then
          spec.rightCount N chips
            ⟨e, ⟨spec.length e - 1, by have := spec.length_pos e; omega⟩⟩
          else 0)) =
      ∑ i, ((if spec.core.tail e = u ∧ (chips i).edge = e ∧ (chips i).step = 0 ∧
              (chips i).toRight = false then (1 : ℤ) else 0) +
            (if spec.core.head e = u ∧ (chips i).edge = e ∧
              (chips i).step = spec.length e - 1 ∧
              (chips i).toRight = true then (1 : ℤ) else 0)) := by
    intro e
    have hpos := spec.length_pos e
    rw [spec.leftCount_eq_sum N chips e ⟨0, spec.length_pos e⟩ 0 rfl,
      spec.rightCount_eq_sum N chips e ⟨spec.length e - 1, by omega⟩
        (spec.length e - 1) rfl,
      ite_sum_ite, ite_sum_ite, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun e _ => hstep e, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => spec.chip_core_sum N (chips i) u

/-- The chips rounded to an interior vertex are exactly the left chips of the
following step and the right chips of the preceding step. -/
private theorem interior_chip_count {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N)
    (e : Fin p) (j : Fin (spec.length e - 1)) :
    spec.leftCount N chips ⟨e, spec.nextStep e j⟩ +
        spec.rightCount N chips ⟨e, spec.previousStep e j⟩ =
      spec.coarseChips N chips (spec.interiorVertex e j) := by
  classical
  rw [spec.coarseChips_apply N chips,
    spec.leftCount_eq_sum N chips e (spec.nextStep e j) (j.val + 1) rfl,
    spec.rightCount_eq_sum N chips e (spec.previousStep e j) j.val rfl,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => spec.chip_interior_sum N (chips i) e j

/-! ## The vertex inequalities and the descent theorem -/

/-- At every coarse vertex, the rounded script loses at most the number of
chips rounded to that vertex relative to the fine script at its image. -/
theorem prin_roundedScript_ge {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N) (D₀ : CFDiv spec.graph)
    (σ : firingScript (spec.scale N hN).graph)
    (hσ : effective (spec.embed N hN D₀ + spec.fineChips N hN chips +
      prin (spec.scale N hN).graph σ))
    (κ : Fin N)
    (hκ : ∀ step : spec.Step,
      round N κ (spec.fineValue N hN σ step.1 (N * (step.2.val + 1)) +
        spec.stepCost N chips step) =
      round N κ (spec.fineValue N hN σ step.1 (N * (step.2.val + 1))))
    (v : spec.Vertex) :
    prin (spec.scale N hN).graph σ (spec.fineOf N hN v) - spec.coarseChips N chips v ≤
      prin spec.graph (spec.roundedScript N hN κ σ) v := by
  classical
  have hslopeF := spec.isStepSlope_fineSlope N hN σ
  have hslopeC := spec.isStepSlope_roundedSlope N hN κ σ
  rcases v with u | ⟨e, j⟩
  · -- core vertex
    have hC : prin spec.graph (spec.roundedScript N hN κ σ) (spec.coreVertex u) =
        ∑ e : Fin p,
          ((if spec.core.tail e = u then spec.roundedSlope N hN κ σ e 0 else 0) +
            (if spec.core.head e = u then
              -spec.roundedSlope N hN κ σ e (spec.length e - 1) else 0)) :=
      spec.prin_coreVertex_eq_endpointSum hslopeC u
    have hF : prin (spec.scale N hN).graph σ ((spec.scale N hN).coreVertex u) =
        ∑ e : Fin p,
          ((if spec.core.tail e = u then spec.fineSlope N hN σ e 0 else 0) +
            (if spec.core.head e = u then
              -spec.fineSlope N hN σ e (N * spec.length e - 1) else 0)) :=
      (spec.scale N hN).prin_coreVertex_eq_endpointSum hslopeF u
    show prin (spec.scale N hN).graph σ ((spec.scale N hN).coreVertex u) -
        spec.coarseChips N chips (spec.coreVertex u) ≤
      prin spec.graph (spec.roundedScript N hN κ σ) (spec.coreVertex u)
    rw [hC, hF, ← spec.core_chip_count N chips u, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun e _ => ?_
    have hpos := spec.length_pos e
    obtain ⟨hlo, -⟩ :=
      spec.roundedSlope_bounds N hN chips D₀ σ hσ κ hκ ⟨e, ⟨0, spec.length_pos e⟩⟩
    obtain ⟨-, hhi⟩ :=
      spec.roundedSlope_bounds N hN chips D₀ σ hσ κ hκ
        ⟨e, ⟨spec.length e - 1, by omega⟩⟩
    rw [show spec.length e - 1 + 1 = spec.length e from by omega] at hhi
    have hlo' : spec.fineSlope N hN σ e 0 -
        spec.leftCount N chips ⟨e, ⟨0, spec.length_pos e⟩⟩ ≤
        spec.roundedSlope N hN κ σ e 0 := hlo
    have hhi' : spec.roundedSlope N hN κ σ e (spec.length e - 1) ≤
        spec.fineSlope N hN σ e (N * spec.length e - 1) +
          spec.rightCount N chips
            ⟨e, ⟨spec.length e - 1, by have := spec.length_pos e; omega⟩⟩ := hhi
    clear hlo hhi
    split_ifs <;> omega
  · -- interior vertex
    have hpos := spec.length_pos e
    have hjlt : j.val < spec.length e - 1 := j.isLt
    have hNpos : 1 ≤ N * (j.val + 1) := Nat.mul_pos hN (Nat.succ_pos _)
    have hfineLt : N * (j.val + 1) - 1 < (spec.scale N hN).length e - 1 := by
      have h2 : j.val + 2 ≤ spec.length e := by omega
      have h3 : N * (j.val + 2) ≤ N * spec.length e := Nat.mul_le_mul_left N h2
      rw [show N * (j.val + 2) = N * (j.val + 1) + N from by ring] at h3
      show N * (j.val + 1) - 1 < N * spec.length e - 1
      omega
    have hC : prin spec.graph (spec.roundedScript N hN κ σ) (spec.interiorVertex e j) =
        spec.roundedSlope N hN κ σ e (j.val + 1) -
          spec.roundedSlope N hN κ σ e j.val :=
      spec.prin_interiorVertex_eq_slopeDifference hslopeC e j
    have hF : prin (spec.scale N hN).graph σ
        ((spec.scale N hN).interiorVertex e ⟨N * (j.val + 1) - 1, hfineLt⟩) =
        spec.fineSlope N hN σ e (N * (j.val + 1)) -
          spec.fineSlope N hN σ e (N * (j.val + 1) - 1) := by
      have hbase := (spec.scale N hN).prin_interiorVertex_eq_slopeDifference hslopeF e
        ⟨N * (j.val + 1) - 1, hfineLt⟩
      rw [hbase, show N * (j.val + 1) - 1 + 1 = N * (j.val + 1) from by omega]
    show prin (spec.scale N hN).graph σ
        ((spec.scale N hN).interiorVertex e ⟨N * (j.val + 1) - 1, hfineLt⟩) -
        spec.coarseChips N chips (spec.interiorVertex e j) ≤
      prin spec.graph (spec.roundedScript N hN κ σ) (spec.interiorVertex e j)
    rw [hC, hF, ← spec.interior_chip_count N chips e j]
    obtain ⟨hlo, -⟩ :=
      spec.roundedSlope_bounds N hN chips D₀ σ hσ κ hκ ⟨e, spec.nextStep e j⟩
    obtain ⟨-, hhi⟩ :=
      spec.roundedSlope_bounds N hN chips D₀ σ hσ κ hκ ⟨e, spec.previousStep e j⟩
    have hlo' : spec.fineSlope N hN σ e (N * (j.val + 1)) -
        spec.leftCount N chips ⟨e, spec.nextStep e j⟩ ≤
        spec.roundedSlope N hN κ σ e (j.val + 1) := hlo
    have hhi' : spec.roundedSlope N hN κ σ e j.val ≤
        spec.fineSlope N hN σ e (N * (j.val + 1) - 1) +
          spec.rightCount N chips ⟨e, spec.previousStep e j⟩ := hhi
    clear hlo hhi
    omega

/-- **Descent of winnability, signed-budget form.**  If the sum over coarse
steps of the absolute *signed* rounding cost of the chips in that step is less
than `N`, winnability on the `N`-fold refinement of the embedded divisor plus
the chips implies winnability on the coarse graph of the divisor plus the
rounded chips.  Chips on one step rounded in opposite directions cancel: at
`N = 3`, chips at offsets `1` and `2` of one edge, rounded left and right,
cost nothing. -/
theorem winnable_of_winnable_scale_cost {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N)
    (D₀ : CFDiv spec.graph)
    (hcost : (∑ step : spec.Step, |spec.stepCost N chips step|) < N)
    (hwin : winnable (spec.scale N hN).graph
      (spec.embed N hN D₀ + spec.fineChips N hN chips)) :
    winnable spec.graph (D₀ + spec.coarseChips N chips) := by
  classical
  obtain ⟨D', hD'eff, hEquiv⟩ := hwin
  obtain ⟨σ, hσeq⟩ :=
    (principal_iff_eq_prin (spec.scale N hN).graph
      (D' - (spec.embed N hN D₀ + spec.fineChips N hN chips))).mp hEquiv
  have hσ : effective (spec.embed N hN D₀ + spec.fineChips N hN chips +
      prin (spec.scale N hN).graph σ) := by
    have hEq : spec.embed N hN D₀ + spec.fineChips N hN chips +
        prin (spec.scale N hN).graph σ = D' := by
      rw [← hσeq]
      abel
    rw [hEq]
    exact hD'eff
  -- the common rounding offset
  have hcost : (∑ step : spec.Step,
      |(spec.fineValue N hN σ step.1 (N * (step.2.val + 1)) +
          spec.stepCost N chips step) -
        spec.fineValue N hN σ step.1 (N * (step.2.val + 1))|) < (N : ℤ) := by
    have hrw : ∀ step : spec.Step,
        |(spec.fineValue N hN σ step.1 (N * (step.2.val + 1)) +
            spec.stepCost N chips step) -
          spec.fineValue N hN σ step.1 (N * (step.2.val + 1))| =
          |spec.stepCost N chips step| := by
      intro step
      congr 1
      ring
    rw [Finset.sum_congr rfl fun step _ => hrw step]
    exact hcost
  obtain ⟨κ, hκ0⟩ := exists_common_offset (ι := spec.Step) N hN Finset.univ
    (fun step => spec.fineValue N hN σ step.1 (N * (step.2.val + 1)) +
      spec.stepCost N chips step)
    (fun step => spec.fineValue N hN σ step.1 (N * (step.2.val + 1))) hcost
  have hκ : ∀ step : spec.Step,
      round N κ (spec.fineValue N hN σ step.1 (N * (step.2.val + 1)) +
        spec.stepCost N chips step) =
      round N κ (spec.fineValue N hN σ step.1 (N * (step.2.val + 1))) :=
    fun step => hκ0 step (Finset.mem_univ step)
  -- the fine chips are invisible at the images of the coarse vertices
  have hfineChips : ∀ v : spec.Vertex,
      spec.fineChips N hN chips (spec.fineOf N hN v) = 0 := by
    intro v
    show (∑ i, oneChip ((chips i).fineVertex hN) :
      CFDiv (spec.scale N hN).graph) (spec.fineOf N hN v) = 0
    rw [Finset.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine one_chip_apply_other' _ _ ?_
    intro hEq
    exact (chips i).fineVertex_not_mem_range hN ⟨v, hEq⟩
  refine ⟨D₀ + spec.coarseChips N chips +
    prin spec.graph (spec.roundedScript N hN κ σ), ?_, ?_⟩
  · show effective (D₀ + spec.coarseChips N chips +
      prin spec.graph (spec.roundedScript N hN κ σ))
    intro v
    have hvertex := spec.prin_roundedScript_ge N hN chips D₀ σ hσ κ hκ v
    have hfine := hσ (spec.fineOf N hN v)
    rw [Pi.add_apply, Pi.add_apply, spec.embed_apply_fineOf N hN D₀ v,
      hfineChips v] at hfine
    show D₀ v + spec.coarseChips N chips v +
      prin spec.graph (spec.roundedScript N hN κ σ) v ≥ 0
    omega
  · have hdiff : D₀ + spec.coarseChips N chips +
        prin spec.graph (spec.roundedScript N hN κ σ) -
        (D₀ + spec.coarseChips N chips) =
        prin spec.graph (spec.roundedScript N hN κ σ) := by abel
    exact (principal_iff_eq_prin spec.graph _).mpr
      ⟨spec.roundedScript N hN κ σ, hdiff⟩

/-- **Descent of winnability, distance form.**  If the total rounding distance
of the chips is less than `N`, winnability on the `N`-fold refinement of the
embedded divisor plus the chips implies winnability on the coarse graph of
the divisor plus the rounded chips.  This is the special case of the signed
budget in which every chip is charged its full distance. -/
theorem winnable_of_winnable_scale {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N)
    (D₀ : CFDiv spec.graph)
    (hbudget : (∑ i, ((chips i).distance : ℤ)) < N)
    (hwin : winnable (spec.scale N hN).graph
      (spec.embed N hN D₀ + spec.fineChips N hN chips)) :
    winnable spec.graph (D₀ + spec.coarseChips N chips) :=
  spec.winnable_of_winnable_scale_cost N hN chips D₀
    (lt_of_le_of_lt (spec.sum_abs_stepCost_le N chips) hbudget) hwin

/-- **Descent of rank, signed-budget form.**  Coarse rank tests embed into fine
rank tests, so the descent of winnability upgrades to every rank lower bound.
The hypothesis charges each coarse step only the absolute value of the
*signed* sum of its chips' rounding costs, so chips on one step rounded in
opposite directions cancel. -/
theorem rank_ge_of_rank_scale_ge_cost {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N)
    (D₀ : CFDiv spec.graph) (r : ℤ)
    (hcost : (∑ step : spec.Step, |spec.stepCost N chips step|) < N)
    (hrank : rank (spec.scale N hN).graph
      (spec.embed N hN D₀ + spec.fineChips N hN chips) ≥ r) :
    rank spec.graph (D₀ + spec.coarseChips N chips) ≥ r := by
  classical
  rw [← rank_geq_iff] at hrank ⊢
  intro T hT
  obtain ⟨hTeff, hTdeg⟩ := hT
  have hfine : winnable (spec.scale N hN).graph
      (spec.embed N hN D₀ + spec.fineChips N hN chips - spec.embed N hN T) :=
    hrank (spec.embed N hN T)
      ⟨spec.effective_embed N hN hTeff, by rw [spec.deg_embed N hN T]; exact hTdeg⟩
  have hrw : spec.embed N hN D₀ + spec.fineChips N hN chips - spec.embed N hN T =
      spec.embed N hN (D₀ - T) + spec.fineChips N hN chips := by
    rw [spec.embed_sub N hN D₀ T]
    abel
  rw [hrw] at hfine
  have hcoarse := spec.winnable_of_winnable_scale_cost N hN chips (D₀ - T) hcost hfine
  have hrw2 : D₀ - T + spec.coarseChips N chips =
      D₀ + spec.coarseChips N chips - T := by abel
  rw [hrw2] at hcoarse
  exact hcoarse

/-- **Descent of rank, distance form.**  The special case of the signed budget
in which every chip is charged its full rounding distance. -/
theorem rank_ge_of_rank_scale_ge {ι : Type*} [Fintype ι] (chips : ι → spec.Chip N)
    (D₀ : CFDiv spec.graph) (r : ℤ)
    (hbudget : (∑ i, ((chips i).distance : ℤ)) < N)
    (hrank : rank (spec.scale N hN).graph
      (spec.embed N hN D₀ + spec.fineChips N hN chips) ≥ r) :
    rank spec.graph (D₀ + spec.coarseChips N chips) ≥ r :=
  spec.rank_ge_of_rank_scale_ge_cost N hN chips D₀ r
    (lt_of_le_of_lt (spec.sum_abs_stepCost_le N chips) hbudget) hrank

end Utilities.Certificate.SubdivisionGraph.Spec
