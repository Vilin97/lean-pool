/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateSpec
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SlopeScript

/-!
# Firing scripts, potentials and the Laplacian on the closed length orthant

This is the `DegSpec` counterpart of `Certificate/SubdivisionGraph.lean`'s
`prin_eq_sum_steps` and of `Certificate/SlopeScript.lean`.  Nothing in
`SubdivisionGraph.Spec` or `SlopeScript` is touched; these are separate
statements about `DegSpec.graph`, so the strictly positive path keeps working
verbatim while the closed-orthant path is proved out beside it.

## The one statement that makes the whole design pay

`prin_coreVertex_eq_endpointSum` below is *word for word* the `Spec` statement
with `rep` applied to the two endpoints:

```
prin d.graph script (d.coreVertex r) =
  ∑ e : Fin p, ((if d.rep (d.core.tail e) = d.rep r then slope e 0 else 0) +
                (if d.rep (d.core.head e) = d.rep r then
                   -slope e (d.length e - 1) else 0))
```

In particular **the sum still runs over every slot of the uncontracted core,
vanishing slots included**.  That is not an accident and it is not free: a
vanishing slot emits no unit steps, so it contributes nothing to the left-hand
side, and it contributes nothing to the right-hand side either because its two
endpoints lie in one `rep`-class (`rep_zero`) and its two endpoint terms are
`slope e 0` and `-slope e (d.length e - 1) = -slope e 0`.  That is exactly
`DegSpec.zero_slot_cancels`.

Consequently `prin_coreVertex_eq_classSum` says the Laplacian at a contracted
class is the **sum over the class members of the uncontracted per-vertex
formula**.  A row's per-core-vertex value lemmas are therefore reusable at
every face by addition, rather than being reproved once per face.  That is the
whole economic argument for the closed-orthant layer, and it is a theorem
here.
-/

namespace Utilities.Certificate.DegenerateSpec
open Utilities.Certificate

open Utilities

open Finset ExplicitPotential

namespace DegSpec

variable {n p : ℕ} (d : DegSpec n p)

/-! ## Which unit steps meet a given vertex -/

/-- The step immediately before the interior vertex with coordinate `j`. -/
def previousStep (e : Fin p) (o : Fin (d.length e - 1)) : Fin (d.length e) :=
  ⟨o.val, by have := o.isLt; omega⟩

/-- The step immediately after the interior vertex with coordinate `j`. -/
def nextStep (e : Fin p) (o : Fin (d.length e - 1)) : Fin (d.length e) :=
  ⟨o.val + 1, by have := o.isLt; omega⟩

theorem stepLeft_eq_coreVertex_iff (e : Fin p) (o : Fin (d.length e))
    (v : Fin n) :
    d.stepLeft e o = d.coreVertex v ↔
      o.val = 0 ∧ d.rep (d.core.tail e) = d.rep v := by
  unfold stepLeft
  by_cases hz : o.val = 0
  · rw [dif_pos hz]
    simp only [hz, true_and]
    exact d.coreVertex_eq_iff _ _
  · rw [dif_neg hz]
    simp [hz, coreVertex, interiorVertex]

theorem stepRight_eq_coreVertex_iff (e : Fin p) (o : Fin (d.length e))
    (v : Fin n) :
    d.stepRight e o = d.coreVertex v ↔
      o.val + 1 = d.length e ∧ d.rep (d.core.head e) = d.rep v := by
  unfold stepRight
  by_cases hl : o.val + 1 = d.length e
  · rw [dif_pos hl]
    simp only [hl, true_and]
    exact d.coreVertex_eq_iff _ _
  · rw [dif_neg hl]
    simp [hl, coreVertex, interiorVertex]

@[simp] theorem stepRight_previousStep (e : Fin p) (o : Fin (d.length e - 1)) :
    d.stepRight e (d.previousStep e o) = d.interiorVertex e o := by
  unfold stepRight previousStep
  rw [dif_neg (by change ¬ (o.val + 1 = d.length e); have := o.isLt; omega)]

@[simp] theorem stepLeft_nextStep (e : Fin p) (o : Fin (d.length e - 1)) :
    d.stepLeft e (d.nextStep e o) = d.interiorVertex e o := by
  unfold stepLeft nextStep
  rw [dif_neg (by change ¬ (o.val + 1 = 0); omega)]
  exact congrArg (d.interiorVertex e) (Fin.ext (by change o.val + 1 - 1 = o.val; omega))

theorem stepRight_eq_interiorVertex_iff (s : d.Step) (e : Fin p)
    (o : Fin (d.length e - 1)) :
    d.stepRight s.1 s.2 = d.interiorVertex e o ↔ s = ⟨e, d.previousStep e o⟩ := by
  constructor
  · intro hEq
    rcases s with ⟨e', o'⟩
    unfold stepRight at hEq
    by_cases hl : o'.val + 1 = d.length e'
    · rw [dif_pos hl] at hEq
      simp [coreVertex, interiorVertex] at hEq
    · rw [dif_neg hl] at hEq
      have hs : (⟨e', ⟨o'.val, by have := o'.isLt; omega⟩⟩ : d.Interior) = ⟨e, o⟩ :=
        Sum.inr.inj hEq
      have he : e' = e := congrArg Sigma.fst hs
      subst he
      have hv : o'.val = o.val :=
        congrArg (fun x : d.Interior => (x.2 : ℕ)) hs
      exact congrArg (Sigma.mk e') (Fin.ext hv)
  · intro hStep
    cases hStep
    exact d.stepRight_previousStep e o

theorem stepLeft_eq_interiorVertex_iff (s : d.Step) (e : Fin p)
    (o : Fin (d.length e - 1)) :
    d.stepLeft s.1 s.2 = d.interiorVertex e o ↔ s = ⟨e, d.nextStep e o⟩ := by
  constructor
  · intro hEq
    rcases s with ⟨e', o'⟩
    unfold stepLeft at hEq
    by_cases hz : o'.val = 0
    · rw [dif_pos hz] at hEq
      simp [coreVertex, interiorVertex] at hEq
    · rw [dif_neg hz] at hEq
      have hs : (⟨e', ⟨o'.val - 1, by have := o'.isLt; omega⟩⟩ : d.Interior)
          = ⟨e, o⟩ := Sum.inr.inj hEq
      have he : e' = e := congrArg Sigma.fst hs
      subst he
      have hv : o'.val - 1 = o.val :=
        congrArg (fun x : d.Interior => (x.2 : ℕ)) hs
      exact congrArg (Sigma.mk e')
        (Fin.ext (by change o'.val = o.val + 1; omega))
  · intro hStep
    cases hStep
    exact d.stepLeft_nextStep e o

/-! ## The Laplacian as a sum over unit steps -/

theorem num_edges_eq_sum_steps (x y : d.Vertex) :
    numEdges d.graph x y =
      ∑ s : d.Step,
        if d.unitEdge s = (x, y) ∨ d.unitEdge s = (y, x) then 1 else 0 := by
  rw [d.num_edges_eq_card_filter_steps]
  simpa only [Finset.sum_filter, Finset.sum_const_zero, Finset.sum_ite_irrel,
    Finset.mem_univ, if_true] using
    (Finset.card_filter
      (fun s : d.Step => d.unitEdge s = (x, y) ∨ d.unitEdge s = (y, x))
      Finset.univ)

theorem prin_eq_sum_steps (script : firingScript d.graph) (v : d.Vertex) :
    prin d.graph script v =
      ∑ s : d.Step,
        ((if d.stepLeft s.1 s.2 = v then
            script (d.stepRight s.1 s.2) - script v else 0) +
          (if d.stepRight s.1 s.2 = v then
            script (d.stepLeft s.1 s.2) - script v else 0)) := by
  change (∑ w : d.graph.V,
    (script w - script v) * (numEdges d.graph v w : ℤ)) = _
  simp_rw [d.num_edges_eq_sum_steps]
  push_cast
  simp_rw [mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _hs
  rcases s with ⟨e, o⟩
  have hne := d.stepLeft_ne_stepRight e o
  by_cases hleft : d.stepLeft e o = v
  · subst v
    simp only [unitEdge, Prod.mk.injEq]
    simp [hne.symm]
  · by_cases hright : d.stepRight e o = v
    · subst v
      simp only [unitEdge, Prod.mk.injEq]
      simp [hne]
    · simp only [unitEdge, Prod.mk.injEq]
      simp [hleft, hright]

/-! ## Slope data -/

/-- A slope datum for a firing script: the script rises by `slope edge k`
across the `k`-th unit step of slot `edge`.  Vanishing slots impose no
condition, since they carry no unit step. -/
def IsStepSlope (script : firingScript d.graph) (slope : Fin p → ℕ → ℤ) :
    Prop :=
  ∀ (e : Fin p) (o : Fin (d.length e)),
    script (d.stepRight e o) - script (d.stepLeft e o) = slope e o.val

theorem prin_eq_sum_slopes {script : firingScript d.graph}
    {slope : Fin p → ℕ → ℤ} (hslope : d.IsStepSlope script slope)
    (v : d.Vertex) :
    prin d.graph script v =
      ∑ s : d.Step,
        ((if d.stepLeft s.1 s.2 = v then slope s.1 s.2.val else 0) +
          (if d.stepRight s.1 s.2 = v then -slope s.1 s.2.val else 0)) := by
  classical
  rw [d.prin_eq_sum_steps]
  apply Finset.sum_congr rfl
  intro s _hs
  rcases s with ⟨e, o⟩
  have hDifference := hslope e o
  by_cases hleft : d.stepLeft e o = v <;> by_cases hright : d.stepRight e o = v
  · exact absurd (hleft.trans hright.symm) (d.stepLeft_ne_stepRight e o)
  · subst v
    simp only [hright, if_false, if_true, add_zero]
    exact hDifference
  · subst v
    simp only [hleft, if_false, if_true, zero_add]
    omega
  · simp [hleft, hright]

/-! ## Endpoint sums, including the vanishing slots -/

theorem sum_over_first_step {e : Fin p} (hpos : 0 < d.length e)
    (value : Fin (d.length e) → ℤ) :
    (∑ o : Fin (d.length e), if o.val = 0 then value o else 0) =
      value ⟨0, hpos⟩ := by
  classical
  refine (Fintype.sum_eq_single (⟨0, hpos⟩ : Fin (d.length e)) ?_).trans (if_pos rfl)
  intro o hne
  exact if_neg fun hz => hne (Fin.ext (by simpa using hz))

theorem sum_over_last_step {e : Fin p} (hpos : 0 < d.length e)
    (value : Fin (d.length e) → ℤ) :
    (∑ o : Fin (d.length e), if o.val + 1 = d.length e then value o else 0) =
      value ⟨d.length e - 1, by omega⟩ := by
  classical
  refine (Fintype.sum_eq_single
    (⟨d.length e - 1, by omega⟩ : Fin (d.length e)) ?_).trans (if_pos (by simp; omega))
  intro o hne
  exact if_neg fun hEq => hne (Fin.ext (by simp; omega))

/-- **The load-bearing formula.**  At a contracted core class the Laplacian is
the endpoint sum over *all* slots of the uncontracted core.  Vanishing slots
appear in the sum and contribute zero, by `zero_slot_cancels`. -/
theorem prin_coreVertex_eq_endpointSum {script : firingScript d.graph}
    {slope : Fin p → ℕ → ℤ} (hslope : d.IsStepSlope script slope) (r : Fin n) :
    prin d.graph script (d.coreVertex r) =
      ∑ e : Fin p,
        ((if d.rep (d.core.tail e) = d.rep r then slope e 0 else 0) +
          (if d.rep (d.core.head e) = d.rep r then
            -slope e (d.length e - 1) else 0)) := by
  classical
  rw [d.prin_eq_sum_slopes hslope, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro e _he
  rw [Finset.sum_add_distrib]
  by_cases hpos : 0 < d.length e
  · have hLeft :
        (∑ o : Fin (d.length e),
          if d.stepLeft e o = d.coreVertex r then slope e o.val else 0) =
          if d.rep (d.core.tail e) = d.rep r then slope e 0 else 0 := by
      by_cases hTail : d.rep (d.core.tail e) = d.rep r
      · simp_rw [d.stepLeft_eq_coreVertex_iff e]
        simp only [hTail, and_true]
        simpa using d.sum_over_first_step hpos (fun o => slope e o.val)
      · have hNever (o : Fin (d.length e)) :
            d.stepLeft e o ≠ d.coreVertex r := by
          simp [d.stepLeft_eq_coreVertex_iff e, hTail]
        simp [hNever, hTail]
    have hRight :
        (∑ o : Fin (d.length e),
          if d.stepRight e o = d.coreVertex r then -slope e o.val else 0) =
          if d.rep (d.core.head e) = d.rep r then
            -slope e (d.length e - 1) else 0 := by
      by_cases hHead : d.rep (d.core.head e) = d.rep r
      · simp_rw [d.stepRight_eq_coreVertex_iff e]
        simp only [hHead, and_true]
        simpa using d.sum_over_last_step hpos (fun o => -slope e o.val)
      · have hNever (o : Fin (d.length e)) :
            d.stepRight e o ≠ d.coreVertex r := by
          simp [d.stepRight_eq_coreVertex_iff e, hHead]
        simp [hNever, hHead]
    rw [hLeft, hRight]
  · have hzero : d.length e = 0 := by omega
    have hEmpty : ∀ f : Fin (d.length e) → ℤ, (∑ o : Fin (d.length e), f o) = 0 := by
      intro f
      apply Finset.sum_eq_zero
      intro o _
      exact absurd o.isLt (by omega)
    rw [hEmpty, hEmpty, add_zero]
    exact (d.zero_slot_cancels (d.rep r) (fun e => slope e 0)
      (fun e => slope e (d.length e - 1)) e hzero (by rw [hzero])).symm

/-- At an interior vertex the Laplacian is the difference of the two adjacent
slopes.  Unchanged in form from the strictly positive case: an interior vertex
only ever exists on a slot of length at least two. -/
theorem prin_interiorVertex_eq_slopeDifference {script : firingScript d.graph}
    {slope : Fin p → ℕ → ℤ} (hslope : d.IsStepSlope script slope)
    (e : Fin p) (o : Fin (d.length e - 1)) :
    prin d.graph script (d.interiorVertex e o) =
      slope e (o.val + 1) - slope e o.val := by
  classical
  rw [d.prin_eq_sum_slopes hslope, Finset.sum_add_distrib]
  have hLeft :
      (∑ s : d.Step,
        if d.stepLeft s.1 s.2 = d.interiorVertex e o then
          slope s.1 s.2.val else 0) = slope e (o.val + 1) := by
    refine (Fintype.sum_eq_single (⟨e, d.nextStep e o⟩ : d.Step) ?_).trans ?_
    · intro s hne
      by_cases hEq : d.stepLeft s.1 s.2 = d.interiorVertex e o
      · exact absurd ((d.stepLeft_eq_interiorVertex_iff s e o).mp hEq) hne
      · exact if_neg hEq
    · rw [if_pos ((d.stepLeft_eq_interiorVertex_iff ⟨e, d.nextStep e o⟩ e o).mpr rfl)]
      rfl
  have hRight :
      (∑ s : d.Step,
        if d.stepRight s.1 s.2 = d.interiorVertex e o then
          -slope s.1 s.2.val else 0) = -slope e o.val := by
    refine (Fintype.sum_eq_single (⟨e, d.previousStep e o⟩ : d.Step) ?_).trans ?_
    · intro s hne
      by_cases hEq : d.stepRight s.1 s.2 = d.interiorVertex e o
      · exact absurd ((d.stepRight_eq_interiorVertex_iff s e o).mp hEq) hne
      · exact if_neg hEq
    · rw [if_pos ((d.stepRight_eq_interiorVertex_iff ⟨e, d.previousStep e o⟩ e o).mpr rfl)]
      rfl
  rw [hLeft, hRight]
  ring

/-! ## The fibre form: a row's per-core-vertex lemmas, reused by addition -/

/-- **Additivity across a face.**  The Laplacian at a contracted class is the
sum, over the members of that class, of the *uncontracted* per-core-vertex
endpoint formula — the same expression `SlopeScript`'s
`prin_coreVertex_eq_endpointSum` produces on a strictly positive `Spec`.

This is what makes a retrofit additive rather than per-face: a row proves its
value lemmas once, at each of the `n` core vertices, and every face reads them
off by summing over classes. -/
theorem prin_coreVertex_eq_classSum {script : firingScript d.graph}
    {slope : Fin p → ℕ → ℤ} (hslope : d.IsStepSlope script slope) (r : Fin n) :
    prin d.graph script (d.coreVertex r) =
      ∑ v ∈ Finset.univ.filter (fun v : Fin n => d.rep v = d.rep r),
        ∑ e : Fin p,
          ((if d.core.tail e = v then slope e 0 else 0) +
            (if d.core.head e = v then -slope e (d.length e - 1) else 0)) := by
  rw [d.prin_coreVertex_eq_endpointSum hslope r, Finset.sum_add_distrib,
    d.sum_tail_class (d.rep r) (fun e => slope e 0),
    d.sum_head_class (d.rep r) (fun e => -slope e (d.length e - 1)),
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => (Finset.sum_add_distrib).symm

/-- Effectivity transfers across a face for free: a class value is a sum of
member values. -/
theorem sum_nonneg_of_members {F : Fin n → ℤ} (r : Fin n)
    (h : ∀ v : Fin n, 0 ≤ F v) :
    0 ≤ ∑ v ∈ Finset.univ.filter (fun v : Fin n => d.rep v = d.rep r), F v :=
  Finset.sum_nonneg fun v _ => h v

/-- Reachability transfers across a face for free: a class value dominates any
one member's value once every member is non-negative. -/
theorem le_sum_of_member {F : Fin n → ℤ} (r u : Fin n)
    (hu : d.rep u = d.rep r) (h : ∀ v : Fin n, 0 ≤ F v) :
    F u ≤ ∑ v ∈ Finset.univ.filter (fun v : Fin n => d.rep v = d.rep r), F v :=
  Finset.single_le_sum (f := F) (fun v _ => h v)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩)

/-! ## Scripts assembled from per-slot path values -/

/-- The script whose value at path position `k` of slot `edge` is
`value edge k`, and `potential (rep v)` at the class of the core vertex `v`. -/
def slotValueScript (potential : Fin n → ℤ) (value : Fin p → ℕ → ℤ) :
    firingScript d.graph
  | Sum.inl c => potential c.val
  | Sum.inr interior => value interior.1 (interior.2.val + 1)

@[simp] theorem slotValueScript_core (potential : Fin n → ℤ)
    (value : Fin p → ℕ → ℤ) (v : Fin n) :
    d.slotValueScript potential value (d.coreVertex v) =
      potential (d.rep v) := rfl

@[simp] theorem slotValueScript_interior (potential : Fin n → ℤ)
    (value : Fin p → ℕ → ℤ) (e : Fin p) (o : Fin (d.length e - 1)) :
    d.slotValueScript potential value (d.interiorVertex e o) =
      value e (o.val + 1) := rfl

/-- Compatibility of the per-slot values with the core potential.

On a vanishing slot the two conditions collide at index `0` and force
`potential (rep (tail e)) = potential (rep (head e))` — which `rep_zero`
already grants.  So a compatible slot-value script is automatically a
well-defined function on the contracted graph, with no extra field. -/
structure SlotValueCompatible (potential : Fin n → ℤ) (value : Fin p → ℕ → ℤ) :
    Prop where
  tail : ∀ e : Fin p, value e 0 = potential (d.rep (d.core.tail e))
  head : ∀ e : Fin p, value e (d.length e) = potential (d.rep (d.core.head e))

theorem slotValueScript_stepLeft {potential : Fin n → ℤ}
    {value : Fin p → ℕ → ℤ} (hCompat : d.SlotValueCompatible potential value)
    (e : Fin p) (o : Fin (d.length e)) :
    d.slotValueScript potential value (d.stepLeft e o) = value e o.val := by
  unfold stepLeft
  by_cases hz : o.val = 0
  · rw [dif_pos hz, hz]
    exact (hCompat.tail e).symm
  · rw [dif_neg hz]
    show value e (o.val - 1 + 1) = value e o.val
    congr 1
    omega

theorem slotValueScript_stepRight {potential : Fin n → ℤ}
    {value : Fin p → ℕ → ℤ} (hCompat : d.SlotValueCompatible potential value)
    (e : Fin p) (o : Fin (d.length e)) :
    d.slotValueScript potential value (d.stepRight e o) =
      value e (o.val + 1) := by
  unfold stepRight
  by_cases hl : o.val + 1 = d.length e
  · rw [dif_pos hl, hl]
    exact (hCompat.head e).symm
  · rw [dif_neg hl]
    exact d.slotValueScript_interior potential value e
      ⟨o.val, by have := o.isLt; omega⟩

theorem isStepSlope_slotValueScript {potential : Fin n → ℤ}
    {value : Fin p → ℕ → ℤ} (hCompat : d.SlotValueCompatible potential value) :
    d.IsStepSlope (d.slotValueScript potential value)
      (fun e k => value e (k + 1) - value e k) := by
  intro e o
  rw [d.slotValueScript_stepRight hCompat, d.slotValueScript_stepLeft hCompat]

/-! ## Agreement with the strictly positive layer

At a strictly positive length vector `rep` is the identity, so every statement
above is the corresponding `SlopeScript` statement transported along
`laplacianEquivToSpec`.  Nothing in `SlopeScript` is restated or weakened. -/

theorem isStepSlope_congr {script : firingScript d.graph}
    {slope slope' : Fin p → ℕ → ℤ}
    (h : ∀ (e : Fin p) (k : ℕ), k < d.length e → slope e k = slope' e k)
    (hslope : d.IsStepSlope script slope) : d.IsStepSlope script slope' := by
  intro e o
  rw [hslope e o]
  exact h e o.val o.isLt

/-- On the interior the class sum degenerates to a single term, so
`prin_coreVertex_eq_classSum` reduces literally to the `Spec` formula. -/
theorem classFilter_eq_singleton_of_pos (hpos : ∀ e : Fin p, 0 < d.length e)
    (r : Fin n) :
    Finset.univ.filter (fun v : Fin n => d.rep v = d.rep r) = {r} := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [d.rep_eq_self_of_pos hpos v, d.rep_eq_self_of_pos hpos r]

/-- Consistency with the strictly positive layer: on the interior the class
sum collapses to a single term and the formula is literally
`SubdivisionGraph.Spec.prin_coreVertex_eq_endpointSum`. -/
theorem prin_coreVertex_eq_endpointSum_of_pos {script : firingScript d.graph}
    {slope : Fin p → ℕ → ℤ} (hslope : d.IsStepSlope script slope)
    (hpos : ∀ e : Fin p, 0 < d.length e) (r : Fin n) :
    prin d.graph script (d.coreVertex r) =
      ∑ e : Fin p,
        ((if d.core.tail e = r then slope e 0 else 0) +
          (if d.core.head e = r then -slope e (d.length e - 1) else 0)) := by
  rw [d.prin_coreVertex_eq_classSum hslope r,
    d.classFilter_eq_singleton_of_pos hpos r, Finset.sum_singleton]

end DegSpec

end Utilities.Certificate.DegenerateSpec
