/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateInterpolation

/-!
# From a closed-orthant explicit-potential record to rank one

This is the `DegSpec`/`ValidClosed` counterpart of the assembly half of
`Certificate/ExplicitPotentialRankOne.lean`: the divisor extended over the
contracted subdivision, the anchor firing script, effectivity of the removed-chip
residual, core reachability, and the rank-one conclusion under a strong-separator
certificate.  Nothing existing is modified; `subdivisionSpec`,
`subdivisionDivisor` and `bnExists_of_valid_of_strongSeparator` keep working
verbatim on the open orthant.

## The two shape changes a consumer sees

1. **`degenerateDivisor`, not `subdivisionDivisor`.**  `DegSpec.coreVertex` is
   *not injective*, so a `Fin n`-indexed divisor is ill-posed on a face: two
   named core vertices can be the same graph vertex.  The extended divisor
   therefore gives a class the **sum** of its members' chips, which is exactly
   what keeps `deg` equal to the checked core degree
   (`deg_degenerateDivisor`).

2. **Class-level endpoint bookkeeping.**  `lowerEndpointContribution_le_endpointContribution`
   is *false vertex by vertex* at a face: on a collapsed slot the certificate
   bounds `α_e ≤ step` and `β_e ≤ -step` are unavailable (they need a unit
   step).  What is true, and what the Laplacian actually needs, is the
   inequality at a contracted **class**, where the collapsed slot contributes
   `α_e + β_e ≤ 0` on the left and exactly `0` on the right because its two
   endpoint terms are equal and opposite.  That is
   `classLowerEndpointContribution_le_classEndpointContribution`, and
   `class_core_balance_nonnegative` is the corresponding balance.  On the
   interior the class is a singleton and both collapse to the existing
   statements.

## The one input the certificate does not determine

`DegSpec.RepInvariant` — that the anchor potential is constant on each
contracted class.  `ValidClosed` gives it along each *individual* collapsed slot
for free (`potential_eq_of_segment_eval_zero`); what it cannot give is that
`rep` merges only vertices joined by chains of collapsed slots, because `rep`
names the face and the certificate does not.  `ZeroReach` and
`repInvariant_evaluatedPotential_of_zeroReach` below discharge it from such a
chain; that is the exact join with the contraction census.
-/

-- `Certificate` is a structure inside a namespace already ending in `Certificate`;
-- renaming either would ripple through every consumer.  Lean v4.33 added
-- `linter.dupNamespace`, which flags exactly this shape.
namespace Utilities.Certificate
open Utilities.Certificate

open Utilities

open Finset ExplicitPotential

/-! ## Fibre regrouping for an arbitrary endpoint map

`Utilities.Certificate.DegenerateSpec.DegSpec.sum_tail_class` / `sum_head_class` are the same
statement for `d.core.tail` / `d.core.head`; this is the version used by the
certificate-level bookkeeping, where no `DegSpec` is in scope yet. -/

theorem sum_endpointIndicator_class {n p : ℕ} (rep : Fin n → Fin n)
    (endpoint : Fin p → Fin n) (r : Fin n) (F : Fin p → ℤ) :
    ∑ e : Fin p, (if rep (endpoint e) = rep r then F e else 0)
      = ∑ v ∈ Finset.univ.filter (fun v : Fin n => rep v = rep r),
          ∑ e : Fin p, (if endpoint e = v then F e else 0) := by
  classical
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : rep (endpoint e) = rep r
  · rw [if_pos h, Finset.sum_eq_single_of_mem (endpoint e)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      (fun b _ hb => if_neg (fun hEq => hb hEq.symm))]
    exact (if_pos rfl).symm
  · rw [if_neg h]
    symm
    refine Finset.sum_eq_zero fun v hv => ?_
    refine if_neg ?_
    rintro rfl
    exact h (Finset.mem_filter.mp hv).2

end Utilities.Certificate

namespace Utilities.Certificate.ExplicitPotential.Certificate
open Utilities
open Utilities.Certificate

open Utilities.Certificate
open Utilities
open Finset ExplicitPotential
open Utilities.Certificate.ExplicitPotential
open Utilities.Certificate.ExplicitPotential.Certificate

variable {m n p : ℕ}

/-! ## Endpoint bookkeeping at a contracted class -/

/-- Conservative endpoint bookkeeping, summed over a contracted class. -/
def classLowerEndpointContribution (certificate : Certificate m n p)
    (rep : Fin n → Fin n) (anchor r : Fin n) : ℤ :=
  ∑ vertex ∈ Finset.univ.filter (fun v : Fin n => rep v = rep r),
    certificate.lowerEndpointContribution anchor vertex

/-- Actual interpolated endpoint contribution, summed over a contracted class. -/
def classEndpointContribution (certificate : Certificate m n p)
    (rep : Fin n → Fin n) (anchor : Fin n) (point : Fin m → ℤ) (r : Fin n) : ℤ :=
  ∑ vertex ∈ Finset.univ.filter (fun v : Fin n => rep v = rep r),
    certificate.endpointContribution anchor point vertex

/-- Target coefficient after removing the anchor chip, summed over a contracted
class. -/
def classTargetCoefficient (certificate : Certificate m n p)
    (rep : Fin n → Fin n) (anchor r : Fin n) : ℤ :=
  ∑ vertex ∈ Finset.univ.filter (fun v : Fin n => rep v = rep r),
    certificate.targetCoefficient anchor vertex

theorem classLowerEndpointContribution_eq (certificate : Certificate m n p)
    (rep : Fin n → Fin n) (anchor r : Fin n) :
    certificate.classLowerEndpointContribution rep anchor r =
      ∑ e : Fin p,
        ((if rep (certificate.core.tail e) = rep r then
            (certificate.witness anchor).alpha e else 0) +
          (if rep (certificate.core.head e) = rep r then
            (certificate.witness anchor).beta e else 0)) := by
  classical
  symm
  rw [Finset.sum_add_distrib,
    sum_endpointIndicator_class rep certificate.core.tail r
      (fun e => (certificate.witness anchor).alpha e),
    sum_endpointIndicator_class rep certificate.core.head r
      (fun e => (certificate.witness anchor).beta e),
    ← Finset.sum_add_distrib]
  unfold classLowerEndpointContribution lowerEndpointContribution
  exact Finset.sum_congr rfl fun v _ => (Finset.sum_add_distrib).symm

theorem classEndpointContribution_eq (certificate : Certificate m n p)
    (rep : Fin n → Fin n) (anchor : Fin n) (point : Fin m → ℤ) (r : Fin n) :
    certificate.classEndpointContribution rep anchor point r =
      ∑ e : Fin p,
        ((if rep (certificate.core.tail e) = rep r then
            SubdivisionArithmetic.step (certificate.segmentNat point e)
              (certificate.riseValue anchor point e) 0 else 0) +
          (if rep (certificate.core.head e) = rep r then
            -SubdivisionArithmetic.step (certificate.segmentNat point e)
              (certificate.riseValue anchor point e)
              (certificate.segmentNat point e - 1) else 0)) := by
  classical
  symm
  rw [Finset.sum_add_distrib,
    sum_endpointIndicator_class rep certificate.core.tail r
      (fun e => SubdivisionArithmetic.step (certificate.segmentNat point e)
        (certificate.riseValue anchor point e) 0),
    sum_endpointIndicator_class rep certificate.core.head r
      (fun e => -SubdivisionArithmetic.step (certificate.segmentNat point e)
        (certificate.riseValue anchor point e)
        (certificate.segmentNat point e - 1)),
    ← Finset.sum_add_distrib]
  unfold classEndpointContribution endpointContribution
  exact Finset.sum_congr rfl fun v _ => (Finset.sum_add_distrib).symm

theorem classTargetCoefficient_eq (certificate : Certificate m n p)
    (rep : Fin n → Fin n) (anchor r : Fin n) :
    certificate.classTargetCoefficient rep anchor r =
      (∑ v ∈ Finset.univ.filter (fun v : Fin n => rep v = rep r),
          certificate.divisor v) -
        (if rep anchor = rep r then 1 else 0) := by
  classical
  unfold classTargetCoefficient targetCoefficient
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_ite_eq' (Finset.univ.filter (fun v : Fin n => rep v = rep r))
    anchor (fun _ => (1 : ℤ))]
  simp

/-- **Gap 2, the comparison.**  The conservative endpoint bound is still
conservative at a contracted class.  On a surviving slot this is the existing
`interpolated_endpoint_bounds` argument, recovered from `ValidClosed` by
`interpolated_endpoint_bounds_of_validClosed`.  On a collapsed slot the actual
contribution is exactly `0`, because the two endpoint terms lie in the same
class and are equal and opposite, while the bound contributes
`α_e + β_e ≤ 0` — `Valid`'s third conjunct, unchanged. -/
theorem classLowerEndpointContribution_le_classEndpointContribution
    (certificate : Certificate m n p) {degree : ℤ}
    (hValid : certificate.ValidClosed degree) (point : Fin m → ℤ)
    (hCone : FormsHold certificate.cone point)
    (rep : Fin n → Fin n)
    (hRepZero : ∀ e : Fin p, certificate.segmentNat point e = 0 →
      rep (certificate.core.tail e) = rep (certificate.core.head e))
    (anchor r : Fin n) :
    certificate.classLowerEndpointContribution rep anchor r ≤
      certificate.classEndpointContribution rep anchor point r := by
  classical
  rw [certificate.classLowerEndpointContribution_eq rep anchor r,
    certificate.classEndpointContribution_eq rep anchor point r]
  refine Finset.sum_le_sum fun e _ => ?_
  by_cases hpos : 0 < certificate.segmentNat point e
  · have hBounds := certificate.interpolated_endpoint_bounds_of_validClosed
      hValid point hCone anchor e hpos
    by_cases hTail : rep (certificate.core.tail e) = rep r <;>
      by_cases hHead : rep (certificate.core.head e) = rep r <;>
        simp only [hTail, ↓reduceIte, hHead, le_add_neg_iff_add_le, ge_iff_le, add_zero, zero_add,
          Std.le_refl]<;> omega
  · have hzero : certificate.segmentNat point e = 0 := by omega
    have hSame := hRepZero e hzero
    have hab := hValid.2.2.1 anchor e
    rw [hSame, hzero]
    by_cases hHead : rep (certificate.core.head e) = rep r <;>
      simp [hHead]
    omega

/-- **Gap 2, the balance.**  At every contracted class the target plus the
actual interpolated contributions is non-negative. -/
theorem class_core_balance_nonnegative
    (certificate : Certificate m n p) {degree : ℤ}
    (hValid : certificate.ValidClosed degree) (point : Fin m → ℤ)
    (hCone : FormsHold certificate.cone point)
    (rep : Fin n → Fin n)
    (hRepZero : ∀ e : Fin p, certificate.segmentNat point e = 0 →
      rep (certificate.core.tail e) = rep (certificate.core.head e))
    (anchor r : Fin n) :
    0 ≤ certificate.classTargetCoefficient rep anchor r +
      certificate.classEndpointContribution rep anchor point r := by
  classical
  have hle := certificate.classLowerEndpointContribution_le_classEndpointContribution
    hValid point hCone rep hRepZero anchor r
  have hlow : 0 ≤ certificate.classTargetCoefficient rep anchor r +
      certificate.classLowerEndpointContribution rep anchor r := by
    unfold classTargetCoefficient classLowerEndpointContribution
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_nonneg fun v _ => hValid.2.2.2.1 anchor v
  omega

/-- On the interior the class is a singleton, so the class-level statements are
literally the existing per-vertex ones. -/
theorem classEndpointContribution_eq_of_rep_id (certificate : Certificate m n p)
    (rep : Fin n → Fin n) (hId : ∀ v : Fin n, rep v = v)
    (anchor : Fin n) (point : Fin m → ℤ) (r : Fin n) :
    certificate.classEndpointContribution rep anchor point r =
      certificate.endpointContribution anchor point r := by
  classical
  have hFilter : (Finset.univ.filter (fun v : Fin n => rep v = rep r)) = {r} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [hId v, hId r]
  unfold classEndpointContribution
  rw [hFilter, Finset.sum_singleton]

/-! ## Rep-invariance of the anchor potential -/

/-- Two core vertices joined by one collapsed slot. -/
def ZeroLink (certificate : Certificate m n p) (point : Fin m → ℤ)
    (u v : Fin n) : Prop :=
  ∃ e : Fin p, certificate.segmentNat point e = 0 ∧
    ((certificate.core.tail e = u ∧ certificate.core.head e = v) ∨
      (certificate.core.tail e = v ∧ certificate.core.head e = u))

/-- Joined by a chain of collapsed slots.  This is the relation a contraction
census decides; `rep` is meant to be its component map. -/
def ZeroReach (certificate : Certificate m n p) (point : Fin m → ℤ) :
    Fin n → Fin n → Prop :=
  Relation.ReflTransGen (certificate.ZeroLink point)

theorem segment_eval_eq_zero_of_segmentNat_eq_zero
    (certificate : Certificate m n p) {degree : ℤ}
    (hValid : certificate.ValidClosed degree) (point : Fin m → ℤ)
    (hCone : FormsHold certificate.cone point) {e : Fin p}
    (hzero : certificate.segmentNat point e = 0) :
    (certificate.segment e).eval point = 0 := by
  have hCast := certificate.segmentNat_cast_eq_of_validClosed hValid point hCone e
  rw [hzero] at hCast
  simpa using hCast.symm

theorem evaluatedPotential_eq_of_zeroLink
    (certificate : Certificate m n p) {degree : ℤ}
    (hValid : certificate.ValidClosed degree) (point : Fin m → ℤ)
    (hCone : FormsHold certificate.cone point) (anchor : Fin n)
    {u v : Fin n} (hLink : certificate.ZeroLink point u v) :
    certificate.evaluatedPotential anchor point u =
      certificate.evaluatedPotential anchor point v := by
  obtain ⟨e, hzero, hcase⟩ := hLink
  have hEval := certificate.segment_eval_eq_zero_of_segmentNat_eq_zero
    hValid point hCone hzero
  have hPot := certificate.potential_eq_of_segment_eval_zero hValid point hCone
    anchor e hEval
  rcases hcase with ⟨hTail, hHead⟩ | ⟨hTail, hHead⟩
  · subst hTail
    subst hHead
    exact hPot.symm
  · subst hTail
    subst hHead
    exact hPot

theorem evaluatedPotential_eq_of_zeroReach
    (certificate : Certificate m n p) {degree : ℤ}
    (hValid : certificate.ValidClosed degree) (point : Fin m → ℤ)
    (hCone : FormsHold certificate.cone point) (anchor : Fin n)
    {u v : Fin n} (hReach : certificate.ZeroReach point u v) :
    certificate.evaluatedPotential anchor point u =
      certificate.evaluatedPotential anchor point v := by
  induction hReach with
  | refl => rfl
  | tail _ hStep ih =>
      exact ih.trans (certificate.evaluatedPotential_eq_of_zeroLink hValid point
        hCone anchor hStep)

/-! ## The face named by a contraction datum -/

section Face

variable (certificate : Certificate m n p) (point : Fin m → ℤ)
  (core_nonempty : 0 < n) (rep : Fin n → Fin n)
  (rep_idem : ∀ v : Fin n, rep (rep v) = rep v)
  (rep_zero : ∀ edge : Fin p, certificate.segmentNat point edge = 0 →
    rep (certificate.core.tail edge) = rep (certificate.core.head edge))
  (rep_loopless : ∀ edge : Fin p, 0 < certificate.segmentNat point edge →
    rep (certificate.core.tail edge) ≠ rep (certificate.core.head edge))
  (forest : (Finset.univ.image rep).card
    + (Finset.univ.filter
        (fun edge : Fin p => certificate.segmentNat point edge = 0)).card = n)

/-- The rep-invariance obligation, discharged from a chain of collapsed slots.
This is the exact join with a contraction census: the census produces `rep`
together with the reachability witness. -/
theorem repInvariant_evaluatedPotential_of_zeroReach {degree : ℤ}
    (hValid : certificate.ValidClosed degree)
    (hCone : FormsHold certificate.cone point) (anchor : Fin n)
    (hReach : ∀ v : Fin n, certificate.ZeroReach point v (rep v)) :
    (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
      rep_loopless forest).RepInvariant
        (certificate.evaluatedPotential anchor point) := fun v =>
  (certificate.evaluatedPotential_eq_of_zeroReach hValid point hCone anchor
    (hReach v)).symm

/-- On the interior of the orthant the obligation is free. -/
theorem repInvariant_evaluatedPotential_of_pos
    (hpos : ∀ edge : Fin p, 0 < certificate.segmentNat point edge)
    (anchor : Fin n) :
    (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
      rep_loopless forest).RepInvariant
        (certificate.evaluatedPotential anchor point) :=
  Utilities.Certificate.DegenerateSpec.DegSpec.repInvariant_of_pos _ hpos _

/-- The degenerate rise is the certificate's numerical rise, verbatim: no `rep`
enters `DegSpec.coreRise`. -/
theorem coreRise_evaluatedPotential_degenerate (anchor : Fin n) (edge : Fin p) :
    (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
        rep_loopless forest).coreRise
        (certificate.evaluatedPotential anchor point) edge =
      certificate.riseValue anchor point edge := by
  simp [evaluatedPotential, degenerateSpec,
    Utilities.Certificate.DegenerateSpec.DegSpec.coreRise, riseValue, rise]

end Face

/-! ## The extended divisor -/

/-- The atlas divisor, pushed to the contracted core: a class carries the total
of its members' chips, and every interior vertex carries none.

This is the shape change forced by non-injectivity of `coreVertex`. -/
def degenerateDivisor (certificate : Certificate m n p)
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p) : CFDiv d.graph :=
  d.coreClassDivisor certificate.divisor

@[simp] theorem degenerateDivisor_coreVertex (certificate : Certificate m n p)
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p) (r : Fin n) :
    certificate.degenerateDivisor d (d.coreVertex r) =
      ∑ v ∈ Finset.univ.filter (fun v : Fin n => d.rep v = d.rep r),
        certificate.divisor v := rfl

@[simp] theorem degenerateDivisor_interiorVertex (certificate : Certificate m n p)
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p) (e : Fin p) (o : Fin (d.length e - 1)) :
    certificate.degenerateDivisor d (d.interiorVertex e o) = 0 := rfl

/-- Agreement with the strictly positive layer: on the interior each class is a
singleton, so the extended divisor is literally `subdivisionDivisor`'s value. -/
theorem degenerateDivisor_coreVertex_of_pos (certificate : Certificate m n p)
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p) (hpos : ∀ e : Fin p, 0 < d.length e)
    (r : Fin n) :
    certificate.degenerateDivisor d (d.coreVertex r) = certificate.divisor r := by
  classical
  rw [degenerateDivisor_coreVertex, d.classFilter_eq_singleton_of_pos hpos r,
    Finset.sum_singleton]

/-- The extended divisor has exactly the degree checked on the core: no chip is
lost when two named core vertices are merged. -/
theorem deg_degenerateDivisor (certificate : Certificate m n p)
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p) :
    deg (certificate.degenerateDivisor d) =
      ∑ v : Fin n, certificate.divisor v := by
  classical
  have hFiber : ∀ c : d.Class,
      (Finset.univ.filter (fun v : Fin n => d.rep v = c.val))
        = Finset.univ.filter
            (fun v : Fin n => (⟨d.rep v, d.rep_idem v⟩ : d.Class) = c) := by
    intro c
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hsplit : deg (certificate.degenerateDivisor d)
      = ∑ c : d.Class, ∑ v ∈ Finset.univ.filter (fun v : Fin n => d.rep v = c.val),
          certificate.divisor v := by
    simp [deg, degenerateDivisor,
      Utilities.Certificate.DegenerateSpec.DegSpec.coreClassDivisor,
      Fintype.sum_sum_type]
  rw [hsplit, Finset.sum_congr rfl (fun c _ => by rw [hFiber c])]
  exact Finset.sum_fiberwise Finset.univ
    (fun v : Fin n => (⟨d.rep v, d.rep_idem v⟩ : d.Class)) certificate.divisor

/-! ## The anchor script and its residual -/

section Assembly

variable (certificate : Certificate m n p) (point : Fin m → ℤ)
  (core_nonempty : 0 < n) (rep : Fin n → Fin n)
  (rep_idem : ∀ v : Fin n, rep (rep v) = rep v)
  (rep_zero : ∀ edge : Fin p, certificate.segmentNat point edge = 0 →
    rep (certificate.core.tail edge) = rep (certificate.core.head edge))
  (rep_loopless : ∀ edge : Fin p, 0 < certificate.segmentNat point edge →
    rep (certificate.core.tail edge) ≠ rep (certificate.core.head edge))
  (forest : (Finset.univ.image rep).card
    + (Finset.univ.filter
        (fun edge : Fin p => certificate.segmentNat point edge = 0)).card = n)

/-- The firing script attached to a core anchor, assembled on the contracted
subdivision by canonical integral interpolation. -/
def degenerateAnchorScript (anchor : Fin n) :
    firing_script (certificate.degenerateSpec point core_nonempty rep rep_idem
      rep_zero rep_loopless forest).graph :=
  Utilities.Certificate.DegenerateSpec.DegSpec.interpolatedScript
    (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
      rep_loopless forest)
    (certificate.evaluatedPotential anchor point)

/-- The Laplacian of the anchor script at a contracted class is the class-level
endpoint contribution.  This is the bridge between the graph layer and the
class-level bookkeeping of gap 2. -/
theorem prin_degenerateAnchorScript_coreVertex (anchor r : Fin n)
    (hInv : (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
      rep_loopless forest).RepInvariant
        (certificate.evaluatedPotential anchor point)) :
    prin (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
        rep_loopless forest).graph
      (certificate.degenerateAnchorScript point core_nonempty rep rep_idem
        rep_zero rep_loopless forest anchor)
      ((certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
        rep_loopless forest).coreVertex r) =
      certificate.classEndpointContribution rep anchor point r := by
  classical
  rw [degenerateAnchorScript,
    Utilities.Certificate.DegenerateSpec.DegSpec.prin_interpolatedScript_coreVertex_eq_classSum _ hInv r]
  unfold classEndpointContribution endpointContribution
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun e _ => ?_
  rw [certificate.coreRise_evaluatedPotential_degenerate point core_nonempty rep
    rep_idem rep_zero rep_loopless forest anchor e]
  rfl

/-- **The rank-one input.**  The removed-chip residual of a checked closed-orthant
record is effective at every vertex of the contracted subdivision. -/
theorem effective_degenerateAnchorResidual {degree : ℤ}
    (hValid : certificate.ValidClosed degree)
    (hCone : FormsHold certificate.cone point) (anchor : Fin n)
    (hInv : (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
      rep_loopless forest).RepInvariant
        (certificate.evaluatedPotential anchor point)) :
    effective
      (certificate.degenerateDivisor
          (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
            rep_loopless forest) -
        one_chip
          ((certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
            rep_loopless forest).coreVertex anchor) +
        prin (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
            rep_loopless forest).graph
          (certificate.degenerateAnchorScript point core_nonempty rep rep_idem
            rep_zero rep_loopless forest anchor)) := by
  classical
  set d := certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
    rep_loopless forest with hd
  intro vertex
  rcases vertex with c | interior
  · have hInl : (Sum.inl c : d.Vertex) = d.coreVertex c.val :=
      (congrArg Sum.inl (Subtype.ext c.property)).symm
    have hRepC : d.rep c.val = c.val := c.property
    simp only [ge_iff_le, Pi.add_apply, Pi.sub_apply]
    rw [hInl, degenerateDivisor_coreVertex,
      certificate.prin_degenerateAnchorScript_coreVertex point core_nonempty rep
        rep_idem rep_zero rep_loopless forest anchor c.val hInv]
    have hChip : one_chip (G := d.graph) (d.coreVertex anchor) (d.coreVertex c.val) =
        (if rep anchor = rep c.val then 1 else 0) := by
      unfold one_chip
      by_cases h : rep anchor = rep c.val
      · rw [if_pos ((d.coreVertex_eq_iff c.val anchor).mpr h.symm), if_pos h]
      · rw [if_neg (fun hEq => h (((d.coreVertex_eq_iff c.val anchor).mp hEq)).symm),
          if_neg h]
    rw [hChip]
    have hBalance := certificate.class_core_balance_nonnegative hValid point hCone
      rep rep_zero anchor c.val
    rw [certificate.classTargetCoefficient_eq rep anchor c.val] at hBalance
    have hRepFilter : (Finset.univ.filter (fun v : Fin n => d.rep v = d.rep c.val))
        = Finset.univ.filter (fun v : Fin n => rep v = rep c.val) := rfl
    rw [hRepFilter]
    omega
  · rcases interior with ⟨e, o⟩
    simp only [ge_iff_le, Pi.add_apply, Pi.sub_apply]
    have hInr : (Sum.inr ⟨e, o⟩ : d.Vertex) = d.interiorVertex e o := rfl
    rw [hInr]
    have hChip : one_chip (G := d.graph) (d.coreVertex anchor)
        (d.interiorVertex e o) = 0 := by
      unfold one_chip Utilities.Certificate.DegenerateSpec.DegSpec.coreVertex
        Utilities.Certificate.DegenerateSpec.DegSpec.interiorVertex
      simp
    rw [degenerateDivisor_interiorVertex, hChip]
    have hInterior :=
      Utilities.Certificate.DegenerateSpec.DegSpec.prin_interpolatedScript_interiorVertex_nonneg d hInv e o
    change (0 : ℤ) ≤ 0 - 0 + prin d.graph
      (Utilities.Certificate.DegenerateSpec.DegSpec.interpolatedScript d
        (certificate.evaluatedPotential anchor point)) (d.interiorVertex e o)
    omega

/-- Every core class is reached by the divisor assembled from a checked
closed-orthant record. -/
theorem reaches_degenerateCoreVertex {degree : ℤ}
    (hValid : certificate.ValidClosed degree)
    (hCone : FormsHold certificate.cone point) (anchor : Fin n)
    (hInv : (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
      rep_loopless forest).RepInvariant
        (certificate.evaluatedPotential anchor point)) :
    StrongSeparator.Reaches
      (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
        rep_loopless forest).graph
      (certificate.degenerateDivisor
        (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
          rep_loopless forest))
      ((certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
        rep_loopless forest).coreVertex anchor) := by
  set d := certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
    rep_loopless forest with hd
  refine ⟨certificate.degenerateDivisor d - one_chip (d.coreVertex anchor) +
    prin d.graph (certificate.degenerateAnchorScript point core_nonempty rep
      rep_idem rep_zero rep_loopless forest anchor),
    certificate.effective_degenerateAnchorResidual point core_nonempty rep
      rep_idem rep_zero rep_loopless forest hValid hCone anchor hInv, ?_⟩
  exact StrongSeparator.linearEquiv_add_prin
    (certificate.degenerateDivisor d - one_chip (d.coreVertex anchor))
    (certificate.degenerateAnchorScript point core_nonempty rep rep_idem rep_zero
      rep_loopless forest anchor)

end Assembly

/-! ## The embedded core classes -/

/-- The embedded core classes of a contracted subdivision.  `coreVertex` is not
injective, so this image can be strictly smaller than `n`. -/
def degenerateCoreVertices (d : Utilities.Certificate.DegenerateSpec.DegSpec n p) : Finset d.graph.V :=
  Finset.univ.image d.coreVertex

theorem degenerateCoreVertices_nonempty (d : Utilities.Certificate.DegenerateSpec.DegSpec n p) :
    (degenerateCoreVertices d).Nonempty :=
  ⟨d.coreVertex ⟨0, d.core_nonempty⟩,
    Finset.mem_image.mpr ⟨⟨0, d.core_nonempty⟩, Finset.mem_univ _, rfl⟩⟩

@[simp] theorem coreVertex_mem_degenerateCoreVertices
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p) (v : Fin n) :
    d.coreVertex v ∈ degenerateCoreVertices d :=
  Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩

@[simp] theorem interiorVertex_not_mem_degenerateCoreVertices
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p) (e : Fin p) (o : Fin (d.length e - 1)) :
    d.interiorVertex e o ∉ degenerateCoreVertices d := by
  simp [degenerateCoreVertices, Utilities.Certificate.DegenerateSpec.DegSpec.coreVertex,
    Utilities.Certificate.DegenerateSpec.DegSpec.interiorVertex]

/-! ## End-to-end local soundness on the closed orthant -/

/-- **The closed-orthant counterpart of `bnExists_of_valid_of_strongSeparator`.**

An accepted closed-orthant record, at one integral length point together with a
contraction datum naming a face, proves `BNExists` for the contracted
subdivision — which, by `DegSpec.Contraction.laplacianEquiv`, is the strictly
positive subdivision of the contracted core.  On the interior (`rep = id`,
`hInv` free by `repInvariant_evaluatedPotential_of_pos`) this is the existing
statement. -/
theorem bnExists_of_validClosed_of_strongSeparator
    (certificate : Certificate m n p) (point : Fin m → ℤ)
    (core_nonempty : 0 < n) (rep : Fin n → Fin n)
    (rep_idem rep_zero rep_loopless forest)
    (degree : ℤ) (hValid : certificate.ValidClosed degree)
    (hCone : FormsHold certificate.cone point)
    (hInv : ∀ anchor : Fin n,
      (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
        rep_loopless forest).RepInvariant
          (certificate.evaluatedPotential anchor point))
    (hConnected : graph_connected
      (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
        rep_loopless forest).graph)
    (hSeparator : StrongSeparator.StrongSeparatorCertificate
      (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
        rep_loopless forest).graph
      (degenerateCoreVertices
        (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
          rep_loopless forest))) :
    BNExists
      (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
        rep_loopless forest).graph 1 degree := by
  classical
  set d := certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
    rep_loopless forest with hd
  refine ⟨certificate.degenerateDivisor d, ?_, ?_⟩
  · rw [certificate.deg_degenerateDivisor d]
    exact hValid.2.1
  · apply StrongSeparator.rank_ge_one_of_strongSeparatorCertificate
      hConnected (degenerateCoreVertices_nonempty d) hSeparator
    intro coreVertex hCoreVertex
    obtain ⟨anchor, _hAnchor, rfl⟩ := Finset.mem_image.mp hCoreVertex
    exact certificate.reaches_degenerateCoreVertex point core_nonempty rep rep_idem
      rep_zero rep_loopless forest hValid hCone anchor (hInv anchor)

end Utilities.Certificate.ExplicitPotential.Certificate

namespace Utilities.Certificate
open Utilities.Certificate
open Utilities
open Finset ExplicitPotential

end Utilities.Certificate
