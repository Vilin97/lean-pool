/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.AffinePosition
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CoreVertexReachability
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SlopeScript

/-!
# Multi-code divisors and multi-break slope scripts

`AffinePosition` names a single point of a subdivided slot by an affine
offset and decodes it to a typed vertex once the local cone is checked.  Two
row-independent constructions are built on top of it here.

* A **multi-code divisor**.  A finite family of position codes, each with its
  own cone-certified bounds, assembles into the sum of the one-chip divisors
  at the decoded vertices.  Its degree is the number of codes (repetitions
  are allowed and produce multiplicities), it is effective, and its value at
  a vertex is the number of codes decoding to that vertex.  This is the
  divisor format needed by rows whose pencil is not supported on the core.

* A **multi-break slope script**.  `Certificate.SlopeScript` computes the
  Laplacian of a firing script from its unit-step slopes.  The scripts used
  by the genus-four all-length rows have exactly one slope window per slot
  (`rampScript`) or one plateau (`capScript`).  Rows without a cut need
  potentials that bend several times inside one slot.  A *break list* is a
  list of pairs `(start, slope)`: the slope of the script at unit step `k` is
  the value of the last entry whose `start` is at most `k`, and `0` before
  every entry.  The resulting Laplacian is exact:

  - at a core vertex it is the endpoint-slope sum, as always;
  - at an interior vertex it is the jump of the break list there, and in
    particular it **vanishes at every interior vertex which is not a break
    position**.

  Finally the breaks themselves are named by affine position codes, so one
  passive `SlopeScript` datum describes a whole cone of length vectors.

Nothing here is row specific and nothing here is decidable-by-`decide`: the
only Boolean checks are the fail-closed bound checks already introduced by
`AffinePosition`.
-/

@[expose] public section

namespace MarkedGraphs.Certificate
open Utilities.Certificate

open Utilities

open Finset
open ExplicitPotential
open SubdivisionGraph

/-! ## Interior decoding -/

end MarkedGraphs.Certificate

namespace Utilities.Certificate.SubdivisionGraph.Spec
open MarkedGraphs
open MarkedGraphs.Certificate

open Utilities.Certificate
open Utilities
open Finset
open ExplicitPotential
open SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

variable {n p : ℕ} (spec : SubdivisionGraph.Spec n p)

/-- A strictly interior path position names an interior vertex.  This is the
positional form of `pathVertex`'s middle branch. -/
theorem pathVertex_of_interior_val (edge : Fin p) (position : spec.PathPosition edge)
    (hPositive : 0 < position.val) (hStrict : position.val < spec.length edge) :
    spec.pathVertex edge position =
      spec.interiorVertex edge ⟨position.val - 1, by omega⟩ := by
  unfold SubdivisionGraph.Spec.pathVertex
  rw [dite_eq_right (by omega : ¬ position.val = 0),
    dite_eq_right (by omega : ¬ position.val = spec.length edge)]

end Utilities.Certificate.SubdivisionGraph.Spec

namespace MarkedGraphs.Certificate
open Utilities.Certificate
open Utilities
open Finset
open ExplicitPotential
open SubdivisionGraph

namespace AffinePosition
open Utilities.Certificate
open Utilities
open Finset
open ExplicitPotential
open SubdivisionGraph

namespace Code

variable {m n p : ℕ}

/-- An affine position code whose normalized coordinate is strictly interior
decodes to the interior vertex one step below that coordinate. -/
theorem decodeVertex_eq_interiorVertex
    (certificate : ExplicitPotential.Certificate m n p) (code : Code m p)
    (point : Fin m → ℤ) (core_nonempty : 0 < n) {degree : ℤ}
    (hValid : certificate.Valid degree) (hBounds : code.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (hPositive : 0 < code.coordinate certificate point)
    (hStrict : code.coordinate certificate point <
      certificate.segmentNat point code.edge) :
    code.decodeVertex certificate point core_nonempty hValid hBounds hCone =
      (certificate.subdivisionSpec point core_nonempty hValid hCone).interiorVertex
        code.edge ⟨code.coordinate certificate point - 1, by
          have hLength :
              (certificate.subdivisionSpec point core_nonempty hValid hCone).length
                code.edge = certificate.segmentNat point code.edge := rfl
          omega⟩ := by
  unfold decodeVertex
  refine ((certificate.subdivisionSpec point core_nonempty hValid hCone).pathVertex_of_interior_val
    code.edge _ ?_ ?_).trans rfl
  · exact hPositive
  · exact hStrict

end Code

/-! ## Geometry-only certificate carriers

`ExplicitPotential.Certificate.Valid` bundles two unrelated things: the
*geometry* of the length cone (a loopless core and a cone which forces every
segment to be positive) and the *interpolated-script* rank-one data
(`alpha`, `beta`, `potential`, and the endpoint inequalities).  Only the
geometry is needed to form `subdivisionSpec`, and hence to decode affine
positions or to run a multi-break script.

A row whose pencil is not an interpolated script therefore should not have to
invent interpolated-script witnesses.  `carrier` packages a core, its segment
forms and a cone with trivial witness data and the all-ones core divisor, and
`carrier_valid` discharges `Valid` from the two geometric hypotheses alone. -/

namespace Carrier

variable {m n p : ℕ}

/-- A certificate carrying only length geometry.  Its `divisor` and `witness`
fields are placeholders: the real pencil is a `MultiCode` and the real firing
scripts are multi-break scripts. -/
def certificate (core : ExplicitPotential.Core n p)
    (segment : Fin p → ExplicitPotential.AffineForm m)
    (cone : List (ExplicitPotential.AffineForm m)) :
    ExplicitPotential.Certificate m n p where
  core := core
  segment := segment
  divisor := fun _ => 1
  witness := fun _ =>
    { alpha := fun _ => 0
      beta := fun _ => 0
      potential := fun _ => 0 }
  cone := cone

@[simp] theorem certificate_core (core : ExplicitPotential.Core n p)
    (segment : Fin p → ExplicitPotential.AffineForm m)
    (cone : List (ExplicitPotential.AffineForm m)) :
    (certificate core segment cone).core = core := rfl

@[simp] theorem certificate_segment (core : ExplicitPotential.Core n p)
    (segment : Fin p → ExplicitPotential.AffineForm m)
    (cone : List (ExplicitPotential.AffineForm m)) :
    (certificate core segment cone).segment = segment := rfl

@[simp] theorem certificate_cone (core : ExplicitPotential.Core n p)
    (segment : Fin p → ExplicitPotential.AffineForm m)
    (cone : List (ExplicitPotential.AffineForm m)) :
    (certificate core segment cone).cone = cone := rfl

private theorem affineForm_eq_zero {k : ℕ} (form : ExplicitPotential.AffineForm k)
    (hConstant : form.fixedValue = 0)
    (hCoefficient : ∀ coordinate, form.coefficient coordinate = 0) :
    form = 0 := by
  obtain ⟨fixedValue, coefficient⟩ := form
  simp only at hConstant hCoefficient
  subst hConstant
  have hFun : coefficient = fun _ => 0 := funext hCoefficient
  subst hFun
  rfl
/-- A geometry-only carrier is valid as soon as its core is loopless and its
cone literally contains the positivity row of every segment.  No
interpolated-script data is required. -/
theorem certificate_valid (core : ExplicitPotential.Core n p)
    (segment : Fin p → ExplicitPotential.AffineForm m)
    (cone : List (ExplicitPotential.AffineForm m))
    (hLoopless : ∀ edge : Fin p, core.tail edge ≠ core.head edge)
    (hPositive : ∀ edge : Fin p,
      ExplicitPotential.AffineForm.positive (segment edge) ∈ cone) :
    (certificate core segment cone).Valid (n : ℤ) := by
  classical
  refine ⟨hLoopless, ?_, ?_, ?_, ?_, ?_⟩
  · simp [certificate]
  · intro anchor edge
    simp [certificate]
  · intro anchor vertex
    have hContribution :
        (certificate core segment cone).lowerEndpointContribution anchor vertex = 0 := by
      change (∑ edge : Fin p,
        ((if core.tail edge = vertex then (0 : ℤ) else 0) +
          if core.head edge = vertex then (0 : ℤ) else 0)) = 0
      simp
    rw [hContribution, add_zero]
    unfold ExplicitPotential.Certificate.targetCoefficient
    by_cases hAnchor : vertex = anchor <;> simp [certificate, hAnchor]
  · intro edge
    exact Or.inr (hPositive edge)
  · intro anchor edge
    constructor
    · left
      apply affineForm_eq_zero <;>
        simp [ExplicitPotential.Certificate.lowerForm,
          ExplicitPotential.Certificate.rise,
          ExplicitPotential.AffineForm.sub, ExplicitPotential.AffineForm.scale,
          certificate]
    · left
      apply affineForm_eq_zero <;>
        simp [ExplicitPotential.Certificate.upperForm,
          ExplicitPotential.Certificate.rise,
          ExplicitPotential.AffineForm.sub, ExplicitPotential.AffineForm.scale,
          certificate]

end Carrier

/-! ## Multi-code divisors -/

/-- A finite family of affine position codes.  Repetitions are allowed and
become chip multiplicities in `divisorOf`. -/
structure MultiCode (m p d : ℕ) where
  /-- The indexed family of affine positions; repeated positions contribute repeated chips to
  its divisor. -/
  code : Fin d → Code m p

namespace MultiCode

variable {m n p d : ℕ}

/-- Every code of the family has its two bound rows in the local cone. -/
def BoundsCertified (certificate : ExplicitPotential.Certificate m n p)
    (family : MultiCode m p d) : Prop :=
  ∀ index : Fin d, (family.code index).BoundsCertified certificate

/-- Fail-closed executable bounds check for a whole family. -/
def checkBounds (certificate : ExplicitPotential.Certificate m n p)
    (family : MultiCode m p d) : Bool :=
  ExplicitPotential.allFin fun index => (family.code index).checkBounds certificate

@[simp] theorem checkBounds_eq_true_iff
    (certificate : ExplicitPotential.Certificate m n p)
    (family : MultiCode m p d) :
    family.checkBounds certificate = true ↔ family.BoundsCertified certificate := by
  simp [checkBounds, BoundsCertified]

/-- The decoded subdivision vertex of one member of the family. -/
def vertex (certificate : ExplicitPotential.Certificate m n p)
    (family : MultiCode m p d) (point : Fin m → ℤ) (core_nonempty : 0 < n)
    {degree : ℤ} (hValid : certificate.Valid degree)
    (hBounds : family.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) (index : Fin d) :
    (certificate.subdivisionSpec point core_nonempty hValid hCone).Vertex :=
  (family.code index).decodeVertex certificate point core_nonempty hValid
    (hBounds index) hCone

/-- The divisor named by a family of affine position codes. -/
def divisorOf (certificate : ExplicitPotential.Certificate m n p)
    (family : MultiCode m p d) (point : Fin m → ℤ) (core_nonempty : 0 < n)
    {degree : ℤ} (hValid : certificate.Valid degree)
    (hBounds : family.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) :
    CFDiv (certificate.subdivisionSpec point core_nonempty hValid hCone).graph :=
  ∑ index : Fin d,
    oneChip (family.vertex certificate point core_nonempty hValid hBounds hCone index)

theorem divisorOf_apply
    (certificate : ExplicitPotential.Certificate m n p)
    (family : MultiCode m p d) (point : Fin m → ℤ) (core_nonempty : 0 < n)
    {degree : ℤ} (hValid : certificate.Valid degree)
    (hBounds : family.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (target : (certificate.subdivisionSpec point core_nonempty hValid hCone).Vertex) :
    family.divisorOf certificate point core_nonempty hValid hBounds hCone target =
      ((Finset.univ.filter fun index : Fin d =>
        family.vertex certificate point core_nonempty hValid hBounds hCone index =
          target).card : ℤ) := by
  classical
  have hSum :
      family.divisorOf certificate point core_nonempty hValid hBounds hCone target =
        ∑ index : Fin d,
          (oneChip
              (family.vertex certificate point core_nonempty hValid hBounds hCone index) :
            CFDiv (certificate.subdivisionSpec point core_nonempty hValid hCone).graph)
            target := by
    simp [divisorOf, Finset.sum_apply]
  rw [hSum]
  have hTerm : ∀ index : Fin d,
      (oneChip
            (family.vertex certificate point core_nonempty hValid hBounds hCone index) :
          CFDiv (certificate.subdivisionSpec point core_nonempty hValid hCone).graph)
          target =
        if family.vertex certificate point core_nonempty hValid hBounds hCone index = target
          then (1 : ℤ) else 0 := by
    intro index
    by_cases hEq :
        family.vertex certificate point core_nonempty hValid hBounds hCone index = target
    · simp [oneChip, hEq]
    · rw [ite_eq_right hEq]
      simp only [oneChip]
      exact ite_eq_right fun hAbsurd => hEq hAbsurd.symm
  simp only [hTerm]
  exact Finset.sum_boole _ _

/-- The degree of a multi-code divisor is the number of codes. -/
@[simp] theorem deg_divisorOf
    (certificate : ExplicitPotential.Certificate m n p)
    (family : MultiCode m p d) (point : Fin m → ℤ) (core_nonempty : 0 < n)
    {degree : ℤ} (hValid : certificate.Valid degree)
    (hBounds : family.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) :
    deg (family.divisorOf certificate point core_nonempty hValid hBounds hCone) =
      (d : ℤ) := by
  unfold divisorOf
  rw [map_sum]
  simp

/-- A multi-code divisor is effective. -/
theorem effective_divisorOf
    (certificate : ExplicitPotential.Certificate m n p)
    (family : MultiCode m p d) (point : Fin m → ℤ) (core_nonempty : 0 < n)
    {degree : ℤ} (hValid : certificate.Valid degree)
    (hBounds : family.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) :
    effective (family.divisorOf certificate point core_nonempty hValid hBounds hCone) := by
  classical
  intro target
  rw [family.divisorOf_apply certificate point core_nonempty hValid hBounds hCone target]
  exact Int.natCast_nonneg _

/-- A multi-code divisor vanishes at every vertex named by no code. -/
theorem divisorOf_apply_eq_zero
    (certificate : ExplicitPotential.Certificate m n p)
    (family : MultiCode m p d) (point : Fin m → ℤ) (core_nonempty : 0 < n)
    {degree : ℤ} (hValid : certificate.Valid degree)
    (hBounds : family.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (target : (certificate.subdivisionSpec point core_nonempty hValid hCone).Vertex)
    (hMissing : ∀ index : Fin d,
      family.vertex certificate point core_nonempty hValid hBounds hCone index ≠ target) :
    family.divisorOf certificate point core_nonempty hValid hBounds hCone target = 0 := by
  classical
  rw [family.divisorOf_apply certificate point core_nonempty hValid hBounds hCone target]
  have hEmpty :
      (Finset.univ.filter fun index : Fin d =>
        family.vertex certificate point core_nonempty hValid hBounds hCone index =
          target) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro index _
    exact hMissing index
  rw [hEmpty]
  simp

/-- A multi-code divisor carries exactly one chip at a vertex named by a
single code. -/
theorem divisorOf_apply_eq_one
    (certificate : ExplicitPotential.Certificate m n p)
    (family : MultiCode m p d) (point : Fin m → ℤ) (core_nonempty : 0 < n)
    {degree : ℤ} (hValid : certificate.Valid degree)
    (hBounds : family.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (target : (certificate.subdivisionSpec point core_nonempty hValid hCone).Vertex)
    (witness : Fin d)
    (hWitness :
      family.vertex certificate point core_nonempty hValid hBounds hCone witness = target)
    (hUnique : ∀ index : Fin d,
      family.vertex certificate point core_nonempty hValid hBounds hCone index = target →
        index = witness) :
    family.divisorOf certificate point core_nonempty hValid hBounds hCone target = 1 := by
  classical
  rw [family.divisorOf_apply certificate point core_nonempty hValid hBounds hCone target]
  have hSingleton :
      (Finset.univ.filter fun index : Fin d =>
        family.vertex certificate point core_nonempty hValid hBounds hCone index =
          target) = {witness} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨by simpa using hWitness, ?_⟩
    intro index hIndex
    exact hUnique index (Finset.mem_filter.mp hIndex).2
  rw [hSingleton]
  simp

/-- A multi-code divisor which reaches every embedded core vertex has rank at
least one.  This is the unmarked end-to-end entry point for affine-positioned
pencils: `MultiBreakScript` supplies the individual `Reaches` witnesses, and
the public core-vertex strong-separator theorem supplies all remaining
subdivision vertices.  No stability hypothesis on the core is needed. -/
theorem bnExists_of_reaches_coreVertices
    (certificate : ExplicitPotential.Certificate m n p)
    (family : MultiCode m p d) (point : Fin m → ℤ) (core_nonempty : 0 < n)
    {degree : ℤ} (hValid : certificate.Valid degree)
    (hBounds : family.BoundsCertified certificate)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (hConnected : graphConnected
      (certificate.subdivisionSpec point core_nonempty hValid hCone).graph)
    (hReaches : ∀ vertex : Fin n,
      Certificate.StrongSeparator.Reaches
        (certificate.subdivisionSpec point core_nonempty hValid hCone).graph
        (family.divisorOf certificate point core_nonempty hValid hBounds hCone)
        ((certificate.subdivisionSpec point core_nonempty hValid hCone).coreVertex vertex)) :
    BNExists
      (certificate.subdivisionSpec point core_nonempty hValid hCone).graph
      1 (d : ℤ) := by
  apply Utilities.Certificate.CoreVertexReachability.bnExists_of_reaches_coreVertices
    (certificate.subdivisionSpec point core_nonempty hValid hCone) hConnected
    (family.divisorOf certificate point core_nonempty hValid hBounds hCone) (d : ℤ)
  · exact family.deg_divisorOf certificate point core_nonempty hValid hBounds hCone
  · exact hReaches

end MultiCode

end AffinePosition

/-! ## Break lists and their piecewise-constant slopes -/

end MarkedGraphs.Certificate

namespace Utilities.Certificate.SubdivisionGraph.Spec
open MarkedGraphs
open MarkedGraphs.Certificate

open Utilities.Certificate
open Utilities
open Finset
open ExplicitPotential
open SubdivisionGraph
variable {m n p : ℕ}
variable {m n p : ℕ}
variable {m n p d : ℕ}
open Utilities.Certificate.SubdivisionGraph.Spec

/-- Scan a break list left to right, keeping the value of the last entry
whose start index is at most `k`.  `initial` is the slope in force before the
list begins. -/
def breakSlopeFrom (initial : ℤ) : List (ℕ × ℤ) → ℕ → ℤ
  | [], _ => initial
  | entry :: rest, k =>
      breakSlopeFrom (if entry.1 ≤ k then entry.2 else initial) rest k

/-- The slope named by a break list at unit step `k`: the value of the last
entry whose start is at most `k`, and `0` before every entry. -/
def breakSlope (breaks : List (ℕ × ℤ)) (k : ℕ) : ℤ := breakSlopeFrom 0 breaks k

@[simp] theorem breakSlopeFrom_nil (initial : ℤ) (k : ℕ) :
    breakSlopeFrom initial [] k = initial := rfl

@[simp] theorem breakSlopeFrom_cons (initial : ℤ) (entry : ℕ × ℤ)
    (rest : List (ℕ × ℤ)) (k : ℕ) :
    breakSlopeFrom initial (entry :: rest) k =
      breakSlopeFrom (if entry.1 ≤ k then entry.2 else initial) rest k := rfl

@[simp] theorem breakSlope_nil (k : ℕ) : breakSlope [] k = 0 := rfl

/-- Two step indices separated by no break start receive the same slope. -/
theorem breakSlopeFrom_congr (breaks : List (ℕ × ℤ)) {k l : ℕ}
    (hSame : ∀ entry ∈ breaks, (entry.1 ≤ k ↔ entry.1 ≤ l)) (initial : ℤ) :
    breakSlopeFrom initial breaks k = breakSlopeFrom initial breaks l := by
  induction breaks generalizing initial with
  | nil => rfl
  | cons entry rest ih =>
      have hHead := hSame entry (by simp)
      have hIf :
          (if entry.1 ≤ k then entry.2 else initial) =
            (if entry.1 ≤ l then entry.2 else initial) := by
        by_cases hk : entry.1 ≤ k
        · rw [ite_eq_left hk, ite_eq_left (hHead.mp hk)]
        · rw [ite_eq_right hk, ite_eq_right fun hl => hk (hHead.mpr hl)]
      rw [breakSlopeFrom_cons, breakSlopeFrom_cons, hIf]
      exact ih (fun e he => hSame e (List.mem_cons_of_mem _ he)) _

/-- The slope is unchanged across a step which is not a break start. -/
theorem breakSlope_succ_of_notMem (breaks : List (ℕ × ℤ)) (k : ℕ)
    (hNoBreak : ∀ entry ∈ breaks, entry.1 ≠ k + 1) :
    breakSlope breaks (k + 1) = breakSlope breaks k := by
  apply breakSlopeFrom_congr
  intro entry hEntry
  have := hNoBreak entry hEntry
  constructor <;> omega

variable {n p : ℕ} (spec : SubdivisionGraph.Spec n p)

/-- Path values of a multi-break script: the core potential at the tail plus
the accumulated break slopes. -/
def breakValue (potential : Fin n → ℤ) (breaks : Fin p → List (ℕ × ℤ)) :
    Fin p → ℕ → ℤ :=
  fun edge k =>
    potential (spec.core.tail edge) +
      ∑ j ∈ Finset.range k, breakSlope (breaks edge) j

/-- The multi-break firing script. -/
def breakScript (potential : Fin n → ℤ) (breaks : Fin p → List (ℕ × ℤ)) :
    firingScript spec.graph :=
  spec.slotValueScript potential (spec.breakValue potential breaks)

/-- The single closing condition on multi-break data: on every slot the total
accumulated rise is the core potential difference. -/
structure BreakData (potential : Fin n → ℤ) (breaks : Fin p → List (ℕ × ℤ)) :
    Prop where
  balance : ∀ edge : Fin p,
    potential (spec.core.head edge) =
      potential (spec.core.tail edge) +
        ∑ j ∈ Finset.range (spec.length edge), breakSlope (breaks edge) j

variable {spec}
variable {potential : Fin n → ℤ} {breaks : Fin p → List (ℕ × ℤ)}

@[simp] theorem breakValue_zero (edge : Fin p) :
    spec.breakValue potential breaks edge 0 = potential (spec.core.tail edge) := by
  simp [breakValue]

theorem slotValueCompatible_breakValue (hData : spec.BreakData potential breaks) :
    spec.SlotValueCompatible potential (spec.breakValue potential breaks) where
  tail := fun edge => by simp
  head := fun edge => (hData.balance edge).symm

/-- The unit-step slopes of a multi-break script are exactly its break
list slopes. -/
theorem isStepSlope_breakScript (hData : spec.BreakData potential breaks) :
    spec.IsStepSlope (spec.breakScript potential breaks)
      fun edge k => breakSlope (breaks edge) k := by
  intro edge offset
  have hStep :=
    spec.isStepSlope_slotValueScript (slotValueCompatible_breakValue hData) edge offset
  have hValue :
      spec.breakValue potential breaks edge (offset.val + 1) -
          spec.breakValue potential breaks edge offset.val =
        breakSlope (breaks edge) offset.val := by
    simp [breakValue, Finset.sum_range_succ]
  exact (hStep.trans hValue)

/-- At a core vertex the Laplacian of a multi-break script is the sum of the
outgoing break slopes at each incident endpoint. -/
theorem prin_breakScript_coreVertex (hData : spec.BreakData potential breaks)
    (vertex : Fin n) :
    prin spec.graph (spec.breakScript potential breaks) (spec.coreVertex vertex) =
      ∑ edge : Fin p,
        ((if spec.core.tail edge = vertex then breakSlope (breaks edge) 0 else 0) +
          (if spec.core.head edge = vertex then
            -breakSlope (breaks edge) (spec.length edge - 1) else 0)) :=
  spec.prin_coreVertex_eq_endpointSum (isStepSlope_breakScript hData) vertex

/-- At an interior vertex the Laplacian of a multi-break script is the jump of
its break list at that coordinate. -/
theorem prin_breakScript_interiorVertex (hData : spec.BreakData potential breaks)
    (edge : Fin p) (offset : Fin (spec.length edge - 1)) :
    prin spec.graph (spec.breakScript potential breaks)
        (spec.interiorVertex edge offset) =
      breakSlope (breaks edge) (offset.val + 1) - breakSlope (breaks edge) offset.val :=
  spec.prin_interiorVertex_eq_slopeDifference (isStepSlope_breakScript hData) edge offset

/-- A multi-break script has trivial Laplacian at every interior vertex which
is not a break position.  This is the reason for the format: the principal
divisor of a multi-break script is supported on the core together with the
finitely many named break points. -/
theorem prin_breakScript_interiorVertex_eq_zero
    (hData : spec.BreakData potential breaks) (edge : Fin p)
    (offset : Fin (spec.length edge - 1))
    (hNoBreak : ∀ entry ∈ breaks edge, entry.1 ≠ offset.val + 1) :
    prin spec.graph (spec.breakScript potential breaks)
        (spec.interiorVertex edge offset) = 0 := by
  rw [prin_breakScript_interiorVertex hData edge offset,
    breakSlope_succ_of_notMem (breaks edge) offset.val hNoBreak]
  ring

end Utilities.Certificate.SubdivisionGraph.Spec

namespace MarkedGraphs.Certificate
open Utilities.Certificate
open Utilities
open Finset
open ExplicitPotential
open SubdivisionGraph

/-! ## Affine-positioned multi-break scripts -/

namespace AffinePosition

/-- One affine-positioned break: a position code together with the slope in
force from that position onwards along its slot. -/
structure BreakPoint (m p : ℕ) where
  /-- The affine-coded position at which this change of slope starts. -/
  position : Code m p
  /-- The integer slope prescribed from this break onward along its slot. -/
  slope : ℤ

/-- A passive multi-break script: an ordered family of affine-positioned
breaks.  Order matters, exactly as in a break list: a later entry on the same
slot overrides an earlier one from its start index onwards. -/
structure SlopeScript (m p b : ℕ) where
  /-- The ordered break entries; a later entry on the same slot overrides an earlier one from
  its starting position onward. -/
  entry : Fin b → BreakPoint m p

namespace SlopeScript

variable {m n p b : ℕ}

/-- Every break position of the script has its bound rows in the local cone. -/
def BoundsCertified (certificate : ExplicitPotential.Certificate m n p)
    (script : SlopeScript m p b) : Prop :=
  ∀ index : Fin b, (script.entry index).position.BoundsCertified certificate

/-- Fail-closed executable bounds check for a multi-break script. -/
def checkBounds (certificate : ExplicitPotential.Certificate m n p)
    (script : SlopeScript m p b) : Bool :=
  ExplicitPotential.allFin fun index =>
    (script.entry index).position.checkBounds certificate

@[simp] theorem checkBounds_eq_true_iff
    (certificate : ExplicitPotential.Certificate m n p)
    (script : SlopeScript m p b) :
    script.checkBounds certificate = true ↔ script.BoundsCertified certificate := by
  simp [checkBounds, BoundsCertified]

/-- The concrete per-slot break list obtained by evaluating every affine
break position at a length point. -/
def breaks (certificate : ExplicitPotential.Certificate m n p)
    (script : SlopeScript m p b) (point : Fin m → ℤ) (edge : Fin p) :
    List (ℕ × ℤ) :=
  (List.ofFn script.entry).filterMap fun item =>
    if item.position.edge = edge then
      some (item.position.coordinate certificate point, item.slope)
    else none

/-- Every entry of a decoded break list comes from a named break of the
script, on the named slot and at its decoded coordinate. -/
theorem exists_of_mem_breaks
    (certificate : ExplicitPotential.Certificate m n p)
    (script : SlopeScript m p b) (point : Fin m → ℤ) (edge : Fin p)
    {pair : ℕ × ℤ} (hMem : pair ∈ script.breaks certificate point edge) :
    ∃ index : Fin b,
      (script.entry index).position.edge = edge ∧
        pair.1 = (script.entry index).position.coordinate certificate point := by
  classical
  rw [breaks, List.mem_filterMap] at hMem
  obtain ⟨item, hItem, hSome⟩ := hMem
  obtain ⟨index, hIndex⟩ := List.mem_ofFn.mp hItem
  by_cases hEdge : item.position.edge = edge
  · rw [ite_eq_left hEdge] at hSome
    refine ⟨index, ?_, ?_⟩
    · rw [hIndex]; exact hEdge
    · rw [hIndex, ← Option.some_inj.mp hSome]
  · rw [ite_eq_right hEdge] at hSome
    exact absurd hSome (by simp)

/-- If no break of the script sits on `edge` at coordinate `coordinate`, then
the decoded break list has no entry starting there. -/
theorem notMem_start_of_no_break
    (certificate : ExplicitPotential.Certificate m n p)
    (script : SlopeScript m p b) (point : Fin m → ℤ) (edge : Fin p)
    (coordinate : ℕ)
    (hAvoid : ∀ index : Fin b,
      (script.entry index).position.edge = edge →
        (script.entry index).position.coordinate certificate point ≠ coordinate) :
    ∀ pair ∈ script.breaks certificate point edge, pair.1 ≠ coordinate := by
  intro pair hPair
  obtain ⟨index, hEdge, hCoordinate⟩ :=
    script.exists_of_mem_breaks certificate point edge hPair
  rw [hCoordinate]
  exact hAvoid index hEdge

/-- The multi-break firing script on the concrete subdivision named by a
length point. -/
def firingScript (certificate : ExplicitPotential.Certificate m n p)
    (script : SlopeScript m p b) (potential : Fin n → ℤ) (point : Fin m → ℤ)
    (core_nonempty : 0 < n) {degree : ℤ} (hValid : certificate.Valid degree)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) :
    firingScript
      (certificate.subdivisionSpec point core_nonempty hValid hCone).graph :=
  (certificate.subdivisionSpec point core_nonempty hValid hCone).breakScript
    potential (script.breaks certificate point)

/-- The closing condition for a multi-break script at one length point. -/
def Balanced (certificate : ExplicitPotential.Certificate m n p)
    (script : SlopeScript m p b) (potential : Fin n → ℤ) (point : Fin m → ℤ)
    (core_nonempty : 0 < n) {degree : ℤ} (hValid : certificate.Valid degree)
    (hCone : ExplicitPotential.FormsHold certificate.cone point) : Prop :=
  (certificate.subdivisionSpec point core_nonempty hValid hCone).BreakData
    potential (script.breaks certificate point)

/-- The Laplacian of an affine-positioned multi-break script at an interior
vertex is the jump of the decoded break list there. -/
theorem prin_firingScript_interiorVertex
    (certificate : ExplicitPotential.Certificate m n p)
    (script : SlopeScript m p b) (potential : Fin n → ℤ) (point : Fin m → ℤ)
    (core_nonempty : 0 < n) {degree : ℤ} (hValid : certificate.Valid degree)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (hBalanced : script.Balanced certificate potential point core_nonempty hValid hCone)
    (edge : Fin p)
    (offset : Fin ((certificate.subdivisionSpec point core_nonempty hValid hCone).length
      edge - 1)) :
    prin (certificate.subdivisionSpec point core_nonempty hValid hCone).graph
        (script.firingScript certificate potential point core_nonempty hValid hCone)
        ((certificate.subdivisionSpec point core_nonempty hValid hCone).interiorVertex
          edge offset) =
      SubdivisionGraph.Spec.breakSlope (script.breaks certificate point edge)
          (offset.val + 1) -
        SubdivisionGraph.Spec.breakSlope (script.breaks certificate point edge)
          offset.val :=
  SubdivisionGraph.Spec.prin_breakScript_interiorVertex hBalanced edge offset

/-- The principal divisor of an affine-positioned multi-break script vanishes
at every interior vertex which no break of the script names.  Together with
`MultiCode.divisorOf_apply_eq_zero` this is the row-independent statement that
lets a residual be checked at the finitely many named positions only. -/
theorem prin_firingScript_interiorVertex_eq_zero
    (certificate : ExplicitPotential.Certificate m n p)
    (script : SlopeScript m p b) (potential : Fin n → ℤ) (point : Fin m → ℤ)
    (core_nonempty : 0 < n) {degree : ℤ} (hValid : certificate.Valid degree)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (hBalanced : script.Balanced certificate potential point core_nonempty hValid hCone)
    (edge : Fin p)
    (offset : Fin ((certificate.subdivisionSpec point core_nonempty hValid hCone).length
      edge - 1))
    (hAvoid : ∀ index : Fin b,
      (script.entry index).position.edge = edge →
        (script.entry index).position.coordinate certificate point ≠ offset.val + 1) :
    prin (certificate.subdivisionSpec point core_nonempty hValid hCone).graph
        (script.firingScript certificate potential point core_nonempty hValid hCone)
        ((certificate.subdivisionSpec point core_nonempty hValid hCone).interiorVertex
          edge offset) = 0 :=
  SubdivisionGraph.Spec.prin_breakScript_interiorVertex_eq_zero hBalanced edge offset
    (script.notMem_start_of_no_break certificate point edge (offset.val + 1) hAvoid)

/-- The Laplacian of an affine-positioned multi-break script at a core vertex
is the usual endpoint-slope sum. -/
theorem prin_firingScript_coreVertex
    (certificate : ExplicitPotential.Certificate m n p)
    (script : SlopeScript m p b) (potential : Fin n → ℤ) (point : Fin m → ℤ)
    (core_nonempty : 0 < n) {degree : ℤ} (hValid : certificate.Valid degree)
    (hCone : ExplicitPotential.FormsHold certificate.cone point)
    (hBalanced : script.Balanced certificate potential point core_nonempty hValid hCone)
    (vertex : Fin n) :
    prin (certificate.subdivisionSpec point core_nonempty hValid hCone).graph
        (script.firingScript certificate potential point core_nonempty hValid hCone)
        ((certificate.subdivisionSpec point core_nonempty hValid hCone).coreVertex
          vertex) =
      ∑ edge : Fin p,
        ((if certificate.core.tail edge = vertex then
            SubdivisionGraph.Spec.breakSlope (script.breaks certificate point edge) 0
          else 0) +
          (if certificate.core.head edge = vertex then
            -SubdivisionGraph.Spec.breakSlope (script.breaks certificate point edge)
              (certificate.segmentNat point edge - 1)
          else 0)) :=
  SubdivisionGraph.Spec.prin_breakScript_coreVertex hBalanced vertex

end SlopeScript

end AffinePosition

end MarkedGraphs.Certificate
