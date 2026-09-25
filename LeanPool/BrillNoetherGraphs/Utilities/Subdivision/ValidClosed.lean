/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ExplicitPotentialRankOne
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DegenerateSpec

/-!
# `ValidClosed`: the affine certificate grammar on the CLOSED length orthant

`ExplicitPotential.Certificate.Valid` has six conjuncts.  Five of them are
already boundary-compatible; exactly one is not:

```
(∀ edge : Fin p,
  AffineForm.positive (certificate.segment edge) = 0 ∨
    AffineForm.positive (certificate.segment edge) ∈ certificate.cone)
```

`AffineForm.positive f` is the row `f − 1 ≥ 0`, so this conjunct says
`ℓ_e ≥ 1` and it excludes every face of the orthant by construction.  This
file relaxes exactly that row and nothing else.

## Nothing existing is modified or weakened

`Valid` is untouched, and `ValidClosed` is a strict *weakening* of it:

* `valid_toValidClosed : c.Valid degree → c.ValidClosed degree`, and
* `valid_of_validClosed`, the converse under the strict rows — so on the
  interior chamber, where the certificate does carry `ℓ_e ≥ 1`, `ValidClosed`
  *is* `Valid`, with the identical five other conjuncts.

Every existing certificate therefore satisfies `ValidClosed` for free, and no
consumer of `Valid` sees a different statement.

## What the relaxed grammar still buys, and the structural surprise

At a cone point `ValidClosed` gives `0 ≤ (segment e).eval point` instead of
`0 < …`.  Everything downstream that only needed non-negativity survives
verbatim (`segmentNat_cast_eq_of_validClosed`, `rise_bounds_of_validClosed`).
Everything that genuinely needed a unit step — `interpolated_endpoint_bounds`
— is recovered from the extra hypothesis `0 < segmentNat`, which on the
degenerate graph is exactly the statement that the slot carries a unit step.

The structural surprise, and the reason this relaxation is cheap, is
`rise_eq_zero_of_segment_eval_zero`: the `lowerForm`/`upperForm` rows, which
`Valid` and `ValidClosed` share unchanged, read `α_e·ℓ_e ≤ rise ≤ −β_e·ℓ_e`,
so at `ℓ_e = 0` they *force* `rise = 0`.  In other words the anchor potential
is automatically constant across every collapsed slot — the `rep`-invariance a
`DegSpec` script needs is already implied by the existing cone rows, not an
extra obligation.  `potential_eq_of_segment_eval_zero` states it in that form.

`zeroSlotContribution_nonpos` records the matching fact for the endpoint
bookkeeping: a collapsed slot contributes `α_e + β_e ≤ 0` to
`lowerEndpointContribution` at the merged class and `0` to the actual
Laplacian, so the conservative bound is still conservative.  That inequality
is `Valid`'s third conjunct, unchanged.
-/

@[expose] public section

-- `Certificate` is a structure inside a namespace already ending in `Certificate`;
-- renaming either would ripple through every consumer.  Lean v4.33 added
-- `linter.dupNamespace`, which flags exactly this shape.
namespace Utilities.Certificate
open Utilities.Certificate

open Utilities

open ExplicitPotential

end Utilities.Certificate

namespace Utilities.Certificate.ExplicitPotential.Certificate
open Utilities
open Utilities.Certificate

open Utilities.Certificate
open Utilities
open ExplicitPotential
open Utilities.Certificate.ExplicitPotential
open Utilities.Certificate.ExplicitPotential.Certificate

variable {m n p : ℕ}

/-! ## The relaxed segment row -/

/-- The closed-orthant segment row.  The first two disjuncts are exactly
`Valid`'s row (`ℓ_e ≥ 1`); the last two are the relaxation (`ℓ_e ≥ 0`).
Any one of the four delivers `0 ≤ (segment e).eval point` at a cone point. -/
def SegmentRowClosed (certificate : Certificate m n p) (edge : Fin p) : Prop :=
  AffineForm.positive (certificate.segment edge) = 0 ∨
    AffineForm.positive (certificate.segment edge) ∈ certificate.cone ∨
    certificate.segment edge = 0 ∨
    certificate.segment edge ∈ certificate.cone

/-- Point-independent validity on the **closed** length orthant.  Identical to
`Valid` except that the segment row is `SegmentRowClosed`. -/
def ValidClosed (certificate : Certificate m n p) (degree : ℤ) : Prop :=
  (∀ edge : Fin p, certificate.core.tail edge ≠ certificate.core.head edge) ∧
  (∑ vertex : Fin n, certificate.divisor vertex) = degree ∧
  (∀ anchor : Fin n, ∀ edge : Fin p,
    (certificate.witness anchor).alpha edge +
      (certificate.witness anchor).beta edge ≤ 0) ∧
  (∀ anchor vertex : Fin n,
    0 ≤ certificate.targetCoefficient anchor vertex +
      certificate.lowerEndpointContribution anchor vertex) ∧
  (∀ edge : Fin p, certificate.SegmentRowClosed edge) ∧
  (∀ anchor : Fin n, ∀ edge : Fin p,
    (certificate.lowerForm anchor edge = 0 ∨
      certificate.lowerForm anchor edge ∈ certificate.cone) ∧
    (certificate.upperForm anchor edge = 0 ∨
      certificate.upperForm anchor edge ∈ certificate.cone))

/-! ## `ValidClosed` is a weakening of `Valid`, and equals it on the interior -/

/-- Every certificate that is `Valid` is `ValidClosed`.  Nothing already proved
is weakened by moving a consumer to the closed grammar. -/
theorem valid_toValidClosed {certificate : Certificate m n p} {degree : ℤ}
    (hValid : certificate.Valid degree) : certificate.ValidClosed degree :=
  ⟨hValid.1, hValid.2.1, hValid.2.2.1, hValid.2.2.2.1,
    fun edge => (hValid.2.2.2.2.1 edge).imp id Or.inl,
    hValid.2.2.2.2.2⟩

/-- **On the interior, `ValidClosed` is `Valid`.**  The two differ only in the
segment row, so supplying the strict rows recovers `Valid` outright. -/
theorem valid_of_validClosed {certificate : Certificate m n p} {degree : ℤ}
    (hClosed : certificate.ValidClosed degree)
    (hStrict : ∀ edge : Fin p,
      AffineForm.positive (certificate.segment edge) = 0 ∨
        AffineForm.positive (certificate.segment edge) ∈ certificate.cone) :
    certificate.Valid degree :=
  ⟨hClosed.1, hClosed.2.1, hClosed.2.2.1, hClosed.2.2.2.1, hStrict,
    hClosed.2.2.2.2.2⟩

/-- The two grammars agree exactly on the interior chamber. -/
theorem validClosed_iff_valid_of_strict {certificate : Certificate m n p}
    {degree : ℤ}
    (hStrict : ∀ edge : Fin p,
      AffineForm.positive (certificate.segment edge) = 0 ∨
        AffineForm.positive (certificate.segment edge) ∈ certificate.cone) :
    certificate.ValidClosed degree ↔ certificate.Valid degree :=
  ⟨fun h => valid_of_validClosed h hStrict, valid_toValidClosed⟩

/-! ## Executable checker -/

/-- Proof-free check of the relaxed segment row. -/
def checkSegmentRowClosed (certificate : Certificate m n p) (edge : Fin p) :
    Bool :=
  AffineCover.AffineForm.equal
      (AffineForm.positive (certificate.segment edge)) 0 ||
    AffineCover.AffineForm.mem
      (AffineForm.positive (certificate.segment edge)) certificate.cone ||
    AffineCover.AffineForm.equal (certificate.segment edge) 0 ||
    AffineCover.AffineForm.mem (certificate.segment edge) certificate.cone

@[simp] theorem checkSegmentRowClosed_eq_true_iff
    (certificate : Certificate m n p) (edge : Fin p) :
    certificate.checkSegmentRowClosed edge = true ↔
      certificate.SegmentRowClosed edge := by
  simp [checkSegmentRowClosed, SegmentRowClosed, or_assoc]

/-- Executable closed-orthant validity checker. -/
def checkClosed (certificate : Certificate m n p) (degree : ℤ) : Bool :=
  (allFin fun edge : Fin p =>
    decide (certificate.core.tail edge ≠ certificate.core.head edge)) &&
  decide ((∑ vertex : Fin n, certificate.divisor vertex) = degree) &&
  (allFin fun anchor : Fin n =>
    allFin fun edge : Fin p =>
      decide ((certificate.witness anchor).alpha edge +
        (certificate.witness anchor).beta edge ≤ 0)) &&
  (allFin fun anchor : Fin n =>
    allFin fun vertex : Fin n =>
      decide (0 ≤ certificate.targetCoefficient anchor vertex +
        certificate.lowerEndpointContribution anchor vertex)) &&
  (allFin fun edge : Fin p => certificate.checkSegmentRowClosed edge) &&
  (allFin fun anchor : Fin n =>
    allFin fun edge : Fin p =>
      (AffineCover.AffineForm.equal (certificate.lowerForm anchor edge) 0 ||
        AffineCover.AffineForm.mem (certificate.lowerForm anchor edge)
          certificate.cone) &&
      (AffineCover.AffineForm.equal (certificate.upperForm anchor edge) 0 ||
        AffineCover.AffineForm.mem (certificate.upperForm anchor edge)
          certificate.cone))

@[simp] theorem checkClosed_eq_true_iff (certificate : Certificate m n p)
    (degree : ℤ) :
    certificate.checkClosed degree = true ↔ certificate.ValidClosed degree := by
  simp [checkClosed, ValidClosed, and_assoc]

/-! ## Point-level consequences -/

private theorem holds_of_zero_or_mem_closed
    (certificate : Certificate m n p) (point : Fin m → ℤ)
    (form : AffineForm m)
    (hForm : form = 0 ∨ form ∈ certificate.cone)
    (hCone : FormsHold certificate.cone point) :
    form.Holds point := by
  rcases hForm with rfl | hMember
  · simp [AffineCover.AffineForm.Holds]
  · exact hCone form hMember

/-- On the closed orthant every segment has **non-negative** integral length at
a cone point.  This is the exact replacement for
`segment_positive_of_valid`. -/
theorem segment_nonneg_of_validClosed
    (certificate : Certificate m n p) {degree : ℤ}
    (hValid : certificate.ValidClosed degree) (point : Fin m → ℤ)
    (hCone : FormsHold certificate.cone point) (edge : Fin p) :
    0 ≤ (certificate.segment edge).eval point := by
  rcases hValid.2.2.2.2.1 edge with h | h | h | h
  · have := holds_of_zero_or_mem_closed certificate point
      (AffineForm.positive (certificate.segment edge)) (Or.inl h) hCone
    simp only [AffineCover.AffineForm.Holds, AffineForm.eval_positive] at this
    omega
  · have := holds_of_zero_or_mem_closed certificate point
      (AffineForm.positive (certificate.segment edge)) (Or.inr h) hCone
    simp only [AffineCover.AffineForm.Holds, AffineForm.eval_positive] at this
    omega
  · have := holds_of_zero_or_mem_closed certificate point
      (certificate.segment edge) (Or.inl h) hCone
    simpa [AffineCover.AffineForm.Holds] using this
  · have := holds_of_zero_or_mem_closed certificate point
      (certificate.segment edge) (Or.inr h) hCone
    simpa [AffineCover.AffineForm.Holds] using this

theorem segmentNat_cast_eq_of_validClosed
    (certificate : Certificate m n p) {degree : ℤ}
    (hValid : certificate.ValidClosed degree) (point : Fin m → ℤ)
    (hCone : FormsHold certificate.cone point) (edge : Fin p) :
    (certificate.segmentNat point edge : ℤ) =
      (certificate.segment edge).eval point :=
  Int.toNat_of_nonneg
    (certificate.segment_nonneg_of_validClosed hValid point hCone edge)

/-- The endpoint-rise bounds need no positivity at all: the `lowerForm` and
`upperForm` rows are shared verbatim with `Valid`. -/
theorem rise_bounds_of_validClosed
    (certificate : Certificate m n p) {degree : ℤ}
    (hValid : certificate.ValidClosed degree) (point : Fin m → ℤ)
    (hCone : FormsHold certificate.cone point)
    (anchor : Fin n) (edge : Fin p) :
    (certificate.witness anchor).alpha edge *
        (certificate.segment edge).eval point ≤
      certificate.riseValue anchor point edge ∧
    certificate.riseValue anchor point edge ≤
      -((certificate.witness anchor).beta edge) *
        (certificate.segment edge).eval point := by
  have hRequired := hValid.2.2.2.2.2 anchor edge
  have hLower := holds_of_zero_or_mem_closed certificate point
    (certificate.lowerForm anchor edge) hRequired.1 hCone
  have hUpper := holds_of_zero_or_mem_closed certificate point
    (certificate.upperForm anchor edge) hRequired.2 hCone
  simp only [AffineCover.AffineForm.Holds, lowerForm, upperForm,
    AffineForm.eval_sub, AffineForm.eval_scale] at hLower hUpper
  unfold riseValue
  constructor <;> omega

/-! ## The structural boundary-compatibility of the existing cone rows -/

/-- **The surprise.**  At a face the shared `lowerForm`/`upperForm` rows pin
the rise to zero: they read `α_e·ℓ_e ≤ rise ≤ −β_e·ℓ_e`, and both bounds
collapse when `ℓ_e = 0`. -/
theorem rise_eq_zero_of_segment_eval_zero
    (certificate : Certificate m n p) {degree : ℤ}
    (hValid : certificate.ValidClosed degree) (point : Fin m → ℤ)
    (hCone : FormsHold certificate.cone point)
    (anchor : Fin n) (edge : Fin p)
    (hZero : (certificate.segment edge).eval point = 0) :
    certificate.riseValue anchor point edge = 0 := by
  have hBounds :=
    certificate.rise_bounds_of_validClosed hValid point hCone anchor edge
  rw [hZero] at hBounds
  omega

/-- Restated as the `rep`-invariance a degenerate script needs: the anchor
potential takes the same value at the two ends of a collapsed slot.  No extra
certificate field is required for this — it is already implied. -/
theorem potential_eq_of_segment_eval_zero
    (certificate : Certificate m n p) {degree : ℤ}
    (hValid : certificate.ValidClosed degree) (point : Fin m → ℤ)
    (hCone : FormsHold certificate.cone point)
    (anchor : Fin n) (edge : Fin p)
    (hZero : (certificate.segment edge).eval point = 0) :
    ((certificate.witness anchor).potential
        (certificate.core.head edge)).eval point =
      ((certificate.witness anchor).potential
        (certificate.core.tail edge)).eval point := by
  have h := certificate.rise_eq_zero_of_segment_eval_zero hValid point hCone
    anchor edge hZero
  unfold riseValue rise at h
  rw [AffineForm.eval_sub] at h
  omega

/-- A collapsed slot contributes at most zero to the conservative endpoint
bookkeeping at the merged class, while contributing exactly zero to the
Laplacian.  The inequality is `Valid`'s third conjunct, unchanged. -/
theorem zeroSlotContribution_nonpos
    (certificate : Certificate m n p) {degree : ℤ}
    (hValid : certificate.ValidClosed degree) (anchor : Fin n) (edge : Fin p) :
    (certificate.witness anchor).alpha edge +
      (certificate.witness anchor).beta edge ≤ 0 :=
  hValid.2.2.1 anchor edge

/-! ## Recovering the strictly positive conclusions slot by slot -/

theorem segmentNat_positive_of_eval_pos
    (certificate : Certificate m n p) {degree : ℤ}
    (hValid : certificate.ValidClosed degree) (point : Fin m → ℤ)
    (hCone : FormsHold certificate.cone point) (edge : Fin p)
    (hPos : 0 < (certificate.segment edge).eval point) :
    0 < certificate.segmentNat point edge := by
  have hCast :=
    certificate.segmentNat_cast_eq_of_validClosed hValid point hCone edge
  omega

/-- `interpolated_endpoint_bounds` needs a unit step, and on the closed orthant
that is precisely `0 < segmentNat`.  Otherwise the statement is unchanged. -/
theorem interpolated_endpoint_bounds_of_validClosed
    (certificate : Certificate m n p) {degree : ℤ}
    (hValid : certificate.ValidClosed degree) (point : Fin m → ℤ)
    (hCone : FormsHold certificate.cone point)
    (anchor : Fin n) (edge : Fin p)
    (hPos : 0 < certificate.segmentNat point edge) :
    (certificate.witness anchor).alpha edge ≤
      SubdivisionArithmetic.step
        (certificate.segmentNat point edge)
        (certificate.riseValue anchor point edge) 0 ∧
    (certificate.witness anchor).beta edge ≤
      -SubdivisionArithmetic.step
        (certificate.segmentNat point edge)
        (certificate.riseValue anchor point edge)
        (certificate.segmentNat point edge - 1) := by
  have hBounds :=
    certificate.rise_bounds_of_validClosed hValid point hCone anchor edge
  have hCast :=
    certificate.segmentNat_cast_eq_of_validClosed hValid point hCone edge
  apply SubdivisionArithmetic.endpointSlopeBounds (hL := hPos)
  · simpa only [hCast] using hBounds.1
  · simpa only [hCast] using hBounds.2

/-! ## The degenerate spec cut out by a closed certificate at a point

The direct analogue of `Certificate.subdivisionSpec`.  The contraction datum
`rep` is *not* determined by the certificate — it names which face is meant —
so it is supplied, exactly as in `Utilities.Certificate.DegenerateSpec.DegSpec`.  Note that
`core_loopless` becomes `rep_loopless`, and that `rep_zero` is the only new
obligation beyond the census data. -/
/-- Turn evaluated affine segment lengths and a checked idempotent contraction representative
into a degenerate subdivision specification, retaining the supplied looplessness and
forest-count guarantees. -/
def degenerateSpec (certificate : Certificate m n p)
    (point : Fin m → ℤ) (core_nonempty : 0 < n)
    (rep : Fin n → Fin n)
    (rep_idem : ∀ v : Fin n, rep (rep v) = rep v)
    (rep_zero : ∀ edge : Fin p, certificate.segmentNat point edge = 0 →
      rep (certificate.core.tail edge) = rep (certificate.core.head edge))
    (rep_loopless : ∀ edge : Fin p, 0 < certificate.segmentNat point edge →
      rep (certificate.core.tail edge) ≠ rep (certificate.core.head edge))
    (forest : (Finset.univ.image rep).card
      + (Finset.univ.filter
          (fun edge : Fin p => certificate.segmentNat point edge = 0)).card = n) :
    Utilities.Certificate.DegenerateSpec.DegSpec n p where
  core := certificate.core
  length := certificate.segmentNat point
  core_nonempty := core_nonempty
  rep := rep
  rep_idem := rep_idem
  rep_zero := rep_zero
  rep_loopless := rep_loopless
  forest := forest

@[simp] theorem degenerateSpec_length (certificate : Certificate m n p)
    (point : Fin m → ℤ) (core_nonempty : 0 < n) (rep : Fin n → Fin n)
    (rep_idem rep_zero rep_loopless forest) :
    (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
      rep_loopless forest).length = certificate.segmentNat point := rfl

/-- Genus of the face cut out by a closed certificate: unchanged from the
core's `p − n + 1`, by `DegSpec.genus_graph`. -/
theorem genus_degenerateSpec (certificate : Certificate m n p)
    (point : Fin m → ℤ) (core_nonempty : 0 < n) (rep : Fin n → Fin n)
    (rep_idem rep_zero rep_loopless forest) :
    genus (certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
        rep_loopless forest).graph = (p : ℤ) - (n : ℤ) + 1 :=
  Utilities.Certificate.DegenerateSpec.DegSpec.genus_graph _

/-- At a strictly positive point the degenerate spec is the ordinary
`subdivisionSpec`: same core, same lengths, and `rep = id`. -/
theorem degenerateSpec_toSpec_length (certificate : Certificate m n p)
    (point : Fin m → ℤ) (core_nonempty : 0 < n) (rep : Fin n → Fin n)
    (rep_idem rep_zero rep_loopless forest)
    (hpos : ∀ edge : Fin p, 0 < certificate.segmentNat point edge) :
    ((certificate.degenerateSpec point core_nonempty rep rep_idem rep_zero
        rep_loopless forest).toSpec hpos).length =
      certificate.segmentNat point := rfl

end Utilities.Certificate.ExplicitPotential.Certificate

namespace Utilities.Certificate
open Utilities.Certificate
open Utilities
open ExplicitPotential

end Utilities.Certificate
