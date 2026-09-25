/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedRowProof.RichLeafSound

/-!
# Raw rich-chip divisors on closed faces

The RPF representation stores chips as raw `(slot, affine form, coefficient)`
triples.  A rich-leaf soundness proof evaluates the forms and supplies a
closed-face vertex decoder (with the C first-match convention).  This module
is deliberately agnostic about that decoder: it packages the resulting chip
divisor and its degree calculation once, so the endpoint-specific decoder is
the only remaining W5 geometry.
-/

@[expose] public section

namespace Utilities.Subdivision.ClosedRowProof

open Utilities

open MarkedGraphs.Certificate
open Utilities.Certificate

namespace RichWitness

variable {n p : ℕ}

/-- Raw signed chip mass at a literal coordinate of one displayed slot.
Unlike a quotient-core vertex, this remains meaningful before any zero-length
core edges are contracted.  The W5 endpoint bridge identifies this mass with
the C first-match prefix/suffix accounting on collapsed endpoint runs. -/
def rawChipMassAt (w : RichWitness) (x : List ℤ) (slot : ℕ) (coordinate : ℤ) : ℤ :=
  (w.chips.map fun chip =>
    if chip.1 == slot && eval chip.2.1 x == coordinate then chip.2.2 else 0).sum

/-! ## Evaluated physical chip positions

Raw RPF forms denote positions by evaluation at the current parameter point.
The decoder below clamps only to make it total; W1 and W3 later prove that
every accepted chip already lies in the displayed closed interval, so the
clamp is definitionally inactive on actual leaf data. -/

/-- Decode an integer coordinate on one slot to its closed-face path vertex.
The `min` is a totality device for this standalone definition, not a semantic
relaxation: `evaluatedPathVertex_eq_pathVertex` removes it under the W1/W3
bounds supplied by an accepted rich leaf. -/
def evaluatedPathVertex
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p) (edge : Fin p)
    (coordinate : ℤ) : d.Vertex :=
  d.pathVertex edge ⟨min coordinate.toNat (d.length edge),
    Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- Under the natural closed-interval bounds, evaluating a form uses its
literal integer position rather than the total decoder's clamp. -/
theorem evaluatedPathVertex_eq_pathVertex
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)
    (edge : Fin p) (coordinate : ℤ)
    (hUpper : coordinate ≤ d.length edge) :
    evaluatedPathVertex d edge coordinate =
      d.pathVertex edge ⟨coordinate.toNat, by
        exact Nat.lt_succ_of_le (Int.toNat_le.mpr hUpper)⟩ := by
  unfold evaluatedPathVertex
  apply congrArg (d.pathVertex edge)
  apply Fin.ext
  exact min_eq_left (Int.toNat_le.mpr hUpper)

/-- A total raw-chip decoder.  The fallback is used only for malformed slot
indices; `w3Checks` proves those cannot occur in an accepted witness. -/
def evaluatedChipVertex
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p) (fallback : Fin n)
    (x : List ℤ) (slot : ℕ) (form : Form) : d.Vertex :=
  if hslot : slot < p then
    evaluatedPathVertex d ⟨slot, hslot⟩ (eval form x)
  else d.coreVertex fallback

theorem evaluatedChipVertex_of_slot_lt
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)
    (fallback : Fin n) (x : List ℤ) (slot : ℕ) (form : Form)
    (hslot : slot < p) :
    evaluatedChipVertex d fallback x slot form =
      evaluatedPathVertex d ⟨slot, hslot⟩ (eval form x) := by
  simp [evaluatedChipVertex, hslot]

/-- On an accepted rich leaf, a raw chip's physical decoded vertex is exactly
the path vertex of its W3-named endpoint.  W1 supplies the interval bounds
that make the total decoder's clamp inactive. -/
theorem evaluatedChipVertex_eq_namedPathVertex
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)
    (fallback : Fin n) (w : RichWitness)
    (core : ExplicitPotential.Core n p) (Γ : Context) (x : List ℤ)
    (hW1 : w.w1Checks core Γ = true) (hW3 : w.w3Checks core = true)
    (hx : Γ.Holds x)
    (hCoord : ∀ e : Fin p, eval (coordForm e.val) x = d.length e)
    (a : Fin n) {chip : ℕ × Form × ℤ} (hchip : chip ∈ w.chips) :
    ∃ i : Fin ((w.blockList a.val chip.1).length - 1),
      evaluatedChipVertex d fallback x chip.1 chip.2.1 =
        d.pathVertex ⟨chip.1, w.slot_lt_of_w3Checks core hW3 hchip⟩
          ⟨(w.pointValue x a.val chip.1 (i.val + 1)).toNat, by
            have hSlot := w.slot_lt_of_w3Checks core hW3 hchip
            let e : Fin p := ⟨chip.1, hSlot⟩
            have hLengths : ∀ t < (w.blockList a.val e.val).length,
                0 ≤ w.blockLengthValue x a.val e.val t := by
              intro t ht
              exact w.blockLength_nonneg_of_w1Checks core Γ x hW1 hx a e t ht
            have hLast : w.pointValue x a.val e.val (w.blockList a.val e.val).length =
                d.length e := by
              rw [w.pointValue_last_eq_coord_of_w1Checks core Γ x hW1 a e, hCoord e]
            have hUpper : w.pointValue x a.val e.val (i.val + 1) ≤ d.length e :=
              w.pointValue_le_of_lengths_last x a.val e.val
                (w.blockList a.val e.val).length (d.length e) (i.val + 1) hLengths hLast
                (by simpa [e] using (show i.val + 1 ≤ (w.blockList a.val chip.1).length by omega))
            exact Nat.lt_succ_of_le (Int.toNat_le.mpr hUpper)⟩ := by
  rcases w.chip_pointValue_eq_of_w3Checks core hW3 a hchip x with ⟨i, hi, hValue⟩
  let i' : Fin ((w.blockList a.val chip.1).length - 1) := ⟨i, hi⟩
  refine ⟨i', ?_⟩
  have hSlot := w.slot_lt_of_w3Checks core hW3 hchip
  let e : Fin p := ⟨chip.1, hSlot⟩
  have hLengths : ∀ t < (w.blockList a.val e.val).length,
      0 ≤ w.blockLengthValue x a.val e.val t := by
    intro t ht
    exact w.blockLength_nonneg_of_w1Checks core Γ x hW1 hx a e t ht
  have hLast : w.pointValue x a.val e.val (w.blockList a.val e.val).length = d.length e := by
    rw [w.pointValue_last_eq_coord_of_w1Checks core Γ x hW1 a e, hCoord e]
  have hUpper : eval chip.2.1 x ≤ d.length e := by
    rw [hValue]
    exact w.pointValue_le_of_lengths_last x a.val e.val
      (w.blockList a.val e.val).length (d.length e) (i'.val + 1) hLengths hLast
      (by simpa [e, i'] using (show i + 1 ≤ (w.blockList a.val chip.1).length by omega))
  calc
    evaluatedChipVertex d fallback x chip.1 chip.2.1 =
        evaluatedPathVertex d e (eval chip.2.1 x) :=
      evaluatedChipVertex_of_slot_lt d fallback x chip.1 chip.2.1 hSlot
    _ = d.pathVertex e ⟨(eval chip.2.1 x).toNat,
        Nat.lt_succ_of_le (Int.toNat_le.mpr hUpper)⟩ :=
      evaluatedPathVertex_eq_pathVertex d e _ hUpper
    _ = d.pathVertex e ⟨(w.pointValue x a.val chip.1 (i'.val + 1)).toNat, by
        rw [← hValue]
        exact Nat.lt_succ_of_le (Int.toNat_le.mpr hUpper)⟩ := by
      apply congrArg (d.pathVertex e)
      apply Fin.ext
      exact congrArg Int.toNat hValue

/-! ## Core divisor on a contracted face

The rich RPF divisor is written on the uncontracted core.  On a closed face
its coefficients must be summed over each quotient class, exactly as for the
existing explicit-potential certificate.  Keeping this operation next to the
raw chip divisor makes the final degree calculation independent of the W5
endpoint accounting. -/

/-- Push the raw core coefficient list to the quotient core of a degenerate
subdivision; interior vertices receive no core coefficient. -/
def richCoreDivisor
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p) (w : RichWitness) :
    CFDiv d.graph
  | Sum.inl c => ∑ v ∈ Finset.univ.filter (fun v : Fin n => d.rep v = c.val),
      w.divisorCore.getD v.val 0
  | Sum.inr _ => 0

@[simp] theorem richCoreDivisor_coreVertex
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)
    (w : RichWitness) (r : Fin n) :
    w.richCoreDivisor d (d.coreVertex r) =
      ∑ v ∈ Finset.univ.filter (fun v : Fin n => d.rep v = d.rep r),
        w.divisorCore.getD v.val 0 := rfl

@[simp] theorem richCoreDivisor_interiorVertex
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)
    (w : RichWitness) (e : Fin p) (o : Fin (d.length e - 1)) :
    w.richCoreDivisor d (d.interiorVertex e o) = 0 := rfl

/-- Quotienting the core cannot change its total degree. -/
theorem deg_richCoreDivisor
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p) (w : RichWitness) :
    deg (w.richCoreDivisor d) = ∑ v : Fin n, w.divisorCore.getD v.val 0 := by
  classical
  have hFiber : ∀ c : d.Class,
      (Finset.univ.filter (fun v : Fin n => d.rep v = c.val)) =
        Finset.univ.filter
          (fun v : Fin n => (⟨d.rep v, d.rep_idem v⟩ : d.Class) = c) := by
    intro c
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hsplit : deg (w.richCoreDivisor d) =
      ∑ c : d.Class, ∑ v ∈ Finset.univ.filter (fun v : Fin n => d.rep v = c.val),
        w.divisorCore.getD v.val 0 := by
    simp [deg, richCoreDivisor, Fintype.sum_sum_type]
  rw [hsplit, Finset.sum_congr rfl (fun c _ => by rw [hFiber c])]
  exact Finset.sum_fiberwise Finset.univ
    (fun v : Fin n => (⟨d.rep v, d.rep_idem v⟩ : d.Class))
    (fun v => w.divisorCore.getD v.val 0)

/-! ## C first-match chip accounting

`rawChipDivisor` deliberately decodes a chip by its evaluated *physical*
position.  The checker, on the other hand, uses syntactic named endpoints to
assign a chip to the first matching interior point.  The following small
list layer exposes that assignment as an ordinary sum of indicator terms.
It is independent of the closed-face geometry and is consequently reusable
both for W4 runs and for W5 endpoint prefixes/suffixes. -/

/-- The Boolean predicate by which the C checker assigns a raw chip to a
named point.  The `range (i - 1)` clause makes this the first syntactic match;
index zero is excluded separately by `chipAt`. -/
def chipMatches (w : RichWitness) (a e i : ℕ) (c : ℕ × Form × ℤ) : Bool :=
  c.1 == e && formEq c.2.1 (w.point a e i) &&
    (List.range (i - 1)).all
      (fun j => !(formEq c.2.1 (w.point a e (j + 1))))

/-- Folding conditional additions is the sum of the corresponding
indicators.  Keeping this as a list theorem prevents the W4/W5 bridge from
having to reason directly about the implementation of `List.foldl`. -/
private theorem foldl_cond_add_eq_sum {α : Type} (xs : List α)
    (test : α → Bool) (weight : α → ℤ) :
    xs.foldl (fun z x => if test x then z + weight x else z) 0 =
      (xs.map fun x => if test x then weight x else 0).sum := by
  have hacc : ∀ z : ℤ,
      xs.foldl (fun z x => if test x then z + weight x else z) z =
        z + (xs.map fun x => if test x then weight x else 0).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
        intro z
        simp only [List.foldl_cons, List.map_cons, List.sum_cons]
        split
        · rw [ih]
          ring
        · rw [ih]
          ring
  simpa using hacc 0

/-- At every nonzero named index, `chipAt` is exactly the sum of coefficients
of raw chips whose first syntactic match is that index. -/
theorem chipAt_eq_indicator_sum (w : RichWitness) (a e i : ℕ) (hi : i ≠ 0) :
    w.chipAt a e i =
      (w.chips.map fun c => if w.chipMatches a e i c then c.2.2 else 0).sum := by
  rw [chipAt, ite_eq_right (by simpa using hi)]
  exact foldl_cond_add_eq_sum w.chips (w.chipMatches a e i) (fun c => c.2.2)

/-- The inclusive named-point sum used in `chipPrefix` has an explicit raw
chip indicator expansion.  Index zero contributes nothing, so this remains
valid even for the tail candidate `s = 0`. -/
theorem chipPrefix_eq_indicator_sum (w : RichWitness) (a e s : ℕ) :
    w.chipPrefix a e s =
      (List.range (s + 1)).foldl (fun z i => z +
        (if i = 0 then 0 else
          (w.chips.map fun c => if w.chipMatches a e i c then c.2.2 else 0).sum)) 0 := by
  unfold chipPrefix
  have hstep : ∀ (z : ℤ) (i : ℕ), z + w.chipAt a e i = z +
      (if i = 0 then 0 else
        (w.chips.map fun c => if w.chipMatches a e i c then c.2.2 else 0).sum) := by
    intro z i
    by_cases hiz : i = 0
    · subst i
      simp
    · rw [chipAt_eq_indicator_sum _ _ _ _ hiz]
      simp [hiz]
  simp_rw [hstep]

/-- The head-side named-point sum used by `headCandidate`, before subtracting
the block-slope bound, likewise expands into first-match chip indicators. -/
theorem headChipSum_eq_indicator_sum (w : RichWitness) (a e s : ℕ) :
    (List.range (s + 1)).foldl (fun z t =>
      if t = 0 then z else z + w.chipAt a e ((w.blockList a e).length - t)) 0 =
      (List.range (s + 1)).foldl (fun z t =>
        if t = 0 then z else z +
          (if (w.blockList a e).length - t = 0 then 0 else
            (w.chips.map fun c =>
              if w.chipMatches a e ((w.blockList a e).length - t) c then c.2.2 else 0).sum)) 0 := by
  have hstep : ∀ (z : ℤ) (t : ℕ),
      (if t = 0 then z else z + w.chipAt a e ((w.blockList a e).length - t)) =
        if t = 0 then z else z +
          (if (w.blockList a e).length - t = 0 then 0 else
            (w.chips.map fun c =>
              if w.chipMatches a e ((w.blockList a e).length - t) c then c.2.2 else 0).sum) := by
    intro z t
    split
    · rfl
    · rename_i htz
      split
      · rename_i hsub
        simp [hsub]
      · rename_i hsub
        rw [chipAt_eq_indicator_sum _ _ _ _ hsub]
  simp_rw [hstep]

/-- The divisor represented by raw RPF chips once their slot/form positions
have been decoded on a particular closed face. -/
def rawChipDivisor
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p) (w : RichWitness)
    (decode : ℕ → Form → d.Vertex) : CFDiv d.graph :=
  (w.chips.map fun chip => chip.2.2 • oneChip
    (G := d.graph) (decode chip.1 chip.2.1)).sum

/-- Pointwise coefficient formula for decoded raw chips.  The endpoint-specific
decoder instantiation will identify the right side with W5's first-matched
prefix/suffix sums. -/
theorem rawChipDivisor_apply
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p) (w : RichWitness)
    (decode : ℕ → Form → d.Vertex) (vertex : d.Vertex) :
    w.rawChipDivisor d decode vertex =
      (w.chips.map fun chip =>
        if decode chip.1 chip.2.1 = vertex then chip.2.2 else 0).sum := by
  unfold rawChipDivisor
  induction w.chips with
  | nil => simp
  | cons chip chips ih =>
      simp only [List.map_cons, List.sum_cons]
      change (chip.2.2 • oneChip (G := d.graph) (decode chip.1 chip.2.1)) vertex +
        ((List.map (fun chip => chip.2.2 • oneChip
          (G := d.graph) (decode chip.1 chip.2.1)) chips).sum) vertex = _
      rw [ih]
      unfold oneChip
      simp [eq_comm]

/-- Exact raw-list coefficient formula at an interior vertex of a closed
face.  Instantiating `decode` with `evaluatedChipVertex` is the row-local
bridge needed by W4: it says that the only remaining geometric question is
which named endpoints evaluate to this particular interior offset.  No
injectivity of `pathVertex` is assumed (and none is available on a closed
face). -/
theorem evaluatedRawChipDivisor_apply_interiorVertex
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)
    (w : RichWitness) (fallback : Fin n)
    (x : List ℤ) (e : Fin p) (o : Fin (d.length e - 1)) :
    w.rawChipDivisor d (evaluatedChipVertex d fallback x)
        (d.interiorVertex e o) =
      (w.chips.map fun chip =>
        if evaluatedChipVertex d fallback x chip.1 chip.2.1 =
            d.interiorVertex e o then chip.2.2 else 0).sum := by
  exact w.rawChipDivisor_apply d (evaluatedChipVertex d fallback x)
    (d.interiorVertex e o)

/-- Decoding positions cannot change degree: every raw coefficient contributes
exactly once.  In particular this is compatible with chips collapsing onto a
core class. -/
theorem deg_rawChipDivisor
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p) (w : RichWitness)
    (decode : ℕ → Form → d.Vertex) :
    deg (w.rawChipDivisor d decode) =
      (w.chips.map fun chip => chip.2.2).sum := by
  have hsum : ∀ entries : List (ℕ × Form × ℤ),
      deg (entries.map fun chip => chip.2.2 • oneChip
        (G := d.graph) (decode chip.1 chip.2.1)).sum =
        (entries.map fun chip => chip.2.2).sum := by
    intro entries
    induction entries with
    | nil => simp
    | cons entry entries ih =>
        simp only [List.map_cons, List.sum_cons, map_add, ih, map_zsmul,
          deg_one_chip, smul_eq_mul, mul_one]
  exact hsum w.chips

end RichWitness

end Utilities.Subdivision.ClosedRowProof
