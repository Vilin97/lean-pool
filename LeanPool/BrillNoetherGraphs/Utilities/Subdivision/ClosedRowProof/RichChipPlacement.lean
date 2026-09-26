/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedRowProof.RichChipBridge

/-!
# Where a raw rich chip actually lands on a closed face

`RichChipDecoder` turns the raw `(slot, form, coefficient)` triples into a
divisor by evaluating each form and reading off `pathVertex`.  `RichChipBridge`
identifies the *physical mass at a coordinate* with the checker's syntactic
first-match accounting.  What is still missing between them is purely the
closed-face trichotomy: which coordinate of which slot is which vertex.

That is this module.  It has no arithmetic content; it is the `pathVertex`
case split (`0` / `length` / interior) pushed through `rawChipDivisor_apply`.

The one place it is not a triviality is the **head mass on a collapsed slot**.
When `length e = 0` the two endpoints of the slot are the same vertex, so
adding a tail term and a head term would count a chip there twice.
`headMassAdj` suppresses the head term exactly there; `RichChipBridge`'s
`rawChipMassAt_eq_zero_of_coord_eq_zero` says the suppressed value was `0`
anyway, so nothing is lost.
-/

@[expose] public section

namespace Utilities.Subdivision.ClosedRowProof

open Utilities

open MarkedGraphs.Certificate
open Utilities.Certificate

namespace RichWitness

variable {n p : ℕ}

/-! ## Vertex identities on a degenerate subdivision -/

section Vertices

variable (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)

theorem interiorVertex_ne_coreVertex (e : Fin p) (o : Fin (d.length e - 1))
    (r : Fin n) : d.interiorVertex e o ≠ d.coreVertex r := by
  simp [Utilities.Certificate.DegenerateSpec.DegSpec.interiorVertex,
    Utilities.Certificate.DegenerateSpec.DegSpec.coreVertex]

theorem interiorVertex_inj {s e : Fin p} {u : Fin (d.length s - 1)}
    {o : Fin (d.length e - 1)} (h : d.interiorVertex s u = d.interiorVertex e o) :
    s = e ∧ u.val = o.val := by
  have h' : (Sum.inr ⟨s, u⟩ : d.Vertex) = Sum.inr ⟨e, o⟩ := h
  have hs : (⟨s, u⟩ : d.Interior) = ⟨e, o⟩ := Sum.inr_injective h'
  exact ⟨congrArg (fun z : d.Interior => z.1) hs,
    congrArg (fun z : d.Interior => z.2.val) hs⟩

/-- Path vertices are determined by slot and position.  This tiny lemma is the
only place the dependency of `PathPosition` on the slot has to be substituted
away. -/
theorem pathVertex_congr {s e : Fin p} (hse : s = e) {k : d.PathPosition s}
    {k' : d.PathPosition e} (hk : k.val = k'.val) :
    d.pathVertex s k = d.pathVertex e k' := by
  subst hse
  exact congrArg (d.pathVertex s) (Fin.ext hk)

/-- On its own slot, the path vertex one past an interior offset *is* that
interior vertex. -/
theorem pathVertex_eq_interiorVertex (e : Fin p) (k : d.PathPosition e)
    (o : Fin (d.length e - 1)) (hval : k.val = o.val + 1) :
    d.pathVertex e k = d.interiorVertex e o := by
  have h0 : k.val ≠ 0 := by omega
  have hL : k.val ≠ d.length e := by
    have := o.isLt
    omega
  rw [d.pathVertex_interior e k h0 hL]
  exact congrArg (d.interiorVertex e) (Fin.ext (show k.val - 1 = o.val by omega))

/-- Conversely, a path vertex which is an interior vertex names its own slot
and offset. -/
theorem slot_eq_of_pathVertex_eq_interiorVertex {s e : Fin p}
    {k : d.PathPosition s} {o : Fin (d.length e - 1)}
    (h : d.pathVertex s k = d.interiorVertex e o) :
    s = e ∧ k.val = o.val + 1 := by
  by_cases h0 : k.val = 0
  · rw [Utilities.Certificate.DegenerateSpec.DegSpec.pathVertex,
      dite_eq_left h0] at h
    exact absurd h.symm (interiorVertex_ne_coreVertex d e o _)
  · by_cases hL : k.val = d.length s
    · rw [Utilities.Certificate.DegenerateSpec.DegSpec.pathVertex,
        dite_eq_right h0, dite_eq_left hL] at h
      exact absurd h.symm (interiorVertex_ne_coreVertex d e o _)
    · rw [d.pathVertex_interior s k h0 hL] at h
      obtain ⟨hse, hval⟩ := interiorVertex_inj d h
      have hval' : k.val - 1 = o.val := hval
      exact ⟨hse, by omega⟩

/-- The core-class half of the same trichotomy. -/
theorem pathVertex_eq_coreVertex_iff (s : Fin p) (k : d.PathPosition s)
    (r : Fin n) :
    d.pathVertex s k = d.coreVertex r ↔
      (k.val = 0 ∧ d.rep (d.core.tail s) = d.rep r) ∨
        (k.val ≠ 0 ∧ k.val = d.length s ∧ d.rep (d.core.head s) = d.rep r) := by
  unfold Utilities.Certificate.DegenerateSpec.DegSpec.pathVertex
  by_cases h0 : k.val = 0
  · rw [dite_eq_left h0, d.coreVertex_eq_iff]
    constructor
    · intro h
      exact Or.inl ⟨h0, h⟩
    · rintro (⟨-, h⟩ | ⟨hne, -⟩)
      · exact h
      · exact absurd h0 hne
  · rw [dite_eq_right h0]
    by_cases hL : k.val = d.length s
    · rw [dite_eq_left hL, d.coreVertex_eq_iff]
      constructor
      · intro h
        exact Or.inr ⟨h0, hL, h⟩
      · rintro (⟨h, -⟩ | ⟨-, -, h⟩)
        · exact absurd h h0
        · exact h
    · rw [dite_eq_right hL]
      constructor
      · intro h
        exact absurd h (interiorVertex_ne_coreVertex d s _ r)
      · rintro (⟨h, -⟩ | ⟨-, h, -⟩)
        · exact absurd h h0
        · exact absurd h hL

end Vertices

/-! ## The evaluated decoder, resolved -/

variable (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)

/-- Every raw chip of an accepted rich leaf evaluates into the closed interval
of its own slot.  This is the hypothesis both placement lemmas need in order
to remove the total decoder's clamp. -/
theorem chip_eval_mem_Icc (w : RichWitness) (core : ExplicitPotential.Core n p)
    (Γ : Context) (x : List ℤ) (hW1 : w.w1Checks core Γ = true)
    (hW3 : w.w3Checks core = true) (hx : Γ.Holds x)
    (hCoord : ∀ e : Fin p, eval (coordForm e.val) x = d.length e)
    (a : Fin n) {chip : ℕ × Form × ℤ} (hchip : chip ∈ w.chips)
    (hslot : chip.1 < p) :
    0 ≤ eval chip.2.1 x ∧ eval chip.2.1 x ≤ d.length ⟨chip.1, hslot⟩ := by
  obtain ⟨i, hi, hValue⟩ := w.chip_pointValue_eq_of_w3Checks core hW3 a hchip x
  have hLengths : ∀ t < (w.blockList a.val chip.1).length,
      0 ≤ w.blockLengthValue x a.val chip.1 t := fun t ht =>
    w.blockLength_nonneg_of_w1Checks core Γ x hW1 hx a ⟨chip.1, hslot⟩ t ht
  have hLast : w.pointValue x a.val chip.1 (w.blockList a.val chip.1).length =
      d.length ⟨chip.1, hslot⟩ := by
    rw [w.pointValue_last_eq_coord_of_w1Checks core Γ x hW1 a ⟨chip.1, hslot⟩,
      hCoord ⟨chip.1, hslot⟩]
  refine ⟨?_, ?_⟩
  · rw [hValue]
    exact w.pointValue_nonneg_of_lengths x a.val chip.1
      (w.blockList a.val chip.1).length (i + 1) hLengths (by omega)
  · rw [hValue]
    exact w.pointValue_le_of_lengths_last x a.val chip.1
      (w.blockList a.val chip.1).length (d.length ⟨chip.1, hslot⟩) (i + 1)
      hLengths hLast (by omega)

/-- The decoded vertex of an in-range chip is the literal path vertex of its
evaluated coordinate. -/
theorem evaluatedChipVertex_eq_pathVertex (fallback : Fin n)
    (x : List ℤ) {chip : ℕ × Form × ℤ} (hslot : chip.1 < p)
    (hUpper : eval chip.2.1 x ≤ d.length ⟨chip.1, hslot⟩) :
    evaluatedChipVertex d fallback x chip.1 chip.2.1 =
      d.pathVertex ⟨chip.1, hslot⟩ ⟨(eval chip.2.1 x).toNat,
        Nat.lt_succ_of_le (Int.toNat_le.mpr hUpper)⟩ := by
  rw [evaluatedChipVertex_of_slot_lt d fallback x chip.1 chip.2.1 hslot]
  exact evaluatedPathVertex_eq_pathVertex d ⟨chip.1, hslot⟩ _ hUpper

/-! ## Placement at an interior vertex -/

/-- **The interior chip coefficient.**  On a closed face the decoded raw chip
divisor at an interior vertex is exactly the physical chip mass of that slot
at that coordinate. -/
theorem rawChipDivisor_interiorVertex_eq_rawChipMassAt (w : RichWitness)
    (core : ExplicitPotential.Core n p) (Γ : Context) (x : List ℤ)
    (hW1 : w.w1Checks core Γ = true) (hW3 : w.w3Checks core = true)
    (hx : Γ.Holds x) (hCoord : ∀ e : Fin p, eval (coordForm e.val) x = d.length e)
    (a : Fin n) (fallback : Fin n) (e : Fin p) (o : Fin (d.length e - 1)) :
    w.rawChipDivisor d (evaluatedChipVertex d fallback x) (d.interiorVertex e o) =
      w.rawChipMassAt x e.val (o.val + 1) := by
  classical
  rw [w.rawChipDivisor_apply d (evaluatedChipVertex d fallback x)
    (d.interiorVertex e o), rawChipMassAt]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro c hc
  have hslot : c.1 < p := w.slot_lt_of_w3Checks core hW3 hc
  obtain ⟨hLower, hUpper⟩ :=
    chip_eval_mem_Icc d w core Γ x hW1 hW3 hx hCoord a hc hslot
  rw [evaluatedChipVertex_eq_pathVertex d fallback x hslot hUpper]
  by_cases hcond : c.1 = e.val ∧ eval c.2.1 x = (o.val + 1 : ℕ)
  · have hfin : (⟨c.1, hslot⟩ : Fin p) = e := Fin.ext hcond.1
    have hpos : d.pathVertex ⟨c.1, hslot⟩
        ⟨(eval c.2.1 x).toNat, Nat.lt_succ_of_le (Int.toNat_le.mpr hUpper)⟩ =
        d.interiorVertex e o := by
      refine (pathVertex_congr d hfin (k' := ⟨o.val + 1, by have := o.isLt; omega⟩)
        ?_).trans (pathVertex_eq_interiorVertex d e _ o rfl)
      change (eval c.2.1 x).toNat = o.val + 1
      have := hcond.2
      omega
    rw [ite_eq_left hpos, ite_eq_left]
    simp only [Bool.and_eq_true, beq_iff_eq, hcond.1, true_and]
    exact_mod_cast hcond.2
  · rw [ite_eq_right, ite_eq_right]
    · simp only [Bool.and_eq_true, beq_iff_eq, not_and]
      intro hEq
      have hne : ¬ eval c.2.1 x = (o.val + 1 : ℕ) := fun h => hcond ⟨hEq, h⟩
      exact_mod_cast hne
    · intro h
      obtain ⟨hse, hval⟩ := slot_eq_of_pathVertex_eq_interiorVertex d h
      have hval' : (eval c.2.1 x).toNat = o.val + 1 := hval
      exact hcond ⟨congrArg Fin.val hse, by omega⟩

/-! ## Placement at a core class -/

/-- The head-side physical chip mass, suppressed on a collapsed slot.

On a slot of length `0` the two displayed endpoints are the same vertex, so a
tail term and a head term would double count.  By
`RichChipBridge.rawChipMassAt_eq_zero_of_coord_eq_zero` an accepted rich leaf
has no chip on such a slot at all, so the suppressed value is `0`; the `if` is
what makes that visible without a hypothesis. -/
def headMassAdj (w : RichWitness) (x : List ℤ) (e : Fin p) : ℤ :=
  if d.length e = 0 then 0 else w.rawChipMassAt x e.val (d.length e)

/-- Exchange a finite index sum with a list sum. -/
private theorem sum_univ_list_sum {α β : Type} [Fintype β] (l : List α)
    (f : β → α → ℤ) :
    ∑ i : β, (l.map (f i)).sum = (l.map fun c => ∑ i : β, f i c).sum := by
  induction l with
  | nil => simp
  | cons c l ih =>
      simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

/-- **The core-class chip coefficient.**  On a closed face the decoded raw
chip divisor at a contracted core class is the sum, over slots, of the two
endpoint masses of the slots whose endpoints lie in the class. -/
theorem rawChipDivisor_coreVertex_eq (w : RichWitness)
    (core : ExplicitPotential.Core n p) (Γ : Context) (x : List ℤ)
    (hW1 : w.w1Checks core Γ = true) (hW3 : w.w3Checks core = true)
    (hx : Γ.Holds x) (hCoord : ∀ e : Fin p, eval (coordForm e.val) x = d.length e)
    (a : Fin n) (fallback : Fin n) (r : Fin n) :
    w.rawChipDivisor d (evaluatedChipVertex d fallback x) (d.coreVertex r) =
      ∑ e : Fin p,
        ((if d.rep (d.core.tail e) = d.rep r then w.rawChipMassAt x e.val 0 else 0) +
          (if d.rep (d.core.head e) = d.rep r then headMassAdj d w x e else 0)) := by
  classical
  rw [w.rawChipDivisor_apply d (evaluatedChipVertex d fallback x) (d.coreVertex r)]
  have hExpand : ∀ e : Fin p,
      ((if d.rep (d.core.tail e) = d.rep r then w.rawChipMassAt x e.val 0 else 0) +
        (if d.rep (d.core.head e) = d.rep r then headMassAdj d w x e else 0)) =
      (w.chips.map fun c =>
        (if d.rep (d.core.tail e) = d.rep r then
            (if c.1 == e.val && eval c.2.1 x == 0 then c.2.2 else 0) else 0) +
        (if d.rep (d.core.head e) = d.rep r ∧ d.length e ≠ 0 then
            (if c.1 == e.val && eval c.2.1 x == (d.length e : ℤ) then c.2.2 else 0)
          else 0)).sum := by
    intro e
    rw [List.sum_map_add]
    congr 1
    · by_cases hT : d.rep (d.core.tail e) = d.rep r
      · simp only [ite_eq_left hT]
        rw [rawChipMassAt]
      · simp [hT]
    · by_cases hH : d.rep (d.core.head e) = d.rep r
      · by_cases hL : d.length e = 0
        · simp [hH, hL, headMassAdj]
        · simp only [ite_eq_left hH, ite_eq_left (show d.rep (d.core.head e) = d.rep r ∧
            d.length e ≠ 0 from ⟨hH, hL⟩), headMassAdj, ite_eq_right hL]
          rw [rawChipMassAt]
      · simp [hH]
  rw [Finset.sum_congr rfl (fun e _ => hExpand e)]
  rw [sum_univ_list_sum w.chips (fun (e : Fin p) c =>
    (if d.rep (d.core.tail e) = d.rep r then
        (if c.1 == e.val && eval c.2.1 x == 0 then c.2.2 else 0) else 0) +
    (if d.rep (d.core.head e) = d.rep r ∧ d.length e ≠ 0 then
        (if c.1 == e.val && eval c.2.1 x == (d.length e : ℤ) then c.2.2 else 0)
      else 0))]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro c hc
  have hslot : c.1 < p := w.slot_lt_of_w3Checks core hW3 hc
  obtain ⟨hLower, hUpper⟩ :=
    chip_eval_mem_Icc d w core Γ x hW1 hW3 hx hCoord a hc hslot
  -- Only the chip's own slot contributes to the finite sum.
  have hsingle : ∀ e ∈ (Finset.univ : Finset (Fin p)), e ≠ ⟨c.1, hslot⟩ →
      ((if d.rep (d.core.tail e) = d.rep r then
          (if c.1 == e.val && eval c.2.1 x == 0 then c.2.2 else 0) else 0) +
        (if d.rep (d.core.head e) = d.rep r ∧ d.length e ≠ 0 then
            (if c.1 == e.val && eval c.2.1 x == (d.length e : ℤ) then c.2.2 else 0)
          else 0)) = 0 := by
    intro e _ hne
    have hval : ¬ (c.1 = e.val) := fun h => hne (Fin.ext h.symm)
    have hb : (c.1 == e.val) = false := by simpa using hval
    simp [hb]
  rw [Finset.sum_eq_single (⟨c.1, hslot⟩ : Fin p) hsingle (by simp)]
  rw [evaluatedChipVertex_eq_pathVertex d fallback x hslot hUpper]
  simp only [pathVertex_eq_coreVertex_iff d ⟨c.1, hslot⟩ _ r]
  have h0 : ((eval c.2.1 x).toNat = 0) ↔ (eval c.2.1 x = 0) := by omega
  have hLen : ((eval c.2.1 x).toNat = d.length ⟨c.1, hslot⟩) ↔
      (eval c.2.1 x = (d.length ⟨c.1, hslot⟩ : ℤ)) := by omega
  simp only [beq_self_eq_true, Bool.true_and, beq_iff_eq]
  by_cases hZ : eval c.2.1 x = 0
  · -- the chip sits on the tail core vertex
    have hN : (eval c.2.1 x).toNat = 0 := by omega
    have hsecond : (if d.rep (d.core.head (⟨c.1, hslot⟩ : Fin p)) = d.rep r ∧
        d.length (⟨c.1, hslot⟩ : Fin p) ≠ 0 then
          (if eval c.2.1 x = (d.length (⟨c.1, hslot⟩ : Fin p) : ℤ) then c.2.2 else 0)
        else 0) = 0 := by
      split_ifs with h1 h2
      · exact absurd (show d.length (⟨c.1, hslot⟩ : Fin p) = 0 by omega) h1.2
      · rfl
      · rfl
    rw [hsecond, ite_eq_left hZ]
    by_cases hT : d.rep (d.core.tail (⟨c.1, hslot⟩ : Fin p)) = d.rep r
    · rw [ite_eq_left hT, ite_eq_left (Or.inl ⟨hN, hT⟩), add_zero]
    · rw [ite_eq_right hT, ite_eq_right ?_, add_zero]
      rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact hT h
      · exact h hN
  · by_cases hQL : eval c.2.1 x = (d.length (⟨c.1, hslot⟩ : Fin p) : ℤ)
    · -- the chip sits on the head core vertex of a surviving slot
      have hNne : (eval c.2.1 x).toNat ≠ 0 := by omega
      have hNL : (eval c.2.1 x).toNat = d.length (⟨c.1, hslot⟩ : Fin p) := by omega
      have hLne : d.length (⟨c.1, hslot⟩ : Fin p) ≠ 0 := by omega
      rw [ite_eq_right hZ, ite_eq_left hQL]
      simp only [ite_self, zero_add]
      by_cases hH : d.rep (d.core.head (⟨c.1, hslot⟩ : Fin p)) = d.rep r
      · rw [ite_eq_left (Or.inr ⟨hNne, hNL, hH⟩), ite_eq_left ⟨hH, hLne⟩]
      · rw [ite_eq_right ?_, ite_eq_right (by tauto)]
        rintro (⟨h, -⟩ | ⟨-, -, h⟩)
        · exact hNne h
        · exact hH h
    · -- the chip sits strictly inside the slot
      have hNne : (eval c.2.1 x).toNat ≠ 0 := by omega
      have hNLne : (eval c.2.1 x).toNat ≠ d.length (⟨c.1, hslot⟩ : Fin p) := by omega
      rw [ite_eq_right hZ, ite_eq_right hQL]
      simp only [ite_self, add_zero]
      rw [ite_eq_right ?_]
      rintro (⟨h, -⟩ | ⟨-, h, -⟩)
      · exact hNne h
      · exact hNLne h

end RichWitness

end Utilities.Subdivision.ClosedRowProof
