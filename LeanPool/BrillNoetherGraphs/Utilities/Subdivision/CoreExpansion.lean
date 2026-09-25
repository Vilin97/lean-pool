/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionSeparator
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionConnectivity
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CubicCore
public import LeanPool.BrillNoetherGraphs.Utilities.Iso.GraphContractionTopology

/-!
# Expanding a small subdivision core to a larger one along a contraction

This module supplies the *inverse* of the usual reduction move.  Given a
subdivision specification `small` over an ordered loopless core, a piece of
passive combinatorial data called an `ExpansionData` describes a larger
ordered loopless core `bigCore` together with

* a **fibre map** `fib` sending each big core vertex to the small core vertex
  its fibre collapses onto, and
* a **slot classification** `kind`, saying for each big slot whether it is
  contracted into a fibre, carries exactly one small slot, or carries two
  small slots in series through a bivalent *marker* of the small core.

The double case is what makes the datum usable for loop-aware small cores.  A
semantic loop of a topological core is displayed in a loopless split core as
two slots meeting at a bivalent marker; on the big side it is one slot whose
two endpoints lie in a single fibre, and the marker is an interior vertex of
that slot.

The output is a *topological contraction certificate*
`bigSpec.graph → small.graph`: quotient multiplicities match exactly and every
fibre is connected.  Nothing here is specific to genus four.
-/

@[expose] public section
namespace Utilities.Subdivision.CoreExpansion
open Utilities.Certificate

open Utilities

open Finset
open ExplicitPotential
open SubdivisionGraph

variable {n p N Q : ℕ}

/-! ## Small helpers about path vertices -/

namespace PathHelpers

variable (spec : Spec n p)

theorem pathVertex_of_zero (j : Fin p) (q : spec.PathPosition j)
    (h : q.val = 0) :
    spec.pathVertex j q = spec.coreVertex (spec.core.tail j) := by
  unfold SubdivisionGraph.Spec.pathVertex
  rw [dite_eq_left h]

theorem pathVertex_of_last (j : Fin p) (q : spec.PathPosition j)
    (h0 : q.val ≠ 0) (h : q.val = spec.length j) :
    spec.pathVertex j q = spec.coreVertex (spec.core.head j) := by
  unfold SubdivisionGraph.Spec.pathVertex
  rw [dite_eq_right h0, dite_eq_left h]

theorem pathVertex_of_interior (j : Fin p) (q : spec.PathPosition j)
    (h0 : q.val ≠ 0) (h : q.val ≠ spec.length j) :
    spec.pathVertex j q =
      spec.interiorVertex j ⟨q.val - 1, by have := q.isLt; omega⟩ := by
  unfold SubdivisionGraph.Spec.pathVertex
  rw [dite_eq_right h0, dite_eq_right h]

theorem pathVertex_congr (j : Fin p) (q q' : spec.PathPosition j)
    (h : q.val = q'.val) : spec.pathVertex j q = spec.pathVertex j q' := by
  congr 1
  exact Fin.ext h

end PathHelpers

/-! ## Slot kinds -/

/-- The role of one big slot in the contraction. -/
inductive SlotKind (p : ℕ) where
  /-- The slot is contracted; both endpoints lie in one fibre. -/
  | contracted : SlotKind p
  /-- The slot maps onto a single small slot. -/
  | single : Fin p → SlotKind p
  /-- The slot maps onto two small slots in series through a marker. -/
  | double : Fin p → Fin p → SlotKind p
  deriving DecidableEq

/-- Length of a big slot forced by its role. -/
def kindLength (small : Spec n p) : SlotKind p → ℕ
  | .contracted => 1
  | .single j => small.length j
  | .double j₁ j₂ => small.length j₁ + small.length j₂

theorem kindLength_pos (small : Spec n p) (k : SlotKind p) :
    0 < kindLength small k := by
  cases k with
  | contracted => exact Nat.zero_lt_one
  | single j => exact small.length_pos j
  | double j₁ j₂ =>
      have := small.length_pos j₁
      simp only [kindLength]
      omega

/-- The vertex of the small subdivision sitting at path position `q` of a big
slot with the given role.  Positions beyond the slot are clamped, which keeps
the definition total and free of transported bound proofs. -/
def kindVertex (small : Spec n p) (fallback : Fin n) :
    SlotKind p → ℕ → small.Vertex
  | .contracted, _ => small.coreVertex fallback
  | .single j, q => small.pathVertex j ⟨min q (small.length j), by omega⟩
  | .double j₁ j₂, q =>
      if q ≤ small.length j₁ then
        small.pathVertex j₁ ⟨min q (small.length j₁), by omega⟩
      else
        small.pathVertex j₂
          ⟨min (q - small.length j₁) (small.length j₂), by omega⟩

theorem kindVertex_double_le {small : Spec n p} (j₁ j₂ : Fin p)
    (fallback : Fin n) {q : ℕ} (hq : q ≤ small.length j₁) :
    kindVertex small fallback (.double j₁ j₂) q =
      small.pathVertex j₁ ⟨min q (small.length j₁), by omega⟩ := by
  simp only [kindVertex, ite_eq_left hq]

theorem kindVertex_double_gt {small : Spec n p} (j₁ j₂ : Fin p)
    (fallback : Fin n) {q : ℕ} (hq : ¬ q ≤ small.length j₁) :
    kindVertex small fallback (.double j₁ j₂) q =
      small.pathVertex j₂
        ⟨min (q - small.length j₁) (small.length j₂), by omega⟩ := by
  simp only [kindVertex, ite_eq_right hq]

/-! ## The passive datum -/

/-- Passive expansion data.  `bigCore` is the expanded ordered core, `fib`
the fibre map on big core vertices, `kind` the slot classification, and
`owner`/`side` the explicit inverse of `kind` on small slots. -/
structure ExpansionData (n p N Q : ℕ) where
  /-- The expanded ordered core. -/
  bigCore : Core N Q
  /-- Which small core vertex a big core vertex collapses onto. -/
  fib : Fin N → Fin n
  /-- The role of each big slot. -/
  kind : Fin Q → SlotKind p
  /-- The big slot carrying a given small slot. -/
  owner : Fin p → Fin Q
  /-- Whether a small slot is the second half of a double. -/
  side : Fin p → Bool

namespace ExpansionData

variable (D : ExpansionData n p N Q) (C : Core n p)

/-- Endpoint compatibility of one big slot with its role. -/
def SlotCompatible (e : Fin Q) : Prop :=
  (D.kind e = .contracted → D.fib (D.bigCore.tail e) = D.fib (D.bigCore.head e)) ∧
  (∀ j : Fin p, D.kind e = .single j →
    D.fib (D.bigCore.tail e) = C.tail j ∧ D.fib (D.bigCore.head e) = C.head j) ∧
  (∀ j₁ j₂ : Fin p, D.kind e = .double j₁ j₂ →
    D.fib (D.bigCore.tail e) = C.tail j₁ ∧ C.head j₁ = C.tail j₂ ∧
      D.fib (D.bigCore.head e) = C.head j₂)

/-- `owner`/`side` really invert `kind`. -/
def SlotIndexed (e : Fin Q) : Prop :=
  (∀ j : Fin p, D.kind e = .single j → D.owner j = e ∧ D.side j = false) ∧
  (∀ j₁ j₂ : Fin p, D.kind e = .double j₁ j₂ →
    D.owner j₁ = e ∧ D.side j₁ = false ∧ D.owner j₂ = e ∧ D.side j₂ = true)

/-- Every small slot really is claimed by its recorded owner. -/
def SlotClaimed (j : Fin p) : Prop :=
  D.kind (D.owner j) ≠ .contracted ∧
  (∀ j' : Fin p, D.kind (D.owner j) = .single j' → D.side j = false ∧ j' = j) ∧
  (∀ j₁ j₂ : Fin p, D.kind (D.owner j) = .double j₁ j₂ →
    (D.side j = false ∧ j₁ = j) ∨ (D.side j = true ∧ j₂ = j))

/-- The middle vertex of a double is a genuine bivalent marker: it is outside
the image of the fibre map, and no other small slot ends there. -/
def MarkerIsolated (e : Fin Q) : Prop :=
  ∀ j₁ j₂ : Fin p, D.kind e = .double j₁ j₂ →
    (∀ v : Fin N, D.fib v ≠ C.head j₁) ∧
      (∀ j : Fin p, C.head j = C.head j₁ → j = j₁)

/-- All conditions a usable expansion datum has to satisfy.  Every clause
ranges over finite types, so the whole conjunction is decidable. -/
def Conditions : Prop :=
  (∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) ∧
  (∀ e : Fin Q, D.SlotCompatible C e) ∧
  (∀ e : Fin Q, D.SlotIndexed e) ∧
  (∀ j : Fin p, D.SlotClaimed j) ∧
  (∀ e : Fin Q, D.MarkerIsolated C e) ∧
  (∀ w : Fin n, ∃ j : Fin p, C.tail j = w ∨ C.head j = w) ∧
  (∀ (w : Fin n) (T : Finset (Fin N)),
      (∃ a, a ∈ T ∧ D.fib a = w) → (∃ b, b ∉ T ∧ D.fib b = w) →
      ∃ e : Fin Q, D.kind e = .contracted ∧ D.fib (D.bigCore.tail e) = w ∧
        ((D.bigCore.tail e ∈ T ∧ D.bigCore.head e ∉ T) ∨
          (D.bigCore.head e ∈ T ∧ D.bigCore.tail e ∉ T)))

instance decidableSlotCompatible (e : Fin Q) : Decidable (D.SlotCompatible C e) := by
  unfold SlotCompatible; infer_instance

instance decidableSlotIndexed (e : Fin Q) : Decidable (D.SlotIndexed e) := by
  unfold SlotIndexed; infer_instance

instance decidableSlotClaimed (j : Fin p) : Decidable (D.SlotClaimed j) := by
  unfold SlotClaimed; infer_instance

instance decidableMarkerIsolated (e : Fin Q) : Decidable (D.MarkerIsolated C e) := by
  unfold MarkerIsolated; infer_instance
instance decidableConditions : Decidable (D.Conditions C) := by
  unfold Conditions
  infer_instance

variable {D C}

theorem loopless_of_conditions (h : D.Conditions C) (e : Fin Q) :
    D.bigCore.tail e ≠ D.bigCore.head e := h.1 e

theorem compatible_of_conditions (h : D.Conditions C) (e : Fin Q) :
    D.SlotCompatible C e := h.2.1 e

theorem indexed_of_conditions (h : D.Conditions C) (e : Fin Q) :
    D.SlotIndexed e := h.2.2.1 e

theorem claimed_of_conditions (h : D.Conditions C) (j : Fin p) :
    D.SlotClaimed j := h.2.2.2.1 j

theorem marker_of_conditions (h : D.Conditions C) (e : Fin Q) :
    D.MarkerIsolated C e := h.2.2.2.2.1 e

theorem incident_of_conditions (h : D.Conditions C) (w : Fin n) :
    ∃ j : Fin p, C.tail j = w ∨ C.head j = w := h.2.2.2.2.2.1 w

theorem fibre_of_conditions (h : D.Conditions C) (w : Fin n)
    (T : Finset (Fin N)) (hIn : ∃ a, a ∈ T ∧ D.fib a = w)
    (hOut : ∃ b, b ∉ T ∧ D.fib b = w) :
    ∃ e : Fin Q, D.kind e = .contracted ∧ D.fib (D.bigCore.tail e) = w ∧
      ((D.bigCore.tail e ∈ T ∧ D.bigCore.head e ∉ T) ∨
        (D.bigCore.head e ∈ T ∧ D.bigCore.tail e ∉ T)) :=
  h.2.2.2.2.2.2 w T hIn hOut

/-- The owner of a small slot determines the big slot it lives in. -/
theorem owner_eq_of_single (h : D.Conditions C) {e : Fin Q} {j : Fin p}
    (hk : D.kind e = .single j) : D.owner j = e ∧ D.side j = false :=
  (indexed_of_conditions h e).1 j hk

theorem owner_eq_of_double (h : D.Conditions C) {e : Fin Q} {j₁ j₂ : Fin p}
    (hk : D.kind e = .double j₁ j₂) :
    D.owner j₁ = e ∧ D.side j₁ = false ∧ D.owner j₂ = e ∧ D.side j₂ = true :=
  (indexed_of_conditions h e).2 j₁ j₂ hk

/-- The big slot owning a small slot really carries it, and `side` records
which half. -/
theorem exists_carrier (h : D.Conditions C) (j : Fin p) :
    (D.kind (D.owner j) = .single j ∧ D.side j = false) ∨
      (∃ j₂, D.kind (D.owner j) = .double j j₂ ∧ D.side j = false) ∨
      (∃ j₁, D.kind (D.owner j) = .double j₁ j ∧ D.side j = true) := by
  have hc := claimed_of_conditions h j
  cases hk : D.kind (D.owner j) with
  | contracted => exact absurd hk hc.1
  | single j' =>
      obtain ⟨hs, he⟩ := hc.2.1 j' hk
      subst he
      exact Or.inl ⟨rfl, hs⟩
  | double j₁ j₂ =>
      rcases hc.2.2 j₁ j₂ hk with ⟨hs, he⟩ | ⟨hs, he⟩
      · subst he
        exact Or.inr (Or.inl ⟨j₂, rfl, hs⟩)
      · subst he
        exact Or.inr (Or.inr ⟨j₁, rfl, hs⟩)

/-! ## The expanded specification -/

variable (D)

/-- The length assignment on the expanded core forced by the datum. -/
def bigLength (small : Spec n p) (e : Fin Q) : ℕ :=
  kindLength small (D.kind e)

theorem bigLength_pos (small : Spec n p) (e : Fin Q) :
    0 < D.bigLength small e :=
  kindLength_pos small (D.kind e)

/-- The expanded subdivision specification. -/
def bigSpec (small : Spec n p) (hN : 0 < N)
    (hLoopless : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) :
    Spec N Q :=
  Spec.ofCore D.bigCore hN hLoopless (D.bigLength small) (D.bigLength_pos small)

end ExpansionData

/-! ## Path terms -/

section Terms

variable (small : Spec n p)

/-- The two ordered-endpoint indicators of one unit step of a small slot,
written through clamped path positions. -/
def smallStepTerm (j : Fin p) (a b : small.Vertex) (i : ℕ) : ℕ :=
  (if small.pathVertex j ⟨min i (small.length j), by omega⟩ = a ∧
      small.pathVertex j ⟨min (i + 1) (small.length j), by omega⟩ = b then 1
    else 0) +
  (if small.pathVertex j ⟨min (i + 1) (small.length j), by omega⟩ = a ∧
      small.pathVertex j ⟨min i (small.length j), by omega⟩ = b then 1 else 0)

/-- The two ordered-endpoint indicators of one unit step of a big slot, after
applying the contraction. -/
def kindStepTerm (fallback : Fin n) (k : SlotKind p) (a b : small.Vertex)
    (i : ℕ) : ℕ :=
  (if kindVertex small fallback k i = a ∧
      kindVertex small fallback k (i + 1) = b then 1 else 0) +
  (if kindVertex small fallback k (i + 1) = a ∧
      kindVertex small fallback k i = b then 1 else 0)

/-- Total contribution of one small slot. -/
def slotSum (j : Fin p) (a b : small.Vertex) : ℕ :=
  ∑ i : Fin (small.length j), smallStepTerm small j a b i.val

/-- Total contribution of the small slots carried by one big slot. -/
def kindSlotSum (a b : small.Vertex) : SlotKind p → ℕ
  | .contracted => 0
  | .single j => slotSum small j a b
  | .double j₁ j₂ => slotSum small j₁ a b + slotSum small j₂ a b

end Terms

/-! ## Per-slot evaluation -/

section SlotSum

variable {small : Spec n p}

theorem kindStepTerm_contracted (fallback : Fin n) {a b : small.Vertex}
    (hab : a ≠ b) (i : ℕ) :
    kindStepTerm small fallback .contracted a b i = 0 := by
  simp only [kindStepTerm, kindVertex]
  have h : ¬ (small.coreVertex fallback = a ∧ small.coreVertex fallback = b) := by
    rintro ⟨h1, h2⟩
    exact hab (h1 ▸ h2)
  simp [h]

theorem kindStepTerm_single (j : Fin p) (fallback : Fin n)
    (a b : small.Vertex) (i : ℕ) :
    kindStepTerm small fallback (.single j) a b i =
      smallStepTerm small j a b i := rfl

/-- Positions of the second half of a double, shifted past the first half. -/
theorem kindVertex_double_shift {j₁ j₂ : Fin p} (fallback : Fin n)
    (hMid : small.core.head j₁ = small.core.tail j₂) (i : ℕ) :
    kindVertex small fallback (.double j₁ j₂) (small.length j₁ + i) =
      small.pathVertex j₂ ⟨min i (small.length j₂), by omega⟩ := by
  rcases Nat.eq_zero_or_pos i with hzero | hpos
  · subst hzero
    rw [kindVertex_double_le j₁ j₂ fallback (by omega)]
    rw [PathHelpers.pathVertex_of_last small j₁ _ (by
        have := small.length_pos j₁
        simp only []
        omega) (by simp only []; omega),
      PathHelpers.pathVertex_of_zero small j₂ _ (by simp only []; omega), hMid]
  · rw [kindVertex_double_gt j₁ j₂ fallback (by omega)]
    exact PathHelpers.pathVertex_congr small j₂ _ _ (by simp only []; omega)

/-- Sum of the contracted step terms over one big slot, in terms of the small
slots it carries. -/
theorem kindSum_eq (fallback : Fin n) (k : SlotKind p)
    {a b : small.Vertex} (hab : a ≠ b)
    (hMid : ∀ j₁ j₂ : Fin p, k = .double j₁ j₂ →
      small.core.head j₁ = small.core.tail j₂) :
    (∑ i : Fin (kindLength small k),
        kindStepTerm small fallback k a b i.val) = kindSlotSum small a b k := by
  cases k with
  | contracted =>
      simp [kindStepTerm_contracted fallback hab, kindSlotSum]
  | single j =>
      simp only [kindLength, slotSum, kindSlotSum]
      exact Finset.sum_congr rfl fun i _ =>
        kindStepTerm_single j fallback a b i.val
  | double j₁ j₂ =>
      have hMid' : small.core.head j₁ = small.core.tail j₂ := hMid j₁ j₂ rfl
      have hFirst : ∀ i : ℕ, i < small.length j₁ →
          kindStepTerm small fallback (.double j₁ j₂) a b i =
            smallStepTerm small j₁ a b i := by
        intro i hi
        simp only [kindStepTerm, smallStepTerm,
          kindVertex_double_le j₁ j₂ fallback (le_of_lt hi),
          kindVertex_double_le j₁ j₂ fallback (Nat.succ_le_of_lt hi)]
      have hSecond : ∀ i : ℕ,
          kindStepTerm small fallback (.double j₁ j₂) a b (small.length j₁ + i) =
            smallStepTerm small j₂ a b i := by
        intro i
        have h1 := kindVertex_double_shift fallback hMid' i
        have h2 := kindVertex_double_shift fallback hMid' (i + 1)
        simp only [kindStepTerm, smallStepTerm]
        rw [h1, show small.length j₁ + i + 1 = small.length j₁ + (i + 1) by omega, h2]
      show (∑ i : Fin (small.length j₁ + small.length j₂),
          kindStepTerm small fallback (.double j₁ j₂) a b i.val) = _
      rw [Fin.sum_univ_add]
      simp only [slotSum, kindSlotSum]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => hFirst i.val i.isLt
      · exact Finset.sum_congr rfl fun i _ => hSecond i.val

end SlotSum


/-! ## A two-point indicator sum -/

private theorem sum_pair_indicator {V : Type} [Fintype V] [DecidableEq V]
    (u v : V) (huv : u ≠ v) (P R : V → Prop) [DecidablePred P] [DecidablePred R] :
    (∑ x : V, ∑ y : V,
        if P x ∧ R y then
          (if (u = x ∧ v = y) ∨ (u = y ∧ v = x) then (1 : ℕ) else 0) else 0)
      = (if P u ∧ R v then 1 else 0) + (if P v ∧ R u then 1 else 0) := by
  classical
  set F : V → V → ℕ := fun x y =>
    if P x ∧ R y then
      (if (u = x ∧ v = y) ∨ (u = y ∧ v = x) then (1 : ℕ) else 0) else 0 with hF
  have hzero : ∀ x y : V, ¬ ((u = x ∧ v = y) ∨ (u = y ∧ v = x)) → F x y = 0 := by
    intro x y hxy
    by_cases h : P x ∧ R y <;> simp [hF, h, hxy]
  have hinner : ∀ x : V, (∑ y : V, F x y) = F x u + F x v := by
    intro x
    have hsub : (∑ y ∈ ({u, v} : Finset V), F x y) = ∑ y : V, F x y := by
      refine Finset.sum_subset (Finset.subset_univ _) ?_
      intro y _ hy
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
      refine hzero x y ?_
      rintro (⟨_, h2⟩ | ⟨h1, _⟩)
      · exact hy.2 h2.symm
      · exact hy.1 h1.symm
    rw [← hsub, Finset.sum_pair huv]
  have houter : (∑ x : V, (F x u + F x v)) = (F u u + F u v) + (F v u + F v v) := by
    have hsub : (∑ x ∈ ({u, v} : Finset V), (F x u + F x v))
        = ∑ x : V, (F x u + F x v) := by
      refine Finset.sum_subset (Finset.subset_univ _) ?_
      intro x _ hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      have h1 : F x u = 0 := by
        refine hzero x u ?_
        rintro (⟨h1, _⟩ | ⟨_, h2⟩)
        · exact hx.1 h1.symm
        · exact hx.2 h2.symm
      have h2 : F x v = 0 := by
        refine hzero x v ?_
        rintro (⟨h1, _⟩ | ⟨_, h2⟩)
        · exact hx.1 h1.symm
        · exact hx.2 h2.symm
      simp [h1, h2]
    rw [← hsub, Finset.sum_pair huv]
  have huu : F u u = 0 := by
    refine hzero u u ?_
    rintro (⟨_, h2⟩ | ⟨_, h2⟩)
    · exact huv h2.symm
    · exact huv h2.symm
  have hvv : F v v = 0 := by
    refine hzero v v ?_
    rintro (⟨h1, _⟩ | ⟨h1, _⟩)
    · exact huv h1
    · exact huv h1
  have huv2 : F u v = if P u ∧ R v then 1 else 0 := by
    by_cases h : P u ∧ R v <;> simp [hF, h]
  have hvu : F v u = if P v ∧ R u then 1 else 0 := by
    by_cases h : P v ∧ R u <;> simp [hF, h, huv, Ne.symm huv]
  calc (∑ x : V, ∑ y : V, F x y) = ∑ x : V, (F x u + F x v) :=
        Finset.sum_congr rfl fun x _ => hinner x
    _ = (F u u + F u v) + (F v u + F v v) := houter
    _ = (if P u ∧ R v then 1 else 0) + (if P v ∧ R u then 1 else 0) := by
        rw [huu, hvv, huv2, hvu]
        omega

/-! ## Small-side edge count -/

theorem numEdges_small_eq (small : Spec n p) (a b : small.Vertex) (hab : a ≠ b) :
    numEdges small.graph a b = ∑ j : Fin p, slotSum small j a b := by
  classical
  rw [small.num_edges_eq_sum_steps a b]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  have hleft : small.stepLeft j i =
      small.pathVertex j ⟨min i.val (small.length j), by omega⟩ := by
    rw [← small.pathVertex_stepLeftPosition j i]
    exact PathHelpers.pathVertex_congr small j _ _ (by
      have := i.isLt
      simp only [SubdivisionGraph.Spec.stepLeftPosition]
      omega)
  have hright : small.stepRight j i =
      small.pathVertex j ⟨min (i.val + 1) (small.length j), by omega⟩ := by
    rw [← small.pathVertex_stepRightPosition j i]
    exact PathHelpers.pathVertex_congr small j _ _ (by
      have := i.isLt
      simp only [SubdivisionGraph.Spec.stepRightPosition]
      omega)
  have hne : small.stepLeft j i ≠ small.stepRight j i :=
    small.stepLeft_ne_stepRight j i
  simp only [SubdivisionGraph.Spec.unitEdge, smallStepTerm, Prod.mk.injEq,
    ← hleft, ← hright]
  by_cases h1 : small.stepLeft j i = a ∧ small.stepRight j i = b
  · have h2 : ¬ (small.stepRight j i = a ∧ small.stepLeft j i = b) := by
      rintro ⟨_, hl⟩
      exact hab (h1.1.symm.trans hl)
    have hswap : ¬ (small.stepLeft j i = b ∧ small.stepRight j i = a) := by
      rintro ⟨hl, hr⟩
      exact h2 ⟨hr, hl⟩
    simp [h1]
    exact fun _ => hab
  · by_cases h2 : small.stepRight j i = a ∧ small.stepLeft j i = b
    · have hswap : small.stepLeft j i = b ∧ small.stepRight j i = a := ⟨h2.2, h2.1⟩
      simp [h2]
      exact fun _ => hab
    · have hswap : ¬ (small.stepLeft j i = b ∧ small.stepRight j i = a) := by
        rintro ⟨hl, hr⟩
        exact h2 ⟨hr, hl⟩
      simp [h1, h2, hswap]

/-! ## Endpoints of a big slot -/

section Endpoints

variable {small : Spec n p} (fallback : Fin n)

theorem kindVertex_zero_single (j : Fin p) :
    kindVertex small fallback (.single j) 0 =
      small.coreVertex (small.core.tail j) :=
  PathHelpers.pathVertex_of_zero small j _ (by simp)

theorem kindVertex_zero_double (j₁ j₂ : Fin p) :
    kindVertex small fallback (.double j₁ j₂) 0 =
      small.coreVertex (small.core.tail j₁) := by
  rw [kindVertex_double_le j₁ j₂ fallback (Nat.zero_le _)]
  exact PathHelpers.pathVertex_of_zero small j₁ _ (by simp)

theorem kindVertex_last_single (j : Fin p) :
    kindVertex small fallback (.single j) (small.length j) =
      small.coreVertex (small.core.head j) := by
  have h : kindVertex small fallback (.single j) (small.length j)
      = small.pathVertex j ⟨small.length j, by omega⟩ :=
    PathHelpers.pathVertex_congr small j _ _ (by simp)
  rw [h]
  exact small.pathVertex_length j

theorem kindVertex_last_double (j₁ j₂ : Fin p) :
    kindVertex small fallback (.double j₁ j₂)
        (small.length j₁ + small.length j₂) =
      small.coreVertex (small.core.head j₂) := by
  have h2 := small.length_pos j₂
  have h : kindVertex small fallback (.double j₁ j₂)
      (small.length j₁ + small.length j₂)
      = small.pathVertex j₂ ⟨small.length j₂, by omega⟩ := by
    rw [kindVertex_double_gt j₁ j₂ fallback (by omega)]
    refine PathHelpers.pathVertex_congr small j₂ _ _ ?_
    show min (small.length j₁ + small.length j₂ - small.length j₁)
      (small.length j₂) = small.length j₂
    omega
  rw [h]
  exact small.pathVertex_length j₂

end Endpoints

/-! ## The contraction certificate -/

namespace ExpansionData

variable (D : ExpansionData n p N Q) (small : Spec n p) (hN : 0 < N)
    (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)

/-- The contraction on subdivision vertices. -/
def vertexMap : (D.bigSpec small hN hL).Vertex → small.Vertex :=
  fun x => match x with
    | Sum.inl v => small.coreVertex (D.fib v)
    | Sum.inr y =>
        kindVertex small (D.fib (D.bigCore.tail y.1)) (D.kind y.1) (y.2.val + 1)

theorem vertexMap_coreVertex (v : Fin N) :
    vertexMap D small hN hL ((D.bigSpec small hN hL).coreVertex v)
      = small.coreVertex (D.fib v) := rfl

theorem vertexMap_interiorVertex (e : Fin Q)
    (o : Fin ((D.bigSpec small hN hL).length e - 1)) :
    vertexMap D small hN hL ((D.bigSpec small hN hL).interiorVertex e o)
      = kindVertex small (D.fib (D.bigCore.tail e)) (D.kind e) (o.val + 1) := rfl

variable {D small hN hL}

/-- The contraction reads off the small path vertex at the same position. -/
theorem vertexMap_pathVertex (hCond : D.Conditions small.core) (e : Fin Q)
    (q : (D.bigSpec small hN hL).PathPosition e) :
    vertexMap D small hN hL ((D.bigSpec small hN hL).pathVertex e q)
      = kindVertex small (D.fib (D.bigCore.tail e)) (D.kind e) q.val := by
  have hcomp := compatible_of_conditions hCond e
  by_cases h0 : q.val = 0
  · rw [PathHelpers.pathVertex_of_zero _ e q h0, h0,
      vertexMap_coreVertex]
    show small.coreVertex (D.fib (D.bigCore.tail e)) =
      kindVertex small (D.fib (D.bigCore.tail e)) (D.kind e) 0
    cases hk : D.kind e with
    | contracted => rfl
    | single j =>
        rw [kindVertex_zero_single, (hcomp.2.1 j hk).1]
    | double j₁ j₂ =>
        rw [kindVertex_zero_double, (hcomp.2.2 j₁ j₂ hk).1]
  · by_cases hlast : q.val = (D.bigSpec small hN hL).length e
    · rw [PathHelpers.pathVertex_of_last _ e q h0 hlast, hlast,
        vertexMap_coreVertex]
      show small.coreVertex (D.fib (D.bigCore.head e)) =
        kindVertex small (D.fib (D.bigCore.tail e)) (D.kind e)
          (kindLength small (D.kind e))
      cases hk : D.kind e with
      | contracted => exact congrArg small.coreVertex (hcomp.1 hk).symm
      | single j =>
          rw [show kindLength small (SlotKind.single j) = small.length j from rfl,
            kindVertex_last_single, (hcomp.2.1 j hk).2]
      | double j₁ j₂ =>
          rw [show kindLength small (SlotKind.double j₁ j₂) =
              small.length j₁ + small.length j₂ from rfl,
            kindVertex_last_double, (hcomp.2.2 j₁ j₂ hk).2.2]
    · rw [PathHelpers.pathVertex_of_interior _ e q h0 hlast,
        vertexMap_interiorVertex]
      congr 1
      show q.val - 1 + 1 = q.val
      omega

theorem vertexMap_stepLeft (hCond : D.Conditions small.core) (e : Fin Q)
    (i : Fin ((D.bigSpec small hN hL).length e)) :
    vertexMap D small hN hL ((D.bigSpec small hN hL).stepLeft e i)
      = kindVertex small (D.fib (D.bigCore.tail e)) (D.kind e) i.val := by
  rw [← (D.bigSpec small hN hL).pathVertex_stepLeftPosition e i,
    vertexMap_pathVertex hCond e]
  rfl

theorem vertexMap_stepRight (hCond : D.Conditions small.core) (e : Fin Q)
    (i : Fin ((D.bigSpec small hN hL).length e)) :
    vertexMap D small hN hL ((D.bigSpec small hN hL).stepRight e i)
      = kindVertex small (D.fib (D.bigCore.tail e)) (D.kind e) (i.val + 1) := by
  rw [← (D.bigSpec small hN hL).pathVertex_stepRightPosition e i,
    vertexMap_pathVertex hCond e]
  rfl

end ExpansionData

/-! ## The quotient multiplicity equation -/

namespace ExpansionData

variable {D : ExpansionData n p N Q} {small : Spec n p} {hN : 0 < N}
    {hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e}

/-- Regroup the small slots carried by a big slot by their recorded owner. -/
theorem owner_aggregate (hCond : D.Conditions small.core)
    (a b : small.Vertex) (e : Fin Q) :
    kindSlotSum small a b (D.kind e)
      = ∑ j : Fin p, if D.owner j = e then slotSum small j a b else 0 := by
  classical
  cases hk : D.kind e with
  | contracted =>
      show (0 : ℕ) = _
      refine (Finset.sum_eq_zero fun j _ => ?_).symm
      by_cases ho : D.owner j = e
      · exact absurd (by rw [ho]; exact hk) (claimed_of_conditions hCond j).1
      · exact ite_eq_right ho
  | single j₀ =>
      obtain ⟨ho1, _⟩ := (indexed_of_conditions hCond e).1 j₀ hk
      show slotSum small j₀ a b = _
      symm
      have hzero : ∀ j ∈ (Finset.univ : Finset (Fin p)), j ≠ j₀ →
          (if D.owner j = e then slotSum small j a b else 0) = 0 := by
        intro j _ hj
        by_cases ho : D.owner j = e
        · exact absurd ((claimed_of_conditions hCond j).2.1 j₀
            (by rw [ho]; exact hk)).2.symm hj
        · exact ite_eq_right ho
      rw [Finset.sum_eq_single j₀ hzero (fun h => absurd (Finset.mem_univ j₀) h),
        ite_eq_left ho1]
  | double j₁ j₂ =>
      obtain ⟨ho1, hs1, ho2, hs2⟩ := (indexed_of_conditions hCond e).2 j₁ j₂ hk
      have hne : j₁ ≠ j₂ := by
        intro h
        rw [h, hs2] at hs1
        exact Bool.noConfusion hs1
      show slotSum small j₁ a b + slotSum small j₂ a b = _
      symm
      have hsub : (∑ j ∈ ({j₁, j₂} : Finset (Fin p)),
          (if D.owner j = e then slotSum small j a b else 0))
          = ∑ j : Fin p, (if D.owner j = e then slotSum small j a b else 0) := by
        refine Finset.sum_subset (Finset.subset_univ _) ?_
        intro j _ hj
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
        by_cases ho : D.owner j = e
        · exfalso
          rcases (claimed_of_conditions hCond j).2.2 j₁ j₂ (by rw [ho]; exact hk) with
            ⟨_, h⟩ | ⟨_, h⟩
          · exact hj.1 h.symm
          · exact hj.2 h.symm
        · exact ite_eq_right ho
      rw [← hsub, Finset.sum_pair hne, ite_eq_left ho1, ite_eq_left ho2]

/-- **Quotient multiplicities match exactly.** -/
theorem valid_multiplicity (hCond : D.Conditions small.core)
    (a b : small.Vertex) (hab : a ≠ b) :
    numEdges small.graph a b =
      ∑ x : (D.bigSpec small hN hL).Vertex, ∑ y : (D.bigSpec small hN hL).Vertex,
        if vertexMap D small hN hL x = a ∧ vertexMap D small hN hL y = b then
          numEdges (D.bigSpec small hN hL).graph x y else 0 := by
  classical
  have hstep1 : ∀ x y : (D.bigSpec small hN hL).Vertex,
      (if vertexMap D small hN hL x = a ∧ vertexMap D small hN hL y = b then
        numEdges (D.bigSpec small hN hL).graph x y else 0)
      = ∑ s : (D.bigSpec small hN hL).Step,
          (if vertexMap D small hN hL x = a ∧ vertexMap D small hN hL y = b then
            (if ((D.bigSpec small hN hL).stepLeft s.1 s.2 = x ∧
                (D.bigSpec small hN hL).stepRight s.1 s.2 = y) ∨
              ((D.bigSpec small hN hL).stepLeft s.1 s.2 = y ∧
                (D.bigSpec small hN hL).stepRight s.1 s.2 = x) then 1 else 0)
          else 0) := by
    intro x y
    by_cases h : vertexMap D small hN hL x = a ∧ vertexMap D small hN hL y = b
    · simp only [ite_eq_left h]
      rw [(D.bigSpec small hN hL).num_edges_eq_sum_steps x y]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [SubdivisionGraph.Spec.unitEdge, Prod.mk.injEq]
    · simp only [ite_eq_right h, Finset.sum_const_zero]
  have hswap : (∑ x : (D.bigSpec small hN hL).Vertex,
      ∑ y : (D.bigSpec small hN hL).Vertex,
        if vertexMap D small hN hL x = a ∧ vertexMap D small hN hL y = b then
          numEdges (D.bigSpec small hN hL).graph x y else 0)
      = ∑ s : (D.bigSpec small hN hL).Step,
          ((if vertexMap D small hN hL
                ((D.bigSpec small hN hL).stepLeft s.1 s.2) = a ∧
              vertexMap D small hN hL
                ((D.bigSpec small hN hL).stepRight s.1 s.2) = b then 1 else 0)
            + (if vertexMap D small hN hL
                  ((D.bigSpec small hN hL).stepRight s.1 s.2) = a ∧
                vertexMap D small hN hL
                  ((D.bigSpec small hN hL).stepLeft s.1 s.2) = b then 1 else 0)) := by
    simp_rw [hstep1]
    rw [show (∑ x : (D.bigSpec small hN hL).Vertex,
          ∑ y : (D.bigSpec small hN hL).Vertex,
            ∑ s : (D.bigSpec small hN hL).Step, _)
        = ∑ x : (D.bigSpec small hN hL).Vertex,
          ∑ s : (D.bigSpec small hN hL).Step,
            ∑ y : (D.bigSpec small hN hL).Vertex, _ from
      Finset.sum_congr rfl fun x _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact sum_pair_indicator _ _
      ((D.bigSpec small hN hL).stepLeft_ne_stepRight s.1 s.2)
      (fun x => vertexMap D small hN hL x = a)
      (fun y => vertexMap D small hN hL y = b)
  rw [hswap, Fintype.sum_sigma, numEdges_small_eq small a b hab]
  have hslot : ∀ e : Fin Q,
      (∑ i : Fin ((D.bigSpec small hN hL).length e),
        ((if vertexMap D small hN hL ((D.bigSpec small hN hL).stepLeft e i) = a ∧
            vertexMap D small hN hL
              ((D.bigSpec small hN hL).stepRight e i) = b then 1 else 0)
          + (if vertexMap D small hN hL
                ((D.bigSpec small hN hL).stepRight e i) = a ∧
              vertexMap D small hN hL
                ((D.bigSpec small hN hL).stepLeft e i) = b then 1 else 0)))
      = ∑ j : Fin p, if D.owner j = e then slotSum small j a b else 0 := by
    intro e
    have hterm : ∀ i : Fin ((D.bigSpec small hN hL).length e),
        ((if vertexMap D small hN hL ((D.bigSpec small hN hL).stepLeft e i) = a ∧
            vertexMap D small hN hL
              ((D.bigSpec small hN hL).stepRight e i) = b then 1 else 0)
          + (if vertexMap D small hN hL
                ((D.bigSpec small hN hL).stepRight e i) = a ∧
              vertexMap D small hN hL
                ((D.bigSpec small hN hL).stepLeft e i) = b then 1 else 0))
        = kindStepTerm small (D.fib (D.bigCore.tail e)) (D.kind e) a b i.val := by
      intro i
      rw [vertexMap_stepLeft hCond e i, vertexMap_stepRight hCond e i]
      rfl
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    rw [show (∑ i : Fin ((D.bigSpec small hN hL).length e),
        kindStepTerm small (D.fib (D.bigCore.tail e)) (D.kind e) a b i.val)
        = ∑ i : Fin (kindLength small (D.kind e)),
          kindStepTerm small (D.fib (D.bigCore.tail e)) (D.kind e) a b i.val from rfl]
    rw [kindSum_eq (D.fib (D.bigCore.tail e)) (D.kind e) hab
      (fun j₁ j₂ hkk => ((compatible_of_conditions hCond e).2.2 j₁ j₂ hkk).2.1)]
    exact owner_aggregate hCond a b e
  rw [Finset.sum_congr rfl fun e _ => hslot e, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

end ExpansionData

/-! ## Shape of the image of an interior position -/

/-- The small slots a big slot carries. -/
def SlotUses (k : SlotKind p) (j : Fin p) : Prop :=
  k = .single j ∨ (∃ j₂, k = .double j j₂) ∨ (∃ j₁, k = .double j₁ j)

section InteriorShape

variable {small : Spec n p}

theorem kindVertex_interior_cases (fallback : Fin n) (k : SlotKind p)
    {q : ℕ} (h0 : 0 < q) (hq : q < kindLength small k) :
    (∃ j : Fin p, SlotUses k j ∧ ∃ o : Fin (small.length j - 1),
        kindVertex small fallback k q = small.interiorVertex j o)
      ∨ (∃ j₁ j₂ : Fin p, k = .double j₁ j₂ ∧
          kindVertex small fallback k q =
            small.coreVertex (small.core.head j₁)) := by
  cases k with
  | contracted =>
      simp only [kindLength] at hq
      omega
  | single j =>
      simp only [kindLength] at hq
      left
      refine ⟨j, Or.inl rfl, ⟨q - 1, by omega⟩, ?_⟩
      have hcast : kindVertex small fallback (.single j) q
          = small.pathVertex j ⟨q, by omega⟩ := by
        refine PathHelpers.pathVertex_congr small j _ _ ?_
        show min q (small.length j) = q
        omega
      rw [hcast]
      exact PathHelpers.pathVertex_of_interior small j _
        (by show q ≠ 0; omega) (by show q ≠ small.length j; omega)
  | double j₁ j₂ =>
      simp only [kindLength] at hq
      by_cases hle : q ≤ small.length j₁
      · rcases eq_or_lt_of_le hle with heq | hlt
        · right
          refine ⟨j₁, j₂, rfl, ?_⟩
          rw [kindVertex_double_le j₁ j₂ fallback hle]
          exact PathHelpers.pathVertex_of_last small j₁ _
            (by show min q (small.length j₁) ≠ 0; omega)
            (by show min q (small.length j₁) = small.length j₁; omega)
        · left
          refine ⟨j₁, Or.inr (Or.inl ⟨j₂, rfl⟩), ⟨q - 1, by omega⟩, ?_⟩
          rw [kindVertex_double_le j₁ j₂ fallback hle]
          have hcast : small.pathVertex j₁
              ⟨min q (small.length j₁), by omega⟩
              = small.pathVertex j₁ ⟨q, by omega⟩ :=
            PathHelpers.pathVertex_congr small j₁ _ _ (by
              show min q (small.length j₁) = q
              omega)
          rw [hcast]
          exact PathHelpers.pathVertex_of_interior small j₁ _
            (by show q ≠ 0; omega) (by show q ≠ small.length j₁; omega)
      · left
        refine ⟨j₂, Or.inr (Or.inr ⟨j₁, rfl⟩),
          ⟨q - small.length j₁ - 1, by omega⟩, ?_⟩
        rw [kindVertex_double_gt j₁ j₂ fallback hle]
        have hcast : small.pathVertex j₂
            ⟨min (q - small.length j₁) (small.length j₂), by omega⟩
            = small.pathVertex j₂ ⟨q - small.length j₁, by omega⟩ :=
          PathHelpers.pathVertex_congr small j₂ _ _ (by
            show min (q - small.length j₁) (small.length j₂)
              = q - small.length j₁
            omega)
        rw [hcast]
        exact PathHelpers.pathVertex_of_interior small j₂ _
          (by show q - small.length j₁ ≠ 0; omega)
          (by show q - small.length j₁ ≠ small.length j₂; omega)

theorem kindVertex_interior_injective (fallback : Fin n) (k : SlotKind p)
    (hne : ∀ j₁ j₂ : Fin p, k = .double j₁ j₂ → j₁ ≠ j₂)
    {q q' : ℕ} (h0 : 0 < q) (hq : q < kindLength small k)
    (h0' : 0 < q') (hq' : q' < kindLength small k)
    (h : kindVertex small fallback k q = kindVertex small fallback k q') :
    q = q' := by
  cases k with
  | contracted =>
      simp only [kindLength] at hq
      omega
  | single j =>
      simp only [kindLength] at hq hq'
      have e1 : kindVertex small fallback (.single j) q
          = small.pathVertex j ⟨q, by omega⟩ :=
        PathHelpers.pathVertex_congr small j _ _ (by
          show min q (small.length j) = q; omega)
      have e2 : kindVertex small fallback (.single j) q'
          = small.pathVertex j ⟨q', by omega⟩ :=
        PathHelpers.pathVertex_congr small j _ _ (by
          show min q' (small.length j) = q'; omega)
      rw [e1, e2] at h
      exact congrArg Fin.val (small.pathVertex_injective j h)
  | double j₁ j₂ =>
      simp only [kindLength] at hq hq'
      have hjne : j₁ ≠ j₂ := hne j₁ j₂ rfl
      have hpathA : ∀ r : ℕ, ∀ _hle : r ≤ small.length j₁,
          kindVertex small fallback (.double j₁ j₂) r
            = small.pathVertex j₁ ⟨r, by omega⟩ := by
        intro r hle
        rw [kindVertex_double_le j₁ j₂ fallback hle]
        exact PathHelpers.pathVertex_congr small j₁ _ _ (by
          show min r (small.length j₁) = r; omega)
      have hpathB : ∀ r : ℕ, ∀ _hr : r < small.length j₁ + small.length j₂,
          ∀ _hgt : ¬ r ≤ small.length j₁,
          kindVertex small fallback (.double j₁ j₂) r
            = small.pathVertex j₂ ⟨r - small.length j₁, by omega⟩ := by
        intro r hr hgt
        rw [kindVertex_double_gt j₁ j₂ fallback hgt]
        exact PathHelpers.pathVertex_congr small j₂ _ _ (by
          show min (r - small.length j₁) (small.length j₂)
            = r - small.length j₁
          omega)
      by_cases hle : q ≤ small.length j₁ <;> by_cases hle' : q' ≤ small.length j₁
      · rw [hpathA q hle, hpathA q' hle'] at h
        exact congrArg Fin.val (small.pathVertex_injective j₁ h)
      · exfalso
        rw [hpathA q hle, hpathB q' hq' hle'] at h
        by_cases hlast : q = small.length j₁
        · rw [PathHelpers.pathVertex_of_last small j₁ _ (by show q ≠ 0; omega)
              (by show q = small.length j₁; omega),
            PathHelpers.pathVertex_of_interior small j₂ _
              (by show q' - small.length j₁ ≠ 0; omega)
              (by show q' - small.length j₁ ≠ small.length j₂; omega)] at h
          simp [SubdivisionGraph.Spec.coreVertex,
            SubdivisionGraph.Spec.interiorVertex] at h
        · rw [PathHelpers.pathVertex_of_interior small j₁ _
              (by show q ≠ 0; omega) (by show q ≠ small.length j₁; omega),
            PathHelpers.pathVertex_of_interior small j₂ _
              (by show q' - small.length j₁ ≠ 0; omega)
              (by show q' - small.length j₁ ≠ small.length j₂; omega)] at h
          simp only [SubdivisionGraph.Spec.interiorVertex, Sum.inr.injEq,
            Sigma.mk.injEq] at h
          exact hjne h.1
      · exfalso
        rw [hpathB q hq hle, hpathA q' hle'] at h
        by_cases hlast : q' = small.length j₁
        · rw [PathHelpers.pathVertex_of_last small j₁ _ (by show q' ≠ 0; omega)
              (by show q' = small.length j₁; omega),
            PathHelpers.pathVertex_of_interior small j₂ _
              (by show q - small.length j₁ ≠ 0; omega)
              (by show q - small.length j₁ ≠ small.length j₂; omega)] at h
          simp [SubdivisionGraph.Spec.coreVertex,
            SubdivisionGraph.Spec.interiorVertex] at h
        · rw [PathHelpers.pathVertex_of_interior small j₁ _
              (by show q' ≠ 0; omega) (by show q' ≠ small.length j₁; omega),
            PathHelpers.pathVertex_of_interior small j₂ _
              (by show q - small.length j₁ ≠ 0; omega)
              (by show q - small.length j₁ ≠ small.length j₂; omega)] at h
          simp only [SubdivisionGraph.Spec.interiorVertex, Sum.inr.injEq,
            Sigma.mk.injEq] at h
          exact hjne h.1.symm
      · rw [hpathB q hq hle, hpathB q' hq' hle'] at h
        have := congrArg Fin.val (small.pathVertex_injective j₂ h)
        show q = q'
        simp only [] at this
        omega

end InteriorShape

/-! ## Fibres -/

namespace ExpansionData

variable {D : ExpansionData n p N Q} {small : Spec n p} {hN : 0 < N}
    {hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e}

theorem owner_of_slotUses (hCond : D.Conditions small.core) {e : Fin Q}
    {j : Fin p} (h : SlotUses (D.kind e) j) : D.owner j = e := by
  rcases h with hk | ⟨j₂, hk⟩ | ⟨j₁, hk⟩
  · exact ((indexed_of_conditions hCond e).1 j hk).1
  · exact ((indexed_of_conditions hCond e).2 j j₂ hk).1
  · exact ((indexed_of_conditions hCond e).2 j₁ j hk).2.2.1

theorem kind_double_ne (hCond : D.Conditions small.core) (e : Fin Q) :
    ∀ j₁ j₂ : Fin p, D.kind e = .double j₁ j₂ → j₁ ≠ j₂ := by
  intro j₁ j₂ hk h
  obtain ⟨_, hs1, _, hs2⟩ := (indexed_of_conditions hCond e).2 j₁ j₂ hk
  rw [h, hs2] at hs1
  exact Bool.noConfusion hs1

/-- Fibres over the image of an interior big vertex are singletons. -/
theorem interior_fibre (hCond : D.Conditions small.core)
    (e : Fin Q) (o : Fin ((D.bigSpec small hN hL).length e - 1))
    (y : (D.bigSpec small hN hL).Vertex)
    (h : vertexMap D small hN hL y
      = vertexMap D small hN hL ((D.bigSpec small hN hL).interiorVertex e o)) :
    y = (D.bigSpec small hN hL).interiorVertex e o := by
  have holt : o.val < kindLength small (D.kind e) - 1 := o.isLt
  have hlenpos := kindLength_pos small (D.kind e)
  have hqlt : o.val + 1 < kindLength small (D.kind e) := by omega
  have hx : vertexMap D small hN hL ((D.bigSpec small hN hL).interiorVertex e o)
      = kindVertex small (D.fib (D.bigCore.tail e)) (D.kind e) (o.val + 1) := rfl
  rw [hx] at h
  rcases kindVertex_interior_cases (D.fib (D.bigCore.tail e)) (D.kind e)
    (Nat.succ_pos _) hqlt with ⟨j, huse, oo, hj⟩ | ⟨j₁, j₂, hk, hmark⟩
  · rw [hj] at h
    cases y with
    | inl v =>
        exfalso
        have h' : small.coreVertex (D.fib v) = small.interiorVertex j oo := h
        simp [SubdivisionGraph.Spec.coreVertex,
          SubdivisionGraph.Spec.interiorVertex] at h'
    | inr yy =>
        obtain ⟨e', o'⟩ := yy
        have holt' : o'.val < kindLength small (D.kind e') - 1 := o'.isLt
        have hlenpos' := kindLength_pos small (D.kind e')
        have hqlt' : o'.val + 1 < kindLength small (D.kind e') := by omega
        have h' : kindVertex small (D.fib (D.bigCore.tail e')) (D.kind e')
            (o'.val + 1) = small.interiorVertex j oo := h
        rcases kindVertex_interior_cases (D.fib (D.bigCore.tail e')) (D.kind e')
          (Nat.succ_pos _) hqlt' with ⟨j', huse', oo', hj'⟩ | ⟨j₁', j₂', hk', hmark'⟩
        · rw [hj'] at h'
          have hjj : j' = j := by
            simp only [SubdivisionGraph.Spec.interiorVertex, Sum.inr.injEq,
              Sigma.mk.injEq] at h'
            exact h'.1
          subst hjj
          have hee : e' = e := by
            rw [← owner_of_slotUses hCond huse', owner_of_slotUses hCond huse]
          subst hee
          have hval : o'.val + 1 = o.val + 1 :=
            kindVertex_interior_injective (D.fib (D.bigCore.tail e')) (D.kind e')
              (kind_double_ne hCond e') (Nat.succ_pos _) hqlt'
              (Nat.succ_pos _) hqlt (by rw [hj', hj]; exact h')
          have hoo : o' = o := Fin.ext (by omega)
          rw [hoo]
          rfl
        · exfalso
          rw [hmark'] at h'
          simp [SubdivisionGraph.Spec.coreVertex,
            SubdivisionGraph.Spec.interiorVertex] at h'
  · rw [hmark] at h
    have hmarker := (marker_of_conditions hCond e) j₁ j₂ hk
    cases y with
    | inl v =>
        exfalso
        have h' : small.coreVertex (D.fib v)
            = small.coreVertex (small.core.head j₁) := h
        have hfv : D.fib v = small.core.head j₁ := by
          simpa [SubdivisionGraph.Spec.coreVertex] using h'
        exact hmarker.1 v hfv
    | inr yy =>
        obtain ⟨e', o'⟩ := yy
        have holt' : o'.val < kindLength small (D.kind e') - 1 := o'.isLt
        have hlenpos' := kindLength_pos small (D.kind e')
        have hqlt' : o'.val + 1 < kindLength small (D.kind e') := by omega
        have h' : kindVertex small (D.fib (D.bigCore.tail e')) (D.kind e')
            (o'.val + 1) = small.coreVertex (small.core.head j₁) := h
        rcases kindVertex_interior_cases (D.fib (D.bigCore.tail e')) (D.kind e')
          (Nat.succ_pos _) hqlt' with ⟨j', huse', oo', hj'⟩ | ⟨j₁', j₂', hk', hmark'⟩
        · exfalso
          rw [hj'] at h'
          simp [SubdivisionGraph.Spec.coreVertex,
            SubdivisionGraph.Spec.interiorVertex] at h'
        · rw [hmark'] at h'
          have hheads : small.core.head j₁' = small.core.head j₁ := by
            simpa [SubdivisionGraph.Spec.coreVertex] using h'
          have hj1 : j₁' = j₁ := hmarker.2 j₁' hheads
          subst hj1
          have hee : e' = e := by
            rw [← owner_of_slotUses hCond (Or.inr (Or.inl ⟨j₂', hk'⟩)),
              owner_of_slotUses hCond (Or.inr (Or.inl ⟨j₂, hk⟩))]
          subst hee
          have hval : o'.val + 1 = o.val + 1 :=
            kindVertex_interior_injective (D.fib (D.bigCore.tail e')) (D.kind e')
              (kind_double_ne hCond e') (Nat.succ_pos _) hqlt'
              (Nat.succ_pos _) hqlt (by rw [hmark', hmark])
          have hoo : o' = o := Fin.ext (by omega)
          rw [hoo]
          rfl

/-- The contraction hits every small vertex. -/
theorem vertexMap_surjective (hCond : D.Conditions small.core) :
    Function.Surjective (vertexMap D small hN hL) := by
  have key : ∀ (j : Fin p) (q : small.PathPosition j),
      ∃ x, vertexMap D small hN hL x = small.pathVertex j q := by
    intro j q
    have hq := q.isLt
    have hcompat := compatible_of_conditions hCond (D.owner j)
    rcases exists_carrier hCond j with ⟨hk, _⟩ | ⟨j₂, hk, _⟩ | ⟨j₁, hk, _⟩
    · have hlen : (D.bigSpec small hN hL).length (D.owner j) = small.length j := by
        show kindLength small (D.kind (D.owner j)) = small.length j
        simp only [hk, kindLength]
      refine ⟨(D.bigSpec small hN hL).pathVertex (D.owner j)
        ⟨q.val, by omega⟩, ?_⟩
      rw [vertexMap_pathVertex hCond]
      show kindVertex small (D.fib (D.bigCore.tail (D.owner j)))
        (D.kind (D.owner j)) q.val = _
      rw [hk]
      exact PathHelpers.pathVertex_congr small j _ _ (by
        show min q.val (small.length j) = q.val
        omega)
    · have hlen : (D.bigSpec small hN hL).length (D.owner j)
          = small.length j + small.length j₂ := by
        show kindLength small (D.kind (D.owner j)) = _
        simp only [hk, kindLength]
      have hj₂ := small.length_pos j₂
      refine ⟨(D.bigSpec small hN hL).pathVertex (D.owner j)
        ⟨q.val, by omega⟩, ?_⟩
      rw [vertexMap_pathVertex hCond]
      show kindVertex small (D.fib (D.bigCore.tail (D.owner j)))
        (D.kind (D.owner j)) q.val = _
      rw [hk, kindVertex_double_le j j₂ _ (by omega)]
      exact PathHelpers.pathVertex_congr small j _ _ (by
        show min q.val (small.length j) = q.val
        omega)
    · have hlen : (D.bigSpec small hN hL).length (D.owner j)
          = small.length j₁ + small.length j := by
        show kindLength small (D.kind (D.owner j)) = _
        simp only [hk, kindLength]
      have hMid : small.core.head j₁ = small.core.tail j :=
        (hcompat.2.2 j₁ j hk).2.1
      refine ⟨(D.bigSpec small hN hL).pathVertex (D.owner j)
        ⟨small.length j₁ + q.val, by omega⟩, ?_⟩
      rw [vertexMap_pathVertex hCond]
      show kindVertex small (D.fib (D.bigCore.tail (D.owner j)))
        (D.kind (D.owner j)) (small.length j₁ + q.val) = _
      rw [hk, kindVertex_double_shift _ hMid]
      exact PathHelpers.pathVertex_congr small j _ _ (by
        show min q.val (small.length j) = q.val
        omega)
  intro w
  cases w with
  | inl v =>
      obtain ⟨j, hj⟩ := incident_of_conditions hCond v
      rcases hj with h | h
      · obtain ⟨x, hx⟩ := key j ⟨0, by omega⟩
        refine ⟨x, ?_⟩
        rw [hx, PathHelpers.pathVertex_of_zero small j _ rfl, h]
        rfl
      · have hpos := small.length_pos j
        obtain ⟨x, hx⟩ := key j ⟨small.length j, by omega⟩
        refine ⟨x, ?_⟩
        rw [hx, PathHelpers.pathVertex_of_last small j _
          (by show small.length j ≠ 0; omega) (by show small.length j = small.length j; rfl), h]
        rfl
  | inr yy =>
      obtain ⟨j, oo⟩ := yy
      have hoo := oo.isLt
      have hpos := small.length_pos j
      obtain ⟨x, hx⟩ := key j ⟨oo.val + 1, by omega⟩
      refine ⟨x, ?_⟩
      rw [hx, PathHelpers.pathVertex_of_interior small j _
        (by show oo.val + 1 ≠ 0; omega)
        (by show oo.val + 1 ≠ small.length j; omega)]
      exact congrArg (small.interiorVertex j) (Fin.ext (by simp))

end ExpansionData

/-! ## The topological contraction certificate -/

namespace ExpansionData

variable (D : ExpansionData n p N Q) (small : Spec n p) (hN : 0 < N)
    (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)

/-- The contraction certificate attached to an expansion datum. -/
def certificate :
    GraphContractionCertificate (D.bigSpec small hN hL).graph small.graph where
  vertexMap := vertexMap D small hN hL

variable {D small hN hL}

theorem certificate_valid (hCond : D.Conditions small.core) :
    (certificate D small hN hL).Valid :=
  ⟨vertexMap_surjective hCond, fun a b hab => valid_multiplicity hCond a b hab⟩

theorem certificate_connectedFibres (hCond : D.Conditions small.core) :
    (certificate D small hN hL).ConnectedFibres := by
  classical
  intro target S hSplit
  obtain ⟨inside, outside, hInS, hOutS, hIn, hOut⟩ := hSplit
  have hne : inside ≠ outside := by
    intro hh
    exact hOutS (hh ▸ hInS)
  have hmapIn : vertexMap D small hN hL inside = target := hIn
  have hmapOut : vertexMap D small hN hL outside = target := hOut
  have hcore : ∀ z z' : (D.bigSpec small hN hL).Vertex,
      vertexMap D small hN hL z = target →
      vertexMap D small hN hL z' = target → z ≠ z' → ∃ v, z = Sum.inl v := by
    intro z z' hz hz' hzz
    cases z with
    | inl v => exact ⟨v, rfl⟩
    | inr yy =>
        exfalso
        obtain ⟨e, o⟩ := yy
        exact hzz (interior_fibre hCond e o z' (by rw [hz']; exact hz.symm)).symm
  obtain ⟨v, rfl⟩ := hcore inside outside hmapIn hmapOut hne
  obtain ⟨w, rfl⟩ := hcore outside (Sum.inl v) hmapOut hmapIn (Ne.symm hne)
  have hmapIn' : small.coreVertex (D.fib v) = target := hmapIn
  have hmapOut' : small.coreVertex (D.fib w) = target := hmapOut
  have hfvw : D.fib v = D.fib w :=
    Sum.inl.inj (hmapIn'.trans hmapOut'.symm)
  set T : Finset (Fin N) :=
    Finset.univ.filter
      (fun u => (Sum.inl u : (D.bigSpec small hN hL).Vertex) ∈ S) with hT
  have hvT : v ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ v, hInS⟩
  have hwT : w ∉ T := fun hh => hOutS (Finset.mem_filter.mp hh).2
  obtain ⟨e, hkc, hfe, hcross⟩ :=
    fibre_of_conditions hCond (D.fib v) T ⟨v, hvT, rfl⟩ ⟨w, hwT, hfvw.symm⟩
  have hlen1 : (D.bigSpec small hN hL).length e = 1 := by
    show kindLength small (D.kind e) = 1
    simp only [hkc, kindLength]
  have hL0 : (D.bigSpec small hN hL).stepLeft e ⟨0, by omega⟩
      = (D.bigSpec small hN hL).coreVertex (D.bigCore.tail e) := by
    unfold SubdivisionGraph.Spec.stepLeft
    rw [dite_eq_left rfl]
    rfl
  have hR0 : (D.bigSpec small hN hL).stepRight e ⟨0, by omega⟩
      = (D.bigSpec small hN hL).coreVertex (D.bigCore.head e) := by
    unfold SubdivisionGraph.Spec.stepRight
    rw [dite_eq_left (by omega : (0 : ℕ) + 1 = (D.bigSpec small hN hL).length e)]
    rfl
  have hedge : 0 < numEdges (D.bigSpec small hN hL).graph
      (Sum.inl (D.bigCore.tail e)) (Sum.inl (D.bigCore.head e)) := by
    have hstep := (D.bigSpec small hN hL).unitStep_num_edges_pos e ⟨0, by omega⟩
    rw [hL0, hR0] at hstep
    exact hstep
  have htargetTail : vertexMap D small hN hL (Sum.inl (D.bigCore.tail e))
      = target := by
    show small.coreVertex (D.fib (D.bigCore.tail e)) = target
    rw [hfe]
    exact hmapIn'
  have htargetHead : vertexMap D small hN hL (Sum.inl (D.bigCore.head e))
      = target := by
    show small.coreVertex (D.fib (D.bigCore.head e)) = target
    rw [← (compatible_of_conditions hCond e).1 hkc, hfe]
    exact hmapIn'
  rcases hcross with ⟨htI, hhO⟩ | ⟨hhI, htO⟩
  · refine ⟨Sum.inl (D.bigCore.tail e), ?_, Sum.inl (D.bigCore.head e), ?_,
      htargetTail, htargetHead, hedge⟩
    · exact (Finset.mem_filter.mp htI).2
    · exact fun hh => hhO (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
  · refine ⟨Sum.inl (D.bigCore.head e), ?_, Sum.inl (D.bigCore.tail e), ?_,
      htargetHead, htargetTail, ?_⟩
    · exact (Finset.mem_filter.mp hhI).2
    · exact fun hh => htO (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
    · rw [num_edges_symmetric]
      exact hedge

theorem certificate_topologicalValid (hCond : D.Conditions small.core) :
    (certificate D small hN hL).TopologicalValid :=
  ⟨certificate_valid hCond, certificate_connectedFibres hCond⟩

end ExpansionData

end Utilities.Subdivision.CoreExpansion
