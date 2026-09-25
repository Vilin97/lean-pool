/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.ThroughValue

/-!
# Subset splitting over disjoint unions

Edge subsets of a disjoint union split componentwise: the
left/right parts, their join, the round trips, and the transport
of pairing-closure, Eulerian-ness, and boundary-state matching —
the first layer of the multiplicativity of the corrected
constrained value over `disjUnion`.
-/

@[expose] public section

namespace RS

variable {α β : Type} {W₁ : Fragment α} {W₂ : Fragment β}



/-! ## The parts and the join -/

/-- The left part of a subset of the disjoint union. -/
noncomputable def leftPart
    (s : Finset ((W₁.disjUnion W₂).Flag)) : Finset W₁.Flag :=
  Finset.toLeft (α := W₁.Flag) (β := W₂.Flag) s

/-- The right part of a subset of the disjoint union. -/
noncomputable def rightPart
    (s : Finset ((W₁.disjUnion W₂).Flag)) : Finset W₂.Flag :=
  Finset.toRight (α := W₁.Flag) (β := W₂.Flag) s

/-- The join of componentwise subsets. -/
noncomputable def joinParts (s₁ : Finset W₁.Flag)
    (s₂ : Finset W₂.Flag) : Finset ((W₁.disjUnion W₂).Flag) :=
  Finset.disjSum s₁ s₂

/-- Membership in the left part of a flag set. -/
@[simp] theorem mem_leftPart {s : Finset ((W₁.disjUnion W₂).Flag)}
    {f : W₁.Flag} : f ∈ leftPart s ↔ Sum.inl f ∈ s :=
  Finset.mem_toLeft

/-- Membership in the right part. -/
@[simp] theorem mem_rightPart {s : Finset ((W₁.disjUnion W₂).Flag)}
    {f : W₂.Flag} : f ∈ rightPart s ↔ Sum.inr f ∈ s :=
  Finset.mem_toRight

/-- A left flag is in a join exactly when it is in the left
summand. -/
@[simp] theorem inl_mem_joinParts {s₁ : Finset W₁.Flag}
    {s₂ : Finset W₂.Flag} {f : W₁.Flag} :
    (Sum.inl f : (W₁.disjUnion W₂).Flag) ∈ joinParts s₁ s₂ ↔
      f ∈ s₁ :=
  Finset.inl_mem_disjSum

/-- The right analogue. -/
@[simp] theorem inr_mem_joinParts {s₁ : Finset W₁.Flag}
    {s₂ : Finset W₂.Flag} {f : W₂.Flag} :
    (Sum.inr f : (W₁.disjUnion W₂).Flag) ∈ joinParts s₁ s₂ ↔
      f ∈ s₂ :=
  Finset.inr_mem_disjSum

/-- The left part of a join is what was joined on the left. -/
theorem leftPart_joinParts (s₁ : Finset W₁.Flag)
    (s₂ : Finset W₂.Flag) :
    leftPart (W₁ := W₁) (W₂ := W₂) (joinParts s₁ s₂) = s₁ :=
  Finset.toLeft_disjSum

/-- And likewise on the right. -/
theorem rightPart_joinParts (s₁ : Finset W₁.Flag)
    (s₂ : Finset W₂.Flag) :
    rightPart (W₁ := W₁) (W₂ := W₂) (joinParts s₁ s₂) = s₂ :=
  Finset.toRight_disjSum

/-- Joining a set's two parts recovers it: the split is a
bijection. -/
theorem joinParts_parts (s : Finset ((W₁.disjUnion W₂).Flag)) :
    joinParts (leftPart s) (rightPart s) = s :=
  Finset.toLeft_disjSum_toRight

/-! ## Closure transport -/

/-- Edge-closure is componentwise, no edge crossing between the
components. -/
theorem pairing_closed_iff_parts
    (s : Finset ((W₁.disjUnion W₂).Flag)) :
    (∀ f ∈ s, (W₁.disjUnion W₂).pairing f ∈ s) ↔
      ((∀ f ∈ leftPart s, W₁.pairing f ∈ leftPart s) ∧
        (∀ f ∈ rightPart s, W₂.pairing f ∈ rightPart s)) := by
  constructor
  · intro hc
    constructor
    · intro f hf
      exact mem_leftPart.mpr (hc _ (mem_leftPart.mp hf))
    · intro f hf
      exact mem_rightPart.mpr (hc _ (mem_rightPart.mp hf))
  · rintro ⟨h₁, h₂⟩ f hf
    cases f with
    | inl g =>
      have := h₁ g (mem_leftPart.mpr hf)
      exact mem_leftPart.mp this
    | inr g =>
      have := h₂ g (mem_rightPart.mpr hf)
      exact mem_rightPart.mp this

/-! ## Attachment over the union -/

/-- A left flag sits at a left vertex exactly as in the left
fragment. -/
private theorem attach_inl_eq_inl {f : W₁.Flag} {v : W₁.Vertex} :
    (W₁.disjUnion W₂).attach (Sum.inl f) = Sum.inl (Sum.inl v) ↔
      W₁.attach f = Sum.inl v := by
  change (W₁.attach f).map Sum.inl Sum.inl = Sum.inl (Sum.inl v) ↔
    W₁.attach f = Sum.inl v
  constructor
  · intro h
    rcases hA : W₁.attach f with w | ℓ <;> rw [hA] at h
    · simp only [Sum.map_inl, Sum.inl.injEq] at h
      rw [h]
    · simp only [Sum.map_inr] at h
      exact absurd h (by simp)
  · intro h
    simp [h]

/-- A right flag sits at a right vertex exactly as in the right
fragment. -/
private theorem attach_inr_eq_inr {f : W₂.Flag} {v : W₂.Vertex} :
    (W₁.disjUnion W₂).attach (Sum.inr f) = Sum.inl (Sum.inr v) ↔
      W₂.attach f = Sum.inl v := by
  change (W₂.attach f).map Sum.inr Sum.inr = Sum.inl (Sum.inr v) ↔
    W₂.attach f = Sum.inl v
  constructor
  · intro h
    rcases hA : W₂.attach f with w | ℓ <;> rw [hA] at h
    · simp only [Sum.map_inl, Sum.inl.injEq, Sum.inr.injEq] at h
      rw [h]
    · simp only [Sum.map_inr] at h
      exact absurd h (by simp)
  · intro h
    simp [h]

/-- A right flag never sits at a left vertex. -/
private theorem attach_inr_ne_inl {f : W₂.Flag} {v : W₁.Vertex} :
    (W₁.disjUnion W₂).attach (Sum.inr f) ≠ Sum.inl (Sum.inl v) := by
  change (W₂.attach f).map Sum.inr Sum.inr ≠ Sum.inl (Sum.inl v)
  rcases W₂.attach f with w | ℓ <;> simp

/-- A left flag never sits at a right vertex. -/
private theorem attach_inl_ne_inr {f : W₁.Flag} {v : W₂.Vertex} :
    (W₁.disjUnion W₂).attach (Sum.inl f) ≠ Sum.inl (Sum.inr v) := by
  change (W₁.attach f).map Sum.inl Sum.inl ≠ Sum.inl (Sum.inr v)
  rcases W₁.attach f with w | ℓ <;> simp

/-! ## Filtering a disjoint sum -/

private theorem filter_disjSum_eq {γ δ : Type} (L : Finset γ)
    (R : Finset δ) (P : γ ⊕ δ → Prop) [DecidablePred P] :
    (L.disjSum R).filter P =
      (L.filter fun x => P (Sum.inl x)).disjSum
        (R.filter fun y => P (Sum.inr y)) := by
  ext x
  cases x <;> simp

/-- The card of a filter over a disjoint sum whose predicate holds
only on the left, with explicit decidability arguments so that the
instances are picked up by unification. -/
private theorem card_filter_disjSum_inl {γ δ : Type} (L : Finset γ)
    (R : Finset δ) (P : γ ⊕ δ → Prop) (instP : DecidablePred P)
    (Q : γ → Prop) (instQ : DecidablePred Q)
    (hQ : ∀ x, P (Sum.inl x) ↔ Q x) (hR : ∀ y, ¬ P (Sum.inr y)) :
    (@Finset.filter _ P instP (L.disjSum R)).card =
      (@Finset.filter _ Q instQ L).card := by
  rw [Finset.filter_congr_decidable (L.disjSum R) P instP,
    Finset.filter_congr_decidable L Q instQ,
    filter_disjSum_eq L R P, Finset.filter_congr (fun x _ => hQ x),
    Finset.filter_false_of_mem (fun y _ => hR y), Finset.card_disjSum,
    Finset.card_empty, Nat.add_zero]

/-- The card of a filter over a disjoint sum whose predicate holds
only on the right. -/
private theorem card_filter_disjSum_inr {γ δ : Type} (L : Finset γ)
    (R : Finset δ) (P : γ ⊕ δ → Prop) (instP : DecidablePred P)
    (Q : δ → Prop) (instQ : DecidablePred Q)
    (hL : ∀ x, ¬ P (Sum.inl x)) (hQ : ∀ y, P (Sum.inr y) ↔ Q y) :
    (@Finset.filter _ P instP (L.disjSum R)).card =
      (@Finset.filter _ Q instQ R).card := by
  rw [Finset.filter_congr_decidable (L.disjSum R) P instP,
    Finset.filter_congr_decidable R Q instQ,
    filter_disjSum_eq L R P, Finset.filter_congr (fun y _ => hQ y),
    Finset.filter_false_of_mem (fun x _ => hL x), Finset.card_disjSum,
    Finset.card_empty, Nat.zero_add]

/-! ## Degree transport -/

/-- The degree at a left vertex is computed in the left part. -/
theorem deg_disjUnion_inl
    (s : Finset ((W₁.disjUnion W₂).Flag))
    (hc : ∀ f ∈ s, (W₁.disjUnion W₂).pairing f ∈ s)
    (h₁ : ∀ f ∈ leftPart s, W₁.pairing f ∈ leftPart s)
    (v : W₁.Vertex) :
    (EdgeSubset.mk s hc).deg (Sum.inl v) =
      (EdgeSubset.mk (leftPart s) h₁).deg v := by
  unfold EdgeSubset.deg
  rw [show (EdgeSubset.mk s hc).flags =
    joinParts (leftPart s) (rightPart s) from (joinParts_parts s).symm]
  unfold joinParts
  exact card_filter_disjSum_inl (leftPart s) (rightPart s) _ _ _ _
    (fun x => attach_inl_eq_inl) (fun y => attach_inr_ne_inl)

/-- The degree at a right vertex is computed in the right part. -/
theorem deg_disjUnion_inr
    (s : Finset ((W₁.disjUnion W₂).Flag))
    (hc : ∀ f ∈ s, (W₁.disjUnion W₂).pairing f ∈ s)
    (h₂ : ∀ f ∈ rightPart s, W₂.pairing f ∈ rightPart s)
    (v : W₂.Vertex) :
    (EdgeSubset.mk s hc).deg (Sum.inr v) =
      (EdgeSubset.mk (rightPart s) h₂).deg v := by
  unfold EdgeSubset.deg
  rw [show (EdgeSubset.mk s hc).flags =
    joinParts (leftPart s) (rightPart s) from (joinParts_parts s).symm]
  unfold joinParts
  exact card_filter_disjSum_inr (leftPart s) (rightPart s) _ _ _ _
    (fun x => attach_inl_ne_inr) (fun y => attach_inr_eq_inr)

/-! ## Eulerian transport -/

/-- Being Eulerian is componentwise. -/
theorem eulerian_iff_parts
    (s : Finset ((W₁.disjUnion W₂).Flag))
    (hc : ∀ f ∈ s, (W₁.disjUnion W₂).pairing f ∈ s)
    (h₁ : ∀ f ∈ leftPart s, W₁.pairing f ∈ leftPart s)
    (h₂ : ∀ f ∈ rightPart s, W₂.pairing f ∈ rightPart s) :
    (EdgeSubset.mk s hc).Eulerian ↔
      ((EdgeSubset.mk (leftPart s) h₁).Eulerian ∧
        (EdgeSubset.mk (rightPart s) h₂).Eulerian) := by
  unfold EdgeSubset.Eulerian
  constructor
  · intro hE
    constructor
    · intro v
      have h := hE (Sum.inl v)
      rwa [deg_disjUnion_inl s hc h₁ v] at h
    · intro v
      have h := hE (Sum.inr v)
      rwa [deg_disjUnion_inr s hc h₂ v] at h
  · rintro ⟨hE₁, hE₂⟩ v
    cases v with
    | inl v =>
      have h := hE₁ v
      rwa [← deg_disjUnion_inl s hc h₁ v] at h
    | inr v =>
      have h := hE₂ v
      rwa [← deg_disjUnion_inr s hc h₂ v] at h

end RS
