/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.CharClass

/-!
# The permutation module on a colour class

The symmetric group `Equiv.Perm (Fin n)` acts on the colour class
`{g : Fin n → Fin N // ∀ j, fibreCard g j = α j}` by precomposition
with the inverse.  The resulting `ofMulAction` representation has
character equal to `colourChar α`.
-/

namespace RS

open Finset Equiv MonoidAlgebra



/-- The colour class: colourings with prescribed fibre sizes. -/
def colourClass (n : ℕ) {N : ℕ} (α : Fin N → ℕ) : Type :=
  {g : Fin n → Fin N // ∀ j, fibreCard g j = α j}

/-- A colour class is finite. -/
noncomputable instance colourClass.fintype (n : ℕ) {N : ℕ}
    (α : Fin N → ℕ) : Fintype (colourClass n α) :=
  Subtype.fintype _

/-- And its members can be compared. -/
noncomputable instance colourClass.decidableEq (n : ℕ) {N : ℕ}
    (α : Fin N → ℕ) : DecidableEq (colourClass n α) :=
  Classical.decEq _

/-- The symmetric group acts on the colour class by precomposition
with the inverse permutation. -/
instance colourClass.mulAction {n N : ℕ} (α : Fin N → ℕ) :
    MulAction (Equiv.Perm (Fin n)) (colourClass n α) where
  smul π g := ⟨g.1 ∘ ⇑π⁻¹, fun j => by
    rw [fibreCard_comp_perm]; exact g.2 j⟩
  one_smul g := by
    apply Subtype.ext
    change g.1 ∘ ⇑(1 : Equiv.Perm (Fin n))⁻¹ = g.1
    simp
  mul_smul π ρ g := by
    apply Subtype.ext
    change g.1 ∘ ⇑(π * ρ)⁻¹ = (⟨(g.1 ∘ ⇑ρ⁻¹) ∘ ⇑π⁻¹, _⟩ : colourClass n α).1
    rw [mul_inv_rev]
    rfl

/-- The permutation representation on the colour class. -/
noncomputable def colourRep {n N : ℕ} (α : Fin N → ℕ) :
    Representation ℂ (Equiv.Perm (Fin n)) ℂ[colourClass n α] :=
  Representation.ofMulAction ℂ _ _

private theorem fixed_iff_comp_eq {n N : ℕ} (α : Fin N → ℕ)
    (π : Equiv.Perm (Fin n)) (g : colourClass n α) :
    π • g = g ↔ g.1 ∘ ⇑π = g.1 := by
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    -- hv : g.1 ∘ π⁻¹ = g.1
    funext i
    have := congrFun hv (π i)
    change g.1 (π⁻¹ (π i)) = g.1 (π i) at this
    simp at this
    exact this.symm
  · intro h
    apply Subtype.ext
    -- need: g.1 ∘ π⁻¹ = g.1
    funext i
    have := congrFun h (π⁻¹ i)
    change g.1 (π (π⁻¹ i)) = g.1 (π⁻¹ i) at this
    simp at this
    exact this.symm

private theorem fixedPoints_card_eq_colourChar {n N : ℕ}
    (α : Fin N → ℕ) (π : Equiv.Perm (Fin n)) :
    (Finset.univ.filter
      (fun g : colourClass n α => π • g = g)).card =
    colourChar α π := by
  rw [colourChar]
  -- Both sides are cardinalities of filters on Finset.univ
  -- LHS: filter over colourClass n α
  -- RHS: filter over Fin n → Fin N
  -- We show they are equal by an explicit bijection
  apply Finset.card_bij (fun (g : colourClass n α) _ => g.1)
  · -- Maps to: g in LHS filter implies g.1 in RHS filter
    intro g hg
    rw [Finset.mem_filter] at hg ⊢
    exact ⟨Finset.mem_univ _, ⟨g.2, (fixed_iff_comp_eq α π g).mp hg.2⟩⟩
  · -- Injective
    intro g₁ _ g₂ _ heq
    exact Subtype.ext heq
  · -- Surjective
    intro f hf
    rw [Finset.mem_filter] at hf
    obtain ⟨_, hcls, hfix⟩ := hf
    exact ⟨⟨f, hcls⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (fixed_iff_comp_eq α π ⟨f, hcls⟩).mpr hfix⟩, rfl⟩

/-- The character of the colour-class permutation representation
equals the combinatorial colour character. -/
theorem colourRep_character {n N : ℕ} (α : Fin N → ℕ)
    (π : Equiv.Perm (Fin n)) :
    (colourRep α).character π = (colourChar α π : ℂ) := by
  -- character = trace of the linear map
  change LinearMap.trace ℂ _ ((colourRep α) π) = _
  -- express trace via MonoidAlgebra basis
  set b := MonoidAlgebra.basis (colourClass n α) ℂ with hb_def
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  -- Matrix.trace = ∑ g, diagonal entry
  change ∑ g : colourClass n α,
    LinearMap.toMatrix b b ((colourRep α) π) g g = _
  -- compute each diagonal entry
  have hdiag : ∀ g : colourClass n α,
      LinearMap.toMatrix b b ((colourRep α) π) g g =
        if π • g = g then 1 else 0 := by
    intro g
    rw [LinearMap.toMatrix_apply]
    -- b g = MonoidAlgebra.single g 1
    change (b.repr ((colourRep α) π (MonoidAlgebra.single g 1))) g =
      if π • g = g then 1 else 0
    -- (colourRep α) π acts by ofMulAction
    rw [show (colourRep α) π (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single (π • g) 1 from
      Representation.ofMulAction_single π g 1]
    -- b.repr = coeffLinearEquiv
    change ((coeffLinearEquiv ℂ)
      (MonoidAlgebra.single (π • g) (1 : ℂ))) g =
        if π • g = g then 1 else 0
    rw [coeffLinearEquiv_apply]
    simp [ Finsupp.single_apply, eq_comm]
  -- rewrite using the diagonal formula
  rw [Finset.sum_congr rfl (fun g _ => hdiag g)]
  -- ∑ g, if π • g = g then 1 else 0 = card of fixed points
  have hsum : ∑ g : colourClass n α,
      (if π • g = g then (1 : ℂ) else 0) =
      ((Finset.univ.filter
        (fun g : colourClass n α => π • g = g)).card : ℂ) := by
    rw [← Finset.sum_filter]
    simp
  rw [hsum, fixedPoints_card_eq_colourChar]

/-- The number of orbits equals `cycleType.card + (n - cycleType.sum)`. -/
theorem card_orbitSpace (n : ℕ) (π : Equiv.Perm (Fin n)) :
    Fintype.card (OrbitSpace π) =
      π.cycleType.card + (n - π.cycleType.sum) := by
  have h := orbCard_multiset π
  have h1 : Fintype.card (OrbitSpace π) =
    ((Finset.univ : Finset (OrbitSpace π)).val.map
      (orbCard π)).card := by
    rw [Multiset.card_map]; rfl
  rw [h1, h, Multiset.card_add, Multiset.card_replicate]

end RS
