/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.FibreCard

/-!
# Stabiliser count for colourings

For `f : Fin n → Fin N`, the number of permutations `π` with `f ∘ π = f`
equals `∏ j, (fibreCard f j)!`.
-/

@[expose] public section

namespace RS

open Finset Equiv Fintype

variable {n N : ℕ}

/-! ### Simp helper for the sigma-fibre equivalence -/

private lemma sigmaFiberEquiv_symm_val {α : Type*} {β : Type*} (f : α → β) (x :
  α) :
    (sigmaFiberEquiv f).symm x = ⟨f x, x, rfl⟩ := rfl

/-! ### Forward and backward maps -/

/-- Forward: a fixing permutation restricts to each fibre. -/
private def toFibrePerms (f : Fin n → Fin N) (π : Perm (Fin n))
    (hπ : f ∘ π = f) (j : Fin N) : Perm {i : Fin n // f i = j} :=
  π.subtypePerm fun i => by
    have key : f (π i) = f i := congr_fun hπ i
    exact ⟨fun h => key.symm.trans h, fun h => key.trans h⟩

/-- Backward: fibre permutations assemble into a global fixing permutation. -/
def ofFibrePerms (f : Fin n → Fin N)
    (σ : ∀ j : Fin N, Perm {i : Fin n // f i = j}) : Perm (Fin n) :=
  (sigmaFiberEquiv f).permCongr (Perm.sigmaCongrRight σ)

/-- Permuting within each fibre fixes the colouring. -/
theorem ofFibrePerms_fixes (f : Fin n → Fin N)
    (σ : ∀ j, Perm {i : Fin n // f i = j}) : f ∘ ofFibrePerms f σ = f := by
  funext x
  simp only [Function.comp_apply, ofFibrePerms, permCongr_apply,
    sigmaFiberEquiv_symm_val, Equiv.sigmaCongrRight_apply,
      sigmaFiberEquiv_apply]
  exact (σ (f x) ⟨x, rfl⟩).property

/-! ### The fixing-perms–fibre-perms equivalence -/

/-- The bijection between fixing permutations and families of fibre
permutations. -/
def fixingEquiv (f : Fin n → Fin N) :
    {π : Perm (Fin n) // f ∘ π = f} ≃
    (∀ j : Fin N, Perm {i : Fin n // f i = j}) where
  toFun πh := toFibrePerms f πh.1 πh.2
  invFun σ := ⟨ofFibrePerms f σ, ofFibrePerms_fixes f σ⟩
  left_inv := by
    rintro ⟨π, hπ⟩
    simp only [Subtype.mk.injEq]
    refine Equiv.ext fun i => ?_
    simp only [ofFibrePerms, permCongr_apply, sigmaFiberEquiv_symm_val,
      Equiv.sigmaCongrRight_apply, toFibrePerms, Perm.subtypePerm_apply,
      sigmaFiberEquiv_apply]
  right_inv := by
    intro σ; funext j
    refine Equiv.ext fun ⟨i, hi⟩ => Subtype.ext ?_
    simp only [toFibrePerms, Perm.subtypePerm_apply, Subtype.coe_mk,
      ofFibrePerms, permCongr_apply, sigmaFiberEquiv_symm_val,
      Equiv.sigmaCongrRight_apply, sigmaFiberEquiv_apply]
    subst hi; rfl

/-- `ofFibrePerms` unfolds to the conjugated sigma-congruence. -/
theorem ofFibrePerms_def (f : Fin n → Fin N)
    (σ : ∀ j : Fin N, Perm {i : Fin n // f i = j}) :
    ofFibrePerms f σ =
      (sigmaFiberEquiv f).permCongr (Perm.sigmaCongrRight σ) :=
  rfl

/-- The inverse of the fixing equivalence is `ofFibrePerms`. -/
theorem fixingEquiv_symm_apply (f : Fin n → Fin N)
    (σ : ∀ j : Fin N, Perm {i : Fin n // f i = j}) :
    ((fixingEquiv f).symm σ : {π : Perm (Fin n) // f ∘ π = f}).1 =
      ofFibrePerms f σ :=
  rfl

/-! ### The cardinality step -/

/-- Fibre card equals the Fintype card of the fibre subtype. -/
lemma fibreCard_eq_card (f : Fin n → Fin N) (j : Fin N) :
    fibreCard f j = Fintype.card {i : Fin n // f i = j} := by
  classical
  rw [fibreCard]
  exact (Fintype.card_of_subtype _ fun x => by simp [mem_filter]).symm

/-- **The stabiliser count**: the permutations fixing a colouring
are exactly those, so there are the product of the fibre
factorials. -/
theorem card_fixing_perms {n N : ℕ} (f : Fin n → Fin N) :
    (Finset.univ.filter
        (fun π : Equiv.Perm (Fin n) => f ∘ π = f)).card =
      ∏ j : Fin N, (fibreCard f j).factorial := by
  classical
  rw [show (univ.filter _).card = Fintype.card {π : Perm (Fin n) // f ∘ π = f}
    from (Fintype.card_of_subtype _ fun x => by simp [mem_filter]).symm,
    Fintype.card_congr (fixingEquiv f), Fintype.card_pi]
  congr 1; ext j
  rw [Fintype.card_perm, fibreCard_eq_card]

end RS
