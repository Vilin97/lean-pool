/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# The cycle type of a fibrewise permutation

The cycle type of `Equiv.Perm.sigmaCongrRight` is the sum of the
fibres' cycle types: a fibrewise permutation moves each fibre inside
itself, so its orbits are the fibres' orbits.
-/

@[expose] public section

namespace RS

open Equiv Equiv.Perm Finset

variable {I : Type*}

/-- The equivalence between `β i` and `{x : Σ j, β j // x.1 = i}`. -/
private def eComp {β : I → Type*}
    (i : I) : β i ≃ {x : Σ j, β j // x.1 = i} where
  toFun b := ⟨⟨i, b⟩, rfl⟩
  invFun x := cast (congrArg β x.2) x.1.2
  left_inv b := by simp
  right_inv := by
    rintro ⟨⟨j, b⟩, rfl : j = i⟩
    simp

private theorem mulSingle_perm_eq_one [DecidableEq I] {β : I → Type*}
    {σ : ∀ i, Perm (β i)} {i k : I} (hki : k ≠
  i) :
    @Pi.mulSingle I (fun j => Perm (β j)) _ _ i (σ i) k = 1 :=
  @Pi.mulSingle_eq_of_ne I (fun j => Perm (β j)) _ _ i k hki (σ i)

/-- `sigmaCongrRight (Pi.mulSingle i (σ i))` equals
`(σ i).extendDomain (eComp i)`. -/
private theorem sigmaCongrRight_mulSingle_eq_extendDomain
    [DecidableEq I] {β : I → Type*}
    (σ : ∀ i, Perm (β i)) (i : I) :
    Perm.sigmaCongrRight (Pi.mulSingle i (σ i)) = (σ i).extendDomain (eComp i)
      := by
  apply Equiv.ext
  intro ⟨j, b⟩
  by_cases hij : j = i
  · subst hij
    simp only [Equiv.sigmaCongrRight_apply, Pi.mulSingle_eq_same]
    symm
    change ((σ j).extendDomain (eComp j (β := β))) ⟨j, b⟩ = ⟨j, (σ j) b⟩
    have : ⟨j, b⟩ = (↑((eComp j (β := β)) b) : Σ k, β k) := rfl
    conv_lhs => rw [this, Perm.extendDomain_apply_image]
    simp [eComp]
  · -- Both sides fix ⟨j, b⟩ since j ≠ i
    have lhs : Perm.sigmaCongrRight (Pi.mulSingle i (σ i)) ⟨j, b⟩ = ⟨j, b⟩ := by
      simp only [Equiv.sigmaCongrRight_apply]
      congr 1
      rw [mulSingle_perm_eq_one hij, Perm.one_apply]
    have rhs : ((σ i).extendDomain (eComp i (β := β))) ⟨j, b⟩ = ⟨j, b⟩ :=
      Perm.extendDomain_apply_not_subtype _ _ hij
    rw [lhs, rhs]

/-- Permutations obtained from `Pi.mulSingle` at different indices are
disjoint. -/
private theorem disjoint_sigmaCongrRight_mulSingle
    [DecidableEq I] {β : I → Type*}
    (σ : ∀ i, Perm (β i)) {i j : I} (hij : i ≠ j) :
    Perm.Disjoint (Perm.sigmaCongrRight (Pi.mulSingle i (σ i)))
      (Perm.sigmaCongrRight (Pi.mulSingle j (σ j))) := by
  intro ⟨k, b⟩
  simp only [Equiv.sigmaCongrRight_apply]
  by_cases hki : k = i <;> by_cases hkj : k = j
  · exact absurd (hki.symm.trans hkj) hij
  · right; congr 1; rw [mulSingle_perm_eq_one hkj, Perm.one_apply]
  · left; congr 1; rw [mulSingle_perm_eq_one hki, Perm.one_apply]
  · left; congr 1; rw [mulSingle_perm_eq_one hki, Perm.one_apply]

/-- `sigmaCongrRight σ` decomposes as a `noncommProd` over indices. -/
private theorem sigmaCongrRight_eq_noncommProd
    [DecidableEq I] [Fintype I] {β : I → Type*}
    (σ : ∀ i, Perm (β i)) :
    Perm.sigmaCongrRight σ =
      univ.noncommProd (fun i => Perm.sigmaCongrRight (Pi.mulSingle i (σ i)))
        (fun _i _ _j _ hij =>
          (disjoint_sigmaCongrRight_mulSingle σ hij).commute) := by
  have h := Finset.noncommProd_mulSingle σ
  apply_fun (sigmaCongrRightHom β) at h
  erw [Finset.map_noncommProd] at h
  exact h.symm

/-- A fibrewise permutation's cycle type is the sum of the fibres':
no cycle crosses between fibres. -/
theorem cycleType_sigmaCongrRight {I : Type*} [DecidableEq I] [Fintype I]
    {β : I → Type*} [∀ i, DecidableEq (β i)] [∀ i, Fintype (β i)]
    (σ : ∀ i, Equiv.Perm (β i)) :
    (Equiv.Perm.sigmaCongrRight σ).cycleType = ∑ i, (σ i).cycleType := by
  rw [sigmaCongrRight_eq_noncommProd σ]
  rw [Equiv.Perm.Disjoint.cycleType_noncommProd
    (fun _i _ _j _ hij => disjoint_sigmaCongrRight_mulSingle σ hij)]
  congr 1
  ext i
  rw [sigmaCongrRight_mulSingle_eq_extendDomain σ i,
      Equiv.Perm.cycleType_extendDomain]

end RS
