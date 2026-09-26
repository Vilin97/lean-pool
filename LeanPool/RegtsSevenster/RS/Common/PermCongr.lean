/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Cycle data under permutation transport

Transporting a permutation along an equivalence of finite types
preserves its cycle type and its fixed-point count: `permCongr` is
`extendDomain` over the trivial predicate, and `extendDomain`
preserves cycle types.

The consequences for a sum of permutations follow: the two factors
`sumCongr σ 1` and `sumCongr 1 τ` are disjoint, so a `sumCongr` has
the sum of the two cycle types and the sum of the two fixed-point
counts.
-/

@[expose] public section

namespace RS

open Equiv Equiv.Perm

/-- `permCongr` is `extendDomain` along the trivial subtype. -/
theorem permCongr_eq_extendDomain {α β : Type}
    (e : α ≃ β) (π : Equiv.Perm α) :
    e.permCongr π =
      π.extendDomain
        (e.trans (Equiv.subtypeUnivEquiv
          (fun _ => trivial : ∀ x : β, (fun _ => True) x)).symm) := by
  ext x
  rw [Equiv.permCongr_apply,
    Equiv.Perm.extendDomain_apply_subtype _ _ (by trivial)]
  rfl

/-- Transporting a permutation preserves its cycle type. -/
theorem cycleType_permCongr {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (π : Equiv.Perm α) :
    (e.permCongr π).cycleType = π.cycleType := by
  rw [permCongr_eq_extendDomain e π,
    Equiv.Perm.cycleType_extendDomain]

/-- Transporting a permutation preserves its fixed points, up to
equivalence. -/
noncomputable def fixedPointsPermCongrEquiv {α β : Type}
    (e : α ≃ β) (π : Equiv.Perm α) :
    Function.fixedPoints (e.permCongr π) ≃ Function.fixedPoints π :=
  (e.subtypeEquiv (fun x => by
    simp only [Function.mem_fixedPoints, Function.IsFixedPt,
      Equiv.permCongr_apply, Equiv.symm_apply_apply]
    exact ⟨fun h => by rw [h], fun h => e.injective h⟩)).symm

/-- Transporting a permutation preserves the fixed-point count. -/
theorem card_fixedPoints_permCongr {α β : Type}
    (e : α ≃ β) (π : Equiv.Perm α)
    [Fintype (Function.fixedPoints π)]
    [Fintype (Function.fixedPoints (e.permCongr π))] :
    Fintype.card (Function.fixedPoints (e.permCongr π)) =
      Fintype.card (Function.fixedPoints π) :=
  Fintype.card_congr (fixedPointsPermCongrEquiv e π)

/-- Left factor in a sum preserves cycle type. -/
theorem cycleType_sumCongr_left {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (σ : Perm α) :
    cycleType (Equiv.sumCongr σ (1 : Perm β)) = σ.cycleType := by
  -- Identify sumCongr σ 1 with σ.extendDomain via the left-injection
  -- We define the equiv α ≃ {x : α ⊕ β // x ∈ Set.range Sum.inl}
  let p : α ⊕ β → Prop := fun x => ∃ a, x = Sum.inl a
  have hdec : DecidablePred p := fun x => by
    rcases x with a | b
    · exact isTrue ⟨a, rfl⟩
    · exact isFalse (fun ⟨_, h⟩ => nomatch h)
  let e : α ≃ Subtype p :=
    { toFun := fun a => ⟨Sum.inl a, ⟨a, rfl⟩⟩
      invFun := fun ⟨x, hx⟩ => hx.choose
      left_inv := fun a => by simp
      right_inv := fun ⟨x, hx⟩ => by
        ext
        simp only [p] at hx
        exact hx.choose_spec.symm }
  suffices hsuff : Equiv.sumCongr σ (1 : Perm β) = @Perm.extendDomain α (α ⊕ β)
    σ p hdec e by
    rw [hsuff, cycleType_extendDomain]
  ext x; rcases x with a | b
  · -- inl a: both sides give inl (σ a)
    change Sum.inl (σ a) = _
    rw [@Perm.extendDomain_apply_subtype α (α ⊕ β) σ p hdec e (Sum.inl a) ⟨a,
      rfl⟩]
    simp [e]
  · -- inr b: both sides give inr b
    change Sum.inr b = _
    have hb : ¬ p (Sum.inr b) := fun ⟨_, h⟩ => nomatch h
    rw [@Perm.extendDomain_apply_not_subtype α (α ⊕ β) σ p hdec e (Sum.inr b)
      hb]

/-- `sumCongr 1 τ` equals the permCongr-transport of `sumCongr τ 1` by
`sumComm`. -/
theorem sumCongr_right_eq_permCongr {α β : Type}
    (τ : Perm β) :
    Equiv.sumCongr (1 : Perm α) τ =
      (Equiv.sumComm β α).permCongr (Equiv.sumCongr τ (1 : Perm α)) := by
  ext x
  rcases x with a | b <;> simp [Equiv.permCongr_apply, Equiv.sumComm]

/-- Right factor in a sum preserves cycle type. -/
theorem cycleType_sumCongr_right {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (τ : Perm β) :
    cycleType (Equiv.sumCongr (1 : Perm α) τ) = τ.cycleType := by
  rw [sumCongr_right_eq_permCongr, cycleType_permCongr, cycleType_sumCongr_left]

/-- The factors `sumCongr σ 1` and `sumCongr 1 τ` are disjoint. -/
theorem disjoint_sumCongr {α β : Type}
    (σ : Perm α) (τ : Perm β) :
    Disjoint
      (Equiv.sumCongr σ (1 : Perm β))
      (Equiv.sumCongr (1 : Perm α) τ) := by
  intro x
  rcases x with a | b
  · right; simp
  · left; simp

/-- A sum of permutations has the sum of the two cycle types. -/
theorem cycleType_sumCongr {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (σ : Perm α) (τ : Perm β) :
    cycleType (Equiv.sumCongr σ τ) = σ.cycleType + τ.cycleType := by
  have hfact : Equiv.sumCongr σ τ =
      Equiv.sumCongr σ (1 : Perm β) * Equiv.sumCongr (1 : Perm α) τ := by
    rw [Perm.sumCongr_mul]; simp
  rw [hfact, (disjoint_sumCongr σ τ).cycleType_mul,
    cycleType_sumCongr_left, cycleType_sumCongr_right]

/-- The fixed points of a sum of permutations are the sum of the two
fixed-point sets. -/
noncomputable def fixedPointsSumCongrEquiv {α β : Type}
    (π₁ : Perm α) (π₂ : Perm β) :
    Function.fixedPoints (Equiv.sumCongr π₁ π₂) ≃
      (Function.fixedPoints π₁ ⊕ Function.fixedPoints π₂) :=
  Equiv.subtypeSum.trans
    (Equiv.sumCongr
      (Equiv.subtypeEquivRight fun a => by
        simp only [Function.mem_fixedPoints, Function.IsFixedPt,
          Equiv.sumCongr_apply, Sum.map_inl, Sum.inl.injEq])
      (Equiv.subtypeEquivRight fun b => by
        simp only [Function.mem_fixedPoints, Function.IsFixedPt,
          Equiv.sumCongr_apply, Sum.map_inr, Sum.inr.injEq]))

/-- A sum of permutations has the sum of the two fixed-point
counts. -/
theorem card_fixedPoints_sumCongr {α β : Type}
    (π₁ : Perm α) (π₂ : Perm β)
    [Fintype (Function.fixedPoints (Equiv.sumCongr π₁ π₂))]
    [Fintype (Function.fixedPoints π₁)]
    [Fintype (Function.fixedPoints π₂)] :
    Fintype.card (Function.fixedPoints (Equiv.sumCongr π₁ π₂)) =
      Fintype.card (Function.fixedPoints π₁) +
        Fintype.card (Function.fixedPoints π₂) :=
  (Fintype.card_congr (fixedPointsSumCongrEquiv π₁ π₂)).trans
    (Fintype.card_sum)

end RS
