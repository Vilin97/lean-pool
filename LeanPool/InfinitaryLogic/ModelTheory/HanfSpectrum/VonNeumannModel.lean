/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.ModelTheory.HanfSpectrum.IndexOrder
import Mathlib.SetTheory.ZFC.VonNeumann
import Mathlib.SetTheory.ZFC.Cardinal

/-!
# The von Neumann ladder model

The maximal model of the ladder sentence at a general stage `α`: the levels are the von Neumann
stages `ladderLevel β := V_{ω+β}` (so `card (ladderLevel β) = ℶ_β` by Mathlib's
`card_vonNeumann` and `beth_eq_preBeth`), the carrier is the `Shrink`-transport of the members
of `ladderLevel (α+1)` to `Type 0`, constants enumerate the countable base `V_ω`, the level
predicate `U_i` is membership in `ladderLevel (idxVal i)`, and `E` is `∈`. Outputs:

* `vStructure_isLadderModel` — the transported structure satisfies all six ladder clauses
  (transitivity of the stages gives extensionality; ranks give limit covering);
* `mk_vCarrier` — the carrier has size exactly `ℶ_{α+1}`.

The upper-bound half (every ladder model has size `≤ ℶ_{α+1}`) is `LadderBound.lean`; the
per-stage endpoint and the supremum assembly are `BethLadder.lean`.
-/

namespace FirstOrder

namespace Language

namespace HanfLadder

open Ordinal Cardinal

/-- The `β`-th ladder level: the von Neumann stage `V_{ω+β}`. -/
noncomputable def ladderLevel (β : Ordinal.{0}) : ZFSet.{0} :=
  ZFSet.vonNeumann (ω + β)

private theorem card_ladderLevel (β : Ordinal.{0}) : (ladderLevel β).card = Cardinal.beth β := by
  rw [ladderLevel, ZFSet.card_vonNeumann, ← Cardinal.beth_eq_preBeth]

theorem ladderLevel_subset {β γ : Ordinal.{0}} (h : β ≤ γ) : ladderLevel β ⊆ ladderLevel γ :=
  ZFSet.vonNeumann_subset_of_le (add_le_add_right h ω)

private theorem isTransitive_ladderLevel (β : Ordinal.{0}) : (ladderLevel β).IsTransitive :=
  ZFSet.isTransitive_vonNeumann _

private theorem ladderLevel_add_one (β : Ordinal.{0}) :
    ladderLevel (β + 1) = ZFSet.powerset (ladderLevel β) := by
  rw [ladderLevel, ladderLevel, ← add_assoc, ZFSet.vonNeumann_add_one]

/-- The countable enumeration of the base level `V_ω`. -/
private noncomputable def omegaEnum : ℕ ≃ Shrink.{0} ↥(ladderLevel 0) :=
  Classical.choice (Cardinal.eq.mp (by
    rw [Cardinal.mk_nat]
    exact (show (ladderLevel 0).card = Cardinal.aleph0 by
      rw [card_ladderLevel, Cardinal.beth_zero]).symm))

/-- The `n`-th base element, as a `ZFSet`. -/
noncomputable def omegaEnumZ (n : ℕ) : ZFSet.{0} :=
  ((equivShrink ↥(ladderLevel 0)).symm (omegaEnum n)).1

theorem omegaEnumZ_mem (n : ℕ) : omegaEnumZ n ∈ ladderLevel 0 :=
  ((equivShrink ↥(ladderLevel 0)).symm (omegaEnum n)).2

private theorem omegaEnumZ_surjective {z : ZFSet.{0}} (hz : z ∈ ladderLevel 0) :
    ∃ n, omegaEnumZ n = z := by
  obtain ⟨n, hn⟩ := omegaEnum.surjective (equivShrink ↥(ladderLevel 0) ⟨z, hz⟩)
  refine ⟨n, ?_⟩
  have h2 : (equivShrink ↥(ladderLevel 0)).symm (omegaEnum n) = ⟨z, hz⟩ :=
    (congrArg _ hn).trans (_root_.Equiv.symm_apply_apply (equivShrink ↥(ladderLevel 0)) ⟨z, hz⟩)
  rw [omegaEnumZ, h2]

variable (α : Ordinal.{0})

/-- The model carrier: the members of `V_{ω+α+1}`, shrunk to `Type 0`. -/
noncomputable def VCarrier : Type := Shrink.{0} ↥(ladderLevel (α + 1))

/-- The underlying `ZFSet` of a carrier element. -/
noncomputable def toZ (x : VCarrier α) : ZFSet.{0} :=
  ((equivShrink ↥(ladderLevel (α + 1))).symm x).1

private theorem toZ_mem (x : VCarrier α) : toZ α x ∈ ladderLevel (α + 1) :=
  ((equivShrink ↥(ladderLevel (α + 1))).symm x).2

private theorem toZ_injective : Function.Injective (toZ α) := fun _ _ hxy =>
  (equivShrink ↥(ladderLevel (α + 1))).symm.injective (Subtype.ext hxy)

private theorem toZ_surjective {z : ZFSet.{0}} (hz : z ∈ ladderLevel (α + 1)) :
    ∃ x : VCarrier α, toZ α x = z := by
  refine ⟨equivShrink ↥(ladderLevel (α + 1)) ⟨z, hz⟩, ?_⟩
  simp only [toZ]
  exact congrArg Subtype.val
    (_root_.Equiv.symm_apply_apply (equivShrink ↥(ladderLevel (α + 1))) ⟨z, hz⟩)

/-- The von Neumann ladder structure: constants enumerate the base, `U_i` is membership in
`ladderLevel (idxVal i)`, and `E` is `∈`. -/
@[reducible] noncomputable def vStructure : (ladderLang α).Structure (VCarrier α) where
  funMap {n} f _ := match n, f with
    | 0, m => equivShrink ↥(ladderLevel (α + 1))
        ⟨omegaEnumZ m, ladderLevel_subset zero_le (omegaEnumZ_mem m)⟩
  RelMap {n} r v := match n, r with
    | 1, i => toZ α (v 0) ∈ ladderLevel (idxVal (i : Index α))
    | 2, _ => toZ α (v 0) ∈ toZ α (v 1)

private theorem toZ_constVal (n : ℕ) :
    letI := vStructure α
    toZ α (constVal α n : VCarrier α) = omegaEnumZ n := by
  let := vStructure α
  rw [toZ, constVal]
  exact congrArg Subtype.val (_root_.Equiv.symm_apply_apply (equivShrink ↥(ladderLevel (α + 1)))
    ⟨omegaEnumZ n, ladderLevel_subset zero_le (omegaEnumZ_mem n)⟩)

/-- **The six ladder clauses hold in the von Neumann model.** -/
theorem vStructure_isLadderModel :
    letI := vStructure α
    IsLadderModel α (M := VCarrier α) := by
  let := vStructure α
  have hLevel : ∀ (i : Index α) (x : VCarrier α),
      Level α i x ↔ toZ α x ∈ ladderLevel (idxVal i) := fun i x => Iff.rfl
  have hEdge : ∀ x y : VCarrier α, Edge α x y ↔ toZ α x ∈ toZ α y := fun x y => Iff.rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- base: `U_⊥` is exactly the constants
    intro x
    rw [hLevel, idxVal_bot]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := omegaEnumZ_surjective hx
      refine ⟨n, toZ_injective α ?_⟩
      rw [toZ_constVal, hn]
    · rintro ⟨n, rfl⟩
      rw [toZ_constVal]
      exact omegaEnumZ_mem n
  · -- top: everything is a member of `ladderLevel (α+1)`
    intro x
    rw [hLevel, idxVal_top]
    exact toZ_mem α x
  · -- nested: the stages are increasing
    intro i j hij x hx
    rw [hLevel] at hx ⊢
    exact ladderLevel_subset (idxVal_le_idxVal_iff.mpr hij.le) hx
  · -- limit covering: split on whether the rank is below `ω`
    intro j hj x hx
    have hv : Order.IsSuccLimit (idxVal j) := isSuccLimit_iff_idxVal.mp hj
    rw [hLevel] at hx
    rw [ladderLevel, ZFSet.mem_vonNeumann] at hx
    rcases lt_or_ge (ZFSet.rank (toZ α x)) ω with hr | hr
    · refine ⟨⊥, hj.bot_lt, ?_⟩
      rw [hLevel, idxVal_bot, ladderLevel, ZFSet.mem_vonNeumann]
      exact lt_of_lt_of_le hr le_self_add
    · set δ := ZFSet.rank (toZ α x) - ω with hδ
      have hrank : ZFSet.rank (toZ α x) = ω + δ := (Ordinal.add_sub_cancel_of_le hr).symm
      have hδlt : δ < idxVal j := by
        rw [hrank] at hx
        exact (add_lt_add_iff_left ω).mp hx
      have hδ1 : δ + 1 < idxVal j := by
        have := hv.succ_lt hδlt
        rwa [Order.succ_eq_add_one] at this
      refine ⟨idxOf (δ + 1) (lt_trans hδ1 (idxVal_lt j)), ?_, ?_⟩
      · rw [← idxVal_lt_idxVal_iff, idxVal_idxOf]
        exact hδ1
      · rw [hLevel, idxVal_idxOf, ladderLevel, ZFSet.mem_vonNeumann, hrank, ← add_assoc]
        exact lt_of_lt_of_eq (Order.lt_succ _) (Order.succ_eq_add_one _)
  · -- predecessor descent: powerset membership
    intro i j hij x y hx hyx
    rw [hLevel] at hx ⊢
    rw [hEdge] at hyx
    rw [covBy_iff_idxVal.mp hij, ladderLevel_add_one, ZFSet.mem_powerset] at hx
    exact hx hyx
  · -- extensionality: transitivity confines members to the carrier
    intro y z h
    refine toZ_injective α (ZFSet.ext fun w => ?_)
    constructor
    · intro hwy
      have hwV : w ∈ ladderLevel (α + 1) :=
        isTransitive_ladderLevel (α + 1) _ (toZ_mem α y) hwy
      obtain ⟨x, rfl⟩ := toZ_surjective α hwV
      exact (h x).mp hwy
    · intro hwz
      have hwV : w ∈ ladderLevel (α + 1) :=
        isTransitive_ladderLevel (α + 1) _ (toZ_mem α z) hwz
      obtain ⟨x, rfl⟩ := toZ_surjective α hwV
      exact (h x).mpr hwz

/-- **The von Neumann model has size exactly `ℶ_{α+1}`.** -/
theorem mk_vCarrier : Cardinal.mk (VCarrier α) = Cardinal.beth (α + 1) := by
  have h : Cardinal.mk (VCarrier α) = (ladderLevel (α + 1)).card := rfl
  rw [h, card_ladderLevel]

end HanfLadder

end Language

end FirstOrder
