/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.ModelTheory.HanfSpectrum.IndexOrder
import LeanPool.InfinitaryLogic.ModelTheory.HanfSpectrum.CardinalBounds
/-!
# The ladder upper bound

EVERY model of the six ladder clauses at stage `α` has size at most `ℶ_{α+1}` — the
maximal-size half of the Marker Exercise 5.3 spectrum computation. The proof is well-founded
induction on the level index: `|U_i| ≤ ℶ_{idxVal i}` — the base level is enumerated by the
constants (`≤ ℵ₀`), a covered level `E`-extensionally injects into the powerset of its
predecessor (`≤ 2^ℶ = ℶ⁺`, `CardinalBounds.mk_le_two_power_of_injective_set`), and a limit
level is a countable union of earlier levels (`CardinalBounds.mk_iUnion_le_of_countable`).
The top clause then bounds the whole model by `|U_⊤| ≤ ℶ_{α+1}`.
-/

namespace FirstOrder

namespace Language

namespace HanfLadder

open Cardinal

variable {α : Ordinal.{0}} {M : Type} [(ladderLang α).Structure M]

/-- The level bound: in any ladder model, `|U_i| ≤ ℶ_{idxVal i}`. -/
private theorem mk_level_le_beth [Countable (Index α)] (h : IsLadderModel α (M := M)) (i :
  Index α) :
    Cardinal.mk {x : M // Level α i x} ≤ Cardinal.beth (idxVal i) := by
  induction i using WellFoundedLT.induction with
  | _ i IH =>
  by_cases hbot : i = ⊥
  · subst hbot
    rw [idxVal_bot, Cardinal.beth_zero]
    have hsurj : Function.Surjective (fun n : ℕ =>
        (⟨constVal α n, (h.base _).mpr ⟨n, rfl⟩⟩ : {x : M // Level α ⊥ x})) := by
      rintro ⟨x, hx⟩
      obtain ⟨n, hn⟩ := (h.base x).mp hx
      exact ⟨n, Subtype.ext hn.symm⟩
    have := hsurj.countable
    exact Cardinal.mk_le_aleph0
  by_cases hcov : ∃ i' : Index α, i' ⋖ i
  · obtain ⟨i', hi'⟩ := hcov
    have hinj : Function.Injective (fun x : {x : M // Level α i x} =>
        {y : {y : M // Level α i' y} | Edge α y.1 x.1}) := by
      intro x₁ x₂ h12
      have h12' : {y : {y : M // Level α i' y} | Edge α y.1 x₁.1}
          = {y : {y : M // Level α i' y} | Edge α y.1 x₂.1} := h12
      refine Subtype.ext (h.ext x₁.1 x₂.1 fun y => ?_)
      constructor
      · intro hy
        have hmem : (⟨y, h.pred_down hi' x₁.1 y x₁.2 hy⟩ : {y : M // Level α i' y}) ∈
            {y : {y : M // Level α i' y} | Edge α y.1 x₁.1} := hy
        rw [h12'] at hmem
        exact hmem
      · intro hy
        have hmem : (⟨y, h.pred_down hi' x₂.1 y x₂.2 hy⟩ : {y : M // Level α i' y}) ∈
            {y : {y : M // Level α i' y} | Edge α y.1 x₂.1} := hy
        rw [← h12'] at hmem
        exact hmem
    calc Cardinal.mk {x : M // Level α i x}
        ≤ 2 ^ Cardinal.mk {y : M // Level α i' y} :=
          FirstOrder.HanfLadder.mk_le_two_power_of_injective_set hinj
      _ ≤ 2 ^ Cardinal.beth (idxVal i') :=
          Cardinal.power_le_power_left two_ne_zero (IH i' hi'.1)
      _ = Cardinal.beth (idxVal i' + 1) := by
          rw [← Cardinal.beth_succ, Order.succ_eq_add_one]
      _ = Cardinal.beth (idxVal i) := by rw [covBy_iff_idxVal.mp hi']
  · have hlim : Order.IsSuccLimit i := by
      constructor
      · intro hmin
        exact hbot (le_antisymm (hmin bot_le) bot_le)
      · intro b hb
        exact hcov ⟨b, hb⟩
    have hsub : {x : M | Level α i x} ⊆
        ⋃ i' : {i' : Index α // i' < i}, {x : M | Level α i'.1 x} := by
      intro x hx
      obtain ⟨i', hi'lt, hi'x⟩ := h.limit_covered hlim x hx
      exact Set.mem_iUnion.mpr ⟨⟨i', hi'lt⟩, hi'x⟩
    refine le_trans (Cardinal.mk_le_mk_of_subset hsub) ?_
    refine FirstOrder.HanfLadder.mk_iUnion_le_of_countable (Cardinal.aleph0_le_beth _) ?_
    intro i'
    exact le_trans (IH i'.1 i'.2)
      (Cardinal.beth_le_beth.mpr (idxVal_lt_idxVal_iff.mpr i'.2).le)

/-- **The ladder upper bound**: every model of the six clauses has size at most `ℶ_{α+1}`. -/
theorem mk_le_beth_of_isLadderModel [Countable (Index α)] (h : IsLadderModel α (M := M)) :
    Cardinal.mk M ≤ Cardinal.beth (α + 1) := by
  have hinj : Function.Injective (fun x : M => (⟨x, h.top x⟩ : {x : M // Level α ⊤ x})) :=
    fun x y hxy => congrArg Subtype.val hxy
  have hle := (Cardinal.mk_le_of_injective hinj).trans (mk_level_le_beth h ⊤)
  rwa [idxVal_top] at hle

end HanfLadder

end Language

end FirstOrder
