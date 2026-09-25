/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndSplit
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.PermRepChar

/-!
# Schur specialisations at super power sums are multiplicities

The additive splitting identity decomposes `superPS p q` as
`superPS p 0 + superPS 0 q`; both one-sided values are intertwiner
dimensions, and the induction multiplicities are natural numbers,
so every Schur specialisation at a super power sum is a natural
number — the full nonnegativity input for the hook arguments of
Deligne 1.10/1.12.
-/

@[expose] public section

namespace RS

/-- A finite sum of natural values is a natural value. -/
theorem exists_nat_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, ∃ m : ℕ, f i = m) :
    ∃ M : ℕ, ∑ i ∈ s, f i = M := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨m, hm⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨M, hM⟩ := ih fun i hi =>
      h i (Finset.mem_insert_of_mem hi)
    exact ⟨m + M, by
      rw [Finset.sum_insert ha, hm, hM, Nat.cast_add]⟩

/-- **Schur specialisations at super power sums are natural
numbers**: the two-sided value splits into one-sided multiplicities
through the additive identity. -/
theorem diagramSchur_superPS_exists_nat (p q : ℕ)
    (lam : YoungDiagram) :
    ∃ m : ℕ, diagramSchur lam (superPS p q) = m := by
  have hsplit : superPS p q =
      fun c => superPS p 0 c + superPS 0 q c := by
    funext c
    simp [superPS]
  rw [hsplit, diagramSchur_add]
  refine exists_nat_sum _ _ fun ab _ => ?_
  refine exists_nat_sum _ _ fun μ _ => ?_
  refine exists_nat_sum _ _ fun ν _ => ?_
  obtain ⟨m₁, h₁⟩ := indMult_exists_nat
    (⟨lam, (Finset.mem_antidiagonal.mp ab.2).symm⟩ :
      Shape (ab.1.1 + ab.1.2)) μ ν
  obtain ⟨m₂, h₂⟩ := diagramSchur_superPS_h_exists_nat p μ
  obtain ⟨m₃, h₃⟩ := diagramSchur_superPS_e_exists_nat q ν
  exact ⟨m₁ * m₂ * m₃, by
    rw [h₁, h₂, h₃, Nat.cast_mul, Nat.cast_mul]⟩

end RS
