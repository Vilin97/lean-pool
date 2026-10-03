/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.QuadraticCircuit

/-!
# Target witnesses for useful gates

The structural part of the `n = 4` argument repeatedly replaces a useful
gate output by the unique target-ambient direction in its one-dimensional
extension.  This file packages that linear-algebra step once.  It is entirely
independent of the later homogeneous-coordinate calculations.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- A useful one-vector extension contains a target-ambient vector which was
not present in the preceding state. -/
theorem exists_targetWitness_of_useful {m r : Nat}
    (C : Circuit m r) (T : Submodule F₂ (ANF m)) (j : Fin r)
    (huse : UsefulAt C T j) :
    ∃ t : ANF m,
      t ∈ targetAmbient m T ∧
      t ∉ circuitFlag C j.val ∧
      t ∈ circuitFlag C (j.val + 1) := by
  let I₀ := circuitFlag C j.val ⊓ targetAmbient m T
  let I₁ := circuitFlag C (j.val + 1) ⊓ targetAmbient m T
  have hnot : ¬ I₁ ≤ I₀ := by
    intro hle
    have hdim : Module.finrank F₂ ↑I₁ ≤ Module.finrank F₂ ↑I₀ :=
      Submodule.finrank_mono hle
    have ha₀ : Module.finrank F₂ ↑(affine m) ≤ Module.finrank F₂ ↑I₀ := by
      apply Submodule.finrank_mono
      intro p hp
      exact ⟨affine_le_wireSpace C.gate hp, Submodule.mem_sup_left hp⟩
    unfold UsefulAt flagTargetRank at huse
    change Module.finrank F₂ ↑I₁ - Module.finrank F₂ ↑(affine m) =
      (Module.finrank F₂ ↑I₀ - Module.finrank F₂ ↑(affine m)) + 1 at huse
    omega
  rw [IsConcreteLE.not_le_iff_exists] at hnot
  rcases hnot with ⟨t, ht₁, ht₀⟩
  refine ⟨t, ht₁.2, ?_, ht₁.1⟩
  intro htold
  exact ht₀ ⟨htold, ht₁.2⟩

/-- A useful gate output differs from a new target-ambient direction by a
wire already present before the gate.  Over `F₂` the coefficient of the new
gate is forced to be one. -/
theorem exists_targetWitness_eq_state_add_gate_of_useful {m r : Nat}
    (C : Circuit m r) (T : Submodule F₂ (ANF m)) (j : Fin r)
    (huse : UsefulAt C T j) :
    ∃ (t v : ANF m),
      t ∈ targetAmbient m T ∧
      t ∉ circuitFlag C j.val ∧
      t ∈ circuitFlag C (j.val + 1) ∧
      v ∈ circuitFlag C j.val ∧
      t = v + C.gate j := by
  rcases exists_targetWitness_of_useful C T j huse with
    ⟨t, htA, htold, htnew⟩
  have hstep : circuitFlag C (j.val + 1) =
      circuitFlag C j.val ⊔ Submodule.span F₂ {C.gate j} := by
    rw [circuitFlag, wireSpace_succ C.gate j.isLt]
    congr 2
  have htnewFlag := htnew
  rw [hstep] at htnew
  rcases Submodule.mem_sup.mp htnew with ⟨v, hv, w, hw, hvw⟩
  rcases Submodule.mem_span_singleton.mp hw with ⟨a, rfl⟩
  rcases f2_eq_zero_or_one a with rfl | rfl
  · simp only [zero_smul, add_zero] at hvw
    exact False.elim (htold (hvw ▸ hv))
  · refine ⟨t, v, htA, htold, htnewFlag, hv, ?_⟩
    simpa using hvw.symm

/-- The target witness generates exactly the same next state as the original
gate output. -/
theorem circuitFlag_succ_eq_targetWitness {m r : Nat}
    (C : Circuit m r) (T : Submodule F₂ (ANF m)) (j : Fin r)
    (huse : UsefulAt C T j) :
    ∃ t : ANF m,
      t ∈ targetAmbient m T ∧
      t ∉ circuitFlag C j.val ∧
      circuitFlag C (j.val + 1) =
        circuitFlag C j.val ⊔ Submodule.span F₂ {t} := by
  rcases exists_targetWitness_of_useful C T j huse with
    ⟨t, htA, htold, htnew⟩
  refine ⟨t, htA, htold, ?_⟩
  exact circuit_first_entry_replacement C j t htnew htold

end

end N4
end UnrestrictedBooleanMul
