/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.UsefulWitness

/-!
# Algebraic normal form for the first suffix gate

Immediately before gate five the state is `Aff + R + ⟨g⟩`.  Idempotence
reduces the product of any two wires in this state, modulo the state itself,
to one of two forms: a low--low product, or a product with exactly one
`g`-containing factor.  This is the non-combinatorial normalization used in
both the quartic and cubic feedback arguments.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- A product of two ANFs in the affine-plus-rational-target space. -/
@[expose]
def IsLowLowProduct (f : ANF 8) : Prop :=
  ∃ p q : ANF 8,
    p ∈ rationalLowSpace ∧ q ∈ rationalLowSpace ∧ f = p * q

/-- A product whose first input is the seed plus a low term and whose second input is low. -/
@[expose]
def IsSeedUsingProduct (g f : ANF 8) : Prop :=
  ∃ p c : ANF 8,
    p ∈ rationalLowSpace ∧ c ∈ rationalLowSpace ∧
      f = (g + p) * c

theorem NormalizedEight.wireSpace_four_eq {C : Circuit 8 8}
    (h : NormalizedEight C) :
    circuitFlag C 4 =
      rationalLowSpace ⊔ Submodule.span F₂ {C.gate 3} := by
  rw [circuitFlag, wireSpace_succ C.gate (by decide)]
  simpa [circuitFlag] using congrArg
    (fun V : Submodule F₂ (ANF 8) =>
      V ⊔ Submodule.span F₂ {C.gate (3 : Fin 8)}) h.wireSpace_seed_eq

/-- Every wire in the first post-seed state has a low part and one Boolean
coefficient of the seed. -/
theorem exists_low_add_seed_of_mem_four {C : Circuit 8 8}
    (h : NormalizedEight C) {w : ANF 8} (hw : w ∈ circuitFlag C 4) :
    ∃ (p : ANF 8) (e : F₂),
      p ∈ rationalLowSpace ∧ w = p + e • C.gate 3 := by
  rw [h.wireSpace_four_eq] at hw
  rcases Submodule.mem_sup.mp hw with ⟨p, hp, q, hq, hpq⟩
  rcases Submodule.mem_span_singleton.mp hq with ⟨e, rfl⟩
  exact ⟨p, e, hp, hpq.symm⟩

private theorem seed_mem_four {C : Circuit 8 8} (h : NormalizedEight C) :
    C.gate 3 ∈ circuitFlag C 4 := by
  rw [h.wireSpace_four_eq]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

/-- Product normalization modulo `Aff + R + ⟨g⟩`. -/
theorem normalize_seed_state_product {C : Circuit 8 8}
    (h : NormalizedEight C) {l r : ANF 8}
    (hl : l ∈ circuitFlag C 4) (hr : r ∈ circuitFlag C 4) :
    ∃ (f s : ANF 8),
      s ∈ circuitFlag C 4 ∧
      l * r = s + f ∧
      (IsLowLowProduct f ∨ IsSeedUsingProduct (C.gate 3) f) := by
  rcases exists_low_add_seed_of_mem_four h hl with ⟨p, ep, hp, rfl⟩
  rcases exists_low_add_seed_of_mem_four h hr with ⟨q, eq, hq, rfl⟩
  rcases f2_eq_zero_or_one ep with rfl | rfl <;>
    rcases f2_eq_zero_or_one eq with rfl | rfl
  · refine ⟨p * q, 0, ?_, ?_, Or.inl ⟨p, q, hp, hq, rfl⟩⟩
    · exact Submodule.zero_mem _
    · simp
  · refine ⟨(C.gate 3 + q) * p, 0, ?_, ?_, Or.inr ⟨q, p, hq, hp, rfl⟩⟩
    · exact Submodule.zero_mem _
    · simp only [zero_smul, one_smul, add_zero, zero_add]
      rw [mul_comm p]
      congr 1
      exact add_comm _ _
  · refine ⟨(C.gate 3 + p) * q, 0, ?_, ?_, Or.inr ⟨p, q, hp, hq, rfl⟩⟩
    · exact Submodule.zero_mem _
    · simp [add_comm]
  · let u : ANF 8 := C.gate 3 + p
    let c : ANF 8 := p + q
    refine ⟨u * c, u, ?_, ?_, Or.inr ⟨p, c, hp, ?_, rfl⟩⟩
    · exact Submodule.add_mem _ (seed_mem_four h)
        (by rw [h.wireSpace_four_eq]; exact Submodule.mem_sup_left hp)
    · simp only [one_smul]
      have hl' : p + C.gate 3 = u := by simp [u, add_comm]
      have hr' : q + C.gate 3 = u + c := by
        change q + C.gate 3 =
          (C.gate 3 + p) + (p + q)
        symm
        calc
          (C.gate 3 + p) + (p + q) = C.gate 3 + (p + p) + q := by
            ac_rfl
          _ = C.gate 3 + q := by simp
          _ = q + C.gate 3 := by ac_rfl
      rw [hl', hr', mul_add, anf_mul_self]
    · exact Submodule.add_mem _ hp hq

/-- A new target at the fifth gate, represented modulo the fourth-gate flag by a seed child. -/
@[expose]
def UsefulSeedChildData (C : Circuit 8 8) : Prop :=
  ∃ (target representative shift : ANF 8),
    target ∈ targetAmbient 8 (mulTarget 4) ∧
    target ∉ circuitFlag C 4 ∧
    target ∈ circuitFlag C 5 ∧
    shift ∈ circuitFlag C 4 ∧
    target = shift + representative ∧
    (IsLowLowProduct representative ∨
      IsSeedUsingProduct (C.gate 3) representative)

/-- Circuit-level gate five is reduced to the two algebraic child types. -/
theorem NormalizedEight.usefulSeedChildData {C : Circuit 8 8}
    (h : NormalizedEight C) : UsefulSeedChildData C := by
  rcases exists_targetWitness_eq_state_add_gate_of_useful
      C (mulTarget 4) (4 : Fin 8) h.gateFive_useful with
    ⟨t, v, htA, htold, htnew, hv, htv⟩
  rcases normalize_seed_state_product h (C.left_mem 4) (C.right_mem 4) with
    ⟨f, s, hs, hgate, hshape⟩
  refine ⟨t, f, v + s, htA, htold, htnew,
    Submodule.add_mem _ hv hs, ?_, hshape⟩
  rw [C.gate_eq 4, hgate] at htv
  rw [htv]
  module

end

end N4
end UnrestrictedBooleanMul
