/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.QuarticCircuit

/-!
# Normal form for a seed-using useful child

The old-state shift may contain the seed with coefficient zero or one.  In
the latter case the identity
`(g + a) * (c + 1) = (g + a) * c + g + a`
absorbs that coefficient.  Thus a useful seed-using child always supplies an
actual target-ambient product `F = (g + a) * c` outside the rational-low
state.  This is the precise input to the quartic idempotence argument.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- A seed-using product that gives a target outside the affine-plus-rational-target space. -/
@[expose]
def SeedUsingTargetWitness (g : ANF 8) : Prop :=
  ∃ (a c F : ANF 8),
    a ∈ rationalLowSpace ∧
    c ∈ rationalLowSpace ∧
    F = (g + a) * c ∧
    F ∈ targetAmbient 8 (mulTarget 4) ∧
    F ∉ rationalLowSpace

private theorem one_mem_rationalLow : (1 : ANF 8) ∈ rationalLowSpace :=
  Submodule.mem_sup_left (one_mem_affine 8)

/-- Convert the circuit-level useful-child data to the target product used by
the manuscript's seed-using quartic argument. -/
theorem NormalizedEight.seedUsingTargetWitness
    {C : Circuit 8 8} (h : NormalizedEight C)
    {target representative shift : ANF 8}
    (htarget : target ∈ targetAmbient 8 (mulTarget 4))
    (htargetOld : target ∉ circuitFlag C 4)
    (hshift : shift ∈ circuitFlag C 4)
    (htargetEq : target = shift + representative)
    (hrepresentative : IsSeedUsingProduct (C.gate 3) representative) :
    SeedUsingTargetWitness (C.gate 3) := by
  have hlowFour : rationalLowSpace ≤ circuitFlag C 4 := by
    rw [h.wireSpace_four_eq]
    exact le_sup_left
  rcases hrepresentative with
    ⟨a, c, ha, hc, hrepresentativeEq⟩
  rcases exists_low_add_seed_of_mem_four h hshift with
    ⟨p, e, hp, hshiftEq⟩
  rcases f2_eq_zero_or_one e with rfl | rfl
  · have htargetEq' : target = p + representative := by
      simpa using htargetEq.trans
        (congrArg (fun z => z + representative) hshiftEq)
    have hrepresentativeAmbient :
        representative ∈ targetAmbient 8 (mulTarget 4) := by
      have htargetPlus :=
        add_mem_targetAmbient_of_mem_rationalLow htarget hp
      have heq : target + p = representative := by
        rw [htargetEq']
        simp [add_comm, add_left_comm]
      rwa [heq] at htargetPlus
    have hrepresentativeNotLow : representative ∉ rationalLowSpace := by
      intro hrepLow
      apply htargetOld
      apply hlowFour
      rw [htargetEq']
      exact Submodule.add_mem _ hp hrepLow
    exact ⟨a, c, representative, ha, hc, hrepresentativeEq,
      hrepresentativeAmbient, hrepresentativeNotLow⟩
  · let c' : ANF 8 := c + 1
    let F : ANF 8 := (C.gate 3 + a) * c'
    have hc' : c' ∈ rationalLowSpace := by
      exact Submodule.add_mem _ hc one_mem_rationalLow
    have hF : F = representative + (C.gate 3 + a) := by
      change (C.gate 3 + a) * (c + 1) =
        representative + (C.gate 3 + a)
      rw [mul_add, mul_one, ← hrepresentativeEq]
    have htargetEq' :
        target = (p + C.gate 3) + representative := by
      simpa using htargetEq.trans
        (congrArg (fun z => z + representative) hshiftEq)
    have hpadd : p + a ∈ rationalLowSpace :=
      Submodule.add_mem _ hp ha
    have htargetCorr : target = (p + a) + F := by
      rw [htargetEq', hF]
      rw [show
        (p + a) + (representative + (C.gate 3 + a)) =
          ((p + C.gate 3) + representative) + (a + a) by abel]
      simp only [anf_add_self, add_zero]
    have hFAmbient : F ∈ targetAmbient 8 (mulTarget 4) := by
      have htargetPlus :=
        add_mem_targetAmbient_of_mem_rationalLow htarget hpadd
      have heq : target + (p + a) = F := by
        rw [htargetCorr]
        calc
          ((p + a) + F) + (p + a) =
              ((p + a) + (p + a)) + F := by ac_rfl
          _ = F := by simp
      rwa [heq] at htargetPlus
    have hFNotLow : F ∉ rationalLowSpace := by
      intro hFLow
      apply htargetOld
      apply hlowFour
      rw [htargetCorr]
      exact Submodule.add_mem _ hpadd hFLow
    exact ⟨a, c', F, ha, hc', rfl, hFAmbient, hFNotLow⟩

/-- The two Boolean idempotence equations attached to a seed-using target
product. -/
theorem seedUsing_idempotence {g a c F : ANF 8}
    (hF : F = (g + a) * c) :
    (g + a) * F = F ∧ F * c = F := by
  exact absorption_of_eq hF

end

end N4
end UnrestrictedBooleanMul
