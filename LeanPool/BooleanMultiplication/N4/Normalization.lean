/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.Geometry

/-!
# First-entry replacement and the normalized eight-gate interface

The actual gate rewiring is captured at the semantic wire-space level: when a
new target direction first enters a one-vector extension, it can replace that
vector without changing the state.  This is exactly what later gates see in
the semantic circuit model.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Basis replacement in a one-vector extension over `F₂`. -/
theorem span_first_entry_replacement {m : Nat}
    (V : Submodule F₂ (ANF m)) (g t : ANF m)
    (ht : t ∈ V ⊔ Submodule.span F₂ {g}) (htV : t ∉ V) :
    V ⊔ Submodule.span F₂ {g} = V ⊔ Submodule.span F₂ {t} := by
  apply le_antisymm
  · apply sup_le le_sup_left
    rw [Submodule.span_singleton_le_iff_mem]
    rcases Submodule.mem_sup.mp ht with ⟨v, hv, w, hw, hvw⟩
    rcases (Submodule.mem_span_singleton.mp hw) with ⟨a, ha⟩
    rcases f2_eq_zero_or_one a with ha0 | ha1
    · rw [ha0, zero_smul] at ha
      subst w
      simp only [add_zero] at hvw
      exact False.elim (htV (hvw ▸ hv))
    · rw [ha1, one_smul] at ha
      subst w
      have hmem : t + v ∈ V ⊔ Submodule.span F₂ {t} :=
        Submodule.add_mem _
          (Submodule.mem_sup_right
            (Submodule.mem_span_singleton_self t))
          (Submodule.mem_sup_left hv)
      have heq : t + v = g := by
        rw [← hvw]
        calc
          (v + g) + v = (v + v) + g := by ac_rfl
          _ = g := by simp
      rwa [heq] at hmem
  · apply sup_le le_sup_left
    rw [Submodule.span_singleton_le_iff_mem]
    exact ht

/-- Circuit form of first-entry replacement. -/
theorem circuit_first_entry_replacement {m r : Nat} (C : Circuit m r)
    (j : Fin r) (t : ANF m)
    (ht : t ∈ circuitFlag C (j.val + 1))
    (htFirst : t ∉ circuitFlag C j.val) :
    circuitFlag C (j.val + 1) =
      circuitFlag C j.val ⊔ Submodule.span F₂ {t} := by
  rw [circuitFlag, wireSpace_succ C.gate j.isLt] at ht ⊢
  have hjeta : (⟨j.val, j.isLt⟩ : Fin r) = j := Fin.ext rfl
  rw [hjeta] at ht ⊢
  exact span_first_entry_replacement _ _ _ ht htFirst

/-- The product target corresponding to evaluation at zero. -/
@[expose] def rZeroANF : ANF 8 := targetANF rZeroCoeff
/-- The product target corresponding to evaluation at one. -/
@[expose] def rOneANF : ANF 8 := targetANF rOneCoeff
/-- The product target corresponding to the leading coefficient. -/
@[expose] def rInfinityANF : ANF 8 := targetANF rInfinityCoeff

/-- The span of the product evaluations at zero, one, and infinity. -/
@[expose] def rationalTargetSpace : Submodule F₂ (ANF 8) :=
  Submodule.span F₂ {rZeroANF, rOneANF, rInfinityANF}

/-- Affine functions together with the rational-place product targets. -/
@[expose] def rationalLowSpace : Submodule F₂ (ANF 8) :=
  affine 8 ⊔ rationalTargetSpace

theorem targetANF_rationalCoeffRep (α : Fin 3 → F₂) :
    targetANF (rationalCoeffRep α) =
      α 0 • rZeroANF + α 1 • rOneANF + α 2 • rInfinityANF := by
  change targetANFLinear (rationalCoeffRep α) =
    α 0 • targetANFLinear rZeroCoeff +
      α 1 • targetANFLinear rOneCoeff +
      α 2 • targetANFLinear rInfinityCoeff
  rw [rationalCoeffRep, map_add, map_add, map_smul, map_smul, map_smul]

theorem mem_rationalTargetSpace_iff (p : ANF 8) :
    p ∈ rationalTargetSpace ↔
      ∃ α : Fin 3 → F₂, p = targetANF (rationalCoeffRep α) := by
  constructor
  · intro hp
    refine Submodule.span_induction
      (p := fun p _ => ∃ α : Fin 3 → F₂,
        p = targetANF (rationalCoeffRep α)) ?_ ?_ ?_ ?_ hp
    · intro q hq
      rcases hq with rfl | rfl | rfl
      · exact ⟨![1, 0, 0], by
          simp [targetANF_rationalCoeffRep, rZeroANF]⟩
      · exact ⟨![0, 1, 0], by
          simp [targetANF_rationalCoeffRep, rOneANF]⟩
      · exact ⟨![0, 0, 1], by
          simp [targetANF_rationalCoeffRep, rInfinityANF]⟩
    · exact ⟨0, by
        change (0 : ANF 8) = targetANFLinear (rationalCoeffRep 0)
        rw [show rationalCoeffRep 0 = 0 by
          funext i
          fin_cases i <;> simp [rationalCoeffRep]]
        exact (map_zero targetANFLinear).symm⟩
    · rintro p q _hp _hq ⟨α, rfl⟩ ⟨β, rfl⟩
      refine ⟨α + β, ?_⟩
      change targetANFLinear (rationalCoeffRep α) +
        targetANFLinear (rationalCoeffRep β) =
          targetANFLinear (rationalCoeffRep (α + β))
      have hrep : rationalCoeffRep (α + β) =
          rationalCoeffRep α + rationalCoeffRep β := by
        funext i
        fin_cases i <;> simp [rationalCoeffRep] <;> ring
      rw [hrep, map_add]
    · rintro a p _hp ⟨α, rfl⟩
      refine ⟨a • α, ?_⟩
      change a • targetANFLinear (rationalCoeffRep α) =
        targetANFLinear (rationalCoeffRep (a • α))
      have hrep : rationalCoeffRep (a • α) =
          a • rationalCoeffRep α := by
        funext i
        fin_cases i <;> simp [rationalCoeffRep] <;> ring
      rw [hrep, map_smul]
  · rintro ⟨α, rfl⟩
    rw [targetANF_rationalCoeffRep]
    apply Submodule.add_mem
    · apply Submodule.add_mem
      · exact Submodule.smul_mem _ _
          (Submodule.subset_span (Set.mem_insert _ _))
      · exact Submodule.smul_mem _ _
          (Submodule.subset_span (Set.mem_insert_of_mem _
            (Set.mem_insert _ _)))
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_insert_of_mem _
          (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

/-- The state constructed by the eight-gate normalization theorem, recording
the rational prefix, seed defect, and useful suffix for the contradiction. -/
structure NormalizedEight (C : Circuit 8 8) : Prop where
  computes : C.Computes (Mul 4)
  gate_zero : C.gate 0 = rZeroANF
  gate_one : C.gate 1 = rOneANF
  gate_infinity : C.gate 2 = rInfinityANF
  seed_nonUseful : ¬ UsefulAt C (mulTarget 4) 3
  suffix_useful : ∀ j : Fin 8, 4 ≤ j.val → UsefulAt C (mulTarget 4) j
  defect_one : flagDefectRank C.finalWire (mulTarget 4) = 1

theorem NormalizedEight.prefixGates_three {C : Circuit 8 8}
    (h : NormalizedEight C) :
    prefixGates C.gate 3 = {rZeroANF, rOneANF, rInfinityANF} := by
  ext p
  constructor
  · rintro ⟨i, hi, rfl⟩
    fin_cases i <;> simp_all [h.gate_zero, h.gate_one, h.gate_infinity]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by decide, h.gate_zero⟩
    · exact ⟨1, by decide, h.gate_one⟩
    · exact ⟨2, by decide, h.gate_infinity⟩

theorem NormalizedEight.wireSpace_seed_eq {C : Circuit 8 8}
    (h : NormalizedEight C) :
    wireSpace C.gate 3 = rationalLowSpace := by
  rw [wireSpace, h.prefixGates_three]
  rfl

theorem NormalizedEight.seed_left_mem_rationalLow {C : Circuit 8 8}
    (h : NormalizedEight C) : C.left 3 ∈ rationalLowSpace := by
  rw [← h.wireSpace_seed_eq]
  exact C.left_mem 3

theorem NormalizedEight.seed_right_mem_rationalLow {C : Circuit 8 8}
    (h : NormalizedEight C) : C.right 3 ∈ rationalLowSpace := by
  rw [← h.wireSpace_seed_eq]
  exact C.right_mem 3

/-- Algebraic factor data exposed by the normalized seed. -/
@[expose]
def SeedFactorData (C : Circuit 8 8) : Prop :=
  ∃ (leftAffine rightAffine : ANF 8)
      (leftCoeff rightCoeff : Fin 3 → F₂),
    leftAffine ∈ affine 8 ∧
    rightAffine ∈ affine 8 ∧
    C.left 3 = leftAffine + targetANF (rationalCoeffRep leftCoeff) ∧
    C.right 3 = rightAffine + targetANF (rationalCoeffRep rightCoeff) ∧
    C.gate 3 =
      (leftAffine + targetANF (rationalCoeffRep leftCoeff)) *
        (rightAffine + targetANF (rationalCoeffRep rightCoeff))

theorem NormalizedEight.seedFactorData {C : Circuit 8 8}
    (h : NormalizedEight C) : SeedFactorData C := by
  rcases Submodule.mem_sup.mp h.seed_left_mem_rationalLow with
    ⟨a, ha, q, hq, hleft⟩
  rcases Submodule.mem_sup.mp h.seed_right_mem_rationalLow with
    ⟨b, hb, r, hr, hright⟩
  rcases (mem_rationalTargetSpace_iff q).mp hq with ⟨α, hα⟩
  rcases (mem_rationalTargetSpace_iff r).mp hr with ⟨β, hβ⟩
  refine ⟨a, b, α, β, ha, hb, ?_, ?_, ?_⟩
  · simpa [hα] using hleft.symm
  · simpa [hβ] using hright.symm
  · rw [C.gate_eq 3]
    congr 1
    · simpa [hα] using hleft.symm
    · simpa [hβ] using hright.symm

theorem NormalizedEight.gateFive_useful {C : Circuit 8 8}
    (h : NormalizedEight C) : UsefulAt C (mulTarget 4) 4 :=
  h.suffix_useful 4 (by decide)

theorem NormalizedEight.gateSix_useful {C : Circuit 8 8}
    (h : NormalizedEight C) : UsefulAt C (mulTarget 4) 5 :=
  h.suffix_useful 5 (by decide)


end

end N4
end UnrestrictedBooleanMul
