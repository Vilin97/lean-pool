/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.CompletedZeta.UnitFundamentalDomain

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open NumberField NumberField.InfinitePlace NumberField.Units
  dirichletUnitTheorem

namespace NumberField.Odlyzko

open mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in
/-- An unit exponent reindex used in the Odlyzko-bound argument. -/
def unitExponentReindex :
    (Fin (rank K) → ℤ) ≃
      ({w : InfinitePlace K // w ≠ w₀} → ℤ) where
  toFun f i := f (equivFinRank.symm i)
  invFun z i := z (equivFinRank i)
  left_inv f := by
    simp
  right_inv z := by
    simp

theorem fundamentalUnitForShift_unitExponentReindex
    (f : Fin (rank K) → ℤ) :
    fundamentalUnitForShift (unitExponentReindex K f) =
      ∏ i, fundSystem K i ^ f i := by
  classical
  exact (Fintype.prod_equiv
    (mixedEmbedding.fundamentalCone.equivFinRank (K := K))
    (fun i ↦ fundSystem K i ^ f i)
    (fun w ↦ fundSystem K (equivFinRank.symm w) ^
      unitExponentReindex K f w)
    (fun _ ↦ by simp [unitExponentReindex])).symm

/-- An unit decomposition map used in the Odlyzko-bound argument. -/
noncomputable def unitDecompositionMap :
    torsion K × ({w : InfinitePlace K // w ≠ w₀} → ℤ) →
      (𝓞 K)ˣ :=
  fun p ↦ p.1 * fundamentalUnitForShift p.2

theorem bijective_unitDecompositionMap :
    Function.Bijective (unitDecompositionMap K) := by
  classical
  constructor
  · rintro ⟨ζ, z⟩ ⟨ζ', z'⟩ h
    let f := (unitExponentReindex K).symm z
    let f' := (unitExponentReindex K).symm z'
    have hfund : fundamentalUnitForShift z =
        ∏ i, fundSystem K i ^ f i := by
      rw [← fundamentalUnitForShift_unitExponentReindex K f]
      simp [f]
    have hfund' : fundamentalUnitForShift z' =
        ∏ i, fundSystem K i ^ f' i := by
      rw [← fundamentalUnitForShift_unitExponentReindex K f']
      simp [f']
    have hu := exist_unique_eq_mul_prod K (unitDecompositionMap K (ζ, z))
    have h₁ : unitDecompositionMap K (ζ, z) =
        ζ * ∏ i, fundSystem K i ^ f i := by
      rw [unitDecompositionMap, hfund]
    have h₂ : unitDecompositionMap K (ζ, z) =
        ζ' * ∏ i, fundSystem K i ^ f' i := by
      calc
        unitDecompositionMap K (ζ, z) =
            unitDecompositionMap K (ζ', z') := h
        _ = ζ' * ∏ i, fundSystem K i ^ f' i := by
          rw [unitDecompositionMap, hfund']
    have hp : (ζ, f) = (ζ', f') := hu.unique h₁ h₂
    apply Prod.ext
    · simp_all
    · apply (unitExponentReindex K).symm.injective
      grind
  · intro u
    obtain ⟨⟨ζ, f⟩, hu, _⟩ := exist_unique_eq_mul_prod K u
    refine ⟨(ζ, unitExponentReindex K f), ?_⟩
    rw [unitDecompositionMap,
      fundamentalUnitForShift_unitExponentReindex]
    simp_all

open scoped Classical in
/-- An unit decomposition equiv used in the Odlyzko-bound argument. -/
def unitDecompositionEquiv :
    torsion K × ({w : InfinitePlace K // w ≠ w₀} → ℤ) ≃
      (𝓞 K)ˣ :=
  Equiv.ofBijective (unitDecompositionMap K)
    (bijective_unitDecompositionMap K)

@[simp]
theorem unitDecompositionEquiv_apply
    (p : torsion K × ({w : InfinitePlace K // w ≠ w₀} → ℤ)) :
    unitDecompositionEquiv K p =
      p.1 * fundamentalUnitForShift p.2 :=
  rfl

end NumberField.Odlyzko
