/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.CohomologyBridge
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Hilbert90
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ValuationHerbrand
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ValueGroupCohomology

/-! # Field Units Herbrand -/
namespace LocalClassFieldTheory
open CyclicCohomology

open LocalFieldTheory

/-!
# The field-unit calculation in the local class-field-axiom theorem

This file proves the final Herbrand-quotient calculation for the local
class-field axiom. Its only input beyond the local-field hypotheses is the
preceding normal-basis calculation `h(G, O_Lˣ) = 1` for the actual action on
integer units.
-/

noncomputable section

open scoped ValuativeRel
open CyclicCohomology.ProfiniteCohomology.Herbrand
open IsNonarchimedeanLocalField

variable (K L : Type) [Field K] [ValuativeRel K]
  [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure (ValuativeRel.valuation L).integer
    (ValuativeRel.valuation K).integer L]

omit [IsGalois K L] in
/-- Finiteness of actual unit Tate `H⁰`, derived from the finite Herbrand
quotients in the valuation exact sequence and transported across the genuine
comparison equivalence. -/
theorem unitsTateH0FiniteOfIntegerUnitsHerbrand
    (g : Gal(L/K))
    (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g)
    (hU :
      letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
      HerbrandQuotientDefined (Gal(L/K))
        (ValuativeRel.valuation L).integerˣ g) :
    Finite (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := galoisGroupFieldUnitsMulDistribMulAction K L
  let := galoisGroupValueGroupMulDistribMulAction K L
  obtain ⟨hField, _⟩ :=
    valuationHerbrand_multiplicativity_of_integerUnits_defined K L g hg hU
  let : Finite (HerbrandH0 (Gal(L/K)) Lˣ) := hField.1
  exact Finite.of_equiv (HerbrandH0 (Gal(L/K)) Lˣ)
    (herbrandH0EquivTateCohomologyZero K L)

/-- Final Herbrand calculation for the local class-field axiom.  Multiplicativity for the
valuation sequence, the normal-basis result `h(G,O_Lˣ)=1`, the value-group
calculation, and Hilbert 90 imply the two asserted cardinalities for the
actual Tate cohomology of `Lˣ`. -/
theorem fieldUnits_tate_card_of_integerUnits_herbrand_eq_one
    (g : Gal(L/K))
    (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g)
    (hU :
      letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
      HerbrandQuotientDefined (Gal(L/K))
        (ValuativeRel.valuation L).integerˣ g)
    (hU_one :
      letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
      @herbrandQuotient (Gal(L/K))
          (ValuativeRel.valuation L).integerˣ _ _ _
          (galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L)
          g hU.1 hU.2 = 1) :
    letI := unitsTateH0FiniteOfIntegerUnitsHerbrand K L g hg hU
    Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) = Module.finrank K L ∧
      Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) = 1 := by
  let := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let := galoisGroupFieldUnitsMulDistribMulAction K L
  let := galoisGroupValueGroupMulDistribMulAction K L
  let hZ : HerbrandQuotientDefined
      (Gal(L/K)) (Multiplicative Int) g :=
    galoisGroupValueGroup_herbrandQuotientDefined K L g
  rcases valuationHerbrand_multiplicativity_of_integerUnits_defined
      K L g hg hU with ⟨hField, hmult⟩
  let : Finite (HerbrandH0 (Gal(L/K)) Lˣ) := hField.1
  let : Finite (HerbrandHMinusOne (Gal(L/K)) Lˣ g) := hField.2
  let : Finite
      (HerbrandH0 (Gal(L/K)) (Multiplicative Int)) := hZ.1
  let : Finite
      (HerbrandHMinusOne (Gal(L/K)) (Multiplicative Int) g) := hZ.2
  have hZ0 :
      Nat.card (HerbrandH0 (Gal(L/K)) (Multiplicative Int)) =
        Module.finrank K L :=
    galoisGroupValueGroup_herbrandH0_card_eq_finrank K L
  have hZm1 :
      Nat.card (HerbrandHMinusOne
        (Gal(L/K)) (Multiplicative Int) g) = 1 :=
    galoisGroupValueGroup_herbrandHMinusOne_card_eq_one K L g
  have hZ_one :
      @herbrandQuotient (Gal(L/K)) (Multiplicative Int) _ _ _
          (galoisGroupValueGroupMulDistribMulAction K L) g hZ.1 hZ.2 =
        (Module.finrank K L : ℚ) := by
    rw [herbrandQuotient_eq_card_ratio, hZ0, hZm1]
    simp
  have hm1_actual :
      Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) = 1 :=
    unitsTateHminusOne_card_eq_one K L g hg
  have hm1_field :
      Nat.card (HerbrandHMinusOne (Gal(L/K)) Lˣ g) = 1 := by
    exact (Nat.card_congr
      (herbrandHminusOneEquivUnitsTateHminusOne K L g hg)).trans hm1_actual
  have hField_quotient :
      @herbrandQuotient (Gal(L/K)) Lˣ _ _ _
          (galoisGroupFieldUnitsMulDistribMulAction K L)
          g hField.1 hField.2 = (Module.finrank K L : ℚ) := by
    rw [hmult, hU_one, hZ_one]
    simp
  have h0_field_rat :
      (Nat.card (HerbrandH0 (Gal(L/K)) Lˣ) : ℚ) =
        (Module.finrank K L : ℚ) := by
    rw [← hField_quotient, herbrandQuotient_eq_card_ratio, hm1_field]
    simp
  have h0_field :
      Nat.card (HerbrandH0 (Gal(L/K)) Lˣ) = Module.finrank K L := by
    exact_mod_cast h0_field_rat
  constructor
  · exact
      (Nat.card_congr (herbrandH0EquivTateCohomologyZero K L)).symm.trans h0_field
  · exact hm1_actual

end
end LocalClassFieldTheory
