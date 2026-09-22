/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Unramified.MaximalSubextension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Unramified.Composition
/-!
# Finite support in the maximal unramified field

The maximal unramified subextension is defined as a compositum.  Compactness
of a simple intermediate field and stability under finite composita imply that every one of its
elements already belongs to a single finite unramified subextension.  This is
the finite-support fact used in the maximal-residue theorem.
-/

noncomputable section

universe u

namespace AlgebraicNumberTheory
namespace Valuations

section FiniteSupport

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The base field, viewed as the bottom intermediate field, is finite
unramified.  This supplies the empty finite-compositum case. -/
theorem finiteUnramifiedSubextension_bot
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation) :
    FiniteUnramifiedSubextension v w hExt ⊥ := by
  let w0 := exponentialValuationRestrict w (⊥ : IntermediateField K L)
  let h0 := exponentialValuationRestrict_extends v w hExt
    (⊥ : IntermediateField K L)
  let a : LubinTate.Valuations.exponentialValuationSubring w0 := 0
  let F : Polynomial (LubinTate.Valuations.exponentialValuationSubring v) := Polynomial.X
  have hFmonic : F.Monic := Polynomial.monic_X
  have hFroot :
      (F.map ((algebraMap K (⊥ : IntermediateField K L)).comp
        (LubinTate.Valuations.exponentialValuationSubring v).subtype)).eval
          (a : (⊥ : IntermediateField K L)) = 0 := by
    simp [F, a]
  have hFreduction :
      (F.map (IsLocalRing.residue
        (LubinTate.Valuations.exponentialValuationSubring v))).Separable := by
    simpa [F] using
      (Polynomial.separable_X : (Polynomial.X : Polynomial
        (IsLocalRing.ResidueField
          (LubinTate.Valuations.exponentialValuationSubring v))).Separable)
  have haGen :
      Algebra.adjoin K ({(a : (⊥ : IntermediateField K L))} :
        Set (⊥ : IntermediateField K L)) = ⊤ := by
    apply top_unique
    intro x _hx
    obtain ⟨b, rfl⟩ := (IntermediateField.botEquiv K L).symm.surjective x
    exact algebraMap_mem _ b
  refine ⟨inferInstance, ?_⟩
  exact finiteUnramifiedExtension_of_primitive_separable_integral_model
    v w0 h0 hhens a F hFmonic hFroot hFreduction haGen

/-- A finite supremum of finite unramified intermediate fields is finite
unramified. -/
theorem finiteUnramifiedSubextension_finset_iSup
    {ι : Type*}
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (s : Finset ι) (F : ι → IntermediateField K L)
    (hs : ∀ i ∈ s, FiniteUnramifiedSubextension v w hExt (F i)) :
    FiniteUnramifiedSubextension v w hExt
      (⨆ i : ι, ⨆ (_h : i ∈ s), F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using finiteUnramifiedSubextension_bot v w hExt hhens
  | @insert i s his ih =>
      let E := F i
      have hE := hs i (by simp)
      have hs' : ∀ j ∈ s,
          FiniteUnramifiedSubextension v w hExt (F j) := by
        intro j hjs
        exact hs j (by simp [hjs])
      have hS := ih hs'
      rcases hE with ⟨hfinE, hEunramified⟩
      rcases hS with ⟨hfinS, hSunramified⟩
      let : FiniteDimensional K E := hfinE
      let Ssup : IntermediateField K L :=
        ⨆ j : ι, ⨆ (_h : j ∈ s), F j
      let : FiniteDimensional K Ssup := hfinS
      let hfinTop : FiniteDimensional K
          (E ⊔ Ssup : IntermediateField K L) :=
        IntermediateField.finiteDimensional_sup E Ssup
      have hTop : FiniteUnramifiedSubextension v w hExt
          (E ⊔ Ssup : IntermediateField K L) := by
        refine ⟨hfinTop, ?_⟩
        exact finiteUnramifiedExtension_sup E Ssup
          v w hExt hhens hEunramified hSunramified
      have hsup :
          (⨆ j : ι, ⨆ (_h : j ∈ insert i s), F j) =
            E ⊔ Ssup := by
        apply le_antisymm
        · apply iSup_le
          intro j
          apply iSup_le
          intro hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact le_sup_left
          · exact le_sup_of_le_right
              (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
        · apply sup_le
          · exact le_iSup_of_le i
              (le_iSup_of_le (Finset.mem_insert_self i s) le_rfl)
          · dsimp [Ssup]
            apply iSup_le
            intro j
            apply iSup_le
            intro hj
            exact le_iSup_of_le j
              (le_iSup_of_le (Finset.mem_insert_of_mem hj) le_rfl)
      rw [hsup]
      exact hTop

/-- Every element of the maximal unramified subextension belongs to one
finite unramified intermediate field. -/
theorem exists_finiteUnramifiedSubextension_of_mem_maximal
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    {x : L}
    (hx : x ∈ maximalUnramifiedSubextension v w hExt) :
    ∃ E : IntermediateField K L,
      x ∈ E ∧ FiniteUnramifiedSubextension v w hExt E := by
  classical
  let S := finiteUnramifiedSubextensions v w hExt
  have hxSup : x ∈ ⨆ E : S, (E : IntermediateField K L) := by
    simpa [maximalUnramifiedSubextension, S, sSup_eq_iSup'] using hx
  obtain ⟨s, hxs⟩ := IntermediateField.exists_finset_of_mem_iSup hxSup
  let E : IntermediateField K L :=
    ⨆ U : S, ⨆ (_h : U ∈ s), (U : IntermediateField K L)
  have hEunramified : FiniteUnramifiedSubextension v w hExt E := by
    apply finiteUnramifiedSubextension_finset_iSup
      v w hExt hhens s (fun U : S ↦ (U : IntermediateField K L))
    intro U hUs
    exact U.property
  exact ⟨E, hxs, hEunramified⟩

end FiniteSupport

end Valuations
end AlgebraicNumberTheory

end
