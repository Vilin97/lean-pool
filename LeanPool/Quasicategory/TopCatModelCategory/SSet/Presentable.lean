/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import LeanPool.Quasicategory.TopCatModelCategory.SSet.IsFiniteCoproducts
import LeanPool.Quasicategory.TopCatModelCategory.SSet.EffectiveEpi
import LeanPool.Quasicategory.TopCatModelCategory.SSet.DimensionProd
import Mathlib.CategoryTheory.Presentable.Limits

universe u

open CategoryTheory Limits Simplicial Opposite

attribute [local instance] Cardinal.fact_isRegular_aleph0

namespace SSet

@[simps!]
def stdSimplex.coyonedaObjIso (n : SimplexCategory) :
    coyoneda.obj (op (stdSimplex.{u}.obj n)) ≅ (evaluation _ _).obj (op n) :=
  NatIso.ofComponents (fun X ↦ yonedaEquiv.toIso)

variable (X : SSet.{u})

noncomputable abbrev nonDegenerateπSrc : SSet.{u} :=
  ∐ (fun (⟨n, _⟩ : (Σ (_d : ℕ), X.nonDegenerate _d)) ↦ Δ[n])

noncomputable def nonDegenerateπSrcι {n : ℕ} (x : X.nonDegenerate n) :
    Δ[n] ⟶ X.nonDegenerateπSrc :=
  Sigma.ι (fun (⟨n, _⟩ : (Σ (_d : ℕ), X.nonDegenerate _d)) ↦ Δ[n]) ⟨n,x⟩

noncomputable def nonDegenerateπ :
    nonDegenerateπSrc X ⟶ X :=
  Sigma.desc (fun ⟨_, x⟩ ↦ yonedaEquiv.symm x.1)

@[reassoc (attr := simp)]
lemma nonDegenerateπSrcι_π {n : ℕ} (x : X.nonDegenerate n) :
    X.nonDegenerateπSrcι x ≫ X.nonDegenerateπ = yonedaEquiv.symm x.1 :=
  Sigma.ι_desc _ _

instance : Epi X.nonDegenerateπ := by
  rw [Subpresheaf.epi_iff_range_eq_top]
  apply le_antisymm (by simp)
  rw [Subcomplex.le_iff_contains_nonDegenerate]
  intro n x hx
  simp only [Subpresheaf.range_obj, Set.mem_range]
  refine ⟨yonedaEquiv (X.nonDegenerateπSrcι x), ?_⟩
  rw [← SSet.yonedaEquiv_comp, nonDegenerateπSrcι_π, Equiv.apply_symm_apply]

noncomputable def nonDegenerateCofork :
    Cofork (nonDegenerateπ _ ≫ pullback.fst X.nonDegenerateπ X.nonDegenerateπ)
      (nonDegenerateπ _ ≫ pullback.snd X.nonDegenerateπ X.nonDegenerateπ) :=
  Cofork.ofπ X.nonDegenerateπ (by simp [pullback.condition])

noncomputable def isColimitNonDegenerateCofork : IsColimit X.nonDegenerateCofork :=
  isCoequalizerOfEpiOfIsPullback _ (IsPullback.of_hasPullback _ _) _

instance (n : ℕ) : IsCardinalPresentable (Δ[n] : SSet.{u}) Cardinal.aleph0.{u} where
  preservesColimitOfShape J _ _ := by
    apply preservesColimitsOfShape_of_natIso (stdSimplex.coyonedaObjIso ⦋n⦌).symm

lemma isCardinalPresentable_coproduct {ι : Type u} [Finite ι] {X : ι → SSet.{u}}
    (c : Cofan X) (hc : IsColimit c) [∀ i, IsCardinalPresentable (X i) Cardinal.aleph0.{u}] :
    IsCardinalPresentable c.pt Cardinal.aleph0.{u} := by
  apply (config := { allowSynthFailures := true})
    isCardinalPresentable_of_isColimit' _ hc
  · rwa [hasCardinalLT_arrow_discrete_iff, hasCardinalLT_aleph0_iff]
  · rintro ⟨i⟩
    dsimp
    infer_instance

instance {ι : Type u} [Finite ι] {X : ι → SSet.{u}}
    [∀ i, IsCardinalPresentable (X i) Cardinal.aleph0.{u}] :
    IsCardinalPresentable (∐ X) Cardinal.aleph0.{u} :=
  isCardinalPresentable_coproduct _ (colimit.isColimit (Discrete.functor X))

instance [X.IsFinite] : IsCardinalPresentable X Cardinal.aleph0.{u} := by
  apply (config := { allowSynthFailures := true})
    isCardinalPresentable_of_isColimit' _ (X.isColimitNonDegenerateCofork)
  · simp
    infer_instance
  · rintro (_ | _) <;> dsimp <;> infer_instance

end SSet
