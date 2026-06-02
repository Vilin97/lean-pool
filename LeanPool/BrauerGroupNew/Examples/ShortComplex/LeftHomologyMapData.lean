/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# LeanPool.BrauerGroupNew.Examples.ShortComplex.LeftHomologyMapData

Imported Lean Pool material for `LeanPool.BrauerGroupNew.Examples.ShortComplex.LeftHomologyMapData`.
-/

universe v u

open CategoryTheory

variable (R : Type u) [CommRing R] (S₁ : ShortComplex (ModuleCat.{v} R))
  (S₂ : ShortComplex (ModuleCat R)) (f : S₁ ⟶ S₂)

/-- The map on explicit cycle modules induced by a morphism of short complexes. -/
abbrev φK : ↥(LinearMap.ker (ModuleCat.Hom.hom S₁.g)) →ₗ[R]
    ↥(LinearMap.ker (ModuleCat.Hom.hom S₂.g)) :=
  LinearMap.restrict f.2.hom
    fun x hx ↦ by
      have := (LinearMap.ext_iff.1 <| ModuleCat.hom_ext_iff|>.1 f.5) x
      simp at hx
      simp [hx] at this
      simp [this]

/-- The map on cycles carries boundaries to boundaries. -/
lemma φK_moduleCatToCycles (x : S₁.X₁) :
    φK R S₁ S₂ f (S₁.moduleCatToCycles x) = S₂.moduleCatToCycles (f.τ₁ x) := by
  ext
  have h := LinearMap.ext_iff.1 ((ModuleCat.hom_ext_iff.1 f.comm₁₂).symm) x
  simpa [φK, ShortComplex.moduleCatToCycles] using h

/-- The map on cycles descends to the quotient by boundaries. -/
lemma φK_maps_moduleCatToCycles_range :
    S₁.moduleCatToCycles.range ≤
      Submodule.comap (φK R S₁ S₂ f) S₂.moduleCatToCycles.range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f.τ₁ x, (φK_moduleCatToCycles R S₁ S₂ f x).symm⟩

/-- The induced map on explicit module-category left homology quotients. -/
abbrev φH :
    ModuleCat.of R (LinearMap.ker (ModuleCat.Hom.hom S₁.g) ⧸ LinearMap.range S₁.moduleCatToCycles) ⟶
      .of R (↥(LinearMap.ker (ModuleCat.Hom.hom S₂.g)) ⧸ LinearMap.range S₂.moduleCatToCycles) :=
  ModuleCat.ofHom <| Submodule.mapQ _ _ (φK _ _ _ f) <|
    φK_maps_moduleCatToCycles_range R S₁ S₂ f

/-- The explicit left homology map data for a morphism of short complexes of modules. -/
@[simps]
def LeftHomologyMapData.ofModuleCat :
    ShortComplex.LeftHomologyMapData f
    (ShortComplex.moduleCatLeftHomologyData S₁)
    (ShortComplex.moduleCatLeftHomologyData S₂) where
  φK := ModuleCat.ofHom <| φK R S₁ S₂ f
  φH := φH R S₁ S₂ f
  commi := ModuleCat.hom_ext <| LinearMap.ext fun ⟨x, hx⟩ ↦ rfl
  commf' := ModuleCat.hom_ext <| LinearMap.ext fun x ↦ by
    change φK R S₁ S₂ f (S₁.moduleCatToCycles x) = S₂.moduleCatToCycles (f.τ₁ x)
    exact φK_moduleCatToCycles R S₁ S₂ f x
  commπ := ModuleCat.hom_ext <| LinearMap.ext fun ⟨x, hx⟩ ↦ by
    change
      (Submodule.mapQ _ _ (φK R S₁ S₂ f)
        (φK_maps_moduleCatToCycles_range R S₁ S₂ f)) (Submodule.Quotient.mk ⟨x, hx⟩) =
      Submodule.Quotient.mk ((φK R S₁ S₂ f) ⟨x, hx⟩)
    rw [Submodule.mapQ_apply]

/-- A concrete quotient criterion for quasi-isomorphisms of short complexes of modules. -/
theorem ShortComplex.IsQuasiIsoAt_iff_moduleCat :
    ShortComplex.QuasiIso f ↔
      (∀ a : S₁.X₂, ModuleCat.Hom.hom S₁.g a = 0 →
        ∀ x : S₂.X₁, ConcreteCategory.hom S₂.f x = ModuleCat.Hom.hom f.τ₂ a →
        ∃ y, ConcreteCategory.hom S₁.f y = a) ∧
      ∀ a : S₂.X₂, ModuleCat.Hom.hom S₂.g a = 0 →
        ∃ a_1, ModuleCat.Hom.hom S₁.g a_1 = 0 ∧
        ∃ y, ConcreteCategory.hom S₂.f y = ModuleCat.Hom.hom f.τ₂ a_1 - a := by
  rw [ShortComplex.LeftHomologyMapData.quasiIso_iff (LeftHomologyMapData.ofModuleCat R S₁ S₂ f)]
  rw [ConcreteCategory.isIso_iff_bijective, Function.Bijective]
  congr!
  · rw [injective_iff_map_eq_zero]
    constructor
    · intro hinj a ha x hx
      have hzero : (ConcreteCategory.hom (LeftHomologyMapData.ofModuleCat R S₁ S₂ f).φH)
          (Submodule.Quotient.mk ⟨a, ha⟩) = 0 := by
        change (S₁.moduleCatToCycles.range.mapQ S₂.moduleCatToCycles.range (φK R S₁ S₂ f)
          (φK_maps_moduleCatToCycles_range R S₁ S₂ f)) (Submodule.Quotient.mk ⟨a, ha⟩) =
          0
        rw [Submodule.mapQ_apply]
        rw [Submodule.Quotient.mk_eq_zero]
        exact ⟨x, by ext; simpa [φK] using hx⟩
      have hz := hinj _ hzero
      have hzmem := (Submodule.Quotient.mk_eq_zero S₁.moduleCatToCycles.range).1 hz
      rcases hzmem with ⟨y, hy⟩
      use y
      have hy' := congrArg Subtype.val hy
      simpa using hy'
    · intro h q
      refine Submodule.Quotient.induction_on S₁.moduleCatToCycles.range q ?_
      intro z hq
      rcases z with ⟨a, ha⟩
      change (S₁.moduleCatToCycles.range.mapQ S₂.moduleCatToCycles.range (φK R S₁ S₂ f)
          (φK_maps_moduleCatToCycles_range R S₁ S₂ f)) (Submodule.Quotient.mk ⟨a, ha⟩) =
        0 at hq
      rw [Submodule.mapQ_apply] at hq
      have hzmem := (Submodule.Quotient.mk_eq_zero S₂.moduleCatToCycles.range).1 hq
      rcases hzmem with ⟨x, hx⟩
      have ⟨y, hy⟩ := h a ha x (by
        have hx' := congrArg Subtype.val hx
        simpa [φK] using hx')
      apply (Submodule.Quotient.mk_eq_zero S₁.moduleCatToCycles.range).2
      exact ⟨y, by ext; simpa using hy⟩
  · constructor
    · intro hsurj a ha
      rcases hsurj (Submodule.Quotient.mk ⟨a, ha⟩) with ⟨q, hq⟩
      revert hq
      refine Submodule.Quotient.induction_on S₁.moduleCatToCycles.range q ?_
      intro z hq
      rcases z with ⟨a₁, ha₁⟩
      use a₁, ha₁
      change (S₁.moduleCatToCycles.range.mapQ S₂.moduleCatToCycles.range (φK R S₁ S₂ f)
          (φK_maps_moduleCatToCycles_range R S₁ S₂ f)) (Submodule.Quotient.mk ⟨a₁, ha₁⟩) =
        Submodule.Quotient.mk ⟨a, ha⟩ at hq
      rw [Submodule.mapQ_apply] at hq
      have hmem := (Submodule.Quotient.eq S₂.moduleCatToCycles.range).1 hq
      rcases hmem with ⟨y, hy⟩
      use y
      have hy' := congrArg Subtype.val hy
      simpa [φK] using hy'
    · intro hsurj q
      refine Submodule.Quotient.induction_on S₂.moduleCatToCycles.range q ?_
      intro z
      rcases z with ⟨a, ha⟩
      rcases hsurj a ha with ⟨a₁, ha₁, y, hy⟩
      refine ⟨Submodule.Quotient.mk ⟨a₁, ha₁⟩, ?_⟩
      change (S₁.moduleCatToCycles.range.mapQ S₂.moduleCatToCycles.range (φK R S₁ S₂ f)
          (φK_maps_moduleCatToCycles_range R S₁ S₂ f)) (Submodule.Quotient.mk ⟨a₁, ha₁⟩) =
        Submodule.Quotient.mk ⟨a, ha⟩
      rw [Submodule.mapQ_apply]
      apply (Submodule.Quotient.eq S₂.moduleCatToCycles.range).2
      exact ⟨y, by ext; simpa [φK] using hy⟩
