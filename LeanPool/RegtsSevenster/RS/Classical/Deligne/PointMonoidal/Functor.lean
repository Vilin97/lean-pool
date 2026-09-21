/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.PointMonoidal.Coherence

/-!
# The monoidal fibre functor at a complex point

The comparison and the unit of
[Comparison.lean](Comparison.lean), with the coherence proved in
[Coherence.lean](Coherence.lean), assemble the fibre functor at a
ℂ-point into a lax monoidal functor; both comparisons being
invertible it is strong monoidal, and it is braided as soon as the
functor upstream of it is.  Applied to a splitting algebra this
gives a braided fibre functor out of the ambient category.

## Contents

* `RS.superVectFunctorLaxMonoidal`, `RS.superVectFunctorMonoidal`:
  the fibre functor at a point is lax monoidal, and strong monoidal
  as soon as the functor upstream of it is.
* `RS.isIso_superVectHom`: the fibre functor carries an
  isomorphism to an isomorphism.
* `RS.superVectFunctorBraided`: the fibre functor at a point is
  braided as soon as the functor upstream of it is.
* `RS.nonempty_braided_deligneFibre`: the fibre functor of a
  splitting algebra at a complex point is braided.
-/

namespace RS

open CategoryTheory MonoidalCategory
open SuperCommAlgebra (pointMod)
open SuperCommAlgebra.Mod

universe u

/-! ## The lax monoidal structure of the fibre functor -/

section LaxMonoidal

open scoped TensorProduct

variable {S : SuperCommAlgebra.{u, u}} (P : SuperPoint S)

/-- **The base change of a tensor product is finite dimensional**
in even degree as soon as the two factors are: the comparison is a
linear equivalence onto it. -/
instance finiteDimensional_tensor_base_even (M N : S.Mod.{u, u, u, u})
    [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).odd] :
    FiniteDimensional ℂ ((M.tensor N).tensor (pointMod P)).even :=
  (LinearEquiv.ofBijective (superVectMuEvenRaw P M N)
    (superVectMuEvenRaw_bijective P M N)).finiteDimensional

/-- **The base change of a tensor product is finite dimensional**
in odd degree. -/
instance finiteDimensional_tensor_base_odd (M N : S.Mod.{u, u, u, u})
    [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).odd] :
    FiniteDimensional ℂ ((M.tensor N).tensor (pointMod P)).odd :=
  (LinearEquiv.ofBijective (superVectMuOddRaw P M N)
    (superVectMuOddRaw_bijective P M N)).finiteDimensional

/-- The same, for the monoidal notation. -/
instance finiteDimensional_tensorObj_base_even (M N : S.Mod.{u, u, u, u})
    [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).odd] :
    FiniteDimensional ℂ ((M ⊗ N).tensor (pointMod P)).even :=
  finiteDimensional_tensor_base_even P M N

/-- The same in odd degree, for the monoidal notation. -/
instance finiteDimensional_tensorObj_base_odd (M N : S.Mod.{u, u, u, u})
    [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).odd] :
    FiniteDimensional ℂ ((M ⊗ N).tensor (pointMod P)).odd :=
  finiteDimensional_tensor_base_odd P M N

variable {E : Type u₂}

/-- **The fibre functor at a point is lax monoidal** whenever the
functor it is applied to is: the comparison of the base change is
composed with the comparison upstream. -/
@[implicit_reducible]
noncomputable def superVectFunctorLaxMonoidal
    [Category.{v₂} E] [MonoidalCategory E] (G : E ⥤ S.Mod.{u, u, u, u})
    [G.LaxMonoidal]
    [hE : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).even]
    [hO : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).odd]
    [FiniteDimensional ℂ ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod
      P)).even]
    [FiniteDimensional ℂ ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod
      P)).odd] :
    (superVectFunctor P G hE hO).LaxMonoidal where
  ε := superVectEps P ≫ superVectHom P (Functor.LaxMonoidal.ε G)
  μ X Y := superVectMu P (G.obj X) (G.obj Y) ≫
    superVectHom P (Functor.LaxMonoidal.μ G X Y)
  μ_natural_left {X Y} f X' := by
    simp only [superVectFunctor_map, superVectFunctor_obj]
    rw [← Category.assoc, superVectMu_naturality_left,
      Category.assoc, ← superVectHom_comp,
      Functor.LaxMonoidal.μ_natural_left, superVectHom_comp,
      ← Category.assoc]
  μ_natural_right X' {X Y} f := by
    simp only [superVectFunctor_map, superVectFunctor_obj]
    rw [← Category.assoc, superVectMu_naturality_right,
      Category.assoc, ← superVectHom_comp,
      Functor.LaxMonoidal.μ_natural_right, superVectHom_comp,
      ← Category.assoc]
  associativity X Y Z := by
    simp only [superVectFunctor_map, superVectFunctor_obj,
      MonoidalCategory.comp_whiskerRight, Category.assoc]
    rw [← Category.assoc (superVectHom P
      (Functor.LaxMonoidal.μ G X Y) ▷ _),
      superVectMu_naturality_left]
    simp only [Category.assoc, ← superVectHom_comp]
    rw [Functor.LaxMonoidal.associativity]
    simp only [superVectHom_comp, modTensorObj]
    rw [superVectMu_associativity_assoc]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [← Category.assoc (toSuperVect P (G.obj X) ◁
      superVectHom P (Functor.LaxMonoidal.μ G Y Z)),
      superVectMu_naturality_right]
    simp only [Category.assoc]
    rfl
  left_unitality X := by
    simp only [superVectFunctor_map, superVectFunctor_obj,
      MonoidalCategory.comp_whiskerRight, Category.assoc]
    rw [← Category.assoc (superVectHom P (Functor.LaxMonoidal.ε G)
      ▷ _), superVectMu_naturality_left]
    simp only [Category.assoc, ← superVectHom_comp]
    rw [← Functor.LaxMonoidal.left_unitality]
    exact superVectMu_left_unitality P (G.obj X)
  right_unitality X := by
    simp only [superVectFunctor_map, superVectFunctor_obj,
      MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [← Category.assoc (toSuperVect P (G.obj X) ◁
      superVectHom P (Functor.LaxMonoidal.ε G)),
      superVectMu_naturality_right]
    simp only [Category.assoc, ← superVectHom_comp]
    rw [← Functor.LaxMonoidal.right_unitality]
    exact superVectMu_right_unitality P (G.obj X)

/-- **Base change carries an isomorphism to an isomorphism.** -/
instance isIso_superVectHom {M N : S.Mod.{u, u, u, u}} (u : M ⟶ N)
    [IsIso u]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).odd] :
    IsIso (superVectHom P u) :=
  ⟨superVectHom P (inv u), by
      rw [← superVectHom_comp, IsIso.hom_inv_id, superVectHom_id],
    by rw [← superVectHom_comp, IsIso.inv_hom_id,
      superVectHom_id]⟩

end LaxMonoidal

section StrongMonoidal

open scoped TensorProduct

variable {S : SuperCommAlgebra.{u, u}} (P : SuperPoint S) {E : Type u₂}

/-- **The fibre functor at a point is strong monoidal** whenever
the functor it is applied to is: both comparisons are invertible,
the one of the base change unconditionally. -/
@[implicit_reducible]
noncomputable def superVectFunctorMonoidal
    [Category.{v₂} E] [MonoidalCategory E] (G : E ⥤ S.Mod.{u, u, u, u})
    [G.Monoidal]
    [hE : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).even]
    [hO : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).odd]
    [FiniteDimensional ℂ ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod
      P)).even]
    [FiniteDimensional ℂ ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod
      P)).odd] :
    (superVectFunctor P G hE hO).Monoidal := by
  letI : (superVectFunctor P G hE hO).LaxMonoidal :=
    superVectFunctorLaxMonoidal P G
  haveI : IsIso (Functor.LaxMonoidal.ε G) :=
    ⟨Functor.OplaxMonoidal.η G, Functor.Monoidal.ε_η G,
      Functor.Monoidal.η_ε G⟩
  haveI : ∀ X Y, IsIso (Functor.LaxMonoidal.μ G X Y) := fun X Y =>
    ⟨Functor.OplaxMonoidal.δ G X Y, Functor.Monoidal.μ_δ G X Y,
      Functor.Monoidal.δ_μ G X Y⟩
  haveI : IsIso (Functor.LaxMonoidal.ε
      (superVectFunctor P G hE hO)) :=
    inferInstanceAs (IsIso (superVectEps P ≫
      superVectHom P (Functor.LaxMonoidal.ε G)))
  haveI : ∀ X Y, IsIso (Functor.LaxMonoidal.μ
      (superVectFunctor P G hE hO) X Y) := fun X Y =>
    inferInstanceAs (IsIso (superVectMu P (G.obj X) (G.obj Y) ≫
      superVectHom P (Functor.LaxMonoidal.μ G X Y)))
  exact Functor.Monoidal.ofLaxMonoidal _

end StrongMonoidal

/-! ## The braided structure of the fibre functor -/

section BraidedStructure

open scoped TensorProduct

variable {S : SuperCommAlgebra.{u, u}} (P : SuperPoint S) {E : Type u₂}

/-- **The fibre functor at a point is braided** whenever the functor
it is applied to is: the comparison of the base change intertwines
the braidings, and so does the comparison upstream. -/
@[implicit_reducible]
noncomputable def superVectFunctorBraided
    [Category.{v₂} E] [MonoidalCategory E] [BraidedCategory E]
    (G : E ⥤ S.Mod.{u, u, u, u}) [G.Braided]
    [hE : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).even]
    [hO : ∀ X, FiniteDimensional ℂ ((G.obj X).tensor (pointMod P)).odd]
    [FiniteDimensional ℂ ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod
      P)).even]
    [FiniteDimensional ℂ ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod
      P)).odd] :
    (superVectFunctor P G hE hO).Braided where
  toMonoidal := superVectFunctorMonoidal P G
  braided X Y := by
    show (superVectMu P (G.obj X) (G.obj Y) ≫
        superVectHom P (Functor.LaxMonoidal.μ G X Y)) ≫
      superVectHom P (G.map (β_ X Y).hom) = _
    simp only [Category.assoc, ← superVectHom_comp]
    rw [Functor.LaxBraided.braided]
    simp only [superVectHom_comp]
    rw [superVectMu_braiding_assoc]
    rfl

end BraidedStructure

/-! ## The fibre functor of a splitting algebra is braided -/

section DeligneFibreBraided

open scoped MonObj

variable {C : Type v}

/-- **The fibre functor of a splitting algebra at a complex point is
braided.**  Upstream, the restriction of the fibre functor along the
embedding is strong monoidal and lax braided; downstream, base
change at the point is strong monoidal and intertwines the Koszul
sign of the super vector spaces with the sign of the braiding of the
super modules. -/
theorem nonempty_braided_deligneFibre
    [SmallCategory C] [MonoidalCategory C] [SymmetricCategory C] [Abelian C]
    [RigidCategory C] [MonoidalPreadditive C]
    [CategoryTheory.Linear ℂ (Ind C)] [MonoidalLinear ℂ (Ind C)]
    (L : OddLine (Ind C)) (𝔸 : Ind C) [MonObj 𝔸] [IsCommMonObj 𝔸]
    (hsp : SplitsOn L 𝔸 (indOf : C ⥤ Ind C))
    (pt : SuperPoint (gammaAlgebra (Ind C) L 𝔸)) :
    Nonempty (deligneFibre L 𝔸 hsp pt).Braided := by
  letI : ((indOf : C ⥤ Ind C) ⋙ fibreOver L 𝔸).Braided :=
    { toMonoidal := indFibreMonoidal L 𝔸 hsp
      braided := Functor.LaxBraided.braided }
  haveI hE : ∀ X, FiniteDimensional ℂ
      ((((indOf : C ⥤ Ind C) ⋙ fibreOver L 𝔸).obj X).tensor
        (pointMod pt)).even :=
    finiteDimensional_indFibre_even L 𝔸 hsp pt
  haveI hO : ∀ X, FiniteDimensional ℂ
      ((((indOf : C ⥤ Ind C) ⋙ fibreOver L 𝔸).obj X).tensor
        (pointMod pt)).odd :=
    finiteDimensional_indFibre_odd L 𝔸 hsp pt
  exact ⟨superVectFunctorBraided pt
    ((indOf : C ⥤ Ind C) ⋙ fibreOver L 𝔸)⟩

end DeligneFibreBraided

end RS
