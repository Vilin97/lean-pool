/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SplittingAlgebra
import LeanPool.RegtsSevenster.RS.Classical.Deligne.FibreExact
import LeanPool.RegtsSevenster.RS.Classical.Deligne.FibreFaithful
import LeanPool.RegtsSevenster.RS.Classical.Deligne.FibreBridge
import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndOfMonoidal

/-!
# The fibre functor over the splitting algebra

Assembling the three properties over the algebra of
`RS.exists_splitting_algebra`: the restriction of the fibre functor
along the Ind-embedding is strong monoidal, it is exact, and it is
faithful once the unit of the algebra is a monomorphism.

The braiding of `Ind C` is hypothesised here, through
`SymmetricCategory (Ind C)`, and is deliberately *not* also
available by transport from a braiding of `C`.  Assuming
`BraidedCategory C` as well would put two unrelated
`BraidedCategory (Ind C)` instances in scope — the transported one
of `RS.Classical.Deligne.IndMonoidal` and the one underlying the
hypothesised symmetry — and `IsCommMonObj 𝔸`, whose commutativity
law is stated against a braiding, would then be a different class
in the variable block from the one the fibre-functor lemmas below
consume.  The variable block therefore names the symmetry of
`Ind C` only, matching `RS.Classical.Deligne.UniversalAlgebra`.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v

variable {C : Type v}

/-- **The restricted fibre functor is strong monoidal** over an
algebra that splits the embedded objects. -/
@[implicit_reducible]
noncomputable def indFibreMonoidal
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [CategoryTheory.Linear ℂ (Ind C)] [MonoidalPreadditive (Ind C)]
    [MonoidalLinear ℂ (Ind C)] [SymmetricCategory (Ind C)]
    [HasCoequalizers (Ind C)]
    [∀ Z : Ind C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft
      Z)] [HasFiniteBiproducts (Ind C)] (L : OddLine (Ind C)) (𝔸 : Ind C)
    [MonObj 𝔸] [IsCommMonObj 𝔸]
    (hsp : SplitsOn L 𝔸 (indOf : C ⥤ Ind C)) :
    ((indOf : C ⥤ Ind C) ⋙ fibreOver L 𝔸).Monoidal :=
  fibreRestrictMonoidal L 𝔸 _ hsp

/-- **The restricted fibre functor is faithful** over an algebra
that splits the embedded objects, provided its unit is a
monomorphism. -/
theorem indFibre_faithful [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [CategoryTheory.Linear ℂ (Ind C)] [MonoidalPreadditive (Ind C)]
    [MonoidalLinear ℂ (Ind C)] [SymmetricCategory (Ind C)]
    [HasFiniteBiproducts (Ind C)] (L : OddLine (Ind C)) (𝔸 : Ind C)
    [MonObj 𝔸] [IsCommMonObj 𝔸]
    (hmono : Mono η[𝔸])
    (hsp : SplitsOn L 𝔸 (indOf : C ⥤ Ind C))
    [∀ Z : Ind C, (tensorRight Z).PreservesMonomorphisms] :
    ((indOf : C ⥤ Ind C) ⋙ fibreFun L 𝔸).Faithful := by
  haveI : (indOf (C := C)).Additive := indOf_additive
  haveI : ((indOf : C ⥤ Ind C) ⋙ fibreFun L 𝔸).Additive :=
    inferInstance
  refine ⟨fun {X Y} f g hfg => ?_⟩
  obtain ⟨p, q, ⟨e⟩⟩ := hsp X
  have h0 : ((indOf : C ⥤ Ind C) ⋙ fibreFun L 𝔸).map (f - g) = 0 := by
    rw [Functor.map_sub, hfg, sub_self]
  have h1 : (indOf : C ⥤ Ind C).map (f - g) = 0 :=
    fibreFun_map_eq_zero L 𝔸 hmono _ e h0
  have h2 : (indOf : C ⥤ Ind C).map f = (indOf : C ⥤ Ind C).map g := by
    rw [Functor.map_sub] at h1
    exact sub_eq_zero.mp h1
  exact (indOf (C := C)).map_injective h2

/-! ## Exactness of the restricted fibre functor -/

section Exact

/-- The embedding carries a short exact sequence of `C` to a short
exact sequence of `Ind C`: it is additive, it preserves limits, and
it preserves finite colimits. -/
theorem indOf_shortExact [SmallCategory C] [Abelian C]
    {S : CategoryTheory.ShortComplex C}
    (hS : S.ShortExact) :
    (S.map (indOf : C ⥤ Ind C)).ShortExact := by
  haveI : (indOf (C := C)).Additive := indOf_additive
  exact hS.map_of_exact (indOf : C ⥤ Ind C)

/-- The restricted fibre functor carries short exact sequences to
short exact sequences, given a base-change section over `𝔸` for
each embedded sequence. -/
theorem indFibre_shortExact [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [MonoidalPreadditive C] [RigidCategory C]
    [CategoryTheory.Linear ℂ (Ind C)] [MonoidalPreadditive (Ind C)]
    [MonoidalLinear ℂ (Ind C)] [SymmetricCategory (Ind C)]
    (L : OddLine (Ind C)) (𝔸 : Ind C) [MonObj 𝔸] [IsCommMonObj 𝔸]
    (hsec : ∀ (S : CategoryTheory.ShortComplex C), S.ShortExact →
      ∃ s : freeMod 𝔸 ((S.map (indOf : C ⥤ Ind C)).X₃) ⟶
            freeMod 𝔸 ((S.map (indOf : C ⥤ Ind C)).X₂),
        s ≫ freeModMap 𝔸 ((S.map (indOf : C ⥤ Ind C)).g) = 𝟙 _)
    (S : CategoryTheory.ShortComplex C) (hS : S.ShortExact) :
    (S.map ((indOf : C ⥤ Ind C) ⋙ fibreFun L 𝔸)).ShortExact := by
  obtain ⟨s, hs⟩ := hsec S hS
  have h := fibreFun_shortExact_of_baseChangeSection L 𝔸
    (indOf_shortExact hS) s hs
  rw [CategoryTheory.ShortComplex.map_comp]
  exact h

/-- **The restricted fibre functor preserves finite limits** over an
algebra that supplies a base-change section for every embedded short
exact sequence. -/
theorem indFibre_preservesFiniteLimits
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [MonoidalPreadditive C] [RigidCategory C]
    [CategoryTheory.Linear ℂ (Ind C)] [MonoidalPreadditive (Ind C)]
    [MonoidalLinear ℂ (Ind C)] [SymmetricCategory (Ind C)]
    (L : OddLine (Ind C)) (𝔸 : Ind C) [MonObj 𝔸] [IsCommMonObj 𝔸]
    (hsec : ∀ (S : CategoryTheory.ShortComplex C), S.ShortExact →
      ∃ s : freeMod 𝔸 ((S.map (indOf : C ⥤ Ind C)).X₃) ⟶
            freeMod 𝔸 ((S.map (indOf : C ⥤ Ind C)).X₂),
        s ≫ freeModMap 𝔸 ((S.map (indOf : C ⥤ Ind C)).g) = 𝟙 _) :
    Limits.PreservesFiniteLimits
      ((indOf : C ⥤ Ind C) ⋙ fibreFun L 𝔸) := by
  haveI : (indOf (C := C)).Additive := indOf_additive
  haveI : ((indOf : C ⥤ Ind C) ⋙ fibreFun L 𝔸).Additive :=
    inferInstance
  exact preservesFiniteLimits_of_shortExact _
    (indFibre_shortExact L 𝔸 hsec)

/-- **The restricted fibre functor preserves finite colimits** under
the same hypothesis; with the previous statement it is exact. -/
theorem indFibre_preservesFiniteColimits
    [SmallCategory C] [MonoidalCategory C] [Abelian C]
    [MonoidalPreadditive C] [RigidCategory C]
    [CategoryTheory.Linear ℂ (Ind C)] [MonoidalPreadditive (Ind C)]
    [MonoidalLinear ℂ (Ind C)] [SymmetricCategory (Ind C)]
    (L : OddLine (Ind C)) (𝔸 : Ind C) [MonObj 𝔸] [IsCommMonObj 𝔸]
    (hsec : ∀ (S : CategoryTheory.ShortComplex C), S.ShortExact →
      ∃ s : freeMod 𝔸 ((S.map (indOf : C ⥤ Ind C)).X₃) ⟶
            freeMod 𝔸 ((S.map (indOf : C ⥤ Ind C)).X₂),
        s ≫ freeModMap 𝔸 ((S.map (indOf : C ⥤ Ind C)).g) = 𝟙 _) :
    Limits.PreservesFiniteColimits
      ((indOf : C ⥤ Ind C) ⋙ fibreFun L 𝔸) := by
  haveI : (indOf (C := C)).Additive := indOf_additive
  haveI : ((indOf : C ⥤ Ind C) ⋙ fibreFun L 𝔸).Additive :=
    inferInstance
  exact preservesFiniteColimits_of_shortExact _
    (indFibre_shortExact L 𝔸 hsec)

end Exact

end RS
