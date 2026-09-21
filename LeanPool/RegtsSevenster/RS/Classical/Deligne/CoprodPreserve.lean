/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Preservation of coproducts from finite and filtered

A functor preserving finite coproducts and `Finset`-shaped
colimits preserves arbitrary coproducts: the coproduct is the
filtered colimit of its finite subcoproducts, and the functor
preserves every stage and the colimit itself.  Mathlib carries the
existence half of this construction; the preservation half is
supplied here.  The consumer is the tensor product on the
ind-category, which is exact and preserves filtered colimits, and
must be seen to preserve the coend presentations of §3.
-/

namespace RS

open CategoryTheory Limits CoproductsFromFiniteFiltered

universe w v u v' u'

variable {C : Type u}

section

/-- The stagewise comparison morphism at a finite stage is
invertible for a functor preserving finite coproducts. -/
instance isIso_sigmaComparison_stage
    [Category.{v} C] {D : Type u'} [Category.{v'} D] {α : Type w}
    [HasFiniteCoproducts C] [HasFiniteCoproducts D] (G : C ⥤ D)
    [PreservesFiniteCoproducts G]
    (f : α → C)
    (S : Finset (Discrete α)) :
    IsIso (sigmaComparison G fun x : S =>
      (Discrete.functor f).obj x) := by
  rw [← PreservesCoproduct.inv_hom]
  infer_instance

/-- The stage-level comparison computation, restated at the exact
syntactic form of the `Finset` diagram's coproduct families. -/
@[reassoc]
theorem stage_ι_comp
    [Category.{v} C] {D : Type u'} [Category.{v'} D] {α : Type w}
    [HasFiniteCoproducts C] [HasFiniteCoproducts D] (G : C ⥤ D)
    (f : α → C) (S : Finset (Discrete α))
    (x : S) :
    Sigma.ι (fun y : S =>
        (Discrete.functor fun z => G.obj (f z)).obj y) x ≫
      sigmaComparison G (fun y : S => (Discrete.functor f).obj y) =
        G.map (Sigma.ι
          (fun y : S => (Discrete.functor f).obj y) x) :=
  ι_comp_sigmaComparison G _ x

/-- The stagewise coproduct comparisons of a functor preserving
finite coproducts, assembled into an isomorphism of `Finset`
diagrams. -/
noncomputable def liftToFinsetComparison
    [Category.{v} C] {D : Type u'} [Category.{v'} D] {α : Type w}
    [HasFiniteCoproducts C] [HasFiniteCoproducts D] (G : C ⥤ D)
    [PreservesFiniteCoproducts G]
    (f : α → C) :
    liftToFinsetObj (Discrete.functor fun x => G.obj (f x)) ≅
      liftToFinsetObj (Discrete.functor f) ⋙ G := by
  refine NatIso.ofComponents
    (fun S => @asIso _ _ _ _
      (sigmaComparison G fun x : S => (Discrete.functor f).obj x)
      (isIso_sigmaComparison_stage G f S)) ?_
  intro S T h
  show ((Sigma.desc fun y : S =>
      Sigma.ι (fun x : T =>
          (Discrete.functor fun z => G.obj (f z)).obj x)
        ⟨y.1, h.down.down y.2⟩ :
      (∐ fun x : S =>
        (Discrete.functor fun z => G.obj (f z)).obj x) ⟶
      ∐ fun x : T =>
        (Discrete.functor fun z => G.obj (f z)).obj x)) ≫
      sigmaComparison G (fun x : T => (Discrete.functor f).obj x) =
    sigmaComparison G (fun x : S => (Discrete.functor f).obj x) ≫
      G.map ((Sigma.desc fun y : S =>
        Sigma.ι (fun x : T => (Discrete.functor f).obj x)
          ⟨y.1, h.down.down y.2⟩ :
        (∐ fun x : S => (Discrete.functor f).obj x) ⟶
        ∐ fun x : T => (Discrete.functor f).obj x))
  apply Sigma.hom_ext
  intro x
  erw [stage_ι_comp_assoc, ← G.map_comp, Sigma.ι_desc,
    Sigma.ι_desc_assoc, stage_ι_comp]

/-- **Preservation of coproducts from finite and filtered**: a
functor preserving finite coproducts and `Finset`-shaped colimits
preserves every coproduct indexed by `α`. -/
theorem preservesCoproduct_of_finite_and_filtered
    [Category.{v} C] {D : Type u'} [Category.{v'} D] {α : Type w}
    [HasFiniteCoproducts C] [HasFiniteCoproducts D] (G : C ⥤ D)
    [PreservesFiniteCoproducts G]
    [HasColimitsOfShape (Finset (Discrete α)) C]
    [HasColimitsOfShape (Finset (Discrete α)) D]
    [PreservesColimitsOfShape (Finset (Discrete α)) G]
    (f : α → C) :
    PreservesColimit (Discrete.functor f) G := by
  haveI : HasCoproduct f :=
    HasColimit.mk (liftToFinsetColimitCocone (Discrete.functor f))
  haveI : HasCoproduct fun x => G.obj (f x) :=
    HasColimit.mk
      (liftToFinsetColimitCocone (Discrete.functor fun x => G.obj (f x)))
  have hD' : IsColimit ((Cocone.precompose
      (liftToFinsetComparison G f).hom).obj
        (G.mapCocone (finiteSubcoproductsCocone f))) :=
    (IsColimit.precomposeHomEquiv (liftToFinsetComparison G f) _).symm
      (isColimitOfPreserves G (isColimitFiniteSubproductsCocone f))
  have hD2 := isColimitFiniteSubproductsCocone fun x => G.obj (f x)
  let m : finiteSubcoproductsCocone (fun x => G.obj (f x)) ⟶
      (Cocone.precompose (liftToFinsetComparison G f).hom).obj
        (G.mapCocone (finiteSubcoproductsCocone f)) :=
    { hom := sigmaComparison G f
      w := by
        intro S
        show ((Sigma.desc fun s : S =>
            Sigma.ι (fun y => G.obj (f y)) s.1.as :
            (∐ fun x : S =>
              (Discrete.functor fun z => G.obj (f z)).obj x) ⟶
            ∐ fun y => G.obj (f y))) ≫ sigmaComparison G f =
          sigmaComparison G
              (fun x : S => (Discrete.functor f).obj x) ≫
            G.map ((Sigma.desc fun s : S => Sigma.ι f s.1.as :
              (∐ fun x : S => (Discrete.functor f).obj x) ⟶
                ∐ f))
        apply Sigma.hom_ext
        intro x
        erw [Sigma.ι_desc_assoc, ι_comp_sigmaComparison,
          stage_ι_comp_assoc, ← G.map_comp, Sigma.ι_desc]
        rfl }
  haveI : IsIso m := hD2.hom_isIso hD' m
  haveI : IsIso (sigmaComparison G f) := by
    have : IsIso ((Cocone.forget _).map m) := inferInstance
    exact this
  exact PreservesCoproduct.of_iso_comparison G f

/-- Shape form of the preservation of coproducts from finite and
filtered. -/
theorem preservesColimitsOfShape_discrete_of_finite_and_filtered
    [Category.{v} C] {D : Type u'} [Category.{v'} D] {α : Type w}
    [HasFiniteCoproducts C] [HasFiniteCoproducts D] (G : C ⥤ D)
    [PreservesFiniteCoproducts G]
    [HasColimitsOfShape (Finset (Discrete α)) C]
    [HasColimitsOfShape (Finset (Discrete α)) D]
    [PreservesColimitsOfShape (Finset (Discrete α)) G] :
    PreservesColimitsOfShape (Discrete α) G := by
  constructor
  intro F
  haveI := preservesCoproduct_of_finite_and_filtered G
    (F.obj ∘ Discrete.mk)
  exact preservesColimit_of_iso_diagram G Discrete.natIsoFunctor.symm

end

end RS
