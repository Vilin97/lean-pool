/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.CountableDescent

/-!
# Embedded images from finite length

`RS.IndImageEmbedded` — the image in `Ind C` of a map out of an
embedded object is again embedded — is carried as a hypothesis by
`RS.Classical.Deligne.CountableDescent` and discharged here from
finite length: if every object of `C` carries a bound on the
length of the chains in its subobject order, then every such image is
embedded.

The argument.  A map `f : indOf.obj Y ⟶ Z` factors through a stage of
the chosen presentation of `Z` (`RS.exists_presStage_factor`), say as
`indOf.map g ≫ presStage Z i`.  The stage may be advanced along any
`α : i ⟶ j`, and advancing it only enlarges the kernel of the
composite `g ≫ F.map α` in the subobject order of `Y`.  Finite length
makes that order satisfy the ascending chain condition
(`RS.exists_maximal_of_lengthLE`), so the kernel may be taken maximal,
at a stage `j₀`; write `g₀` for the map to that stage.

Maximality says that no further advance of the stage enlarges the
kernel, and that is exactly what makes the image of `g₀` embed into
`Z`: the map `indOf.map (image.ι g₀) ≫ presStage Z j₀` is a
monomorphism.  Monomorphisms of ind-objects are detected on the
embedded objects (`RS.mono_of_hom_indOf_injective`), the detection
brings the question back to a single stage of the presentation, and
there `RS.mono_of_kernelSubobject_comp_le` settles it inside `C`.  The
embedding preserves finite colimits, so the other half of the
factorisation of `g₀` stays an epimorphism, and `f` acquires a strong
epi–mono factorisation through `indOf.obj (image g₀)`; uniqueness of
such factorisations identifies the image of `f` with it.
-/

namespace RS

open CategoryTheory Limits

universe w v u

/-! ## Finite length is the ascending chain condition

`RS.LengthLE Y N` forbids strictly increasing chains of `N + 2`
subobjects of `Y`.  A family of subobjects without a maximal member
would generate an infinite strictly increasing chain, so it forbids
that too. -/

section Order

variable {C : Type u}

/-- **Finite length gives maximal members**: if the subobject order
of `Y` carries no strictly increasing chain of `N + 2` terms, then
every nonempty family of subobjects of `Y` has a maximal member. -/
theorem exists_maximal_of_lengthLE [Category.{w} C]
    {Y : C} {N : ℕ} (hY : LengthLE Y N)
    {S : Set (Subobject Y)} (hS : S.Nonempty) :
    ∃ P ∈ S, ∀ Q ∈ S, P ≤ Q → Q ≤ P := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨P₀, hP₀⟩ := hS
  have hstep : ∀ x : S, ∃ y : S, (x : Subobject Y) < (y : Subobject Y) := by
    rintro ⟨x, hx⟩
    obtain ⟨Q, hQ, hxQ, hQx⟩ := hcon x hx
    exact ⟨⟨Q, hQ⟩, lt_of_le_of_ne hxQ (fun he => hQx (le_of_eq he.symm))⟩
  choose next hnext using hstep
  have hchain : StrictMono
      (fun n : ℕ => ((next^[n] (⟨P₀, hP₀⟩ : S) : S) : Subobject Y)) := by
    refine strictMono_nat_of_lt_succ (fun n => ?_)
    have hsucc : next^[n + 1] (⟨P₀, hP₀⟩ : S) =
        next (next^[n] (⟨P₀, hP₀⟩ : S)) :=
      Function.iterate_succ_apply' next n _
    rw [hsucc]
    exact hnext _
  exact hY (fun k => ((next^[k.val] (⟨P₀, hP₀⟩ : S) : S) : Subobject Y))
    (fun a b hab => hchain hab)

end Order

/-! ## The stable-kernel criterion for a monomorphism

A map `f` followed by `g` has a kernel at least that of `f`.  When
the two kernels agree, the mono half of the image factorisation of
`f` survives postcomposition with `g`: the kernel of `image.ι f ≫ g`
is pulled back along the epi half to the common kernel, and an
epimorphism cancels. -/

section Ambient

variable {C : Type u}

/-- Postcomposition only enlarges the kernel. -/
theorem kernelSubobject_le_comp [Category.{w} C] [Abelian C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    kernelSubobject f ≤ kernelSubobject (f ≫ g) :=
  Subobject.le_of_factors
    ((kernelSubobject_factors_iff (f ≫ g)
      (kernelSubobject f).arrow).mpr (by
        rw [← Category.assoc, kernelSubobject_arrow_comp, zero_comp]))

/-- **The stable-kernel criterion**: if postcomposing `f` with `g`
does not enlarge the kernel of `f`, then the mono half of the image
factorisation of `f` remains a monomorphism after postcomposition
with `g`. -/
theorem mono_of_kernelSubobject_comp_le [Category.{w} C] [Abelian C]
    {X Y Z : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) (h : kernelSubobject (f ≫ g) ≤ kernelSubobject f) :
    Mono (image.ι f ≫ g) := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro T x hx
  have hcond : pullback.fst x (factorThruImage f) ≫ x =
      pullback.snd x (factorThruImage f) ≫ factorThruImage f :=
    pullback.condition
  have hker : pullback.snd x (factorThruImage f) ≫ (f ≫ g) = 0 := by
    calc pullback.snd x (factorThruImage f) ≫ (f ≫ g)
        = (pullback.snd x (factorThruImage f) ≫ factorThruImage f) ≫
            (image.ι f ≫ g) := by
          rw [Category.assoc, ← Category.assoc (factorThruImage f),
            image.fac]
      _ = (pullback.fst x (factorThruImage f) ≫ x) ≫
            (image.ι f ≫ g) := by rw [hcond]
      _ = pullback.fst x (factorThruImage f) ≫
            (x ≫ (image.ι f ≫ g)) := Category.assoc _ _ _
      _ = 0 := by rw [hx, comp_zero]
  have hfib : pullback.snd x (factorThruImage f) ≫ f = 0 :=
    (kernelSubobject_factors_iff f _).mp
      (Subobject.factors_of_le _ h
        ((kernelSubobject_factors_iff (f ≫ g) _).mpr hker))
  have hzero : pullback.fst x (factorThruImage f) ≫
      (x ≫ image.ι f) = 0 := by
    rw [← Category.assoc, hcond, Category.assoc, image.fac, hfib]
  have hxι : x ≫ image.ι f = 0 :=
    (cancel_epi (pullback.fst x (factorThruImage f))).mp
      (hzero.trans (comp_zero).symm)
  exact (cancel_mono (image.ι f)).mp (hxι.trans (zero_comp).symm)

end Ambient

/-! ## Embedded images

The main theorem: finite length discharges `RS.IndImageEmbedded`. -/

section Embedded

variable {C : Type v}

/-- Two maps out of an embedded object into a stage of the
presentation of an ind-object which agree in the ind-object already
agree at a later stage — the merging half of compactness, read at the
structural maps of the presentation. -/
theorem exists_stage_comp_eq_of_presStage [SmallCategory C]
    {Z : Ind C} {W : C}
    {j : Z.presentation.I} (a b : indOf.obj W ⟶ indOf.obj
      (Z.presentation.F.obj j))
    (hab : a ≫ presStage Z j = b ≫ presStage Z j) :
    ∃ (k : Z.presentation.I) (β : j ⟶ k),
      a ≫ indOf.map (Z.presentation.F.map β) =
        b ≫ indOf.map (Z.presentation.F.map β) := by
  have hcancel : a ≫ colimit.ι (presDiagram Z) j =
      b ≫ colimit.ι (presDiagram Z) j := by
    refine (cancel_mono (Ind.colimitPresentationCompYoneda Z).hom).mp ?_
    calc (a ≫ colimit.ι (presDiagram Z) j) ≫
          (Ind.colimitPresentationCompYoneda Z).hom
        = a ≫ presStage Z j := Category.assoc _ _ _
      _ = b ≫ presStage Z j := hab
      _ = (b ≫ colimit.ι (presDiagram Z) j) ≫
          (Ind.colimitPresentationCompYoneda Z).hom :=
        (Category.assoc _ _ _).symm
  obtain ⟨k, β, hβ⟩ :=
    (comp_ι_eq_comp_ι_iff (presDiagram Z) W a b).mp hcancel
  exact ⟨k, β, hβ⟩

/-- **Embedded images from finite length.**  If every object of `C`
has a bound on the length of the chains in its subobject order, then
the image in `Ind C` of a map out of an embedded object is again
embedded. -/
theorem indImageEmbedded_of_lengthLE [SmallCategory C] [Abelian C]
    (hlen : ∀ Z : C, ∃ N, LengthLE Z N) : IndImageEmbedded C := by
  classical
  intro Y Z f
  obtain ⟨N, hN⟩ := hlen Y
  obtain ⟨i, g, hg⟩ := exists_presStage_factor Z f
  obtain ⟨P₀, hP₀mem, hmax⟩ := exists_maximal_of_lengthLE hN
    (S := {P : Subobject Y | ∃ (j : Z.presentation.I) (α : i ⟶ j),
      P = kernelSubobject (g ≫ Z.presentation.F.map α)})
    ⟨kernelSubobject (g ≫ Z.presentation.F.map (𝟙 i)), i, 𝟙 i, rfl⟩
  obtain ⟨j₀, α₀, hP₀⟩ := hP₀mem
  subst hP₀
  -- The map to the maximal stage, and the factorisation of `f`.
  have hf : indOf.map (g ≫ Z.presentation.F.map α₀) ≫
      presStage Z j₀ = f := by
    rw [CategoryTheory.Functor.map_comp, Category.assoc,
      presStage_naturality, hg]
  -- Maximality: advancing the stage no longer enlarges the kernel.
  have hstable : ∀ (k : Z.presentation.I) (β : j₀ ⟶ k),
      kernelSubobject ((g ≫ Z.presentation.F.map α₀) ≫
          Z.presentation.F.map β) ≤
        kernelSubobject (g ≫ Z.presentation.F.map α₀) := by
    intro k β
    have hcomp : g ≫ Z.presentation.F.map (α₀ ≫ β) =
        (g ≫ Z.presentation.F.map α₀) ≫ Z.presentation.F.map β := by
      rw [CategoryTheory.Functor.map_comp, Category.assoc]
    have hmem : kernelSubobject (g ≫ Z.presentation.F.map (α₀ ≫ β)) ∈
        {P : Subobject Y | ∃ (j : Z.presentation.I) (α : i ⟶ j),
          P = kernelSubobject (g ≫ Z.presentation.F.map α)} :=
      ⟨k, α₀ ≫ β, rfl⟩
    have hle : kernelSubobject (g ≫ Z.presentation.F.map α₀) ≤
        kernelSubobject (g ≫ Z.presentation.F.map (α₀ ≫ β)) :=
      (congrArg (fun t : Y ⟶ Z.presentation.F.obj k =>
          kernelSubobject t) hcomp.symm) ▸
        kernelSubobject_le_comp (g ≫ Z.presentation.F.map α₀)
          (Z.presentation.F.map β)
    exact (congrArg (fun t : Y ⟶ Z.presentation.F.obj k =>
      kernelSubobject t) hcomp) ▸ hmax _ hmem hle
  -- The mono half of the factorisation, after the embedding.
  have hmono : Mono (indOf.map
      (image.ι (g ≫ Z.presentation.F.map α₀)) ≫ presStage Z j₀) := by
    refine mono_of_hom_indOf_injective _ (fun W u v huv => ?_)
    have hu : indOf.map (Ind.yoneda.fullyFaithful.preimage u) = u :=
      Ind.yoneda.fullyFaithful.map_preimage u
    have hv : indOf.map (Ind.yoneda.fullyFaithful.preimage v) = v :=
      Ind.yoneda.fullyFaithful.map_preimage v
    obtain ⟨k, β, hβ⟩ := exists_stage_comp_eq_of_presStage
      (u ≫ indOf.map (image.ι (g ≫ Z.presentation.F.map α₀)))
      (v ≫ indOf.map (image.ι (g ≫ Z.presentation.F.map α₀)))
      ((Category.assoc _ _ _).trans (huv.trans
        (Category.assoc _ _ _).symm))
    have hpre : (Ind.yoneda.fullyFaithful.preimage u ≫
        image.ι (g ≫ Z.presentation.F.map α₀) ≫
          Z.presentation.F.map β) =
      (Ind.yoneda.fullyFaithful.preimage v ≫
        image.ι (g ≫ Z.presentation.F.map α₀) ≫
          Z.presentation.F.map β) := by
      refine indOf.map_injective ?_
      rw [CategoryTheory.Functor.map_comp,
        CategoryTheory.Functor.map_comp,
        CategoryTheory.Functor.map_comp,
        CategoryTheory.Functor.map_comp, hu, hv]
      exact ((Category.assoc _ _ _).symm.trans hβ).trans
        (Category.assoc _ _ _)
    haveI : Mono (image.ι (g ≫ Z.presentation.F.map α₀) ≫
        Z.presentation.F.map β) :=
      mono_of_kernelSubobject_comp_le _ _ (hstable k β)
    have : Ind.yoneda.fullyFaithful.preimage u =
        Ind.yoneda.fullyFaithful.preimage v :=
      (cancel_mono (image.ι (g ≫ Z.presentation.F.map α₀) ≫
        Z.presentation.F.map β)).mp hpre
    rw [← hu, ← hv, this]
  haveI := hmono
  haveI : StrongEpi (indOf.map
      (factorThruImage (g ≫ Z.presentation.F.map α₀))) :=
    strongEpi_of_epi _
  refine ⟨image (g ≫ Z.presentation.F.map α₀), ⟨(image.isoStrongEpiMono
    (indOf.map (factorThruImage (g ≫ Z.presentation.F.map α₀)))
    (indOf.map (image.ι (g ≫ Z.presentation.F.map α₀)) ≫
      presStage Z j₀) ?_).symm⟩⟩
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, image.fac]
  exact hf

end Embedded

end RS
