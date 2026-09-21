/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing schemes along one common open per chart

This file packages a frequent special case of `Scheme.GlueData`: every off-diagonal overlap in a
chart is the same open subscheme.  The triple-overlap pullbacks are therefore self-pullbacks of an
open immersion.  Their projections are isomorphisms because open immersions are monomorphisms,
which makes the required pullback-level cocycle explicit.
-/

open CategoryTheory CategoryTheory.Limits

namespace BGS

noncomputable section

universe v

variable {J : Type v}

/-- The off-diagonal `GlueData'` for charts that all use one fixed open subscheme per chart.

The transition maps are required to compose strictly.  This is the exact input needed to construct
the pullback transition `t'`; no gluing conclusion is assumed as a structure field. -/
def constantOpenGlueDataAux
    (U V : J → AlgebraicGeometry.Scheme.{v})
    (f : ∀ i, V i ⟶ U i)
    [∀ i, AlgebraicGeometry.IsOpenImmersion (f i)]
    (t : ∀ i j, V i ⟶ V j)
    (t_id : ∀ i, t i i = 𝟙 _)
    (t_comp : ∀ i j k, t i j ≫ t j k = t i k) :
    CategoryTheory.GlueData' AlgebraicGeometry.Scheme.{v} where
  J := J
  U := U
  V i _ _ := V i
  f i _ _ := f i
  f_mono := by intros; infer_instance
  f_hasPullback := by intros; infer_instance
  t i j _ := t i j
  t' i j _ _ _ _ :=
    pullback.fst (f i) (f i) ≫ t i j ≫ inv (pullback.fst (f j) (f j))
  t_fac i j k _ _ _ := by
    rw [← fst_eq_snd_of_mono_eq (f j)]
    simp
  t_inv i j _ := by
    rw [t_comp, t_id]
  cocycle i j k _ _ _ := by
    have hcycle : t i j ≫ (t j k ≫ t k i) = 𝟙 _ := by
      rw [← Category.assoc, t_comp i j k, t_comp i k i, t_id]
    simpa [Category.assoc] using congrArg
      (fun g : V i ⟶ V i ↦
        pullback.fst (f i) (f i) ≫ g ≫ inv (pullback.fst (f i) (f i))) hcycle

/-- Glue schemes when every chart has one common overlap and the transition maps compose
strictly. -/
def constantOpenGlueData
    (U V : J → AlgebraicGeometry.Scheme.{v})
    (f : ∀ i, V i ⟶ U i)
    [∀ i, AlgebraicGeometry.IsOpenImmersion (f i)]
    (t : ∀ i j, V i ⟶ V j)
    (t_id : ∀ i, t i i = 𝟙 _)
    (t_comp : ∀ i j k, t i j ≫ t j k = t i k) :
    AlgebraicGeometry.Scheme.GlueData where
  toGlueData := CategoryTheory.GlueData.ofGlueData'
    (constantOpenGlueDataAux U V f t t_id t_comp)
  f_open i j := by
    change J at i j
    have hf : AlgebraicGeometry.IsOpenImmersion (f i) := inferInstance
    dsimp [CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f',
      constantOpenGlueDataAux]
    split_ifs with hij
    · infer_instance
    · change AlgebraicGeometry.IsOpenImmersion (eqToHom _ ≫ f i)
      refine @AlgebraicGeometry.IsOpenImmersion.comp _ (V i) (U i)
        (eqToHom _) (f i) ?_ hf
      refine @AlgebraicGeometry.IsOpenImmersion.of_isIso _ _ (eqToHom _) ?_
      exact (eqToIso (if_neg hij)).isIso_hom

/-- Glue schemes whose overlap in each chart is identified with one common scheme.  The transition
from chart `i` to chart `j` is induced by passing through the common target, so identity and
composition are consequences of the isomorphism laws. -/
def constantOpenGlueDataOfCommonTarget
    (U V : J → AlgebraicGeometry.Scheme.{v})
    (f : ∀ i, V i ⟶ U i)
    [∀ i, AlgebraicGeometry.IsOpenImmersion (f i)]
    (W : AlgebraicGeometry.Scheme.{v})
    (s : ∀ i, V i ≅ W) :
    AlgebraicGeometry.Scheme.GlueData :=
  constantOpenGlueData U V f
    (fun i j ↦ (s i).hom ≫ (s j).inv)
    (fun i ↦ Iso.hom_inv_id (s i))
    (fun i j k ↦ by simp)

/-- A compatible family of chart morphisms and a morphism of their common overlaps descends to a
morphism between the glued schemes.  The square `h` is the substantive input: it states that each
chart morphism restricts to the specified common-overlap morphism. -/
def constantOpenGlueDataOfCommonTargetMap
    (U V U' V' : J → AlgebraicGeometry.Scheme.{v})
    (f : ∀ i, V i ⟶ U i) [∀ i, AlgebraicGeometry.IsOpenImmersion (f i)]
    (f' : ∀ i, V' i ⟶ U' i) [∀ i, AlgebraicGeometry.IsOpenImmersion (f' i)]
    (W W' : AlgebraicGeometry.Scheme.{v})
    (s : ∀ i, V i ≅ W) (s' : ∀ i, V' i ≅ W')
    (g : ∀ i, U i ⟶ U' i) (q : W ⟶ W')
    (h : ∀ i, f i ≫ g i = (s i).hom ≫ q ≫ (s' i).inv ≫ f' i) :
    (constantOpenGlueDataOfCommonTarget U V f W s).glued ⟶
      (constantOpenGlueDataOfCommonTarget U' V' f' W' s').glued := by
  let D := constantOpenGlueDataOfCommonTarget U V f W s
  let E := constantOpenGlueDataOfCommonTarget U' V' f' W' s'
  let inc : ∀ i : J, U' i ⟶ E.glued := fun i ↦ E.ι i
  have inc_transition (i j : J) (hij : i ≠ j) :
      (s' i).hom ≫ (s' j).inv ≫ f' j ≫ inc j = f' i ≫ inc i := by
    have hc := E.glue_condition i j
    dsimp only [E, constantOpenGlueDataOfCommonTarget, constantOpenGlueData,
      CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f',
      constantOpenGlueDataAux] at hc
    simp only [dif_neg hij, dif_neg (Ne.symm hij)] at hc
    simp at hc
    exact (cancel_epi _).mp hc
  fapply Multicoequalizer.desc
  · exact fun i ↦ g i ≫ inc i
  · rintro ⟨i, j⟩
    simp only [CategoryTheory.GlueData.diagram_fst, CategoryTheory.GlueData.diagram_snd]
    change D.f i j ≫ g i ≫ inc i =
      (D.t i j ≫ D.f j i) ≫ g j ≫ inc j
    change J at i j
    by_cases hij : i = j
    · subst j
      erw [D.t_id]
      simp
    · dsimp only [D, constantOpenGlueDataOfCommonTarget, constantOpenGlueData,
        CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f',
        constantOpenGlueDataAux]
      simp only [dif_neg hij, dif_neg (Ne.symm hij)]
      simp
      congr 1
      simp only [← Category.assoc]
      rw [h i]
      rw [Category.assoc ((s i).hom ≫ (s j).inv) (f j) (g j)]
      rw [h j]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← inc_transition i j hij]
      simp

/-- The descended morphism restricts to the prescribed morphism on every chart. -/
@[reassoc]
theorem constantOpenGlueDataOfCommonTargetMap_chart
    (U V U' V' : J → AlgebraicGeometry.Scheme.{v})
    (f : ∀ i, V i ⟶ U i) [∀ i, AlgebraicGeometry.IsOpenImmersion (f i)]
    (f' : ∀ i, V' i ⟶ U' i) [∀ i, AlgebraicGeometry.IsOpenImmersion (f' i)]
    (W W' : AlgebraicGeometry.Scheme.{v})
    (s : ∀ i, V i ≅ W) (s' : ∀ i, V' i ≅ W')
    (g : ∀ i, U i ⟶ U' i) (q : W ⟶ W')
    (h : ∀ i, f i ≫ g i = (s i).hom ≫ q ≫ (s' i).inv ≫ f' i)
    (i : J) :
    (constantOpenGlueDataOfCommonTarget U V f W s).ι i ≫
        constantOpenGlueDataOfCommonTargetMap U V U' V' f f' W W' s s' g q h =
      g i ≫ (constantOpenGlueDataOfCommonTarget U' V' f' W' s').ι i := by
  dsimp [constantOpenGlueDataOfCommonTargetMap]
  unfold AlgebraicGeometry.Scheme.GlueData.ι
  exact Multicoequalizer.π_desc
    (constantOpenGlueDataOfCommonTarget U V f W s).toGlueData.diagram _ _ _ i

end

end BGS
