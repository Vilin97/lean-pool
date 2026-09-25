/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SymAlg

/-!
# The module power, one letter at a time

The relative tensor power `modPow A X n` of `SymAlg.lean` is
presented in a single step, over all adjacent slots at once.  The
arities are nevertheless joined by one letter at a time, and this
file supplies that stage map: the projection at arity `n + 1`
factors through the projection at arity `n` whiskered by one
further letter.

* `modPowGlue_succ`, `modPowLegM_succ`, `modPowLegN_succ`: a
  relation slot with one further letter of tail is that slot with
  the shorter tail, whiskered by the letter, after the associator
  that exposes it.
* `modPowStage A X n : modPow A X n ⊗ X ⟶ modPow A X (n + 1)`,
  descended along the whiskered presentation of `SymAlg.lean`, with
  `modPowπ_whiskerRight_stage` the factorisation itself.
* `modPow_invisible_succ`: an ambient endomorphism invisible to the
  projection at one arity is invisible at the next.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## One further letter of tail

Every relation leg is a local morphism whiskered by the tail and
then glued.  Lengthening the tail by one letter therefore only
reassociates: at general objects this is a single application of
`whiskerRight_tensor`, and each arity-bearing instance is obtained
from it by `exact`, so that no tensor-power arity enters the
rewriting.
-/

section LegSucc

/-- Lengthening the tail by one letter, at general objects. -/
private theorem glue_succ_aux [Category.{v} D] [MonoidalCategory D]
    {S T Q : D} (v : S ⟶ T) (P : D)
    (c : T ⊗ P ⟶ Q) (W : D) :
    (v ▷ (P ⊗ W)) ≫ ((α_ T P W).inv ≫ (c ▷ W)) =
      (α_ S P W).inv ≫ (((v ▷ P) ≫ c) ▷ W) := by
  rw [MonoidalCategory.whiskerRight_tensor,
    MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- **Gluing a longer tail**: the glue at tail length `b + 1` is the
glue at tail length `b`, whiskered by the extra letter. -/
theorem modPowGlue_succ [Category.{v} D] [MonoidalCategory D] (X : D)
    (a b : ℕ) :
    modPowGlue X a (b + 1) =
      (α_ (tensorPow D X a ⊗ (X ⊗ X)) (tensorPow D X b) X).inv ≫
        (modPowGlue X a b ▷ X) :=
  glue_succ_aux (α_ (tensorPow D X a) X X).inv (tensorPow D X b)
    (tensorPowConcat X (a + 2) b).hom X

end LegSucc

section LegSuccMod

/-- **The first leg with a longer tail**: acting on the left module
factor over a tail of length `b + 1` is doing so over a tail of
length `b`, whiskered by the extra letter. -/
theorem modPowLegM_succ
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X]
    (a b : ℕ) :
    modPowLegM A X a (b + 1) =
      (α_ (tensorPow D X a ⊗ ((X ⊗ A) ⊗ X)) (tensorPow D X b) X).inv ≫
        (modPowLegM A X a b ▷ X) := by
  change ((tensorPow D X a ◁ winLegM A X) ▷ tensorPow D X (b + 1)) ≫
      modPowGlue X a (b + 1) = _
  rw [modPowGlue_succ]
  exact glue_succ_aux (tensorPow D X a ◁ winLegM A X)
    (tensorPow D X b) (modPowGlue X a b) X

/-- **The second leg with a longer tail**: acting on the right
module factor over a tail of length `b + 1` is doing so over a tail
of length `b`, whiskered by the extra letter. -/
theorem modPowLegN_succ
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : D)
    [ModObj A X]
    (a b : ℕ) :
    modPowLegN A X a (b + 1) =
      (α_ (tensorPow D X a ⊗ ((X ⊗ A) ⊗ X)) (tensorPow D X b) X).inv ≫
        (modPowLegN A X a b ▷ X) := by
  change ((tensorPow D X a ◁ winLegN A X) ▷ tensorPow D X (b + 1)) ≫
      modPowGlue X a (b + 1) = _
  rw [modPowGlue_succ]
  exact glue_succ_aux (tensorPow D X a ◁ winLegN A X)
    (tensorPow D X b) (modPowGlue X a b) X

end LegSuccMod

/-! ## The stage map

The whiskered relation pair still coequalizes the projection one
arity up: tensoring on the right is additive, so the assembled legs
split into their slots, and each slot is the slot relation of the
longer arity with one more letter of tail.
-/

section BiproductWhisker

/-- Whiskering a biproduct descent: tensoring on the right is an
additive functor, so it distributes over the slot decomposition. -/
private theorem desc_whiskerRight
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D]
    {J : Type} [Fintype J]
    {f : J → D} {T : D} (g : ∀ i, f i ⟶ T) (W : D) :
    biproduct.desc g ▷ W =
      ∑ i : J, (biproduct.π f i ▷ W) ≫ (g i ▷ W) := by
  rw [biproduct.desc_eq,
    show (∑ i : J, biproduct.π f i ≫ g i) ▷ W =
      (tensorRight W).map (∑ i : J, biproduct.π f i ≫ g i) from rfl,
    (tensorRight W).map_sum (fun i => biproduct.π f i ≫ g i)
      Finset.univ]
  exact Finset.sum_congr rfl fun i _ =>
    MonoidalCategory.comp_whiskerRight _ _ _

end BiproductWhisker

section Stage

/-- One slot of the whiskered relation pair is the slot relation of
the longer arity, with one more letter of tail. -/
private theorem slot_whiskerRight
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    {n : ℕ} (a b : ℕ)
    (h : a + 2 + b = n) :
    ((modPowLegM A X a b ≫ powCast X h) ▷ X) ≫
        modPowπ A X (n + 1) =
      ((modPowLegN A X a b ≫ powCast X h) ▷ X) ≫
        modPowπ A X (n + 1) := by
  have key := modPow_rel A X a (b + 1)
    (by omega : a + 2 + (b + 1) = n + 1)
  rw [modPowLegM_succ, modPowLegN_succ] at key
  refine (cancel_epi (α_ (tensorPow D X a ⊗ ((X ⊗ A) ⊗ X))
    (tensorPow D X b) X).inv).1 ?_
  rw [MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.comp_whiskerRight, powCast_whiskerRight]
  repeat' erw [Category.assoc]
  exact ((Category.assoc _ _ _).symm.trans key).trans
    (Category.assoc _ _ _)

/-- **The whiskered relation pair coequalizes one arity up**: the
assembled legs at arity `n`, whiskered by one letter, agree after
the projection at arity `n + 1`. -/
theorem modPow_condition_succ
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [MonoidalPreadditive D]
    [HasFiniteBiproducts D] [HasCoequalizers D]
    (n : ℕ) :
    (modPowLegFst A X n ▷ X) ≫ modPowπ A X (n + 1) =
      (modPowLegSnd A X n ▷ X) ≫ modPowπ A X (n + 1) := by
  erw [modPowLegFst, modPowLegSnd, desc_whiskerRight,
    desc_whiskerRight, Preadditive.sum_comp, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  repeat' erw [Category.assoc]
  have hslot := slot_whiskerRight A X i.val (n - 2 - i.val) (slot_decomp i)
  simp only [modPowLegM, modPowLegN, modPowGlue, Category.assoc] at hslot
  repeat' erw [Category.assoc] at hslot
  exact whisker_eq _ hslot

/-- **The stage map**: the projection at arity `n + 1` factors
through the projection at arity `n` whiskered by one letter. -/
noncomputable def modPowStage
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [MonoidalPreadditive D]
    [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (n : ℕ) :
    modPow A X n ⊗ X ⟶ modPow A X (n + 1) :=
  modPowWhiskerRightDesc A X n X (modPowπ A X (n + 1))
    (modPow_condition_succ A X n)

/-- The stage map is the factorisation of the projection at arity
`n + 1` through the whiskered projection at arity `n`. -/
@[reassoc (attr := simp)]
theorem modPowπ_whiskerRight_stage
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [MonoidalPreadditive D]
    [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (n : ℕ) :
    (modPowπ A X n ▷ X) ≫ modPowStage A X n = modPowπ A X (n + 1) :=
  modPowπ_whiskerRight_desc A X n X _ _

/-- **An identity invisible at one arity is invisible at the
next**: whiskering by a further letter keeps it invisible. -/
theorem modPow_invisible_succ
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [MonoidalPreadditive D]
    [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (n : ℕ)
    {g : tensorPow D X n ⟶ tensorPow D X n}
    (hg : g ≫ modPowπ A X n = modPowπ A X n) :
    (g ▷ X) ≫ modPowπ A X (n + 1) = modPowπ A X (n + 1) := by
  rw [← modPowπ_whiskerRight_stage A X n, ← Category.assoc,
    ← MonoidalCategory.comp_whiskerRight, hg]

end Stage

end RS
