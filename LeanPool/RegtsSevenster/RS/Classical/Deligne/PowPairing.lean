/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.KeyLemma
import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowAct

/-!
# The power pairing

For a Mod-internal duality datum on a pair of modules, the nested
pairing of equal tensor powers: peel the innermost pair — the last
factor of the `M'`-power against the first factor of the
`M`-power — evaluate the datum, braid the scalar out, and multiply
onto the pairing of the remaining powers.  The pairing is defined
at the raw tensor-power level by recursion on the arity; the
descent obligations through the module-power and module-tensor
coequalizers reduce, by the same recursion, to the datum's
linearity and the commutativity of the monoid.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

section Braided

/-! ## The datum's pairing at the raw tensor level -/

section PairRaw

/-- The datum's pairing evaluated on the raw tensor product. -/
noncomputable def pairRaw
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    M'.X ⊗ M.X ⟶ A :=
  modTensorπ A M' M ≫ d.pair

/-- Raw linearity of the pairing in the `M'`-factor: acting on the
first factor multiplies the scalar. -/
@[reassoc]
theorem pairRaw_actLeft_fst
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    ((α_ A M'.X M.X).inv ≫ actLeft A M'.X ▷ M.X) ≫
        pairRaw A M M' d =
      (A ◁ pairRaw A M M' d) ≫ μ[A] := by
  have h : modTensorAct A M' M ≫ d.pair =
      (A ◁ d.pair) ≫ μ[A] := d.pair_linear
  rw [pairRaw]
  conv_rhs => rw [MonoidalCategory.whiskerLeft_comp,
    Category.assoc, ← h, whiskerLeft_modTensorπ_act_assoc]
  simp only [Category.assoc]

/-- The middle slide across the raw pairing: the braided right
action on `M'` and the left action on `M` pair equally. -/
@[reassoc]
theorem pairRaw_slide [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    (actRight A M'.X ▷ M.X) ≫ pairRaw A M M' d =
      ((α_ M'.X A M.X).hom ≫ M'.X ◁ actLeft A M.X) ≫
        pairRaw A M M' d := by
  have h := modTensor_condition_assoc A M' M d.pair
  rw [modTensorLegM, modTensorLegN] at h
  simpa [pairRaw] using h

/-- Raw linearity through the braided right action: acting on the
right of the `M'`-factor braids the scalar out to the left and
multiplies. -/
@[reassoc]
theorem pairRaw_actRight_fst
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    (actRight A M'.X ▷ M.X) ≫ pairRaw A M M' d =
      ((β_ M'.X A).hom ▷ M.X) ≫ (α_ A M'.X M.X).hom ≫
        (A ◁ pairRaw A M M' d) ≫ μ[A] := by
  conv_rhs => rw [← pairRaw_actLeft_fst A M M' d]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [actRight, comp_whiskerRight, Category.assoc]

/-- Raw linearity in the `M`-factor: acting on the left of the
`M`-factor braids the scalar out to the left and multiplies. -/
@[reassoc]
theorem pairRaw_actLeft_snd
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    (M'.X ◁ actLeft A M.X) ≫ pairRaw A M M' d =
      (α_ M'.X A M.X).inv ≫ ((β_ M'.X A).hom ▷ M.X) ≫
        (α_ A M'.X M.X).hom ≫ (A ◁ pairRaw A M M' d) ≫ μ[A] := by
  rw [← pairRaw_actRight_fst, pairRaw_slide]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end PairRaw

/-! ## The nested power pairing -/

section RawPair

/-- **The nested power pairing** at the raw tensor level, by
recursion on the arity: at `n + 1`, peel the first factor of the
`M`-power, pair it with the exposed last factor of the `M'`-power,
braid the resulting scalar past the remaining `M`-power, and
multiply it onto the pairing of the remaining powers. -/
noncomputable def rawPair
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    (n : ℕ) → (tensorPow D M'.X n ⊗ tensorPow D M.X n ⟶ A)
  | 0 => (λ_ (𝟙_ D)).hom ≫ η[A]
  | n + 1 =>
      (tensorPow D M'.X (n + 1) ◁ (powPeel M.X n).hom) ≫
        (α_ (tensorPow D M'.X n) M'.X
          (M.X ⊗ tensorPow D M.X n)).hom ≫
        (tensorPow D M'.X n ◁
          (α_ M'.X M.X (tensorPow D M.X n)).inv) ≫
        (tensorPow D M'.X n ◁
          (pairRaw A M M' d ▷ tensorPow D M.X n)) ≫
        (tensorPow D M'.X n ◁ (β_ A (tensorPow D M.X n)).hom) ≫
        (α_ (tensorPow D M'.X n) (tensorPow D M.X n) A).inv ≫
        (rawPair A M M' d n ▷ A) ≫ μ[A]

/-- The base case of the power pairing. -/
theorem rawPair_zero [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    rawPair A M M' d 0 = (λ_ (𝟙_ D)).hom ≫ η[A] :=
  rfl

/-- The recursion of the power pairing. -/
theorem rawPair_succ [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') (n : ℕ) :
    rawPair A M M' d (n + 1) =
      (tensorPow D M'.X (n + 1) ◁ (powPeel M.X n).hom) ≫
        (α_ (tensorPow D M'.X n) M'.X
          (M.X ⊗ tensorPow D M.X n)).hom ≫
        (tensorPow D M'.X n ◁
          (α_ M'.X M.X (tensorPow D M.X n)).inv) ≫
        (tensorPow D M'.X n ◁
          (pairRaw A M M' d ▷ tensorPow D M.X n)) ≫
        (tensorPow D M'.X n ◁ (β_ A (tensorPow D M.X n)).hom) ≫
        (α_ (tensorPow D M'.X n) (tensorPow D M.X n) A).inv ≫
        (rawPair A M M' d n ▷ A) ≫ μ[A] :=
  rfl

end RawPair

/-! ## The generic pairing step

The recursion step of the power pairing, over an arbitrary
continuation pairing: pair the exposed last `M'`-factor against
the exposed head `M`-factor, braid the scalar past the remaining
block, and fold it onto the continuation by multiplication.  All
extraction and naturality laws are proved at this generality, so
that the inductions over the arity reduce to threading through
the step.
-/

section PairStep

/-- The generic recursion step of the power pairing. -/
noncomputable def pairStep
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    {Q R : D} (r : Q ⊗ R ⟶ A) :
    (Q ⊗ M'.X) ⊗ (M.X ⊗ R) ⟶ A :=
  (α_ Q M'.X (M.X ⊗ R)).hom ≫
    (Q ◁ ((α_ M'.X M.X R).inv ≫
      (pairRaw A M M' d ▷ R) ≫ (β_ A R).hom)) ≫
    (α_ Q R A).inv ≫ (r ▷ A) ≫ μ[A]

/-- The recursion of the power pairing through the generic
step. -/
theorem rawPair_succ_step
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') (n : ℕ) :
    rawPair A M M' d (n + 1) =
      (tensorPow D M'.X (n + 1) ◁ (powPeel M.X n).hom) ≫
        pairStep A M M' d (rawPair A M M' d n) := by
  rw [rawPair_succ, pairStep]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rfl

/-- Naturality of the step in the block variable. -/
theorem pairStep_precomp
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    {Q' Q R : D} (f : Q' ⟶ Q) (r : Q ⊗ R ⟶ A) :
    ((f ▷ M'.X) ▷ (M.X ⊗ R)) ≫ pairStep A M M' d r =
      pairStep A M M' d ((f ▷ R) ≫ r) := by
  rw [pairStep, pairStep,
    associator_naturality_left_assoc, ← whisker_exchange_assoc,
    associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc]

/-- Naturality of the step in the continuation variable. -/
theorem pairStep_postcomp
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    {Q R' R : D} (g : R' ⟶ R) (r : Q ⊗ R ⟶ A) :
    ((Q ⊗ M'.X) ◁ (M.X ◁ g)) ≫ pairStep A M M' d r =
      pairStep A M M' d ((Q ◁ g) ≫ r) := by
  rw [pairStep, pairStep, associator_naturality_right_assoc]
  have hblock : (M'.X ◁ (M.X ◁ g)) ≫
      ((α_ M'.X M.X R).inv ≫
        (pairRaw A M M' d ▷ R) ≫ (β_ A R).hom) =
      ((α_ M'.X M.X R').inv ≫
        (pairRaw A M M' d ▷ R') ≫ (β_ A R').hom) ≫ (g ▷ A) := by
    rw [associator_inv_naturality_right_assoc,
      whisker_exchange_assoc,
      BraidedCategory.braiding_naturality_right]
    simp only [Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, hblock,
    MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight_assoc]

end PairStep

/-- The mirror crossing coherence, for a strand arriving from the
left of the pair's second factor. -/
private theorem cross_shuffle_snd
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (S T R C : D) :
    (S ◁ (α_ C T R).inv) ≫ (α_ S (C ⊗ T) R).inv ≫
        ((S ◁ (β_ C T).hom) ▷ R) ≫ ((α_ S T C).inv ▷ R) ≫
        (β_ ((S ⊗ T) ⊗ C) R).hom =
      (S ◁ (β_ C (T ⊗ R)).hom) ≫ (α_ S (T ⊗ R) C).inv ≫
        ((α_ S T R).inv ▷ C) ≫ ((β_ (S ⊗ T) R).hom ▷ C) ≫
        (α_ R (S ⊗ T) C).hom := by
  rw [BraidedCategory.braiding_tensor_left_hom,
    BraidedCategory.braiding_tensor_right_hom]
  monoidal

/-- A strand crossing a block from inside a left pair: crossing
the adjacent factor and then the whole block as a unit equals
first regrouping and crossing factor by factor. -/
private theorem cross_shuffle
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (S T R C : D) :
    (α_ (S ⊗ C) T R).inv ≫ ((α_ S C T).hom ▷ R) ≫
        ((S ◁ (β_ C T).hom) ▷ R) ≫ ((α_ S T C).inv ▷ R) ≫
        (β_ ((S ⊗ T) ⊗ C) R).hom =
      (α_ S C (T ⊗ R)).hom ≫ (S ◁ (β_ C (T ⊗ R)).hom) ≫
        (α_ S (T ⊗ R) C).inv ≫ ((α_ S T R).inv ▷ C) ≫
        ((β_ (S ⊗ T) R).hom ▷ C) ≫ (α_ R (S ⊗ T) C).hom := by
  rw [BraidedCategory.braiding_tensor_left_hom,
    BraidedCategory.braiding_tensor_right_hom]
  monoidal

end Braided

/-! ## Scalar extraction over a symmetric base

The descent obligations move an acted scalar across whole tensor
blocks in both directions; the two routes agree only when the
braiding is symmetric.  The pairing calculus therefore runs over a
symmetric base from here on — which is the generality of the Key
Lemma itself.  The section is fresh, so that the symmetric
structure's braiding is the only braiding in scope.
-/

section ConcatPeel

/-- **Concatenation against the head peel**: concatenating onto a
power with an exposed head factor and peeling the head of the
result equals peeling the first block and concatenating the
rest under the exposed factor. -/
theorem concat_peel_head [Category.{v} D] [MonoidalCategory D] (X : D)
    (p : ℕ) : ∀ q : ℕ,
    (tensorPowConcat X (p + 1) q).hom ≫
      powCast X (by omega : p + 1 + q = p + q + 1) ≫
      (powPeel X (p + q)).hom =
    ((powPeel X p).hom ▷ tensorPow D X q) ≫
      (α_ X (tensorPow D X p) (tensorPow D X q)).hom ≫
      (X ◁ (tensorPowConcat X p q).hom)
  | 0 => by
    rw [tensorPowConcat_zero, tensorPowConcat_zero]
    show (ρ_ (tensorPow D X (p + 1))).hom ≫
        𝟙 (tensorPow D X (p + 1)) ≫ (powPeel X p).hom =
      ((powPeel X p).hom ▷ 𝟙_ D) ≫
        (α_ X (tensorPow D X p) (𝟙_ D)).hom ≫
        (X ◁ (ρ_ (tensorPow D X p)).hom)
    rw [Category.id_comp]
    monoidal
  | q + 1 => by
    rw [tensorPowConcat_succ, tensorPowConcat_succ]
    show ((α_ (tensorPow D X (p + 1)) (tensorPow D X q) X).inv ≫
        ((tensorPowConcat X (p + 1) q).hom ▷ X)) ≫
      powCast X (by omega : p + 1 + q + 1 = p + q + 1 + 1) ≫
      (((powPeel X (p + q)).hom ▷ X) ≫
        (α_ X (tensorPow D X (p + q)) X).hom) =
    ((powPeel X p).hom ▷ (tensorPow D X q ⊗ X)) ≫
      (α_ X (tensorPow D X p) (tensorPow D X q ⊗ X)).hom ≫
      (X ◁ ((α_ (tensorPow D X p) (tensorPow D X q) X).inv ≫
        ((tensorPowConcat X p q).hom ▷ X)))
    rw [← powCast_whiskerRight]
    simp only [Category.assoc]
    show (α_ (tensorPow D X (p + 1)) (tensorPow D X q) X).inv ≫
      ((tensorPowConcat X (p + 1) q).hom ▷ X) ≫
      (powCast X (by omega : p + 1 + q = p + q + 1) ▷ X) ≫
      ((powPeel X (p + q)).hom ▷ X) ≫
      (α_ X (tensorPow D X (p + q)) X).hom =
    ((powPeel X p).hom ▷ (tensorPow D X q ⊗ X)) ≫
      (α_ X (tensorPow D X p) (tensorPow D X q ⊗ X)).hom ≫
      (X ◁ ((α_ (tensorPow D X p) (tensorPow D X q) X).inv ≫
        ((tensorPowConcat X p q).hom ▷ X)))
    rw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc,
      Category.assoc, concat_peel_head X p q]
    simp only [comp_whiskerRight, Category.assoc]
    monoidal

/-- **The head decomposition of a slot leg**: a leg with a
non-trivial left context, followed by the head peel, is the head
peel of the block followed by the leg at the lower context under
the exposed factor. -/
private theorem leg_step_snd_eq [Category.{v} D] [MonoidalCategory D]
    {A X : D}
    (w : (X ⊗ A) ⊗ X ⟶ X ⊗ X) (a b : ℕ) :
    ((tensorPow D X (a + 1) ◁ w) ▷ tensorPow D X b) ≫
      modPowGlue X (a + 1) b ≫
      powCast X (by omega : a + 1 + 2 + b = a + 2 + b + 1) ≫
      (powPeel X (a + 2 + b)).hom =
    (((powPeel X a).hom ▷ ((X ⊗ A) ⊗ X)) ▷ tensorPow D X b) ≫
      ((α_ X (tensorPow D X a) ((X ⊗ A) ⊗ X)).hom ▷
        tensorPow D X b) ≫
      (α_ X (tensorPow D X a ⊗ ((X ⊗ A) ⊗ X))
        (tensorPow D X b)).hom ≫
      (X ◁ (((tensorPow D X a ◁ w) ▷ tensorPow D X b) ≫
        modPowGlue X a b)) := by
  rw [modPowGlue, modPowGlue]
  show ((tensorPow D X (a + 1) ◁ w) ▷ tensorPow D X b) ≫
    (((α_ (tensorPow D X (a + 1)) X X).inv ▷ tensorPow D X b) ≫
      (tensorPowConcat X (a + 2 + 1) b).hom) ≫
    powCast X (by omega : a + 2 + 1 + b = a + 2 + b + 1) ≫
    (powPeel X (a + 2 + b)).hom = _
  simp only [Category.assoc]
  refine Eq.trans (congrArg (fun t =>
    ((tensorPow D X (a + 1) ◁ w) ▷ tensorPow D X b) ≫
      ((α_ (tensorPow D X (a + 1)) X X).inv ▷
        tensorPow D X b) ≫ t) (concat_peel_head X (a + 2) b)) ?_
  trans (((tensorPow D X (a + 1) ◁ w) ▷ tensorPow D X b) ≫
    (((powPeel X a).hom ▷ (X ⊗ X)) ▷ tensorPow D X b) ≫
    ((α_ X (tensorPow D X a) (X ⊗ X)).hom ▷ tensorPow D X b) ≫
    (α_ X (tensorPow D X a ⊗ (X ⊗ X)) (tensorPow D X b)).hom ≫
    (X ◁ (((α_ (tensorPow D X a) X X).inv ▷ tensorPow D X b) ≫
      (tensorPowConcat X (a + 2) b).hom)))
  · rw [show (powPeel X (a + 2)).hom =
      ((((powPeel X a).hom ▷ X) ≫
        (α_ X (tensorPow D X a) X).hom) ▷ X) ≫
      (α_ X (tensorPow D X (a + 1)) X).hom from rfl]
    monoidal
  · rw [← comp_whiskerRight_assoc, whisker_exchange,
      comp_whiskerRight, Category.assoc]
    monoidal

end ConcatPeel

section Symmetric

/-- A strand crossing out to the left through an evaluated pairing
may instead cross to the right and braid past the output. -/
theorem braid_cross_pair
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    {S T Z : D} (C : D) (f : S ⊗ T ⟶ Z) :
    ((β_ S C).hom ▷ T) ≫ (α_ C S T).hom ≫ (C ◁ f) =
      (α_ S C T).hom ≫ (S ◁ (β_ C T).hom) ≫ (α_ S T C).inv ≫
        (f ▷ C) ≫ (β_ Z C).hom := by
  rw [BraidedCategory.braiding_naturality_left f C,
    BraidedCategory.braiding_tensor_left_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc,
    SymmetricCategory.symmetry]
  simp

/-- **Scalar extraction at the pair**: acting on the right of the
`M'`-factor equals sliding the scalar rightwards past the
`M`-factor, pairing, and multiplying from the right. -/
@[reassoc]
theorem pairRaw_actRight_out
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    (actRight A M'.X ▷ M.X) ≫ pairRaw A M M' d =
      (α_ M'.X A M.X).hom ≫ (M'.X ◁ (β_ A M.X).hom) ≫
        (α_ M'.X M.X A).inv ≫ (pairRaw A M M' d ▷ A) ≫ μ[A] := by
  rw [pairRaw_actRight_fst,
    reassoc_of% braid_cross_pair A (pairRaw A M M' d)]
  rw [IsCommMonObj.mul_comm]

/-- The inner extraction: acting on the right of the `M'`-factor
before a whiskered pairing-and-braid block equals braiding the
scalar past the block and folding it by multiplication. -/
private theorem inner_extract
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (R : D) :
    (actRight A M'.X ▷ (M.X ⊗ R)) ≫ (α_ M'.X M.X R).inv ≫
        (pairRaw A M M' d ▷ R) ≫ (β_ A R).hom =
      (α_ M'.X A (M.X ⊗ R)).hom ≫
        (M'.X ◁ (β_ A (M.X ⊗ R)).hom) ≫
        (α_ M'.X (M.X ⊗ R) A).inv ≫
        (((α_ M'.X M.X R).inv ≫ (pairRaw A M M' d ▷ R) ≫
            (β_ A R).hom) ▷ A) ≫
        (α_ R A A).hom ≫ (R ◁ μ[A]) := by
  rw [associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc, pairRaw_actRight_out]
  simp only [comp_whiskerRight, Category.assoc]
  rw [BraidedCategory.braiding_naturality_left μ[A] R,
    BraidedCategory.braiding_naturality_left_assoc
      (pairRaw A M M' d ▷ A) R]
  have hp : (pairRaw A M M' d ▷ R) ≫ (β_ A R).hom =
      (β_ (M'.X ⊗ M.X) R).hom ≫ (R ◁ pairRaw A M M' d) :=
    BraidedCategory.braiding_naturality_left _ R
  conv_rhs => rw [← comp_whiskerRight_assoc,
    ← comp_whiskerRight_assoc, Category.assoc, hp]
  simp only [comp_whiskerRight, Category.assoc]
  rw [associator_naturality_middle_assoc]
  rw [reassoc_of% cross_shuffle M'.X M.X R A]

/-- **Scalar extraction at the pair, second slot**: acting on the
left of the `M`-factor equals sliding the scalar rightwards past
the `M`-factor, pairing, and multiplying from the right. -/
@[reassoc]
theorem pairRaw_actLeft_out
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    (M'.X ◁ actLeft A M.X) ≫ pairRaw A M M' d =
      (M'.X ◁ (β_ A M.X).hom) ≫ (α_ M'.X M.X A).inv ≫
        (pairRaw A M M' d ▷ A) ≫ μ[A] := by
  rw [pairRaw_actLeft_snd,
    reassoc_of% braid_cross_pair A (pairRaw A M M' d),
    IsCommMonObj.mul_comm]
  simp only [Iso.inv_hom_id_assoc]

/-- **Scalar extraction at the pair, second slot from the
right**: acting through the braided right action on the
`M`-factor multiplies the pairing from the right, with no
crossing at all. -/
@[reassoc]
theorem pairRaw_actRight_snd
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    (M'.X ◁ actRight A M.X) ≫ pairRaw A M M' d =
      (α_ M'.X M.X A).inv ≫ (pairRaw A M M' d ▷ A) ≫ μ[A] := by
  rw [actRight, MonoidalCategory.whiskerLeft_comp, Category.assoc,
    pairRaw_actLeft_out, ← MonoidalCategory.whiskerLeft_comp_assoc,
    SymmetricCategory.symmetry]
  simp

/-- The mirror inner extraction: acting on the left of the
`M`-factor before a whiskered pairing-and-braid block equals
braiding the scalar past the block and folding by
multiplication. -/
private theorem inner_extract_snd
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (R : D) :
    (M'.X ◁ ((α_ A M.X R).inv ≫ (actLeft A M.X ▷ R))) ≫
        (α_ M'.X M.X R).inv ≫ (pairRaw A M M' d ▷ R) ≫
        (β_ A R).hom =
      (M'.X ◁ (β_ A (M.X ⊗ R)).hom) ≫
        (α_ M'.X (M.X ⊗ R) A).inv ≫
        (((α_ M'.X M.X R).inv ≫ (pairRaw A M M' d ▷ R) ≫
            (β_ A R).hom) ▷ A) ≫
        (α_ R A A).hom ≫ (R ◁ μ[A]) := by
  rw [MonoidalCategory.whiskerLeft_comp, Category.assoc,
    associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight_assoc, pairRaw_actLeft_out]
  simp only [comp_whiskerRight, Category.assoc]
  rw [BraidedCategory.braiding_naturality_left μ[A] R,
    BraidedCategory.braiding_naturality_left_assoc
      (pairRaw A M M' d ▷ A) R]
  have hp : (pairRaw A M M' d ▷ R) ≫ (β_ A R).hom =
      (β_ (M'.X ⊗ M.X) R).hom ≫ (R ◁ pairRaw A M M' d) :=
    BraidedCategory.braiding_naturality_left _ R
  conv_rhs => rw [← comp_whiskerRight_assoc,
    ← comp_whiskerRight_assoc, Category.assoc, hp]
  simp only [comp_whiskerRight, Category.assoc]
  rw [associator_naturality_middle_assoc]
  rw [reassoc_of% cross_shuffle_snd M'.X M.X R A]

/-- **Scalar extraction at the last `M'`-factor**: acting on the
right of the exposed last factor of the `M'`-power equals braiding
the scalar past the whole `M`-power and multiplying the pairing
from the right. -/
theorem rawPair_actRight_last
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    ((tensorPow D M'.X n ◁ actRight A M'.X) ▷
        tensorPow D M.X (n + 1)) ≫ rawPair A M M' d (n + 1) =
      ((α_ (tensorPow D M'.X n) M'.X A).inv ▷
          tensorPow D M.X (n + 1)) ≫
        (α_ (tensorPow D M'.X (n + 1)) A
            (tensorPow D M.X (n + 1))).hom ≫
        (tensorPow D M'.X (n + 1) ◁
          (β_ A (tensorPow D M.X (n + 1))).hom) ≫
        (α_ (tensorPow D M'.X (n + 1)) (tensorPow D M.X (n + 1))
            A).inv ≫
        (rawPair A M M' d (n + 1) ▷ A) ≫ μ[A] := by
  conv_lhs =>
    change ((tensorPow D M'.X n ◁ actRight A M'.X) ▷
        tensorPow D M.X (n + 1)) ≫
      (((tensorPow D M'.X n ⊗ M'.X) ◁ (powPeel M.X n).hom) ≫
        (α_ (tensorPow D M'.X n) M'.X
          (M.X ⊗ tensorPow D M.X n)).hom ≫
        (tensorPow D M'.X n ◁
          (α_ M'.X M.X (tensorPow D M.X n)).inv) ≫
        (tensorPow D M'.X n ◁
          (pairRaw A M M' d ▷ tensorPow D M.X n)) ≫
        (tensorPow D M'.X n ◁ (β_ A (tensorPow D M.X n)).hom) ≫
        (α_ (tensorPow D M'.X n) (tensorPow D M.X n) A).inv ≫
        (rawPair A M M' d n ▷ A) ≫ μ[A])
  conv_lhs => rw [← whisker_exchange_assoc,
    associator_naturality_middle_assoc]
  conv_lhs => simp only [← MonoidalCategory.whiskerLeft_comp_assoc]
  conv_lhs => simp only [Category.assoc]
  conv_lhs => rw [inner_extract A M M' d (tensorPow D M.X n)]
  conv_rhs =>
    change ((α_ (tensorPow D M'.X n) M'.X A).inv ▷
        tensorPow D M.X (n + 1)) ≫
      (α_ (tensorPow D M'.X n ⊗ M'.X) A
        (tensorPow D M.X (n + 1))).hom ≫
      ((tensorPow D M'.X n ⊗ M'.X) ◁
        (β_ A (tensorPow D M.X (n + 1))).hom) ≫
      (α_ (tensorPow D M'.X n ⊗ M'.X) (tensorPow D M.X (n + 1))
        A).inv ≫
      ((((tensorPow D M'.X n ⊗ M'.X) ◁ (powPeel M.X n).hom) ≫
        (α_ (tensorPow D M'.X n) M'.X
          (M.X ⊗ tensorPow D M.X n)).hom ≫
        (tensorPow D M'.X n ◁
          (α_ M'.X M.X (tensorPow D M.X n)).inv) ≫
        (tensorPow D M'.X n ◁
          (pairRaw A M M' d ▷ tensorPow D M.X n)) ≫
        (tensorPow D M'.X n ◁ (β_ A (tensorPow D M.X n)).hom) ≫
        (α_ (tensorPow D M'.X n) (tensorPow D M.X n) A).inv ≫
        (rawPair A M M' d n ▷ A) ≫ μ[A]) ▷ A) ≫ μ[A]
  conv_rhs => simp only [comp_whiskerRight, Category.assoc]
  conv_rhs => rw [MonObj.mul_assoc,
    associator_naturality_left_assoc, ← whisker_exchange_assoc]
  conv_rhs => rw [← associator_inv_naturality_middle_assoc]
  conv_rhs => rw [← MonoidalCategory.whiskerLeft_comp_assoc,
    ← BraidedCategory.braiding_naturality_right,
    MonoidalCategory.whiskerLeft_comp]
  conv_rhs => simp only [Category.assoc]
  conv_rhs => rw [← associator_naturality_right_assoc]
  conv_rhs => rw [← whisker_exchange_assoc]
  monoidal

/-- **Generic scalar extraction at the `M'`-slot of the step**:
acting through the braided right action on the exposed `M'`-factor
equals braiding the scalar past the peeled block and multiplying
the step from the right. -/
theorem pairStep_actRight
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    {Q R : D} (r : Q ⊗ R ⟶ A) :
    ((Q ◁ actRight A M'.X) ▷ (M.X ⊗ R)) ≫
        pairStep A M M' d r =
      ((α_ Q M'.X A).inv ▷ (M.X ⊗ R)) ≫
        (α_ (Q ⊗ M'.X) A (M.X ⊗ R)).hom ≫
        ((Q ⊗ M'.X) ◁ (β_ A (M.X ⊗ R)).hom) ≫
        (α_ (Q ⊗ M'.X) (M.X ⊗ R) A).inv ≫
        (pairStep A M M' d r ▷ A) ≫ μ[A] := by
  conv_lhs => rw [pairStep]
  conv_lhs => rw [associator_naturality_middle_assoc]
  conv_lhs => rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  conv_lhs => simp only [Category.assoc]
  conv_lhs => rw [inner_extract A M M' d R]
  conv_rhs => rw [pairStep]
  conv_rhs => simp only [comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  conv_rhs => rw [MonObj.mul_assoc,
    associator_naturality_left_assoc, ← whisker_exchange_assoc]
  conv_lhs => simp only [MonoidalCategory.whiskerLeft_comp,
    Category.assoc]
  monoidal

/-- **Generic scalar extraction at the `M`-slot of the step**:
acting on the exposed head `M`-factor equals braiding the scalar
past the peeled block and multiplying the step from the right. -/
theorem pairStep_actHead
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    {Q R : D} (r : Q ⊗ R ⟶ A) :
    ((Q ⊗ M'.X) ◁ ((α_ A M.X R).inv ≫
        (actLeft A M.X ▷ R))) ≫ pairStep A M M' d r =
      ((Q ⊗ M'.X) ◁ (β_ A (M.X ⊗ R)).hom) ≫
        (α_ (Q ⊗ M'.X) (M.X ⊗ R) A).inv ≫
        (pairStep A M M' d r ▷ A) ≫ μ[A] := by
  conv_lhs => rw [pairStep]
  conv_lhs => rw [associator_naturality_right_assoc]
  conv_lhs => rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  conv_lhs => simp only [Category.assoc]
  conv_lhs => rw [inner_extract_snd A M M' d R]
  conv_rhs => rw [pairStep]
  conv_rhs => simp only [comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  conv_rhs => rw [MonObj.mul_assoc,
    associator_naturality_left_assoc, ← whisker_exchange_assoc]
  conv_lhs => simp only [MonoidalCategory.whiskerLeft_comp,
    Category.assoc]
  monoidal

/-- Over a symmetric base the left action is the braided right
action after one crossing. -/
theorem actLeft_eq_braid_actRight
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A]
    (X : D) [ModObj A X] :
    actLeft A X = (β_ A X).hom ≫ actRight A X := by
  rw [actRight, ← Category.assoc, SymmetricCategory.symmetry,
    Category.id_comp]

/-- Generic scalar extraction at the `M'`-slot, for a scalar
arriving from the left of the consumed factor. -/
theorem pairStep_actLeft_pair
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    {Q R : D} (r : Q ⊗ R ⟶ A) :
    ((Q ◁ actLeft A M'.X) ▷ (M.X ⊗ R)) ≫
        pairStep A M M' d r =
      ((Q ◁ (β_ A M'.X).hom) ▷ (M.X ⊗ R)) ≫
        ((α_ Q M'.X A).inv ▷ (M.X ⊗ R)) ≫
        (α_ (Q ⊗ M'.X) A (M.X ⊗ R)).hom ≫
        ((Q ⊗ M'.X) ◁ (β_ A (M.X ⊗ R)).hom) ≫
        (α_ (Q ⊗ M'.X) (M.X ⊗ R) A).inv ≫
        (pairStep A M M' d r ▷ A) ≫ μ[A] := by
  rw [actLeft_eq_braid_actRight, MonoidalCategory.whiskerLeft_comp,
    comp_whiskerRight, Category.assoc,
    pairStep_actRight A M M' d r]

/-- The scalar strand crossing the whole pairing block: crossing
factor by factor before the block equals letting the block fire
and crossing its output. -/
private theorem cross_block
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (R : D) :
    ((β_ A M'.X).hom ▷ (M.X ⊗ R)) ≫
        (α_ M'.X A (M.X ⊗ R)).hom ≫
        (M'.X ◁ (β_ A (M.X ⊗ R)).hom) ≫
        (α_ M'.X (M.X ⊗ R) A).inv ≫
        (((α_ M'.X M.X R).inv ≫ (pairRaw A M M' d ▷ R) ≫
          (β_ A R).hom) ▷ A) =
      (α_ A M'.X (M.X ⊗ R)).hom ≫
        (A ◁ ((α_ M'.X M.X R).inv ≫ (pairRaw A M M' d ▷ R) ≫
          (β_ A R).hom)) ≫
        (β_ A (R ⊗ A)).hom := by
  rw [BraidedCategory.braiding_naturality_right A
      ((α_ M'.X M.X R).inv ≫ (pairRaw A M M' d ▷ R) ≫
        (β_ A R).hom),
    BraidedCategory.braiding_tensor_right_hom A M'.X (M.X ⊗ R)]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The core of the top-slot slide, after both legs have been
opened: an identity between two routings of the scalar through
the pairing block, valid for every continuation. -/
private theorem slide_core
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    {Q R : D} (r : (Q ⊗ M'.X) ⊗ R ⟶ A) :
    ((α_ Q (M'.X ⊗ A) M'.X).inv ▷ (M.X ⊗ R)) ≫
      (α_ (Q ⊗ (M'.X ⊗ A)) M'.X (M.X ⊗ R)).hom ≫
      ((Q ⊗ (M'.X ⊗ A)) ◁ (α_ M'.X M.X R).inv) ≫
      ((Q ⊗ (M'.X ⊗ A)) ◁ (pairRaw A M M' d ▷ R)) ≫
      ((Q ⊗ (M'.X ⊗ A)) ◁ (β_ A R).hom) ≫
      (α_ (Q ⊗ (M'.X ⊗ A)) R A).inv ≫
      (((α_ Q M'.X A).inv ▷ R) ▷ A) ≫
      ((α_ (Q ⊗ M'.X) A R).hom ▷ A) ≫
      (((Q ⊗ M'.X) ◁ (β_ A R).hom) ▷ A) ≫
      ((α_ (Q ⊗ M'.X) R A).inv ▷ A) ≫
      (α_ ((Q ⊗ M'.X) ⊗ R) A A).hom ≫
      (((Q ⊗ M'.X) ⊗ R) ◁ μ[A]) ≫ (r ▷ A) ≫ μ[A] =
    ((Q ◁ (α_ M'.X A M'.X).hom) ▷ (M.X ⊗ R)) ≫
      ((α_ Q M'.X (A ⊗ M'.X)).inv ▷ (M.X ⊗ R)) ≫
      (((Q ⊗ M'.X) ◁ (β_ A M'.X).hom) ▷ (M.X ⊗ R)) ≫
      ((α_ (Q ⊗ M'.X) M'.X A).inv ▷ (M.X ⊗ R)) ≫
      (α_ ((Q ⊗ M'.X) ⊗ M'.X) A (M.X ⊗ R)).hom ≫
      (((Q ⊗ M'.X) ⊗ M'.X) ◁ (β_ A (M.X ⊗ R)).hom) ≫
      (α_ ((Q ⊗ M'.X) ⊗ M'.X) (M.X ⊗ R) A).inv ≫
      ((α_ (Q ⊗ M'.X) M'.X (M.X ⊗ R)).hom ▷ A) ≫
      (((Q ⊗ M'.X) ◁ (α_ M'.X M.X R).inv) ▷ A) ≫
      (((Q ⊗ M'.X) ◁ (pairRaw A M M' d ▷ R)) ▷ A) ≫
      (((Q ⊗ M'.X) ◁ (β_ A R).hom) ▷ A) ≫
      ((α_ (Q ⊗ M'.X) R A).inv ▷ A) ≫
      (α_ ((Q ⊗ M'.X) ⊗ R) A A).hom ≫
      (((Q ⊗ M'.X) ⊗ R) ◁ μ[A]) ≫ (r ▷ A) ≫ μ[A] := by
  trans (((α_ Q (M'.X ⊗ A) M'.X).inv ▷ (M.X ⊗ R)) ≫
    (α_ (Q ⊗ (M'.X ⊗ A)) M'.X (M.X ⊗ R)).hom ≫
    ((Q ⊗ (M'.X ⊗ A)) ◁ ((α_ M'.X M.X R).inv ≫
      (pairRaw A M M' d ▷ R) ≫ (β_ A R).hom)) ≫
    (α_ (Q ⊗ (M'.X ⊗ A)) R A).inv ≫
    (((α_ Q M'.X A).inv ▷ R) ▷ A) ≫
    ((α_ (Q ⊗ M'.X) A R).hom ▷ A) ≫
    (((Q ⊗ M'.X) ◁ (β_ A R).hom) ▷ A) ≫
    ((α_ (Q ⊗ M'.X) R A).inv ▷ A) ≫
    (α_ ((Q ⊗ M'.X) ⊗ R) A A).hom ≫
    (((Q ⊗ M'.X) ⊗ R) ◁ (β_ A A).hom) ≫
    (((Q ⊗ M'.X) ⊗ R) ◁ μ[A]) ≫ (r ▷ A) ≫ μ[A])
  · conv_rhs => rw [← MonoidalCategory.whiskerLeft_comp_assoc,
      IsCommMonObj.mul_comm]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  trans (((α_ Q (M'.X ⊗ A) M'.X).inv ▷ (M.X ⊗ R)) ≫
    (((α_ Q M'.X A).inv ▷ M'.X) ▷ (M.X ⊗ R)) ≫
    ((α_ (Q ⊗ M'.X) A M'.X).hom ▷ (M.X ⊗ R)) ≫
    (α_ (Q ⊗ M'.X) (A ⊗ M'.X) (M.X ⊗ R)).hom ≫
    ((Q ⊗ M'.X) ◁ ((α_ A M'.X (M.X ⊗ R)).hom ≫
      (A ◁ ((α_ M'.X M.X R).inv ≫ (pairRaw A M M' d ▷ R) ≫
        (β_ A R).hom)) ≫
      (β_ A (R ⊗ A)).hom)) ≫
    ((Q ⊗ M'.X) ◁ (α_ R A A).hom) ≫
    (α_ (Q ⊗ M'.X) R (A ⊗ A)).inv ≫
    (((Q ⊗ M'.X) ⊗ R) ◁ μ[A]) ≫ (r ▷ A) ≫ μ[A])
  · conv_rhs => rw [MonoidalCategory.whiskerLeft_comp,
      MonoidalCategory.whiskerLeft_comp,
      BraidedCategory.braiding_tensor_right_hom A R A]
    monoidal
  · conv_lhs => rw [← cross_block A M M' d R]
    monoidal

/-- **The top-slot slide law**: for a continuation pairing that
absorbs the braided right action on its last block factor — the
extraction property of the power pairing — the two legs of the
top slot window agree after the generic step. -/
theorem pairStep_slide
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') {Q R : D}
    (r : (Q ⊗ M'.X) ⊗ R ⟶ A)
    (hr : ((Q ◁ actRight A M'.X) ▷ R) ≫ r =
      ((α_ Q M'.X A).inv ▷ R) ≫ (α_ (Q ⊗ M'.X) A R).hom ≫
        ((Q ⊗ M'.X) ◁ (β_ A R).hom) ≫
        (α_ (Q ⊗ M'.X) R A).inv ≫ (r ▷ A) ≫ μ[A]) :
    ((Q ◁ winLegM A M'.X) ▷ (M.X ⊗ R)) ≫
        ((α_ Q M'.X M'.X).inv ▷ (M.X ⊗ R)) ≫
        pairStep A M M' d r =
      ((Q ◁ winLegN A M'.X) ▷ (M.X ⊗ R)) ≫
        ((α_ Q M'.X M'.X).inv ▷ (M.X ⊗ R)) ≫
        pairStep A M M' d r := by
  conv_lhs => rw [← comp_whiskerRight_assoc, winLegM,
    associator_inv_naturality_middle, comp_whiskerRight,
    Category.assoc, pairStep_precomp, hr]
  conv_rhs => rw [← comp_whiskerRight_assoc, winLegN,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    associator_inv_naturality_right, comp_whiskerRight,
    Category.assoc, comp_whiskerRight, Category.assoc,
    pairStep_actLeft_pair]
  conv_lhs => rw [pairStep]
  conv_lhs => simp only [comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  conv_lhs => rw [MonObj.mul_assoc,
    associator_naturality_left_assoc, ← whisker_exchange_assoc]
  conv_rhs => rw [pairStep]
  conv_rhs => simp only [comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  conv_rhs => rw [MonObj.mul_assoc,
    associator_naturality_left_assoc, ← whisker_exchange_assoc]
  exact slide_core A M M' d r

/-- The core of the head-slot slide: two routings of a scalar
born between the two consumed factors, for opaque pairing and
continuation. -/
private theorem slide_snd_core
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [IsCommMonObj A]
    (V' V P R : D)
    (u : V' ⊗ V ⟶ A) (t : P ⊗ (V ⊗ R) ⟶ A) :
    (α_ P V' (((V ⊗ A) ⊗ V) ⊗ R)).hom ≫
      (P ◁ (V' ◁ (α_ (V ⊗ A) V R).hom)) ≫
      (P ◁ (α_ V' (V ⊗ A) (V ⊗ R)).inv) ≫
      (P ◁ ((α_ V' V A).inv ▷ (V ⊗ R))) ≫
      (P ◁ (β_ ((V' ⊗ V) ⊗ A) (V ⊗ R)).hom) ≫
      (P ◁ ((V ⊗ R) ◁ (u ▷ A))) ≫
      (α_ P (V ⊗ R) (A ⊗ A)).inv ≫
      (t ▷ (A ⊗ A)) ≫ (A ◁ μ[A]) ≫ μ[A] =
    ((P ⊗ V') ◁ (α_ (V ⊗ A) V R).hom) ≫
      ((P ⊗ V') ◁ (α_ V A (V ⊗ R)).hom) ≫
      (α_ P V' (V ⊗ (A ⊗ (V ⊗ R)))).hom ≫
      (P ◁ (α_ V' V (A ⊗ (V ⊗ R))).inv) ≫
      (P ◁ (u ▷ (A ⊗ (V ⊗ R)))) ≫
      (P ◁ (β_ A (A ⊗ (V ⊗ R))).hom) ≫
      (α_ P (A ⊗ (V ⊗ R)) A).inv ≫
      ((P ◁ (β_ A (V ⊗ R)).hom) ▷ A) ≫
      ((α_ P (V ⊗ R) A).inv ▷ A) ≫
      (α_ (P ⊗ (V ⊗ R)) A A).hom ≫
      (t ▷ (A ⊗ A)) ≫ (A ◁ μ[A]) ≫ μ[A] := by
  have hpull : (β_ ((V' ⊗ V) ⊗ A) (V ⊗ R)).hom ≫
      ((V ⊗ R) ◁ (u ▷ A)) =
    ((u ▷ A) ▷ (V ⊗ R)) ≫ (β_ (A ⊗ A) (V ⊗ R)).hom :=
    (BraidedCategory.braiding_naturality_left (u ▷ A)
      (V ⊗ R)).symm
  conv_lhs => rw [← MonoidalCategory.whiskerLeft_comp_assoc P
    (β_ ((V' ⊗ V) ⊗ A) (V ⊗ R)).hom
    ((V ⊗ R) ◁ (u ▷ A)), hpull]
  conv_lhs => rw [show μ[A] = (β_ A A).hom ≫ μ[A] from
    (IsCommMonObj.mul_comm A).symm]
  conv_rhs => rw [BraidedCategory.braiding_tensor_right_hom
    A A (V ⊗ R)]
  conv_lhs => simp only [MonoidalCategory.whiskerLeft_comp,
    Category.assoc]
  conv_rhs => simp only [MonoidalCategory.whiskerLeft_comp,
    Category.assoc]
  conv_lhs => rw [IsCommMonObj.mul_comm]
  conv_lhs => rw [← whisker_exchange_assoc]
  conv_lhs => rw [← associator_inv_naturality_right_assoc]
  conv_lhs => rw [← MonoidalCategory.whiskerLeft_comp_assoc P
    (β_ (A ⊗ A) (V ⊗ R)).hom ((V ⊗ R) ◁ (β_ A A).hom)]
  conv_lhs => rw [show (β_ (A ⊗ A) (V ⊗ R)).hom ≫
      ((V ⊗ R) ◁ (β_ A A).hom) =
    ((β_ A A).hom ▷ (V ⊗ R)) ≫ (β_ (A ⊗ A) (V ⊗ R)).hom from
    (BraidedCategory.braiding_naturality_left (β_ A A).hom
      (V ⊗ R)).symm]
  conv_lhs => rw [BraidedCategory.braiding_tensor_left_hom
    A A (V ⊗ R)]
  monoidal

/-- Transport of the head peel along an arity equality. -/
private theorem powPeel_cast [Category.{v} D] [MonoidalCategory D]
    {X : D} {m n : ℕ} (h : m = n) :
    powCast X (by omega : m + 1 = n + 1) ≫ (powPeel X n).hom =
      (powPeel X m).hom ≫ (X ◁ powCast X h) := by
  subst h
  simp only [powCast_rfl, MonoidalCategory.whiskerLeft_id]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- A head slot leg followed by the double peel: the empty left
context is absorbed and the window fires at the exposed head
pair. -/
private theorem leg_head_snd_eq [Category.{v} D] [MonoidalCategory D] (A : D)
    {X : D}
    (w : (X ⊗ A) ⊗ X ⟶ X ⊗ X) (b : ℕ) :
    ((tensorPow D X 0 ◁ w) ▷ tensorPow D X b) ≫
      modPowGlue X 0 b ≫
      powCast X (by omega : 0 + 2 + b = b + 1 + 1) ≫
      (powPeel X (b + 1)).hom ≫ (X ◁ (powPeel X b).hom) =
    ((λ_ ((X ⊗ A) ⊗ X)).hom ▷ tensorPow D X b) ≫
      (w ▷ tensorPow D X b) ≫ (α_ X X (tensorPow D X b)).hom := by
  rw [modPowGlue]
  show ((tensorPow D X 0 ◁ w) ▷ tensorPow D X b) ≫
    (((α_ (tensorPow D X 0) X X).inv ▷ tensorPow D X b) ≫
      (tensorPowConcat X (0 + 2) b).hom) ≫
    powCast X (by omega : 0 + 2 + b = b + 1 + 1) ≫
    (powPeel X (b + 1)).hom ≫ (X ◁ (powPeel X b).hom) = _
  simp only [Category.assoc]
  rw [show powCast X (by omega : 0 + 2 + b = b + 1 + 1) =
    powCast X (by omega : 0 + 2 + b = 1 + b + 1) ≫
    powCast X (by omega : 1 + b + 1 = b + 1 + 1) from
    (powCast_comp X _ _).symm]
  simp only [Category.assoc]
  have h2 : powCast X (by omega : 1 + b + 1 = b + 1 + 1) ≫
      (powPeel X (b + 1)).hom ≫ (X ◁ (powPeel X b).hom) =
    (powPeel X (1 + b)).hom ≫
      (X ◁ (powCast X (by omega : 1 + b = b + 1) ≫
        (powPeel X b).hom)) := by
    rw [← Category.assoc,
      powPeel_cast (X := X) (by omega : 1 + b = b + 1)]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  refine Eq.trans (congrArg (fun t =>
    ((tensorPow D X 0 ◁ w) ▷ tensorPow D X b) ≫
    ((α_ (tensorPow D X 0) X X).inv ▷ tensorPow D X b) ≫
    (tensorPowConcat X (0 + 2) b).hom ≫
    powCast X (by omega : 0 + 2 + b = 1 + b + 1) ≫ t) h2) ?_
  have hc := reassoc_of% (concat_peel_head X 1 b)
  have h3 : (tensorPowConcat X (0 + 2) b).hom ≫
      powCast X (by omega : 0 + 2 + b = 1 + b + 1) ≫
      (powPeel X (1 + b)).hom ≫
      (X ◁ (powCast X (by omega : 1 + b = b + 1) ≫
        (powPeel X b).hom)) =
    ((powPeel X 1).hom ▷ tensorPow D X b) ≫
      (α_ X (tensorPow D X 1) (tensorPow D X b)).hom ≫
      (X ◁ (tensorPowConcat X 1 b).hom) ≫
      (X ◁ (powCast X (by omega : 1 + b = b + 1) ≫
        (powPeel X b).hom)) := hc _
  refine Eq.trans (congrArg (fun t =>
    ((tensorPow D X 0 ◁ w) ▷ tensorPow D X b) ≫
    ((α_ (tensorPow D X 0) X X).inv ▷ tensorPow D X b) ≫ t)
    h3) ?_
  have h4 : (tensorPowConcat X 1 b).hom ≫
      powCast X (by omega : 1 + b = b + 1) ≫
      (powPeel X b).hom =
    ((powPeel X 0).hom ▷ tensorPow D X b) ≫
      (α_ X (tensorPow D X 0) (tensorPow D X b)).hom ≫
      (X ◁ ((tensorPowConcat X 0 b).hom ≫
        powCast X (by omega : 0 + b = b))) := by
    rw [show powCast X (by omega : 1 + b = b + 1) =
      powCast X (by omega : 1 + b = 0 + b + 1) ≫
      powCast X (by omega : 0 + b + 1 = b + 1) from
      (powCast_comp X _ _).symm]
    rw [Category.assoc, powPeel_cast (X := X)
      (by omega : 0 + b = b)]
    have hc0 := reassoc_of% (concat_peel_head X 0 b)
    refine Eq.trans (hc0 _) ?_
    simp only [MonoidalCategory.whiskerLeft_comp]
  have h4' : (X ◁ (tensorPowConcat X 1 b).hom) ≫
      (X ◁ (powCast X (by omega : 1 + b = b + 1) ≫
        (powPeel X b).hom)) =
    X ◁ (((powPeel X 0).hom ▷ tensorPow D X b) ≫
      (α_ X (tensorPow D X 0) (tensorPow D X b)).hom ≫
      (X ◁ ((tensorPowConcat X 0 b).hom ≫
        powCast X (by omega : 0 + b = b)))) := by
    rw [← MonoidalCategory.whiskerLeft_comp, h4]
  refine Eq.trans (congrArg (fun t =>
    ((tensorPow D X 0 ◁ w) ▷ tensorPow D X b) ≫
    ((α_ (tensorPow D X 0) X X).inv ▷ tensorPow D X b) ≫
    ((powPeel X 1).hom ▷ tensorPow D X b) ≫
    (α_ X (tensorPow D X 1) (tensorPow D X b)).hom ≫ t)
    h4') ?_
  have h5 : (tensorPowConcat X 0 b).hom ≫
      powCast X (by omega : 0 + b = b) =
    (λ_ (tensorPow D X b)).hom := by
    refine Eq.trans (congrArg
      (fun t => t ≫ powCast X (by omega : 0 + b = b))
      (tensorPowConcat_zero_left (X := X) b)) ?_
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun t => (λ_ (tensorPow D X b)).hom ≫ t)
        (powCast_comp X _ _)).trans (Category.comp_id _))
  rw [h5]
  show ((𝟙_ D ◁ w) ▷ tensorPow D X b) ≫
    ((α_ (𝟙_ D) X X).inv ▷ tensorPow D X b) ≫
    (((((λ_ X).hom ≫ (ρ_ X).inv) ▷ X) ≫
      (α_ X (𝟙_ D) X).hom) ▷ tensorPow D X b) ≫
    (α_ X (𝟙_ D ⊗ X) (tensorPow D X b)).hom ≫
    (X ◁ ((((λ_ X).hom ≫ (ρ_ X).inv) ▷ tensorPow D X b) ≫
      (α_ X (𝟙_ D) (tensorPow D X b)).hom ≫
      (X ◁ (λ_ (tensorPow D X b)).hom))) =
    ((λ_ ((X ⊗ A) ⊗ X)).hom ▷ tensorPow D X b) ≫
    (w ▷ tensorPow D X b) ≫ (α_ X X (tensorPow D X b)).hom
  monoidal

/-- Transport of the power pairing along an arity equality. -/
theorem rawPair_cast [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') {m n : ℕ}
    (h : m = n) :
    rawPair A M M' d m =
      (powCast M'.X h ▷ tensorPow D M.X m) ≫
        (tensorPow D M'.X n ◁ powCast M.X h) ≫
        rawPair A M M' d n := by
  subst h
  simp only [powCast_rfl, MonoidalCategory.whiskerLeft_id,
    MonoidalCategory.id_whiskerRight, Category.id_comp]

/-- **The head-slot slide law**: the two legs of a slot window on
the first two `M`-factors agree after the doubled generic step.
The statement is closed — the continuation is arbitrary. -/
theorem pairStep_slide_snd
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    {Q R : D} (r : Q ⊗ R ⟶ A) :
    (((Q ⊗ M'.X) ⊗ M'.X) ◁
        ((winLegM A M.X ▷ R) ≫ (α_ M.X M.X R).hom)) ≫
      pairStep A M M' d (pairStep A M M' d r) =
    (((Q ⊗ M'.X) ⊗ M'.X) ◁
        ((winLegN A M.X ▷ R) ≫ (α_ M.X M.X R).hom)) ≫
      pairStep A M M' d (pairStep A M M' d r) := by
  have hN : ((((α_ M.X A M.X).hom ≫
      (M.X ◁ actLeft A M.X)) ▷ R) ≫ (α_ M.X M.X R).hom :
        ((M.X ⊗ A) ⊗ M.X) ⊗ R ⟶ M.X ⊗ (M.X ⊗ R)) =
    (α_ (M.X ⊗ A) M.X R).hom ≫ (α_ M.X A (M.X ⊗ R)).hom ≫
      (M.X ◁ ((α_ A M.X R).inv ≫ (actLeft A M.X ▷ R))) := by
    simp only [comp_whiskerRight, Category.assoc]
    monoidal
  conv_rhs => rw [winLegN, hN]
  conv_rhs => simp only [MonoidalCategory.whiskerLeft_comp,
    Category.assoc]
  conv_rhs => rw [pairStep_postcomp]
  conv_rhs => rw [pairStep_postcomp]
  have hArg : ((Q ⊗ M'.X) ◁ (α_ A M.X R).inv) ≫
      ((Q ⊗ M'.X) ◁ (actLeft A M.X ▷ R)) ≫
      pairStep A M M' d r =
    ((Q ⊗ M'.X) ◁ (β_ A (M.X ⊗ R)).hom) ≫
      (α_ (Q ⊗ M'.X) (M.X ⊗ R) A).inv ≫
      (pairStep A M M' d r ▷ A) ≫ μ[A] := by
    rw [← MonoidalCategory.whiskerLeft_comp_assoc]
    exact pairStep_actHead A M M' d r
  conv_rhs => rw [hArg]
  have hM : (M'.X ◁ ((actRight A M.X ▷ M.X ▷ R) ≫
        (α_ M.X M.X R).hom)) ≫
      (α_ M'.X M.X (M.X ⊗ R)).inv ≫
      (pairRaw A M M' d ▷ (M.X ⊗ R)) ≫
      (β_ A (M.X ⊗ R)).hom =
    (M'.X ◁ (α_ (M.X ⊗ A) M.X R).hom) ≫
      (α_ M'.X (M.X ⊗ A) (M.X ⊗ R)).inv ≫
      ((α_ M'.X M.X A).inv ▷ (M.X ⊗ R)) ≫
      (β_ ((M'.X ⊗ M.X) ⊗ A) (M.X ⊗ R)).hom ≫
      ((M.X ⊗ R) ◁ (pairRaw A M M' d ▷ A)) ≫
      ((M.X ⊗ R) ◁ μ[A]) := by
    rw [associator_naturality_left,
      MonoidalCategory.whiskerLeft_comp, Category.assoc,
      associator_inv_naturality_middle_assoc,
      ← comp_whiskerRight_assoc, pairRaw_actRight_snd]
    simp only [comp_whiskerRight, Category.assoc]
    rw [BraidedCategory.braiding_naturality_left μ[A] (M.X ⊗ R),
      BraidedCategory.braiding_naturality_left_assoc
        (pairRaw A M M' d ▷ A) (M.X ⊗ R)]
  conv_lhs => rw [winLegM, pairStep]
  conv_lhs => rw [associator_naturality_right_assoc]
  conv_lhs => rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  conv_lhs => simp only [Category.assoc]
  conv_lhs => rw [hM]
  conv_rhs => rw [pairStep]
  conv_rhs => simp only [comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  conv_rhs => rw [MonObj.mul_assoc,
    associator_naturality_left_assoc, ← whisker_exchange_assoc]
  conv_lhs => simp only [MonoidalCategory.whiskerLeft_comp,
    Category.assoc]
  conv_lhs => rw [associator_inv_naturality_right_assoc,
    whisker_exchange_assoc]
  conv_rhs => rw [whisker_exchange_assoc]
  exact slide_snd_core A M'.X M.X (Q ⊗ M'.X) R
    (pairRaw A M M' d) (pairStep A M M' d r)

/-- A slot leg at the top decomposes as the window against the
unitor: the empty right context is absorbed. -/
private theorem leg_top_eq
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (M' : Mod D A)
    (w : (M'.X ⊗ A) ⊗ M'.X ⟶ M'.X ⊗ M'.X)
    (a : ℕ) :
    ((tensorPow D M'.X a ◁ w) ▷ tensorPow D M'.X 0) ≫
        modPowGlue M'.X a 0 =
      (ρ_ (tensorPow D M'.X a ⊗ ((M'.X ⊗ A) ⊗ M'.X))).hom ≫
        (tensorPow D M'.X a ◁ w) ≫
        (α_ (tensorPow D M'.X a) M'.X M'.X).inv := by
  rw [modPowGlue, tensorPowConcat_zero]
  change ((tensorPow D M'.X a ◁ w) ▷ 𝟙_ D) ≫
    ((α_ (tensorPow D M'.X a) M'.X M'.X).inv ▷ 𝟙_ D) ≫
    (ρ_ ((tensorPow D M'.X a ⊗ M'.X) ⊗ M'.X)).hom = _
  rw [← comp_whiskerRight_assoc,
    MonoidalCategory.rightUnitor_naturality]

/-- **The top slot relation of the power pairing**: at the slot
touching the last two factors of the `M'`-power, the two legs
pair equally. -/
theorem rawPair_rel_fst_top
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (a : ℕ) :
    (modPowLegM A M'.X a 0 ▷ tensorPow D M.X (a + 2)) ≫
        rawPair A M M' d (a + 2) =
      (modPowLegN A M'.X a 0 ▷ tensorPow D M.X (a + 2)) ≫
        rawPair A M M' d (a + 2) := by
  have hM : modPowLegM A M'.X a 0 =
      (ρ_ (tensorPow D M'.X a ⊗ ((M'.X ⊗ A) ⊗ M'.X))).hom ≫
        (tensorPow D M'.X a ◁ winLegM A M'.X) ≫
        (α_ (tensorPow D M'.X a) M'.X M'.X).inv := by
    rw [modPowLegM]; exact leg_top_eq A M' _ a
  have hN : modPowLegN A M'.X a 0 =
      (ρ_ (tensorPow D M'.X a ⊗ ((M'.X ⊗ A) ⊗ M'.X))).hom ≫
        (tensorPow D M'.X a ◁ winLegN A M'.X) ≫
        (α_ (tensorPow D M'.X a) M'.X M'.X).inv := by
    rw [modPowLegN]; exact leg_top_eq A M' _ a
  rw [hM, hN]
  show (((ρ_ (tensorPow D M'.X a ⊗ ((M'.X ⊗ A) ⊗ M'.X))).hom ≫
      (tensorPow D M'.X a ◁ winLegM A M'.X) ≫
      (α_ (tensorPow D M'.X a) M'.X M'.X).inv) ▷
        tensorPow D M.X (a + 1 + 1)) ≫
      rawPair A M M' d (a + 1 + 1) =
    (((ρ_ (tensorPow D M'.X a ⊗ ((M'.X ⊗ A) ⊗ M'.X))).hom ≫
      (tensorPow D M'.X a ◁ winLegN A M'.X) ≫
      (α_ (tensorPow D M'.X a) M'.X M'.X).inv) ▷
        tensorPow D M.X (a + 1 + 1)) ≫
      rawPair A M M' d (a + 1 + 1)
  rw [rawPair_succ_step]
  simp only [comp_whiskerRight, Category.assoc, cancel_epi]
  show ((tensorPow D M'.X a ◁ winLegM A M'.X) ▷
      tensorPow D M.X (a + 1 + 1)) ≫
    ((α_ (tensorPow D M'.X a) M'.X M'.X).inv ▷
      tensorPow D M.X (a + 1 + 1)) ≫
    (((tensorPow D M'.X a ⊗ M'.X) ⊗ M'.X) ◁
      (powPeel M.X (a + 1)).hom) ≫
    pairStep A M M' d (rawPair A M M' d (a + 1)) =
  ((tensorPow D M'.X a ◁ winLegN A M'.X) ▷
      tensorPow D M.X (a + 1 + 1)) ≫
    ((α_ (tensorPow D M'.X a) M'.X M'.X).inv ▷
      tensorPow D M.X (a + 1 + 1)) ≫
    (((tensorPow D M'.X a ⊗ M'.X) ⊗ M'.X) ◁
      (powPeel M.X (a + 1)).hom) ≫
    pairStep A M M' d (rawPair A M M' d (a + 1))
  rw [← whisker_exchange_assoc, ← whisker_exchange_assoc,
    ← whisker_exchange_assoc]
  rw [cancel_epi]
  exact pairStep_slide A M M' d (rawPair A M M' d (a + 1))
    (rawPair_actRight_last A M M' d a)

/-- A slot leg with a non-empty right context peels its top
factor: the leg at the extended context is the leg at the lower
context whiskered by the exposed factor. -/
private theorem leg_step_eq
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (M' : Mod D A)
    (w : (M'.X ⊗ A) ⊗ M'.X ⟶ M'.X ⊗ M'.X)
    (a b : ℕ) :
    ((tensorPow D M'.X a ◁ w) ▷ tensorPow D M'.X (b + 1)) ≫
        modPowGlue M'.X a (b + 1) =
      (α_ (tensorPow D M'.X a ⊗ ((M'.X ⊗ A) ⊗ M'.X))
          (tensorPow D M'.X b) M'.X).inv ≫
        ((((tensorPow D M'.X a ◁ w) ▷ tensorPow D M'.X b) ≫
          modPowGlue M'.X a b) ▷ M'.X) := by
  rw [modPowGlue, modPowGlue, tensorPowConcat_succ]
  show ((tensorPow D M'.X a ◁ w) ▷
      (tensorPow D M'.X b ⊗ M'.X)) ≫
    ((α_ (tensorPow D M'.X a) M'.X M'.X).inv ▷
      (tensorPow D M'.X b ⊗ M'.X)) ≫
    (α_ ((tensorPow D M'.X a ⊗ M'.X) ⊗ M'.X) (tensorPow D M'.X b)
      M'.X).inv ≫
    ((tensorPowConcat M'.X (a + 2) b).hom ▷ M'.X) = _
  rw [associator_inv_naturality_left_assoc,
    associator_inv_naturality_left_assoc]
  simp only [comp_whiskerRight]
  rfl

/-- **The first slot relations of the power pairing**: at every
slot of the `M'`-power, the two legs pair equally. -/
theorem rawPair_rel_fst
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') (a : ℕ) :
    ∀ b : ℕ,
      (modPowLegM A M'.X a b ▷ tensorPow D M.X (a + 2 + b)) ≫
          rawPair A M M' d (a + 2 + b) =
        (modPowLegN A M'.X a b ▷ tensorPow D M.X (a + 2 + b)) ≫
          rawPair A M M' d (a + 2 + b)
  | 0 => rawPair_rel_fst_top A M M' d a
  | b + 1 => by
    have hM : modPowLegM A M'.X a (b + 1) =
        (α_ (tensorPow D M'.X a ⊗ ((M'.X ⊗ A) ⊗ M'.X))
          (tensorPow D M'.X b) M'.X).inv ≫
          (modPowLegM A M'.X a b ▷ M'.X) := by
      rw [modPowLegM, modPowLegM]
      exact leg_step_eq A M' _ a b
    have hN : modPowLegN A M'.X a (b + 1) =
        (α_ (tensorPow D M'.X a ⊗ ((M'.X ⊗ A) ⊗ M'.X))
          (tensorPow D M'.X b) M'.X).inv ≫
          (modPowLegN A M'.X a b ▷ M'.X) := by
      rw [modPowLegN, modPowLegN]
      exact leg_step_eq A M' _ a b
    rw [hM, hN]
    show (((α_ (tensorPow D M'.X a ⊗ ((M'.X ⊗ A) ⊗ M'.X))
        (tensorPow D M'.X b) M'.X).inv ≫
        (modPowLegM A M'.X a b ▷ M'.X)) ▷
          tensorPow D M.X (a + 2 + b + 1)) ≫
        rawPair A M M' d (a + 2 + b + 1) =
      (((α_ (tensorPow D M'.X a ⊗ ((M'.X ⊗ A) ⊗ M'.X))
        (tensorPow D M'.X b) M'.X).inv ≫
        (modPowLegN A M'.X a b ▷ M'.X)) ▷
          tensorPow D M.X (a + 2 + b + 1)) ≫
        rawPair A M M' d (a + 2 + b + 1)
    simp only [comp_whiskerRight, Category.assoc, cancel_epi]
    rw [rawPair_succ_step]
    show ((modPowLegM A M'.X a b ▷ M'.X) ▷
        tensorPow D M.X (a + 2 + b + 1)) ≫
      ((tensorPow D M'.X (a + 2 + b) ⊗ M'.X) ◁
        (powPeel M.X (a + 2 + b)).hom) ≫
      pairStep A M M' d (rawPair A M M' d (a + 2 + b)) =
    ((modPowLegN A M'.X a b ▷ M'.X) ▷
        tensorPow D M.X (a + 2 + b + 1)) ≫
      ((tensorPow D M'.X (a + 2 + b) ⊗ M'.X) ◁
        (powPeel M.X (a + 2 + b)).hom) ≫
      pairStep A M M' d (rawPair A M M' d (a + 2 + b))
    rw [← whisker_exchange_assoc, ← whisker_exchange_assoc]
    rw [pairStep_precomp, pairStep_precomp,
      rawPair_rel_fst A M M' d a b]

/-- **The second slot relations of the power pairing**: at every
slot of the `M`-power, the two legs pair equally. -/
theorem rawPair_rel_snd
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') (b : ℕ) :
    ∀ (a m : ℕ) (h : a + 2 + b = m),
      (tensorPow D M'.X m ◁
          (modPowLegM A M.X a b ≫ powCast M.X h)) ≫
          rawPair A M M' d m =
        (tensorPow D M'.X m ◁
          (modPowLegN A M.X a b ≫ powCast M.X h)) ≫
          rawPair A M M' d m
  | 0, m, h => by
    subst h
    rw [rawPair_cast A M M' d (by omega : 0 + 2 + b = b + 1 + 1)]
    rw [rawPair_succ_step, rawPair_succ_step,
      ← pairStep_postcomp]
    rw [powCast_rfl, Category.comp_id, Category.comp_id]
    rw [whisker_exchange_assoc, whisker_exchange_assoc]
    refine congrArg (CategoryStruct.comp _) ?_
    have hside : ∀ w : (M.X ⊗ A) ⊗ M.X ⟶ M.X ⊗ M.X,
        (tensorPow D M'.X (b + 1 + 1) ◁
          (((tensorPow D M.X 0 ◁ w) ▷ tensorPow D M.X b) ≫
            modPowGlue M.X 0 b)) ≫
        (tensorPow D M'.X (b + 1 + 1) ◁
          powCast M.X (by omega : 0 + 2 + b = b + 1 + 1)) ≫
        (tensorPow D M'.X (b + 1 + 1) ◁
          (powPeel M.X (b + 1)).hom) ≫
        ((tensorPow D M'.X (b + 1) ⊗ M'.X) ◁
          (M.X ◁ (powPeel M.X b).hom)) ≫
        pairStep A M M' d
          (pairStep A M M' d (rawPair A M M' d b)) =
      ((tensorPow D M'.X (b + 1) ⊗ M'.X) ◁
          (((λ_ ((M.X ⊗ A) ⊗ M.X)).hom ▷ tensorPow D M.X b) ≫
            (w ▷ tensorPow D M.X b) ≫
            (α_ M.X M.X (tensorPow D M.X b)).hom)) ≫
        pairStep A M M' d
          (pairStep A M M' d (rawPair A M M' d b)) := by
      intro w
      show ((tensorPow D M'.X (b + 1) ⊗ M'.X) ◁
          (((tensorPow D M.X 0 ◁ w) ▷ tensorPow D M.X b) ≫
            modPowGlue M.X 0 b)) ≫
        ((tensorPow D M'.X (b + 1) ⊗ M'.X) ◁
          powCast M.X (by omega : 0 + 2 + b = b + 1 + 1)) ≫
        ((tensorPow D M'.X (b + 1) ⊗ M'.X) ◁
          (powPeel M.X (b + 1)).hom) ≫
        ((tensorPow D M'.X (b + 1) ⊗ M'.X) ◁
          (M.X ◁ (powPeel M.X b).hom)) ≫
        pairStep A M M' d
          (pairStep A M M' d (rawPair A M M' d b)) = _
      rw [← MonoidalCategory.whiskerLeft_comp_assoc,
        ← MonoidalCategory.whiskerLeft_comp_assoc,
        ← MonoidalCategory.whiskerLeft_comp_assoc]
      conv_lhs => simp only [Category.assoc]
      rw [leg_head_snd_eq A w b]
      rfl
    refine ((hside (winLegM A M.X)).trans ?_).trans
      (hside (winLegN A M.X)).symm
    rw [MonoidalCategory.whiskerLeft_comp _
        ((λ_ ((M.X ⊗ A) ⊗ M.X)).hom ▷ tensorPow D M.X b),
      MonoidalCategory.whiskerLeft_comp _
        ((λ_ ((M.X ⊗ A) ⊗ M.X)).hom ▷ tensorPow D M.X b),
      Category.assoc, Category.assoc]
    refine congrArg (CategoryStruct.comp
      ((tensorPow D M'.X (b + 1) ⊗ M'.X) ◁
        ((λ_ ((M.X ⊗ A) ⊗ M.X)).hom ▷ tensorPow D M.X b))) ?_
    exact pairStep_slide_snd A M M' d (rawPair A M M' d b)
  | a + 1, m, h => by
    subst h
    rw [powCast_rfl, Category.comp_id, Category.comp_id]
    rw [rawPair_cast A M M' d
      (by omega : a + 1 + 2 + b = a + 2 + b + 1)]
    rw [rawPair_succ_step]
    rw [whisker_exchange_assoc, whisker_exchange_assoc]
    refine congrArg (CategoryStruct.comp _) ?_
    have hIH := rawPair_rel_snd A M M' d b a (a + 2 + b) rfl
    rw [powCast_rfl, Category.comp_id, Category.comp_id] at hIH
    have hstep : ∀ w : (M.X ⊗ A) ⊗ M.X ⟶ M.X ⊗ M.X,
        (tensorPow D M'.X (a + 2 + b + 1) ◁
          (((tensorPow D M.X (a + 1) ◁ w) ▷ tensorPow D M.X b) ≫
            modPowGlue M.X (a + 1) b)) ≫
        (tensorPow D M'.X (a + 2 + b + 1) ◁
          powCast M.X
            (by omega : a + 1 + 2 + b = a + 2 + b + 1)) ≫
        (tensorPow D M'.X (a + 2 + b + 1) ◁
          (powPeel M.X (a + 2 + b)).hom) ≫
        pairStep A M M' d (rawPair A M M' d (a + 2 + b)) =
      (tensorPow D M'.X (a + 2 + b + 1) ◁
        (((powPeel M.X a).hom ▷ ((M.X ⊗ A) ⊗ M.X)) ▷
          tensorPow D M.X b)) ≫
      (tensorPow D M'.X (a + 2 + b + 1) ◁
        ((α_ M.X (tensorPow D M.X a)
          ((M.X ⊗ A) ⊗ M.X)).hom ▷ tensorPow D M.X b)) ≫
      (tensorPow D M'.X (a + 2 + b + 1) ◁
        (α_ M.X (tensorPow D M.X a ⊗ ((M.X ⊗ A) ⊗ M.X))
          (tensorPow D M.X b)).hom) ≫
      ((tensorPow D M'.X (a + 2 + b) ⊗ M'.X) ◁
        (M.X ◁ (((tensorPow D M.X a ◁ w) ▷
          tensorPow D M.X b) ≫ modPowGlue M.X a b))) ≫
      pairStep A M M' d (rawPair A M M' d (a + 2 + b)) := by
      intro w
      rw [← MonoidalCategory.whiskerLeft_comp_assoc,
        ← MonoidalCategory.whiskerLeft_comp_assoc]
      conv_lhs => simp only [Category.assoc]
      rw [leg_step_snd_eq w a b]
      rw [MonoidalCategory.whiskerLeft_comp,
        MonoidalCategory.whiskerLeft_comp,
        MonoidalCategory.whiskerLeft_comp]
      simp only [Category.assoc]
      rfl
    refine ((hstep (winLegM A M.X)).trans ?_).trans
      (hstep (winLegN A M.X)).symm
    refine congrArg (CategoryStruct.comp _) ?_
    refine congrArg (CategoryStruct.comp _) ?_
    refine congrArg (CategoryStruct.comp _) ?_
    exact (pairStep_postcomp A M M' d (modPowLegM A M.X a b)
        (rawPair A M M' d (a + 2 + b))).trans
      ((congrArg (pairStep A M M' d) hIH).trans
        (pairStep_postcomp A M M' d (modPowLegN A M.X a b)
          (rawPair A M M' d (a + 2 + b))).symm)

/-- **Extraction propagates through the step**: the step over an
extracted continuation is the extraction of the step, with the
scalar crossing the continuation block. -/
theorem pairStep_ext [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    {Q R : D} (r : Q ⊗ R ⟶ A) :
    pairStep A M M' d ((Q ◁ (β_ A R).hom) ≫
        (α_ Q R A).inv ≫ (r ▷ A) ≫ μ[A]) =
      ((Q ⊗ M'.X) ◁ (M.X ◁ (β_ A R).hom)) ≫
        ((Q ⊗ M'.X) ◁ (α_ M.X R A).inv) ≫
        (α_ (Q ⊗ M'.X) (M.X ⊗ R) A).inv ≫
        (pairStep A M M' d r ▷ A) ≫ μ[A] := by
  conv_lhs => rw [pairStep]
  conv_lhs => simp only [comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  conv_lhs => rw [MonObj.mul_assoc,
    associator_naturality_left_assoc, ← whisker_exchange_assoc]
  conv_rhs => rw [pairStep]
  conv_rhs => simp only [comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  conv_rhs => rw [MonObj.mul_assoc,
    associator_naturality_left_assoc, ← whisker_exchange_assoc]
  conv_lhs => rw [BraidedCategory.braiding_tensor_right_hom
    A A R]
  conv_rhs => rw [show ((Q ⊗ R) ◁ μ[A]) =
    ((Q ⊗ R) ◁ ((β_ A A).hom ≫ μ[A])) from
    congrArg (fun t => (Q ⊗ R) ◁ t)
      (IsCommMonObj.mul_comm A).symm]
  conv_rhs => rw [MonoidalCategory.whiskerLeft_comp]
  trans ((α_ Q M'.X (M.X ⊗ (A ⊗ R))).hom ≫
    (Q ◁ (α_ M'.X M.X (A ⊗ R)).inv) ≫
    (Q ◁ (pairRaw A M M' d ▷ (A ⊗ R))) ≫
    (Q ◁ ((α_ A A R).inv ≫ ((β_ A A).hom ▷ R) ≫
      (α_ A A R).hom ≫ (A ◁ (β_ A R).hom) ≫
      (α_ A R A).inv ≫ ((β_ A R).hom ▷ A) ≫
      (α_ R A A).hom)) ≫
    (Q ◁ (R ◁ μ[A])) ≫
    (α_ Q R A).inv ≫ (r ▷ A) ≫ μ[A])
  · monoidal
  · rw [BraidedCategory.yang_baxter]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc Q
      (pairRaw A M M' d ▷ (A ⊗ R))]
    rw [← whisker_exchange_assoc]
    simp only [MonoidalCategory.whiskerLeft_comp,
      Category.assoc]
    monoidal

/-- The tail action passes the head peel: acting on the last
factor and peeling the head equals peeling, braiding past the
exposed head, and acting on the tail below. -/
private theorem powTailAct_peel
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] {X : D}
    [ModObj A X] (n : ℕ) :
    powTailAct A X (n + 1) ≫ (powPeel X (n + 1)).hom =
      (A ◁ (powPeel X (n + 1)).hom) ≫
        (braidPast A X (tensorPow D X (n + 1))).hom ≫
        (X ◁ powTailAct A X n) := by
  rw [powTailAct_eq, powTailAct_eq]
  rw [show (powPeel X (n + 1)).hom =
    ((powPeel X n).hom ▷ X) ≫
      (α_ X (tensorPow D X n) X).hom from rfl]
  show actAcross A (tensorPow D X (n + 1)) X ≫
      ((powPeel X n).hom ▷ X) ≫
      (α_ X (tensorPow D X n) X).hom =
    (A ◁ (((powPeel X n).hom ▷ X) ≫
      (α_ X (tensorPow D X n) X).hom)) ≫
      (braidPast A X (tensorPow D X n ⊗ X)).hom ≫
      (X ◁ actAcross A (tensorPow D X n) X)
  rw [← actAcross_natural_assoc, actAcross_context_split]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]

/-- **Scalar extraction at the tail of the `M`-power**: the tail
action on the `M`-power extracts as the scalar braiding past the
whole power and multiplying the pairing from the right. -/
theorem rawPair_actTail
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    ∀ n : ℕ,
    (tensorPow D M'.X (n + 1) ◁ powTailAct A M.X n) ≫
        rawPair A M M' d (n + 1) =
      (tensorPow D M'.X (n + 1) ◁
          (β_ A (tensorPow D M.X (n + 1))).hom) ≫
        (α_ (tensorPow D M'.X (n + 1)) (tensorPow D M.X (n + 1))
          A).inv ≫
        (rawPair A M M' d (n + 1) ▷ A) ≫ μ[A]
  | 0 => by
    have hact : powTailAct A M.X 0 ≫ (powPeel M.X 0).hom =
        (A ◁ (powPeel M.X 0).hom) ≫
          (α_ A M.X (tensorPow D M.X 0)).inv ≫
          (actLeft A M.X ▷ tensorPow D M.X 0) := by
      rw [powTailAct_eq]
      show ((α_ A (tensorPow D M.X 0) M.X).inv ≫
        ((β_ A (𝟙_ D)).hom ▷ M.X) ≫
        (α_ (𝟙_ D) A M.X).hom ≫
        ((𝟙_ D) ◁ actLeft A M.X)) ≫
        ((λ_ M.X).hom ≫ (ρ_ M.X).inv) =
        (A ◁ ((λ_ M.X).hom ≫ (ρ_ M.X).inv)) ≫
          (α_ A M.X (𝟙_ D)).inv ≫
          (actLeft A M.X ▷ 𝟙_ D)
      rw [braiding_tensorUnit_right]
      monoidal
    rw [rawPair_succ_step]
    conv_lhs => rw [← MonoidalCategory.whiskerLeft_comp_assoc,
      hact]
    conv_lhs => simp only [MonoidalCategory.whiskerLeft_comp,
      Category.assoc]
    show ((tensorPow D M'.X 0 ⊗ M'.X) ◁
        (A ◁ (powPeel M.X 0).hom)) ≫
      ((tensorPow D M'.X 0 ⊗ M'.X) ◁
        (α_ A M.X (tensorPow D M.X 0)).inv) ≫
      ((tensorPow D M'.X 0 ⊗ M'.X) ◁
        (actLeft A M.X ▷ tensorPow D M.X 0)) ≫
      pairStep A M M' d (rawPair A M M' d 0) = _
    rw [← MonoidalCategory.whiskerLeft_comp_assoc
      (tensorPow D M'.X 0 ⊗ M'.X)
      (α_ A M.X (tensorPow D M.X 0)).inv]
    rw [pairStep_actHead]
    conv_rhs => rw [comp_whiskerRight]
    conv_rhs => simp only [Category.assoc]
    conv_rhs => rw [← associator_inv_naturality_middle_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      ← BraidedCategory.braiding_naturality_right,
      MonoidalCategory.whiskerLeft_comp]
    conv_rhs =>
      rw [show (tensorPow D M'.X 1 ◁
          (A ◁ (powPeel M.X 0).hom)) =
        ((tensorPow D M'.X 0 ⊗ M'.X) ◁
          (A ◁ (powPeel M.X 0).hom)) from rfl]
    conv_rhs => simp only [Category.assoc]
    refine congrArg (CategoryStruct.comp
      ((tensorPow D M'.X 0 ⊗ M'.X) ◁
        (A ◁ (powPeel M.X 0).hom))) ?_
    monoidal
  | n + 1 => by
    rw [rawPair_succ_step]
    conv_lhs => rw [← MonoidalCategory.whiskerLeft_comp_assoc,
      powTailAct_peel A]
    conv_lhs => simp only [MonoidalCategory.whiskerLeft_comp,
      Category.assoc]
    show ((tensorPow D M'.X (n + 1) ⊗ M'.X) ◁
        (A ◁ (powPeel M.X (n + 1)).hom)) ≫
      ((tensorPow D M'.X (n + 1) ⊗ M'.X) ◁
        (braidPast A M.X (tensorPow D M.X (n + 1))).hom) ≫
      ((tensorPow D M'.X (n + 1) ⊗ M'.X) ◁
        (M.X ◁ powTailAct A M.X n)) ≫
      pairStep A M M' d (rawPair A M M' d (n + 1)) = _
    rw [pairStep_postcomp]
    rw [rawPair_actTail A M M' d n]
    rw [pairStep_ext]
    conv_rhs => rw [comp_whiskerRight]
    conv_rhs => simp only [Category.assoc]
    conv_rhs => rw [← associator_inv_naturality_middle_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      ← BraidedCategory.braiding_naturality_right,
      MonoidalCategory.whiskerLeft_comp]
    conv_rhs =>
      rw [show (tensorPow D M'.X (n + 1 + 1) ◁
          (A ◁ (powPeel M.X (n + 1)).hom)) =
        ((tensorPow D M'.X (n + 1) ⊗ M'.X) ◁
          (A ◁ (powPeel M.X (n + 1)).hom)) from rfl]
    conv_rhs => simp only [Category.assoc]
    refine congrArg (CategoryStruct.comp
      ((tensorPow D M'.X (n + 1) ⊗ M'.X) ◁
        (A ◁ (powPeel M.X (n + 1)).hom))) ?_
    conv_rhs => rw [BraidedCategory.braiding_tensor_right_hom
      A M.X (tensorPow D M.X (n + 1))]
    simp only [braidPast_hom, MonoidalCategory.whiskerLeft_comp,
      Category.assoc]
    monoidal

/-- Braiding the scalar over the whole power and acting across to
the tail equals the braided right action at the last slot. -/
private theorem braid_powTailAct
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A]
    {X : D} [ModObj A X] (n : ℕ) :
    (β_ (tensorPow D X (n + 1)) A).hom ≫ powTailAct A X n =
      (α_ (tensorPow D X n) X A).hom ≫
        (tensorPow D X n ◁ actRight A X) := by
  rw [powTailAct_eq]
  show (β_ (tensorPow D X n ⊗ X) A).hom ≫
    ((α_ A (tensorPow D X n) X).inv ≫
      ((β_ A (tensorPow D X n)).hom ▷ X) ≫
      (α_ (tensorPow D X n) A X).hom ≫
      (tensorPow D X n ◁ actLeft A X)) = _
  rw [BraidedCategory.braiding_tensor_left_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, SymmetricCategory.symmetry]
  rw [actRight]
  simp only [MonoidalCategory.id_whiskerRight, Category.id_comp,
    MonoidalCategory.whiskerLeft_comp]
  monoidal

/-! ## The descended pairing

The two-stage descent of the raw pairing through the module-power
coequalizers, mirroring the descent of the raw multiplication:
the slot relations assemble over the biproduct legs, the first
stage descends the `M'`-power against the ambient `M`-power, and
the second stage descends the `M`-power.
-/

section Descent

/-- The first assembled leg as a sum over the slots. -/
private theorem legFst_eq_sum'
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [Preadditive D] [HasFiniteBiproducts D]
    {X : D} [ModObj A X] (n : ℕ) :
    modPowLegFst A X n = ∑ i : Fin (n - 1),
      biproduct.π (fun i : Fin (n - 1) =>
        modPowMid A X i.val (n - 2 - i.val)) i ≫
        (modPowLegM A X i.val (n - 2 - i.val) ≫
          powCast X (slot_decomp i)) := by
  conv_lhs => rw [← Category.id_comp (modPowLegFst A X n),
    ← biproduct.total]
  rw [Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Category.assoc, modPowLegFst, biproduct.ι_desc]

/-- The second assembled leg as a sum over the slots. -/
private theorem legSnd_eq_sum'
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] [Preadditive D]
    [HasFiniteBiproducts D]
    {X : D} [ModObj A X] (n : ℕ) :
    modPowLegSnd A X n = ∑ i : Fin (n - 1),
      biproduct.π (fun i : Fin (n - 1) =>
        modPowMid A X i.val (n - 2 - i.val)) i ≫
        (modPowLegN A X i.val (n - 2 - i.val) ≫
          powCast X (slot_decomp i)) := by
  conv_lhs => rw [← Category.id_comp (modPowLegSnd A X n),
    ← biproduct.total]
  rw [Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Category.assoc, modPowLegSnd, biproduct.ι_desc]

/-- A slot-wise condition assembles over the right-whiskered
legs. -/
private theorem legs_whiskerRight_cond'
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D]
    {X : D} [ModObj A X]
    {m : ℕ} {W Z : D} (k : tensorPow D X m ⊗ W ⟶ Z)
    (h : ∀ a b (hab : a + 2 + b = m),
      ((modPowLegM A X a b ≫ powCast X hab) ▷ W) ≫ k =
        ((modPowLegN A X a b ≫ powCast X hab) ▷ W) ≫ k) :
    (modPowLegFst A X m ▷ W) ≫ k =
      (modPowLegSnd A X m ▷ W) ≫ k := by
  rw [legFst_eq_sum' A, legSnd_eq_sum' A]
  rw [sum_whiskerRight, sum_whiskerRight,
    Preadditive.sum_comp, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := h i.val (m - 2 - i.val) (slot_decomp i)
  simp only [MonoidalCategory.comp_whiskerRight,
    Category.assoc] at hi ⊢
  rw [hi]

/-- A slot-wise condition assembles over the left-whiskered
legs. -/
private theorem legs_whiskerLeft_cond'
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D]
    {X : D} [ModObj A X]
    {n : ℕ} {W Z : D} (k : W ⊗ tensorPow D X n ⟶ Z)
    (h : ∀ a b (hab : a + 2 + b = n),
      (W ◁ (modPowLegM A X a b ≫ powCast X hab)) ≫ k =
        (W ◁ (modPowLegN A X a b ≫ powCast X hab)) ≫ k) :
    (W ◁ modPowLegFst A X n) ≫ k =
      (W ◁ modPowLegSnd A X n) ≫ k := by
  rw [legFst_eq_sum' A, legSnd_eq_sum' A]
  rw [whiskerLeft_sum, whiskerLeft_sum,
    Preadditive.sum_comp, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := h i.val (n - 2 - i.val) (slot_decomp i)
  simp only [MonoidalCategory.whiskerLeft_comp,
    Category.assoc] at hi ⊢
  rw [hi]

/-- The first slot relations, in cast-carrying form. -/
theorem rawPair_rel_fst'
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') {m : ℕ}
    (a b : ℕ) (hab : a + 2 + b = m) :
    ((modPowLegM A M'.X a b ≫ powCast M'.X hab) ▷
        tensorPow D M.X m) ≫ rawPair A M M' d m =
      ((modPowLegN A M'.X a b ≫ powCast M'.X hab) ▷
        tensorPow D M.X m) ≫ rawPair A M M' d m := by
  subst hab
  rw [powCast_rfl, Category.comp_id, Category.comp_id]
  exact rawPair_rel_fst A M M' d a b

/-- **The first stage of the pairing descent**: the raw pairing
descends through the `M'`-power against the ambient
`M`-power. -/
noncomputable def pairPowStage
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [Preadditive D] [HasFiniteBiproducts D] [MonoidalPreadditive D]
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    modPow A M'.X n ⊗ tensorPow D M.X n ⟶ A :=
  modPowWhiskerRightDesc A M'.X n (tensorPow D M.X n)
    (rawPair A M M' d n)
    (legs_whiskerRight_cond' A (rawPair A M M' d n)
      (fun a b hab => rawPair_rel_fst' A M M' d a b hab))

/-- Defining equation of the first stage. -/
@[reassoc (attr := simp)]
theorem modPowπ_whiskerRight_pairPowStage
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [Preadditive D] [HasFiniteBiproducts D] [MonoidalPreadditive D]
    (d : ModDualityDatum A M M') (n : ℕ) :
    (modPowπ A M'.X n ▷ tensorPow D M.X n) ≫
        pairPowStage A M M' d n = rawPair A M M' d n :=
  modPowπ_whiskerRight_desc A M'.X n (tensorPow D M.X n) _ _

/-- The first stage coequalizes the left-whiskered legs of the
`M`-power. -/
theorem pairPowStage_cond
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [Preadditive D] [HasFiniteBiproducts D] [MonoidalPreadditive D]
    (d : ModDualityDatum A M M') (n : ℕ) :
    (modPow A M'.X n ◁ modPowLegFst A M.X n) ≫
        pairPowStage A M M' d n =
      (modPow A M'.X n ◁ modPowLegSnd A M.X n) ≫
        pairPowStage A M M' d n := by
  apply modPow_whiskerRight_hom_ext A M'.X n
    (modPowSrc A M.X n)
  rw [← MonoidalCategory.whisker_exchange_assoc,
    ← MonoidalCategory.whisker_exchange_assoc,
    modPowπ_whiskerRight_pairPowStage]
  exact legs_whiskerLeft_cond' A (rawPair A M M' d n)
    (fun a b hab => rawPair_rel_snd A M M' d b a n hab)

/-- **The descended power pairing** on the module powers, in two
stages. -/
noncomputable def pairPow
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [Preadditive D] [HasFiniteBiproducts D] [MonoidalPreadditive D]
    (d : ModDualityDatum A M M') (n : ℕ) :
    modPow A M'.X n ⊗ modPow A M.X n ⟶ A :=
  modPowWhiskerLeftDesc A M.X (modPow A M'.X n) n
    (pairPowStage A M M' d n) (pairPowStage_cond A M M' d n)

/-- Defining equation of the descended pairing. -/
@[reassoc (attr := simp)]
theorem modPowπ_tensor_pairPow
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [Preadditive D] [HasFiniteBiproducts D] [MonoidalPreadditive D]
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    (modPowπ A M'.X n ⊗ₘ modPowπ A M.X n) ≫
        pairPow A M M' d n = rawPair A M M' d n := by
  rw [MonoidalCategory.tensorHom_def, Category.assoc, pairPow]
  rw [modPowπ_whiskerLeft_desc A M.X (modPow A M'.X n) n _ _]
  exact modPowπ_whiskerRight_pairPowStage A M M' d n

/-- **The middle relation**: the descended pairing coequalizes
the module-tensor legs of the power bundles. -/
theorem pairPow_middle_cond
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [Preadditive D] [HasFiniteBiproducts D] [MonoidalPreadditive D]
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    modTensorLegM A (modPowMod A M'.X n) (modPowMod A M.X n) ≫
        pairPow A M M' d (n + 1) =
      modTensorLegN A (modPowMod A M'.X n) (modPowMod A M.X n) ≫
        pairPow A M M' d (n + 1) := by
  rw [modTensorLegM, modTensorLegN]
  letI := modPowModObj A M'.X n
  letI := modPowModObj A M.X n
  show (actRight A (modPow A M'.X (n + 1)) ▷
      modPow A M.X (n + 1)) ≫ pairPow A M M' d (n + 1) =
    ((α_ (modPow A M'.X (n + 1)) A (modPow A M.X (n + 1))).hom ≫
      (modPow A M'.X (n + 1) ◁
        actLeft A (modPow A M.X (n + 1)))) ≫
      pairPow A M M' d (n + 1)
  apply modPow_whiskerLeft_hom_ext A M.X
    (modPow A M'.X (n + 1) ⊗ A) (n + 1)
  conv_lhs => rw [whisker_exchange_assoc, pairPow,
    modPowπ_whiskerLeft_desc]
  conv_rhs => simp only [Category.assoc]
  conv_rhs => rw [associator_naturality_right_assoc,
    show actLeft A (modPow A M.X (n + 1)) =
      modPowAct A M.X n from rfl,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_modPowπ_modPowAct,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    pairPow, modPowπ_whiskerLeft_desc]
  rw [← cancel_epi ((α_ (modPow A M'.X (n + 1)) A
    (tensorPow D M.X (n + 1))).inv)]
  apply modPow_whiskerRight_hom_ext A M'.X (n + 1)
    (A ⊗ tensorPow D M.X (n + 1))
  simp only [Iso.inv_hom_id_assoc]
  conv_rhs => rw [← whisker_exchange_assoc,
    modPowπ_whiskerRight_pairPowStage,
    rawPair_actTail A M M' d n]
  have hM' : (modPowπ A M'.X (n + 1) ▷ A) ≫
      actRight A (modPow A M'.X (n + 1)) =
    (β_ (tensorPow D M'.X (n + 1)) A).hom ≫
      powTailAct A M'.X n ≫ modPowπ A M'.X (n + 1) := by
    rw [actRight,
      show actLeft A (modPow A M'.X (n + 1)) =
        modPowAct A M'.X n from rfl,
      BraidedCategory.braiding_naturality_left_assoc,
      whiskerLeft_modPowπ_modPowAct]
  rw [reassoc_of% braid_powTailAct A n] at hM'
  have hM'w := congrArg
    (fun t => t ▷ tensorPow D M.X (n + 1)) hM'
  conv_lhs => rw [associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc, hM'w]
  have hstage1 : ∀ {Y : D} (x : Y ⟶ tensorPow D M'.X (n + 1)),
      ((x ≫ modPowπ A M'.X (n + 1)) ▷
        tensorPow D M.X (n + 1)) ≫
        pairPowStage A M M' d (n + 1) =
      (x ▷ tensorPow D M.X (n + 1)) ≫
        rawPair A M M' d (n + 1) := by
    intro Y x
    rw [comp_whiskerRight, Category.assoc,
      modPowπ_whiskerRight_pairPowStage]
  have hstage : ∀ {Y Y' : D} (f : Y ⟶ Y')
      (g : Y' ⟶ tensorPow D M'.X n ⊗ M'.X),
      (((f ≫ g) ≫ modPowπ A M'.X (n + 1)) ▷
        tensorPow D M.X (n + 1)) ≫
        pairPowStage A M M' d (n + 1) =
      (f ▷ tensorPow D M.X (n + 1)) ≫
        (g ▷ tensorPow D M.X (n + 1)) ≫
        rawPair A M M' d (n + 1) := by
    intro Y Y' f g
    refine (hstage1 (f ≫ g)).trans ?_
    rw [comp_whiskerRight, Category.assoc]
    rfl
  refine Eq.trans (congrArg (fun t =>
    (α_ (tensorPow D M'.X (n + 1)) A
      (tensorPow D M.X (n + 1))).inv ≫ t) (hstage _ _)) ?_
  conv_lhs => rw [rawPair_actRight_last A M M' d n]
  monoidal

/-- **The Mod-internal power pairing**: the descended pairing on
the module tensor product of the power bundles. -/
noncomputable def modPowPairing
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [Preadditive D] [HasFiniteBiproducts D] [MonoidalPreadditive D]
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    modTensor A (modPowMod A M'.X n) (modPowMod A M.X n) ⟶ A :=
  modTensorDesc A (modPowMod A M'.X n) (modPowMod A M.X n)
    (pairPow A M M' d (n + 1)) (pairPow_middle_cond A M M' d n)

/-- Defining equation of the Mod-internal power pairing. -/
@[reassoc (attr := simp)]
theorem modTensorπ_modPowPairing
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [Preadditive D] [HasFiniteBiproducts D] [MonoidalPreadditive D]
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    modTensorπ A (modPowMod A M'.X n) (modPowMod A M.X n) ≫
        modPowPairing A M M' d n =
      pairPow A M M' d (n + 1) :=
  modTensorπ_desc A _ _ _ _

section SymDescent

/-- The section of the symmetric power, as a morphism of
modules. -/
noncomputable def symPowσMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] [Preadditive D]
    [HasFiniteBiproducts D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    {X : D} [ModObj A X] (n : ℕ) :
    symPowMod A X n ⟶ modPowMod A X n :=
  letI := symPowModObj A X n
  letI := modPowModObj A X n
  Mod.Hom.mk (symPowσ A X (n + 1))
    (isModHom := ⟨(symPowσ_modPowAct A X n).symm⟩)

@[simp] theorem symPowσMod_hom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] [Preadditive D]
    [HasFiniteBiproducts D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    {X : D} [ModObj A X] (n : ℕ) :
    (symPowσMod A (X := X) n).hom = symPowσ A X (n + 1) :=
  rfl

/-- **The symmetric power pairing**: the Mod-internal pairing on
the symmetric powers, through the sections. -/
noncomputable def symPowPairing
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [Preadditive D] [HasFiniteBiproducts D] [MonoidalPreadditive D]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    modTensor A (symPowMod A M'.X n) (symPowMod A M.X n) ⟶ A :=
  modTensorMap A (symPowσMod A n) (symPowσMod A n) ≫
    modPowPairing A M M' d n

/-- Defining equation of the symmetric power pairing. -/
@[reassoc (attr := simp)]
theorem modTensorπ_symPowPairing
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [Preadditive D] [HasFiniteBiproducts D] [MonoidalPreadditive D]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    modTensorπ A (symPowMod A M'.X n) (symPowMod A M.X n) ≫
        symPowPairing A M M' d n =
      (symPowσ A M'.X (n + 1) ⊗ₘ symPowσ A M.X (n + 1)) ≫
        pairPow A M M' d (n + 1) := by
  rw [symPowPairing, modTensorπ_map_assoc,
    modTensorπ_modPowPairing]
  rfl

end SymDescent

end Descent

end Symmetric

end RS
