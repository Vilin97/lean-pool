/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SymMul

/-!
# The monoid action on module powers and symmetric powers

Over an internal commutative monoid `A` and a left module `X` in a
braided category, the tensor powers of `X` carry an `A`-action
through their last factor, with `A` braided past the lower factors.
This module descends that action through the coequalizers of
`SymAlg.lean`, making every positive module power and every positive
symmetric power a module again.

* `braidPast A V T`: the structural isomorphism carrying `A` across
  a context `V`, with naturality in both the context and the tail.
* `actAcross`/`tensorLeftModObj`: a module tensored with an object
  on the left is again a module, acting through the right factor —
  the braided mirror of `tensorRightModObj`.
* `powTailAct`: the induced action on `tensorPow D X (n + 1)`.
* `modPowAct`/`modPowModObj`: over a commutative monoid the tail
  action descends to the module power; the slot relations away from
  the top factor pass by naturality alone, and the top slot passes
  by one slot relation together with commutativity.
* `modPowAct_perm`/`modPowAct_alg`: the descended action commutes
  with the permutation action and its `ℂ`-linear extension.
* `symPowAct`/`symPowModObj`: the action descends to the symmetric
  power, with `symPowσ` a module map.
* `modPowMod`/`symPowMod`: the bundled modules.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## Braiding a monoid past a context -/

section BraidPast

/-- Carry an object across a context: the isomorphism
`A ⊗ (V ⊗ T) ≅ V ⊗ (A ⊗ T)` braiding `A` past `V`. -/
def braidPast [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (A V T : D) : A ⊗ (V ⊗ T) ≅ V ⊗ (A ⊗ T) :=
  (α_ A V T).symm ≪≫ whiskerRightIso (β_ A V) T ≪≫ α_ V A T

@[simp]
theorem braidPast_hom [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (A V T : D) :
    (braidPast A V T).hom =
      (α_ A V T).inv ≫ ((β_ A V).hom ▷ T) ≫ (α_ V A T).hom := by
  simp [braidPast]

/-- The carrying isomorphism is natural in the tail. -/
@[reassoc]
theorem braidPast_natural_tail
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (A V : D) {T T' : D} (g : T ⟶ T') :
    (A ◁ (V ◁ g)) ≫ (braidPast A V T').hom =
      (braidPast A V T).hom ≫ (V ◁ (A ◁ g)) := by
  simp only [braidPast_hom]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right]
  simp only [Category.assoc]

/-- The carrying isomorphism is natural in the context. -/
@[reassoc]
theorem braidPast_natural_context
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (A : D) {V V' : D} (f : V ⟶ V')
    (T : D) :
    (A ◁ (f ▷ T)) ≫ (braidPast A V' T).hom =
      (braidPast A V T).hom ≫ (f ▷ (A ⊗ T)) := by
  simp only [braidPast_hom]
  rw [associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_right,
    comp_whiskerRight_assoc, associator_naturality_left]
  simp only [Category.assoc]

/-- Carrying past a tensor context is carrying past the factors in
turn. -/
theorem braidPast_tensor_context
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (A V₁ V₂ T : D) :
    (α_ A (V₁ ⊗ V₂) T).inv ≫ ((β_ A (V₁ ⊗ V₂)).hom ▷ T) ≫
        (α_ (V₁ ⊗ V₂) A T).hom ≫ (α_ V₁ V₂ (A ⊗ T)).hom =
      (A ◁ (α_ V₁ V₂ T).hom) ≫ (braidPast A V₁ (V₂ ⊗ T)).hom ≫
        (V₁ ◁ (braidPast A V₂ T).hom) := by
  rw [BraidedCategory.braiding_tensor_right_hom]
  simp only [braidPast_hom, comp_whiskerRight, whiskerLeft_comp,
    Category.assoc]
  monoidal

/-- Carrying a tensor pair past a context is carrying the factors
past it in turn. -/
theorem braidPast_tensor_first
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (A₁ A₂ V T : D) :
    (α_ (A₁ ⊗ A₂) V T).inv ≫ ((β_ (A₁ ⊗ A₂) V).hom ▷ T) ≫
        (α_ V (A₁ ⊗ A₂) T).hom =
      (α_ A₁ A₂ (V ⊗ T)).hom ≫ (A₁ ◁ (braidPast A₂ V T).hom) ≫
        (braidPast A₁ V (A₂ ⊗ T)).hom ≫ (V ◁ (α_ A₁ A₂ T).inv) := by
  rw [BraidedCategory.braiding_tensor_left_hom]
  simp only [braidPast_hom, comp_whiskerRight, whiskerLeft_comp,
    Category.assoc]
  monoidal

end BraidPast

/-! ## The action through the right tensor factor -/

section ActAcross

/-- The action of a monoid on `V ⊗ X` through the right factor:
braid `A` past `V`, then act on `X`. -/
def actAcross [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A]
    (V X : D) [ModObj A X] : A ⊗ (V ⊗ X) ⟶ V ⊗ X :=
  (α_ A V X).inv ≫ ((β_ A V).hom ▷ X) ≫ (α_ V A X).hom ≫
    (V ◁ actLeft A X)

/-- The action through the right factor, through the carrying
isomorphism. -/
theorem actAcross_eq_braidPast
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A]
    (V X : D) [ModObj A X] :
    actAcross A V X = (braidPast A V X).hom ≫ (V ◁ actLeft A X) := by
  simp [actAcross]

/-- The action through the right factor is natural in the
context. -/
@[reassoc]
theorem actAcross_natural
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A]
    {V V' : D} (f : V ⟶ V') (X : D)
    [ModObj A X] :
    (A ◁ (f ▷ X)) ≫ actAcross A V' X = actAcross A V X ≫ (f ▷ X) := by
  rw [actAcross_eq_braidPast A V' X, actAcross_eq_braidPast A V X,
    ← Category.assoc, braidPast_natural_context, Category.assoc,
    ← whisker_exchange]
  simp only [Category.assoc]

/-- Unitality of the action through the right factor. -/
theorem one_actAcross
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A]
    (V X : D) [ModObj A X] :
    η[A] ▷ (V ⊗ X) ≫ actAcross A V X = (λ_ (V ⊗ X)).hom := by
  rw [actAcross, associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_left,
    braiding_tensorUnit_left, comp_whiskerRight_assoc,
    associator_naturality_middle_assoc, ← whiskerLeft_comp,
    one_actLeft]
  monoidal

/-- Associativity of the action through the right factor. -/
theorem mul_actAcross
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A]
    (V X : D) [ModObj A X] :
    μ[A] ▷ (V ⊗ X) ≫ actAcross A V X =
      (α_ A A (V ⊗ X)).hom ≫ (A ◁ actAcross A V X) ≫
        actAcross A V X := by
  have hL : μ[A] ▷ (V ⊗ X) ≫ actAcross A V X =
      (α_ A A (V ⊗ X)).hom ≫ (A ◁ (braidPast A V X).hom) ≫
        (braidPast A V (A ⊗ X)).hom ≫
        (V ◁ ((α_ A A X).inv ≫ μ[A] ▷ X ≫ actLeft A X)) := by
    rw [actAcross, associator_inv_naturality_left_assoc,
      ← comp_whiskerRight_assoc,
      BraidedCategory.braiding_naturality_left,
      comp_whiskerRight_assoc, associator_naturality_middle_assoc,
      reassoc_of% (braidPast_tensor_first A A V X)]
    simp only [whiskerLeft_comp]
  have hR : (A ◁ actAcross A V X) ≫ actAcross A V X =
      (A ◁ (braidPast A V X).hom) ≫ (braidPast A V (A ⊗ X)).hom ≫
        (V ◁ ((α_ A A X).inv ≫ μ[A] ▷ X ≫ actLeft A X)) := by
    rw [actAcross_eq_braidPast]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [braidPast_natural_tail_assoc, ← whiskerLeft_comp,
      actLeft_actLeft]
    simp only [whiskerLeft_comp]
  rw [hL, hR]

/-- A left module tensored with an object on the left: the action
of `A` on `V ⊗ X` through the right factor. -/
@[implicit_reducible]
def tensorLeftModObj
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A]
    (V X : D) [ModObj A X] : ModObj A (V ⊗ X) where
  smul := actAcross A V X
  one_smul := one_actAcross A V X
  mul_smul := mul_actAcross A V X

@[simp] theorem tensorLeftModObj_smul
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A]
    (V X : D) [ModObj A X] :
    (tensorLeftModObj A V X).smul =
      (α_ A V X).inv ≫ ((β_ A V).hom ▷ X) ≫ (α_ V A X).hom ≫
        (V ◁ actLeft A X) :=
  rfl

/-- The action through the right factor decomposes over a tensor
context: braid past the outer factor, then act through the
inner one. -/
@[reassoc]
theorem actAcross_context_split
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A]
    (V₁ V₂ X : D) [ModObj A X] :
    actAcross A (V₁ ⊗ V₂) X ≫ (α_ V₁ V₂ X).hom =
      (A ◁ (α_ V₁ V₂ X).hom) ≫ (braidPast A V₁ (V₂ ⊗ X)).hom ≫
        (V₁ ◁ actAcross A V₂ X) := by
  rw [actAcross]
  simp only [Category.assoc]
  rw [associator_naturality_right,
    reassoc_of% (braidPast_tensor_context A V₁ V₂ X),
    actAcross_eq_braidPast]
  simp only [whiskerLeft_comp]

/-- The action through the right factor of a two-step context,
conjugated by the associator: braid past the outer factor, act
inside the last two. -/
theorem actAcross_split_last
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A]
    (V X : D) [ModObj A X] :
    (A ◁ (α_ V X X).inv) ≫ actAcross A (V ⊗ X) X =
      (braidPast A V (X ⊗ X)).hom ≫ (V ◁ actAcross A X X) ≫
        (α_ V X X).inv := by
  rw [← cancel_mono (α_ V X X).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [actAcross_context_split, ← whiskerLeft_comp_assoc,
    Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]

/-- An action through the right factor, precomposed with a
reassociated whiskered morphism into the context. -/
theorem whiskerLeft_associator_inv_actAcross
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A]
    {P₁ P₂ Q : D}
    (g : P₁ ⊗ P₂ ⟶ Q) (X : D) [ModObj A X] {Z : D} (p : Q ⊗ X ⟶ Z) :
    (A ◁ ((α_ P₁ P₂ X).inv ≫ (g ▷ X))) ≫ actAcross A Q X ≫ p =
      (A ◁ (α_ P₁ P₂ X).inv) ≫ actAcross A (P₁ ⊗ P₂) X ≫
        (g ▷ X) ≫ p := by
  rw [whiskerLeft_comp, Category.assoc, actAcross_natural_assoc]

/-- Over a commutative monoid the braided self-crossing of the
action agrees with the plain iterated action. -/
theorem actAcross_actLeft
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A]
    [IsCommMonObj A] (X : D) [ModObj A X] :
    actAcross A A X ≫ actLeft A X =
      (A ◁ actLeft A X) ≫ actLeft A X := by
  rw [actAcross]
  simp only [Category.assoc]
  rw [actLeft_actLeft]
  simp only [Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, IsCommMonObj.mul_comm]

/-- **The key commutation**: over a commutative monoid the external
action slides across a slot leg acting on the inner factor. -/
theorem actAcross_winLegN
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A]
    [IsCommMonObj A] (X : D) [ModObj A X] :
    actAcross A (X ⊗ A) X ≫ winLegN A X =
      (A ◁ winLegN A X) ≫ actAcross A X X := by
  rw [winLegN, ← Category.assoc, actAcross_context_split]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [← whiskerLeft_comp, actAcross_actLeft, whiskerLeft_comp,
    actAcross_eq_braidPast, ← braidPast_natural_tail_assoc]

end ActAcross

/-! ## The tail action on tensor powers -/

section PowTail

/-- The raw tail action on a positive tensor power: the monoid acts
on the last factor, braided past the lower power. -/
def powTailAct [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X]
    (n : ℕ) :
    A ⊗ tensorPow D X (n + 1) ⟶ tensorPow D X (n + 1) :=
  (tensorLeftModObj A (tensorPow D X n) X).smul

/-- The tail action is the action through the right factor at the
definitional fold of the tensor power. -/
theorem powTailAct_eq
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X]
    (n : ℕ) :
    powTailAct A X n = actAcross A (tensorPow D X n) X :=
  rfl

/-- Unitality of the tail action. -/
@[reassoc]
theorem powTailAct_one
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X]
    (n : ℕ) :
    η[A] ▷ tensorPow D X (n + 1) ≫ powTailAct A X n =
      (λ_ (tensorPow D X (n + 1))).hom :=
  one_actAcross A (tensorPow D X n) X

/-- Associativity of the tail action. -/
@[reassoc]
theorem powTailAct_mul
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X]
    (n : ℕ) :
    μ[A] ▷ tensorPow D X (n + 1) ≫ powTailAct A X n =
      (α_ A A (tensorPow D X (n + 1))).hom ≫
        (A ◁ powTailAct A X n) ≫ powTailAct A X n :=
  mul_actAcross A (tensorPow D X n) X

end PowTail

/-! ## Descent of the tail action to the module power

The tail action coequalizes the whiskered relation legs: at a slot
away from the top factor the action and the leg touch disjoint
factors and pass one another by naturality, and at the top slot one
slot relation together with commutativity of the monoid closes the
square.  Every equation crossing the definitional fold
`tensorPow D X (n + 1) = tensorPow D X n ⊗ X` is applied by exact
term-level composition, never by rewriting inside a foreign frame.
-/

section GlueAux

/-- Splitting a below-top slot leg, at general objects. -/
private theorem below_aux [Category.{v} D] [MonoidalCategory D]
    {Y P Q B Z : D} (θ : P ⟶ Q)
    (c : Q ⊗ B ⟶ Z) :
    (θ ▷ (B ⊗ Y)) ≫ (α_ Q B Y).inv ≫ (c ▷ Y) =
      (α_ P B Y).inv ≫ (((θ ▷ B) ≫ c) ▷ Y) := by
  rw [associator_inv_naturality_left_assoc]
  simp only [comp_whiskerRight]

end GlueAux

section ActDescent

/-- The first assembled leg as a sum over the slots. -/
private theorem legFst_eq_sum
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    (n : ℕ) :
    modPowLegFst A X n = ∑ i : Fin (n - 1),
      biproduct.π
          (fun i : Fin (n - 1) => modPowMid A X i.val (n - 2 - i.val))
          i ≫
        (modPowLegM A X i.val (n - 2 - i.val) ≫
          powCast X (slot_decomp i)) := by
  conv_lhs => rw [← Category.id_comp (modPowLegFst A X n),
    ← biproduct.total]
  rw [Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Category.assoc, modPowLegFst, biproduct.ι_desc]

/-- The second assembled leg as a sum over the slots. -/
private theorem legSnd_eq_sum
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : D)
    [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    (n : ℕ) :
    modPowLegSnd A X n = ∑ i : Fin (n - 1),
      biproduct.π
          (fun i : Fin (n - 1) => modPowMid A X i.val (n - 2 - i.val))
          i ≫
        (modPowLegN A X i.val (n - 2 - i.val) ≫
          powCast X (slot_decomp i)) := by
  conv_lhs => rw [← Category.id_comp (modPowLegSnd A X n),
    ← biproduct.total]
  rw [Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Category.assoc, modPowLegSnd, biproduct.ι_desc]

/-- A slot-wise coequalizing condition assembles over the
left-whiskered legs. -/
private theorem legs_whiskerLeft_cond
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D]
    (P : D) {n : ℕ} {Z : D}
    (k : P ⊗ tensorPow D X n ⟶ Z)
    (h : ∀ a b (hab : a + 2 + b = n),
      (P ◁ (modPowLegM A X a b ≫ powCast X hab)) ≫ k =
        (P ◁ (modPowLegN A X a b ≫ powCast X hab)) ≫ k) :
    (P ◁ modPowLegFst A X n) ≫ k =
      (P ◁ modPowLegSnd A X n) ≫ k := by
  rw [legFst_eq_sum, legSnd_eq_sum, whiskerLeft_sum, whiskerLeft_sum,
    Preadditive.sum_comp, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := h i.val (n - 2 - i.val) (slot_decomp i)
  simp only [whiskerLeft_comp, Category.assoc] at hi ⊢
  rw [hi]

/-- **A below-top slot leg splits off the last factor**: the leg of
slot `(a, b + 1)` in arity `a + 2 + b + 1` is the leg of slot
`(a, b)` in arity `a + 2 + b`, whiskered by the untouched last
factor. -/
private theorem leg_split_below
    [Category.{v} D] [MonoidalCategory D] (A : D) (X : D)
    (a b : ℕ) (w : (X ⊗ A) ⊗ X ⟶ X ⊗ X) :
    ((tensorPow D X a ◁ w) ▷ tensorPow D X (b + 1)) ≫
        modPowGlue X a (b + 1) =
      (α_ (tensorPow D X a ⊗ ((X ⊗ A) ⊗ X)) (tensorPow D X b)
          X).inv ≫
        ((((tensorPow D X a ◁ w) ▷ tensorPow D X b) ≫
          modPowGlue X a b) ▷ X) := by
  have h0 := below_aux (Y := X)
    ((tensorPow D X a ◁ w) ≫ (α_ (tensorPow D X a) X X).inv)
    ((tensorPowConcat X (a + 2) b).hom)
  simp only [modPowGlue, tensorPowConcat_succ_hom, powExpose,
    comp_whiskerRight, Category.assoc] at h0 ⊢
  exact h0

/-- **The below-top slots pass the tail action** by naturality. -/
private theorem act_slot_below
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (a b : ℕ) :
    (A ◁ modPowLegM A X a (b + 1)) ≫ powTailAct A X (a + 2 + b) ≫
        modPowπ A X (a + 2 + b + 1) =
      (A ◁ modPowLegN A X a (b + 1)) ≫ powTailAct A X (a + 2 + b) ≫
        modPowπ A X (a + 2 + b + 1) := by
  have hkey : ∀ w : (X ⊗ A) ⊗ X ⟶ X ⊗ X,
      (A ◁ (((tensorPow D X a ◁ w) ▷ tensorPow D X (b + 1)) ≫
          modPowGlue X a (b + 1))) ≫
          powTailAct A X (a + 2 + b) ≫ modPowπ A X (a + 2 + b + 1) =
        (A ◁ (α_ (tensorPow D X a ⊗ ((X ⊗ A) ⊗ X))
            (tensorPow D X b) X).inv) ≫
          actAcross A
            ((tensorPow D X a ⊗ ((X ⊗ A) ⊗ X)) ⊗ tensorPow D X b)
            X ≫
          ((((tensorPow D X a ◁ w) ▷ tensorPow D X b) ≫
            modPowGlue X a b) ▷ X) ≫
          modPowπ A X (a + 2 + b + 1) :=
    fun w =>
      (congrArg
        (fun z : modPowMid A X a (b + 1) ⟶
            tensorPow D X (a + 2 + (b + 1)) =>
          (A ◁ z) ≫ powTailAct A X (a + 2 + b) ≫
            modPowπ A X (a + 2 + b + 1))
        (leg_split_below A X a b w)).trans
      (whiskerLeft_associator_inv_actAcross A
        (((tensorPow D X a ◁ w) ▷ tensorPow D X b) ≫
          modPowGlue X a b)
        X (modPowπ A X (a + 2 + b + 1)))
  have hid : powCast X (rfl : a + 2 + (b + 1) = a + 2 + b + 1) ≫
      modPowπ A X (a + 2 + b + 1) = modPowπ A X (a + 2 + b + 1) :=
    Category.id_comp _
  have hr : modPowLegM A X a (b + 1) ≫ modPowπ A X (a + 2 + b + 1) =
      modPowLegN A X a (b + 1) ≫ modPowπ A X (a + 2 + b + 1) :=
    (congrArg (fun z => modPowLegM A X a (b + 1) ≫ z)
        hid).symm.trans
      ((modPow_rel A X a (b + 1)
        (rfl : a + 2 + (b + 1) = a + 2 + b + 1)).trans
        (congrArg (fun z => modPowLegN A X a (b + 1) ≫ z) hid))
  have hrelW :
      ((((tensorPow D X a ◁ winLegM A X) ▷ tensorPow D X b) ≫
        modPowGlue X a b) ▷ X) ≫ modPowπ A X (a + 2 + b + 1) =
      ((((tensorPow D X a ◁ winLegN A X) ▷ tensorPow D X b) ≫
        modPowGlue X a b) ▷ X) ≫ modPowπ A X (a + 2 + b + 1) := by
    have hM := congrArg
      (fun z : modPowMid A X a (b + 1) ⟶
          tensorPow D X (a + 2 + (b + 1)) =>
        z ≫ modPowπ A X (a + 2 + b + 1))
      (leg_split_below A X a b (winLegM A X))
    have hN := congrArg
      (fun z : modPowMid A X a (b + 1) ⟶
          tensorPow D X (a + 2 + (b + 1)) =>
        z ≫ modPowπ A X (a + 2 + b + 1))
      (leg_split_below A X a b (winLegN A X))
    have h3 := hM.symm.trans (hr.trans hN)
    have h4 := (Category.assoc
        (α_ (tensorPow D X a ⊗ ((X ⊗ A) ⊗ X)) (tensorPow D X b)
          X).inv
        ((((tensorPow D X a ◁ winLegM A X) ▷ tensorPow D X b) ≫
          modPowGlue X a b) ▷ X)
        (modPowπ A X (a + 2 + b + 1))).symm.trans
      (h3.trans (Category.assoc
        (α_ (tensorPow D X a ⊗ ((X ⊗ A) ⊗ X)) (tensorPow D X b)
          X).inv
        ((((tensorPow D X a ◁ winLegN A X) ▷ tensorPow D X b) ≫
          modPowGlue X a b) ▷ X)
        (modPowπ A X (a + 2 + b + 1))))
    exact (cancel_epi
      (α_ (tensorPow D X a ⊗ ((X ⊗ A) ⊗ X)) (tensorPow D X b)
        X).inv).mp h4
  exact (hkey (winLegM A X)).trans
    ((congrArg
        (fun z => (A ◁ (α_ (tensorPow D X a ⊗ ((X ⊗ A) ⊗ X))
            (tensorPow D X b) X).inv) ≫
          actAcross A
            ((tensorPow D X a ⊗ ((X ⊗ A) ⊗ X)) ⊗ tensorPow D X b)
            X ≫ z)
        hrelW).trans (hkey (winLegN A X)).symm)

/-- The top-slot glue absorbed by the right unitor, at general
objects. -/
private theorem top_glue_aux
    [Category.{v} D] [MonoidalCategory D] (A : D) (X : D)
    (V : D) {Z : D}
    (w : (X ⊗ A) ⊗ X ⟶ X ⊗ X) (p : (V ⊗ X) ⊗ X ⟶ Z) :
    (((V ◁ w) ▷ 𝟙_ D) ≫ ((α_ V X X).inv ▷ 𝟙_ D) ≫
        (ρ_ ((V ⊗ X) ⊗ X)).hom) ≫ p =
      (ρ_ (V ⊗ ((X ⊗ A) ⊗ X))).hom ≫ (V ◁ w) ≫
        (α_ V X X).inv ≫ p := by
  simp only [Category.assoc]
  rw [← comp_whiskerRight_assoc, rightUnitor_naturality_assoc]
  simp only [Category.assoc]

/-- The whole top-slot conjugation of the tail action, at general
objects: unwrap the glue, braid past the lower power, and act
inside the window. -/
private theorem top_act_aux
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X]
    (V : D) {Z : D}
    (w : (X ⊗ A) ⊗ X ⟶ X ⊗ X) (p : (V ⊗ X) ⊗ X ⟶ Z) :
    (A ◁ (((V ◁ w) ▷ 𝟙_ D) ≫ ((α_ V X X).inv ▷ 𝟙_ D) ≫
        (ρ_ ((V ⊗ X) ⊗ X)).hom)) ≫ actAcross A (V ⊗ X) X ≫ p =
      (A ◁ (ρ_ (V ⊗ ((X ⊗ A) ⊗ X))).hom) ≫
        (braidPast A V ((X ⊗ A) ⊗ X)).hom ≫
        (V ◁ ((A ◁ w) ≫ actAcross A X X)) ≫
        (α_ V X X).inv ≫ p := by
  have h1 : ((V ◁ w) ▷ 𝟙_ D) ≫ ((α_ V X X).inv ▷ 𝟙_ D) ≫
      (ρ_ ((V ⊗ X) ⊗ X)).hom =
        (ρ_ (V ⊗ ((X ⊗ A) ⊗ X))).hom ≫ (V ◁ w) ≫
          (α_ V X X).inv := by
    rw [← comp_whiskerRight_assoc, rightUnitor_naturality]
  rw [h1]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% (actAcross_split_last A V X),
    braidPast_natural_tail_assoc, ← whiskerLeft_comp_assoc]

/-- The top-slot relation, with the empty upper context already
absorbed. -/
private theorem rel_top
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (a : ℕ) :
    (tensorPow D X a ◁ winLegM A X) ≫
        (α_ (tensorPow D X a) X X).inv ≫ modPowπ A X (a + 2) =
      (tensorPow D X a ◁ winLegN A X) ≫
        (α_ (tensorPow D X a) X X).inv ≫ modPowπ A X (a + 2) := by
  refine (cancel_epi
    (ρ_ (tensorPow D X a ⊗ ((X ⊗ A) ⊗ X))).hom).mp ?_
  have hid : powCast X (rfl : a + 2 + 0 = a + 2) ≫
      modPowπ A X (a + 2) = modPowπ A X (a + 2) :=
    Category.id_comp _
  have hr : modPowLegM A X a 0 ≫ modPowπ A X (a + 2) =
      modPowLegN A X a 0 ≫ modPowπ A X (a + 2) :=
    (congrArg (fun z => modPowLegM A X a 0 ≫ z) hid).symm.trans
      ((modPow_rel A X a 0 (rfl : a + 2 + 0 = a + 2)).trans
        (congrArg (fun z => modPowLegN A X a 0 ≫ z) hid))
  exact ((top_glue_aux A X (tensorPow D X a) (winLegM A X)
      (modPowπ A X (a + 2))).symm.trans hr).trans
    (top_glue_aux A X (tensorPow D X a) (winLegN A X)
      (modPowπ A X (a + 2)))

/-- **The top slot passes the tail action**: one slot relation, and
the commutation of the two actions across the window. -/
private theorem act_slot_top
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [IsCommMonObj A]
    (a : ℕ) :
    (A ◁ modPowLegM A X a 0) ≫ powTailAct A X (a + 1) ≫
        modPowπ A X (a + 2) =
      (A ◁ modPowLegN A X a 0) ≫ powTailAct A X (a + 1) ≫
        modPowπ A X (a + 2) := by
  have hstep : ∀ w : (X ⊗ A) ⊗ X ⟶ X ⊗ X,
      (A ◁ (((tensorPow D X a ◁ w) ▷ tensorPow D X 0) ≫
          modPowGlue X a 0)) ≫
        powTailAct A X (a + 1) ≫ modPowπ A X (a + 2) =
      (A ◁ (ρ_ (tensorPow D X a ⊗ ((X ⊗ A) ⊗ X))).hom) ≫
        (braidPast A (tensorPow D X a) ((X ⊗ A) ⊗ X)).hom ≫
        (tensorPow D X a ◁ ((A ◁ w) ≫ actAcross A X X)) ≫
        (α_ (tensorPow D X a) X X).inv ≫ modPowπ A X (a + 2) :=
    fun w => top_act_aux A X (tensorPow D X a) w (modPowπ A X (a + 2))
  have hMwin : (A ◁ winLegM A X) ≫ actAcross A X X =
      actAcross A (X ⊗ A) X ≫ winLegM A X :=
    actAcross_natural A (actRight A X) X
  have hmid :
      (A ◁ (ρ_ (tensorPow D X a ⊗ ((X ⊗ A) ⊗ X))).hom) ≫
        (braidPast A (tensorPow D X a) ((X ⊗ A) ⊗ X)).hom ≫
        (tensorPow D X a ◁ ((A ◁ winLegM A X) ≫
          actAcross A X X)) ≫
        (α_ (tensorPow D X a) X X).inv ≫ modPowπ A X (a + 2) =
      (A ◁ (ρ_ (tensorPow D X a ⊗ ((X ⊗ A) ⊗ X))).hom) ≫
        (braidPast A (tensorPow D X a) ((X ⊗ A) ⊗ X)).hom ≫
        (tensorPow D X a ◁ ((A ◁ winLegN A X) ≫
          actAcross A X X)) ≫
        (α_ (tensorPow D X a) X X).inv ≫ modPowπ A X (a + 2) := by
    rw [hMwin, whiskerLeft_comp]
    simp only [Category.assoc]
    rw [rel_top A X a, ← whiskerLeft_comp_assoc, actAcross_winLegN]
  exact (hstep (winLegM A X)).trans
    (hmid.trans (hstep (winLegN A X)).symm)

/-- The raw action on the ambient power of the module power. -/
noncomputable def modPowActRaw
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (n : ℕ) :
    A ⊗ tensorPow D X (n + 1) ⟶ modPow A X (n + 1) :=
  powTailAct A X n ≫ modPowπ A X (n + 1)

/-- **The raw action coequalizes the whiskered relation legs.** -/
theorem modPowActRaw_cond
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    (n : ℕ) :
    (A ◁ modPowLegFst A X (n + 1)) ≫ modPowActRaw A X n =
      (A ◁ modPowLegSnd A X (n + 1)) ≫ modPowActRaw A X n := by
  refine legs_whiskerLeft_cond A X A _ (fun a b hab => ?_)
  cases b with
  | zero =>
    obtain rfl : n = a + 1 := by omega
    have hM : modPowLegM A X a 0 ≫ powCast X hab =
        modPowLegM A X a 0 := Category.comp_id _
    have hN : modPowLegN A X a 0 ≫ powCast X hab =
        modPowLegN A X a 0 := Category.comp_id _
    exact (congrArg
        (fun z => (A ◁ z) ≫ modPowActRaw A X (a + 1)) hM).trans
      ((act_slot_top A X a).trans
        (congrArg
          (fun z => (A ◁ z) ≫ modPowActRaw A X (a + 1)) hN).symm)
  | succ b₀ =>
    obtain rfl : n = a + 2 + b₀ := by omega
    have hM : modPowLegM A X a (b₀ + 1) ≫ powCast X hab =
        modPowLegM A X a (b₀ + 1) := Category.comp_id _
    have hN : modPowLegN A X a (b₀ + 1) ≫ powCast X hab =
        modPowLegN A X a (b₀ + 1) := Category.comp_id _
    exact (congrArg
        (fun z => (A ◁ z) ≫ modPowActRaw A X (a + 2 + b₀)) hM).trans
      ((act_slot_below A X a b₀).trans
        (congrArg
          (fun z => (A ◁ z) ≫ modPowActRaw A X (a + 2 + b₀))
          hN).symm)

/-- **The monoid action on the module power**, descended from the
tail action through the whiskered coequalizer. -/
noncomputable def modPowAct
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) :
    A ⊗ modPow A X (n + 1) ⟶ modPow A X (n + 1) :=
  modPowWhiskerLeftDesc A X A (n + 1) (modPowActRaw A X n)
    (modPowActRaw_cond A X n)

/-- Defining equation of the descended action. -/
@[reassoc (attr := simp)]
theorem whiskerLeft_modPowπ_modPowAct
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) :
    (A ◁ modPowπ A X (n + 1)) ≫ modPowAct A X n =
      powTailAct A X n ≫ modPowπ A X (n + 1) :=
  modPowπ_whiskerLeft_desc A X A (n + 1) _ _

/-- Unitality of the descended action. -/
theorem modPowAct_one
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) :
    η[A] ▷ modPow A X (n + 1) ≫ modPowAct A X n =
      (λ_ (modPow A X (n + 1))).hom := by
  apply modPow_whiskerLeft_hom_ext A X (𝟙_ D) (n + 1)
  rw [whisker_exchange_assoc, whiskerLeft_modPowπ_modPowAct,
    powTailAct_one_assoc, leftUnitor_naturality]

/-- Associativity of the descended action. -/
theorem modPowAct_mul
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) :
    μ[A] ▷ modPow A X (n + 1) ≫ modPowAct A X n =
      (α_ A A (modPow A X (n + 1))).hom ≫
        (A ◁ modPowAct A X n) ≫ modPowAct A X n := by
  apply modPow_whiskerLeft_hom_ext A X (A ⊗ A) (n + 1)
  conv_lhs => rw [whisker_exchange_assoc,
    whiskerLeft_modPowπ_modPowAct, powTailAct_mul_assoc]
  conv_rhs => rw [associator_naturality_right_assoc,
    ← whiskerLeft_comp_assoc, whiskerLeft_modPowπ_modPowAct,
    whiskerLeft_comp_assoc, whiskerLeft_modPowπ_modPowAct]

/-- **The module power of a module is a module**, in every positive
arity. -/
@[implicit_reducible]
noncomputable def modPowModObj
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) :
    ModObj A (modPow A X (n + 1)) where
  smul := modPowAct A X n
  one_smul := modPowAct_one A X n
  mul_smul := modPowAct_mul A X n

/-- The module power of a module, bundled as a module. -/
noncomputable def modPowMod
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) : Mod D A :=
  letI := modPowModObj A X n
  ⟨modPow A X (n + 1)⟩

@[simp] theorem modPowMod_X
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) :
    (modPowMod A X n).X = modPow A X (n + 1) := rfl

end ActDescent

/-! ## Permutation equivariance of the descended action

The descended action commutes with the permutation action: for a
top-fixing generator by naturality alone, and for the top
transposition by carrying the acting monoid into the top slot and
applying the slot relation there — the same slot the descent itself
used.  Generation by the adjacent transpositions extends both to the
full symmetric group, and linearity to the group algebra.
-/

section ActGlue

/-- Intertwining a whiskered action is closed under sums. -/
private theorem whisker_act_add
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D]
    {P M : D} (act : P ⊗ M ⟶ M)
    {u v : M ⟶ M} (hu : act ≫ u = (P ◁ u) ≫ act)
    (hv : act ≫ v = (P ◁ v) ≫ act) :
    act ≫ (u + v) = (P ◁ (u + v)) ≫ act := by
  rw [Preadditive.comp_add, MonoidalPreadditive.whiskerLeft_add,
    Preadditive.add_comp, hu, hv]

/-- Intertwining a whiskered action is closed under scalars. -/
private theorem whisker_act_smul
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [Linear ℂ D] [MonoidalLinear ℂ D]
    {P M : D} (act : P ⊗ M ⟶ M)
    (r : ℂ) {u : M ⟶ M} (hu : act ≫ u = (P ◁ u) ≫ act) :
    act ≫ (r • u) = (P ◁ (r • u)) ≫ act := by
  rw [Linear.comp_smul, MonoidalLinear.whiskerLeft_smul,
    Linear.smul_comp, hu]

end ActGlue

section ActPerm

/-- The window shuffle carrying the acting monoid into the top
slot: `d ⊗ (y ⊗ z) ↦ (z ⊗ d) ⊗ y`. -/
def winShuffle
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    (X : D) : A ⊗ (X ⊗ X) ⟶ (X ⊗ A) ⊗ X :=
  (A ◁ (β_ X X).hom) ≫ (α_ A X X).inv ≫ ((β_ A X).hom ▷ X)

/-- **The braided window identity for the first leg**: acting on
the top factor and braiding is shuffling and acting through the
braided right action. -/
theorem actAcross_braiding
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] :
    actAcross A X X ≫ (β_ X X).hom =
      winShuffle A X ≫ winLegM A X := by
  have hR : winShuffle A X ≫ winLegM A X =
      (A ◁ (β_ X X).hom) ≫ (α_ A X X).inv ≫ (actLeft A X ▷ X) := by
    rw [winShuffle, winLegM, actRight, comp_whiskerRight]
    simp only [Category.assoc]
    rw [← comp_whiskerRight_assoc, SymmetricCategory.symmetry,
      id_whiskerRight, Category.id_comp]
  have hL : actAcross A X X ≫ (β_ X X).hom =
      (A ◁ (β_ X X).hom) ≫ (α_ A X X).inv ≫ (actLeft A X ▷ X) := by
    rw [actAcross]
    simp only [Category.assoc]
    rw [BraidedCategory.braiding_naturality_right,
      BraidedCategory.braiding_tensor_right_hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← comp_whiskerRight_assoc, SymmetricCategory.symmetry,
      id_whiskerRight, Category.id_comp, Iso.inv_hom_id_assoc]
  rw [hL, hR]

/-- **The braided window identity for the second leg**: the shuffle
followed by the second leg is braiding first, then acting on the
top factor. -/
theorem winShuffle_winLegN
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] :
    winShuffle A X ≫ winLegN A X =
      (A ◁ (β_ X X).hom) ≫ actAcross A X X := by
  rw [winShuffle, winLegN, actAcross]
  simp only [Category.assoc]

/-- The tail action framed through the top window, on the left of
the top braiding. -/
private theorem swap_left_aux
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X]
    (V : D) {Z : D} (p : (V ⊗ X) ⊗ X ⟶ Z) :
    actAcross A (V ⊗ X) X ≫
        ((α_ V X X).hom ≫ (V ◁ (β_ X X).hom) ≫ (α_ V X X).inv) ≫
        p =
      (A ◁ (α_ V X X).hom) ≫ (braidPast A V (X ⊗ X)).hom ≫
        (V ◁ (actAcross A X X ≫ (β_ X X).hom)) ≫
        (α_ V X X).inv ≫ p := by
  simp only [Category.assoc]
  rw [actAcross_context_split_assoc, ← whiskerLeft_comp_assoc]

/-- The tail action framed through the top window, on the right of
the top braiding. -/
private theorem swap_right_aux
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X]
    (V : D) {Z : D}
    (p : (V ⊗ X) ⊗ X ⟶ Z) :
    (A ◁ ((α_ V X X).hom ≫ (V ◁ (β_ X X).hom) ≫
        (α_ V X X).inv)) ≫ actAcross A (V ⊗ X) X ≫ p =
      (A ◁ (α_ V X X).hom) ≫ (braidPast A V (X ⊗ X)).hom ≫
        (V ◁ ((A ◁ (β_ X X).hom) ≫ actAcross A X X)) ≫
        (α_ V X X).inv ≫ p := by
  simp only [whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% (actAcross_split_last A V X),
    braidPast_natural_tail_assoc, ← whiskerLeft_comp_assoc]

/-- **The tail action commutes with the top braiding after the
projection**: the braided slide moves the acting monoid across the
swapped pair, and the top slot relation closes the square. -/
private theorem act_swapTop
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (m : ℕ) :
    powTailAct A X (m + 1) ≫ swapTop X m ≫ modPowπ A X (m + 2) =
      (A ◁ swapTop X m) ≫ powTailAct A X (m + 1) ≫
        modPowπ A X (m + 2) := by
  have hwin : (A ◁ (α_ (tensorPow D X m) X X).hom) ≫
      (braidPast A (tensorPow D X m) (X ⊗ X)).hom ≫
      (tensorPow D X m ◁ (actAcross A X X ≫ (β_ X X).hom)) ≫
      (α_ (tensorPow D X m) X X).inv ≫ modPowπ A X (m + 2) =
      (A ◁ (α_ (tensorPow D X m) X X).hom) ≫
        (braidPast A (tensorPow D X m) (X ⊗ X)).hom ≫
        (tensorPow D X m ◁ ((A ◁ (β_ X X).hom) ≫
          actAcross A X X)) ≫
        (α_ (tensorPow D X m) X X).inv ≫ modPowπ A X (m + 2) := by
    rw [actAcross_braiding A X, whiskerLeft_comp]
    simp only [Category.assoc]
    rw [rel_top A X m, ← whiskerLeft_comp_assoc,
      winShuffle_winLegN A X]
  exact (swap_left_aux A X (tensorPow D X m)
      (modPowπ A X (m + 2))).trans
    (hwin.trans (swap_right_aux A X (tensorPow D X m)
      (modPowπ A X (m + 2))).symm)

/-- A raw intertwining of the tail action with a permutation
descends to the module power. -/
private theorem modPowAct_perm_of_raw
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 1)))
    (h : powTailAct A X n ≫ permMor X (n + 1) σ ≫
        modPowπ A X (n + 1) =
      (A ◁ permMor X (n + 1) σ) ≫ powTailAct A X n ≫
        modPowπ A X (n + 1)) :
    modPowAct A X n ≫ modPowPerm (A := A) (X := X) (n + 1) σ =
      (A ◁ modPowPerm (A := A) (X := X) (n + 1) σ) ≫
        modPowAct A X n := by
  apply modPow_whiskerLeft_hom_ext A X A (n + 1)
  conv_lhs => rw [whiskerLeft_modPowπ_modPowAct_assoc,
    modPowπ_perm]
  conv_rhs => rw [← whiskerLeft_comp_assoc, modPowπ_perm,
    whiskerLeft_comp_assoc, whiskerLeft_modPowπ_modPowAct]
  exact h

/-- The raw intertwining for a top-fixing permutation, by
naturality in the context. -/
private theorem act_perm_ext
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    powTailAct A X n ≫ permMor X (n + 1) (extPerm τ) ≫
        modPowπ A X (n + 1) =
      (A ◁ permMor X (n + 1) (extPerm τ)) ≫ powTailAct A X n ≫
        modPowπ A X (n + 1) := by
  have hp := permMor_extPerm X n τ
  exact (congrArg
      (fun z : tensorPow D X (n + 1) ⟶ tensorPow D X (n + 1) =>
        powTailAct A X n ≫ z ≫ modPowπ A X (n + 1)) hp).trans
    (((actAcross_natural_assoc A (permMor X n τ) X
        (modPowπ A X (n + 1))).symm).trans
      (congrArg
        (fun z : tensorPow D X (n + 1) ⟶ tensorPow D X (n + 1) =>
          (A ◁ z) ≫ powTailAct A X n ≫ modPowπ A X (n + 1))
        hp).symm)

/-- **The descended action commutes with every permutation.** -/
theorem modPowAct_perm
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    modPowAct A X n ≫ modPowPerm (A := A) (X := X) (n + 1) σ =
      (A ◁ modPowPerm (A := A) (X := X) (n + 1) σ) ≫
        modPowAct A X n := by
  cases n with
  | zero =>
    have hσ : σ = 1 := Equiv.ext fun i => by
      have h1 := (σ i).isLt
      have h2 := i.isLt
      rw [Equiv.Perm.one_apply]
      exact Fin.ext (by omega)
    rw [hσ, modPowPerm_one, Category.comp_id, whiskerLeft_id,
      Category.id_comp]
  | succ m =>
    have hgen : ∀ i : Fin (m + 1),
        modPowAct A X (m + 1) ≫ modPowPerm (A := A) (X := X) (m + 2)
            (Equiv.swap i.castSucc i.succ) =
          (A ◁ modPowPerm (A := A) (X := X) (m + 2)
            (Equiv.swap i.castSucc i.succ)) ≫
            modPowAct A X (m + 1) := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have ht : Equiv.swap (Fin.last m).castSucc
            (Fin.last m).succ =
              (topSwap : Equiv.Perm (Fin (m + 2))) := by
          rw [Fin.succ_last]
          rfl
        rw [ht]
        refine modPowAct_perm_of_raw A X (m + 1) topSwap ?_
        have hp : permMor X (m + 2)
            (topSwap : Equiv.Perm (Fin (m + 2))) = swapTop X m :=
          permMor_topSwap_eq X m
        rw [hp]
        exact act_swapTop A X m
      · have he : Equiv.swap (Fin.castSucc j).castSucc
            (Fin.castSucc j).succ =
              extPerm (Equiv.swap j.castSucc j.succ) :=
          swap_castSucc_succ_castSucc j
        rw [he]
        exact modPowAct_perm_of_raw A X (m + 1) _
          (act_perm_ext A X (m + 1) (Equiv.swap j.castSucc j.succ))
    have key : ∀ τ : Equiv.Perm (Fin (m + 2)),
        τ ∈ Submonoid.closure (Set.range fun i : Fin (m + 1) =>
          Equiv.swap i.castSucc i.succ) →
        modPowAct A X (m + 1) ≫
            modPowPerm (A := A) (X := X) (m + 2) τ =
          (A ◁ modPowPerm (A := A) (X := X) (m + 2) τ) ≫
            modPowAct A X (m + 1) := by
      intro τ hτ
      induction hτ using Submonoid.closure_induction_left with
      | one =>
        rw [modPowPerm_one, Category.comp_id, whiskerLeft_id,
          Category.id_comp]
      | mul_left g hg τ' hτ' ih =>
        obtain ⟨i, rfl⟩ := hg
        rw [modPowPerm_mul, whiskerLeft_comp, ← Category.assoc, ih,
          Category.assoc, hgen i, ← Category.assoc]
    exact key σ (by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial)

/-- **The descended action commutes with the group-algebra
action**, by linear extension of the permutation case. -/
theorem modPowAct_alg
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    (n : ℕ) (z : SymGroupAlgebra (n + 1)) :
    modPowAct A X n ≫
        (modPowAlg A X (n + 1) z : End (modPow A X (n + 1))) =
      (A ◁ (modPowAlg A X (n + 1) z :
          End (modPow A X (n + 1)))) ≫
        modPowAct A X n := by
  induction z using MonoidAlgebra.induction_on with
  | of σ =>
    rw [show (MonoidAlgebra.of ℂ (Equiv.Perm (Fin (n + 1)))) σ =
        MonoidAlgebra.single σ (1 : ℂ) from rfl, modPowAlg_single]
    exact modPowAct_perm A X n σ
  | add z₁ z₂ h₁ h₂ =>
    rw [map_add]
    exact whisker_act_add (modPowAct A X n) h₁ h₂
  | smul r z' h =>
    rw [map_smul]
    exact whisker_act_smul (modPowAct A X n) r h

end ActPerm

/-! ## The symmetric power as a module -/

section SymAct

/-- **The monoid action on the symmetric power**, through the
section and the descended action. -/
noncomputable def symPowAct
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [Linear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) :
    A ⊗ symPow A X (n + 1) ⟶ symPow A X (n + 1) :=
  (A ◁ symPowσ A X (n + 1)) ≫ modPowAct A X n ≫
    symPowπ A X (n + 1)

/-- Defining equation of the symmetric-power action. -/
@[reassoc (attr := simp)]
theorem whiskerLeft_symPowπ_symPowAct
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) :
    (A ◁ symPowπ A X (n + 1)) ≫ symPowAct A X n =
      modPowAct A X n ≫ symPowπ A X (n + 1) := by
  have h' : modPowAct A X n ≫ symPowIdem A X (n + 1) =
      (A ◁ symPowIdem A X (n + 1)) ≫ modPowAct A X n :=
    modPowAct_alg A X n (symmetriser (n + 1))
  rw [symPowAct, ← whiskerLeft_comp_assoc, symPowπ_symPowσ,
    reassoc_of% h'.symm, symPowIdem_π]

/-- Unitality of the symmetric-power action. -/
theorem symPowAct_one
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) :
    η[A] ▷ symPow A X (n + 1) ≫ symPowAct A X n =
      (λ_ (symPow A X (n + 1))).hom := by
  apply symPow_whiskerLeft_hom_ext A X (𝟙_ D) (n + 1)
  rw [whisker_exchange_assoc, whiskerLeft_symPowπ_symPowAct,
    reassoc_of% (modPowAct_one A X n), leftUnitor_naturality]

/-- Associativity of the symmetric-power action. -/
theorem symPowAct_mul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) :
    μ[A] ▷ symPow A X (n + 1) ≫ symPowAct A X n =
      (α_ A A (symPow A X (n + 1))).hom ≫
        (A ◁ symPowAct A X n) ≫ symPowAct A X n := by
  apply symPow_whiskerLeft_hom_ext A X (A ⊗ A) (n + 1)
  conv_lhs => rw [whisker_exchange_assoc,
    whiskerLeft_symPowπ_symPowAct,
    reassoc_of% (modPowAct_mul A X n)]
  conv_rhs => rw [associator_naturality_right_assoc,
    ← whiskerLeft_comp_assoc, whiskerLeft_symPowπ_symPowAct,
    whiskerLeft_comp_assoc, whiskerLeft_symPowπ_symPowAct]

/-- **The symmetric power of a module is a module**, in every
positive arity. -/
@[implicit_reducible]
noncomputable def symPowModObj
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) :
    ModObj A (symPow A X (n + 1)) where
  smul := symPowAct A X n
  one_smul := symPowAct_one A X n
  mul_smul := symPowAct_mul A X n

/-- **The section of the symmetric power is a module map.** -/
theorem symPowσ_modPowAct
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) :
    (A ◁ symPowσ A X (n + 1)) ≫ modPowAct A X n =
      symPowAct A X n ≫ symPowσ A X (n + 1) := by
  have h' : modPowAct A X n ≫ symPowIdem A X (n + 1) =
      (A ◁ symPowIdem A X (n + 1)) ≫ modPowAct A X n :=
    modPowAct_alg A X n (symmetriser (n + 1))
  have hσI : symPowσ A X (n + 1) ≫ symPowIdem A X (n + 1) =
      symPowσ A X (n + 1) := by
    rw [← symPowπ_symPowσ, symPowσ_symPowπ_assoc]
  rw [symPowAct]
  simp only [Category.assoc]
  rw [symPowπ_symPowσ, h', ← whiskerLeft_comp_assoc, hσI]

/-- The symmetric power of a module, bundled as a module. -/
noncomputable def symPowMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) : Mod D A :=
  letI := symPowModObj A X n
  ⟨symPow A X (n + 1)⟩

@[simp] theorem symPowMod_X
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) :
    (symPowMod A X n).X = symPow A X (n + 1) := rfl

end SymAct

end RS
