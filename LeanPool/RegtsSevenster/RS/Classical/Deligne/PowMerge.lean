/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowChain

/-!
# The merge isomorphism for module powers

The relative tensor product of two module powers is the module
power of the summed arity: the descended power multiplication
`powMulDesc` of `PowChain.lean` is an isomorphism
`modTensor A (modPowMod A X a) (modPowMod A X b) ≅
  modPow A X (a + 1 + b + 1)`,
with inverse `powSplit` descended from the inverse of the
concatenation of ambient tensor powers.

* `headMod`: the head insertion `X ⊗ X^⊗b ⟶ modPow A X (b + 1)`;
  through `modPowMul` with the singleton power it is a module map
  for the action on the head factor (`headMod_act`) — the slide of
  the monoid from the head to the tail of a module power, packaged
  through the multiplication rather than proved slot by slot.
* `powSplit`: the inverse direction, descended through the wide
  coequalizer.  Each slot relation of the big power either lands
  inside one half, where the corresponding half projection absorbs
  it (`powSplit_cond_left`/`powSplit_cond_right`), or at the
  boundary between the halves, where it becomes the coequalizer
  relation of the module tensor product itself
  (`powSplit_cond_bound`).
* `powMergeIso`: the packaged isomorphism, with `powMulDesc` as the
  forward direction and `powSplit` as the inverse.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## Structural shuffles of the boundary window

Both boundary computations move a window map across the split of
the ambient power into two halves.  The shuffles are stated at
general objects, so that no tensor-power arity enters the
rewriting.
-/

section Shuffle

/-- The left-window shuffle: a window map acting on the first two
window factors passes to the left half of the split. -/
theorem split_shuffle_fst [Category.{v} D] [MonoidalCategory D]
    {P Q R S B : D} (u : Q ⟶ R) :
    ((P ◁ (u ▷ S)) ▷ B) ≫ ((α_ P R S).inv ▷ B) ≫
        (α_ (P ⊗ R) S B).hom =
      (α_ P (Q ⊗ S) B).hom ≫ (P ◁ (α_ Q S B).hom) ≫
        (α_ P Q (S ⊗ B)).inv ≫ ((P ◁ u) ▷ (S ⊗ B)) := by
  have hpent : (α_ P (R ⊗ S) B).hom ≫ (P ◁ (α_ R S B).hom) ≫
      (α_ P R (S ⊗ B)).inv =
        ((α_ P R S).inv ▷ B) ≫ (α_ (P ⊗ R) S B).hom := by
    monoidal
  conv_rhs => rw [← associator_inv_naturality_middle,
    ← whiskerLeft_comp_assoc, ← associator_naturality_left,
    whiskerLeft_comp_assoc, ← associator_naturality_middle_assoc]
  rw [hpent]

/-- A whisker absorbed into the left factor of a tensor of
morphisms. -/
theorem whiskerRight_tensorHom [Category.{v} D] [MonoidalCategory D]
    {P₁ P₂ Q₂ R S : D}
    (f : P₁ ⟶ P₂) (g : P₂ ⟶ S) (h : R ⟶ Q₂) :
    (f ▷ R) ≫ (g ⊗ₘ h) = (f ≫ g) ⊗ₘ h := by
  rw [← tensorHom_id f R, MonoidalCategory.tensorHom_comp_tensorHom,
    Category.id_comp]

/-- Two whiskers absorbed into the left factor of a tensor of
morphisms. -/
theorem whiskerRight_tensorHom_whiskerRight
    [Category.{v} D] [MonoidalCategory D]
    {P₁ P₂ S T R Q₂ : D}
    (f : P₁ ⟶ P₂) (g : P₂ ⟶ S) (k : S ⟶ T) (h : R ⟶ Q₂) :
    (f ▷ R) ≫ (g ⊗ₘ h) ≫ (k ▷ Q₂) = (f ≫ g ≫ k) ⊗ₘ h := by
  rw [← tensorHom_id f R, ← tensorHom_id k Q₂,
    MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.id_comp, Category.comp_id]

/-- A left whisker absorbed into the right factor of a tensor of
morphisms. -/
theorem whiskerLeft_comp_tensorHom [Category.{v} D] [MonoidalCategory D]
    {P Q₁ R₁ R₂ S : D}
    (f : R₁ ⟶ R₂) (g : P ⟶ Q₁) (h : R₂ ⟶ S) :
    (P ◁ f) ≫ (g ⊗ₘ h) = g ⊗ₘ (f ≫ h) := by
  rw [← id_tensorHom P f, MonoidalCategory.tensorHom_comp_tensorHom,
    Category.id_comp]

/-- The right-window shuffle: a window map acting on the last two
window factors passes to the head of the right half of the
split. -/
theorem split_shuffle_snd [Category.{v} D] [MonoidalCategory D]
    {P Y G S B : D} (v : G ⊗ S ⟶ S) :
    ((P ◁ ((α_ Y G S).hom ≫ (Y ◁ v))) ▷ B) ≫
        ((α_ P Y S).inv ▷ B) ≫ (α_ (P ⊗ Y) S B).hom =
      (α_ P ((Y ⊗ G) ⊗ S) B).hom ≫
        (P ◁ (α_ (Y ⊗ G) S B).hom) ≫
        (α_ P (Y ⊗ G) (S ⊗ B)).inv ≫
        ((α_ P Y G).inv ▷ (S ⊗ B)) ≫
        (α_ (P ⊗ Y) G (S ⊗ B)).hom ≫
        ((P ⊗ Y) ◁ ((α_ G S B).inv ≫ (v ▷ B))) := by
  have hstruct : (α_ P ((Y ⊗ G) ⊗ S) B).hom ≫
      (P ◁ (α_ (Y ⊗ G) S B).hom) ≫
      (α_ P (Y ⊗ G) (S ⊗ B)).inv ≫
      ((α_ P Y G).inv ▷ (S ⊗ B)) ≫
      (α_ (P ⊗ Y) G (S ⊗ B)).hom ≫
      ((P ⊗ Y) ◁ (α_ G S B).inv) =
        ((P ◁ (α_ Y G S).hom) ▷ B) ≫
          ((α_ P Y (G ⊗ S)).inv ▷ B) ≫
          (α_ (P ⊗ Y) (G ⊗ S) B).hom := by
    monoidal
  have hnat : (P ◁ (Y ◁ v)) ≫ (α_ P Y S).inv =
      (α_ P Y (G ⊗ S)).inv ≫ ((P ⊗ Y) ◁ v) :=
    associator_inv_naturality_right P Y v
  conv_lhs => rw [MonoidalCategory.whiskerLeft_comp,
    comp_whiskerRight, Category.assoc,
    ← comp_whiskerRight_assoc (P ◁ (Y ◁ v)) (α_ P Y S).inv,
    hnat, comp_whiskerRight_assoc,
    associator_naturality_middle]
  rw [← reassoc_of% hstruct, ← MonoidalCategory.whiskerLeft_comp]

end Shuffle

/-! ## The head insertion

The split of the big power exposes the right half with its head
factor peeled: the map into the module power of the right half is
the peeling inverse followed by the projection.  Through the
multiplication with the singleton power this insertion is a module
map for the action on the head factor — the slide of the monoid
from the head to the tail of a module power, obtained from
`modPowMul_actLeft` rather than slot by slot.
-/

section HeadJoin

/-- The left unitor inverse, retyped so that its target is stated
through the singleton tensor power — this keeps every statement
about it type-correct at low transparency. -/
noncomputable def toPowOne
    [Category.{v} D] [MonoidalCategory D] (X : D) : X ⟶ tensorPow D X 1 :=
  (λ_ X).inv

/-- The peeling inverse is the concatenation with a singleton
block, up to the unitor and an arity transport. -/
@[reassoc]
theorem powPeel_inv_concat [Category.{v} D] [MonoidalCategory D] (X : D)
    (b : ℕ) :
    (toPowOne X ▷ tensorPow D X b) ≫ (tensorPowConcat X 1 b).hom ≫
        powCast X (by omega : 1 + b = b + 1) =
      (powPeel X b).inv := by
  rw [← cancel_epi (powPeel X b).hom, Iso.hom_inv_id]
  have hcombine : (tensorPow D X 0 ◁ (powPeel X b).hom) ≫
      powAttach X 0 b ≫ (tensorPowConcat X (0 + 1) b).hom ≫
      powCast X (by omega : 0 + 1 + b = 0 + (b + 1)) =
        (λ_ (tensorPow D X (b + 1))).hom ≫
          powCast X (by omega : b + 1 = 0 + (b + 1)) := by
    rw [← tensorPowConcat_peel, tensorPowConcat_zero_left]
  have hcoh : (λ_ X).inv ▷ tensorPow D X b =
      (λ_ (X ⊗ tensorPow D X b)).inv ≫
        (α_ (𝟙_ D) X (tensorPow D X b)).inv := by
    monoidal
  have hsplit : powCast X (by omega : 0 + 1 + b = b + 1) =
      powCast X (by omega : 0 + 1 + b = 0 + (b + 1)) ≫
        powCast X (by omega : 0 + (b + 1) = b + 1) := by
    rw [powCast_comp]
  have hcombine' : (𝟙_ D ◁ (powPeel X b).hom) ≫
      (α_ (𝟙_ D) X (tensorPow D X b)).inv ≫
      (tensorPowConcat X (0 + 1) b).hom ≫
      powCast X (by omega : 0 + 1 + b = 0 + (b + 1)) =
        (λ_ (tensorPow D X (b + 1))).hom ≫
          powCast X (by omega : b + 1 = 0 + (b + 1)) := hcombine
  have hgoal : (powPeel X b).hom ≫
      ((λ_ X).inv ▷ tensorPow D X b) ≫
      (tensorPowConcat X (0 + 1) b).hom ≫
      powCast X (by omega : 0 + 1 + b = b + 1) =
        𝟙 (tensorPow D X (b + 1)) := by
    rw [hcoh, hsplit]
    simp only [Category.assoc]
    have hc := congrArg (fun t => t ≫ powCast X
      (by omega : 0 + (b + 1) = b + 1)) hcombine'
    repeat' erw [Category.assoc] at hc
    erw [leftUnitor_inv_naturality_assoc, hc]
    simp only [powCast_comp]
    have hid : powCast X
        (by omega : b + 1 = b + 1) = 𝟙 _ := powCast_rfl X (b + 1)
    rw [hid, Category.comp_id, Iso.inv_hom_id]
  exact hgoal

/-- The head insertion of a factor into a module power: peel the
head off the target power and project. -/
noncomputable def headMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] (A : D)
    [MonObj A] (X : D) [ModObj A X]
    (b : ℕ) :
    X ⊗ tensorPow D X b ⟶ modPow A X (b + 1) :=
  (powPeel X b).inv ≫ modPowπ A X (b + 1)

/-- The head insertion is the multiplication with the singleton
power, up to the singleton isomorphism and an arity transport. -/
theorem headMod_eq_mul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (X : D) [ModObj A X]
    (b : ℕ) :
    headMod A X b =
      ((modPowOne A X).inv ⊗ₘ modPowπ A X b) ≫
        modPowMul A X 1 b ≫
        modPowCast A X (by omega : 1 + b = b + 1) := by
  have h1 : (modPowOne A X).inv = toPowOne X ≫ modPowπ A X 1 := rfl
  have hB : ((modPowOne A X).inv ⊗ₘ modPowπ A X b) =
      (toPowOne X ▷ tensorPow D X b) ≫
        (modPowπ A X 1 ⊗ₘ modPowπ A X b) := by
    rw [h1]
    conv_lhs => rw [← Category.id_comp (modPowπ A X b),
      ← MonoidalCategory.tensorHom_comp_tensorHom]
    rw [tensorHom_id]
  rw [hB]
  simp only [Category.assoc]
  rw [modPowπ_tensor_modPowMul_assoc, modPowπ_cast,
    powPeel_inv_concat_assoc]
  rfl

/-- **The head insertion is a module map**: the monoid acting on
the head factor descends to the module-power action.  At positive
arity this is `modPowMul_actLeft` with a singleton left block — the
slide of the monoid across the whole power, packaged through the
multiplication. -/
theorem headMod_act [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (b : ℕ) :
    (A ◁ headMod A X b) ≫ modPowAct A X b =
      (α_ A X (tensorPow D X b)).inv ≫
        (actLeft A X ▷ tensorPow D X b) ≫ headMod A X b := by
  cases b with
  | zero =>
    have h0 : headMod A X 0 =
        (show X ⊗ tensorPow D X 0 ⟶ X from (ρ_ X).hom) ≫
          (modPowOne A X).inv := by
      show ((ρ_ X).hom ≫ (λ_ X).inv) ≫ modPowπ A X 1 = _
      erw [Category.assoc]
      rfl
    have hu : (actLeft A X ▷ tensorPow D X 0) ≫
        (show X ⊗ tensorPow D X 0 ⟶ X from (ρ_ X).hom) =
          (show (A ⊗ X) ⊗ tensorPow D X 0 ⟶ A ⊗ X from
            (ρ_ (A ⊗ X)).hom) ≫ actLeft A X :=
      rightUnitor_naturality (actLeft A X)
    have hcoh : (α_ A X (tensorPow D X 0)).inv ≫
        (show (A ⊗ X) ⊗ tensorPow D X 0 ⟶ A ⊗ X from
          (ρ_ (A ⊗ X)).hom) =
          A ◁ (show X ⊗ tensorPow D X 0 ⟶ X from (ρ_ X).hom) := by
      have hcoh0 : (α_ A X (𝟙_ D)).inv ≫ (ρ_ (A ⊗ X)).hom =
          A ◁ (ρ_ X).hom := by monoidal
      exact hcoh0
    have hu' := congrArg (fun t => t ≫ (modPowOne A X).inv) hu
    repeat' erw [Category.assoc] at hu'
    have hcoh' := congrArg (fun t => t ≫ actLeft A X ≫ (modPowOne A X).inv) hcoh
    repeat' erw [Category.assoc] at hcoh'
    erw [h0, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      ← actLeft_modPowOne_inv, hu', hcoh']
  | succ b₀ =>
    have hcast : (A ◁ modPowCast A X
          (by omega : 1 + (b₀ + 1) = b₀ + 1 + 1)) ≫
        modPowAct A X (b₀ + 1) =
          modPowAct A X (1 + b₀) ≫ modPowCast A X
            (by omega : 1 + (b₀ + 1) = b₀ + 1 + 1) :=
      modPowAct_cast A X _
    have hml : (α_ A (modPow A X 1) (modPow A X (b₀ + 1))).inv ≫
        (modPowAct A X 0 ▷ modPow A X (b₀ + 1)) ≫
        modPowMul A X 1 (b₀ + 1) =
          (A ◁ modPowMul A X 1 (b₀ + 1)) ≫
            modPowAct A X (1 + b₀) :=
      modPowMul_actLeft A X 0 b₀
    have hassoc : (A ◁ ((modPowOne A X).inv ⊗ₘ
          modPowπ A X (b₀ + 1))) ≫
        (α_ A (modPow A X 1) (modPow A X (b₀ + 1))).inv =
          (α_ A X (tensorPow D X (b₀ + 1))).inv ≫
            ((A ◁ (modPowOne A X).inv) ⊗ₘ
              modPowπ A X (b₀ + 1)) := by
      rw [← id_tensorHom, associator_inv_naturality, id_tensorHom]
    have hact : ((A ◁ (modPowOne A X).inv) ⊗ₘ
          modPowπ A X (b₀ + 1)) ≫
        (modPowAct A X 0 ▷ modPow A X (b₀ + 1)) =
          (actLeft A X ▷ tensorPow D X (b₀ + 1)) ≫
            ((modPowOne A X).inv ⊗ₘ modPowπ A X (b₀ + 1)) := by
      rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom,
        tensorHom_comp_tensorHom, Category.comp_id,
        Category.id_comp, actLeft_modPowOne_inv]
    rw [headMod_eq_mul A X (b₀ + 1),
      MonoidalCategory.whiskerLeft_comp,
      MonoidalCategory.whiskerLeft_comp]
    simp only [Category.assoc]
    rw [hcast, ← reassoc_of% hml, reassoc_of% hassoc,
      reassoc_of% hact]

end HeadJoin

/-! ## The tail of the left half

The braided right action of the monoid on the left half of the
split is, after the projection, the boundary window's action on
the last factor of the left half.
-/

section TailJoin

/-- In a symmetric category, carrying past a context inverts to
carrying back past it. -/
theorem braidPast_hom_swap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (U V T : D) :
    (braidPast U V T).hom ≫ (braidPast V U T).hom = 𝟙 _ := by
  simp only [braidPast_hom]
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
    ← comp_whiskerRight_assoc, SymmetricCategory.symmetry,
    MonoidalCategory.id_whiskerRight, Category.id_comp,
    Iso.inv_hom_id]

/-- **Braiding the monoid over a context pair**: the braided right
action through the last factor of a pair is the braiding of the
factor alone, then the action — the monoid never crosses the
context. -/
theorem braiding_actAcross
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X]
    (P : D) :
    (β_ (P ⊗ X) A).hom ≫ actAcross A P X =
      (α_ P X A).hom ≫ (P ◁ actRight A X) := by
  have h2 : (braidPast P A X).inv = (braidPast A P X).hom := by
    rw [← cancel_epi (braidPast P A X).hom, Iso.hom_inv_id]
    exact (braidPast_hom_swap P A X).symm
  have h1 := associator_inv_braiding_braidPast_inv P X A
  rw [h2] at h1
  have h3 : (β_ (P ⊗ X) A).hom ≫ (braidPast A P X).hom =
      (α_ P X A).hom ≫ (P ◁ (β_ X A).hom) := by
    rw [← h1, Iso.hom_inv_id_assoc]
  rw [actAcross_eq_braidPast, ← Category.assoc, h3,
    Category.assoc, ← MonoidalCategory.whiskerLeft_comp]
  rfl

/-- The braided right action of the module power, typed at the
plain power — this keeps every statement about it type-correct at
low transparency. -/
noncomputable def powActRight
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (a : ℕ) :
    modPow A X (a + 1) ⊗ A ⟶ modPow A X (a + 1) :=
  actRight A (modPowMod A X a).X

/-- The boundary reassociation, retyped so that its target is
stated through the grown tensor power. -/
noncomputable def boundAssoc
    [Category.{v} D] [MonoidalCategory D] (A : D) (X : D)
    (a : ℕ) :
    tensorPow D X a ⊗ (X ⊗ A) ⟶ tensorPow D X (a + 1) ⊗ A :=
  (α_ (tensorPow D X a) X A).inv

/-- **The braided right action of the left half after the
projection**: on the ambient power it is the boundary window's
right action on the last factor. -/
theorem modPowπ_actRight
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (a : ℕ) :
    (modPowπ A X (a + 1) ▷ A) ≫ powActRight A X a =
      (α_ (tensorPow D X a) X A).hom ≫
        (tensorPow D X a ◁ actRight A X) ≫ modPowπ A X (a + 1) := by
  have hβ : (modPowπ A X (a + 1) ▷ A) ≫
      (β_ (modPow A X (a + 1)) A).hom =
        (β_ (tensorPow D X (a + 1)) A).hom ≫
          (A ◁ modPowπ A X (a + 1)) :=
    BraidedCategory.braiding_naturality_left (modPowπ A X (a + 1)) A
  have hact : (A ◁ modPowπ A X (a + 1)) ≫
      actLeft A (modPowMod A X a).X =
        powTailAct A X a ≫ modPowπ A X (a + 1) :=
    whiskerLeft_modPowπ_modPowAct A X a
  have hkey : (β_ (tensorPow D X (a + 1)) A).hom ≫
      powTailAct A X a =
        (α_ (tensorPow D X a) X A).hom ≫
          (tensorPow D X a ◁ actRight A X) :=
    braiding_actAcross A X (tensorPow D X a)
  show (modPowπ A X (a + 1) ▷ A) ≫
      ((β_ (modPow A X (a + 1)) A).hom ≫
        actLeft A (modPowMod A X a).X) = _
  erw [← Category.assoc, hβ, Category.assoc, hact]
  exact ((reassoc_of% hkey) (modPowπ A X (a + 1))).trans
    (Category.assoc _ _ _)

end TailJoin

/-! ## The boundary bridge of the concatenation -/

section ConcatBound

/-- Detach the top factor of the first block onto the second.  The
associator, retyped so that its source is stated through the tensor
power — the inverse bridge to `powAttach`. -/
noncomputable def powDetach [Category.{v} D] [MonoidalCategory D] (X : D)
    (p q : ℕ) :
    tensorPow D X (p + 1) ⊗ tensorPow D X q ⟶
      tensorPow D X p ⊗ (X ⊗ tensorPow D X q) :=
  (α_ (tensorPow D X p) X (tensorPow D X q)).hom

/-- **The boundary split of the concatenation**: undoing the split
concatenation after the glued one detaches the exposed window
factor onto the right half and peels it back in. -/
theorem concat_split_bound [Category.{v} D] [MonoidalCategory D] (X : D)
    (a b : ℕ) :
    (tensorPowConcat X (a + 1 + 1) b).hom ≫
        powCast X (by omega : a + 1 + 1 + b = a + 1 + (b + 1)) ≫
        (tensorPowConcat X (a + 1) (b + 1)).inv =
      powDetach X (a + 1) b ≫
        (tensorPow D X (a + 1) ◁ (powPeel X b).inv) := by
  rw [← cancel_mono (tensorPowConcat X (a + 1) (b + 1)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [tensorPowConcat_peel X (a + 1) b]
  rw [← whiskerLeft_comp_assoc, Iso.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]
  have hda : powDetach X (a + 1) b ≫ powAttach X (a + 1) b =
      𝟙 (tensorPow D X (a + 1 + 1) ⊗ tensorPow D X b) :=
    (α_ (tensorPow D X (a + 1)) X (tensorPow D X b)).hom_inv_id
  rw [reassoc_of% hda]

end ConcatBound

/-! ## The boundary slot

The slot relation straddling the two halves of the split becomes,
after both projections, the coequalizer relation of the module
tensor product: the boundary bridge carries the relation object
onto `(modPow ⊗ A) ⊗ modPow`, the braided right action of the left
half absorbs the `M`-leg, and the head insertion of the right half
absorbs the `N`-leg.
-/

section Boundary

/-- The boundary bridge: reassociate the window across the split
and project both halves, keeping the monoid between them. -/
noncomputable def boundBridge
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] (A : D)
    [MonObj A] (X : D) [ModObj A X]
    (a b : ℕ) :
    modPowMid A X a b ⟶
      (modPow A X (a + 1) ⊗ A) ⊗ modPow A X (b + 1) :=
  (α_ (tensorPow D X a) ((X ⊗ A) ⊗ X) (tensorPow D X b)).hom ≫
    (tensorPow D X a ◁ (α_ (X ⊗ A) X (tensorPow D X b)).hom) ≫
    (α_ (tensorPow D X a) (X ⊗ A) (X ⊗ tensorPow D X b)).inv ≫
    (boundAssoc A X a ▷ (X ⊗ tensorPow D X b)) ≫
    ((modPowπ A X (a + 1) ▷ A) ⊗ₘ headMod A X b)

/-- The `M`-leg of the boundary slot factors through the boundary
bridge and the first module-tensor leg. -/
theorem boundBridge_legM
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (a b : ℕ) :
    modPowLegM A X a b ≫
        powCast X (by omega : a + 2 + b = a + 1 + (b + 1)) ≫
        (tensorPowConcat X (a + 1) (b + 1)).inv ≫
        (modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫
        modTensorπ A (modPowMod A X a) (modPowMod A X b) =
      boundBridge A X a b ≫
        modTensorLegM A (modPowMod A X a) (modPowMod A X b) ≫
        modTensorπ A (modPowMod A X a) (modPowMod A X b) := by
  have hsplit : (tensorPowConcat X (a + 2) b).hom ≫
      powCast X (by omega : a + 2 + b = a + 1 + (b + 1)) ≫
      (tensorPowConcat X (a + 1) (b + 1)).inv =
        powDetach X (a + 1) b ≫
          (tensorPow D X (a + 1) ◁ (powPeel X b).inv) :=
    concat_split_bound X a b
  have hM : ((tensorPow D X a ◁ (actRight A X ▷ X)) ▷
        tensorPow D X b) ≫
      ((α_ (tensorPow D X a) X X).inv ▷ tensorPow D X b) ≫
      powDetach X (a + 1) b =
        (α_ (tensorPow D X a) ((X ⊗ A) ⊗ X)
            (tensorPow D X b)).hom ≫
          (tensorPow D X a ◁
            (α_ (X ⊗ A) X (tensorPow D X b)).hom) ≫
          (α_ (tensorPow D X a) (X ⊗ A)
            (X ⊗ tensorPow D X b)).inv ≫
          ((tensorPow D X a ◁ actRight A X) ▷
            (X ⊗ tensorPow D X b)) :=
    split_shuffle_fst (actRight A X)
  have sub1 : (tensorPow D X (a + 1) ◁ (powPeel X b).inv) ≫
      (modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) =
        (modPowπ A X (a + 1) ⊗ₘ headMod A X b) :=
    whiskerLeft_comp_tensorHom (powPeel X b).inv
      (modPowπ A X (a + 1)) (modPowπ A X (b + 1))
  have hcancel : boundAssoc A X a ≫
      (α_ (tensorPow D X a) X A).hom ≫
      ((tensorPow D X a ◁ actRight A X) ≫ modPowπ A X (a + 1)) =
        (tensorPow D X a ◁ actRight A X) ≫ modPowπ A X (a + 1) :=
    Iso.inv_hom_id_assoc (α_ (tensorPow D X a) X A)
      ((tensorPow D X a ◁ actRight A X) ≫ modPowπ A X (a + 1))
  have hπR : (tensorPow D X a ◁ actRight A X) ≫
      modPowπ A X (a + 1) =
        boundAssoc A X a ≫ (modPowπ A X (a + 1) ▷ A) ≫
          powActRight A X a :=
    hcancel.symm.trans (congrArg (fun z => boundAssoc A X a ≫ z)
      (modPowπ_actRight A X a).symm)
  have sub2 : ((tensorPow D X a ◁ actRight A X) ▷
        (X ⊗ tensorPow D X b)) ≫
      (modPowπ A X (a + 1) ⊗ₘ headMod A X b) =
        (boundAssoc A X a ▷ (X ⊗ tensorPow D X b)) ≫
          ((modPowπ A X (a + 1) ▷ A) ⊗ₘ headMod A X b) ≫
          (powActRight A X a ▷ modPow A X (b + 1)) :=
    (whiskerRight_tensorHom (tensorPow D X a ◁ actRight A X)
        (modPowπ A X (a + 1)) (headMod A X b)).trans
      ((congrArg (· ⊗ₘ headMod A X b) hπR).trans
        (whiskerRight_tensorHom_whiskerRight (boundAssoc A X a)
          (modPowπ A X (a + 1) ▷ A) (powActRight A X a)
          (headMod A X b)).symm)
  have hLegM : (powActRight A X a ▷ modPow A X (b + 1)) =
      modTensorLegM A (modPowMod A X a) (modPowMod A X b) := rfl
  -- names for the factors of the chain
  set w₁ := (tensorPow D X a ◁ (actRight A X ▷ X)) ▷
    tensorPow D X b with hw₁
  set w₂ := (α_ (tensorPow D X a) X X).inv ▷ tensorPow D X b
    with hw₂
  set cc := (tensorPowConcat X (a + 2) b).hom with hcc
  set ci := (tensorPowConcat X (a + 1) (b + 1)).inv with hci
  set pd := powDetach X (a + 1) b with hpd
  set pl := tensorPow D X (a + 1) ◁ (powPeel X b).inv with hpl
  set ππ := modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1) with hππ
  set mT := modTensorπ A (modPowMod A X a) (modPowMod A X b)
    with hmT
  set σ₁ := (α_ (tensorPow D X a) ((X ⊗ A) ⊗ X)
    (tensorPow D X b)).hom with hσ₁
  set σ₂ := tensorPow D X a ◁
    (α_ (X ⊗ A) X (tensorPow D X b)).hom with hσ₂
  set σ₃ := (α_ (tensorPow D X a) (X ⊗ A)
    (X ⊗ tensorPow D X b)).inv with hσ₃
  set wact := (tensorPow D X a ◁ actRight A X) ▷
    (X ⊗ tensorPow D X b) with hwact
  set bA := boundAssoc A X a ▷ (X ⊗ tensorPow D X b) with hbA
  set tH := (modPowπ A X (a + 1) ▷ A) ⊗ₘ headMod A X b with htH
  set pR := powActRight A X a ▷ modPow A X (b + 1) with hpR
  set cs := powCast X
    (by omega : a + 2 + b = a + 1 + (b + 1)) with hcs
  have E1 : cc ≫ (cs ≫ (ci ≫ (ππ ≫ mT))) =
      pd ≫ (pl ≫ (ππ ≫ mT)) :=
    (reassoc_of% hsplit) (ππ ≫ mT)
  have E2 : wact ≫ (pl ≫ (ππ ≫ mT)) =
      bA ≫ (tH ≫ (pR ≫ mT)) := by
    calc wact ≫ (pl ≫ (ππ ≫ mT))
        = wact ≫ ((pl ≫ ππ) ≫ mT) :=
          congrArg (fun z => wact ≫ z)
            (Category.assoc pl ππ mT).symm
      _ = wact ≫ ((modPowπ A X (a + 1) ⊗ₘ headMod A X b) ≫
            mT) :=
          congrArg (fun z => wact ≫ (z ≫ mT)) sub1
      _ = (wact ≫ (modPowπ A X (a + 1) ⊗ₘ headMod A X b)) ≫
            mT :=
          (Category.assoc wact _ mT).symm
      _ = (bA ≫ (tH ≫ pR)) ≫ mT := congrArg (· ≫ mT) sub2
      _ = bA ≫ (tH ≫ (pR ≫ mT)) :=
          (Category.assoc bA (tH ≫ pR) mT).trans
            (congrArg (fun z => bA ≫ z)
              (Category.assoc tH pR mT))
  calc modPowLegM A X a b ≫
      (cs ≫ (ci ≫ (ππ ≫ mT)))
      = (w₁ ≫ (w₂ ≫ cc)) ≫ (cs ≫ (ci ≫ (ππ ≫ mT))) := rfl
    _ = w₁ ≫ ((w₂ ≫ cc) ≫ (cs ≫ (ci ≫ (ππ ≫ mT)))) :=
        Category.assoc w₁ (w₂ ≫ cc) _
    _ = w₁ ≫ (w₂ ≫ (cc ≫ (cs ≫ (ci ≫ (ππ ≫ mT))))) :=
        congrArg (fun z => w₁ ≫ z) (Category.assoc w₂ cc _)
    _ = w₁ ≫ (w₂ ≫ (pd ≫ (pl ≫ (ππ ≫ mT)))) :=
        congrArg (fun z => w₁ ≫ (w₂ ≫ z)) E1
    _ = w₁ ≫ ((w₂ ≫ pd) ≫ (pl ≫ (ππ ≫ mT))) :=
        congrArg (fun z => w₁ ≫ z)
          (Category.assoc w₂ pd _).symm
    _ = (w₁ ≫ (w₂ ≫ pd)) ≫ (pl ≫ (ππ ≫ mT)) :=
        (Category.assoc w₁ (w₂ ≫ pd) _).symm
    _ = (σ₁ ≫ (σ₂ ≫ (σ₃ ≫ wact))) ≫ (pl ≫ (ππ ≫ mT)) :=
        congrArg (· ≫ (pl ≫ (ππ ≫ mT))) hM
    _ = σ₁ ≫ ((σ₂ ≫ (σ₃ ≫ wact)) ≫ (pl ≫ (ππ ≫ mT))) :=
        Category.assoc σ₁ _ _
    _ = σ₁ ≫ (σ₂ ≫ ((σ₃ ≫ wact) ≫ (pl ≫ (ππ ≫ mT)))) :=
        congrArg (fun z => σ₁ ≫ z) (Category.assoc σ₂ _ _)
    _ = σ₁ ≫ (σ₂ ≫ (σ₃ ≫ (wact ≫ (pl ≫ (ππ ≫ mT))))) :=
        congrArg (fun z => σ₁ ≫ (σ₂ ≫ z))
          (Category.assoc σ₃ wact _)
    _ = σ₁ ≫ (σ₂ ≫ (σ₃ ≫ (bA ≫ (tH ≫ (pR ≫ mT))))) :=
        congrArg (fun z => σ₁ ≫ (σ₂ ≫ (σ₃ ≫ z))) E2
    _ = σ₁ ≫ (σ₂ ≫ (σ₃ ≫ ((bA ≫ tH) ≫ (pR ≫ mT)))) :=
        congrArg (fun z => σ₁ ≫ (σ₂ ≫ (σ₃ ≫ z)))
          (Category.assoc bA tH _).symm
    _ = σ₁ ≫ (σ₂ ≫ ((σ₃ ≫ (bA ≫ tH)) ≫ (pR ≫ mT))) :=
        congrArg (fun z => σ₁ ≫ (σ₂ ≫ z))
          (Category.assoc σ₃ (bA ≫ tH) _).symm
    _ = σ₁ ≫ ((σ₂ ≫ (σ₃ ≫ (bA ≫ tH))) ≫ (pR ≫ mT)) :=
        congrArg (fun z => σ₁ ≫ z)
          (Category.assoc σ₂ (σ₃ ≫ (bA ≫ tH)) _).symm
    _ = (σ₁ ≫ (σ₂ ≫ (σ₃ ≫ (bA ≫ tH)))) ≫ (pR ≫ mT) :=
        (Category.assoc σ₁ (σ₂ ≫ (σ₃ ≫ (bA ≫ tH)))
          (pR ≫ mT)).symm
    _ = boundBridge A X a b ≫
          (modTensorLegM A (modPowMod A X a) (modPowMod A X b) ≫
            mT) :=
        congrArg (fun z => boundBridge A X a b ≫ (z ≫ mT)) hLegM

/-- The `N`-leg of the boundary slot factors through the boundary
bridge and the second module-tensor leg. -/
theorem boundBridge_legN
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (a b : ℕ) :
    modPowLegN A X a b ≫
        powCast X (by omega : a + 2 + b = a + 1 + (b + 1)) ≫
        (tensorPowConcat X (a + 1) (b + 1)).inv ≫
        (modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫
        modTensorπ A (modPowMod A X a) (modPowMod A X b) =
      boundBridge A X a b ≫
        modTensorLegN A (modPowMod A X a) (modPowMod A X b) ≫
        modTensorπ A (modPowMod A X a) (modPowMod A X b) := by
  have hsplit : (tensorPowConcat X (a + 2) b).hom ≫
      powCast X (by omega : a + 2 + b = a + 1 + (b + 1)) ≫
      (tensorPowConcat X (a + 1) (b + 1)).inv =
        powDetach X (a + 1) b ≫
          (tensorPow D X (a + 1) ◁ (powPeel X b).inv) :=
    concat_split_bound X a b
  have hN : ((tensorPow D X a ◁
        ((α_ X A X).hom ≫ (X ◁ actLeft A X))) ▷
        tensorPow D X b) ≫
      ((α_ (tensorPow D X a) X X).inv ▷ tensorPow D X b) ≫
      powDetach X (a + 1) b =
        (α_ (tensorPow D X a) ((X ⊗ A) ⊗ X)
            (tensorPow D X b)).hom ≫
          (tensorPow D X a ◁
            (α_ (X ⊗ A) X (tensorPow D X b)).hom) ≫
          (α_ (tensorPow D X a) (X ⊗ A)
            (X ⊗ tensorPow D X b)).inv ≫
          (boundAssoc A X a ▷ (X ⊗ tensorPow D X b)) ≫
          (α_ (tensorPow D X (a + 1)) A
            (X ⊗ tensorPow D X b)).hom ≫
          (tensorPow D X (a + 1) ◁
            ((α_ A X (tensorPow D X b)).inv ≫
              (actLeft A X ▷ tensorPow D X b))) :=
    split_shuffle_snd (actLeft A X)
  have sub1 : (tensorPow D X (a + 1) ◁ (powPeel X b).inv) ≫
      (modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) =
        (modPowπ A X (a + 1) ⊗ₘ headMod A X b) :=
    whiskerLeft_comp_tensorHom (powPeel X b).inv
      (modPowπ A X (a + 1)) (modPowπ A X (b + 1))
  have n2 : (tensorPow D X (a + 1) ◁
        ((α_ A X (tensorPow D X b)).inv ≫
          (actLeft A X ▷ tensorPow D X b))) ≫
      (modPowπ A X (a + 1) ⊗ₘ headMod A X b) =
        (modPowπ A X (a + 1) ⊗ₘ
          (((α_ A X (tensorPow D X b)).inv ≫
            (actLeft A X ▷ tensorPow D X b)) ≫
            headMod A X b)) :=
    whiskerLeft_comp_tensorHom _ (modPowπ A X (a + 1))
      (headMod A X b)
  have n3 : ((α_ A X (tensorPow D X b)).inv ≫
        (actLeft A X ▷ tensorPow D X b)) ≫ headMod A X b =
      (A ◁ headMod A X b) ≫ modPowAct A X b :=
    (Category.assoc _ _ _).trans (headMod_act A X b).symm
  have n4 : (modPowπ A X (a + 1) ⊗ₘ
        ((A ◁ headMod A X b) ≫ modPowAct A X b)) =
      (modPowπ A X (a + 1) ⊗ₘ (A ◁ headMod A X b)) ≫
        (modPow A X (a + 1) ◁ modPowAct A X b) :=
    (tensorHom_comp_whiskerLeft (modPowπ A X (a + 1))
      (A ◁ headMod A X b) (modPowAct A X b)).symm
  have n5 : (α_ (tensorPow D X (a + 1)) A
        (X ⊗ tensorPow D X b)).hom ≫
      (modPowπ A X (a + 1) ⊗ₘ (A ◁ headMod A X b)) =
        ((modPowπ A X (a + 1) ▷ A) ⊗ₘ headMod A X b) ≫
          (α_ (modPow A X (a + 1)) A (modPow A X (b + 1))).hom := by
    have hnat := associator_naturality (modPowπ A X (a + 1)) (𝟙 A)
      (headMod A X b)
    rw [tensorHom_id, id_tensorHom] at hnat
    exact hnat.symm
  have hLegN : (α_ (modPow A X (a + 1)) A
        (modPow A X (b + 1))).hom ≫
      (modPow A X (a + 1) ◁ modPowAct A X b) =
        modTensorLegN A (modPowMod A X a) (modPowMod A X b) := rfl
  set w₁ := (tensorPow D X a ◁
    ((α_ X A X).hom ≫ (X ◁ actLeft A X))) ▷ tensorPow D X b
    with hw₁
  set w₂ := (α_ (tensorPow D X a) X X).inv ▷ tensorPow D X b
    with hw₂
  set cc := (tensorPowConcat X (a + 2) b).hom with hcc
  set ci := (tensorPowConcat X (a + 1) (b + 1)).inv with hci
  set pd := powDetach X (a + 1) b with hpd
  set pl := tensorPow D X (a + 1) ◁ (powPeel X b).inv with hpl
  set ππ := modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1) with hππ
  set mT := modTensorπ A (modPowMod A X a) (modPowMod A X b)
    with hmT
  set σ₁ := (α_ (tensorPow D X a) ((X ⊗ A) ⊗ X)
    (tensorPow D X b)).hom with hσ₁
  set σ₂ := tensorPow D X a ◁
    (α_ (X ⊗ A) X (tensorPow D X b)).hom with hσ₂
  set σ₃ := (α_ (tensorPow D X a) (X ⊗ A)
    (X ⊗ tensorPow D X b)).inv with hσ₃
  set bA := boundAssoc A X a ▷ (X ⊗ tensorPow D X b) with hbA
  set σ₅ := (α_ (tensorPow D X (a + 1)) A
    (X ⊗ tensorPow D X b)).hom with hσ₅
  set wv := tensorPow D X (a + 1) ◁
    ((α_ A X (tensorPow D X b)).inv ≫
      (actLeft A X ▷ tensorPow D X b)) with hwv
  set tH := (modPowπ A X (a + 1) ▷ A) ⊗ₘ headMod A X b with htH
  set wq := modPow A X (a + 1) ◁ modPowAct A X b with hwq
  set aₘ := (α_ (modPow A X (a + 1)) A
    (modPow A X (b + 1))).hom with haₘ
  set cs := powCast X
    (by omega : a + 2 + b = a + 1 + (b + 1)) with hcs
  have E1 : cc ≫ (cs ≫ (ci ≫ (ππ ≫ mT))) =
      pd ≫ (pl ≫ (ππ ≫ mT)) :=
    (reassoc_of% hsplit) (ππ ≫ mT)
  have E2 : σ₅ ≫ (wv ≫ (pl ≫ (ππ ≫ mT))) =
      tH ≫ (modTensorLegN A (modPowMod A X a) (modPowMod A X b) ≫
        mT) := by
    calc σ₅ ≫ (wv ≫ (pl ≫ (ππ ≫ mT)))
        = σ₅ ≫ (wv ≫ ((pl ≫ ππ) ≫ mT)) :=
          congrArg (fun z => σ₅ ≫ (wv ≫ z))
            (Category.assoc pl ππ mT).symm
      _ = σ₅ ≫ (wv ≫ ((modPowπ A X (a + 1) ⊗ₘ headMod A X b) ≫
            mT)) :=
          congrArg (fun z => σ₅ ≫ (wv ≫ (z ≫ mT))) sub1
      _ = σ₅ ≫ ((wv ≫ (modPowπ A X (a + 1) ⊗ₘ headMod A X b)) ≫
            mT) :=
          congrArg (fun z => σ₅ ≫ z) (Category.assoc wv _ mT).symm
      _ = σ₅ ≫ ((modPowπ A X (a + 1) ⊗ₘ
            (((α_ A X (tensorPow D X b)).inv ≫
              (actLeft A X ▷ tensorPow D X b)) ≫
              headMod A X b)) ≫ mT) :=
          congrArg (fun z => σ₅ ≫ (z ≫ mT)) n2
      _ = σ₅ ≫ ((modPowπ A X (a + 1) ⊗ₘ
            ((A ◁ headMod A X b) ≫ modPowAct A X b)) ≫ mT) :=
          congrArg (fun z => σ₅ ≫
            ((modPowπ A X (a + 1) ⊗ₘ z) ≫ mT)) n3
      _ = σ₅ ≫ (((modPowπ A X (a + 1) ⊗ₘ
            (A ◁ headMod A X b)) ≫ wq) ≫ mT) :=
          congrArg (fun z => σ₅ ≫ (z ≫ mT)) n4
      _ = σ₅ ≫ ((modPowπ A X (a + 1) ⊗ₘ
            (A ◁ headMod A X b)) ≫ (wq ≫ mT)) :=
          congrArg (fun z => σ₅ ≫ z)
            (Category.assoc _ wq mT)
      _ = (σ₅ ≫ (modPowπ A X (a + 1) ⊗ₘ
            (A ◁ headMod A X b))) ≫ (wq ≫ mT) :=
          (Category.assoc σ₅ _ (wq ≫ mT)).symm
      _ = (tH ≫ aₘ) ≫ (wq ≫ mT) :=
          congrArg (· ≫ (wq ≫ mT)) n5
      _ = tH ≫ (aₘ ≫ (wq ≫ mT)) :=
          Category.assoc tH aₘ (wq ≫ mT)
      _ = tH ≫ ((aₘ ≫ wq) ≫ mT) :=
          congrArg (fun z => tH ≫ z)
            (Category.assoc aₘ wq mT).symm
      _ = tH ≫ (modTensorLegN A (modPowMod A X a)
            (modPowMod A X b) ≫ mT) :=
          congrArg (fun z => tH ≫ (z ≫ mT)) hLegN
  calc modPowLegN A X a b ≫ (cs ≫ (ci ≫ (ππ ≫ mT)))
      = (w₁ ≫ (w₂ ≫ cc)) ≫ (cs ≫ (ci ≫ (ππ ≫ mT))) := rfl
    _ = w₁ ≫ ((w₂ ≫ cc) ≫ (cs ≫ (ci ≫ (ππ ≫ mT)))) :=
        Category.assoc w₁ (w₂ ≫ cc) _
    _ = w₁ ≫ (w₂ ≫ (cc ≫ (cs ≫ (ci ≫ (ππ ≫ mT))))) :=
        congrArg (fun z => w₁ ≫ z) (Category.assoc w₂ cc _)
    _ = w₁ ≫ (w₂ ≫ (pd ≫ (pl ≫ (ππ ≫ mT)))) :=
        congrArg (fun z => w₁ ≫ (w₂ ≫ z)) E1
    _ = w₁ ≫ ((w₂ ≫ pd) ≫ (pl ≫ (ππ ≫ mT))) :=
        congrArg (fun z => w₁ ≫ z)
          (Category.assoc w₂ pd _).symm
    _ = (w₁ ≫ (w₂ ≫ pd)) ≫ (pl ≫ (ππ ≫ mT)) :=
        (Category.assoc w₁ (w₂ ≫ pd) _).symm
    _ = (σ₁ ≫ (σ₂ ≫ (σ₃ ≫ (bA ≫ (σ₅ ≫ wv))))) ≫
          (pl ≫ (ππ ≫ mT)) :=
        congrArg (· ≫ (pl ≫ (ππ ≫ mT))) hN
    _ = σ₁ ≫ ((σ₂ ≫ (σ₃ ≫ (bA ≫ (σ₅ ≫ wv)))) ≫
          (pl ≫ (ππ ≫ mT))) :=
        Category.assoc σ₁ _ _
    _ = σ₁ ≫ (σ₂ ≫ ((σ₃ ≫ (bA ≫ (σ₅ ≫ wv))) ≫
          (pl ≫ (ππ ≫ mT)))) :=
        congrArg (fun z => σ₁ ≫ z) (Category.assoc σ₂ _ _)
    _ = σ₁ ≫ (σ₂ ≫ (σ₃ ≫ ((bA ≫ (σ₅ ≫ wv)) ≫
          (pl ≫ (ππ ≫ mT))))) :=
        congrArg (fun z => σ₁ ≫ (σ₂ ≫ z))
          (Category.assoc σ₃ _ _)
    _ = σ₁ ≫ (σ₂ ≫ (σ₃ ≫ (bA ≫ ((σ₅ ≫ wv) ≫
          (pl ≫ (ππ ≫ mT)))))) :=
        congrArg (fun z => σ₁ ≫ (σ₂ ≫ (σ₃ ≫ z)))
          (Category.assoc bA _ _)
    _ = σ₁ ≫ (σ₂ ≫ (σ₃ ≫ (bA ≫ (σ₅ ≫ (wv ≫
          (pl ≫ (ππ ≫ mT))))))) :=
        congrArg (fun z => σ₁ ≫ (σ₂ ≫ (σ₃ ≫ (bA ≫ z))))
          (Category.assoc σ₅ wv _)
    _ = σ₁ ≫ (σ₂ ≫ (σ₃ ≫ (bA ≫ (tH ≫
          (modTensorLegN A (modPowMod A X a) (modPowMod A X b) ≫
            mT))))) :=
        congrArg (fun z => σ₁ ≫ (σ₂ ≫ (σ₃ ≫ (bA ≫ z)))) E2
    _ = σ₁ ≫ (σ₂ ≫ (σ₃ ≫ ((bA ≫ tH) ≫
          (modTensorLegN A (modPowMod A X a) (modPowMod A X b) ≫
            mT)))) :=
        congrArg (fun z => σ₁ ≫ (σ₂ ≫ (σ₃ ≫ z)))
          (Category.assoc bA tH _).symm
    _ = σ₁ ≫ (σ₂ ≫ ((σ₃ ≫ (bA ≫ tH)) ≫
          (modTensorLegN A (modPowMod A X a) (modPowMod A X b) ≫
            mT))) :=
        congrArg (fun z => σ₁ ≫ (σ₂ ≫ z))
          (Category.assoc σ₃ (bA ≫ tH) _).symm
    _ = σ₁ ≫ ((σ₂ ≫ (σ₃ ≫ (bA ≫ tH))) ≫
          (modTensorLegN A (modPowMod A X a) (modPowMod A X b) ≫
            mT)) :=
        congrArg (fun z => σ₁ ≫ z)
          (Category.assoc σ₂ (σ₃ ≫ (bA ≫ tH)) _).symm
    _ = (σ₁ ≫ (σ₂ ≫ (σ₃ ≫ (bA ≫ tH)))) ≫
          (modTensorLegN A (modPowMod A X a) (modPowMod A X b) ≫
            mT) :=
        (Category.assoc σ₁ _ _).symm
    _ = boundBridge A X a b ≫
          (modTensorLegN A (modPowMod A X a) (modPowMod A X b) ≫
            mT) := rfl

/-- **The boundary slot condition**: the slot relation straddling
the two halves is absorbed by the split, through the coequalizer
relation of the module tensor product. -/
theorem powSplit_cond_bound
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (a b : ℕ) :
    modPowLegM A X a b ≫
        powCast X (by omega : a + 2 + b = a + 1 + (b + 1)) ≫
        (tensorPowConcat X (a + 1) (b + 1)).inv ≫
        (modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫
        modTensorπ A (modPowMod A X a) (modPowMod A X b) =
      modPowLegN A X a b ≫
        powCast X (by omega : a + 2 + b = a + 1 + (b + 1)) ≫
        (tensorPowConcat X (a + 1) (b + 1)).inv ≫
        (modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫
        modTensorπ A (modPowMod A X a) (modPowMod A X b) :=
  (boundBridge_legM A X a b).trans
    ((congrArg (fun z => boundBridge A X a b ≫ z)
        (modTensor_condition A (modPowMod A X a)
          (modPowMod A X b))).trans
      (boundBridge_legN A X a b).symm)

end Boundary

/-! ## The interior slots

A slot relation lying inside one half of the split embeds across
the concatenation into that half and is absorbed by the half's own
projection.
-/

section Interior

/-- The bridge of `midConcatFst`, as an isomorphism. -/
noncomputable def midConcatFstIso
    [Category.{v} D] [MonoidalCategory D] (A : D) (X : D)
    (s t n : ℕ) :
    modPowMid A X s t ⊗ tensorPow D X n ≅
      modPowMid A X s (t + n) :=
  α_ (tensorPow D X s ⊗ ((X ⊗ A) ⊗ X)) (tensorPow D X t)
      (tensorPow D X n) ≪≫
    whiskerLeftIso (tensorPow D X s ⊗ ((X ⊗ A) ⊗ X))
      (tensorPowConcat X t n)

/-- The bridge of `midConcatSnd`, as an isomorphism. -/
noncomputable def midConcatSndIso
    [Category.{v} D] [MonoidalCategory D] (A : D) (X : D)
    (m s t : ℕ) :
    tensorPow D X m ⊗ modPowMid A X s t ≅
      modPowMid A X (m + s) t :=
  (α_ (tensorPow D X m)
      (tensorPow D X s ⊗ ((X ⊗ A) ⊗ X)) (tensorPow D X t)).symm ≪≫
    whiskerRightIso
      ((α_ (tensorPow D X m) (tensorPow D X s)
          ((X ⊗ A) ⊗ X)).symm ≪≫
        whiskerRightIso (tensorPowConcat X m s) ((X ⊗ A) ⊗ X))
      (tensorPow D X t)

/-- **The in-left slot condition**: a slot relation of the left
half is absorbed by the left projection. -/
theorem powSplit_cond_left
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (a b s t' : ℕ) (hL : s + 2 + t' = a + 1) :
    modPowLegM A X s (t' + (b + 1)) ≫
        powCast X
          (by omega : s + 2 + (t' + (b + 1)) = a + 1 + (b + 1)) ≫
        (tensorPowConcat X (a + 1) (b + 1)).inv ≫
        (modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫
        modTensorπ A (modPowMod A X a) (modPowMod A X b) =
      modPowLegN A X s (t' + (b + 1)) ≫
        powCast X
          (by omega : s + 2 + (t' + (b + 1)) = a + 1 + (b + 1)) ≫
        (tensorPowConcat X (a + 1) (b + 1)).inv ≫
        (modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫
        modTensorπ A (modPowMod A X a) (modPowMod A X b) := by
  have hwrc := powCast_whiskerRight_concat X hL (b + 1)
  have hc2 : (tensorPowConcat X (s + 2 + t') (b + 1)).hom ≫
      powCast X
        (by omega : s + 2 + t' + (b + 1) = a + 1 + (b + 1)) ≫
      (tensorPowConcat X (a + 1) (b + 1)).inv =
        powCast X hL ▷ tensorPow D X (b + 1) := by
    rw [← reassoc_of% hwrc, Iso.hom_inv_id, Category.comp_id]
  set ci := (tensorPowConcat X (a + 1) (b + 1)).inv with hci
  set ππ := modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1) with hππ
  set mT := modTensorπ A (modPowMod A X a) (modPowMod A X b)
    with hmT
  have key : ∀ w : (X ⊗ A) ⊗ X ⟶ X ⊗ X,
      midConcatFst A X s t' (b + 1) ≫
        ((((tensorPow D X s ◁ w) ▷ tensorPow D X (t' + (b + 1))) ≫
          modPowGlue X s (t' + (b + 1))) ≫
          (powCast X (by omega :
              s + 2 + (t' + (b + 1)) = a + 1 + (b + 1)) ≫
            (ci ≫ (ππ ≫ mT)))) =
        (((((tensorPow D X s ◁ w) ▷ tensorPow D X t') ≫
            modPowGlue X s t') ≫
          (powCast X hL ≫ modPowπ A X (a + 1))) ⊗ₘ
          modPowπ A X (b + 1)) ≫ mT := by
    intro w
    have hM1 := modPowLeg_concat_fst A X s t' (b + 1) w
    have hT : powCast X (by omega :
          s + 2 + (t' + (b + 1)) = a + 1 + (b + 1)) ≫
        (ci ≫ (ππ ≫ mT)) =
          powCast X (by omega : s + 2 + (t' + (b + 1)) =
              s + 2 + t' + (b + 1)) ≫
            (powCast X (by omega : s + 2 + t' + (b + 1) =
                a + 1 + (b + 1)) ≫
              (ci ≫ (ππ ≫ mT))) :=
      (powCast_comp_assoc X _ _ _).symm
    calc midConcatFst A X s t' (b + 1) ≫
        ((((tensorPow D X s ◁ w) ▷ tensorPow D X (t' + (b + 1))) ≫
          modPowGlue X s (t' + (b + 1))) ≫
          (powCast X (by omega :
              s + 2 + (t' + (b + 1)) = a + 1 + (b + 1)) ≫
            (ci ≫ (ππ ≫ mT))))
        = midConcatFst A X s t' (b + 1) ≫
            (((tensorPow D X s ◁ w) ▷
                tensorPow D X (t' + (b + 1))) ≫
              (modPowGlue X s (t' + (b + 1)) ≫
                (powCast X (by omega : s + 2 + (t' + (b + 1)) =
                    s + 2 + t' + (b + 1)) ≫
                  (powCast X (by omega : s + 2 + t' + (b + 1) =
                      a + 1 + (b + 1)) ≫
                    (ci ≫ (ππ ≫ mT)))))) := by
          exact congrArg (fun z => midConcatFst A X s t' (b + 1) ≫ z)
            ((congrArg (fun z =>
                (((tensorPow D X s ◁ w) ▷
                  tensorPow D X (t' + (b + 1))) ≫
                  modPowGlue X s (t' + (b + 1))) ≫ z) hT).trans
              (Category.assoc _ _ _))
      _ = (((tensorPow D X s ◁ w) ▷ tensorPow D X t') ≫
            modPowGlue X s t') ▷ tensorPow D X (b + 1) ≫
            ((tensorPowConcat X (s + 2 + t') (b + 1)).hom ≫
              (powCast X (by omega : s + 2 + t' + (b + 1) =
                  a + 1 + (b + 1)) ≫
                (ci ≫ (ππ ≫ mT)))) :=
          ((reassoc_of% hM1)
            (powCast X (by omega : s + 2 + t' + (b + 1) =
                a + 1 + (b + 1)) ≫
              (ci ≫ (ππ ≫ mT)))).symm
      _ = (((tensorPow D X s ◁ w) ▷ tensorPow D X t') ≫
            modPowGlue X s t') ▷ tensorPow D X (b + 1) ≫
            ((powCast X hL ▷ tensorPow D X (b + 1)) ≫
              (ππ ≫ mT)) :=
          congrArg (fun z =>
            (((tensorPow D X s ◁ w) ▷ tensorPow D X t') ≫
              modPowGlue X s t') ▷ tensorPow D X (b + 1) ≫ z)
            ((reassoc_of% hc2) (ππ ≫ mT))
      _ = (((tensorPow D X s ◁ w) ▷ tensorPow D X t') ≫
            modPowGlue X s t') ▷ tensorPow D X (b + 1) ≫
            (((powCast X hL ≫ modPowπ A X (a + 1)) ⊗ₘ
              modPowπ A X (b + 1)) ≫ mT) :=
          congrArg (fun z =>
            (((tensorPow D X s ◁ w) ▷ tensorPow D X t') ≫
              modPowGlue X s t') ▷ tensorPow D X (b + 1) ≫ z)
            ((Category.assoc _ ππ mT).symm.trans
              (congrArg (· ≫ mT)
                (whiskerRight_tensorHom (powCast X hL)
                  (modPowπ A X (a + 1)) (modPowπ A X (b + 1)))))
      _ = ((((((tensorPow D X s ◁ w) ▷ tensorPow D X t') ≫
            modPowGlue X s t') ≫
          (powCast X hL ≫ modPowπ A X (a + 1))) ⊗ₘ
          modPowπ A X (b + 1)) ≫ mT) :=
          ((Category.assoc _ _ mT).symm.trans
            (congrArg (· ≫ mT)
              (whiskerRight_tensorHom _
                (powCast X hL ≫ modPowπ A X (a + 1))
                (modPowπ A X (b + 1)))))
  refine (Iso.cancel_iso_hom_left
    (midConcatFstIso A X s t' (b + 1)) _ _).mp ?_
  refine (key (winLegM A X)).trans
    (Eq.trans ?_ (key (winLegN A X)).symm)
  exact congrArg
    (fun z => (z ⊗ₘ modPowπ A X (b + 1)) ≫ mT)
    (modPow_rel A X s t' hL)

/-- **The in-right slot condition**: a slot relation of the right
half is absorbed by the right projection. -/
theorem powSplit_cond_right
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (a b s' t : ℕ)
    (hR : s' + 2 + t = b + 1) :
    modPowLegM A X (a + 1 + s') t ≫
        powCast X
          (by omega : a + 1 + s' + 2 + t = a + 1 + (b + 1)) ≫
        (tensorPowConcat X (a + 1) (b + 1)).inv ≫
        (modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫
        modTensorπ A (modPowMod A X a) (modPowMod A X b) =
      modPowLegN A X (a + 1 + s') t ≫
        powCast X
          (by omega : a + 1 + s' + 2 + t = a + 1 + (b + 1)) ≫
        (tensorPowConcat X (a + 1) (b + 1)).inv ≫
        (modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫
        modTensorπ A (modPowMod A X a) (modPowMod A X b) := by
  have hwlc := powCast_whiskerLeft_concat X (a + 1) hR
  have hc2 : (tensorPowConcat X (a + 1) (s' + 2 + t)).hom ≫
      powCast X
        (by omega : a + 1 + (s' + 2 + t) = a + 1 + (b + 1)) ≫
      (tensorPowConcat X (a + 1) (b + 1)).inv =
        tensorPow D X (a + 1) ◁ powCast X hR := by
    rw [← reassoc_of% hwlc, Iso.hom_inv_id, Category.comp_id]
  set ci := (tensorPowConcat X (a + 1) (b + 1)).inv with hci
  set ππ := modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1) with hππ
  set mT := modTensorπ A (modPowMod A X a) (modPowMod A X b)
    with hmT
  have key : ∀ w : (X ⊗ A) ⊗ X ⟶ X ⊗ X,
      midConcatSnd A X (a + 1) s' t ≫
        ((((tensorPow D X (a + 1 + s') ◁ w) ▷ tensorPow D X t) ≫
          modPowGlue X (a + 1 + s') t) ≫
          (powCast X (by omega :
              a + 1 + s' + 2 + t = a + 1 + (b + 1)) ≫
            (ci ≫ (ππ ≫ mT)))) =
        (modPowπ A X (a + 1) ⊗ₘ
          ((((tensorPow D X s' ◁ w) ▷ tensorPow D X t) ≫
            modPowGlue X s' t) ≫
            (powCast X hR ≫ modPowπ A X (b + 1)))) ≫ mT := by
    intro w
    have hM1 := modPowLeg_concat_snd A X (a + 1) s' t w
    have hT : powCast X (by omega :
          a + 1 + s' + 2 + t = a + 1 + (b + 1)) ≫
        (ci ≫ (ππ ≫ mT)) =
          powCast X (by omega : a + 1 + s' + 2 + t =
              a + 1 + (s' + 2 + t)) ≫
            (powCast X (by omega : a + 1 + (s' + 2 + t) =
                a + 1 + (b + 1)) ≫
              (ci ≫ (ππ ≫ mT))) :=
      (powCast_comp_assoc X _ _ _).symm
    calc midConcatSnd A X (a + 1) s' t ≫
        ((((tensorPow D X (a + 1 + s') ◁ w) ▷ tensorPow D X t) ≫
          modPowGlue X (a + 1 + s') t) ≫
          (powCast X (by omega :
              a + 1 + s' + 2 + t = a + 1 + (b + 1)) ≫
            (ci ≫ (ππ ≫ mT))))
        = midConcatSnd A X (a + 1) s' t ≫
            (((tensorPow D X (a + 1 + s') ◁ w) ▷
                tensorPow D X t) ≫
              (modPowGlue X (a + 1 + s') t ≫
                (powCast X (by omega : a + 1 + s' + 2 + t =
                    a + 1 + (s' + 2 + t)) ≫
                  (powCast X (by omega : a + 1 + (s' + 2 + t) =
                      a + 1 + (b + 1)) ≫
                    (ci ≫ (ππ ≫ mT)))))) := by
          exact congrArg
            (fun z => midConcatSnd A X (a + 1) s' t ≫ z)
            ((congrArg (fun z =>
                (((tensorPow D X (a + 1 + s') ◁ w) ▷
                  tensorPow D X t) ≫
                  modPowGlue X (a + 1 + s') t) ≫ z) hT).trans
              (Category.assoc _ _ _))
      _ = (tensorPow D X (a + 1) ◁
            ((((tensorPow D X s' ◁ w) ▷ tensorPow D X t) ≫
              modPowGlue X s' t))) ≫
            ((tensorPowConcat X (a + 1) (s' + 2 + t)).hom ≫
              (powCast X (by omega : a + 1 + (s' + 2 + t) =
                  a + 1 + (b + 1)) ≫
                (ci ≫ (ππ ≫ mT)))) :=
          ((reassoc_of% hM1)
            (powCast X (by omega : a + 1 + (s' + 2 + t) =
                a + 1 + (b + 1)) ≫
              (ci ≫ (ππ ≫ mT)))).symm
      _ = (tensorPow D X (a + 1) ◁
            ((((tensorPow D X s' ◁ w) ▷ tensorPow D X t) ≫
              modPowGlue X s' t))) ≫
            ((tensorPow D X (a + 1) ◁ powCast X hR) ≫
              (ππ ≫ mT)) :=
          congrArg (fun z =>
            (tensorPow D X (a + 1) ◁
              ((((tensorPow D X s' ◁ w) ▷ tensorPow D X t) ≫
                modPowGlue X s' t))) ≫ z)
            ((reassoc_of% hc2) (ππ ≫ mT))
      _ = (tensorPow D X (a + 1) ◁
            ((((tensorPow D X s' ◁ w) ▷ tensorPow D X t) ≫
              modPowGlue X s' t))) ≫
            ((modPowπ A X (a + 1) ⊗ₘ
              (powCast X hR ≫ modPowπ A X (b + 1))) ≫ mT) :=
          congrArg (fun z =>
            (tensorPow D X (a + 1) ◁
              ((((tensorPow D X s' ◁ w) ▷ tensorPow D X t) ≫
                modPowGlue X s' t))) ≫ z)
            ((Category.assoc _ ππ mT).symm.trans
              (congrArg (· ≫ mT)
                (whiskerLeft_comp_tensorHom (powCast X hR)
                  (modPowπ A X (a + 1)) (modPowπ A X (b + 1)))))
      _ = (modPowπ A X (a + 1) ⊗ₘ
            ((((tensorPow D X s' ◁ w) ▷ tensorPow D X t) ≫
              modPowGlue X s' t) ≫
              (powCast X hR ≫ modPowπ A X (b + 1)))) ≫ mT :=
          ((Category.assoc _ _ mT).symm.trans
            (congrArg (· ≫ mT)
              (whiskerLeft_comp_tensorHom _
                (modPowπ A X (a + 1))
                (powCast X hR ≫ modPowπ A X (b + 1)))))
  refine (Iso.cancel_iso_hom_left
    (midConcatSndIso A X (a + 1) s' t) _ _).mp ?_
  refine (key (winLegM A X)).trans
    (Eq.trans ?_ (key (winLegN A X)).symm)
  exact congrArg
    (fun z => (modPowπ A X (a + 1) ⊗ₘ z) ≫ mT)
    (modPow_rel A X s' t hR)

end Interior

/-! ## The split and the merge isomorphism -/

section Merge

/-- **The wide-coequalizer condition of the split**: every slot
relation of the big power is absorbed by the split — inside the
left half, at the boundary, or inside the right half. -/
theorem powSplit_cond
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (a b : ℕ) :
    ∀ s t (hst : s + 2 + t = a + 1 + b + 1),
      modPowLegM A X s t ≫ powCast X hst ≫
        ((tensorPowConcat X (a + 1) (b + 1)).inv ≫
          (modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫
          modTensorπ A (modPowMod A X a) (modPowMod A X b)) =
      modPowLegN A X s t ≫ powCast X hst ≫
        ((tensorPowConcat X (a + 1) (b + 1)).inv ≫
          (modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫
          modTensorπ A (modPowMod A X a) (modPowMod A X b)) := by
  intro s t hst
  rcases Nat.lt_trichotomy s a with h | h | h
  · obtain ⟨t', rfl⟩ : ∃ t', t = t' + (b + 1) :=
      ⟨t - (b + 1), by omega⟩
    exact powSplit_cond_left A X a b s t' (by omega)
  · subst h
    obtain rfl : b = t := by omega
    exact powSplit_cond_bound A X s b
  · obtain ⟨s', rfl⟩ : ∃ s', s = a + 1 + s' :=
      ⟨s - (a + 1), by omega⟩
    exact powSplit_cond_right A X a b s' t (by omega)

/-- **The split of a module power**: the inverse of the
concatenation descends through the wide coequalizer onto the
module tensor product of the two halves. -/
noncomputable def powSplit
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (a b : ℕ) :
    modPow A X (a + 1 + b + 1) ⟶
      modTensor A (modPowMod A X a) (modPowMod A X b) :=
  modPowDesc A X
    ((tensorPowConcat X (a + 1) (b + 1)).inv ≫
      (modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫
      modTensorπ A (modPowMod A X a) (modPowMod A X b))
    (powSplit_cond A X a b)

/-- Defining equation of the split. -/
@[reassoc (attr := simp)]
theorem modPowπ_powSplit
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (a b : ℕ) :
    modPowπ A X (a + 1 + b + 1) ≫ powSplit A X a b =
      (tensorPowConcat X (a + 1) (b + 1)).inv ≫
        (modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫
        modTensorπ A (modPowMod A X a) (modPowMod A X b) :=
  modPowπ_desc A X _ _

/-- The split is a section of the descended power
multiplication. -/
@[reassoc (attr := simp)]
theorem powSplit_powMulDesc
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (a b : ℕ) :
    powSplit A X a b ≫ powMulDesc A X a b =
      𝟙 (modPow A X (a + 1 + b + 1)) := by
  apply modPow_hom_ext A X
  calc modPowπ A X (a + 1 + b + 1) ≫
      (powSplit A X a b ≫ powMulDesc A X a b)
      = (modPowπ A X (a + 1 + b + 1) ≫ powSplit A X a b) ≫
          powMulDesc A X a b := (Category.assoc _ _ _).symm
    _ = ((tensorPowConcat X (a + 1) (b + 1)).inv ≫
          (modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫
          modTensorπ A (modPowMod A X a) (modPowMod A X b)) ≫
          powMulDesc A X a b :=
        congrArg (· ≫ powMulDesc A X a b)
          (modPowπ_powSplit A X a b)
    _ = (tensorPowConcat X (a + 1) (b + 1)).inv ≫
          (((modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫
            modTensorπ A (modPowMod A X a) (modPowMod A X b)) ≫
          powMulDesc A X a b) := Category.assoc _ _ _
    _ = (tensorPowConcat X (a + 1) (b + 1)).inv ≫
          ((modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫
            (modTensorπ A (modPowMod A X a) (modPowMod A X b) ≫
              powMulDesc A X a b)) :=
        congrArg
          (fun z => (tensorPowConcat X (a + 1) (b + 1)).inv ≫ z)
          (Category.assoc _ _ _)
    _ = (tensorPowConcat X (a + 1) (b + 1)).inv ≫
          ((modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫
            modPowMul A X (a + 1) (b + 1)) :=
        congrArg
          (fun z => (tensorPowConcat X (a + 1) (b + 1)).inv ≫
            ((modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫ z))
          (modTensorπ_powMulDesc A X a b)
    _ = (tensorPowConcat X (a + 1) (b + 1)).inv ≫
          ((tensorPowConcat X (a + 1) (b + 1)).hom ≫
            modPowπ A X (a + 1 + (b + 1))) :=
        congrArg
          (fun z => (tensorPowConcat X (a + 1) (b + 1)).inv ≫ z)
          (modPowπ_tensor_modPowMul A X (a + 1) (b + 1))
    _ = modPowπ A X (a + 1 + (b + 1)) :=
        Iso.inv_hom_id_assoc (tensorPowConcat X (a + 1) (b + 1)) _
    _ = modPowπ A X (a + 1 + b + 1) ≫
          𝟙 (modPow A X (a + 1 + b + 1)) :=
        (Category.comp_id (modPowπ A X (a + 1 + b + 1))).symm

/-- The split is a retraction of the descended power
multiplication. -/
@[reassoc (attr := simp)]
theorem powMulDesc_powSplit
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (a b : ℕ) :
    powMulDesc A X a b ≫ powSplit A X a b =
      𝟙 (modTensor A (modPowMod A X a) (modPowMod A X b)) := by
  apply modTensor_hom_ext A (modPowMod A X a) (modPowMod A X b)
  apply modPowTensor_hom_ext A X (a + 1) (b + 1)
  have hs : modPowπ A X (a + 1 + (b + 1)) ≫ powSplit A X a b =
      (tensorPowConcat X (a + 1) (b + 1)).inv ≫
        ((modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫
          modTensorπ A (modPowMod A X a) (modPowMod A X b)) :=
    modPowπ_powSplit A X a b
  calc (modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫
      (modTensorπ A (modPowMod A X a) (modPowMod A X b) ≫
        (powMulDesc A X a b ≫ powSplit A X a b))
      = (modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫
          ((modTensorπ A (modPowMod A X a) (modPowMod A X b) ≫
            powMulDesc A X a b) ≫ powSplit A X a b) :=
        congrArg
          (fun z => (modPowπ A X (a + 1) ⊗ₘ
            modPowπ A X (b + 1)) ≫ z)
          (Category.assoc _ _ _).symm
    _ = (modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫
          (modPowMul A X (a + 1) (b + 1) ≫ powSplit A X a b) :=
        congrArg
          (fun z => (modPowπ A X (a + 1) ⊗ₘ
            modPowπ A X (b + 1)) ≫ (z ≫ powSplit A X a b))
          (modTensorπ_powMulDesc A X a b)
    _ = ((modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫
          modPowMul A X (a + 1) (b + 1)) ≫ powSplit A X a b :=
        (Category.assoc _ _ _).symm
    _ = ((tensorPowConcat X (a + 1) (b + 1)).hom ≫
          modPowπ A X (a + 1 + (b + 1))) ≫ powSplit A X a b :=
        congrArg (· ≫ powSplit A X a b)
          (modPowπ_tensor_modPowMul A X (a + 1) (b + 1))
    _ = (tensorPowConcat X (a + 1) (b + 1)).hom ≫
          (modPowπ A X (a + 1 + (b + 1)) ≫ powSplit A X a b) :=
        Category.assoc _ _ _
    _ = (tensorPowConcat X (a + 1) (b + 1)).hom ≫
          ((tensorPowConcat X (a + 1) (b + 1)).inv ≫
            ((modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫
              modTensorπ A (modPowMod A X a) (modPowMod A X b))) :=
        congrArg
          (fun z => (tensorPowConcat X (a + 1) (b + 1)).hom ≫ z)
          hs
    _ = (modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫
          modTensorπ A (modPowMod A X a) (modPowMod A X b) :=
        Iso.hom_inv_id_assoc (tensorPowConcat X (a + 1) (b + 1)) _
    _ = (modPowπ A X (a + 1) ⊗ₘ modPowπ A X (b + 1)) ≫
          (modTensorπ A (modPowMod A X a) (modPowMod A X b) ≫
            𝟙 (modTensor A (modPowMod A X a) (modPowMod A X b))) :=
        congrArg
          (fun z => (modPowπ A X (a + 1) ⊗ₘ
            modPowπ A X (b + 1)) ≫ z)
          (Category.comp_id _).symm

/-- **The merge isomorphism**: the relative tensor product of two
module powers is the module power of the summed arity, with the
descended power multiplication as the forward direction and the
split as its inverse. -/
noncomputable def powMergeIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (a b : ℕ) :
    modTensor A (modPowMod A X a) (modPowMod A X b) ≅
      modPow A X (a + 1 + b + 1) where
  hom := powMulDesc A X a b
  inv := powSplit A X a b
  hom_inv_id := powMulDesc_powSplit A X a b
  inv_hom_id := powSplit_powMulDesc A X a b

end Merge

end RS
