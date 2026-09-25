/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SymAlg

/-!
# Multiplication on symmetric module powers

The multiplication layer of Deligne (2002), §2.8: over an internal
monoid `A` and a module `X`, the concatenation of tensor powers
descends through the module-power coequalizers of `SymAlg.lean` to a
multiplication `modPow A X m ⊗ modPow A X n ⟶ modPow A X (m + n)`,
and then, through the symmetrisers, to the symmetric powers.

* `tensorPowConcat_assoc`: the concatenation isomorphisms are
  associative up to the `powCast` of `p + (q + r) = p + q + r`.
* `midConcatFst`/`midConcatSnd` and `modPowMul_rel_fst/snd`: the
  slot relations of arity `m` (resp. `n`) embed across the
  concatenation boundary into slots of `m + n`.
* `modPowMul`: the raw multiplication, descended in two stages
  through whiskered coequalizers; its defining equation is
  `(modPowπ ⊗ₘ modPowπ) ≫ modPowMul = concat ≫ modPowπ`.
* `modPowMul_perm`/`modPowMul_alg`: equivariance for the block
  embedding of permutations and its `ℂ`-bilinear extension.
* `symMul`: the multiplication on symmetric powers, with defining
  equation `(symPowπ ⊗ₘ symPowπ) ≫ symMul = modPowMul ≫ symPowπ`,
  by absorption of the block-embedded symmetrisers.
* Laws: `symPowZero`, unit laws (`symMul_zero_left/right`),
  associativity (`symMul_assoc`) and commutativity (`symMul_comm`,
  through `tensorPowConcat_braiding_exists`: the braiding of two
  tensor powers is, across the concatenations, the action of a
  permutation, which the symmetriser absorbs).

Whiskered coequalizers are handled by an instance parameter asking
that each `tensorLeft Y` preserve colimits of parallel pairs — in a
braided category the `tensorRight` mirror follows — together with
`MonoidalPreadditive D` for the biproduct legs; these hold in the
intended consumers.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## Associativity of the concatenation -/

section ConcatAssoc

/-- The base of the associativity recursion, at general objects. -/
private theorem concat_assoc_zero_aux [Category.{v} D] [MonoidalCategory D]
    {P Q R : D} (c : P ⊗ Q ⟶ R) :
    (c ▷ 𝟙_ D) ≫ (ρ_ R).hom =
      (α_ P Q (𝟙_ D)).hom ≫ (P ◁ (ρ_ Q).hom) ≫ c := by
  have h : (α_ P Q (𝟙_ D)).hom ≫ (P ◁ (ρ_ Q).hom) =
      (ρ_ (P ⊗ Q)).hom := by monoidal
  rw [← Category.assoc, h, MonoidalCategory.rightUnitor_naturality]

/-- The step of the associativity recursion, at general objects:
one exposed top factor passes from the inner to the outer
concatenation stage. -/
private theorem concat_assoc_step_aux [Category.{v} D] [MonoidalCategory D]
    {P Q R S T Y : D}
    (cq : Q ⊗ R ⟶ S) (cp : P ⊗ S ⟶ T) :
    (α_ P Q (R ⊗ Y)).hom ≫
        (P ◁ ((α_ Q R Y).inv ≫ (cq ▷ Y))) ≫
        (α_ P S Y).inv ≫ (cp ▷ Y) =
      (α_ (P ⊗ Q) R Y).inv ≫ ((α_ P Q R).hom ▷ Y) ≫
        (((P ◁ cq) ≫ cp) ▷ Y) := by
  have hpent : (α_ P Q (R ⊗ Y)).hom ≫ (P ◁ (α_ Q R Y).inv) ≫
      (α_ P (Q ⊗ R) Y).inv =
        (α_ (P ⊗ Q) R Y).inv ≫ ((α_ P Q R).hom ▷ Y) := by
    monoidal
  rw [MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [MonoidalCategory.associator_inv_naturality_middle_assoc,
    reassoc_of% hpent, ← MonoidalCategory.comp_whiskerRight]

/-- **Associativity of the concatenation**: concatenating the first
two blocks and then the third agrees, up to the arity transport of
`p + (q + r) = p + q + r`, with concatenating the last two blocks
and then the first. -/
theorem tensorPowConcat_assoc [Category.{v} D] [MonoidalCategory D] (X : D)
    (p q : ℕ) : ∀ r : ℕ,
    ((tensorPowConcat X p q).hom ▷ tensorPow D X r) ≫
        (tensorPowConcat X (p + q) r).hom =
      (α_ (tensorPow D X p) (tensorPow D X q) (tensorPow D X r)).hom ≫
        (tensorPow D X p ◁ (tensorPowConcat X q r).hom) ≫
        (tensorPowConcat X p (q + r)).hom ≫
        powCast X (by omega : p + (q + r) = p + q + r)
  | 0 => by
    have hc : powCast X
        (by omega : p + (q + 0) = p + q + 0) = 𝟙 _ := rfl
    rw [tensorPowConcat_zero, tensorPowConcat_zero, hc,
      Category.comp_id]
    exact concat_assoc_zero_aux ((tensorPowConcat X p q).hom)
  | r + 1 => by
    have hstep := concat_assoc_step_aux (Y := X)
      ((tensorPowConcat X q r).hom) ((tensorPowConcat X p (q + r)).hom)
    have hcast : powCast X
        (by omega : p + (q + (r + 1)) = p + q + (r + 1)) =
          powCast X (by omega : p + (q + r) = p + q + r) ▷ X := by
      rw [powCast_whiskerRight]
    change ((tensorPowConcat X p q).hom ▷
          (tensorPow D X r ⊗ X)) ≫
        (powExpose X (p + q) r ≫
          ((tensorPowConcat X (p + q) r).hom ▷ X)) =
      (α_ (tensorPow D X p) (tensorPow D X q)
          (tensorPow D X r ⊗ X)).hom ≫
        (tensorPow D X p ◁ (powExpose X q r ≫
          ((tensorPowConcat X q r).hom ▷ X))) ≫
        (powExpose X p (q + r) ≫
          ((tensorPowConcat X p (q + r)).hom ▷ X)) ≫
        powCast X (by omega : p + (q + (r + 1)) = p + q + (r + 1))
    rw [hcast, powExpose, powExpose, powExpose]
    repeat' erw [Category.assoc]
    rw [MonoidalCategory.associator_inv_naturality_left_assoc,
      ← MonoidalCategory.comp_whiskerRight,
      tensorPowConcat_assoc X p q r]
    simp only [MonoidalCategory.whiskerLeft_comp,
      MonoidalCategory.comp_whiskerRight, Category.assoc] at hstep ⊢
    erw [reassoc_of% hstep]
    rfl

/-- Concatenation with an empty first block is the left unitor, up
to the arity transport. -/
theorem tensorPowConcat_zero_left
    [Category.{v} D] [MonoidalCategory D] (X : D) : ∀ n : ℕ,
    (tensorPowConcat X 0 n).hom =
      (λ_ (tensorPow D X n)).hom ≫ powCast X (by omega : n = 0 + n)
  | 0 => by
    have hc : powCast X (by omega : 0 = 0 + 0) = 𝟙 _ := rfl
    rw [tensorPowConcat_zero, hc, Category.comp_id]
    change (ρ_ (𝟙_ D)).hom = (λ_ (𝟙_ D)).hom
    rw [← unitors_equal]
  | n + 1 => by
    have hcast : powCast X (by omega : n + 1 = 0 + (n + 1)) =
        powCast X (by omega : n = 0 + n) ▷ X := by
      rw [powCast_whiskerRight]
    have hlam : (α_ (𝟙_ D) (tensorPow D X n) X).inv ≫
        ((λ_ (tensorPow D X n)).hom ▷ X) =
        (λ_ (tensorPow D X n ⊗ X)).hom := by
      monoidal
    rw [tensorPowConcat_succ_hom X 0 n, tensorPowConcat_zero_left X n]
    change (α_ (𝟙_ D) (tensorPow D X n) X).inv ≫
        (((λ_ (tensorPow D X n)).hom ≫
          powCast X (by omega : n = 0 + n)) ▷ X) =
      (λ_ (tensorPow D X n ⊗ X)).hom ≫
        powCast X (by omega : n + 1 = 0 + (n + 1))
    rw [MonoidalCategory.comp_whiskerRight, ← Category.assoc, hlam,
      hcast]
    rfl

end ConcatAssoc

/-! ## Transport of concatenation and projections along arities -/

section CastTransport

/-- An arity transport of the first block passes the
concatenation. -/
theorem powCast_whiskerRight_concat
    [Category.{v} D] [MonoidalCategory D] (X : D)
    {k m : ℕ} (h : k = m) (n : ℕ) :
    (powCast X h ▷ tensorPow D X n) ≫ (tensorPowConcat X m n).hom =
      (tensorPowConcat X k n).hom ≫
        powCast X (by omega : k + n = m + n) := by
  subst h
  simp

/-- An arity transport of the second block passes the
concatenation. -/
theorem powCast_whiskerLeft_concat [Category.{v} D] [MonoidalCategory D] (X : D)
    (m : ℕ) {k n : ℕ} (h : k = n) :
    (tensorPow D X m ◁ powCast X h) ≫ (tensorPowConcat X m n).hom =
      (tensorPowConcat X m k).hom ≫
        powCast X (by omega : m + k = m + n) := by
  subst h
  simp

end CastTransport

section ModCast

/-- Transport of a module power along an equality of arities. -/
noncomputable def modPowCast
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    {m n : ℕ} (h : m = n) :
    modPow A X m ⟶ modPow A X n :=
  eqToHom (congrArg (modPow A X) h)

@[simp]
theorem modPowCast_rfl
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (n : ℕ) :
    modPowCast A X (rfl : n = n) = 𝟙 _ := rfl

/-- Two module-power transports with the same endpoints agree. -/
theorem modPowCast_irrel
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    {m n : ℕ} (h h' : m = n) :
    modPowCast A X h = modPowCast A X h' := rfl

/-- The projection intertwines the two arity transports. -/
@[reassoc]
theorem modPowπ_cast
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    {m n : ℕ} (h : m = n) :
    modPowπ A X m ≫ modPowCast A X h =
      powCast X h ≫ modPowπ A X n := by
  subst h
  simp [powCast]

end ModCast

/-! ## Embedding the slot relations across the concatenation

A relation slot of the left block, whiskered by the right block and
concatenated, is a relation slot of the concatenated power; and
mirrored for the right block.  Each embedding is mediated by a
structural bridge morphism that is independent of the relation leg,
so both legs of a slot embed through the same bridge and the ambient
relation applies.
-/

section SlotEmbed

/-- The bridge carrying a left-block slot into the concatenated
power: reassociate the right block onto the slot context and
concatenate the contexts. -/
noncomputable def midConcatFst
    [Category.{v} D] [MonoidalCategory D] (A : D) (X : D)
    (a b n : ℕ) :
    modPowMid A X a b ⊗ tensorPow D X n ⟶ modPowMid A X a (b + n) :=
  (α_ (tensorPow D X a ⊗ ((X ⊗ A) ⊗ X)) (tensorPow D X b)
      (tensorPow D X n)).hom ≫
    ((tensorPow D X a ⊗ ((X ⊗ A) ⊗ X)) ◁
      (tensorPowConcat X b n).hom)

/-- The bridge carrying a right-block slot into the concatenated
power: reassociate the left block onto the slot's lower context and
concatenate. -/
noncomputable def midConcatSnd
    [Category.{v} D] [MonoidalCategory D] (A : D) (X : D)
    (m a b : ℕ) :
    tensorPow D X m ⊗ modPowMid A X a b ⟶ modPowMid A X (m + a) b :=
  (α_ (tensorPow D X m) (tensorPow D X a ⊗ ((X ⊗ A) ⊗ X))
      (tensorPow D X b)).inv ≫
    (((α_ (tensorPow D X m) (tensorPow D X a) ((X ⊗ A) ⊗ X)).inv ≫
      ((tensorPowConcat X m a).hom ▷ ((X ⊗ A) ⊗ X))) ▷
        tensorPow D X b)

/-- The exchange across the reassociated context, at general
objects. -/
private theorem exchange_assoc_aux [Category.{v} D] [MonoidalCategory D]
    {P M Q N S : D} (f : P ⟶ M)
    (c : Q ⊗ N ⟶ S) :
    ((f ▷ Q) ▷ N) ≫ (α_ M Q N).hom ≫ (M ◁ c) =
      (α_ P Q N).hom ≫ (P ◁ c) ≫ (f ▷ S) := by
  rw [MonoidalCategory.associator_naturality_left_assoc,
    ← MonoidalCategory.whisker_exchange]

/-- The left-block embedding at general objects, against an opaque
outer stage `E` carrying the associativity shift. -/
private theorem leg_fst_aux [Category.{v} D] [MonoidalCategory D] (X : D)
    {P V B N S U Z : D} (w : V ⟶ X ⊗ X)
    (cbn : B ⊗ N ⟶ S) (cab : ((P ⊗ X) ⊗ X) ⊗ B ⟶ U)
    (Cout : U ⊗ N ⟶ Z) (E : ((P ⊗ X) ⊗ X) ⊗ S ⟶ Z)
    (hs : (cab ▷ N) ≫ Cout =
      (α_ ((P ⊗ X) ⊗ X) B N).hom ≫
        (((P ⊗ X) ⊗ X) ◁ cbn) ≫ E) :
    ((((P ◁ w) ▷ B) ≫ ((α_ P X X).inv ▷ B) ≫ cab) ▷ N) ≫ Cout =
      ((α_ (P ⊗ V) B N).hom ≫ ((P ⊗ V) ◁ cbn)) ≫
        ((P ◁ w) ▷ S) ≫ ((α_ P X X).inv ▷ S) ≫ E := by
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [hs, ← MonoidalCategory.comp_whiskerRight_assoc,
    ← MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.associator_naturality_left_assoc,
    MonoidalCategory.whisker_exchange_assoc]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [← MonoidalCategory.whisker_exchange_assoc]

/-- **A left-block slot leg embeds across the concatenation**: the
same computation for both legs, with the leg abstracted as `w`. -/
theorem modPowLeg_concat_fst
    [Category.{v} D] [MonoidalCategory D] (A : D) (X : D)
    (a b n : ℕ)
    (w : (X ⊗ A) ⊗ X ⟶ X ⊗ X) :
    ((((tensorPow D X a ◁ w) ▷ tensorPow D X b) ≫
        modPowGlue X a b) ▷ tensorPow D X n) ≫
      (tensorPowConcat X (a + 2 + b) n).hom =
    midConcatFst A X a b n ≫
      ((tensorPow D X a ◁ w) ▷ tensorPow D X (b + n)) ≫
      modPowGlue X a (b + n) ≫
      powCast X (by omega : a + 2 + (b + n) = a + 2 + b + n) := by
  have h0 := leg_fst_aux X w ((tensorPowConcat X b n).hom)
    ((tensorPowConcat X (a + 2) b).hom)
    ((tensorPowConcat X (a + 2 + b) n).hom)
    ((tensorPowConcat X (a + 2) (b + n)).hom ≫
      powCast X (by omega : a + 2 + (b + n) = a + 2 + b + n))
    (tensorPowConcat_assoc X (a + 2) b n)
  simp only [modPowGlue, midConcatFst, Category.assoc] at h0 ⊢
  repeat' erw [Category.assoc]
  exact h0

/-- The core of the right-block embedding, at general objects. -/
private theorem concat_snd_core_aux
    [Category.{v} D] [MonoidalCategory D] (X : D)
    {P Q V M : D} (w : V ⟶ X ⊗ X)
    (c : P ⊗ Q ⟶ M) :
    (P ◁ ((Q ◁ w) ≫ (α_ Q X X).inv)) ≫
        (α_ P (Q ⊗ X) X).inv ≫
        (((α_ P Q X).inv ≫ (c ▷ X)) ▷ X) =
      (α_ P Q V).inv ≫ (c ▷ V) ≫ (M ◁ w) ≫ (α_ M X X).inv := by
  have hpent : (P ◁ (α_ Q X X).inv) ≫ (α_ P (Q ⊗ X) X).inv ≫
      ((α_ P Q X).inv ▷ X) =
        (α_ P Q (X ⊗ X)).inv ≫ (α_ (P ⊗ Q) X X).inv := by
    monoidal
  rw [MonoidalCategory.whiskerLeft_comp]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [reassoc_of% hpent,
    MonoidalCategory.associator_inv_naturality_right_assoc,
    ← MonoidalCategory.associator_inv_naturality_left,
    MonoidalCategory.whisker_exchange_assoc]

/-- The right-block embedding at general objects, against an opaque
outer stage `E` carrying the associativity shift. -/
private theorem leg_snd_aux [Category.{v} D] [MonoidalCategory D] (X : D)
    {P Q V B N Z M : D} (w : V ⟶ X ⊗ X)
    (c : P ⊗ Q ⟶ M) (cab : ((Q ⊗ X) ⊗ X) ⊗ B ⟶ N)
    (Cbig : P ⊗ N ⟶ Z) (E : ((M ⊗ X) ⊗ X) ⊗ B ⟶ Z)
    (hs : (P ◁ cab) ≫ Cbig =
      (α_ P ((Q ⊗ X) ⊗ X) B).inv ≫
        (((α_ P (Q ⊗ X) X).inv ≫
          (((α_ P Q X).inv ≫ (c ▷ X)) ▷ X)) ▷ B) ≫ E) :
    (P ◁ (((Q ◁ w) ▷ B) ≫ ((α_ Q X X).inv ▷ B) ≫ cab)) ≫ Cbig =
      (α_ P (Q ⊗ V) B).inv ≫
        (((α_ P Q V).inv ≫ (c ▷ V)) ▷ B) ≫
        ((M ◁ w) ▷ B) ≫ ((α_ M X X).inv ▷ B) ≫ E := by
  have hbody : ((P ◁ (Q ◁ w)) ≫ (P ◁ (α_ Q X X).inv)) ≫
      ((α_ P (Q ⊗ X) X).inv ≫
        (((α_ P Q X).inv ≫ (c ▷ X)) ▷ X)) =
      (α_ P Q V).inv ≫ (c ▷ V) ≫ (M ◁ w) ≫ (α_ M X X).inv := by
    rw [← MonoidalCategory.whiskerLeft_comp]
    exact concat_snd_core_aux X w c
  rw [MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [hs, MonoidalCategory.associator_inv_naturality_middle_assoc,
    MonoidalCategory.associator_inv_naturality_middle_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc, hbody]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]

/-- **A right-block slot leg embeds across the concatenation**: the
same computation for both legs, with the leg abstracted as `w`. -/
theorem modPowLeg_concat_snd
    [Category.{v} D] [MonoidalCategory D] (A : D) (X : D)
    (m a b : ℕ)
    (w : (X ⊗ A) ⊗ X ⟶ X ⊗ X) :
    (tensorPow D X m ◁ (((tensorPow D X a ◁ w) ▷ tensorPow D X b) ≫
        modPowGlue X a b)) ≫
      (tensorPowConcat X m (a + 2 + b)).hom =
    midConcatSnd A X m a b ≫
      ((tensorPow D X (m + a) ◁ w) ▷ tensorPow D X b) ≫
      modPowGlue X (m + a) b ≫
      powCast X (by omega : m + a + 2 + b = m + (a + 2 + b)) := by
  have hassoc := tensorPowConcat_assoc X m (a + 2) b
  have hshift : (tensorPow D X m ◁ (tensorPowConcat X (a + 2) b).hom)
        ≫ (tensorPowConcat X m (a + 2 + b)).hom =
      (α_ (tensorPow D X m) (tensorPow D X (a + 2))
          (tensorPow D X b)).inv ≫
        ((tensorPowConcat X m (a + 2)).hom ▷ tensorPow D X b) ≫
        (tensorPowConcat X (m + (a + 2)) b).hom ≫
        powCast X (by omega : m + (a + 2) + b = m + (a + 2 + b)) := by
    rw [Iso.eq_inv_comp, reassoc_of% hassoc, powCast_comp]
    have hc : powCast X
        (by omega : m + (a + 2 + b) = m + (a + 2 + b)) = 𝟙 _ := rfl
    rw [hc, Category.comp_id]
  have h0 := leg_snd_aux X w
    ((tensorPowConcat X m a).hom) ((tensorPowConcat X (a + 2) b).hom)
    ((tensorPowConcat X m (a + 2 + b)).hom)
    ((tensorPowConcat X (m + (a + 2)) b).hom ≫
      powCast X (by omega : m + (a + 2) + b = m + (a + 2 + b)))
    hshift
  simp only [modPowGlue, midConcatSnd, Category.assoc] at h0 ⊢
  repeat' erw [Category.assoc]
  exact h0

end SlotEmbed

/-! ## The slot relations across the concatenation boundary -/

section RelEmbed

/-- **Left-block slot relations embed**: a relation slot of the
left block, whiskered by the right block and concatenated into the
ambient power of arity `m + n`, is absorbed by the projection. -/
theorem modPowMul_rel_fst
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    {m : ℕ} (n a b : ℕ) (hab : a + 2 + b = m) :
    ((modPowLegM A X a b ≫ powCast X hab) ▷ tensorPow D X n) ≫
        (tensorPowConcat X m n).hom ≫ modPowπ A X (m + n) =
      ((modPowLegN A X a b ≫ powCast X hab) ▷ tensorPow D X n) ≫
        (tensorPowConcat X m n).hom ≫ modPowπ A X (m + n) := by
  subst hab
  have hM := modPowLeg_concat_fst A X a b n (winLegM A X)
  have hN := modPowLeg_concat_fst A X a b n (winLegN A X)
  have hrel := modPow_rel A X a (b + n)
    (by omega : a + 2 + (b + n) = a + 2 + b + n)
  simp only [powCast_rfl, Category.comp_id, modPowLegM, modPowLegN,
    Category.assoc] at hrel ⊢
  rw [reassoc_of% hM, reassoc_of% hN, hrel]

/-- **Right-block slot relations embed**: a relation slot of the
right block, whiskered by the left block and concatenated into the
ambient power of arity `m + n`, is absorbed by the projection. -/
theorem modPowMul_rel_snd
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (m : ℕ) {n : ℕ} (a b : ℕ)
    (hab : a + 2 + b = n) :
    (tensorPow D X m ◁ (modPowLegM A X a b ≫ powCast X hab)) ≫
        (tensorPowConcat X m n).hom ≫ modPowπ A X (m + n) =
      (tensorPow D X m ◁ (modPowLegN A X a b ≫ powCast X hab)) ≫
        (tensorPowConcat X m n).hom ≫ modPowπ A X (m + n) := by
  subst hab
  have hM := modPowLeg_concat_snd A X m a b (winLegM A X)
  have hN := modPowLeg_concat_snd A X m a b (winLegN A X)
  have hrel := modPow_rel A X (m + a) b
    (by omega : m + a + 2 + b = m + (a + 2 + b))
  simp only [powCast_rfl, Category.comp_id, modPowLegM, modPowLegN,
    Category.assoc] at hrel ⊢
  rw [reassoc_of% hM, reassoc_of% hN, hrel]

end RelEmbed

/-! ## Whiskered coequalizers of the module power

The two-stage descent needs the module-power coequalizer to remain
a colimit after whiskering on either side; this is exactly the
preservation of parallel-pair colimits by `tensorLeft`/`tensorRight`,
taken as instance parameters.
-/

section WhiskerColimit

/-- Whiskering the module-power coequalizer on the left yields a
colimit cofork. -/
noncomputable def modPowWhiskerLeftIsColimit
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (P : D) (n : ℕ) :
    IsColimit (Cofork.ofπ (P ◁ modPowπ A X n)
      (by rw [← MonoidalCategory.whiskerLeft_comp, modPow_condition,
        MonoidalCategory.whiskerLeft_comp]) :
      Cofork (P ◁ modPowLegFst A X n) (P ◁ modPowLegSnd A X n)) :=
  isColimitOfHasCoequalizerOfPreservesColimit (tensorLeft P) _ _

/-- Morphisms out of a left-whiskered module power are determined
by their composite with the whiskered projection. -/
theorem modPow_whiskerLeft_hom_ext
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (P : D) (n : ℕ) {Z : D}
    {k l : P ⊗ modPow A X n ⟶ Z}
    (h : (P ◁ modPowπ A X n) ≫ k = (P ◁ modPowπ A X n) ≫ l) :
    k = l :=
  Cofork.IsColimit.hom_ext (modPowWhiskerLeftIsColimit A X P n) h

/-- Descend a morphism along the left-whiskered projection. -/
noncomputable def modPowWhiskerLeftDesc
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (P : D) (n : ℕ) {Z : D}
    (k : P ⊗ tensorPow D X n ⟶ Z)
    (h : (P ◁ modPowLegFst A X n) ≫ k =
      (P ◁ modPowLegSnd A X n) ≫ k) :
    P ⊗ modPow A X n ⟶ Z :=
  Cofork.IsColimit.desc (modPowWhiskerLeftIsColimit A X P n) k h

/-- The left-whiskered descent factors through the whiskered
projection. -/
@[reassoc (attr := simp)]
theorem modPowπ_whiskerLeft_desc
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (P : D) (n : ℕ) {Z : D}
    (k : P ⊗ tensorPow D X n ⟶ Z)
    (h : (P ◁ modPowLegFst A X n) ≫ k =
      (P ◁ modPowLegSnd A X n) ≫ k) :
    (P ◁ modPowπ A X n) ≫ modPowWhiskerLeftDesc A X P n k h = k :=
  Cofork.IsColimit.π_desc' (modPowWhiskerLeftIsColimit A X P n) k h

/-- A doubly whiskered projection is still a colimit cofork. -/
noncomputable def modPowWhiskerRightLeftIsColimit
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) (W P : D) :
    IsColimit (Cofork.ofπ (P ◁ (modPowπ A X n ▷ W))
      (by rw [← MonoidalCategory.whiskerLeft_comp,
        ← MonoidalCategory.comp_whiskerRight, modPow_condition,
        MonoidalCategory.comp_whiskerRight,
        MonoidalCategory.whiskerLeft_comp]) :
      Cofork (P ◁ (modPowLegFst A X n ▷ W))
        (P ◁ (modPowLegSnd A X n ▷ W))) :=
  isColimitCoforkMapOfIsColimit (tensorLeft P) _
    (modPowWhiskerRightIsColimit A X n W)

/-- The left-whiskered projection is an epimorphism. -/
instance epi_whiskerLeft_modPowπ
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (P : D) (n : ℕ) :
    Epi (P ◁ modPowπ A X n) :=
  epi_of_isColimit_cofork (modPowWhiskerLeftIsColimit A X P n)

/-- The doubly whiskered projection is an epimorphism. -/
instance epi_whiskerLeft_modPowπ_whiskerRight
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) (W P : D) :
    Epi (P ◁ (modPowπ A X n ▷ W)) :=
  epi_of_isColimit_cofork
    (modPowWhiskerRightLeftIsColimit A X n W P)

/-- Morphisms out of a tensor product of module powers are
determined by their composite with the tensored projections. -/
theorem modPowTensor_hom_ext
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (m n : ℕ) {Z : D}
    {k l : modPow A X m ⊗ modPow A X n ⟶ Z}
    (h : (modPowπ A X m ⊗ₘ modPowπ A X n) ≫ k =
      (modPowπ A X m ⊗ₘ modPowπ A X n) ≫ l) : k = l := by
  apply modPow_whiskerLeft_hom_ext A X (modPow A X m) n
  apply modPow_whiskerRight_hom_ext A X m (tensorPow D X n)
  simpa only [MonoidalCategory.tensorHom_def, Category.assoc] using h

end WhiskerColimit

/-! ## The raw multiplication -/

section MulDesc

/-- The first assembled leg as a sum over the slots. -/
private theorem modPowLegFst_eq_sum
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
private theorem modPowLegSnd_eq_sum
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

/-- A slot-wise condition assembles over the right-whiskered legs. -/
private theorem legs_whiskerRight_cond
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D]
    {m : ℕ} (n : ℕ) {Z : D}
    (k : tensorPow D X m ⊗ tensorPow D X n ⟶ Z)
    (h : ∀ a b (hab : a + 2 + b = m),
      ((modPowLegM A X a b ≫ powCast X hab) ▷ tensorPow D X n) ≫ k =
        ((modPowLegN A X a b ≫ powCast X hab) ▷ tensorPow D X n) ≫ k) :
    (modPowLegFst A X m ▷ tensorPow D X n) ≫ k =
      (modPowLegSnd A X m ▷ tensorPow D X n) ≫ k := by
  rw [modPowLegFst_eq_sum, modPowLegSnd_eq_sum,
    sum_whiskerRight, sum_whiskerRight,
    Preadditive.sum_comp, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := h i.val (m - 2 - i.val) (slot_decomp i)
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
    at hi ⊢
  rw [hi]

/-- A slot-wise condition assembles over the left-whiskered legs. -/
private theorem legs_whiskerLeft_cond
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D]
    (m : ℕ) {n : ℕ} {Z : D}
    (k : tensorPow D X m ⊗ tensorPow D X n ⟶ Z)
    (h : ∀ a b (hab : a + 2 + b = n),
      (tensorPow D X m ◁ (modPowLegM A X a b ≫ powCast X hab)) ≫ k =
        (tensorPow D X m ◁ (modPowLegN A X a b ≫ powCast X hab)) ≫ k) :
    (tensorPow D X m ◁ modPowLegFst A X n) ≫ k =
      (tensorPow D X m ◁ modPowLegSnd A X n) ≫ k := by
  rw [modPowLegFst_eq_sum, modPowLegSnd_eq_sum,
    whiskerLeft_sum, whiskerLeft_sum,
    Preadditive.sum_comp, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := h i.val (n - 2 - i.val) (slot_decomp i)
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    at hi ⊢
  rw [hi]

/-- The first stage of the multiplication: the concatenation
descends through the left factor against an ambient right factor. -/
noncomputable def modPowMulStage
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [MonoidalPreadditive D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (m n : ℕ) :
    modPow A X m ⊗ tensorPow D X n ⟶ modPow A X (m + n) :=
  modPowWhiskerRightDesc A X m (tensorPow D X n)
    ((tensorPowConcat X m n).hom ≫ modPowπ A X (m + n))
    (legs_whiskerRight_cond A X n _
      (fun a b hab => modPowMul_rel_fst A X n a b hab))

/-- Defining equation of the first stage. -/
@[reassoc (attr := simp)]
theorem modPowπ_whiskerRight_mulStage
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [MonoidalPreadditive D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (m n : ℕ) :
    (modPowπ A X m ▷ tensorPow D X n) ≫ modPowMulStage A X m n =
      (tensorPowConcat X m n).hom ≫ modPowπ A X (m + n) :=
  modPowπ_whiskerRight_desc A X m (tensorPow D X n) _ _

/-- The first stage coequalizes the left-whiskered legs of the
right factor. -/
theorem modPowMulStage_cond
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [MonoidalPreadditive D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (m n : ℕ) :
    (modPow A X m ◁ modPowLegFst A X n) ≫ modPowMulStage A X m n =
      (modPow A X m ◁ modPowLegSnd A X n) ≫ modPowMulStage A X m n := by
  apply modPow_whiskerRight_hom_ext A X m (modPowSrc A X n)
  rw [← MonoidalCategory.whisker_exchange_assoc,
    ← MonoidalCategory.whisker_exchange_assoc,
    modPowπ_whiskerRight_mulStage]
  exact legs_whiskerLeft_cond A X m _
    (fun a b hab => modPowMul_rel_snd A X m a b hab)

/-- **The raw multiplication** on module powers, descended from the
concatenation of the ambient tensor powers in two stages. -/
noncomputable def modPowMul
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [MonoidalPreadditive D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (m n : ℕ) :
    modPow A X m ⊗ modPow A X n ⟶ modPow A X (m + n) :=
  modPowWhiskerLeftDesc A X (modPow A X m) n (modPowMulStage A X m n)
    (modPowMulStage_cond A X m n)

/-- The second-stage defining equation. -/
@[reassoc (attr := simp)]
theorem modPow_whiskerLeft_modPowMul
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [MonoidalPreadditive D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (m n : ℕ) :
    (modPow A X m ◁ modPowπ A X n) ≫ modPowMul A X m n =
      modPowMulStage A X m n :=
  modPowπ_whiskerLeft_desc A X (modPow A X m) n _ _

/-- **Defining equation of the raw multiplication**: on the ambient
tensor powers it is the concatenation followed by the projection. -/
@[reassoc]
theorem modPowπ_tensor_modPowMul
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [MonoidalPreadditive D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (m n : ℕ) :
    (modPowπ A X m ⊗ₘ modPowπ A X n) ≫ modPowMul A X m n =
      (tensorPowConcat X m n).hom ≫ modPowπ A X (m + n) := by
  rw [MonoidalCategory.tensorHom_def, Category.assoc,
    modPow_whiskerLeft_modPowMul, modPowπ_whiskerRight_mulStage]

end MulDesc

/-! ## Bilinear glue for the algebra intertwining -/

section LinearGlue

/-- Intertwining across `T` is closed under sums in the second
factor. -/
private theorem tensor_add_glue
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D]
    {P Q R : D} {T : P ⊗ Q ⟶ R}
    {u v : R ⟶ R} {f : P ⟶ P} {g h : Q ⟶ Q}
    (hu : (f ⊗ₘ g) ≫ T = T ≫ u) (hv : (f ⊗ₘ h) ≫ T = T ≫ v) :
    (f ⊗ₘ (g + h)) ≫ T = T ≫ (u + v) := by
  rw [MonoidalPreadditive.tensor_add, Preadditive.add_comp,
    Preadditive.comp_add, hu, hv]

/-- Intertwining across `T` is closed under sums in the first
factor. -/
private theorem add_tensor_glue
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D]
    {P Q R : D} {T : P ⊗ Q ⟶ R}
    {u v : R ⟶ R} {f g : P ⟶ P} {h : Q ⟶ Q}
    (hu : (f ⊗ₘ h) ≫ T = T ≫ u) (hv : (g ⊗ₘ h) ≫ T = T ≫ v) :
    ((f + g) ⊗ₘ h) ≫ T = T ≫ (u + v) := by
  rw [MonoidalPreadditive.add_tensor, Preadditive.add_comp,
    Preadditive.comp_add, hu, hv]

/-- The tensor product of morphisms is homogeneous in the second
factor. -/
private theorem tensorHom_smul
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [Linear ℂ D] [MonoidalLinear ℂ D]
    {P Q R S : D} (f : P ⟶ Q) (r : ℂ)
    (g : R ⟶ S) : f ⊗ₘ (r • g) = r • (f ⊗ₘ g) := by
  rw [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_def,
    MonoidalLinear.whiskerLeft_smul, Linear.comp_smul]

/-- The tensor product of morphisms is homogeneous in the first
factor. -/
private theorem smul_tensorHom
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [Linear ℂ D] [MonoidalLinear ℂ D]
    {P Q R S : D} (r : ℂ) (f : P ⟶ Q)
    (g : R ⟶ S) : (r • f) ⊗ₘ g = r • (f ⊗ₘ g) := by
  rw [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_def,
    MonoidalLinear.smul_whiskerRight, Linear.smul_comp]

/-- Intertwining across `T` is closed under scalars in the second
factor. -/
private theorem tensor_smul_glue
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [Linear ℂ D] [MonoidalLinear ℂ D]
    {P Q R : D} {T : P ⊗ Q ⟶ R}
    {u : R ⟶ R} {f : P ⟶ P} {g : Q ⟶ Q} (r : ℂ)
    (h : (f ⊗ₘ g) ≫ T = T ≫ u) :
    (f ⊗ₘ (r • g)) ≫ T = T ≫ (r • u) := by
  rw [tensorHom_smul, Linear.smul_comp, Linear.comp_smul, h]

/-- Intertwining across `T` is closed under scalars in the first
factor. -/
private theorem smul_tensor_glue
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [Linear ℂ D] [MonoidalLinear ℂ D]
    {P Q R : D} {T : P ⊗ Q ⟶ R}
    {u : R ⟶ R} {f : P ⟶ P} {g : Q ⟶ Q} (r : ℂ)
    (h : (f ⊗ₘ g) ≫ T = T ≫ u) :
    ((r • f) ⊗ₘ g) ≫ T = T ≫ (r • u) := by
  rw [smul_tensorHom, Linear.smul_comp, Linear.comp_smul, h]

end LinearGlue

/-! ## Equivariance of the raw multiplication -/

section Equivariance

/-- **Equivariance**: the raw multiplication intertwines the pair
of permutation actions with the block-embedded action. -/
theorem modPowMul_perm
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [MonoidalPreadditive D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (m n : ℕ) (σ : Equiv.Perm (Fin m))
    (τ : Equiv.Perm (Fin n)) :
    (modPowPerm (A := A) (X := X) m σ ⊗ₘ
        modPowPerm (A := A) (X := X) n τ) ≫ modPowMul A X m n =
      modPowMul A X m n ≫
        modPowPerm (A := A) (X := X) (m + n) (blockEmbed σ τ) := by
  apply modPowTensor_hom_ext A X m n
  conv_lhs => rw [← Category.assoc, tensorHom_comp_tensorHom,
    modPowπ_perm, modPowπ_perm, ← tensorHom_comp_tensorHom,
    Category.assoc, modPowπ_tensor_modPowMul, ← Category.assoc,
    ← tensorPowConcat_permMor, Category.assoc]
  conv_rhs => rw [← Category.assoc, modPowπ_tensor_modPowMul,
    Category.assoc, modPowπ_perm]

/-- **Linear equivariance**: the raw multiplication intertwines the
group-algebra actions with the block embedding of group algebras,
by bilinear extension of the permutation case. -/
theorem modPowMul_alg
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [MonoidalPreadditive D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    (m n : ℕ) (x : SymGroupAlgebra m)
    (y : SymGroupAlgebra n) :
    ((modPowAlg A X m x : End _) ⊗ₘ (modPowAlg A X n y : End _)) ≫
        modPowMul A X m n =
      modPowMul A X m n ≫ modPowAlg A X (m + n) (blockAlgEmbed x y) := by
  induction x using MonoidAlgebra.induction_on with
  | of σ =>
    induction y using MonoidAlgebra.induction_on with
    | of τ =>
      rw [show (MonoidAlgebra.of ℂ (Equiv.Perm (Fin m))) σ =
          MonoidAlgebra.single σ (1 : ℂ) from rfl,
        show (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n))) τ =
          MonoidAlgebra.single τ (1 : ℂ) from rfl,
        blockAlgEmbed_single, one_mul, modPowAlg_single,
        modPowAlg_single, modPowAlg_single]
      exact modPowMul_perm A X m n σ τ
    | add y₁ y₂ hy₁ hy₂ =>
      rw [blockAlgEmbed_add_snd, map_add, map_add]
      exact tensor_add_glue hy₁ hy₂
    | smul r y' hy =>
      rw [blockAlgEmbed_smul_snd, map_smul, map_smul]
      exact tensor_smul_glue r hy
  | add x₁ x₂ hx₁ hx₂ =>
    rw [blockAlgEmbed_add_fst, map_add, map_add]
    exact add_tensor_glue hx₁ hx₂
  | smul r x' hx =>
    rw [blockAlgEmbed_smul_fst, map_smul, map_smul]
    exact smul_tensor_glue r hx

end Equivariance

/-! ## Absorption of embedded symmetrisers -/

section Absorption

/-- The full symmetriser absorbs the image of any mass-one average:
pushing a symmetriser forward along any group homomorphism into the
larger symmetric group leaves the larger symmetriser fixed. -/
theorem symmetriser_mul_mapDomain {k N : ℕ}
    (f : Equiv.Perm (Fin k) →* Equiv.Perm (Fin N)) :
    symmetriser N *
        MonoidAlgebra.mapDomainAlgHom ℂ ℂ f (symmetriser k) =
      symmetriser N := by
  have hmap : MonoidAlgebra.mapDomainAlgHom ℂ ℂ f (symmetriser k) =
      ((k.factorial : ℂ))⁻¹ •
        ∑ σ : Equiv.Perm (Fin k),
          MonoidAlgebra.single (f σ) (1 : ℂ) := by
    rw [symmetriser, map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    change MonoidAlgebra.mapDomain _ _ = _
    exact MonoidAlgebra.mapDomain_single
  rw [hmap, mul_smul_comm, Finset.mul_sum]
  simp only [symmetriser_mul_single]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀
      (by exact_mod_cast k.factorial_ne_zero : (k.factorial : ℂ) ≠ 0),
    one_smul]

/-- **The coset identity**: the block embedding of the two
symmetrisers is absorbed by the full symmetriser. -/
theorem symmetriser_mul_blockAlgEmbed (m n : ℕ) :
    symmetriser (m + n) *
        blockAlgEmbed (symmetriser m) (symmetriser n) =
      symmetriser (m + n) := by
  rw [blockAlgEmbed, ← mul_assoc, symmetriser_mul_mapDomain,
    symmetriser_mul_mapDomain]

/-- The block embedding of a one-sided unit is one-sided. -/
theorem blockAlgEmbed_one_left {m n : ℕ} (y : SymGroupAlgebra n) :
    blockAlgEmbed (1 : SymGroupAlgebra m) y =
      MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockEmbedSndHom m n) y := by
  rw [blockAlgEmbed, map_one, one_mul]

/-- The block embedding of a one-sided unit is one-sided. -/
theorem blockAlgEmbed_one_right {m n : ℕ} (x : SymGroupAlgebra m) :
    blockAlgEmbed x (1 : SymGroupAlgebra n) =
      MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockEmbedFstHom m n) x := by
  rw [blockAlgEmbed, map_one, mul_one]

/-- Any element absorbed by the symmetriser acts trivially after
the symmetric-power projection. -/
theorem modPowAlg_absorb
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    {N : ℕ} (z : SymGroupAlgebra N)
    (hz : symmetriser N * z = symmetriser N) :
    (modPowAlg A X N z : End _) ≫ symPowπ A X N = symPowπ A X N := by
  have h2 : (modPowAlg A X N z : End _) ≫ symPowIdem A X N =
      symPowIdem A X N := by
    have h3 := congrArg (modPowAlg A X N) hz
    rw [map_mul] at h3
    exact h3
  conv_lhs => rw [← symPowIdem_π A X N, ← Category.assoc, h2]
  rw [symPowIdem_π]

end Absorption

/-! ## The multiplication on symmetric powers -/

section SymMulDef

/-- **The multiplication on symmetric powers**, through the
sections and the raw multiplication. -/
noncomputable def symMul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [MonoidalPreadditive D] [Linear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (m n : ℕ) :
    symPow A X m ⊗ symPow A X n ⟶ symPow A X (m + n) :=
  (symPowσ A X m ⊗ₘ symPowσ A X n) ≫ modPowMul A X m n ≫
    symPowπ A X (m + n)

/-- **Defining equation of the symmetric multiplication**: the two
projections carry the raw multiplication to `symMul`.  The two
factor symmetrisers introduced by the sections are absorbed by the
full symmetriser through equivariance and the coset identity. -/
@[reassoc]
theorem symPowπ_tensor_symMul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (m n : ℕ) :
    (symPowπ A X m ⊗ₘ symPowπ A X n) ≫ symMul A X m n =
      modPowMul A X m n ≫ symPowπ A X (m + n) := by
  have h1 : (symPowIdem A X m ⊗ₘ symPowIdem A X n) ≫
      modPowMul A X m n =
      modPowMul A X m n ≫ modPowAlg A X (m + n)
        (blockAlgEmbed (symmetriser m) (symmetriser n)) :=
    modPowMul_alg A X m n (symmetriser m) (symmetriser n)
  rw [symMul, ← Category.assoc, tensorHom_comp_tensorHom,
    symPowπ_symPowσ, symPowπ_symPowσ, reassoc_of% h1,
    modPowAlg_absorb A X _ (symmetriser_mul_blockAlgEmbed m n)]

/-- Morphisms out of a tensor product of symmetric powers are
determined by their composites with the tensored projections. -/
theorem symPowTensor_hom_ext
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (m n : ℕ) {Z : D}
    {k l : symPow A X m ⊗ symPow A X n ⟶ Z}
    (h : (symPowπ A X m ⊗ₘ symPowπ A X n) ≫ k =
      (symPowπ A X m ⊗ₘ symPowπ A X n) ≫ l) : k = l := by
  have hsec : (symPowσ A X m ⊗ₘ symPowσ A X n) ≫
      (symPowπ A X m ⊗ₘ symPowπ A X n) = 𝟙 _ := by
    rw [tensorHom_comp_tensorHom, symPowσ_symPowπ, symPowσ_symPowπ,
      tensorHom_id, MonoidalCategory.id_whiskerRight]
  calc k = ((symPowσ A X m ⊗ₘ symPowσ A X n) ≫
        (symPowπ A X m ⊗ₘ symPowπ A X n)) ≫ k := by
        rw [hsec, Category.id_comp]
    _ = ((symPowσ A X m ⊗ₘ symPowσ A X n) ≫
        (symPowπ A X m ⊗ₘ symPowπ A X n)) ≫ l := by
        rw [Category.assoc, Category.assoc, h]
    _ = l := by rw [hsec, Category.id_comp]

end SymMulDef

/-! ## The empty symmetric power -/

section ZeroPow

/-- At arity zero the symmetriser is the unit of the group
algebra. -/
theorem symmetriser_zero : symmetriser 0 = 1 := by
  let : Unique (Equiv.Perm (Fin 0)) :=
    ⟨⟨1⟩, fun σ => Equiv.ext fun x => x.elim0⟩
  rw [symmetriser, Fintype.sum_unique]
  change ((Nat.factorial 0 : ℂ))⁻¹ •
    MonoidAlgebra.single 1 (1 : ℂ) = 1
  rw [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
  exact MonoidAlgebra.one_def.symm

/-- At arity zero the symmetriser acts as the identity. -/
theorem symPowIdem_zero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] : symPowIdem A X 0 = 𝟙 (modPow A X 0) := by
  rw [symPowIdem, symmetriser_zero, map_one]
  rfl

/-- **The empty symmetric power is the unit object.** -/
noncomputable def symPowZero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] : symPow A X 0 ≅ 𝟙_ D where
  hom := symPowσ A X 0 ≫ (modPowZero A X).hom
  inv := (modPowZero A X).inv ≫ symPowπ A X 0
  hom_inv_id := by
    rw [Category.assoc, Iso.hom_inv_id_assoc, symPowσ_symPowπ]
  inv_hom_id := by
    rw [Category.assoc, symPowπ_symPowσ_assoc, symPowIdem_zero,
      Category.id_comp, Iso.inv_hom_id]

/-- At arity one the symmetriser is the unit of the group
algebra. -/
theorem symmetriser_one : symmetriser 1 = 1 := by
  let : Unique (Equiv.Perm (Fin 1)) :=
    ⟨⟨1⟩, fun σ => Equiv.ext fun x => Subsingleton.elim _ _⟩
  rw [symmetriser, Fintype.sum_unique]
  change ((Nat.factorial 1 : ℂ))⁻¹ •
    MonoidAlgebra.single 1 (1 : ℂ) = 1
  rw [Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
  exact MonoidAlgebra.one_def.symm

/-- At arity one the symmetriser acts as the identity. -/
theorem symPowIdem_one
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] : symPowIdem A X 1 = 𝟙 (modPow A X 1) := by
  rw [symPowIdem, symmetriser_one, map_one]
  rfl

/-- **The singleton symmetric power is the module.** -/
noncomputable def symPowOne
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] : symPow A X 1 ≅ X where
  hom := symPowσ A X 1 ≫ (modPowOne A X).hom
  inv := (modPowOne A X).inv ≫ symPowπ A X 1
  hom_inv_id := by
    rw [Category.assoc, Iso.hom_inv_id_assoc, symPowσ_symPowπ]
  inv_hom_id := by
    rw [Category.assoc, symPowπ_symPowσ_assoc, symPowIdem_one,
      Category.id_comp, Iso.inv_hom_id]

/-- Transport of a symmetric power along an equality of arities. -/
noncomputable def symPowCast
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    {m n : ℕ} (h : m = n) :
    symPow A X m ⟶ symPow A X n :=
  eqToHom (congrArg (symPow A X) h)

@[simp]
theorem symPowCast_rfl
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) :
    symPowCast A X (rfl : n = n) = 𝟙 _ := rfl

/-- The projection intertwines the module- and symmetric-power
transports. -/
@[reassoc]
theorem symPowπ_cast
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    {m n : ℕ} (h : m = n) :
    symPowπ A X m ≫ symPowCast A X h =
      modPowCast A X h ≫ symPowπ A X n := by
  subst h
  simp [symPowCast]

/-- Morphisms out of a left-whiskered symmetric power are
determined by the whiskered projection, which is split epi. -/
theorem symPow_whiskerLeft_hom_ext
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (P : D) (n : ℕ) {Z : D}
    {k l : P ⊗ symPow A X n ⟶ Z}
    (h : (P ◁ symPowπ A X n) ≫ k = (P ◁ symPowπ A X n) ≫ l) :
    k = l := by
  have hsec : (P ◁ symPowσ A X n) ≫ (P ◁ symPowπ A X n) = 𝟙 _ := by
    rw [← MonoidalCategory.whiskerLeft_comp, symPowσ_symPowπ,
      MonoidalCategory.whiskerLeft_id]
  calc k = ((P ◁ symPowσ A X n) ≫ (P ◁ symPowπ A X n)) ≫ k := by
        rw [hsec, Category.id_comp]
    _ = ((P ◁ symPowσ A X n) ≫ (P ◁ symPowπ A X n)) ≫ l := by
        rw [Category.assoc, Category.assoc, h]
    _ = l := by rw [hsec, Category.id_comp]

/-- Morphisms out of a right-whiskered symmetric power are
determined by the whiskered projection, which is split epi. -/
theorem symPow_whiskerRight_hom_ext
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) (W : D) {Z : D}
    {k l : symPow A X n ⊗ W ⟶ Z}
    (h : (symPowπ A X n ▷ W) ≫ k = (symPowπ A X n ▷ W) ≫ l) :
    k = l := by
  have hsec : (symPowσ A X n ▷ W) ≫ (symPowπ A X n ▷ W) = 𝟙 _ := by
    rw [← MonoidalCategory.comp_whiskerRight, symPowσ_symPowπ,
      MonoidalCategory.id_whiskerRight]
  calc k = ((symPowσ A X n ▷ W) ≫ (symPowπ A X n ▷ W)) ≫ k := by
        rw [hsec, Category.id_comp]
    _ = ((symPowσ A X n ▷ W) ≫ (symPowπ A X n ▷ W)) ≫ l := by
        rw [Category.assoc, Category.assoc, h]
    _ = l := by rw [hsec, Category.id_comp]

end ZeroPow

/-! ## Unit laws -/

section UnitLaws

/-- **Left unit law at the module-power level**: multiplying by the
empty power is the left unitor, up to the arity transport. -/
theorem modPowMul_zero_left
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [MonoidalPreadditive D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) :
    ((modPowZero A X).inv ▷ modPow A X n) ≫ modPowMul A X 0 n =
      (λ_ (modPow A X n)).hom ≫
        modPowCast A X (by omega : n = 0 + n) := by
  apply modPow_whiskerLeft_hom_ext A X (𝟙_ D) n
  have h0 : (tensorPowConcat X 0 n).hom ≫ modPowπ A X (0 + n) =
      ((λ_ (tensorPow D X n)).hom ≫
        powCast X (by omega : n = 0 + n)) ≫ modPowπ A X (0 + n) :=
    congrArg (· ≫ modPowπ A X (0 + n)) (tensorPowConcat_zero_left X n)
  have hkey : ((modPowZero A X).inv ▷ tensorPow D X n) ≫
      modPowMulStage A X 0 n =
        (λ_ (tensorPow D X n)).hom ≫
          powCast X (by omega : n = 0 + n) ≫ modPowπ A X (0 + n) :=
    (modPowπ_whiskerRight_mulStage A X 0 n).trans
      (h0.trans (Category.assoc _ _ _))
  conv_lhs => rw [MonoidalCategory.whisker_exchange_assoc,
    modPow_whiskerLeft_modPowMul, hkey]
  conv_rhs => rw [MonoidalCategory.leftUnitor_naturality_assoc,
    modPowπ_cast]

/-- **Right unit law at the module-power level**: multiplying by
the empty power is the right unitor, up to the arity transport. -/
theorem modPowMul_zero_right
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [MonoidalPreadditive D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) :
    (modPow A X n ◁ (modPowZero A X).inv) ≫ modPowMul A X n 0 =
      (ρ_ (modPow A X n)).hom ≫
        modPowCast A X (by omega : n = n + 0) := by
  apply modPow_whiskerRight_hom_ext A X n (𝟙_ D)
  have hc : powCast X (by omega : n = n + 0) = 𝟙 _ := rfl
  have h2 : (tensorPow D X n ◁ modPowπ A X 0) ≫
      (modPowπ A X n ▷ modPow A X 0) ≫ modPowMul A X n 0 =
        (modPowπ A X n ⊗ₘ modPowπ A X 0) ≫ modPowMul A X n 0 := by
    rw [← Category.assoc, ← MonoidalCategory.tensorHom_def']
  have h0 : (tensorPowConcat X n 0).hom ≫ modPowπ A X (n + 0) =
      (ρ_ (tensorPow D X n)).hom ≫ modPowπ A X (n + 0) :=
    congrArg (· ≫ modPowπ A X (n + 0))
      (congrArg Iso.hom (tensorPowConcat_zero X n))
  have hkey : (tensorPow D X n ◁ (modPowZero A X).inv) ≫
      (modPowπ A X n ▷ modPow A X 0) ≫ modPowMul A X n 0 =
        (ρ_ (tensorPow D X n)).hom ≫ modPowπ A X (n + 0) :=
    h2.trans ((modPowπ_tensor_modPowMul A X n 0).trans h0)
  conv_lhs => rw [← MonoidalCategory.whisker_exchange_assoc, hkey]
  conv_rhs => rw [MonoidalCategory.rightUnitor_naturality_assoc,
    modPowπ_cast, hc, Category.id_comp]

end UnitLaws

/-! ## Unit laws for the symmetric multiplication -/

section SymUnitLaws

/-- The unit section of the empty symmetric power lifts to the
empty module power. -/
theorem symPowZero_inv_symPowσ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] :
    (symPowZero A X).inv ≫ symPowσ A X 0 = (modPowZero A X).inv := by
  change ((modPowZero A X).inv ≫ symPowπ A X 0) ≫ symPowσ A X 0 =
    (modPowZero A X).inv
  rw [Category.assoc, symPowπ_symPowσ, symPowIdem_zero,
    Category.comp_id]

/-- **Left unit law**: multiplying by the empty symmetric power is
the left unitor, up to the arity transport. -/
theorem symMul_zero_left
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) :
    ((symPowZero A X).inv ▷ symPow A X n) ≫ symMul A X 0 n =
      (λ_ (symPow A X n)).hom ≫
        symPowCast A X (by omega : n = 0 + n) := by
  apply symPow_whiskerLeft_hom_ext A X (𝟙_ D) n
  have hA : (symPow A X 0 ◁ symPowπ A X n) ≫ symMul A X 0 n =
      (symPowσ A X 0 ⊗ₘ symPowIdem A X n) ≫ modPowMul A X 0 n ≫
        symPowπ A X (0 + n) := by
    rw [symMul, ← Category.assoc, ← MonoidalCategory.id_tensorHom,
      tensorHom_comp_tensorHom, Category.id_comp, symPowπ_symPowσ]
  have hsplit : (modPowZero A X).inv ⊗ₘ symPowIdem A X n =
      ((modPowZero A X).inv ⊗ₘ 𝟙 (modPow A X n)) ≫
        (𝟙 (modPow A X 0) ⊗ₘ symPowIdem A X n) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  have hD : (𝟙 (modPow A X 0) ⊗ₘ symPowIdem A X n) ≫
      modPowMul A X 0 n =
        modPowMul A X 0 n ≫
          modPowAlg A X (0 + n) (blockAlgEmbed 1 (symmetriser n)) := by
    have h := modPowMul_alg A X 0 n 1 (symmetriser n)
    rwa [map_one] at h
  have hE : modPowAlg A X (0 + n)
        (blockAlgEmbed 1 (symmetriser n)) ≫ symPowπ A X (0 + n) =
      symPowπ A X (0 + n) :=
    modPowAlg_absorb A X _
      (by rw [blockAlgEmbed_one_left, symmetriser_mul_mapDomain])
  conv_lhs => rw [MonoidalCategory.whisker_exchange_assoc, hA,
    ← Category.assoc, ← MonoidalCategory.tensorHom_id,
    tensorHom_comp_tensorHom, Category.id_comp,
    symPowZero_inv_symPowσ, hsplit, Category.assoc,
    reassoc_of% hD, hE, MonoidalCategory.tensorHom_id,
    reassoc_of% (modPowMul_zero_left A X n)]
  conv_rhs => rw [MonoidalCategory.leftUnitor_naturality_assoc,
    symPowπ_cast]

end SymUnitLaws
/-! ## Associativity -/

section WhiskerConj

/-- A doubly right-whiskered morphism, conjugated to a single
whisker. -/
private theorem whiskerRight_whiskerRight_conj
    [Category.{v} D] [MonoidalCategory D]
    {P Q : D}
    (f : P ⟶ Q) (Y Z : D) :
    (f ▷ Y) ▷ Z =
      (α_ P Y Z).hom ≫ (f ▷ (Y ⊗ Z)) ≫ (α_ Q Y Z).inv := by
  rw [← MonoidalCategory.associator_naturality_left_assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- A left-then-right whiskered morphism, conjugated to nested
whiskers. -/
private theorem whiskerLeft_whiskerRight_conj
    [Category.{v} D] [MonoidalCategory D]
    (P : D) {Q R : D}
    (g : Q ⟶ R) (Z : D) :
    (P ◁ g) ▷ Z =
      (α_ P Q Z).hom ≫ (P ◁ (g ▷ Z)) ≫ (α_ P R Z).inv := by
  rw [← MonoidalCategory.associator_naturality_middle_assoc,
    Iso.hom_inv_id, Category.comp_id]

end WhiskerConj

section AssocLaw

instance [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (m n : ℕ) : Epi (modPowπ A X m ⊗ₘ modPowπ A X n) := by
  rw [MonoidalCategory.tensorHom_def]
  exact epi_comp _ _

instance [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (m n r : ℕ) :
    Epi ((modPowπ A X m ⊗ₘ modPowπ A X n) ▷ tensorPow D X r) := by
  rw [MonoidalCategory.tensorHom_def,
    MonoidalCategory.comp_whiskerRight,
    whiskerRight_whiskerRight_conj, whiskerLeft_whiskerRight_conj]
  infer_instance

/-- Morphisms out of a triple tensor product of module powers are
determined by their composites with the tensored projections. -/
theorem modPowTriple_hom_ext
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (m n r : ℕ) {Z : D}
    {k l : (modPow A X m ⊗ modPow A X n) ⊗ modPow A X r ⟶ Z}
    (h : ((modPowπ A X m ⊗ₘ modPowπ A X n) ⊗ₘ modPowπ A X r) ≫ k =
      ((modPowπ A X m ⊗ₘ modPowπ A X n) ⊗ₘ modPowπ A X r) ≫ l) :
    k = l := by
  apply modPow_whiskerLeft_hom_ext A X
    (modPow A X m ⊗ modPow A X n) r
  refine (cancel_epi
    ((modPowπ A X m ⊗ₘ modPowπ A X n) ▷ tensorPow D X r)).mp ?_
  rw [← Category.assoc, ← Category.assoc,
    ← MonoidalCategory.tensorHom_def]
  simpa only [Category.assoc] using h

/-- **Associativity of the raw multiplication**, up to the arity
transport of `m + (n + r) = m + n + r`. -/
theorem modPowMul_assoc
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [MonoidalPreadditive D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (m n r : ℕ) :
    (modPowMul A X m n ▷ modPow A X r) ≫ modPowMul A X (m + n) r =
      (α_ (modPow A X m) (modPow A X n) (modPow A X r)).hom ≫
        (modPow A X m ◁ modPowMul A X n r) ≫
        modPowMul A X m (n + r) ≫
        modPowCast A X (by omega : m + (n + r) = m + n + r) := by
  apply modPowTriple_hom_ext A X m n r
  have hsplit1 : ((tensorPowConcat X m n).hom ≫ modPowπ A X (m + n))
      ⊗ₘ modPowπ A X r =
      ((tensorPowConcat X m n).hom ⊗ₘ 𝟙 (tensorPow D X r)) ≫
        (modPowπ A X (m + n) ⊗ₘ modPowπ A X r) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  have hsplit2 : modPowπ A X m ⊗ₘ
      ((tensorPowConcat X n r).hom ≫ modPowπ A X (n + r)) =
      (𝟙 (tensorPow D X m) ⊗ₘ (tensorPowConcat X n r).hom) ≫
        (modPowπ A X m ⊗ₘ modPowπ A X (n + r)) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  have hL : (((tensorPowConcat X m n).hom ≫ modPowπ A X (m + n))
      ⊗ₘ modPowπ A X r) ≫ modPowMul A X (m + n) r =
      ((tensorPowConcat X m n).hom ▷ tensorPow D X r) ≫
        (tensorPowConcat X (m + n) r).hom ≫
        modPowπ A X (m + n + r) := by
    rw [hsplit1, Category.assoc, modPowπ_tensor_modPowMul,
      MonoidalCategory.tensorHom_id]
  have hR : (modPowπ A X m ⊗ₘ
      ((tensorPowConcat X n r).hom ≫ modPowπ A X (n + r))) ≫
      modPowMul A X m (n + r) =
      (tensorPow D X m ◁ (tensorPowConcat X n r).hom) ≫
        (tensorPowConcat X m (n + r)).hom ≫
        modPowπ A X (m + (n + r)) := by
    rw [hsplit2, Category.assoc, modPowπ_tensor_modPowMul,
      MonoidalCategory.id_tensorHom]
  conv_lhs => rw [← MonoidalCategory.tensorHom_id,
    tensorHom_comp_tensorHom_assoc, Category.comp_id,
    modPowπ_tensor_modPowMul, hL,
    reassoc_of% (tensorPowConcat_assoc X m n r)]
  conv_rhs => rw [MonoidalCategory.associator_naturality_assoc,
    ← MonoidalCategory.id_tensorHom, tensorHom_comp_tensorHom_assoc,
    Category.comp_id, modPowπ_tensor_modPowMul,
    reassoc_of% hR, modPowπ_cast]

end AssocLaw

/-! ## Associativity of the symmetric multiplication -/

section SymAssocLaw

/-- Morphisms out of a triple tensor product of symmetric powers
are determined by their composites with the tensored projections,
which are jointly split epi. -/
theorem symPowTriple_hom_ext
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (m n r : ℕ) {Z : D}
    {k l : (symPow A X m ⊗ symPow A X n) ⊗ symPow A X r ⟶ Z}
    (h : ((symPowπ A X m ⊗ₘ symPowπ A X n) ⊗ₘ symPowπ A X r) ≫ k =
      ((symPowπ A X m ⊗ₘ symPowπ A X n) ⊗ₘ symPowπ A X r) ≫ l) :
    k = l := by
  have hsec : ((symPowσ A X m ⊗ₘ symPowσ A X n) ⊗ₘ symPowσ A X r) ≫
      ((symPowπ A X m ⊗ₘ symPowπ A X n) ⊗ₘ symPowπ A X r) =
      𝟙 _ := by
    simp only [tensorHom_comp_tensorHom, symPowσ_symPowπ,
      MonoidalCategory.tensorHom_id,
      MonoidalCategory.id_whiskerRight]
  calc k = (((symPowσ A X m ⊗ₘ symPowσ A X n) ⊗ₘ symPowσ A X r) ≫
        ((symPowπ A X m ⊗ₘ symPowπ A X n) ⊗ₘ symPowπ A X r)) ≫ k := by
        rw [hsec, Category.id_comp]
    _ = (((symPowσ A X m ⊗ₘ symPowσ A X n) ⊗ₘ symPowσ A X r) ≫
        ((symPowπ A X m ⊗ₘ symPowπ A X n) ⊗ₘ symPowπ A X r)) ≫ l := by
        rw [Category.assoc, Category.assoc, h]
    _ = l := by rw [hsec, Category.id_comp]

/-- **Associativity of the symmetric multiplication**, up to the
arity transport of `m + (n + r) = m + n + r`. -/
theorem symMul_assoc
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (m n r : ℕ) :
    (symMul A X m n ▷ symPow A X r) ≫ symMul A X (m + n) r =
      (α_ (symPow A X m) (symPow A X n) (symPow A X r)).hom ≫
        (symPow A X m ◁ symMul A X n r) ≫
        symMul A X m (n + r) ≫
        symPowCast A X (by omega : m + (n + r) = m + n + r) := by
  apply symPowTriple_hom_ext A X m n r
  have hsplit1 : (modPowMul A X m n ≫ symPowπ A X (m + n)) ⊗ₘ
      symPowπ A X r =
      (modPowMul A X m n ⊗ₘ 𝟙 (modPow A X r)) ≫
        (symPowπ A X (m + n) ⊗ₘ symPowπ A X r) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  have hsplit2 : symPowπ A X m ⊗ₘ
      (modPowMul A X n r ≫ symPowπ A X (n + r)) =
      (𝟙 (modPow A X m) ⊗ₘ modPowMul A X n r) ≫
        (symPowπ A X m ⊗ₘ symPowπ A X (n + r)) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  have hL : ((modPowMul A X m n ≫ symPowπ A X (m + n)) ⊗ₘ
      symPowπ A X r) ≫ symMul A X (m + n) r =
      (modPowMul A X m n ▷ modPow A X r) ≫
        modPowMul A X (m + n) r ≫ symPowπ A X (m + n + r) := by
    rw [hsplit1, Category.assoc, symPowπ_tensor_symMul,
      MonoidalCategory.tensorHom_id]
  have hR : (symPowπ A X m ⊗ₘ
      (modPowMul A X n r ≫ symPowπ A X (n + r))) ≫
      symMul A X m (n + r) =
      (modPow A X m ◁ modPowMul A X n r) ≫
        modPowMul A X m (n + r) ≫ symPowπ A X (m + (n + r)) := by
    rw [hsplit2, Category.assoc, symPowπ_tensor_symMul,
      MonoidalCategory.id_tensorHom]
  conv_lhs => rw [← MonoidalCategory.tensorHom_id,
    tensorHom_comp_tensorHom_assoc, Category.comp_id,
    symPowπ_tensor_symMul, hL,
    reassoc_of% (modPowMul_assoc A X m n r)]
  conv_rhs => rw [MonoidalCategory.associator_naturality_assoc,
    ← MonoidalCategory.id_tensorHom, tensorHom_comp_tensorHom_assoc,
    Category.comp_id, symPowπ_tensor_symMul,
    reassoc_of% hR, symPowπ_cast]

end SymAssocLaw

/-! ## Commutativity

The braiding of two tensor powers is, through the concatenations, a
permutation action; commutativity of `symMul` then follows because
the symmetriser absorbs every permutation.  The permutation itself
is never computed: each intertwining is established with an
existentially quantified permutation, assembled by the same
recursion as the concatenation. -/

section CommPerm

/-- **The peeled braiding of one factor with a power acts by a
permutation**, assembled by the recursion of the power itself. -/
theorem braiding_one_pow_exists
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (X : D) :
    ∀ n : ℕ,
    ∃ τ : Equiv.Perm (Fin (n + 1)),
      (powPeel X n).hom ≫ (β_ X (tensorPow D X n)).hom =
        permMor X (n + 1) τ
  | 0 => ⟨1, by
      rw [powPeel_zero, permMor_one]
      change ((λ_ X).hom ≫ (ρ_ X).inv) ≫ (β_ X (𝟙_ D)).hom =
        𝟙 (𝟙_ D ⊗ X)
      rw [braiding_tensorUnit_right, Category.assoc,
        Iso.inv_hom_id_assoc, Iso.hom_inv_id]⟩
  | n + 1 => by
    obtain ⟨τ, hn⟩ := braiding_one_pow_exists X n
    refine ⟨topSwap * extPerm τ, ?_⟩
    have hstep1 : (powPeel X (n + 1)).hom ≫
        (β_ X (tensorPow D X (n + 1))).hom =
        (((powPeel X n).hom ▷ X) ≫
          (α_ X (tensorPow D X n) X).hom) ≫
          (β_ X (tensorPow D X n ⊗ X)).hom := rfl
    rw [hstep1, Category.assoc,
      BraidedCategory.braiding_tensor_right_hom,
      Iso.hom_inv_id_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc]
    have s1 : (((powPeel X n).hom ≫
          (β_ X (tensorPow D X n)).hom) ▷ X) ≫
        (α_ (tensorPow D X n) X X).hom ≫
        (tensorPow D X n ◁ (β_ X X).hom) ≫
        (α_ (tensorPow D X n) X X).inv =
        (permMor X (n + 1) τ ▷ X) ≫ swapTop X n := by
      rw [hn]; rfl
    have s2 : (permMor X (n + 1) τ ▷ X) ≫ swapTop X n =
        permMor X (n + 2) (topSwap * extPerm τ) := by
      rw [permMor_mul, permMor_extPerm, permMor_topSwap_eq]
      rfl
    exact s1.trans s2

end CommPerm

/-- The hexagon step of the braiding–concatenation intertwining, at
general objects. -/
private theorem comm_step_aux
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (X : D)
    {Pm Pn Q : D} (c : Pn ⊗ Pm ⟶ Q)
    {w : Pm ⊗ Pn ⟶ Q} (hIH : (β_ Pm Pn).hom ≫ c = w) :
    (β_ (Pm ⊗ X) Pn).hom ≫ (α_ Pn Pm X).inv ≫ (c ▷ X) =
      (α_ Pm X Pn).hom ≫ (Pm ◁ (β_ X Pn).hom) ≫
        (α_ Pm Pn X).inv ≫ (w ▷ X) := by
  rw [BraidedCategory.braiding_tensor_left_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← MonoidalCategory.comp_whiskerRight, hIH]

section CommMain

/-- The head of the commutation step: attaching the peeled factor
to the first block. -/
private theorem comm_head [Category.{v} D] [MonoidalCategory D] (X : D)
    (m n : ℕ) :
    (α_ (tensorPow D X m) X (tensorPow D X n)).hom ≫
        (tensorPow D X m ◁ (powPeel X n).inv) ≫
        (tensorPowConcat X m (n + 1)).hom =
      (tensorPowConcat X (m + 1) n).hom ≫
        powCast X (by omega : m + 1 + n = m + (n + 1)) := by
  have hcanc : (α_ (tensorPow D X m) X (tensorPow D X n)).hom ≫
      powAttach X m n = 𝟙 _ := Iso.hom_inv_id _
  rw [tensorPowConcat_peel X m n,
    ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp,
    reassoc_of% hcanc]
  exact Category.id_comp _

/-- The whiskered braiding expands through the peel. -/
private theorem comm_beta_expand
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (X : D)
    (m n : ℕ) :
    (tensorPow D X m ◁ (powPeel X n).inv) ≫
        (tensorPow D X m ◁
          ((powPeel X n).hom ≫ (β_ X (tensorPow D X n)).hom)) =
      tensorPow D X m ◁ (β_ X (tensorPow D X n)).hom := by
  rw [← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id_assoc]

/-- **The braiding of tensor powers is a permutation across the
concatenations**: for some permutation `σ` of the slots. -/
theorem tensorPowConcat_braiding_exists
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (X : D)
    (n : ℕ) : ∀ m : ℕ,
    ∃ σ : Equiv.Perm (Fin (n + m)),
      (β_ (tensorPow D X m) (tensorPow D X n)).hom ≫
          (tensorPowConcat X n m).hom =
        (tensorPowConcat X m n).hom ≫
          powCast X (by omega : m + n = n + m) ≫
          permMor X (n + m) σ
  | 0 => ⟨1, by
      rw [permMor_one, Category.comp_id, tensorPowConcat_zero,
        tensorPowConcat_zero_left]
      change (β_ (𝟙_ D) (tensorPow D X n)).hom ≫
          (ρ_ (tensorPow D X n)).hom =
        ((λ_ (tensorPow D X n)).hom ≫
            powCast X (by omega : n = 0 + n)) ≫
          powCast X (by omega : 0 + n = n + 0)
      have hc : powCast X (by omega : n = n + 0) = 𝟙 _ := rfl
      rw [Category.assoc, powCast_comp, hc, Category.comp_id,
        braiding_tensorUnit_left, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]⟩
  | m + 1 => by
    obtain ⟨σ, hm⟩ := tensorPowConcat_braiding_exists X n m
    obtain ⟨τ, hτ⟩ := braiding_one_pow_exists X n
    refine ⟨extPerm σ *
      (finCongr (by omega : m + (n + 1) = n + (m + 1))).permCongr
        (blockEmbed 1 τ), ?_⟩
    have g1 : (β_ (tensorPow D X (m + 1)) (tensorPow D X n)).hom ≫
        (tensorPowConcat X n (m + 1)).hom =
        (β_ (tensorPow D X m ⊗ X) (tensorPow D X n)).hom ≫
          (α_ (tensorPow D X n) (tensorPow D X m) X).inv ≫
          ((tensorPowConcat X n m).hom ▷ X) := rfl
    have g2 := comm_step_aux X ((tensorPowConcat X n m).hom) hm
    have g4 : (α_ (tensorPow D X m) (tensorPow D X n) X).inv ≫
        ((tensorPowConcat X m n).hom ▷ X) =
        (tensorPowConcat X m (n + 1)).hom := rfl
    have e3a : (α_ (tensorPow D X m) X (tensorPow D X n)).hom ≫
        (tensorPow D X m ◁ (β_ X (tensorPow D X n)).hom) ≫
        (α_ (tensorPow D X m) (tensorPow D X n) X).inv ≫
        (((tensorPowConcat X m n).hom ≫
          powCast X (by omega : m + n = n + m) ≫
          permMor X (n + m) σ) ▷ X) =
        (α_ (tensorPow D X m) X (tensorPow D X n)).hom ≫
          (tensorPow D X m ◁ (powPeel X n).inv) ≫
          ((tensorPow D X m ◁ permMor X (n + 1) τ) ≫
            (tensorPowConcat X m (n + 1)).hom) ≫
          ((powCast X (by omega : m + n = n + m) ≫
            permMor X (n + m) σ) ▷ X) := by
      conv_lhs => rw [MonoidalCategory.comp_whiskerRight,
        reassoc_of% g4, ← comm_beta_expand X m n, hτ]
      repeat' erw [Category.assoc]
      rfl
    have hw : ((powCast X (by omega : m + n = n + m) ≫
        permMor X (n + m) σ) ▷ X) =
        powCast X (by omega : m + n + 1 = n + m + 1) ≫
          permMor X (n + m + 1) (extPerm σ) := by
      rw [MonoidalCategory.comp_whiskerRight, powCast_whiskerRight,
        ← permMor_extPerm]
      rfl
    have hcp := reassoc_of% (powCast_permMor X
      (by omega : m + (n + 1) = n + (m + 1)) (blockEmbed 1 τ))
    have hfinal : ((tensorPowConcat X (m + 1) n).hom ≫
        powCast X (by omega : m + 1 + n = m + (n + 1))) ≫
        permMor X (m + (n + 1)) (blockEmbed 1 τ) ≫
        powCast X (by omega : m + n + 1 = n + m + 1) ≫
        permMor X (n + m + 1) (extPerm σ) =
        (tensorPowConcat X (m + 1) n).hom ≫
          powCast X (by omega : m + 1 + n = n + (m + 1)) ≫
          permMor X (n + (m + 1))
            (extPerm σ *
              (finCongr
                (by omega : m + (n + 1) = n + (m + 1))).permCongr
                (blockEmbed 1 τ)) := by
      have hb1 : (powCast X (by omega : m + n + 1 = n + m + 1) :
          tensorPow D X (m + (n + 1)) ⟶
            tensorPow D X (n + (m + 1))) =
          powCast X (by omega : m + (n + 1) = n + (m + 1)) := rfl
      have hb2 : (permMor X (n + m + 1) (extPerm σ) :
          tensorPow D X (n + (m + 1)) ⟶
            tensorPow D X (n + (m + 1))) =
          permMor X (n + (m + 1)) (extPerm σ) := rfl
      rw [Category.assoc, hb1, hb2, ← hcp, powCast_comp_assoc,
        ← permMor_mul]
    have e3b : (α_ (tensorPow D X m) X (tensorPow D X n)).hom ≫
        (tensorPow D X m ◁ (powPeel X n).inv) ≫
        ((tensorPow D X m ◁ permMor X (n + 1) τ) ≫
          (tensorPowConcat X m (n + 1)).hom) ≫
        ((powCast X (by omega : m + n = n + m) ≫
          permMor X (n + m) σ) ▷ X) =
        (tensorPowConcat X (m + 1) n).hom ≫
          powCast X (by omega : m + 1 + n = n + (m + 1)) ≫
          permMor X (n + (m + 1))
            (extPerm σ *
              (finCongr
                (by omega : m + (n + 1) = n + (m + 1))).permCongr
                (blockEmbed 1 τ)) := by
      rw [(tensorPowConcat_permMor_snd X m (n + 1) τ).symm]
      erw [hw]
      change (α_ (tensorPow D X m) X (tensorPow D X n)).hom ≫
        (tensorPow D X m ◁ (powPeel X n).inv) ≫
        ((tensorPowConcat X m (n + 1)).hom ≫
          permMor X (m + (n + 1)) (blockEmbed 1 τ)) ≫
        powCast X (by omega : m + (n + 1) = n + (m + 1)) ≫
        permMor X (n + (m + 1)) (extPerm σ) = _
      simp only [Category.assoc]
      rw [reassoc_of% (comm_head X m n)]
      exact hfinal
    exact g1.trans (g2.trans (e3a.trans e3b))

end CommMain

/-! ## Commutativity of the symmetric multiplication -/

section SymCommLaw

/-- Every permutation action on the ambient power is absorbed by
the two projections: the symmetriser eats it. -/
theorem permMor_π_absorb
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (N : ℕ) (τ : Equiv.Perm (Fin N)) :
    permMor X N τ ≫ modPowπ A X N ≫ symPowπ A X N =
      modPowπ A X N ≫ symPowπ A X N := by
  have h1 : modPowPerm (A := A) (X := X) N τ ≫ symPowπ A X N =
      symPowπ A X N := by
    have h2 := modPowAlg_absorb A X (MonoidAlgebra.single τ (1 : ℂ))
      (symmetriser_mul_single N τ)
    rwa [modPowAlg_single] at h2
  rw [← modPowπ_perm_assoc, h1]

/-- **Commutativity of the symmetric multiplication**, up to the
arity transport of `m + n = n + m`. -/
theorem symMul_comm
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (m n : ℕ) :
    (β_ (symPow A X m) (symPow A X n)).hom ≫ symMul A X n m =
      symMul A X m n ≫
        symPowCast A X (by omega : m + n = n + m) := by
  obtain ⟨σ, hσ⟩ := tensorPowConcat_braiding_exists X n m
  apply symPowTensor_hom_ext A X m n
  conv_lhs => rw [← Category.assoc,
    BraidedCategory.braiding_naturality, Category.assoc,
    symPowπ_tensor_symMul]
  conv_rhs => rw [← Category.assoc, symPowπ_tensor_symMul,
    Category.assoc, symPowπ_cast]
  apply modPowTensor_hom_ext A X m n
  conv_lhs => rw [← Category.assoc,
    BraidedCategory.braiding_naturality, Category.assoc,
    modPowπ_tensor_modPowMul_assoc]
  conv_rhs => rw [modPowπ_tensor_modPowMul_assoc, modPowπ_cast_assoc]
  rw [reassoc_of% hσ, permMor_π_absorb]

end SymCommLaw

end RS
