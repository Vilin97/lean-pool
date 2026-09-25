/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModTensor
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.MixedConc

/-!
# Module powers and symmetric powers over an internal monoid

The substrate of the Key Lemma: for an internal monoid `A` and a
left module `X` in a symmetric monoidal category, the `n`-th module
power `X ^ ⊗_A n` is presented in one step, with no associativity of
a binary product anywhere — it is the coequalizer of a single pair

    `⊕ᵢ Rᵢ ⇉ X ^ ⊗ n`

whose source is the finite biproduct, over the `n − 1` adjacent
slots, of the relation objects `Rᵢ = X^⊗a ⊗ ((X ⊗ A) ⊗ X) ⊗ X^⊗b`
(`a + 2 + b = n`), and whose legs act on the slot through the
braided right action and the left action respectively — identifying
`(x·c) ⊗ y` with `x ⊗ (c·y)` in every adjacent slot at once.

* `modPow A X n`, `modPowπ`, `modPowDesc`, `modPow_hom_ext`: the
  power and its universal property.  Slot conditions are quantified
  over decompositions `a + 2 + b = n` (with a `powCast` transport),
  so consumers never meet truncated subtraction.
* `modPowZero`, `modPowOne`: at `n ≤ 1` there are no slots, the
  legs agree, and the projection is an isomorphism.
* `modPowPerm`: the permutation action of `Envelope/SymPerm.lean`
  descends to the module power; `modPowPermHom`, `modPowAlg` package
  it as a monoid homomorphism and a `ℂ`-algebra map.  The descent is
  proved on the adjacent transpositions and extended by generation;
  commutativity of `A` is not needed, because the braided right
  action is by definition the left action through the braiding.
* `symmetriser n`: the trivial-character central idempotent
  `(1/n!) • ∑ σ, σ` of the group algebra, with absorption and
  idempotency.
* `symPow A X n`: the symmetric power, presented as the coequalizer
  of `modPowAlg (symmetriser n)` against the identity — the
  coinvariants — which the idempotent splits into a direct summand:
  `symPowσ ≫ symPowπ = 𝟙` and `symPowπ ≫ symPowσ` is the
  symmetriser's action.  This presentation is chosen because the
  consumers build morphisms out of `symPow` by descent along
  `symPowπ` and morphisms in through the section `symPowσ`.
The multiplication maps between module powers of different arities
are outside this module's scope; `tensorPowConcat_peel` and the
frame machinery below are the concatenation substrate they will
consume.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## Transport along equal arities -/

section PowCast

/-- Transport of a tensor power along an equality of arities.  It is
an `eqToHom`, so it composes and cancels by `eqToHom` simp lemmas. -/
def powCast [Category.{v} D] [MonoidalCategory D] (X : D)
    {m n : ℕ} (h : m = n) :
    tensorPow D X m ⟶ tensorPow D X n :=
  eqToHom (congrArg (tensorPow D X) h)

@[simp]
theorem powCast_rfl [Category.{v} D] [MonoidalCategory D] (X : D)
    (n : ℕ) : powCast X (rfl : n = n) = 𝟙 _ := rfl

@[reassoc (attr := simp)]
theorem powCast_comp [Category.{v} D] [MonoidalCategory D] (X : D)
    {m n k : ℕ} (h : m = n) (h' : n = k) :
    powCast X h ≫ powCast X h' = powCast X (h.trans h') := by
  simp [powCast]

/-- Two arity transports with the same endpoints agree. -/
theorem powCast_irrel [Category.{v} D] [MonoidalCategory D] (X : D)
    {m n : ℕ} (h h' : m = n) :
    powCast X h = powCast X h' := rfl

/-- Whiskering an arity transport is an arity transport. -/
theorem powCast_whiskerRight [Category.{v} D] [MonoidalCategory D] (X : D)
    {m n : ℕ} (h : m = n) :
    powCast X h ▷ X = powCast X (by omega : m + 1 = n + 1) := by
  subst h
  simp only [powCast_rfl, MonoidalCategory.id_whiskerRight]
  rfl

end PowCast

/-! ## Peeling the first factor off a tensor power

The tensor power grows at the top, so the bottom factor is exposed
by a recursion of its own; the peeling intertwines the two
concatenation stages `p + (q + 1)` and `(p + 1) + q`, which is what
lets a relation slot and an adjacent braiding that overlap in one
module factor be compared in a common frame.
-/

section Peel

/-- Peel the first factor off a non-empty tensor power. -/
noncomputable def powPeel
    [Category.{v} D] [MonoidalCategory D] (X : D) : (q : ℕ) →
    (tensorPow D X (q + 1) ≅ X ⊗ tensorPow D X q)
  | 0 => λ_ X ≪≫ (ρ_ X).symm
  | q + 1 => whiskerRightIso (powPeel X q) X ≪≫ α_ X (tensorPow D X q) X

/-- The base case of the peeling. -/
theorem powPeel_zero [Category.{v} D] [MonoidalCategory D] (X : D) :
    powPeel X 0 = λ_ X ≪≫ (ρ_ X).symm := rfl

/-- Attach a peeled factor to the power below it.  The associator,
retyped so that its target is stated through the tensor power — this
keeps every statement about it type-correct at low transparency. -/
noncomputable def powAttach [Category.{v} D] [MonoidalCategory D] (X : D)
    (p q : ℕ) :
    tensorPow D X p ⊗ (X ⊗ tensorPow D X q) ⟶
      tensorPow D X (p + 1) ⊗ tensorPow D X q :=
  (α_ (tensorPow D X p) X (tensorPow D X q)).inv

/-- Expose the top factor of the second block of a pair of powers.
The associator, retyped so that its source is stated through the
tensor power. -/
noncomputable def powExpose [Category.{v} D] [MonoidalCategory D] (X : D)
    (p q : ℕ) :
    tensorPow D X p ⊗ tensorPow D X (q + 1) ⟶
      (tensorPow D X p ⊗ tensorPow D X q) ⊗ X :=
  (α_ (tensorPow D X p) (tensorPow D X q) X).inv

/-- The successor stage of the concatenation, through the exposed
top factor; definitional. -/
theorem tensorPowConcat_succ_hom [Category.{v} D] [MonoidalCategory D] (X : D)
    (p q : ℕ) :
    (tensorPowConcat X p (q + 1)).hom =
      powExpose X p q ≫ ((tensorPowConcat X p q).hom ▷ X) :=
  rfl

/-- The base case of the concatenation shift, at general objects. -/
private theorem concat_peel_zero_aux
    [Category.{v} D] [MonoidalCategory D] (X : D)
    (P : D) :
    (α_ P (𝟙_ D) X).inv ≫ ((ρ_ P).hom ▷ X) =
      (P ◁ ((λ_ X).hom ≫ (ρ_ X).inv)) ≫ (α_ P X (𝟙_ D)).inv ≫
        (ρ_ (P ⊗ X)).hom := by
  monoidal

/-- The associator shuffle of the concatenation shift, at general
objects. -/
private theorem concat_peel_step_aux
    [Category.{v} D] [MonoidalCategory D] (X : D)
    {P R S : D} (e : R ⟶ X ⊗ S) :
    (α_ P R X).inv ≫ ((P ◁ e) ▷ X) ≫ ((α_ P X S).inv ▷ X) =
      (P ◁ ((e ▷ X) ≫ (α_ X S X).hom)) ≫
        (α_ P X (S ⊗ X)).inv ≫ (α_ (P ⊗ X) S X).inv := by
  have hpent : (α_ P (X ⊗ S) X).inv ≫ ((α_ P X S).inv ▷ X) =
      (P ◁ (α_ X S X).hom) ≫ (α_ P X (S ⊗ X)).inv ≫
        (α_ (P ⊗ X) S X).inv := by
    monoidal
  rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, ← hpent,
    ← MonoidalCategory.associator_inv_naturality_middle_assoc]

/-- The step of the concatenation shift, stated through the retyped
bridges and the unexpanded peeling, so that every composite is typed
at a tensor power. -/
private theorem concat_peel_step [Category.{v} D] [MonoidalCategory D] (X : D)
    (p q : ℕ) :
    powExpose X p (q + 1) ≫
        ((tensorPow D X p ◁ (powPeel X q).hom) ▷ X) ≫
        (powAttach X p q ▷ X) ≫
        ((tensorPowConcat X (p + 1) q).hom ▷ X) =
      (tensorPow D X p ◁ (powPeel X (q + 1)).hom) ≫
        powAttach X p (q + 1) ≫
        (tensorPowConcat X (p + 1) (q + 1)).hom := by
  suffices hpre : powExpose X p (q + 1) ≫
      ((tensorPow D X p ◁ (powPeel X q).hom) ▷ X) ≫
      (powAttach X p q ▷ X) =
        (tensorPow D X p ◁ (powPeel X (q + 1)).hom) ≫
          powAttach X p (q + 1) ≫ powExpose X (p + 1) q by
    rw [tensorPowConcat_succ_hom X (p + 1) q]
    simp only [← Category.assoc] at hpre ⊢
    rw [hpre]
    simp only [Category.assoc]
    rfl
  exact concat_peel_step_aux X (powPeel X q).hom

/-- **The concatenation shift**: concatenating `p` with `q + 1`
factors is peeling the first of the `q + 1`, attaching it to the
`p`, and concatenating `p + 1` with `q`. -/
theorem tensorPowConcat_peel [Category.{v} D] [MonoidalCategory D] (X : D)
    (p : ℕ) : ∀ q : ℕ,
    (tensorPowConcat X p (q + 1)).hom =
      (tensorPow D X p ◁ (powPeel X q).hom) ≫
        powAttach X p q ≫
        (tensorPowConcat X (p + 1) q).hom ≫
        powCast X (by omega : p + 1 + q = p + (q + 1))
  | 0 => by
    rw [tensorPowConcat_succ X p 0, powPeel_zero,
      tensorPowConcat_zero, tensorPowConcat_zero]
    simp only [Iso.trans_hom, Iso.symm_hom]
    exact (concat_peel_zero_aux X (tensorPow D X p)).trans
      (congrArg (fun z =>
          (tensorPow D X p ◁ ((λ_ X).hom ≫ (ρ_ X).inv)) ≫
            (α_ (tensorPow D X p) X (𝟙_ D)).inv ≫ z)
        (Category.comp_id (ρ_ (tensorPow D X p ⊗ X)).hom)).symm
  | q + 1 => by
    rw [tensorPowConcat_succ_hom X p (q + 1), tensorPowConcat_peel X p q]
    simp only [MonoidalCategory.comp_whiskerRight]
    erw [powCast_whiskerRight, reassoc_of% (concat_peel_step X p q)]
    exact (Category.assoc _ _ _).trans (congrArg
      (fun z => (tensorPow D X p ◁ (powPeel X (q + 1)).hom) ≫ z)
      (Category.assoc _ _ _))

end Peel

/-! ## The slot relation

The local shape of one relation slot: on `(X ⊗ A) ⊗ X`, either the
monoid acts on the left factor through the braided right action, or
it associates and acts on the right factor.  These are the legs of
`ModTensor.lean` at the module `X` itself, unbundled.
-/

section WinLeg

/-- The slot leg acting on the left factor, through the braided
right action. -/
noncomputable def winLegM
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] : (X ⊗ A) ⊗ X ⟶ X ⊗ X :=
  actRight A X ▷ X

/-- The slot leg acting on the right factor: associate, then act. -/
noncomputable def winLegN
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : D)
    [ModObj A X] : (X ⊗ A) ⊗ X ⟶ X ⊗ X :=
  (α_ X A X).hom ≫ X ◁ actLeft A X

end WinLeg

/-! ## The relation pair of the module power -/

section ModPowDefs

/-- The relation object of the slot `a + 2 + b = n`: the ambient
power with the monoid inserted between the module factors in slots
`a` and `a + 1`.  An abbreviation, so that statements about it stay
type-correct at low transparency. -/
abbrev modPowMid [Category.{v} D] [MonoidalCategory D] (A : D) (X : D)
    (a b : ℕ) : D :=
  (tensorPow D X a ⊗ ((X ⊗ A) ⊗ X)) ⊗ tensorPow D X b

/-- Glue a resolved slot back into the ambient power: reassociate
the two exposed factors onto the lower power and concatenate. -/
noncomputable def modPowGlue [Category.{v} D] [MonoidalCategory D] (X : D)
    (a b : ℕ) :
    (tensorPow D X a ⊗ (X ⊗ X)) ⊗ tensorPow D X b ⟶
      tensorPow D X (a + 2 + b) :=
  ((α_ (tensorPow D X a) X X).inv ▷ tensorPow D X b) ≫
    (tensorPowConcat X (a + 2) b).hom

/-- The first relation leg at slot `(a, b)`: act on the left module
factor through the braided right action, then glue. -/
noncomputable def modPowLegM
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X]
    (a b : ℕ) :
    modPowMid A X a b ⟶ tensorPow D X (a + 2 + b) :=
  ((tensorPow D X a ◁ winLegM A X) ▷ tensorPow D X b) ≫
    modPowGlue X a b

/-- The second relation leg at slot `(a, b)`: associate and act on
the right module factor, then glue. -/
noncomputable def modPowLegN
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : D)
    [ModObj A X]
    (a b : ℕ) :
    modPowMid A X a b ⟶ tensorPow D X (a + 2 + b) :=
  ((tensorPow D X a ◁ winLegN A X) ▷ tensorPow D X b) ≫
    modPowGlue X a b

variable {A X} in
/-- Each slot index of arity `n` decomposes it. -/
theorem slot_decomp {n : ℕ} (i : Fin (n - 1)) :
    i.val + 2 + (n - 2 - i.val) = n := by
  have := i.isLt; omega

/-- The source of the relation pair: the biproduct of the relation
objects over all `n − 1` adjacent slots.  An abbreviation, so that
the biproduct API applies to the legs without unfolding. -/
noncomputable abbrev modPowSrc
    [Category.{v} D] [MonoidalCategory D] (A : D) (X : D) [Preadditive D]
    [HasFiniteBiproducts D]
    (n : ℕ) : D :=
  ⨁ fun i : Fin (n - 1) => modPowMid A X i.val (n - 2 - i.val)

/-- The first leg of the relation pair, assembled over all slots. -/
noncomputable def modPowLegFst
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    (n : ℕ) :
    modPowSrc A X n ⟶ tensorPow D X n :=
  biproduct.desc fun i =>
    modPowLegM A X i.val (n - 2 - i.val) ≫ powCast X (slot_decomp i)

/-- The second leg of the relation pair, assembled over all slots. -/
noncomputable def modPowLegSnd
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : D)
    [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    (n : ℕ) :
    modPowSrc A X n ⟶ tensorPow D X n :=
  biproduct.desc fun i =>
    modPowLegN A X i.val (n - 2 - i.val) ≫ powCast X (slot_decomp i)

end ModPowDefs

/-! ## The module power and its universal property -/

section ModPow

/-- **The `n`-th module power** of `X` over `A`: the coequalizer of
the wide relation pair, identifying `(x·c) ⊗ y ~ x ⊗ (c·y)` in every
adjacent slot simultaneously.  No binary module tensor product and
no associativity enter. -/
noncomputable def modPow
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (n : ℕ) : D :=
  coequalizer (modPowLegFst A X n) (modPowLegSnd A X n)

/-- The projection of the ambient power onto the module power. -/
noncomputable def modPowπ
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (n : ℕ) :
    tensorPow D X n ⟶ modPow A X n :=
  coequalizer.π _ _

instance [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (n : ℕ) : Epi (modPowπ A X n) :=
  inferInstanceAs (Epi (coequalizer.π _ _))

/-- The two assembled legs agree after the projection. -/
@[reassoc]
theorem modPow_condition
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (n : ℕ) :
    modPowLegFst A X n ≫ modPowπ A X n =
      modPowLegSnd A X n ≫ modPowπ A X n :=
  coequalizer.condition _ _

/-- **The slot relation in the module power**: at every
decomposition `a + 2 + b = n` the two slot legs agree after the
projection. -/
@[reassoc]
theorem modPow_rel
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    {n : ℕ} (a b : ℕ) (h : a + 2 + b = n) :
    modPowLegM A X a b ≫ powCast X h ≫ modPowπ A X n =
      modPowLegN A X a b ≫ powCast X h ≫ modPowπ A X n := by
  have hb : b = n - 2 - a := by omega
  subst hb
  have hi : a < n - 1 := by omega
  have h2 : biproduct.ι
        (fun i : Fin (n - 1) => modPowMid A X i.val (n - 2 - i.val))
        ⟨a, hi⟩ ≫ modPowLegFst A X n ≫ modPowπ A X n =
      biproduct.ι
        (fun i : Fin (n - 1) => modPowMid A X i.val (n - 2 - i.val))
        ⟨a, hi⟩ ≫ modPowLegSnd A X n ≫ modPowπ A X n := by
    rw [modPow_condition]
  simp only [modPowLegFst, modPowLegSnd, biproduct.ι_desc_assoc,
    Category.assoc] at h2
  exact h2

/-- Morphisms out of the module power are determined by their
composite with the projection. -/
theorem modPow_hom_ext
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    {n : ℕ} {W : D} {k l : modPow A X n ⟶ W}
    (h : modPowπ A X n ≫ k = modPowπ A X n ≫ l) : k = l :=
  coequalizer.hom_ext h

/-- Descend a morphism that coequalizes every slot relation to the
module power. -/
noncomputable def modPowDesc
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    {n : ℕ} {W : D} (k : tensorPow D X n ⟶ W)
    (h : ∀ a b (hab : a + 2 + b = n),
      modPowLegM A X a b ≫ powCast X hab ≫ k =
        modPowLegN A X a b ≫ powCast X hab ≫ k) :
    modPow A X n ⟶ W :=
  coequalizer.desc k (by
    apply biproduct.hom_ext'
    intro i
    simp only [modPowLegFst, modPowLegSnd, biproduct.ι_desc_assoc,
      Category.assoc]
    exact h i.val (n - 2 - i.val) (slot_decomp i))

/-- The descent factors the given morphism through the
projection. -/
@[reassoc (attr := simp)]
theorem modPowπ_desc
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    {n : ℕ} {W : D} (k : tensorPow D X n ⟶ W)
    (h : ∀ a b (hab : a + 2 + b = n),
      modPowLegM A X a b ≫ powCast X hab ≫ k =
        modPowLegN A X a b ≫ powCast X hab ≫ k) :
    modPowπ A X n ≫ modPowDesc A X k h = k :=
  coequalizer.π_desc _ _

/-! ### The empty and singleton powers

At `n ≤ 1` there are no adjacent slots: the relation source is the
empty biproduct, the legs agree, and the projection is an
isomorphism.
-/

/-- Below two factors the projection is an isomorphism. -/
noncomputable def modPowTriv
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    {n : ℕ} (h : n ≤ 1) :
    modPow A X n ≅ tensorPow D X n where
  hom := modPowDesc A X (𝟙 _) (fun a b hab => absurd hab (by omega))
  inv := modPowπ A X n
  hom_inv_id := modPow_hom_ext A X (by
    rw [modPowπ_desc_assoc, Category.id_comp, Category.comp_id])
  inv_hom_id := modPowπ_desc A X _ _

/-- **The empty module power is the unit.** -/
noncomputable def modPowZero
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] : modPow A X 0 ≅ 𝟙_ D :=
  modPowTriv A X (by omega)

/-- **The singleton module power is the module.** -/
noncomputable def modPowOne
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] : modPow A X 1 ≅ X :=
  modPowTriv A X (by omega) ≪≫ λ_ X

/-! ### Whiskering the presentation on the right

Tensoring on the right by a fixed object carries the coequalizer
presenting the module power to a coequalizer, so a morphism out of
the whiskered module power is a morphism out of the whiskered
ambient power that respects the whiskered relation.  The hypothesis
is the exact colimit preservation needed, so that the kit applies
both where tensoring on the left is assumed exact and where
tensoring on the right is.
-/

/-- Whiskering the module-power coequalizer on the right yields a
colimit cofork. -/
noncomputable def modPowWhiskerRightIsColimit
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] (n : ℕ) (W : D)
    [PreservesColimit (parallelPair (modPowLegFst A X n) (modPowLegSnd A X
      n)) (tensorRight W)] :
    IsColimit (Cofork.ofπ (modPowπ A X n ▷ W)
      (by rw [← MonoidalCategory.comp_whiskerRight, modPow_condition,
        MonoidalCategory.comp_whiskerRight]) :
      Cofork (modPowLegFst A X n ▷ W) (modPowLegSnd A X n ▷ W)) :=
  isColimitOfHasCoequalizerOfPreservesColimit (tensorRight W) _ _

/-- Morphisms out of a right-whiskered module power are determined
by their composite with the whiskered projection. -/
theorem modPow_whiskerRight_hom_ext
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] (n : ℕ) (W : D)
    [PreservesColimit (parallelPair (modPowLegFst A X n) (modPowLegSnd A X
      n)) (tensorRight W)]
    {Z : D}
    {k l : modPow A X n ⊗ W ⟶ Z}
    (h : (modPowπ A X n ▷ W) ≫ k = (modPowπ A X n ▷ W) ≫ l) :
    k = l :=
  Cofork.IsColimit.hom_ext (modPowWhiskerRightIsColimit A X n W) h

/-- The right-whiskered projection is an epimorphism. -/
instance epi_modPowπ_whiskerRight
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] (n : ℕ) (W : D)
    [PreservesColimit (parallelPair (modPowLegFst A X n) (modPowLegSnd A X
      n)) (tensorRight W)] : Epi (modPowπ A X n ▷ W) :=
  epi_of_isColimit_cofork (modPowWhiskerRightIsColimit A X n W)

/-- Descend a morphism along the right-whiskered projection. -/
noncomputable def modPowWhiskerRightDesc
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] (n : ℕ) (W : D)
    [PreservesColimit (parallelPair (modPowLegFst A X n) (modPowLegSnd A X
      n)) (tensorRight W)]
    {Z : D}
    (k : tensorPow D X n ⊗ W ⟶ Z)
    (h : (modPowLegFst A X n ▷ W) ≫ k =
      (modPowLegSnd A X n ▷ W) ≫ k) :
    modPow A X n ⊗ W ⟶ Z :=
  Cofork.IsColimit.desc (modPowWhiskerRightIsColimit A X n W) k h

/-- The right-whiskered descent factors through the whiskered
projection. -/
@[reassoc (attr := simp)]
theorem modPowπ_whiskerRight_desc
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] (n : ℕ) (W : D)
    [PreservesColimit (parallelPair (modPowLegFst A X n) (modPowLegSnd A X
      n)) (tensorRight W)]
    {Z : D}
    (k : tensorPow D X n ⊗ W ⟶ Z)
    (h : (modPowLegFst A X n ▷ W) ≫ k =
      (modPowLegSnd A X n ▷ W) ≫ k) :
    (modPowπ A X n ▷ W) ≫ modPowWhiskerRightDesc A X n W k h = k :=
  Cofork.IsColimit.π_desc' (modPowWhiskerRightIsColimit A X n W) k h

end ModPow

/-! ## The adjacent transposition on the ambient power

The permutation action descends to the module power once it
descends on the adjacent transpositions, which act by a braiding of
two adjacent slots — the top braiding of the first `a + 2` factors,
conjugated into the ambient power by the concatenation.
-/

section AdjSwap

/-- The braiding of slots `a` and `a + 1` of the ambient power:
the top braiding of the first `a + 2` factors, in block form. -/
noncomputable def adjSwapMor
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (X : D)
    (a b : ℕ) :
    tensorPow D X (a + 2 + b) ⟶ tensorPow D X (a + 2 + b) :=
  (tensorPowConcat X (a + 2) b).inv ≫
    (swapTop X a ▷ tensorPow D X b) ≫
    (tensorPowConcat X (a + 2) b).hom

/-- Conjugation carries a transposition to the transposition of the
images. -/
private theorem permCongr_swap {α β : Type*} [DecidableEq α]
    [DecidableEq β] (e : α ≃ β) (u v : α) :
    e.permCongr (Equiv.swap u v) = Equiv.swap (e u) (e v) := by
  rw [Equiv.permCongr_def]
  exact Equiv.symm_trans_swap_trans u v e

/-- A block-embedded transposition of the first block. -/
private theorem blockEmbed_swap_one {p b : ℕ} (u v : Fin p) :
    blockEmbed (Equiv.swap u v) (1 : Equiv.Perm (Fin b)) =
      Equiv.swap (Fin.castAdd b u) (Fin.castAdd b v) := by
  rw [blockEmbed, Equiv.Perm.one_def, Equiv.Perm.sumCongr_swap_refl,
    permCongr_swap]
  rfl

/-- A block-embedded transposition of the last block. -/
private theorem blockEmbed_one_swap {p b : ℕ} (u v : Fin b) :
    blockEmbed (1 : Equiv.Perm (Fin p)) (Equiv.swap u v) =
      Equiv.swap (Fin.natAdd p u) (Fin.natAdd p v) := by
  rw [blockEmbed, Equiv.Perm.one_def, Equiv.Perm.sumCongr_refl_swap,
    permCongr_swap]
  rfl

/-- The top transposition, as a transposition of explicit slots. -/
private theorem topSwap_eq_mk (a : ℕ) :
    (topSwap : Equiv.Perm (Fin (a + 2))) =
      Equiv.swap ⟨a, by omega⟩ ⟨a + 1, by omega⟩ :=
  rfl

/-- **The adjacent braiding is the action of the adjacent
transposition.** -/
theorem adjSwapMor_eq_permMor
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (X : D)
    (a b : ℕ) :
    adjSwapMor X a b =
      permMor X (a + 2 + b)
        (Equiv.swap ⟨a, by omega⟩ ⟨a + 1, by omega⟩) := by
  have hswap :
      (Equiv.swap (⟨a, by omega⟩ : Fin (a + 2 + b)) ⟨a + 1, by omega⟩)
        = blockEmbed (topSwap : Equiv.Perm (Fin (a + 2)))
            (1 : Equiv.Perm (Fin b)) := by
    rw [topSwap_eq_mk, blockEmbed_swap_one]
    rfl
  rw [hswap, adjSwapMor, ← permMor_topSwap_eq, Iso.inv_comp_eq,
    tensorPowConcat_permMor_fst]

/-- Transport of a permutation action along an equality of
arities. -/
theorem powCast_permMor
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (X : D)
    {m n : ℕ} (h : m = n)
    (σ : Equiv.Perm (Fin m)) :
    powCast X h ≫ permMor X n ((finCongr h).permCongr σ) =
      permMor X m σ ≫ powCast X h := by
  subst h
  have hσ : (finCongr (rfl : m = m)).permCongr σ = σ :=
    Equiv.ext fun i => by simp
  rw [hσ]
  simp [powCast]

/-- Transport of a transposition action along an equality of
arities. -/
theorem powCast_permMor_swap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (X : D)
    {m n : ℕ} (h : m = n) (u v : Fin m) :
    powCast X h ≫ permMor X n (Equiv.swap (Fin.cast h u) (Fin.cast h v)) =
      permMor X m (Equiv.swap u v) ≫ powCast X h := by
  have h2 := powCast_permMor X h (Equiv.swap u v)
  rwa [permCongr_swap, finCongr_apply, finCongr_apply] at h2

end AdjSwap

/-! ## The braiding at a relation slot

The braiding of the two module factors of a slot carries the monoid
along; the relation legs intertwine it with the plain braiding on
the resolved slot.  No commutativity of the monoid is needed: the
braided right action is by definition the left action through the
braiding, so the exchanged slot acts by the same morphism.
-/

section WinSwap

/-- Exchange of the two module factors of a relation slot, carrying
the monoid along: `(x ⊗ c) ⊗ y ↦ (y ⊗ c) ⊗ x`. -/
noncomputable def winSwap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (A X : D) : (X ⊗ A) ⊗ X ⟶ (X ⊗ A) ⊗ X :=
  (β_ (X ⊗ A) X).hom ≫ (X ◁ (β_ X A).hom) ≫ (α_ X A X).inv

/-- The slot exchange is an involution. -/
@[reassoc (attr := simp)]
theorem winSwap_winSwap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (A X : D) :
    winSwap A X ≫ winSwap A X = 𝟙 _ := by
  simp only [winSwap, BraidedCategory.braiding_tensor_left_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc X (β_ X A).hom
      (β_ A X).hom, SymmetricCategory.symmetry,
    MonoidalCategory.whiskerLeft_id, Category.id_comp,
    Iso.hom_inv_id_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc,
    SymmetricCategory.symmetry, MonoidalCategory.id_whiskerRight,
    Category.id_comp, Iso.inv_hom_id_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    SymmetricCategory.symmetry, MonoidalCategory.whiskerLeft_id,
    Category.id_comp, Iso.hom_inv_id]

/-- The first leg intertwines the slot exchange with the braiding:
acting on the left factor and braiding is exchanging and acting on
the right factor. -/
theorem winLegM_braiding
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] :
    winLegM A X ≫ (β_ X X).hom = winSwap A X ≫ winLegN A X := by
  rw [winLegM, BraidedCategory.braiding_naturality_left, actRight,
    MonoidalCategory.whiskerLeft_comp, winSwap, winLegN]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The second leg intertwines the slot exchange with the braiding,
by the involutivity of both. -/
theorem winLegN_braiding
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] :
    winLegN A X ≫ (β_ X X).hom = winSwap A X ≫ winLegM A X := by
  have h1 : winLegM A X = winSwap A X ≫ winLegN A X ≫ (β_ X X).hom := by
    rw [← Category.assoc, ← winLegM_braiding, Category.assoc,
      SymmetricCategory.symmetry, Category.comp_id]
  rw [h1, ← Category.assoc, ← Category.assoc, winSwap_winSwap,
    Category.id_comp]

end WinSwap

/-! ## Descent of the slot relations under the adjacent braiding -/

section Descent

/-- The same-slot conjugation, at general objects, so that no
tensor-power arity enters the rewriting. -/
private theorem glue_adjSwap_aux
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    (X : D)
    {P Q N : D}
    (C : ((P ⊗ X) ⊗ X) ⊗ Q ≅ N) (u : (X ⊗ A) ⊗ X ⟶ X ⊗ X) :
    (((P ◁ u) ▷ Q) ≫ ((α_ P X X).inv ▷ Q ≫ C.hom)) ≫
        (C.inv ≫
          (((α_ P X X).hom ≫ (P ◁ (β_ X X).hom) ≫ (α_ P X X).inv) ▷ Q)
            ≫ C.hom) =
      ((P ◁ (u ≫ (β_ X X).hom)) ▷ Q) ≫
        ((α_ P X X).inv ▷ Q ≫ C.hom) := by
  have h : ((α_ P X X).inv ▷ Q) ≫
      (((α_ P X X).hom ≫ (P ◁ (β_ X X).hom) ≫ (α_ P X X).inv) ▷ Q) =
        ((P ◁ (β_ X X).hom) ▷ Q) ≫ ((α_ P X X).inv ▷ Q) := by
    rw [← MonoidalCategory.comp_whiskerRight, Iso.inv_hom_id_assoc,
      MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% h, ← MonoidalCategory.comp_whiskerRight_assoc,
    ← MonoidalCategory.whiskerLeft_comp]

/-- Postcomposing a glued slot morphism with the adjacent braiding
at the same slot braids the resolved factors. -/
private theorem glue_adjSwap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    (X : D)
    (a b : ℕ) (u : (X ⊗ A) ⊗ X ⟶ X ⊗ X) :
    (((tensorPow D X a ◁ u) ▷ tensorPow D X b) ≫ modPowGlue X a b) ≫
        adjSwapMor X a b =
      ((tensorPow D X a ◁ (u ≫ (β_ X X).hom)) ▷ tensorPow D X b) ≫
        modPowGlue X a b :=
  glue_adjSwap_aux A X (tensorPowConcat X (a + 2) b) u

/-- The slot relation with no arity transport. -/
@[reassoc]
theorem modPow_rel_self
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (a b : ℕ) :
    modPowLegM A X a b ≫ modPowπ A X (a + 2 + b) =
      modPowLegN A X a b ≫ modPowπ A X (a + 2 + b) := by
  have h := modPow_rel A X a b (rfl : a + 2 + b = a + 2 + b)
  simpa using h

/-- **Descent along the projection**: the property that an ambient
endomorphism carries every slot relation into the kernel of the
projection again. -/
def modPowDescends
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (n : ℕ)
    (f : tensorPow D X n ⟶ tensorPow D X n) : Prop :=
  ∀ a b (hab : a + 2 + b = n),
    modPowLegM A X a b ≫ powCast X hab ≫ f ≫ modPowπ A X n =
      modPowLegN A X a b ≫ powCast X hab ≫ f ≫ modPowπ A X n

/-- **The same-slot case**: the adjacent braiding at the slot of the
relation itself. -/
private theorem adjSwap_rel_same
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (a b : ℕ) :
    modPowLegM A X a b ≫ adjSwapMor X a b ≫
        modPowπ A X (a + 2 + b) =
      modPowLegN A X a b ≫ adjSwapMor X a b ≫
        modPowπ A X (a + 2 + b) := by
  have h1 : modPowLegM A X a b ≫ adjSwapMor X a b =
      ((tensorPow D X a ◁ winSwap A X) ▷ tensorPow D X b) ≫
        modPowLegN A X a b := by
    rw [modPowLegM, modPowLegN, glue_adjSwap A X a b,
      winLegM_braiding, MonoidalCategory.whiskerLeft_comp,
      MonoidalCategory.comp_whiskerRight, Category.assoc]
  have h2 : modPowLegN A X a b ≫ adjSwapMor X a b =
      ((tensorPow D X a ◁ winSwap A X) ▷ tensorPow D X b) ≫
        modPowLegM A X a b := by
    rw [modPowLegN, modPowLegM, glue_adjSwap A X a b,
      winLegN_braiding, MonoidalCategory.whiskerLeft_comp,
      MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [← Category.assoc, h1, ← Category.assoc, h2, Category.assoc,
    Category.assoc, modPow_rel_self]

/-! ### The disjoint cases

When the braided pair lies entirely inside the upper or lower
context of the relation slot, the braiding passes the legs by the
exchange law, through the block form of the embedded permutation.
-/

/-- A morphism conjugate to one of the upper context passes a glued
slot leg; at general objects. -/
private theorem ctx_above_aux
    [Category.{v} D] [MonoidalCategory D] (A : D) (X : D)
    {P Q N : D}
    (C : ((P ⊗ X) ⊗ X) ⊗ Q ≅ N) (w : (X ⊗ A) ⊗ X ⟶ X ⊗ X)
    (v : Q ⟶ Q) (E : N ⟶ N)
    (hE : C.hom ≫ E = (((P ⊗ X) ⊗ X) ◁ v) ≫ C.hom) :
    (((P ◁ w) ▷ Q) ≫ ((α_ P X X).inv ▷ Q ≫ C.hom)) ≫ E =
      ((P ⊗ ((X ⊗ A) ⊗ X)) ◁ v) ≫
        (((P ◁ w) ▷ Q) ≫ ((α_ P X X).inv ▷ Q ≫ C.hom)) := by
  simp only [Category.assoc, hE]
  rw [← MonoidalCategory.whisker_exchange_assoc,
    ← MonoidalCategory.whisker_exchange_assoc]

/-- A morphism conjugate to one of the lower context passes a glued
slot leg; at general objects. -/
private theorem ctx_below_aux
    [Category.{v} D] [MonoidalCategory D] (A : D) (X : D)
    {P Q N : D}
    (C : ((P ⊗ X) ⊗ X) ⊗ Q ≅ N) (w : (X ⊗ A) ⊗ X ⟶ X ⊗ X)
    (v : P ⟶ P) (E : N ⟶ N)
    (hE : C.hom ≫ E = (((v ▷ X) ▷ X) ▷ Q) ≫ C.hom) :
    (((P ◁ w) ▷ Q) ≫ ((α_ P X X).inv ▷ Q ≫ C.hom)) ≫ E =
      ((v ▷ ((X ⊗ A) ⊗ X)) ▷ Q) ≫
        (((P ◁ w) ▷ Q) ≫ ((α_ P X X).inv ▷ Q ≫ C.hom)) := by
  have hinner : (P ◁ w) ≫ (α_ P X X).inv ≫ ((v ▷ X) ▷ X) =
      (v ▷ ((X ⊗ A) ⊗ X)) ≫ (P ◁ w) ≫ (α_ P X X).inv := by
    rw [← MonoidalCategory.associator_inv_naturality_left,
      ← MonoidalCategory.whisker_exchange_assoc]
  simp only [Category.assoc, hE]
  rw [← MonoidalCategory.comp_whiskerRight_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc]
  simp only [Category.assoc]
  rw [hinner]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]

variable {A X} in
/-- **The disjoint case, braid above**: the adjacent braiding lies
inside the upper context of the relation slot. -/
private theorem adjSwap_rel_above
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] {A : D}
    [MonObj A] {X : D} [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (a j b₀ : ℕ)
    (h : a + 2 + (j + 2 + b₀) = a + 2 + j + 2 + b₀) :
    modPowLegM A X a (j + 2 + b₀) ≫ powCast X h ≫
        adjSwapMor X (a + 2 + j) b₀ ≫
        modPowπ A X (a + 2 + j + 2 + b₀) =
      modPowLegN A X a (j + 2 + b₀) ≫ powCast X h ≫
        adjSwapMor X (a + 2 + j) b₀ ≫
        modPowπ A X (a + 2 + j + 2 + b₀) := by
  have hcast : powCast X h ≫ adjSwapMor X (a + 2 + j) b₀ =
      permMor X (a + 2 + (j + 2 + b₀))
          (Equiv.swap ⟨a + 2 + j, by omega⟩ ⟨a + 2 + j + 1, by omega⟩)
        ≫ powCast X h := by
    rw [adjSwapMor_eq_permMor]
    exact powCast_permMor_swap X h ⟨a + 2 + j, by omega⟩
      ⟨a + 2 + j + 1, by omega⟩
  have hE : (tensorPowConcat X (a + 2) (j + 2 + b₀)).hom ≫
      permMor X (a + 2 + (j + 2 + b₀))
        (Equiv.swap ⟨a + 2 + j, by omega⟩ ⟨a + 2 + j + 1, by omega⟩) =
      (tensorPow D X (a + 2) ◁ adjSwapMor X j b₀) ≫
        (tensorPowConcat X (a + 2) (j + 2 + b₀)).hom := by
    have hsw : (Equiv.swap (⟨a + 2 + j, by omega⟩ :
          Fin (a + 2 + (j + 2 + b₀))) ⟨a + 2 + j + 1, by omega⟩) =
        blockEmbed (1 : Equiv.Perm (Fin (a + 2)))
          (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, by omega⟩) := by
      rw [blockEmbed_one_swap]
      rfl
    rw [hsw, adjSwapMor_eq_permMor, tensorPowConcat_permMor_snd]
  have hM : ∀ w : (X ⊗ A) ⊗ X ⟶ X ⊗ X,
      (((tensorPow D X a ◁ w) ▷ tensorPow D X (j + 2 + b₀)) ≫
          modPowGlue X a (j + 2 + b₀)) ≫ powCast X h ≫
          adjSwapMor X (a + 2 + j) b₀ ≫
          modPowπ A X (a + 2 + j + 2 + b₀) =
        ((tensorPow D X a ⊗ ((X ⊗ A) ⊗ X)) ◁ adjSwapMor X j b₀) ≫
          (((tensorPow D X a ◁ w) ▷ tensorPow D X (j + 2 + b₀)) ≫
            modPowGlue X a (j + 2 + b₀)) ≫ powCast X h ≫
          modPowπ A X (a + 2 + j + 2 + b₀) := by
    intro w
    conv_lhs => rw [reassoc_of% hcast]
    rw [modPowGlue]
    simp only [Category.assoc]
    repeat' erw [Category.assoc]
    erw [reassoc_of% (ctx_above_aux A X
      (tensorPowConcat X (a + 2) (j + 2 + b₀)) w
      (adjSwapMor X j b₀) _ hE)]
  rw [modPowLegM, modPowLegN, hM (winLegM A X), hM (winLegN A X),
    ← modPowLegM, ← modPowLegN, modPow_rel A X a (j + 2 + b₀) h]

variable {A X} in
/-- **The disjoint case, braid below**: the adjacent braiding lies
inside the lower context of the relation slot. -/
private theorem adjSwap_rel_below
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] {A : D}
    [MonObj A] {X : D} [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (a₀ j b : ℕ)
    (h : a₀ + 2 + j + 2 + b = a₀ + 2 + (j + 2 + b)) :
    modPowLegM A X (a₀ + 2 + j) b ≫ powCast X h ≫
        adjSwapMor X a₀ (j + 2 + b) ≫
        modPowπ A X (a₀ + 2 + (j + 2 + b)) =
      modPowLegN A X (a₀ + 2 + j) b ≫ powCast X h ≫
        adjSwapMor X a₀ (j + 2 + b) ≫
        modPowπ A X (a₀ + 2 + (j + 2 + b)) := by
  have hcast : powCast X h ≫ adjSwapMor X a₀ (j + 2 + b) =
      permMor X (a₀ + 2 + j + 2 + b)
          (Equiv.swap ⟨a₀, by omega⟩ ⟨a₀ + 1, by omega⟩)
        ≫ powCast X h := by
    rw [adjSwapMor_eq_permMor]
    exact powCast_permMor_swap X h ⟨a₀, by omega⟩ ⟨a₀ + 1, by omega⟩
  have hlow : permMor X (a₀ + 2 + j + 2)
        (Equiv.swap ⟨a₀, by omega⟩ ⟨a₀ + 1, by omega⟩) =
      (adjSwapMor X a₀ j ▷ X) ▷ X := by
    have hsw : (Equiv.swap (⟨a₀, by omega⟩ : Fin (a₀ + 2 + j + 2))
          ⟨a₀ + 1, by omega⟩) =
        extPerm (extPerm
          (Equiv.swap (⟨a₀, by omega⟩ : Fin (a₀ + 2 + j))
            ⟨a₀ + 1, by omega⟩)) := by
      rw [extPerm_swap, extPerm_swap]
      rfl
    rw [hsw, permMor_extPerm, permMor_extPerm, adjSwapMor_eq_permMor]
    rfl
  have hE : (tensorPowConcat X (a₀ + 2 + j + 2) b).hom ≫
      permMor X (a₀ + 2 + j + 2 + b)
        (Equiv.swap ⟨a₀, by omega⟩ ⟨a₀ + 1, by omega⟩) =
      (((adjSwapMor X a₀ j ▷ X) ▷ X) ▷ tensorPow D X b) ≫
        (tensorPowConcat X (a₀ + 2 + j + 2) b).hom := by
    have hsw : (Equiv.swap (⟨a₀, by omega⟩ : Fin (a₀ + 2 + j + 2 + b))
          ⟨a₀ + 1, by omega⟩) =
        blockEmbed
          (Equiv.swap (⟨a₀, by omega⟩ : Fin (a₀ + 2 + j + 2))
            ⟨a₀ + 1, by omega⟩) (1 : Equiv.Perm (Fin b)) := by
      rw [blockEmbed_swap_one]
      rfl
    rw [hsw, ← hlow, tensorPowConcat_permMor_fst]
    rfl
  have hM : ∀ w : (X ⊗ A) ⊗ X ⟶ X ⊗ X,
      (((tensorPow D X (a₀ + 2 + j) ◁ w) ▷ tensorPow D X b) ≫
          modPowGlue X (a₀ + 2 + j) b) ≫ powCast X h ≫
          adjSwapMor X a₀ (j + 2 + b) ≫
          modPowπ A X (a₀ + 2 + (j + 2 + b)) =
        ((adjSwapMor X a₀ j ▷ ((X ⊗ A) ⊗ X)) ▷ tensorPow D X b) ≫
          (((tensorPow D X (a₀ + 2 + j) ◁ w) ▷ tensorPow D X b) ≫
            modPowGlue X (a₀ + 2 + j) b) ≫ powCast X h ≫
          modPowπ A X (a₀ + 2 + (j + 2 + b)) := by
    intro w
    conv_lhs => rw [reassoc_of% hcast]
    rw [modPowGlue]
    simp only [Category.assoc]
    repeat' erw [Category.assoc]
    erw [reassoc_of% (ctx_below_aux A X
      (tensorPowConcat X (a₀ + 2 + j + 2) b) w
      (adjSwapMor X a₀ j) _ hE)]
  rw [modPowLegM, modPowLegN, hM (winLegM A X), hM (winLegN A X),
    ← modPowLegM, ← modPowLegN, modPow_rel A X (a₀ + 2 + j) b h]

/-! ### The three-slot window

The two overlapping cases — the braided pair sharing one module
factor with the relation slot — are compared inside a window of
three module factors.  The window morphisms below are stated on
`((X ⊗ A) ⊗ X) ⊗ X` and `X ⊗ ((X ⊗ A) ⊗ X)`, with the monoid
carried along; their identities against the slot legs are the local
content of the two cases.
-/

/-- The braiding of the two upper factors of the resolved window. -/
noncomputable def winHigh
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (X : D) :
    (X ⊗ X) ⊗ X ⟶ (X ⊗ X) ⊗ X :=
  (α_ X X X).hom ≫ (X ◁ (β_ X X).hom) ≫ (α_ X X X).inv

/-- The braiding of the two lower factors of the resolved window. -/
noncomputable def winLow
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (X : D) :
    (X ⊗ X) ⊗ X ⟶ (X ⊗ X) ⊗ X :=
  (β_ X X).hom ▷ X

/-- Exchange of the two pure module factors of a lower-relation
window, carrying nothing else along. -/
noncomputable def winTSwap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    (X : D) : ((X ⊗ A) ⊗ X) ⊗ X ⟶ ((X ⊗ A) ⊗ X) ⊗ X :=
  (α_ (X ⊗ A) X X).hom ≫ ((X ⊗ A) ◁ (β_ X X).hom) ≫
    (α_ (X ⊗ A) X X).inv

/-- From a lower-relation window to an upper-relation window: the
top module factor moves down past the flanked pair, by the braiding
against the pair. -/
noncomputable def winShiftUp
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    (X : D) : ((X ⊗ A) ⊗ X) ⊗ X ⟶ X ⊗ ((X ⊗ A) ⊗ X) :=
  ((α_ X A X).hom ▷ X) ≫ (α_ X (A ⊗ X) X).hom ≫
    (X ◁ (β_ (A ⊗ X) X).hom) ≫ (X ◁ (α_ X A X).inv)

/-- From an upper-relation window to a lower-relation window: the
bottom module factor moves up past the flanked pair. -/
noncomputable def winShiftDown
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    (X : D) : X ⊗ ((X ⊗ A) ⊗ X) ⟶ ((X ⊗ A) ⊗ X) ⊗ X :=
  (α_ X (X ⊗ A) X).inv ≫ ((β_ X (X ⊗ A)).hom ▷ X)

/-- Exchange of the two lower module factors of an upper-relation
window, across the monoid. -/
noncomputable def winNSwap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    (X : D) : X ⊗ ((X ⊗ A) ⊗ X) ⟶ X ⊗ ((X ⊗ A) ⊗ X) :=
  (α_ X (X ⊗ A) X).inv ≫
    (((α_ X X A).inv ≫ ((β_ X X).hom ▷ A) ≫ (α_ X X A).hom) ▷ X) ≫
    (α_ X (X ⊗ A) X).hom

/-- **Lower window, first leg**: the first leg passes the upper
braiding, exchanging the two untouched module factors. -/
private theorem winLegM_winHigh
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    (X : D)
    (u : X ⊗ A ⟶ X) :
    ((u ▷ X) ▷ X) ≫ winHigh X = winTSwap A X ≫ ((u ▷ X) ▷ X) := by
  rw [winHigh, winTSwap, ← Category.assoc,
    MonoidalCategory.associator_naturality_left]
  simp only [Category.assoc]
  rw [← MonoidalCategory.whisker_exchange_assoc,
    MonoidalCategory.associator_inv_naturality_left]

/-- The braiding against a pair, unwound at the swapped slot: the
hexagon against the symmetry. -/
private theorem braiding_pair_unwind
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    (X : D) :
    (β_ (A ⊗ X) X).hom ≫ (α_ X A X).inv ≫ ((β_ X A).hom ▷ X) =
      (α_ A X X).hom ≫ (A ◁ (β_ X X).hom) ≫ (α_ A X X).inv := by
  rw [BraidedCategory.braiding_tensor_left_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← MonoidalCategory.comp_whiskerRight,
    SymmetricCategory.symmetry, MonoidalCategory.id_whiskerRight,
    Category.comp_id]

/-- Conjugating an endomorphism of the two upper factors from the
lower-window bracketing to the deep bracketing. -/
private theorem shift_conj_aux
    [Category.{v} D] [MonoidalCategory D] (A : D) (X : D)
    (g : X ⊗ X ⟶ X ⊗ X) :
    (α_ (X ⊗ A) X X).hom ≫ ((X ⊗ A) ◁ g) ≫ (α_ (X ⊗ A) X X).inv ≫
        ((α_ X A X).hom ▷ X) =
      ((α_ X A X).hom ▷ X) ≫ (α_ X (A ⊗ X) X).hom ≫
        (X ◁ (α_ A X X).hom) ≫ (X ◁ (A ◁ g)) ≫
        (X ◁ (α_ A X X).inv) ≫ (α_ X (A ⊗ X) X).inv := by
  have hg : (X ⊗ A) ◁ g = (α_ X A (X ⊗ X)).hom ≫ (X ◁ (A ◁ g)) ≫
      (α_ X A (X ⊗ X)).inv := by
    rw [← MonoidalCategory.associator_naturality_right_assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hpre : (α_ (X ⊗ A) X X).hom ≫ (α_ X A (X ⊗ X)).hom =
      ((α_ X A X).hom ▷ X) ≫ (α_ X (A ⊗ X) X).hom ≫
        (X ◁ (α_ A X X).hom) := by
    monoidal
  have hpost : (α_ X A (X ⊗ X)).inv ≫ (α_ (X ⊗ A) X X).inv ≫
      ((α_ X A X).hom ▷ X) =
        (X ◁ (α_ A X X).inv) ≫ (α_ X (A ⊗ X) X).inv := by
    monoidal
  rw [hg]
  simp only [Category.assoc]
  rw [reassoc_of% hpre, hpost]

/-- **Lower window, exchanged second leg**: the exchange followed by
the second leg is the shift followed by the upper first leg. -/
private theorem winTSwap_winLegN
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] :
    winTSwap A X ≫ (winLegN A X ▷ X) =
      winShiftUp A X ≫ (X ◁ winLegM A X) ≫ (α_ X X X).inv := by
  conv_lhs => rw [winLegN, MonoidalCategory.comp_whiskerRight,
    winTSwap]
  conv_rhs => rw [winLegM, winShiftUp, actRight,
    MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [MonoidalCategory.associator_inv_naturality_middle,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [Category.assoc]
  rw [braiding_pair_unwind A X]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [← reassoc_of% (shift_conj_aux A X (β_ X X).hom)]

/-- **Lower window, second leg**: the second leg passes the upper
braiding through the shifted window's second leg. -/
private theorem winShiftUp_winLegN
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] :
    winShiftUp A X ≫ (X ◁ winLegN A X) ≫ (α_ X X X).inv =
      (winLegN A X ▷ X) ≫ winHigh X := by
  have hnat : ((X ◁ actLeft A X) ▷ X) ≫ (α_ X X X).hom ≫
      (X ◁ (β_ X X).hom) =
        (α_ X (A ⊗ X) X).hom ≫ (X ◁ (β_ (A ⊗ X) X).hom) ≫
          (X ◁ (X ◁ actLeft A X)) := by
    rw [MonoidalCategory.associator_naturality_middle_assoc,
      ← MonoidalCategory.whiskerLeft_comp,
      BraidedCategory.braiding_naturality_left,
      MonoidalCategory.whiskerLeft_comp]
  conv_rhs => rw [winLegN, winHigh,
    MonoidalCategory.comp_whiskerRight]
  have hcancel : ∀ {W : D} (f : X ⊗ (X ⊗ (A ⊗ X)) ⟶ W),
      X ◁ (α_ X A X).inv ≫ X ◁ (α_ X A X).hom ≫ f = f := by
    intro W f
    rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
      Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id,
      Category.id_comp]
  conv_lhs => rw [winShiftUp, winLegN,
    MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hnat, hcancel]

/-- **Upper window, first leg**: the shift followed by the lower
first leg is the upper first leg followed by the lower braiding. -/
private theorem winShiftDown_winLegM
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] :
    winShiftDown A X ≫ (winLegM A X ▷ X) =
      ((X ◁ winLegM A X) ≫ (α_ X X X).inv) ≫ winLow X := by
  conv_lhs => rw [winShiftDown, winLegM, Category.assoc,
    ← MonoidalCategory.comp_whiskerRight,
    ← BraidedCategory.braiding_naturality_right,
    MonoidalCategory.comp_whiskerRight]
  conv_rhs => rw [winLegM, winLow, Category.assoc,
    MonoidalCategory.associator_inv_naturality_middle_assoc]

/-- **Upper window, exchanged first leg**: the exchange followed by
the first leg is the shift followed by the lower second leg. -/
private theorem winNSwap_winLegM
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] :
    winNSwap A X ≫ (X ◁ winLegM A X) ≫ (α_ X X X).inv =
      winShiftDown A X ≫ (winLegN A X ▷ X) := by
  have hmid : (α_ X (X ⊗ A) X).hom ≫ (X ◁ ((β_ X A).hom ▷ X)) ≫
      (α_ X (A ⊗ X) X).inv = (X ◁ (β_ X A).hom) ▷ X := by
    rw [← MonoidalCategory.associator_naturality_middle_assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hPu : winNSwap A X ≫ (X ◁ ((β_ X A).hom ▷ X)) ≫
      (α_ X (A ⊗ X) X).inv =
        (α_ X (X ⊗ A) X).inv ≫ ((β_ X (X ⊗ A)).hom ▷ X) ≫
          ((α_ X A X).hom ▷ X) := by
    rw [winNSwap,
      show (β_ X (X ⊗ A)).hom = (α_ X X A).inv ≫
          ((β_ X X).hom ▷ A) ≫ (α_ X X A).hom ≫
          (X ◁ (β_ X A).hom) ≫ (α_ X A X).inv from
        BraidedCategory.braiding_tensor_right_hom X X A]
    simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
    rw [hmid,
      show (α_ X A X).inv ▷ X ≫ (α_ X A X).hom ▷ X =
          𝟙 ((X ⊗ (A ⊗ X)) ⊗ X) from by
        rw [← MonoidalCategory.comp_whiskerRight, Iso.inv_hom_id,
          MonoidalCategory.id_whiskerRight],
      Category.comp_id]
  conv_lhs => rw [winLegM, actRight,
    MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    MonoidalCategory.associator_inv_naturality_middle]
  conv_rhs => rw [winShiftDown, winLegN,
    MonoidalCategory.comp_whiskerRight]
  rw [reassoc_of% hPu]
  simp only [Category.assoc]

/-- **Upper window, second leg**: the exchange followed by the
second leg is the second leg followed by the lower braiding. -/
private theorem winNSwap_winLegN
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] :
    winNSwap A X ≫ (X ◁ winLegN A X) ≫ (α_ X X X).inv =
      ((X ◁ winLegN A X) ≫ (α_ X X X).inv) ≫ winLow X := by
  have htail : ((α_ X X A).hom ▷ X) ≫ (α_ X (X ⊗ A) X).hom ≫
      (X ◁ (α_ X A X).hom) ≫ (α_ X X (A ⊗ X)).inv =
        (α_ (X ⊗ X) A X).hom := by
    monoidal
  have hpre : (α_ X (X ⊗ A) X).inv ≫ ((α_ X X A).inv ▷ X) ≫
      (α_ (X ⊗ X) A X).hom =
        (X ◁ (α_ X A X).hom) ≫ (α_ X X (A ⊗ X)).inv := by
    monoidal
  have hkey : winNSwap A X ≫ (X ◁ (α_ X A X).hom) ≫
      (α_ X X (A ⊗ X)).inv =
        (X ◁ (α_ X A X).hom) ≫ (α_ X X (A ⊗ X)).inv ≫
          ((β_ X X).hom ▷ (A ⊗ X)) := by
    rw [winNSwap]
    simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
    rw [htail, MonoidalCategory.associator_naturality_left,
      reassoc_of% hpre]
  conv_lhs => rw [winLegN, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, MonoidalCategory.associator_inv_naturality_right]
  conv_rhs => rw [winLegN, winLow,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    Category.assoc,
    MonoidalCategory.associator_inv_naturality_right_assoc,
    MonoidalCategory.whisker_exchange]
  rw [reassoc_of% hkey]

/-! ### The three-slot frame

Both overlap cases are compared in a frame `(Xᵃ ⊗ V) ⊗ Xᑫ` around a
three-slot window `V`, glued into the ambient power through the
assembled window and the concatenation.
-/

/-- Assemble a resolved three-slot window onto the power below. -/
noncomputable def winAssemble [Category.{v} D] [MonoidalCategory D] (X : D)
    (a : ℕ) :
    tensorPow D X a ⊗ ((X ⊗ X) ⊗ X) ⟶ tensorPow D X (a + 3) :=
  (α_ (tensorPow D X a) (X ⊗ X) X).inv ≫
    ((α_ (tensorPow D X a) X X).inv ▷ X)

/-- The framed window morphism: act inside the window, assemble,
concatenate, and transport. -/
noncomputable def winFrame [Category.{v} D] [MonoidalCategory D] (X : D)
    (a q : ℕ) {n : ℕ} (h : a + 3 + q = n)
    {V : D} (u : V ⟶ (X ⊗ X) ⊗ X) :
    (tensorPow D X a ⊗ V) ⊗ tensorPow D X q ⟶ tensorPow D X n :=
  ((tensorPow D X a ◁ u) ▷ tensorPow D X q) ≫
    (winAssemble X a ▷ tensorPow D X q) ≫
    (tensorPowConcat X (a + 3) q).hom ≫ powCast X h

/-- Precomposition inside the frame. -/
theorem winFrame_pre [Category.{v} D] [MonoidalCategory D] (X : D)
    (a q : ℕ) {n : ℕ} (h : a + 3 + q = n)
    {V V' : D} (m : V' ⟶ V) (u : V ⟶ (X ⊗ X) ⊗ X) :
    winFrame X a q h (m ≫ u) =
      ((tensorPow D X a ◁ m) ▷ tensorPow D X q) ≫
        winFrame X a q h u := by
  rw [winFrame, winFrame, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.comp_whiskerRight, Category.assoc]

/-- The lower-relation mid object entering the frame. -/
noncomputable def winFromLower
    [Category.{v} D] [MonoidalCategory D] (A : D) (X : D)
    (a q : ℕ) :
    modPowMid A X a (q + 1) ≅
      (tensorPow D X a ⊗ (((X ⊗ A) ⊗ X) ⊗ X)) ⊗ tensorPow D X q :=
  whiskerLeftIso (tensorPow D X a ⊗ ((X ⊗ A) ⊗ X)) (powPeel X q) ≪≫
    (α_ (tensorPow D X a ⊗ ((X ⊗ A) ⊗ X)) X (tensorPow D X q)).symm ≪≫
    whiskerRightIso (α_ (tensorPow D X a) ((X ⊗ A) ⊗ X) X)
      (tensorPow D X q)

/-- The upper-relation mid object entering the frame. -/
noncomputable def winFromUpper
    [Category.{v} D] [MonoidalCategory D] (A : D) (X : D)
    (a q : ℕ) :
    modPowMid A X (a + 1) q ≅
      (tensorPow D X a ⊗ (X ⊗ ((X ⊗ A) ⊗ X))) ⊗ tensorPow D X q :=
  whiskerRightIso (α_ (tensorPow D X a) X ((X ⊗ A) ⊗ X))
    (tensorPow D X q)

/-- The upper legs enter the frame; at general objects. -/
private theorem frame_upper_aux [Category.{v} D] [MonoidalCategory D] (X : D)
    {P Q W N : D} (w : W ⟶ X ⊗ X)
    (C : (((P ⊗ X) ⊗ X) ⊗ X) ⊗ Q ⟶ N) :
    (((P ⊗ X) ◁ w) ▷ Q) ≫ ((α_ (P ⊗ X) X X).inv ▷ Q) ≫ C =
      ((α_ P X W).hom ▷ Q) ≫
        ((P ◁ ((X ◁ w) ≫ (α_ X X X).inv)) ▷ Q) ≫
        (((α_ P (X ⊗ X) X).inv ≫ ((α_ P X X).inv ▷ X)) ▷ Q) ≫ C := by
  have hw : (P ⊗ X) ◁ w =
      (α_ P X W).hom ≫ (P ◁ (X ◁ w)) ≫ (α_ P X (X ⊗ X)).inv := by
    rw [← MonoidalCategory.associator_naturality_right_assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hco : (α_ P X (X ⊗ X)).inv ≫ (α_ (P ⊗ X) X X).inv =
      (P ◁ (α_ X X X).inv) ≫
        ((α_ P (X ⊗ X) X).inv ≫ ((α_ P X X).inv ▷ X)) := by
    monoidal
  have hpre : ((P ⊗ X) ◁ w) ≫ (α_ (P ⊗ X) X X).inv =
      (α_ P X W).hom ≫ (P ◁ ((X ◁ w) ≫ (α_ X X X).inv)) ≫
        ((α_ P (X ⊗ X) X).inv ≫ ((α_ P X X).inv ▷ X)) := by
    rw [hw]
    simp only [Category.assoc]
    rw [hco, MonoidalCategory.whiskerLeft_comp]
    simp only [Category.assoc]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, hpre,
    MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc]

/-- The upper legs enter the frame. -/
private theorem legUpper_frame
    [Category.{v} D] [MonoidalCategory D] (A : D) (X : D)
    (a q : ℕ) {n : ℕ}
    (h12 : a + 1 + 2 + q = n) (h3 : a + 3 + q = n)
    (w : (X ⊗ A) ⊗ X ⟶ X ⊗ X) {W' : D}
    (k : tensorPow D X n ⟶ W') :
    ((tensorPow D X (a + 1) ◁ w) ▷ tensorPow D X q) ≫
        modPowGlue X (a + 1) q ≫ powCast X h12 ≫ k =
      (winFromUpper A X a q).hom ≫
        winFrame X a q h3 ((X ◁ w) ≫ (α_ X X X).inv) ≫ k := by
  have h0 := frame_upper_aux X (P := tensorPow D X a)
    (Q := tensorPow D X q) w
    ((tensorPowConcat X (a + 1 + 2) q).hom ≫ powCast X h12 ≫ k)
  simp only [modPowGlue, winFrame, winFromUpper,
    whiskerRightIso_hom, Category.assoc] at h0 ⊢
  simpa only [tensorPow, tensorPowConcat, Iso.trans_inv, whiskerRightIso_inv,
    Iso.symm_inv, winAssemble, Category.assoc] using! h0

/-- The lower legs enter the frame; at general objects, against a
peeled upper context. -/
private theorem frame_lower_aux [Category.{v} D] [MonoidalCategory D] (X : D)
    {P Q R W N : D} (w : W ⟶ X ⊗ X)
    (e : R ⟶ X ⊗ Q) (C₁ : ((P ⊗ X) ⊗ X) ⊗ R ⟶ N)
    (C₃ : (((P ⊗ X) ⊗ X) ⊗ X) ⊗ Q ⟶ N)
    (hC : C₁ = (((P ⊗ X) ⊗ X) ◁ e) ≫
      (α_ ((P ⊗ X) ⊗ X) X Q).inv ≫ C₃) :
    ((P ◁ w) ▷ R) ≫ ((α_ P X X).inv ▷ R) ≫ C₁ =
      (((P ⊗ W) ◁ e) ≫ ((α_ (P ⊗ W) X Q).inv ≫
          ((α_ P W X).hom ▷ Q))) ≫
        ((P ◁ (w ▷ X)) ▷ Q) ≫
        (((α_ P (X ⊗ X) X).inv ≫ ((α_ P X X).inv ▷ X)) ▷ Q) ≫ C₃ := by
  subst hC
  have hmid : (α_ P W X).hom ≫ (P ◁ (w ▷ X)) ≫
      (α_ P (X ⊗ X) X).inv ≫ ((α_ P X X).inv ▷ X) =
        ((P ◁ w) ▷ X) ≫ ((α_ P X X).inv ▷ X) := by
    rw [← MonoidalCategory.associator_naturality_middle_assoc,
      Iso.hom_inv_id_assoc]
  conv_lhs => rw [← MonoidalCategory.whisker_exchange_assoc,
    ← MonoidalCategory.whisker_exchange_assoc]
  conv_rhs => simp only [Category.assoc]
  conv_rhs => rw [← MonoidalCategory.comp_whiskerRight_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc]
  conv_rhs => simp only [Category.assoc]
  conv_rhs => rw [hmid]
  conv_rhs => simp only [MonoidalCategory.comp_whiskerRight,
    Category.assoc]
  conv_rhs => rw [← MonoidalCategory.associator_inv_naturality_left_assoc,
    ← MonoidalCategory.associator_inv_naturality_left_assoc]

/-- The shift instance of the lower-frame decomposition. -/
private theorem legLower_shift [Category.{v} D] [MonoidalCategory D] (X : D)
    (a q : ℕ) {n : ℕ}
    (h12 : a + 2 + (q + 1) = n) (h3 : a + 3 + q = n) :
    (tensorPowConcat X (a + 2) (q + 1)).hom ≫ powCast X h12 =
      (((tensorPow D X a ⊗ X) ⊗ X) ◁ (powPeel X q).hom) ≫
        (α_ ((tensorPow D X a ⊗ X) ⊗ X) X (tensorPow D X q)).inv ≫
        (tensorPowConcat X (a + 3) q).hom ≫ powCast X h3 := by
  rw [tensorPowConcat_peel X (a + 2) q]
  simp only [Category.assoc, powCast_comp]
  rfl

/-- The lower legs enter the frame. -/
private theorem legLower_frame
    [Category.{v} D] [MonoidalCategory D] (A : D) (X : D)
    (a q : ℕ) {n : ℕ}
    (h12 : a + 2 + (q + 1) = n) (h3 : a + 3 + q = n)
    (w : (X ⊗ A) ⊗ X ⟶ X ⊗ X) {W' : D}
    (k : tensorPow D X n ⟶ W') :
    ((tensorPow D X a ◁ w) ▷ tensorPow D X (q + 1)) ≫
        modPowGlue X a (q + 1) ≫ powCast X h12 ≫ k =
      (winFromLower A X a q).hom ≫
        winFrame X a q h3 (w ▷ X) ≫ k := by
  have hC : (tensorPowConcat X (a + 2) (q + 1)).hom ≫
      powCast X h12 ≫ k =
        (((tensorPow D X a ⊗ X) ⊗ X) ◁ (powPeel X q).hom) ≫
          (α_ ((tensorPow D X a ⊗ X) ⊗ X) X (tensorPow D X q)).inv ≫
          ((tensorPowConcat X (a + 3) q).hom ≫ powCast X h3) ≫ k := by
    rw [← Category.assoc, legLower_shift X a q h12 h3]
    exact (Category.assoc _ _ _).trans (congrArg
      (fun z => (((tensorPow D X a ⊗ X) ⊗ X) ◁ (powPeel X q).hom) ≫ z)
      (Category.assoc _ _ _))
  have h0 := frame_lower_aux X w (powPeel X q).hom
    ((tensorPowConcat X (a + 2) (q + 1)).hom ≫ powCast X h12 ≫ k)
    (((tensorPowConcat X (a + 3) q).hom ≫ powCast X h3) ≫ k) hC
  simp only [modPowGlue, winFrame, winFromLower, Iso.trans_hom,
    whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom,
    Category.assoc] at h0 ⊢
  repeat' erw [Category.assoc] at h0 ⊢
  exact h0

/-- The upper-pair braiding conjugated through the frame; at
general objects. -/
private theorem frame_swap_high_aux
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (X : D)
    {P Q N V : D}
    (u : V ⟶ (X ⊗ X) ⊗ X)
    (Ca : (((P ⊗ X) ⊗ X) ⊗ X) ⊗ Q ⟶ N)
    (Cb : (((P ⊗ X) ⊗ X) ⊗ X) ⊗ Q ≅ N) (hab : Ca = Cb.hom) :
    (((P ◁ u) ▷ Q) ≫
        (((α_ P (X ⊗ X) X).inv ≫ ((α_ P X X).inv ▷ X)) ▷ Q) ≫ Ca) ≫
      (Cb.inv ≫
        (((α_ (P ⊗ X) X X).hom ≫ ((P ⊗ X) ◁ (β_ X X).hom) ≫
          (α_ (P ⊗ X) X X).inv) ▷ Q) ≫ Cb.hom) =
    ((P ◁ (u ≫ winHigh X)) ▷ Q) ≫
      (((α_ P (X ⊗ X) X).inv ≫ ((α_ P X X).inv ▷ X)) ▷ Q) ≫ Ca := by
  subst hab
  have hcore : ((α_ P (X ⊗ X) X).inv ≫ ((α_ P X X).inv ▷ X)) ≫
      ((α_ (P ⊗ X) X X).hom ≫ ((P ⊗ X) ◁ (β_ X X).hom) ≫
        (α_ (P ⊗ X) X X).inv) =
      (P ◁ winHigh X) ≫
        ((α_ P (X ⊗ X) X).inv ≫ ((α_ P X X).inv ▷ X)) := by
    have hθ : (α_ P (X ⊗ X) X).inv ≫ ((α_ P X X).inv ▷ X) ≫
        (α_ (P ⊗ X) X X).hom =
          (P ◁ (α_ X X X).hom) ≫ (α_ P X (X ⊗ X)).inv := by
      monoidal
    have hpent : (α_ P X (X ⊗ X)).inv ≫ (α_ (P ⊗ X) X X).inv =
        (P ◁ (α_ X X X).inv) ≫ (α_ P (X ⊗ X) X).inv ≫
          ((α_ P X X).inv ▷ X) := by
      monoidal
    rw [winHigh]
    simp only [Category.assoc, MonoidalCategory.whiskerLeft_comp]
    rw [reassoc_of% hθ,
      ← MonoidalCategory.associator_inv_naturality_right_assoc,
      hpent]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← MonoidalCategory.comp_whiskerRight_assoc
      ((α_ P (X ⊗ X) X).inv ≫ ((α_ P X X).inv ▷ X)),
    hcore, MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc]
  rw [← MonoidalCategory.comp_whiskerRight_assoc (P ◁ u),
    ← MonoidalCategory.whiskerLeft_comp]

/-- The upper-pair braiding through the frame. -/
private theorem winFrame_adjSwap_high
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (X : D)
    (a q : ℕ)
    (h3 : a + 3 + q = a + 1 + 2 + q) {V : D}
    (u : V ⟶ (X ⊗ X) ⊗ X) :
    winFrame X a q h3 u ≫ adjSwapMor X (a + 1) q =
      winFrame X a q h3 (u ≫ winHigh X) := by
  have h0 := frame_swap_high_aux X (P := tensorPow D X a) u
    ((tensorPowConcat X (a + 3) q).hom ≫ powCast X h3)
    (tensorPowConcat X (a + 1 + 2) q)
    (show (tensorPowConcat X (a + 3) q).hom ≫ powCast X h3 =
        (tensorPowConcat X (a + 1 + 2) q).hom from
      Category.comp_id _)
  simp only [winFrame, winAssemble, adjSwapMor, swapTop,
    Category.assoc] at h0 ⊢
  simpa only [tensorPow, tensorPowConcat, Iso.trans_inv, whiskerRightIso_inv,
    Iso.symm_inv, winAssemble, Category.assoc] using! h0

/-- The lower-pair braiding conjugated through the frame; at
general objects, against a peeled upper context. -/
private theorem frame_swap_low_aux
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (X : D)
    {P Q R N V : D}
    (u : V ⟶ (X ⊗ X) ⊗ X) (e : R ≅ X ⊗ Q)
    (C₃ : (((P ⊗ X) ⊗ X) ⊗ X) ⊗ Q ⟶ N)
    (Cb : ((P ⊗ X) ⊗ X) ⊗ R ≅ N)
    (hCb : Cb.hom = (((P ⊗ X) ⊗ X) ◁ e.hom) ≫
      (α_ ((P ⊗ X) ⊗ X) X Q).inv ≫ C₃) :
    (((P ◁ u) ▷ Q) ≫
        (((α_ P (X ⊗ X) X).inv ≫ ((α_ P X X).inv ▷ X)) ▷ Q) ≫ C₃) ≫
      (Cb.inv ≫
        (((α_ P X X).hom ≫ (P ◁ (β_ X X).hom) ≫ (α_ P X X).inv) ▷ R)
          ≫ Cb.hom) =
    ((P ◁ (u ≫ winLow X)) ▷ Q) ≫
      (((α_ P (X ⊗ X) X).inv ≫ ((α_ P X X).inv ▷ X)) ▷ Q) ≫ C₃ := by
  have hC₃ : C₃ ≫ Cb.inv =
      (α_ ((P ⊗ X) ⊗ X) X Q).hom ≫ (((P ⊗ X) ⊗ X) ◁ e.inv) := by
    rw [Iso.comp_inv_eq, hCb]
    simp only [Category.assoc]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp,
      Iso.hom_inv_id_assoc]
  have hcore : ((α_ P (X ⊗ X) X).inv ≫ ((α_ P X X).inv ▷ X)) ≫
      (((α_ P X X).hom ≫ (P ◁ (β_ X X).hom) ≫ (α_ P X X).inv) ▷ X) =
        (P ◁ winLow X) ≫
          ((α_ P (X ⊗ X) X).inv ≫ ((α_ P X X).inv ▷ X)) := by
    conv_rhs => rw [winLow]
    simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
    rw [← MonoidalCategory.comp_whiskerRight_assoc ((α_ P X X).inv),
      Iso.inv_hom_id, MonoidalCategory.id_whiskerRight,
      Category.id_comp,
      ← MonoidalCategory.associator_inv_naturality_middle_assoc]
  simp only [Category.assoc]
  rw [reassoc_of% hC₃, MonoidalCategory.whisker_exchange_assoc, hCb,
    ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp,
    ← MonoidalCategory.associator_naturality_left_assoc,
    Iso.hom_inv_id_assoc,
    ← MonoidalCategory.comp_whiskerRight_assoc
      ((α_ P (X ⊗ X) X).inv ≫ ((α_ P X X).inv ▷ X)),
    hcore, MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc]
  rw [← MonoidalCategory.comp_whiskerRight_assoc (P ◁ u),
    ← MonoidalCategory.whiskerLeft_comp]

/-- The lower-pair braiding through the frame. -/
private theorem winFrame_adjSwap_low
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (X : D)
    (a q : ℕ)
    (h3 : a + 3 + q = a + 2 + (q + 1)) {V : D}
    (u : V ⟶ (X ⊗ X) ⊗ X) :
    winFrame X a q h3 u ≫ adjSwapMor X a (q + 1) =
      winFrame X a q h3 (u ≫ winLow X) := by
  have hCb : (tensorPowConcat X (a + 2) (q + 1)).hom =
      (((tensorPow D X a ⊗ X) ⊗ X) ◁ (powPeel X q).hom) ≫
        (α_ ((tensorPow D X a ⊗ X) ⊗ X) X (tensorPow D X q)).inv ≫
        ((tensorPowConcat X (a + 3) q).hom ≫ powCast X h3) := by
    have h0 := legLower_shift X a q
      (rfl : a + 2 + (q + 1) = a + 2 + (q + 1)) h3
    rwa [powCast_rfl, Category.comp_id] at h0
  have h0 := frame_swap_low_aux X (P := tensorPow D X a) u
    (powPeel X q)
    ((tensorPowConcat X (a + 3) q).hom ≫ powCast X h3)
    (tensorPowConcat X (a + 2) (q + 1)) hCb
  simp only [winFrame, winAssemble, adjSwapMor, swapTop,
    Category.assoc] at h0 ⊢
  simp only [tensorPow, tensorPowConcat, Iso.trans_inv,
    Iso.symm_inv,  Category.assoc] at h0 ⊢
  repeat' erw [Category.assoc] at h0
  exact h0

variable {A X} in
/-- **The overlap case, braid above**: the braided pair shares its
lower factor with the upper module factor of the relation slot. -/
private theorem adjSwap_rel_LU
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] {A : D}
    [MonObj A] {X : D} [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (a q : ℕ)
    (h : a + 2 + (q + 1) = a + 1 + 2 + q) :
    modPowLegM A X a (q + 1) ≫ powCast X h ≫
        adjSwapMor X (a + 1) q ≫ modPowπ A X (a + 1 + 2 + q) =
      modPowLegN A X a (q + 1) ≫ powCast X h ≫
        adjSwapMor X (a + 1) q ≫ modPowπ A X (a + 1 + 2 + q) := by
  have h3 : a + 3 + q = a + 1 + 2 + q := by omega
  have hbarL : winFrame X a q h3 (winLegM A X ▷ X) ≫
      modPowπ A X (a + 1 + 2 + q) =
        winFrame X a q h3 (winLegN A X ▷ X) ≫
          modPowπ A X (a + 1 + 2 + q) := by
    have hr := modPow_rel A X a (q + 1) h
    rw [modPowLegM, modPowLegN, Category.assoc, Category.assoc,
      legLower_frame A X a q h h3 (winLegM A X) (modPowπ A X _),
      legLower_frame A X a q h h3 (winLegN A X) (modPowπ A X _)]
      at hr
    exact (cancel_epi (winFromLower A X a q).hom).mp hr
  have hbarU : winFrame X a q h3
      ((X ◁ winLegM A X) ≫ (α_ X X X).inv) ≫
        modPowπ A X (a + 1 + 2 + q) =
      winFrame X a q h3 ((X ◁ winLegN A X) ≫ (α_ X X X).inv) ≫
        modPowπ A X (a + 1 + 2 + q) := by
    have hr := modPow_rel A X (a + 1) q
      (rfl : a + 1 + 2 + q = a + 1 + 2 + q)
    rw [modPowLegM, modPowLegN, Category.assoc, Category.assoc,
      legUpper_frame A X a q rfl h3 (winLegM A X) (modPowπ A X _),
      legUpper_frame A X a q rfl h3 (winLegN A X) (modPowπ A X _)]
      at hr
    exact (cancel_epi (winFromUpper A X a q).hom).mp hr
  rw [modPowLegM, modPowLegN, Category.assoc, Category.assoc,
    legLower_frame A X a q h h3 (winLegM A X)
      (adjSwapMor X (a + 1) q ≫ modPowπ A X _),
    legLower_frame A X a q h h3 (winLegN A X)
      (adjSwapMor X (a + 1) q ≫ modPowπ A X _),
    cancel_epi (winFromLower A X a q).hom,
    reassoc_of% (winFrame_adjSwap_high X a q h3 (winLegM A X ▷ X)),
    reassoc_of% (winFrame_adjSwap_high X a q h3 (winLegN A X ▷ X)),
    show (winLegM A X ▷ X) ≫ winHigh X =
        winTSwap A X ≫ (winLegM A X ▷ X) from
      winLegM_winHigh A X (actRight A X),
    winFrame_pre, Category.assoc, hbarL, ← Category.assoc,
    ← winFrame_pre, winTSwap_winLegN A X, winFrame_pre,
    Category.assoc, hbarU, ← Category.assoc, ← winFrame_pre,
    winShiftUp_winLegN A X]

variable {A X} in
/-- **The overlap case, braid below**: the braided pair shares its
upper factor with the lower module factor of the relation slot. -/
private theorem adjSwap_rel_UL
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] {A : D}
    [MonObj A] {X : D} [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (a q : ℕ)
    (h : a + 1 + 2 + q = a + 2 + (q + 1)) :
    modPowLegM A X (a + 1) q ≫ powCast X h ≫
        adjSwapMor X a (q + 1) ≫ modPowπ A X (a + 2 + (q + 1)) =
      modPowLegN A X (a + 1) q ≫ powCast X h ≫
        adjSwapMor X a (q + 1) ≫ modPowπ A X (a + 2 + (q + 1)) := by
  have h3 : a + 3 + q = a + 2 + (q + 1) := by omega
  have hbarL : winFrame X a q h3 (winLegM A X ▷ X) ≫
      modPowπ A X (a + 2 + (q + 1)) =
        winFrame X a q h3 (winLegN A X ▷ X) ≫
          modPowπ A X (a + 2 + (q + 1)) := by
    have hr := modPow_rel A X a (q + 1)
      (rfl : a + 2 + (q + 1) = a + 2 + (q + 1))
    rw [modPowLegM, modPowLegN, Category.assoc, Category.assoc,
      legLower_frame A X a q rfl h3 (winLegM A X) (modPowπ A X _),
      legLower_frame A X a q rfl h3 (winLegN A X) (modPowπ A X _)]
      at hr
    exact (cancel_epi (winFromLower A X a q).hom).mp hr
  have hbarU : winFrame X a q h3
      ((X ◁ winLegM A X) ≫ (α_ X X X).inv) ≫
        modPowπ A X (a + 2 + (q + 1)) =
      winFrame X a q h3 ((X ◁ winLegN A X) ≫ (α_ X X X).inv) ≫
        modPowπ A X (a + 2 + (q + 1)) := by
    have hr := modPow_rel A X (a + 1) q h
    rw [modPowLegM, modPowLegN, Category.assoc, Category.assoc,
      legUpper_frame A X a q h h3 (winLegM A X) (modPowπ A X _),
      legUpper_frame A X a q h h3 (winLegN A X) (modPowπ A X _)]
      at hr
    exact (cancel_epi (winFromUpper A X a q).hom).mp hr
  have hu1 : (X ◁ winLegM A X) ≫ (α_ X X X).inv ≫ winLow X =
      winShiftDown A X ≫ (winLegM A X ▷ X) := by
    rw [winShiftDown_winLegM]
    exact (Category.assoc _ _ _).symm
  have hu2b : winNSwap A X ≫ (X ◁ winLegN A X) ≫ (α_ X X X).inv =
      (X ◁ winLegN A X) ≫ (α_ X X X).inv ≫ winLow X := by
    rw [winNSwap_winLegN]
    exact Category.assoc _ _ _
  rw [modPowLegM, modPowLegN, Category.assoc, Category.assoc,
    legUpper_frame A X a q h h3 (winLegM A X)
      (adjSwapMor X a (q + 1) ≫ modPowπ A X _),
    legUpper_frame A X a q h h3 (winLegN A X)
      (adjSwapMor X a (q + 1) ≫ modPowπ A X _),
    cancel_epi (winFromUpper A X a q).hom,
    reassoc_of% (winFrame_adjSwap_low X a q h3
      ((X ◁ winLegM A X) ≫ (α_ X X X).inv)),
    reassoc_of% (winFrame_adjSwap_low X a q h3
      ((X ◁ winLegN A X) ≫ (α_ X X X).inv)),
    hu1, winFrame_pre, Category.assoc, hbarL,
    ← Category.assoc, ← winFrame_pre, ← winNSwap_winLegM A X,
    winFrame_pre, Category.assoc, hbarU, ← Category.assoc,
    ← winFrame_pre, hu2b]

variable {A X} in
/-- Descent transports along an equality of arities. -/
theorem modPowDescends_cast
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] {A : D}
    [MonObj A] {X : D} [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    {n₁ n₂ : ℕ} (h : n₁ = n₂)
    {f₁ : tensorPow D X n₁ ⟶ tensorPow D X n₁}
    {f₂ : tensorPow D X n₂ ⟶ tensorPow D X n₂}
    (hf : powCast X h ≫ f₂ = f₁ ≫ powCast X h)
    (hd : modPowDescends A X n₁ f₁) :
    modPowDescends A X n₂ f₂ := by
  subst h
  rw [powCast_rfl, Category.id_comp, Category.comp_id] at hf
  exact hf ▸ hd

variable {A X} in
/-- **Descent of the adjacent braiding**: every slot relation passes
every adjacent braiding, by the same-slot, disjoint and overlap
cases. -/
theorem modPowDescends_adjSwap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] {A : D}
    [MonObj A] {X : D} [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (a₀ b₀ : ℕ) :
    modPowDescends A X (a₀ + 2 + b₀) (adjSwapMor X a₀ b₀) := by
  intro a b hab
  rcases Nat.lt_trichotomy a a₀ with hlt | rfl | hgt
  · rcases Nat.lt_or_ge a₀ (a + 2) with h2 | h2
    · obtain rfl : a₀ = a + 1 := by omega
      obtain rfl : b = b₀ + 1 := by omega
      exact adjSwap_rel_LU a b₀ hab
    · obtain ⟨j, rfl⟩ : ∃ j, a₀ = a + 2 + j := ⟨a₀ - a - 2, by omega⟩
      obtain rfl : b = j + 2 + b₀ := by omega
      exact adjSwap_rel_above a j b₀ hab
  · obtain rfl : b = b₀ := by omega
    rw [powCast_irrel X hab rfl, powCast_rfl, Category.id_comp]
    exact adjSwap_rel_same A X a b
  · rcases Nat.lt_or_ge a (a₀ + 2) with h2 | h2
    · obtain rfl : a = a₀ + 1 := by omega
      obtain rfl : b₀ = b + 1 := by omega
      exact adjSwap_rel_UL a₀ b hab
    · obtain ⟨j, rfl⟩ : ∃ j, a = a₀ + 2 + j := ⟨a - a₀ - 2, by omega⟩
      obtain rfl : b₀ = j + 2 + b := by omega
      exact adjSwap_rel_below a₀ j b hab

variable {A X} in
/-- **Descent of the permutation action**: every slot relation
passes the action of every permutation — on the adjacent
transpositions by the case analysis, and in general by generation
and multiplicativity, exactly as the ambient action itself was
assembled. -/
theorem modPowDescends_permMor
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] {A : D}
    [MonObj A] {X : D} [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] :
    ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
      modPowDescends A X n (permMor X n σ)
  | 0, _ => fun _ _ hab => absurd hab (by omega)
  | 1, _ => fun _ _ hab => absurd hab (by omega)
  | m + 2, σ => by
    have hgen : ∀ i : Fin (m + 1),
        modPowDescends A X (m + 2)
          (permMor X (m + 2) (Equiv.swap i.castSucc i.succ)) := by
      intro i
      have he : i.val + 2 + (m - i.val) = m + 2 := by
        have := i.isLt; omega
      have hmor : powCast X he ≫
          permMor X (m + 2) (Equiv.swap i.castSucc i.succ) =
            adjSwapMor X i.val (m - i.val) ≫ powCast X he := by
        rw [adjSwapMor_eq_permMor]
        exact powCast_permMor_swap X he ⟨i.val, by omega⟩
          ⟨i.val + 1, by omega⟩
      exact modPowDescends_cast he hmor
        (modPowDescends_adjSwap i.val (m - i.val))
    have hone : modPowDescends A X (m + 2) (permMor X (m + 2) 1) := by
      intro a b hab
      rw [permMor_one]
      simpa using modPow_rel A X a b hab
    have key : ∀ τ : Equiv.Perm (Fin (m + 2)),
        τ ∈ Submonoid.closure (Set.range fun i : Fin (m + 1) =>
          Equiv.swap i.castSucc i.succ) →
        modPowDescends A X (m + 2) (permMor X (m + 2) τ) := by
      intro τ hτ
      induction hτ using Submonoid.closure_induction_left with
      | one => exact hone
      | mul_left g hg τ' hτ' ih =>
        obtain ⟨i, rfl⟩ := hg
        intro a b hab
        rw [permMor_mul]
        have hfac : permMor X (m + 2)
            (Equiv.swap i.castSucc i.succ) ≫ modPowπ A X (m + 2) =
              modPowπ A X (m + 2) ≫ modPowDesc A X
                (permMor X (m + 2) (Equiv.swap i.castSucc i.succ) ≫
                  modPowπ A X (m + 2)) (hgen i) :=
          (modPowπ_desc A X _ _).symm
        rw [Category.assoc, hfac, reassoc_of% (ih a b hab)]
    exact key σ (by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial)

variable {A X} in
/-- **The permutation action descends to the module power.** -/
noncomputable def modPowPerm
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] {A : D}
    [MonObj A] {X : D} [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    modPow A X n ⟶ modPow A X n :=
  modPowDesc A X (permMor X n σ ≫ modPowπ A X n)
    (modPowDescends_permMor n σ)

variable {A X} in
/-- Defining square of the descended action. -/
@[reassoc (attr := simp)]
theorem modPowπ_perm
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] {A : D}
    [MonObj A] {X : D} [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    modPowπ A X n ≫ modPowPerm (A := A) (X := X) n σ =
      permMor X n σ ≫ modPowπ A X n :=
  modPowπ_desc A X _ _

variable {A X} in
/-- The identity acts as the identity on the module power. -/
theorem modPowPerm_one
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] {A : D}
    [MonObj A] {X : D} [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (n : ℕ) :
    modPowPerm (A := A) (X := X) n 1 = 𝟙 (modPow A X n) := by
  apply modPow_hom_ext
  rw [modPowπ_perm, permMor_one, Category.id_comp, Category.comp_id]

variable {A X} in
/-- The descended action is functorial. -/
theorem modPowPerm_mul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] {A : D}
    [MonObj A] {X : D} [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (n : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    modPowPerm (A := A) (X := X) n (σ * τ) =
      modPowPerm (A := A) (X := X) n τ ≫
        modPowPerm (A := A) (X := X) n σ := by
  apply modPow_hom_ext
  rw [modPowπ_perm, permMor_mul, modPowπ_perm_assoc, Category.assoc,
    modPowπ_perm]

/-- **The symmetric group acting on the module power**, as a monoid
homomorphism. -/
@[simps]
noncomputable def modPowPermHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (n : ℕ) :
    Equiv.Perm (Fin n) →* End (modPow A X n) where
  toFun := modPowPerm n
  map_one' := modPowPerm_one n
  map_mul' := modPowPerm_mul n

end Descent

/-! ## The symmetriser

The trivial-character central idempotent of the group algebra
`ℂ[Sₙ]` — the `charIdempotent 1 (fun _ => 1)` of the Schur
interface, written directly.
-/

section Symmetriser

/-- **The symmetriser** `(1/n!) • ∑ σ, σ` of the symmetric-group
algebra. -/
noncomputable def symmetriser (n : ℕ) : SymGroupAlgebra n :=
  ((n.factorial : ℂ))⁻¹ •
    ∑ σ : Equiv.Perm (Fin n), MonoidAlgebra.single σ 1

/-- The symmetriser absorbs every group element on the right. -/
@[simp]
theorem symmetriser_mul_single (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    symmetriser n * MonoidAlgebra.single τ (1 : ℂ) = symmetriser n := by
  unfold symmetriser
  rw [smul_mul_assoc, Finset.sum_mul]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulRight τ) _ _ fun σ => ?_
  simp [MonoidAlgebra.single_mul_single]

/-- The symmetriser absorbs every group element on the left. -/
@[simp]
theorem single_mul_symmetriser (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    MonoidAlgebra.single τ (1 : ℂ) * symmetriser n = symmetriser n := by
  unfold symmetriser
  rw [mul_smul_comm, Finset.mul_sum]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
  simp [MonoidAlgebra.single_mul_single]

/-- **The symmetriser is idempotent.** -/
theorem symmetriser_idem (n : ℕ) :
    symmetriser n * symmetriser n = symmetriser n := by
  nth_rewrite 2 [symmetriser]
  rw [mul_smul_comm, Finset.mul_sum]
  simp only [symmetriser_mul_single, Finset.sum_const,
    Finset.card_univ]
  rw [Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (by
      exact_mod_cast n.factorial_ne_zero), one_smul]

end Symmetriser

/-! ## The group algebra on the module power, and the symmetric
power -/

section SymPow

/-- **The symmetric-group algebra acting on the module power**, the
`ℂ`-linear extension of the descended action. -/
noncomputable def modPowAlg
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) :
    SymGroupAlgebra n →ₐ[ℂ] End (modPow A X n) :=
  MonoidAlgebra.lift ℂ (End (modPow A X n)) (Equiv.Perm (Fin n))
    (modPowPermHom A X n)

/-- The algebra map sends a group element to its action. -/
@[simp]
theorem modPowAlg_single
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    modPowAlg A X n (MonoidAlgebra.single σ (1 : ℂ)) =
      modPowPerm (A := A) (X := X) n σ := by
  rw [modPowAlg, MonoidAlgebra.lift_single, one_smul]
  rfl

/-- The symmetriser acting on the module power. -/
noncomputable def symPowIdem
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) : modPow A X n ⟶ modPow A X n :=
  modPowAlg A X n (symmetriser n)

/-- The symmetriser's action is idempotent. -/
theorem symPowIdem_idem
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) :
    symPowIdem A X n ≫ symPowIdem A X n = symPowIdem A X n := by
  have h := congrArg (modPowAlg A X n) (symmetriser_idem n)
  rw [map_mul] at h
  exact h

/-- **The symmetric power**: the coinvariants of the symmetriser's
action — the coequalizer of the action against the identity.  The
idempotency splits it off as a direct summand of the module power,
with section `symPowσ`; this presentation is chosen because the
consumers of the Key Lemma build morphisms out of the symmetric
power by descent along `symPowπ` and morphisms into it through the
section. -/
noncomputable def symPow
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) : D :=
  coequalizer (symPowIdem A X n) (𝟙 (modPow A X n))

/-- The projection onto the symmetric power. -/
noncomputable def symPowπ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) : modPow A X n ⟶ symPow A X n :=
  coequalizer.π _ _

instance [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) : Epi (symPowπ A X n) :=
  inferInstanceAs (Epi (coequalizer.π _ _))

/-- The symmetriser is absorbed by the projection. -/
@[reassoc (attr := simp)]
theorem symPowIdem_π
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) :
    symPowIdem A X n ≫ symPowπ A X n = symPowπ A X n := by
  have h := coequalizer.condition (symPowIdem A X n)
    (𝟙 (modPow A X n))
  rwa [Category.id_comp] at h

/-- The section of the symmetric power, from idempotency. -/
noncomputable def symPowσ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) : symPow A X n ⟶ modPow A X n :=
  coequalizer.desc (symPowIdem A X n)
    (by rw [Category.id_comp, symPowIdem_idem])

/-- The section realises the symmetriser as projection followed by
inclusion. -/
@[reassoc (attr := simp)]
theorem symPowπ_symPowσ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) :
    symPowπ A X n ≫ symPowσ A X n = symPowIdem A X n :=
  coequalizer.π_desc _ _

/-- Morphisms out of the symmetric power are determined by their
composite with the projection. -/
theorem symPow_hom_ext
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    {n : ℕ} {W : D} {k l : symPow A X n ⟶ W}
    (h : symPowπ A X n ≫ k = symPowπ A X n ≫ l) : k = l :=
  coequalizer.hom_ext h

/-- **The symmetric power is a direct summand**: the section
followed by the projection is the identity. -/
@[reassoc (attr := simp)]
theorem symPowσ_symPowπ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (n : ℕ) :
    symPowσ A X n ≫ symPowπ A X n = 𝟙 (symPow A X n) := by
  apply symPow_hom_ext A X
  rw [← Category.assoc, symPowπ_symPowσ, symPowIdem_π,
    Category.comp_id]

/-- Descend a morphism absorbed by the symmetriser to the symmetric
power. -/
noncomputable def symPowDesc
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    {n : ℕ} {W : D} (k : modPow A X n ⟶ W)
    (h : symPowIdem A X n ≫ k = k) : symPow A X n ⟶ W :=
  coequalizer.desc k (by rw [Category.id_comp, h])

/-- The descent factors the given morphism through the
projection. -/
@[reassoc (attr := simp)]
theorem symPowπ_desc
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    {n : ℕ} {W : D} (k : modPow A X n ⟶ W)
    (h : symPowIdem A X n ≫ k = k) :
    symPowπ A X n ≫ symPowDesc A X k h = k :=
  coequalizer.π_desc _ _

end SymPow

end RS
