/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperSmall

/-!
# The four-block Γ-algebra of a commutative monoid at an odd line

`RS.SuperRealize` supplies the even half of the §4 monoid
transport: the convolution product `unitHomMul` making `𝟙_ D ⟶ R`
a commutative ℂ-algebra for a commutative monoid object `R`.  This
file supplies the full super-commutative algebra.  Fix an *odd
line* `o : D`: an object with a chosen trivialization
`ho : o ⊗ o ≅ 𝟙_ D` on which the braiding acts by `-1`.  The four
graded blocks of `R`-valued points are

* even = `𝟙_ D ⟶ R` and odd = `o ⟶ R` — the `o ⟶ R` form is
  chosen over `𝟙_ D ⟶ o ⊗ R` because the odd-odd product then
  pairs the two source copies of `o` directly through `ho`;
* `EE` = convolution through `(λ_ (𝟙_ D)).inv` (definitionally
  the existing `unitHomMul`);
* `EO` = convolution through `(λ_ o).inv`;
* `OE` = convolution through `(ρ_ o).inv`;
* `OO` = convolution through `ho.inv`.

All four are instances of a single construction, *convolution
along a prefix*: `convAlong R p f g = p ≫ (f ⊗ₘ g) ≫ μ` for a
chosen `p : A ⟶ X ⊗ Y`.  Associativity holds once and for all
(`convAlong_assoc`) given a single coherence identity relating the
four prefixes involved; the eight parity associativities are the
eight instantiations.  Seven of the eight coherence residues are
consequences of monoidal coherence and the naturality of the
unitors; the eighth — the odd-odd-odd pattern — genuinely compares
the two ways of trivializing one factor of `o ⊗ o ⊗ o` through
`ho` and is *not* a formal consequence of the data `(ho, hβ)`.  It
is stated as the hypothesis `hα` of
`superGammaAlgebra`; it holds in super vector spaces (both sides
are `x ↦ e ⊗ e ⊗ x`-type maps for a basis vector `e` of the odd
line) and more generally whenever `ho` is a coherent
self-duality.

Commutativity likewise holds once (`convAlong_braid`, from the
commutativity of `μ` and the naturality of the braiding); the
even-even and even-odd patterns follow from the unit braiding
identities, and the odd-odd pattern picks up the Koszul sign from
`hβ`.  The package `superGammaAlgebra` assembles the blocks into
an `RS.SuperCommAlgebra`, feeding the odd-nil quotient theory of
`RS.SuperRealize`.
-/

@[expose] public section

namespace RS

noncomputable section

open CategoryTheory MonoidalCategory MonObj
open scoped MonObj

universe u u'

variable {D : Type u}

/-! ## Convolution along a prefix -/

section ConvAlong

/-- *Convolution along a prefix*: for a monoid object `R` and a
chosen morphism `p : A ⟶ X ⊗ Y`, the pairing sending
`f : X ⟶ R` and `g : Y ⟶ R` to `p ≫ (f ⊗ₘ g) ≫ μ : A ⟶ R`.
All four graded multiplication blocks of the Γ-algebra at an odd
line are instances, at the prefixes `(λ_ (𝟙_ D)).inv`,
`(λ_ o).inv`, `(ρ_ o).inv` and `ho.inv`. -/
def convAlong [Category.{u'} D] [MonoidalCategory D] (R : D) [MonObj R]
    {A X Y : D} (p : A ⟶ X ⊗ Y)
    (f : X ⟶ R) (g : Y ⟶ R) : A ⟶ R :=
  p ≫ (f ⊗ₘ g) ≫ μ

/-- The monoid unit is a left unit for convolution along a left
unitor prefix. -/
theorem convAlong_one_left
    [Category.{u'} D] [MonoidalCategory D] (R : D) [MonObj R]
    {Z : D} (x : Z ⟶ R) :
    convAlong R (λ_ Z).inv η x = x := by
  rw [convAlong, MonObj.one_mul_hom, Iso.inv_hom_id_assoc]

/-- **Generic associativity of prefixed convolution.**  Given
inner and outer prefixes on each side whose two composites into
`X ⊗ Y ⊗ Z` agree (`hpq`), the two iterated convolutions agree.
The eight parity associativities of the Γ-algebra are the eight
instantiations, with `hpq` a coherence residue in each case. -/
theorem convAlong_assoc
    [Category.{u'} D] [MonoidalCategory D] (R : D) [MonObj R]
    {B A A' X Y Z : D}
    (q : B ⟶ A ⊗ Z) (p : A ⟶ X ⊗ Y)
    (q' : B ⟶ X ⊗ A') (p' : A' ⟶ Y ⊗ Z)
    (hpq : q ≫ p ▷ Z ≫ (α_ X Y Z).hom = q' ≫ X ◁ p')
    (f : X ⟶ R) (g : Y ⟶ R) (h : Z ⟶ R) :
    convAlong R q (convAlong R p f g) h =
      convAlong R q' f (convAlong R p' g h) := by
  have hL : convAlong R q (convAlong R p f g) h =
      q ≫ p ▷ Z ≫ (α_ X Y Z).hom ≫ (f ⊗ₘ (g ⊗ₘ h)) ≫
        R ◁ μ ≫ μ := by
    rw [convAlong, convAlong, tensorHom_def (p ≫ (f ⊗ₘ g) ≫ μ) h]
    simp only [comp_whiskerRight, Category.assoc]
    rw [← whisker_exchange_assoc, ← tensorHom_def_assoc,
      MonObj.mul_assoc, associator_naturality_assoc]
  have hR : convAlong R q' f (convAlong R p' g h) =
      q' ≫ X ◁ p' ≫ (f ⊗ₘ (g ⊗ₘ h)) ≫ R ◁ μ ≫ μ := by
    rw [convAlong, convAlong,
      tensorHom_def' f (p' ≫ (g ⊗ₘ h) ≫ μ)]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [whisker_exchange_assoc, ← tensorHom_def'_assoc]
  rw [hL, hR, reassoc_of% hpq]

/-- **Generic commutativity of prefixed convolution** against a
commutative monoid object: exchanging the two arguments costs
composing the prefix with the braiding.  The Koszul signs of the
Γ-algebra arise from evaluating the braiding on the prefixes. -/
theorem convAlong_braid
    [Category.{u'} D] [MonoidalCategory D] (R : D) [MonObj R]
    [BraidedCategory D] [IsCommMonObj R]
    {A X Y : D} (p : A ⟶ X ⊗ Y) (f : X ⟶ R) (g : Y ⟶ R) :
    convAlong R p f g = convAlong R (p ≫ (β_ X Y).hom) g f := by
  simp only [convAlong, Category.assoc]
  conv_lhs => rw [← IsCommMonObj.mul_comm R]
  rw [BraidedCategory.braiding_naturality_assoc]

/-- Even-even commutativity: at the unit prefix the braiding
correction collapses through the unit braiding identities. -/
theorem convAlong_ee_comm
    [Category.{u'} D] [MonoidalCategory D] (R : D) [MonObj R]
    [BraidedCategory D] [IsCommMonObj R]
    (a b : 𝟙_ D ⟶ R) :
    convAlong R (λ_ (𝟙_ D)).inv a b =
      convAlong R (λ_ (𝟙_ D)).inv b a := by
  rw [convAlong_braid R (λ_ (𝟙_ D)).inv a b,
    braiding_tensorUnit_left, Iso.inv_hom_id_assoc,
    ← unitors_inv_equal]

/-- Even-odd commutativity: the braiding against the unit turns
the left unitor prefix into the right unitor prefix, with no
sign. -/
theorem convAlong_eo_comm
    [Category.{u'} D] [MonoidalCategory D] (R : D) [MonObj R]
    [BraidedCategory D] [IsCommMonObj R]
    {o : D} (a : 𝟙_ D ⟶ R) (x : o ⟶ R) :
    convAlong R (λ_ o).inv a x = convAlong R (ρ_ o).inv x a := by
  rw [convAlong_braid R (ρ_ o).inv x a, braiding_tensorUnit_right,
    Iso.inv_hom_id_assoc]

end ConvAlong

/-! ## Bilinearity -/

section Bilinear

/-- Prefixed convolution is additive in the left argument. -/
theorem convAlong_add_left
    [Category.{u'} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] (R : D) [MonObj R]
    {A X Y : D} (p : A ⟶ X ⊗ Y)
    (f f' : X ⟶ R) (g : Y ⟶ R) :
    convAlong R p (f + f') g =
      convAlong R p f g + convAlong R p f' g := by
  rw [convAlong, convAlong, convAlong,
    MonoidalPreadditive.add_tensor, Preadditive.add_comp,
    Preadditive.comp_add]

/-- Prefixed convolution is additive in the right argument. -/
theorem convAlong_add_right
    [Category.{u'} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] (R : D) [MonObj R]
    {A X Y : D} (p : A ⟶ X ⊗ Y)
    (f : X ⟶ R) (g g' : Y ⟶ R) :
    convAlong R p f (g + g') =
      convAlong R p f g + convAlong R p f g' := by
  rw [convAlong, convAlong, convAlong,
    MonoidalPreadditive.tensor_add, Preadditive.add_comp,
    Preadditive.comp_add]

/-- **Odd-odd anticommutativity.**  At a trivialization prefix
`ho.inv` on whose source the braiding acts by `-1`, exchanging the
arguments of prefixed convolution costs the Koszul sign. -/
theorem convAlong_oo_comm
    [Category.{u'} D] [MonoidalCategory D] [Preadditive D] (R : D)
    [MonObj R]
    [BraidedCategory D] [IsCommMonObj R]
    {o : D} (ho : o ⊗ o ≅ 𝟙_ D)
    (hβ : (β_ o o).hom = -𝟙 (o ⊗ o)) (x y : o ⟶ R) :
    convAlong R ho.inv x y = -convAlong R ho.inv y x := by
  rw [convAlong_braid R ho.inv x y, hβ, convAlong, convAlong,
    Preadditive.comp_neg, Category.comp_id, Preadditive.neg_comp]

/-- Prefixed convolution is ℂ-homogeneous in the left argument. -/
theorem convAlong_smul_left
    [Category.{u'} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] (R : D) [MonObj R] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    {A X Y : D} (p : A ⟶ X ⊗ Y) (r : ℂ)
    (f : X ⟶ R) (g : Y ⟶ R) :
    convAlong R p (r • f) g = r • convAlong R p f g := by
  have h : (r • f) ⊗ₘ g = r • (f ⊗ₘ g) := by
    rw [tensorHom_def, tensorHom_def,
      MonoidalLinear.smul_whiskerRight, Linear.smul_comp]
  rw [convAlong, convAlong, h, Linear.smul_comp, Linear.comp_smul]

/-- Prefixed convolution is ℂ-homogeneous in the right
argument. -/
theorem convAlong_smul_right
    [Category.{u'} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] (R : D) [MonObj R] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    {A X Y : D} (p : A ⟶ X ⊗ Y) (r : ℂ)
    (f : X ⟶ R) (g : Y ⟶ R) :
    convAlong R p f (r • g) = r • convAlong R p f g := by
  have h : f ⊗ₘ (r • g) = r • (f ⊗ₘ g) := by
    rw [tensorHom_def', tensorHom_def',
      MonoidalLinear.whiskerLeft_smul, Linear.smul_comp]
  rw [convAlong, convAlong, h, Linear.smul_comp, Linear.comp_smul]

/-- Prefixed convolution packaged as a ℂ-bilinear map on hom
ℂ-modules. -/
def convAlongHom [Category.{u'} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] (R : D) [MonObj R] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    {A X Y : D} (p : A ⟶ X ⊗ Y) :
    (X ⟶ R) →ₗ[ℂ] (Y ⟶ R) →ₗ[ℂ] (A ⟶ R) :=
  LinearMap.mk₂ ℂ (convAlong R p)
    (convAlong_add_left R p)
    (fun r f g => convAlong_smul_left R p r f g)
    (convAlong_add_right R p)
    (fun r f g => convAlong_smul_right R p r f g)

/-- Application of the packaged bilinear map is prefixed
convolution. -/
@[simp] theorem convAlongHom_apply
    [Category.{u'} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] (R : D) [MonObj R] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    {A X Y : D} (p : A ⟶ X ⊗ Y)
    (f : X ⟶ R) (g : Y ⟶ R) :
    convAlongHom R p f g = convAlong R p f g := rfl

end Bilinear

/-! ## The Γ-algebra at an odd line -/

section Residues

/-- The even-odd-odd coherence residue: trivializing `o ⊗ o` after
inserting a unit on the left agrees with inserting the
trivialized unit directly.  Naturality of the left unitor. -/
private theorem residue_eoo [Category.{u'} D] [MonoidalCategory D] {o : D}
    (ho : o ⊗ o ≅ 𝟙_ D) :
    ho.inv ≫ (λ_ o).inv ▷ o ≫ (α_ (𝟙_ D) o o).hom =
      (λ_ (𝟙_ D)).inv ≫ 𝟙_ D ◁ ho.inv := by
  rw [← leftUnitor_tensor_inv, leftUnitor_inv_naturality]

/-- The odd-odd-even coherence residue: trivializing `o ⊗ o`
before inserting a unit on the right agrees with inserting the
unit inside.  Naturality of the right unitor. -/
private theorem residue_ooe [Category.{u'} D] [MonoidalCategory D] {o : D}
    (ho : o ⊗ o ≅ 𝟙_ D) :
    (λ_ (𝟙_ D)).inv ≫ ho.inv ▷ 𝟙_ D ≫ (α_ o o (𝟙_ D)).hom =
      ho.inv ≫ o ◁ (ρ_ o).inv := by
  rw [unitors_inv_equal, ← rightUnitor_inv_naturality_assoc,
    rightUnitor_tensor_inv]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Residues

section OddLine

/-- **The four-block Γ-algebra of a commutative monoid object at
an odd line.**  For a commutative monoid object `R` of a braided
ℂ-linear monoidal category and an odd line `o` — an object with a
trivialization `ho : o ⊗ o ≅ 𝟙_ D` on which the braiding acts by
`-1` (`hβ`) and which is associativity-coherent (`hα`: the two
insertions of `ho.inv` into `o` agree through the associator) —
the morphisms `𝟙_ D ⟶ R` and `o ⟶ R` form a super-commutative
ℂ-algebra under prefixed convolution.  The even block is the
convolution algebra of `RS.SuperRealize`; the odd-odd block pairs
the sources through `ho` and anticommutes by `hβ`.

The hypothesis `hα` is not a formal consequence of `(ho, hβ)`: it
pins down the compatibility of the chosen trivialization with the
associator, and holds for the standard odd line of super vector
spaces (hence in `Ind SmallSuperVect`). -/
def superGammaAlgebra [Category.{u'} D] [MonoidalCategory D] [BraidedCategory D]
    [Preadditive D] [MonoidalPreadditive D] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D] (R : D) [MonObj R] [IsCommMonObj R]
    (o : D) (ho : o ⊗ o ≅ 𝟙_ D)
    (hβ : (β_ o o).hom = -𝟙 (o ⊗ o))
    (hα : (λ_ o).inv ≫ ho.inv ▷ o ≫ (α_ o o o).hom =
      (ρ_ o).inv ≫ o ◁ ho.inv) :
    SuperCommAlgebra where
  even := 𝟙_ D ⟶ R
  odd := o ⟶ R
  one := η
  mulEE := convAlongHom R (λ_ (𝟙_ D)).inv
  mulEO := convAlongHom R (λ_ o).inv
  mulOE := convAlongHom R (ρ_ o).inv
  mulOO := convAlongHom R ho.inv
  one_mul_e := fun x => by
    change convAlong R (λ_ (𝟙_ D)).inv η x = x
    exact convAlong_one_left R x
  one_mul_o := fun u => by
    change convAlong R (λ_ o).inv η u = u
    exact convAlong_one_left R u
  assoc_eee := fun x y z => by
    change convAlong R (λ_ (𝟙_ D)).inv
        (convAlong R (λ_ (𝟙_ D)).inv x y) z =
      convAlong R (λ_ (𝟙_ D)).inv x
        (convAlong R (λ_ (𝟙_ D)).inv y z)
    exact convAlong_assoc R _ _ _ _ (by monoidal) x y z
  assoc_eeo := fun x y u => by
    change convAlong R (λ_ o).inv
        (convAlong R (λ_ (𝟙_ D)).inv x y) u =
      convAlong R (λ_ o).inv x (convAlong R (λ_ o).inv y u)
    exact convAlong_assoc R _ _ _ _ (by monoidal) x y u
  assoc_eoe := fun x u y => by
    change convAlong R (ρ_ o).inv
        (convAlong R (λ_ o).inv x u) y =
      convAlong R (λ_ o).inv x (convAlong R (ρ_ o).inv u y)
    exact convAlong_assoc R _ _ _ _ (by monoidal) x u y
  assoc_eoo := fun x u v => by
    change convAlong R ho.inv (convAlong R (λ_ o).inv x u) v =
      convAlong R (λ_ (𝟙_ D)).inv x (convAlong R ho.inv u v)
    exact convAlong_assoc R _ _ _ _ (residue_eoo ho) x u v
  assoc_oee := fun u x y => by
    change convAlong R (ρ_ o).inv
        (convAlong R (ρ_ o).inv u x) y =
      convAlong R (ρ_ o).inv u
        (convAlong R (λ_ (𝟙_ D)).inv x y)
    exact convAlong_assoc R _ _ _ _ (by monoidal) u x y
  assoc_oeo := fun u x v => by
    change convAlong R ho.inv (convAlong R (ρ_ o).inv u x) v =
      convAlong R ho.inv u (convAlong R (λ_ o).inv x v)
    exact convAlong_assoc R _ _ _ _ (by monoidal) u x v
  assoc_ooe := fun u v y => by
    change convAlong R (λ_ (𝟙_ D)).inv
        (convAlong R ho.inv u v) y =
      convAlong R ho.inv u (convAlong R (ρ_ o).inv v y)
    exact convAlong_assoc R _ _ _ _ (residue_ooe ho) u v y
  assoc_ooo := fun u v w => by
    change convAlong R (λ_ o).inv (convAlong R ho.inv u v) w =
      convAlong R (ρ_ o).inv u (convAlong R ho.inv v w)
    exact convAlong_assoc R _ _ _ _ hα u v w
  comm_ee := fun x y => by
    change convAlong R (λ_ (𝟙_ D)).inv x y =
      convAlong R (λ_ (𝟙_ D)).inv y x
    exact convAlong_ee_comm R x y
  comm_eo := fun x u => by
    change convAlong R (λ_ o).inv x u = convAlong R (ρ_ o).inv u x
    exact convAlong_eo_comm R x u
  comm_oo := fun u v => by
    change convAlong R ho.inv u v = -convAlong R ho.inv v u
    exact convAlong_oo_comm R ho hβ u v

end OddLine

/-!
## Instantiation notes: `D := Ind SmallSuperVect`

Applying `superGammaAlgebra` over the intended ind-completion
requires the following instance stack on `Ind SmallSuperVect`
(not assembled here; recorded for the instantiation lane):

* `Preadditive (Ind SmallSuperVect)` and the ℂ-linear structure —
  the tree's route is through `RS.ScalarLinear` (linearity of a
  preadditive category over the scalars of its unit
  endomorphisms) rather than a direct Day-convolution transport;
* the monoidal structure and its braiding on the ind-completion —
  `RS.IndMonoidal` / `RS.ScalarBraiding` layer, with
  `MonoidalPreadditive` and `MonoidalLinear ℂ` verified against
  the transported tensor;
* the odd line: `o := indOf sOdd`, with `ho` induced by the
  isomorphism `sOdd ⊗ sOdd ≅ sEven ≅ 𝟙` of `RS.SuperSmall`
  (`sEvenIso` after the embedding), `hβ` from the sign of the
  super braiding on the odd generator, and `hα` by evaluating
  both sides on the one-dimensional odd line;
* the monoid object `R` supplied by the §4 descent, with
  `IsCommMonObj R` from commutativity of the transported
  multiplication.
-/

end

end RS
