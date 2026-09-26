/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.OddLinePairing
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperRealize

/-!
# The Γ-algebra of a commutative monoid object

A commutative monoid object `R` of a symmetric ℂ-linear monoidal
category `D` equipped with an odd line `L` realizes as a
super-commutative ℂ-algebra (`RS.SuperCommAlgebra`): the even part
is `𝟙_ D ⟶ R`, the odd part is `L.obj ⟶ R`, and the four graded
multiplication blocks are the convolution product of the monoid
sandwiched between the coherence isomorphisms that identify the
sources.

Everything rests on one ungraded operation, `RS.gmul`: the
convolution `(a ⊗ₘ b) ≫ μ` of two morphisms into `R` at
*arbitrary* sources.  Its three structural laws — associativity up
to the associator (`RS.gmul_assoc`), the two unit laws
(`RS.gmul_one_left`, `RS.gmul_one_right`) and commutativity up to
the braiding (`RS.gmul_comm`) — hold once and for all, and each of
the thirteen axioms of `RS.SuperCommAlgebra` is one of them
conjugated by coherence isomorphisms.  The Koszul sign is the sole
place where the odd line enters: `RS.gmul_comm` produces the
self-braiding of `L.obj`, which `RS.OddLine.braid_neg` identifies
with `-𝟙`.

The odd-odd-odd associativity is the one axiom not implied by
coherence alone: it is the first triangle identity of the
self-duality of the odd line, `RS.OddLine.evaluation_coevaluation`.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory
open scoped MonObj

universe v u

/-! ## Ungraded convolution -/

section Convolution

variable {D : Type u}

/-- The *convolution product* of two morphisms into a monoid
object, taken at arbitrary sources: tensor the two morphisms and
multiply. -/
noncomputable def gmul [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R]
    {X Y : D} (a : X ⟶ R) (b : Y ⟶ R) :
    X ⊗ Y ⟶ R :=
  (a ⊗ₘ b) ≫ μ

/-- Convolution unfolded. -/
theorem gmul_def [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R]
    {X Y : D} (a : X ⟶ R) (b : Y ⟶ R) :
    gmul a b = (a ⊗ₘ b) ≫ μ[R] := rfl

/-- Reindexing the left source of a convolution. -/
theorem comp_gmul [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R]
    {W X Y : D} (f : W ⟶ X) (a : X ⟶ R)
    (b : Y ⟶ R) : gmul (f ≫ a) b = f ▷ Y ≫ gmul a b := by
  have h : f ▷ Y ≫ (a ⊗ₘ b) = (f ≫ a) ⊗ₘ b := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
  rw [gmul_def, gmul_def, ← h, Category.assoc]

/-- Reindexing the right source of a convolution. -/
theorem gmul_comp [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R]
    {X Y Z : D} (a : X ⟶ R) (g : Z ⟶ Y)
    (b : Y ⟶ R) : gmul a (g ≫ b) = X ◁ g ≫ gmul a b := by
  have h : X ◁ g ≫ (a ⊗ₘ b) = a ⊗ₘ (g ≫ b) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
  rw [gmul_def, gmul_def, ← h, Category.assoc]

/-- **Convolution is associative**, up to the associator of the
three sources. -/
theorem gmul_assoc [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R]
    {X Y Z : D} (a : X ⟶ R) (b : Y ⟶ R)
    (c : Z ⟶ R) :
    gmul (gmul a b) c = (α_ X Y Z).hom ≫ gmul a (gmul b c) := by
  have hl : ((a ⊗ₘ b) ⊗ₘ c) ≫ (μ[R] ▷ R) ≫ μ[R] =
      gmul (gmul a b) c := by
    rw [← Category.assoc, ← tensorHom_id, tensorHom_comp_tensorHom,
      Category.comp_id]
    rfl
  have hr : (a ⊗ₘ (b ⊗ₘ c)) ≫ (R ◁ μ[R]) ≫ μ[R] =
      gmul a (gmul b c) := by
    rw [← Category.assoc, ← id_tensorHom, tensorHom_comp_tensorHom,
      Category.comp_id]
    rfl
  rw [← hl, ← hr, MonObj.mul_assoc R, ← Category.assoc,
    associator_naturality, Category.assoc]

/-- The monoid unit is a left unit for convolution. -/
theorem gmul_one_left [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R]
    {Y : D} (b : Y ⟶ R) :
    gmul (η[R]) b = (λ_ Y).hom ≫ b := by
  rw [gmul_def, tensorHom_def', Category.assoc, MonObj.one_mul,
    leftUnitor_naturality]

/-- The monoid unit is a right unit for convolution. -/
theorem gmul_one_right [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R]
    {X : D} (a : X ⟶ R) :
    gmul a (η[R]) = (ρ_ X).hom ≫ a := by
  rw [gmul_def, tensorHom_def, Category.assoc, MonObj.mul_one,
    rightUnitor_naturality]

/-- **Convolution against a commutative monoid object is
commutative**, up to the braiding of the two sources. -/
theorem gmul_comm [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R]
    [BraidedCategory D] [IsCommMonObj R] {X Y : D}
    (a : X ⟶ R) (b : Y ⟶ R) :
    gmul a b = (β_ X Y).hom ≫ gmul b a := by
  rw [gmul_def, gmul_def]
  conv_lhs => rw [← IsCommMonObj.mul_comm R]
  rw [BraidedCategory.braiding_naturality_assoc]

section Additive

/-- Convolution is additive in its left argument. -/
theorem add_gmul
    [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R] [Preadditive D]
    [MonoidalPreadditive D]
    {X Y : D} (a a' : X ⟶ R) (b : Y ⟶ R) :
    gmul (a + a') b = gmul a b + gmul a' b := by
  rw [gmul_def, gmul_def, gmul_def, MonoidalPreadditive.add_tensor,
    Preadditive.add_comp]

/-- Convolution is additive in its right argument. -/
theorem gmul_add
    [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R] [Preadditive D]
    [MonoidalPreadditive D]
    {X Y : D} (a : X ⟶ R) (b b' : Y ⟶ R) :
    gmul a (b + b') = gmul a b + gmul a b' := by
  rw [gmul_def, gmul_def, gmul_def, MonoidalPreadditive.tensor_add,
    Preadditive.add_comp]

end Additive

section Homogeneous

/-- Convolution is ℂ-homogeneous in its left argument. -/
theorem smul_gmul
    [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R] [Preadditive D]
    [MonoidalPreadditive D] [Linear ℂ D] [MonoidalLinear ℂ D]
    (r : ℂ) {X Y : D} (a : X ⟶ R) (b : Y ⟶ R) :
    gmul (r • a) b = r • gmul a b := by
  have h : (r • a) ⊗ₘ b = r • (a ⊗ₘ b) := by
    rw [tensorHom_def, tensorHom_def,
      MonoidalLinear.smul_whiskerRight, Linear.smul_comp]
  rw [gmul_def, gmul_def, h, Linear.smul_comp]

/-- Convolution is ℂ-homogeneous in its right argument. -/
theorem gmul_smul
    [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R] [Preadditive D]
    [MonoidalPreadditive D] [Linear ℂ D] [MonoidalLinear ℂ D]
    (r : ℂ) {X Y : D} (a : X ⟶ R) (b : Y ⟶ R) :
    gmul a (r • b) = r • gmul a b := by
  have h : a ⊗ₘ (r • b) = r • (a ⊗ₘ b) := by
    rw [tensorHom_def', tensorHom_def',
      MonoidalLinear.whiskerLeft_smul, Linear.smul_comp]
  rw [gmul_def, gmul_def, h, Linear.smul_comp]

end Homogeneous

/-! ### The bundled bilinear convolution -/

section Bundled

/-- The convolution product as a ℂ-bilinear map of hom-modules,
transported along a chosen morphism `s` from the intended source
into the tensor product of the two given sources.  The four graded
multiplication blocks of `RS.gammaAlgebra` are the four instances
of this construction. -/
noncomputable def gmulLin
    [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R] [Preadditive D]
    [MonoidalPreadditive D] [Linear ℂ D] [MonoidalLinear ℂ D]
    {W X Y : D} (s : W ⟶ X ⊗ Y) :
    (X ⟶ R) →ₗ[ℂ] (Y ⟶ R) →ₗ[ℂ] (W ⟶ R) :=
  LinearMap.mk₂ ℂ (fun a b => s ≫ gmul a b)
    (fun a a' b => by rw [add_gmul, Preadditive.comp_add])
    (fun r a b => by rw [smul_gmul, Linear.comp_smul])
    (fun a b b' => by rw [gmul_add, Preadditive.comp_add])
    (fun r a b => by rw [gmul_smul, Linear.comp_smul])

@[simp]
theorem gmulLin_apply
    [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R] [Preadditive D]
    [MonoidalPreadditive D] [Linear ℂ D] [MonoidalLinear ℂ D]
    {W X Y : D} (s : W ⟶ X ⊗ Y) (a : X ⟶ R)
    (b : Y ⟶ R) : gmulLin s a b = s ≫ gmul a b := rfl

/-- **The transported associativity law**: given a coherence
identity between the two ways of reassociating the chosen sources,
the two bracketings of a triple convolution agree. -/
theorem gmulLin_assoc
    [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R] [Preadditive D]
    [MonoidalPreadditive D] [Linear ℂ D] [MonoidalLinear ℂ D]
    {W W' V X Y Z : D} (s₁ : W' ⟶ W ⊗ Z)
    (s₂ : W ⟶ X ⊗ Y) (s₃ : W' ⟶ X ⊗ V) (s₄ : V ⟶ Y ⊗ Z)
    (h : s₁ ≫ s₂ ▷ Z ≫ (α_ X Y Z).hom = s₃ ≫ X ◁ s₄)
    (a : X ⟶ R) (b : Y ⟶ R) (c : Z ⟶ R) :
    gmulLin s₁ (gmulLin s₂ a b) c
      = gmulLin s₃ a (gmulLin s₄ b c) := by
  simp only [gmulLin_apply]
  rw [comp_gmul, gmul_assoc, gmul_comp, reassoc_of% h]

end Bundled

end Convolution

/-! ## The super-commutative algebra of a commutative monoid -/

/-- **The Γ-algebra of a commutative monoid object**: for a
commutative monoid object `R` of a symmetric ℂ-linear monoidal
category carrying an odd line `L`, the morphisms `𝟙_ D ⟶ R` and
`L.obj ⟶ R` form a super-commutative ℂ-algebra under convolution.

The four blocks are the convolution product conjugated by the
coherence isomorphisms that identify each source with a tensor
product of the two sources involved: the left unitor for
even-even and even-odd, the right unitor for odd-even, and the
square trivialisation `L.sq` of the odd line for odd-odd.  The
Koszul sign of `comm_oo` is exactly `RS.OddLine.braid_neg`. -/
noncomputable def gammaAlgebra (D : Type u) [Category.{v} D]
    [MonoidalCategory D] [SymmetricCategory D] [Preadditive D]
    [MonoidalPreadditive D] [Linear ℂ D] [MonoidalLinear ℂ D]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] :
    SuperCommAlgebra where
  even := 𝟙_ D ⟶ R
  odd := L.obj ⟶ R
  one := η[R]
  mulEE := gmulLin (R := R) (λ_ (𝟙_ D)).inv
  mulEO := gmulLin (R := R) (λ_ L.obj).inv
  mulOE := gmulLin (R := R) (ρ_ L.obj).inv
  mulOO := gmulLin (R := R) L.sq.inv
  one_mul_e x := by
    rw [gmulLin_apply, gmul_one_left, Iso.inv_hom_id_assoc]
  one_mul_o u := by
    rw [gmulLin_apply, gmul_one_left, Iso.inv_hom_id_assoc]
  assoc_eee x y z := by
    refine gmulLin_assoc _ _ _ _ ?_ x y z
    monoidal
  assoc_eeo x y u := by
    refine gmulLin_assoc _ _ _ _ ?_ x y u
    monoidal
  assoc_eoe x u y := by
    refine gmulLin_assoc _ _ _ _ ?_ x u y
    monoidal
  assoc_eoo x u v := by
    refine gmulLin_assoc _ _ _ _ ?_ x u v
    have hc : (λ_ L.obj).inv ▷ L.obj ≫
        (α_ (𝟙_ D) L.obj L.obj).hom =
        (λ_ (L.obj ⊗ L.obj)).inv := by monoidal
    rw [hc]
    exact leftUnitor_inv_naturality L.sq.inv
  assoc_oee u x y := by
    refine gmulLin_assoc _ _ _ _ ?_ u x y
    monoidal
  assoc_oeo u x v := by
    refine gmulLin_assoc _ _ _ _ ?_ u x v
    have hc : (ρ_ L.obj).inv ▷ L.obj ≫
        (α_ L.obj (𝟙_ D) L.obj).hom =
        L.obj ◁ (λ_ L.obj).inv := by monoidal
    rw [hc]
  assoc_ooe u v y := by
    refine gmulLin_assoc _ _ _ _ ?_ u v y
    have hc : (ρ_ (L.obj ⊗ L.obj)).inv ≫
        (α_ L.obj L.obj (𝟙_ D)).hom =
        L.obj ◁ (ρ_ L.obj).inv := by monoidal
    rw [unitors_inv_equal, ← Category.assoc,
      ← rightUnitor_inv_naturality, Category.assoc, hc]
  assoc_ooo u v w := by
    refine gmulLin_assoc _ _ _ _ ?_ u v w
    have h2 : L.sq.inv ▷ L.obj ≫ (α_ L.obj L.obj L.obj).hom =
        (λ_ L.obj).hom ≫ (ρ_ L.obj).inv ≫
          L.obj ◁ L.sq.inv := by
      rw [← reassoc_of% L.evaluation_coevaluation,
        ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id,
        MonoidalCategory.whiskerLeft_id, Category.comp_id]
    rw [h2, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  comm_ee x y := by
    have hb : (λ_ (𝟙_ D)).inv ≫ (β_ (𝟙_ D) (𝟙_ D)).hom =
        (λ_ (𝟙_ D)).inv := by
      rw [← cancel_mono (ρ_ (𝟙_ D)).hom, Category.assoc,
        braiding_rightUnitor, ← unitors_equal]
    rw [gmulLin_apply, gmulLin_apply, gmul_comm x y, ← Category.assoc,
      hb]
  comm_eo x u := by
    have hb : (λ_ L.obj).inv ≫ (β_ (𝟙_ D) L.obj).hom =
        (ρ_ L.obj).inv := by
      rw [← cancel_mono (ρ_ L.obj).hom, Category.assoc,
        braiding_rightUnitor, Iso.inv_hom_id, Iso.inv_hom_id]
    rw [gmulLin_apply, gmulLin_apply, gmul_comm x u, ← Category.assoc,
      hb]
  comm_oo u v := by
    rw [gmulLin_apply, gmulLin_apply, gmul_comm u v, L.braid_neg,
      Preadditive.neg_comp, Category.id_comp,
      Preadditive.comp_neg]

end RS
