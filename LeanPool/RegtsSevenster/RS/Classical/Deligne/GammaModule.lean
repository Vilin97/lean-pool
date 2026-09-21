/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaAlgebra

/-!
# The Γ-module of a module object

A module object `M` over a commutative monoid object `R` of a
symmetric ℂ-linear monoidal category with an odd line `L` realizes
as a module over the super-commutative ℂ-algebra
`RS.gammaAlgebra D L R`: the even part is `𝟙_ D ⟶ M`, the odd part
is `L.obj ⟶ M`, and the four graded action blocks are the
convolution of the internal action sandwiched between the same
coherence isomorphisms that identify the sources in
`RS.gammaAlgebra`.

The pattern of `RS.GammaAlgebra` repeats one level down.
Everything rests on a single ungraded operation, `RS.gact`: the
convolution `(a ⊗ₘ m) ≫ γ` of a morphism into `R` against a
morphism into `M`, at *arbitrary* sources.  Its two structural
laws — associativity against `RS.gmul` up to the associator
(`RS.gact_assoc`) and the unit law (`RS.gact_one`) — hold once and
for all, and each of the ten axioms of `RS.SuperCommAlgebra.Mod`
is one of them conjugated by coherence isomorphisms.

There is no commutativity axiom for a module, so the odd line
enters only through the source identification `L.sq` of the
odd-odd block; as in the algebra, the odd-odd-odd associativity is
the one axiom not implied by coherence alone, and it is again the
first triangle identity of the self-duality of the odd line,
`RS.OddLine.evaluation_coevaluation`.
-/

namespace RS

open CategoryTheory MonoidalCategory
open scoped MonObj

universe v u u' w w'

/-! ## Modules over a super-commutative ℂ-algebra -/

/-- A *module* over a super-commutative ℂ-algebra, presented as a
pair of ℂ-modules — the even and odd components — with the four
graded action blocks, the two unit laws and associativity at every
parity pattern of a scalar pair acting on a module element.

The blocks are indexed by the parities of the two algebra
arguments and of the module argument, and the parity of the value
is their sum: `assoc_xyz` says that acting by the product of an
`x`-parity and a `y`-parity scalar is acting by the second and
then by the first. -/
-- `w` and `w'` are the universes of the even and odd components:
-- independent by design, and the structure is a pair, so they can
-- only ever occur together in its type.
structure SuperCommAlgebra.Mod (S : SuperCommAlgebra.{u, u'}) where
  /-- The even component. -/
  even : Type w
  /-- The odd component. -/
  odd : Type w'
  [evenAddCommGroup : AddCommGroup even]
  [evenModule : Module ℂ even]
  [oddAddCommGroup : AddCommGroup odd]
  [oddModule : Module ℂ odd]
  /-- The action of an even scalar on an even element. -/
  actEE : S.even →ₗ[ℂ] even →ₗ[ℂ] even
  /-- The action of an even scalar on an odd element. -/
  actEO : S.even →ₗ[ℂ] odd →ₗ[ℂ] odd
  /-- The action of an odd scalar on an even element. -/
  actOE : S.odd →ₗ[ℂ] even →ₗ[ℂ] odd
  /-- The action of an odd scalar on an odd element. -/
  actOO : S.odd →ₗ[ℂ] odd →ₗ[ℂ] even
  /-- The unit acts as the identity on the even component. -/
  one_act_e : ∀ m, actEE S.one m = m
  /-- The unit acts as the identity on the odd component. -/
  one_act_o : ∀ m, actEO S.one m = m
  /-- Associativity at parity pattern even-even-even. -/
  assoc_eee : ∀ x y m, actEE (S.mulEE x y) m = actEE x (actEE y m)
  /-- Associativity at parity pattern even-even-odd. -/
  assoc_eeo : ∀ x y m, actEO (S.mulEE x y) m = actEO x (actEO y m)
  /-- Associativity at parity pattern even-odd-even. -/
  assoc_eoe : ∀ x u m, actOE (S.mulEO x u) m = actEO x (actOE u m)
  /-- Associativity at parity pattern even-odd-odd. -/
  assoc_eoo : ∀ x u m, actOO (S.mulEO x u) m = actEE x (actOO u m)
  /-- Associativity at parity pattern odd-even-even. -/
  assoc_oee : ∀ u x m, actOE (S.mulOE u x) m = actOE u (actEE x m)
  /-- Associativity at parity pattern odd-even-odd. -/
  assoc_oeo : ∀ u x m, actOO (S.mulOE u x) m = actOO u (actEO x m)
  /-- Associativity at parity pattern odd-odd-even. -/
  assoc_ooe : ∀ u v m, actEE (S.mulOO u v) m = actOO u (actOE v m)
  /-- Associativity at parity pattern odd-odd-odd. -/
  assoc_ooo : ∀ u v m, actEO (S.mulOO u v) m = actOE u (actOO v m)

attribute [instance] SuperCommAlgebra.Mod.evenAddCommGroup
  SuperCommAlgebra.Mod.evenModule
  SuperCommAlgebra.Mod.oddAddCommGroup
  SuperCommAlgebra.Mod.oddModule

/-! ## Ungraded convolution against a module object -/

section Action

variable {D : Type u}

/-- The *convolution action* of a morphism into a monoid object on
a morphism into a module object, taken at arbitrary sources:
tensor the two morphisms and act. -/
noncomputable def gact
    [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R] {M : D}
    [ModObj R M]
    {X Y : D} (a : X ⟶ R) (m : Y ⟶ M) :
    X ⊗ Y ⟶ M :=
  (a ⊗ₘ m) ≫ actLeft R M

/-- The convolution action unfolded. -/
theorem gact_def
    [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R] {M : D}
    [ModObj R M]
    {X Y : D} (a : X ⟶ R) (m : Y ⟶ M) :
    gact a m = (a ⊗ₘ m) ≫ actLeft R M := rfl

/-- Reindexing the scalar source of a convolution action. -/
theorem comp_gact
    [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R] {M : D}
    [ModObj R M]
    {W X Y : D} (f : W ⟶ X) (a : X ⟶ R)
    (m : Y ⟶ M) : gact (f ≫ a) m = f ▷ Y ≫ gact a m := by
  have h : f ▷ Y ≫ (a ⊗ₘ m) = (f ≫ a) ⊗ₘ m := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
  rw [gact_def, gact_def, ← h, Category.assoc]

/-- Reindexing the module source of a convolution action. -/
theorem gact_comp
    [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R] {M : D}
    [ModObj R M]
    {X Y Z : D} (a : X ⟶ R) (g : Z ⟶ Y)
    (m : Y ⟶ M) : gact a (g ≫ m) = X ◁ g ≫ gact a m := by
  have h : X ◁ g ≫ (a ⊗ₘ m) = a ⊗ₘ (g ≫ m) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
  rw [gact_def, gact_def, ← h, Category.assoc]

/-- **The convolution action is associative** against the
convolution product, up to the associator of the three sources. -/
theorem gact_assoc
    [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R] {M : D}
    [ModObj R M]
    {X Y Z : D} (a : X ⟶ R) (b : Y ⟶ R)
    (m : Z ⟶ M) :
    gact (gmul a b) m = (α_ X Y Z).hom ≫ gact a (gact b m) := by
  have hl : ((a ⊗ₘ b) ⊗ₘ m) ≫ (μ[R] ▷ M) ≫ actLeft R M =
      gact (gmul a b) m := by
    rw [← Category.assoc, ← tensorHom_id, tensorHom_comp_tensorHom,
      Category.comp_id]
    rfl
  have hr : (a ⊗ₘ (b ⊗ₘ m)) ≫ (R ◁ actLeft R M) ≫ actLeft R M =
      gact a (gact b m) := by
    rw [← Category.assoc, ← id_tensorHom, tensorHom_comp_tensorHom,
      Category.comp_id]
    rfl
  rw [← hl, ← hr, mul_actLeft R M, ← Category.assoc,
    associator_naturality, Category.assoc]

/-- The monoid unit acts as the identity. -/
theorem gact_one
    [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R] {M : D}
    [ModObj R M]
    {Y : D} (m : Y ⟶ M) :
    gact (η[R]) m = (λ_ Y).hom ≫ m := by
  rw [gact_def, tensorHom_def', Category.assoc, one_actLeft,
    leftUnitor_naturality]

section Additive

/-- The convolution action is additive in its scalar argument. -/
theorem add_gact
    [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R] {M : D}
    [ModObj R M] [Preadditive D] [MonoidalPreadditive D]
    {X Y : D} (a a' : X ⟶ R) (m : Y ⟶ M) :
    gact (a + a') m = gact a m + gact a' m := by
  rw [gact_def, gact_def, gact_def, MonoidalPreadditive.add_tensor,
    Preadditive.add_comp]

/-- The convolution action is additive in its module argument. -/
theorem gact_add
    [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R] {M : D}
    [ModObj R M] [Preadditive D] [MonoidalPreadditive D]
    {X Y : D} (a : X ⟶ R) (m m' : Y ⟶ M) :
    gact a (m + m') = gact a m + gact a m' := by
  rw [gact_def, gact_def, gact_def, MonoidalPreadditive.tensor_add,
    Preadditive.add_comp]

end Additive

section Homogeneous

/-- The convolution action is ℂ-homogeneous in its scalar
argument. -/
theorem smul_gact
    [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R] {M : D}
    [ModObj R M] [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    (r : ℂ) {X Y : D} (a : X ⟶ R) (m : Y ⟶ M) :
    gact (r • a) m = r • gact a m := by
  have h : (r • a) ⊗ₘ m = r • (a ⊗ₘ m) := by
    rw [tensorHom_def, tensorHom_def,
      MonoidalLinear.smul_whiskerRight, Linear.smul_comp]
  rw [gact_def, gact_def, h, Linear.smul_comp]

/-- The convolution action is ℂ-homogeneous in its module
argument. -/
theorem gact_smul
    [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R] {M : D}
    [ModObj R M] [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    (r : ℂ) {X Y : D} (a : X ⟶ R) (m : Y ⟶ M) :
    gact a (r • m) = r • gact a m := by
  have h : a ⊗ₘ (r • m) = r • (a ⊗ₘ m) := by
    rw [tensorHom_def', tensorHom_def',
      MonoidalLinear.whiskerLeft_smul, Linear.smul_comp]
  rw [gact_def, gact_def, h, Linear.smul_comp]

end Homogeneous

/-! ### The bundled bilinear convolution action -/

section Bundled

/-- The convolution action as a ℂ-bilinear map of hom-modules,
transported along a chosen morphism `s` from the intended source
into the tensor product of the two given sources.  The four graded
action blocks of `RS.gammaModule` are the four instances of this
construction. -/
noncomputable def gactLin
    [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R] {M : D}
    [ModObj R M] [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    {W X Y : D} (s : W ⟶ X ⊗ Y) :
    (X ⟶ R) →ₗ[ℂ] (Y ⟶ M) →ₗ[ℂ] (W ⟶ M) :=
  LinearMap.mk₂ ℂ (fun a m => s ≫ gact a m)
    (fun a a' m => by rw [add_gact, Preadditive.comp_add])
    (fun r a m => by rw [smul_gact, Linear.comp_smul])
    (fun a m m' => by rw [gact_add, Preadditive.comp_add])
    (fun r a m => by rw [gact_smul, Linear.comp_smul])

@[simp]
theorem gactLin_apply
    [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R] {M : D}
    [ModObj R M] [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    {W X Y : D} (s : W ⟶ X ⊗ Y) (a : X ⟶ R)
    (m : Y ⟶ M) : gactLin s a m = s ≫ gact a m := rfl

/-- **The transported associativity law**: given a coherence
identity between the two ways of reassociating the chosen sources,
acting by a convolution product agrees with acting twice. -/
theorem gactLin_assoc
    [Category.{v} D] [MonoidalCategory D] {R : D} [MonObj R] {M : D}
    [ModObj R M] [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    {W W' V X Y Z : D} (s₁ : W' ⟶ W ⊗ Z)
    (s₂ : W ⟶ X ⊗ Y) (s₃ : W' ⟶ X ⊗ V) (s₄ : V ⟶ Y ⊗ Z)
    (h : s₁ ≫ s₂ ▷ Z ≫ (α_ X Y Z).hom = s₃ ≫ X ◁ s₄)
    (a : X ⟶ R) (b : Y ⟶ R) (m : Z ⟶ M) :
    gactLin s₁ (gmulLin s₂ a b) m
      = gactLin s₃ a (gactLin s₄ b m) := by
  simp only [gactLin_apply, gmulLin_apply]
  rw [comp_gact, gact_assoc, gact_comp, reassoc_of% h]

end Bundled

end Action

/-! ## The Γ-module of a module object -/

/-- **The Γ-module of a module object**: for a module object `M`
over a commutative monoid object `R` of a symmetric ℂ-linear
monoidal category carrying an odd line `L`, the morphisms
`𝟙_ D ⟶ M` and `L.obj ⟶ M` form a module over the
super-commutative ℂ-algebra `RS.gammaAlgebra D L R` under the
convolution action.

The four blocks are the convolution action conjugated by the same
coherence isomorphisms that identify the sources in
`RS.gammaAlgebra`: the left unitor for even-even and even-odd, the
right unitor for odd-even, and the square trivialisation `L.sq` of
the odd line for odd-odd. -/
noncomputable def gammaModule (D : Type u) [Category.{v} D]
    [MonoidalCategory D] [SymmetricCategory D] [Preadditive D]
    [MonoidalPreadditive D] [Linear ℂ D] [MonoidalLinear ℂ D]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (M : D) [ModObj R M] : (gammaAlgebra D L R).Mod where
  even := 𝟙_ D ⟶ M
  odd := L.obj ⟶ M
  actEE := gactLin (R := R) (M := M) (λ_ (𝟙_ D)).inv
  actEO := gactLin (R := R) (M := M) (λ_ L.obj).inv
  actOE := gactLin (R := R) (M := M) (ρ_ L.obj).inv
  actOO := gactLin (R := R) (M := M) L.sq.inv
  one_act_e m := by
    have h : gactLin (R := R) (M := M) (λ_ (𝟙_ D)).inv η[R] m
        = m := by
      rw [gactLin_apply, gact_one, Iso.inv_hom_id_assoc]
    exact h
  one_act_o m := by
    have h : gactLin (R := R) (M := M) (λ_ L.obj).inv η[R] m
        = m := by
      rw [gactLin_apply, gact_one, Iso.inv_hom_id_assoc]
    exact h
  assoc_eee x y m := by
    refine gactLin_assoc _ _ _ _ ?_ x y m
    monoidal
  assoc_eeo x y m := by
    refine gactLin_assoc _ _ _ _ ?_ x y m
    monoidal
  assoc_eoe x u m := by
    refine gactLin_assoc _ _ _ _ ?_ x u m
    monoidal
  assoc_eoo x u m := by
    refine gactLin_assoc _ _ _ _ ?_ x u m
    have hc : (λ_ L.obj).inv ▷ L.obj ≫
        (α_ (𝟙_ D) L.obj L.obj).hom =
        (λ_ (L.obj ⊗ L.obj)).inv := by monoidal
    rw [hc]
    exact leftUnitor_inv_naturality L.sq.inv
  assoc_oee u x m := by
    refine gactLin_assoc _ _ _ _ ?_ u x m
    monoidal
  assoc_oeo u x m := by
    refine gactLin_assoc _ _ _ _ ?_ u x m
    have hc : (ρ_ L.obj).inv ▷ L.obj ≫
        (α_ L.obj (𝟙_ D) L.obj).hom =
        L.obj ◁ (λ_ L.obj).inv := by monoidal
    rw [hc]
  assoc_ooe u v m := by
    refine gactLin_assoc _ _ _ _ ?_ u v m
    have hc : (ρ_ (L.obj ⊗ L.obj)).inv ≫
        (α_ L.obj L.obj (𝟙_ D)).hom =
        L.obj ◁ (ρ_ L.obj).inv := by monoidal
    rw [unitors_inv_equal, ← Category.assoc,
      ← rightUnitor_inv_naturality, Category.assoc, hc]
  assoc_ooo u v m := by
    refine gactLin_assoc _ _ _ _ ?_ u v m
    have h2 : L.sq.inv ▷ L.obj ≫ (α_ L.obj L.obj L.obj).hom =
        (λ_ L.obj).hom ≫ (ρ_ L.obj).inv ≫
          L.obj ◁ L.sq.inv := by
      rw [← reassoc_of% L.evaluation_coevaluation,
        ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id,
        MonoidalCategory.whiskerLeft_id, Category.comp_id]
    rw [h2, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end RS
