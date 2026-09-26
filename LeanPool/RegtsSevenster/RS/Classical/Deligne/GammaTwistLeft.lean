/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaShift
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.TwistShuffle

/-!
# The realization of a left odd twist is a parity shift

Twisting a module `N` over a commutative monoid object `R` by the
odd line *on the left* produces `1̄ ⊗ N`, and its Γ-module is the
parity shift of the Γ-module of `N`.  This is the mirror of
`RS.gammaShiftIso`, which twists the regular module on the right.

The two identifications are again a source identification followed
by a contraction, but the contraction is now the *left* cap
`RS.OddLine.capL`, which folds the two leading odd legs of
`1̄ ⊗ (1̄ ⊗ Z)` against the square trivialisation.  The left cap is
natural in the capped object (`RS.OddLine.capL_naturality`), it
commutes with carrying a further object past the two odd legs
(`RS.OddLine.capL_braidPast`), and the tensor–hom bijection of the
self-duality of the odd line makes it invertible
(`RS.OddLine.capLEquiv`).  Those three facts give the single
sliding lemma `RS.left_cap_slide`, of which the four action
compatibilities are instances.

Unlike the right-handed twist, a sign is unavoidable here: the
scalar has to be carried past the free odd leg, and in the two
odd-scalar blocks that carrying is the self-braiding of the odd
line, which is `−1`.  The sign is absorbed once and for all into
the odd component `RS.gammaTwistLeftOdd`.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

/-! ## Carrying an object past a context -/

section Braid

variable {D : Type u}

/-- Carrying an object past a context is inverse to carrying it
back: over a symmetric base the two directions are inverse
isomorphisms. -/
theorem braidPast_symm
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (A V T : D) :
    (braidPast A V T).inv = (braidPast V A T).hom := by
  simp only [braidPast, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
    Iso.symm_hom, whiskerRightIso_inv, whiskerRightIso_hom,
    Category.assoc,
    SymmetricCategory.braiding_swap_eq_inv_braiding]

/-- Carrying an object past the unit is the unit coherence. -/
theorem braidPast_tensorUnit
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (A Z : D) :
    (braidPast A (𝟙_ D) Z).hom ≫ (λ_ (A ⊗ Z)).hom =
      A ◁ (λ_ Z).hom := by
  rw [braidPast_hom, braiding_tensorUnit_right]
  monoidal

end Braid

/-! ## Capping the two leading odd legs -/

section Cap

variable {D : Type u}

/-- **The left odd cap**: contract the two leading legs of a doubly
twisted object against the square trivialisation of the odd
line. -/
def OddLine.capL [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D]
    (L : OddLine D) (Z : D) :
    L.obj ⊗ (L.obj ⊗ Z) ⟶ Z :=
  (α_ L.obj L.obj Z).inv ≫ (L.sq.hom ▷ Z) ≫ (λ_ Z).hom

/-- The left odd cap unfolded. -/
theorem OddLine.capL_def
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D]
    (L : OddLine D) (Z : D) :
    L.capL Z =
      (α_ L.obj L.obj Z).inv ≫ (L.sq.hom ▷ Z) ≫ (λ_ Z).hom :=
  rfl

/-- **The left odd cap is natural** in the capped object: a
morphism whiskered by the two legs passes through the
contraction. -/
theorem OddLine.capL_naturality
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D]
    (L : OddLine D) {Z Z' : D}
    (f : Z ⟶ Z') :
    (L.obj ◁ (L.obj ◁ f)) ≫ L.capL Z' = L.capL Z ≫ f := by
  simp only [OddLine.capL_def, Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    leftUnitor_naturality]

/-- **The left odd cap commutes with carrying an object past the
two odd legs**: capping after the carry is carrying after the
cap. -/
theorem OddLine.capL_braidPast
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D]
    (L : OddLine D) (A Z : D) :
    (L.obj ◁ (braidPast A L.obj Z).hom) ≫ L.capL (A ⊗ Z) =
      (braidPast L.obj A (L.obj ⊗ Z)).hom ≫ (A ◁ L.capL Z) := by
  have hP : (braidPast A (L.obj ⊗ L.obj) Z).hom ≫
      (α_ L.obj L.obj (A ⊗ Z)).hom =
      (A ◁ (α_ L.obj L.obj Z).hom) ≫
        (braidPast A L.obj (L.obj ⊗ Z)).hom ≫
        (L.obj ◁ (braidPast A L.obj Z).hom) := by
    rw [braidPast_hom]
    simp only [Category.assoc]
    exact braidPast_tensor_context A L.obj L.obj Z
  have hQ : (braidPast A L.obj (L.obj ⊗ Z)).hom ≫
      (L.obj ◁ (braidPast A L.obj Z).hom) =
      (A ◁ (α_ L.obj L.obj Z).inv) ≫
        (braidPast A (L.obj ⊗ L.obj) Z).hom ≫
        (α_ L.obj L.obj (A ⊗ Z)).hom := by
    rw [hP, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
      Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id,
      Category.id_comp]
  have hE : (braidPast A (L.obj ⊗ L.obj) Z).hom ≫
      (L.sq.hom ▷ (A ⊗ Z)) ≫ (λ_ (A ⊗ Z)).hom =
      (A ◁ (L.sq.hom ▷ Z)) ≫ (A ◁ (λ_ Z).hom) := by
    rw [← braidPast_natural_context_assoc A L.sq.hom Z,
      braidPast_tensorUnit]
  have hG : (braidPast A L.obj (L.obj ⊗ Z)).hom ≫
      ((L.obj ◁ (braidPast A L.obj Z).hom) ≫ L.capL (A ⊗ Z)) =
      A ◁ L.capL Z := by
    rw [← Category.assoc, hQ, OddLine.capL_def]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [hE, OddLine.capL_def]
    simp only [MonoidalCategory.whiskerLeft_comp]
  have h0 : (braidPast L.obj A (L.obj ⊗ Z)).hom ≫
      (braidPast A L.obj (L.obj ⊗ Z)).hom = 𝟙 _ := by
    rw [← braidPast_symm A L.obj (L.obj ⊗ Z)]
    exact Iso.inv_hom_id _
  rw [← hG, ← Category.assoc, h0, Category.id_comp]

end Cap

/-! ## The sliding lemma -/

section Slide

variable {D : Type u}

/-- **The sliding lemma**: the action on a left twist by the odd
line, capped, is the convolution action of the scalar on the
capped module element, up to carrying the odd leg past the scalar.
This is the whole content of the left parity shift. -/
theorem left_cap_slide
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D) (R : D) [MonObj R] (N : D) [ModObj R N]
    {W X : D} (a : W ⟶ R) (m : X ⟶ L.obj ⊗ N) :
    (L.obj ◁ ((a ⊗ₘ m) ≫ actAcross R L.obj N)) ≫ L.capL N =
      (braidPast L.obj W X).hom ≫
        gact a ((L.obj ◁ m) ≫ L.capL N) := by
  have h1 : (L.obj ◁ (a ⊗ₘ m)) ≫
      (braidPast L.obj R (L.obj ⊗ N)).hom =
      (braidPast L.obj W X).hom ≫ (a ⊗ₘ (L.obj ◁ m)) := by
    rw [tensorHom_def, tensorHom_def]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [braidPast_natural_tail L.obj R m,
      ← Category.assoc, braidPast_natural_context L.obj a X,
      Category.assoc]
  have h2 : (a ⊗ₘ (L.obj ◁ m)) ≫ (R ◁ L.capL N) =
      a ⊗ₘ ((L.obj ◁ m) ≫ L.capL N) := by
    rw [tensorHom_def, tensorHom_def,
      MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [actAcross_eq_braidPast]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [L.capL_naturality (actLeft R N),
    reassoc_of% (L.capL_braidPast R N), reassoc_of% h1,
    reassoc_of% h2, gact_def]

/-- **The transported sliding lemma**: for any two contractions `Φ`
and `Ψ` presented as a source identification followed by the left
cap, and any coherence identity between the two ways of
reassociating the chosen sources, the contraction of a twisted
action is the transported convolution action against the
contraction.  The four action compatibilities of
`RS.gammaTwistLeftHom` are the four instances of this. -/
theorem left_cap_slide'
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D) (R : D) [MonObj R] (N : D) [ModObj R N]
    {W X U V V' : D} (a : W ⟶ R)
    (m : X ⟶ L.obj ⊗ N) (s₁ : U ⟶ W ⊗ X) (p : V ⟶ L.obj ⊗ U)
    (q : V' ⟶ L.obj ⊗ X) (s₂ : V ⟶ W ⊗ V')
    {Φ : (U ⟶ L.obj ⊗ N) → (V ⟶ N)}
    {Ψ : (X ⟶ L.obj ⊗ N) → (V' ⟶ N)}
    (hΦ : ∀ f, Φ f = p ≫ (L.obj ◁ f) ≫ L.capL N)
    (hΨ : ∀ f, Ψ f = q ≫ (L.obj ◁ f) ≫ L.capL N)
    (act : R ⊗ (L.obj ⊗ N) ⟶ L.obj ⊗ N)
    (hact : act = actAcross R L.obj N)
    (h : p ≫ (L.obj ◁ s₁) ≫ (braidPast L.obj W X).hom =
      s₂ ≫ (W ◁ q)) :
    Φ (s₁ ≫ (a ⊗ₘ m) ≫ act) = s₂ ≫ gact a (Ψ m) := by
  rw [hΦ, hΨ, hact, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, left_cap_slide, reassoc_of% h,
    gact_comp a q ((L.obj ◁ m) ≫ L.capL N)]

end Slide

/-! ## The two contractions are isomorphisms -/

section Equivalence

variable {D : Type u}

/-- **Lowering along the left cap is a ℂ-linear isomorphism**: it
is the tensor–hom bijection of the self-duality of the odd line. -/
noncomputable def OddLine.capLEquiv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (Y Z : D) :
    (Y ⟶ L.obj ⊗ Z) ≃ₗ[ℂ] (L.obj ⊗ Y ⟶ Z) where
  toFun f := (L.obj ◁ f) ≫ L.capL Z
  map_add' f g := by
    simp [MonoidalPreadditive.whiskerLeft_add, Preadditive.add_comp]
  map_smul' c f := by
    simp [MonoidalLinear.whiskerLeft_smul, Linear.smul_comp]
  invFun h := (λ_ Y).inv ≫ (L.sq.inv ▷ Y) ≫
    (α_ L.obj L.obj Y).hom ≫ (L.obj ◁ h)
  left_inv f := by
    let := L.exactPairing
    have hs : ∀ F : Y ⟶ L.obj ⊗ Z,
        (tensorLeftHomEquiv Y L.obj L.obj Z).symm F =
          (L.obj ◁ F) ≫ L.capL Z := fun _ => rfl
    have ht : ∀ g : L.obj ⊗ Y ⟶ Z,
        (tensorLeftHomEquiv Y L.obj L.obj Z) g =
          (λ_ Y).inv ≫ (L.sq.inv ▷ Y) ≫
            (α_ L.obj L.obj Y).hom ≫ (L.obj ◁ g) := fun _ => rfl
    change (λ_ Y).inv ≫ (L.sq.inv ▷ Y) ≫ (α_ L.obj L.obj Y).hom ≫
      (L.obj ◁ ((L.obj ◁ f) ≫ L.capL Z)) = f
    rw [← ht, ← hs, Equiv.apply_symm_apply]
  right_inv g := by
    let := L.exactPairing
    have hs : ∀ F : Y ⟶ L.obj ⊗ Z,
        (tensorLeftHomEquiv Y L.obj L.obj Z).symm F =
          (L.obj ◁ F) ≫ L.capL Z := fun _ => rfl
    have ht : ∀ g : L.obj ⊗ Y ⟶ Z,
        (tensorLeftHomEquiv Y L.obj L.obj Z) g =
          (λ_ Y).inv ≫ (L.sq.inv ▷ Y) ≫
            (α_ L.obj L.obj Y).hom ≫ (L.obj ◁ g) := fun _ => rfl
    change (L.obj ◁ ((λ_ Y).inv ≫ (L.sq.inv ▷ Y) ≫
      (α_ L.obj L.obj Y).hom ≫ (L.obj ◁ g))) ≫ L.capL Z = g
    rw [← hs, ← ht, Equiv.symm_apply_apply]

/-- **The even component**: points of a left twist by the odd line
are odd elements of the module. -/
noncomputable def gammaTwistLeftEven
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (Z : D) :
    (𝟙_ D ⟶ L.obj ⊗ Z) ≃ₗ[ℂ] (L.obj ⟶ Z) :=
  (L.capLEquiv (𝟙_ D) Z).trans
    (Linear.homCongr ℂ (ρ_ L.obj) (Iso.refl Z))

theorem gammaTwistLeftEven_apply
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (Z : D)
    (f : 𝟙_ D ⟶ L.obj ⊗ Z) :
    (gammaTwistLeftEven L Z).toLinearMap f =
      (ρ_ L.obj).inv ≫ (L.obj ◁ f) ≫ L.capL Z := by
  change gammaTwistLeftEven L Z f = _
  rw [gammaTwistLeftEven, LinearEquiv.trans_apply,
    Linear.homCongr_apply, Iso.refl_hom, Category.comp_id]
  rfl

/-- **The odd component**: odd elements of a left twist by the odd
line are points of the module.  The sign is the self-braiding of
the odd line, and it is what makes the odd blocks of the twist
match the shifted blocks of the module. -/
noncomputable def gammaTwistLeftOdd
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (Z : D) :
    (L.obj ⟶ L.obj ⊗ Z) ≃ₗ[ℂ] (𝟙_ D ⟶ Z) :=
  ((L.capLEquiv L.obj Z).trans
    (Linear.homCongr ℂ L.sq (Iso.refl Z))).trans (LinearEquiv.neg ℂ)

theorem gammaTwistLeftOdd_apply
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (Z : D)
    (g : L.obj ⟶ L.obj ⊗ Z) :
    (gammaTwistLeftOdd L Z).toLinearMap g =
      (-L.sq.inv) ≫ (L.obj ◁ g) ≫ L.capL Z := by
  change gammaTwistLeftOdd L Z g = _
  rw [gammaTwistLeftOdd, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply, LinearEquiv.neg_apply,
    Linear.homCongr_apply, Iso.refl_hom, Category.comp_id,
    Preadditive.neg_comp]
  rfl

end Equivalence

/-! ## The parity shift of the Γ-module -/

section Twist

variable {D : Type u}

/-- **The two contractions form a morphism of Γ-modules**: they
intertwine the four action blocks of the Γ-module of the left twist
with the four relabelled blocks of the parity shift of the
Γ-module of the module. -/
noncomputable def gammaTwistLeftHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (R : D)
    [MonObj R] [IsCommMonObj R] (N : Mod D R) :
    gammaModule D L R (tensorLeftMod R L.obj N).X ⟶
      SuperCommAlgebra.Mod.shift (gammaModule D L R N.X) where
  evenMap := (gammaTwistLeftEven L N.X).toLinearMap
  oddMap := (gammaTwistLeftOdd L N.X).toLinearMap
  map_actEE x m := by
    refine left_cap_slide' L R N.X x m (λ_ (𝟙_ D)).inv
      (ρ_ L.obj).inv (ρ_ L.obj).inv (λ_ L.obj).inv
      (gammaTwistLeftEven_apply L N.X)
      (gammaTwistLeftEven_apply L N.X) _ rfl ?_
    rw [braidPast_hom, braiding_tensorUnit_right]
    monoidal
  map_actEO x m := by
    refine left_cap_slide' L R N.X x m (λ_ L.obj).inv
      (-L.sq.inv) (-L.sq.inv) (λ_ (𝟙_ D)).inv
      (gammaTwistLeftOdd_apply L N.X)
      (gammaTwistLeftOdd_apply L N.X) _ rfl ?_
    have hc : (L.obj ◁ (λ_ L.obj).inv) ≫
        (braidPast L.obj (𝟙_ D) L.obj).hom =
        (λ_ (L.obj ⊗ L.obj)).inv := by
      rw [braidPast_hom, braiding_tensorUnit_right]
      monoidal
    rw [hc, whiskerLeft_neg, Preadditive.neg_comp,
      Preadditive.comp_neg, leftUnitor_inv_naturality]
  map_actOE u m := by
    refine left_cap_slide' L R N.X u m (ρ_ L.obj).inv
      (-L.sq.inv) (ρ_ L.obj).inv L.sq.inv
      (gammaTwistLeftOdd_apply L N.X)
      (gammaTwistLeftEven_apply L N.X) _ rfl ?_
    have hb : (braidPast L.obj L.obj (𝟙_ D)).hom =
        -𝟙 (L.obj ⊗ (L.obj ⊗ 𝟙_ D)) := by
      rw [braidPast_hom, L.braid_neg, neg_id_whiskerRight]
      simp
    rw [hb]
    simp only [Preadditive.comp_neg, Preadditive.neg_comp,
      Category.comp_id, neg_neg]
  map_actOO u m := by
    refine left_cap_slide' L R N.X u m L.sq.inv
      (ρ_ L.obj).inv (-L.sq.inv) (ρ_ L.obj).inv
      (gammaTwistLeftEven_apply L N.X)
      (gammaTwistLeftOdd_apply L N.X) _ rfl ?_
    have hb : (braidPast L.obj L.obj L.obj).hom =
        -𝟙 (L.obj ⊗ (L.obj ⊗ L.obj)) := by
      rw [braidPast_hom, L.braid_neg, neg_id_whiskerRight]
      simp
    rw [hb]
    simp only [whiskerLeft_neg, Preadditive.comp_neg,
      Category.comp_id]

end Twist

end RS
