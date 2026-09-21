/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.RhoTwist
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperModIso
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperModShift

/-!
# The realization of an odd twist is a parity shift

The Γ-module of the free module `R ⊗ 1̄` on the odd line is the
parity shift of the Γ-module of `R` itself: twisting by the odd
line exchanges the two components of `ρ`, and the exchange is
compatible with all four graded action blocks.

The two components of the identification are the parity swaps
`RS.rhoEvenOdd` and `RS.rhoOddOdd` of `RS.RhoTwist`, and no sign
enters.  Both swaps have the same shape, `s ≫ (· ▷ 1̄) ≫ cap` for
a source identification `s`, where `RS.OddLine.cap` contracts the
two twisting legs of `(Z ⊗ 1̄) ⊗ 1̄` against the square
trivialisation.  The cap is natural in the capped object
(`RS.OddLine.cap_naturality`) and compatible with the associator
(`RS.OddLine.cap_tensor`), and those two facts alone give the one
sliding lemma of the file, `RS.free_cap_slide`: capping the free
action of a scalar is convolution by that scalar, up to the
associator of the three sources.  Each of the four action
compatibilities is that lemma conjugated by the very coherence
isomorphisms that identify the sources in `RS.gammaAlgebra`.
-/

namespace RS

open CategoryTheory MonoidalCategory
open scoped MonObj

universe v u

attribute [local instance] CategoryTheory.ModObj.regular

/-! ## Capping the two twisting legs -/

section Cap

variable {D : Type u}

/-- **The odd cap**: contract the two twisting legs of a doubly
twisted object against the square trivialisation of the odd
line. -/
def OddLine.cap [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D]
    (L : OddLine D) (Z : D) :
    (Z ⊗ L.obj) ⊗ L.obj ⟶ Z :=
  (α_ Z L.obj L.obj).hom ≫ (Z ◁ L.sq.hom) ≫ (ρ_ Z).hom

/-- The odd cap unfolded. -/
theorem OddLine.cap_def
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D]
    (L : OddLine D) (Z : D) :
    L.cap Z =
      (α_ Z L.obj L.obj).hom ≫ (Z ◁ L.sq.hom) ≫ (ρ_ Z).hom :=
  rfl

/-- **The odd cap is natural** in the capped object: a morphism
whiskered by the two legs passes through the contraction. -/
theorem OddLine.cap_naturality
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D]
    (L : OddLine D) {Z Z' : D}
    (f : Z ⟶ Z') :
    ((f ▷ L.obj) ▷ L.obj) ≫ L.cap Z' = L.cap Z ≫ f := by
  simp only [OddLine.cap_def, Category.assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
    rightUnitor_naturality]

/-- **The odd cap is compatible with the associator**: capping a
tensor product is capping the right-hand factor inside the
left-hand one. -/
theorem OddLine.cap_tensor
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D]
    (L : OddLine D) (A B : D) :
    ((α_ A B L.obj).inv ▷ L.obj) ≫ L.cap (A ⊗ B) =
      (α_ A (B ⊗ L.obj) L.obj).hom ≫ (A ◁ L.cap B) := by
  have hpre : ((α_ A B L.obj).inv ▷ L.obj) ≫
      (α_ (A ⊗ B) L.obj L.obj).hom ≫
        (α_ A B (L.obj ⊗ L.obj)).hom =
      (α_ A (B ⊗ L.obj) L.obj).hom ≫
        (A ◁ (α_ B L.obj L.obj).hom) := by
    monoidal
  have hpost : (α_ A B (𝟙_ D)).inv ≫ (ρ_ (A ⊗ B)).hom =
      A ◁ (ρ_ B).hom := by
    monoidal
  simp only [OddLine.cap_def, tensor_whiskerLeft, whiskerLeft_comp,
    Category.assoc]
  rw [reassoc_of% hpre, hpost]

/-! ## The two parity swaps, capped -/

/-- The even parity swap is a whiskering followed by the cap. -/
theorem rhoEvenOdd_eq_cap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [CategoryTheory.Linear ℂ D] [MonoidalPreadditive D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (Z : D)
    (f : 𝟙_ D ⟶ Z ⊗ L.obj) :
    rhoEvenOdd L Z f = (λ_ L.obj).inv ≫ (f ▷ L.obj) ≫ L.cap Z :=
  rfl

/-- The odd parity swap is a whiskering followed by the cap. -/
theorem rhoOddOdd_eq_cap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [CategoryTheory.Linear ℂ D] [MonoidalPreadditive D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (Z : D)
    (g : L.obj ⟶ Z ⊗ L.obj) :
    rhoOddOdd L Z g = L.sq.inv ≫ (g ▷ L.obj) ≫ L.cap Z := by
  rw [rhoOddOdd, LinearEquiv.trans_apply, Linear.homCongr_apply]
  simp only [Iso.refl_inv, Category.id_comp, Iso.trans_hom,
    whiskerLeftIso_hom, oddParitySwap_symm_apply, OddLine.cap_def,
    Category.assoc]

end Cap

/-! ## The sliding lemma -/

section Slide

variable {D : Type u}

/-- **The sliding lemma**: the free action of a scalar on the free
module of the odd line, capped, is the convolution product by that
scalar, up to the associator of the three sources.  This is `μ`
sliding past an associator and the square trivialisation, and it
is the whole content of the parity shift. -/
theorem free_cap_slide
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D) (R : D) [MonObj R]
    {W X : D} (a : W ⟶ R)
    (m : X ⟶ R ⊗ L.obj) :
    (((a ⊗ₘ m) ≫ (α_ R R L.obj).inv ≫ μ[R] ▷ L.obj) ▷ L.obj) ≫
        L.cap R =
      (α_ W X L.obj).hom ≫ gmul a ((m ▷ L.obj) ≫ L.cap R) := by
  have h1 : ((a ⊗ₘ m) ▷ L.obj) ≫ (α_ R (R ⊗ L.obj) L.obj).hom =
      (α_ W X L.obj).hom ≫ (a ⊗ₘ (m ▷ L.obj)) := by
    rw [← tensorHom_id, ← tensorHom_id, associator_naturality]
  have h2 : (a ⊗ₘ (m ▷ L.obj)) ≫ (R ◁ L.cap R) =
      a ⊗ₘ ((m ▷ L.obj) ≫ L.cap R) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
  simp only [comp_whiskerRight, Category.assoc]
  rw [L.cap_naturality μ[R], reassoc_of% (L.cap_tensor R R),
    reassoc_of% h1, reassoc_of% h2, gmul_def]

/-- **The transported sliding lemma**: for any two parity swaps
`Φ` and `Ψ` presented as a source identification followed by the
cap, and any coherence identity between the two ways of
reassociating the chosen sources, the swap of a free action is the
transported convolution product against the swap.  The four action
compatibilities of `RS.gammaShiftHom` are the four instances of
this. -/
theorem free_cap_slide'
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] (L : OddLine D) (R : D) [MonObj R]
    {W X U V V' : D} (a : W ⟶ R)
    (m : X ⟶ R ⊗ L.obj) (s₁ : U ⟶ W ⊗ X) (p : V ⟶ U ⊗ L.obj)
    (q : V' ⟶ X ⊗ L.obj) (s₂ : V ⟶ W ⊗ V')
    {Φ : (U ⟶ R ⊗ L.obj) → (V ⟶ R)}
    {Ψ : (X ⟶ R ⊗ L.obj) → (V' ⟶ R)}
    (hΦ : ∀ f, Φ f = p ≫ (f ▷ L.obj) ≫ L.cap R)
    (hΨ : ∀ f, Ψ f = q ≫ (f ▷ L.obj) ≫ L.cap R)
    (h : p ≫ (s₁ ▷ L.obj) ≫ (α_ W X L.obj).hom =
      s₂ ≫ (W ◁ q)) :
    Φ (s₁ ≫ (a ⊗ₘ m) ≫ (α_ R R L.obj).inv ≫ μ[R] ▷ L.obj) =
      s₂ ≫ gmul a (Ψ m) := by
  rw [hΦ, hΨ, comp_whiskerRight, Category.assoc, free_cap_slide,
    reassoc_of% h, ← gmul_comp]

end Slide

/-! ## The parity shift of the Γ-module -/

section Shift

variable {D : Type u}

/-- **The parity swap is a morphism of Γ-modules**: the two
parity swaps of `RS.RhoTwist` intertwine the four action blocks of
the Γ-module of the free module on the odd line with the four
relabelled blocks of the parity shift of the Γ-module of `R`. -/
noncomputable def gammaShiftHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (R : D) [MonObj R]
    [IsCommMonObj R] :
    gammaModule D L R ((freeMod R L.obj).X) ⟶
      SuperCommAlgebra.Mod.shift (gammaModule D L R R) where
  evenMap := (rhoEvenOdd L R).toLinearMap
  oddMap := (rhoOddOdd L R).toLinearMap
  map_actEE x m := by
    refine free_cap_slide' L R x m (λ_ (𝟙_ D)).inv (λ_ L.obj).inv
      (λ_ L.obj).inv (λ_ L.obj).inv (rhoEvenOdd_eq_cap L R)
      (rhoEvenOdd_eq_cap L R) ?_
    monoidal
  map_actEO x m := by
    refine free_cap_slide' L R x m (λ_ L.obj).inv L.sq.inv
      L.sq.inv (λ_ (𝟙_ D)).inv (rhoOddOdd_eq_cap L R)
      (rhoOddOdd_eq_cap L R) ?_
    have hc : (λ_ L.obj).inv ▷ L.obj ≫
        (α_ (𝟙_ D) L.obj L.obj).hom =
        (λ_ (L.obj ⊗ L.obj)).inv := by monoidal
    rw [hc]
    exact leftUnitor_inv_naturality L.sq.inv
  map_actOE u m := by
    refine free_cap_slide' L R u m (ρ_ L.obj).inv L.sq.inv
      (λ_ L.obj).inv L.sq.inv (rhoOddOdd_eq_cap L R)
      (rhoEvenOdd_eq_cap L R) ?_
    have hc : (ρ_ L.obj).inv ▷ L.obj ≫
        (α_ L.obj (𝟙_ D) L.obj).hom =
        L.obj ◁ (λ_ L.obj).inv := by monoidal
    rw [hc]
  map_actOO u m := by
    refine free_cap_slide' L R u m L.sq.inv (λ_ L.obj).inv
      L.sq.inv (ρ_ L.obj).inv (rhoEvenOdd_eq_cap L R)
      (rhoOddOdd_eq_cap L R) ?_
    have h2 : L.sq.inv ▷ L.obj ≫ (α_ L.obj L.obj L.obj).hom =
        (λ_ L.obj).hom ≫ (ρ_ L.obj).inv ≫
          L.obj ◁ L.sq.inv := by
      rw [← reassoc_of% L.evaluation_coevaluation,
        ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id,
        MonoidalCategory.whiskerLeft_id, Category.comp_id]
    rw [h2, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- **The realization of an odd twist is the parity shift of the
realization**: the Γ-module of the free `R`-module on the odd line
is the parity shift of the Γ-module of `R`. -/
noncomputable def gammaShiftIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (R : D) [MonObj R]
    [IsCommMonObj R] :
    gammaModule D L R ((freeMod R L.obj).X) ≅
      SuperCommAlgebra.Mod.shift (gammaModule D L R R) :=
  SuperCommAlgebra.Mod.isoOfComponents (gammaShiftHom L R)
    (rhoEvenOdd L R).bijective (rhoOddOdd L R).bijective

end Shift

end RS
