/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperModHom
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperModTensor

/-!
# The comparison map of Deligne's (2.11.1)

For two module objects `M`, `N` over a commutative monoid object
`R` of a symmetric ℂ-linear monoidal category carrying an odd line
`L`, the Γ-modules of `M` and of `N` may be tensored over the
Γ-algebra of `R` (`RS.SuperCommAlgebra.Mod.tensor`), and the
relative tensor product `RS.modTensor` of the module objects has a
Γ-module of its own.  This file builds the comparison map between
them, `RS.gammaPairComparison`, as a morphism of super modules.

Everything rests on one ungraded operation, `RS.gpair`: the
pairing `(m ⊗ₘ n) ≫ π` of a morphism into `M` against a morphism
into `N`, at *arbitrary* sources, followed by the projection onto
the relative tensor product.  It obeys two structural laws, which
between them carry the whole construction.

* **The balance law** `RS.gpair_balance`:
  `gpair (gact a m) n = (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫
  gpair m (gact a n)`.
  A scalar may be moved from the left argument to the right one at
  the cost of braiding it past the source of the left argument.
  This is the defining relation `RS.modTensor_condition` of the
  coequalizer, written in the language of the pairing: the leg
  acting on `M` does so through `RS.actRight`, which is the left
  action conjugated by the braiding.
* **The action law** `RS.gact_gpair`:
  `gact a (gpair m n) = (α_ X Y Z).inv ≫ gpair (gact a m) n`.
  The descended action of `R` on the relative tensor product is
  the action on the left factor.

Instantiating the balance law at the four source identifications
`(λ_ (𝟙_ D)).inv`, `(λ_ L.obj).inv`, `(ρ_ L.obj).inv` and
`L.sq.inv` gives the eight balancing laws `RS.gpair_balanced_xyz`
that the universal property of `RS.SuperCommAlgebra.Mod.tensor`
requires; the Koszul sign appears in exactly the two patterns
`ooe` and `ooo`, where the scalar and the left argument are both
odd, and it is `RS.OddLine.braid_neg`.  Instantiating the action
law at the same four identifications gives the eight action laws
`RS.gpair_act_xyz`, which say that the resulting map is a morphism
of super modules.

The only identity not implied by coherence is the odd-odd-odd one,
`RS.oddLine_sq_assoc`: it is the first triangle identity of the
self-duality of the odd line,
`RS.OddLine.evaluation_coevaluation`.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

/-! ## The ungraded pairing -/

section Pairing

variable {D : Type u}

/-- The *pairing* of a morphism into one module object with a
morphism into another, taken at arbitrary sources: tensor the two
morphisms and project to the relative tensor product. -/
noncomputable def gpair
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D] {R : D} [MonObj R] {M : Mod D R} {N : Mod D R}
    {X Y : D} (m : X ⟶ M.X) (n : Y ⟶ N.X) :
    X ⊗ Y ⟶ modTensor R M N :=
  (m ⊗ₘ n) ≫ modTensorπ R M N

/-- The pairing unfolded. -/
theorem gpair_def [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D] {R : D} [MonObj R] {M : Mod D R} {N : Mod D R}
    {X Y : D} (m : X ⟶ M.X) (n : Y ⟶ N.X) :
    gpair m n = (m ⊗ₘ n) ≫ modTensorπ R M N := rfl

/-- Reindexing the left source of a pairing. -/
theorem comp_gpair [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D] {R : D} [MonObj R] {M : Mod D R} {N : Mod D R}
    {W X Y : D} (f : W ⟶ X) (m : X ⟶ M.X)
    (n : Y ⟶ N.X) :
    gpair (f ≫ m) n = f ▷ Y ≫ gpair (M := M) (N := N) m n := by
  have h : f ▷ Y ≫ (m ⊗ₘ n) = (f ≫ m) ⊗ₘ n := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
  rw [gpair_def, gpair_def, ← h, Category.assoc]

/-- Reindexing the right source of a pairing. -/
theorem gpair_comp [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D] {R : D} [MonObj R] {M : Mod D R} {N : Mod D R}
    {X Y Z : D} (m : X ⟶ M.X) (g : Z ⟶ Y)
    (n : Y ⟶ N.X) :
    gpair m (g ≫ n) = X ◁ g ≫ gpair (M := M) (N := N) m n := by
  have h : X ◁ g ≫ (m ⊗ₘ n) = m ⊗ₘ (g ≫ n) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
  rw [gpair_def, gpair_def, ← h, Category.assoc]

section Additive

/-- The pairing is additive in its left argument. -/
theorem add_gpair [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D] {R : D} [MonObj R] {M : Mod D R} {N : Mod D R}
    [Preadditive D] [MonoidalPreadditive D]
    {X Y : D} (m m' : X ⟶ M.X) (n : Y ⟶ N.X) :
    gpair (m + m') n = gpair (N := N) m n + gpair (N := N) m' n := by
  rw [gpair_def, gpair_def, gpair_def, MonoidalPreadditive.add_tensor,
    Preadditive.add_comp]

/-- The pairing is additive in its right argument. -/
theorem gpair_add [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D] {R : D} [MonObj R] {M : Mod D R} {N : Mod D R}
    [Preadditive D] [MonoidalPreadditive D]
    {X Y : D} (m : X ⟶ M.X) (n n' : Y ⟶ N.X) :
    gpair m (n + n') = gpair (M := M) m n + gpair (M := M) m n' := by
  rw [gpair_def, gpair_def, gpair_def, MonoidalPreadditive.tensor_add,
    Preadditive.add_comp]

end Additive

section Homogeneous

/-- The pairing is ℂ-homogeneous in its left argument. -/
theorem smul_gpair [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D] {R : D} [MonObj R] {M : Mod D R} {N : Mod D R}
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    (r : ℂ) {X Y : D} (m : X ⟶ M.X) (n : Y ⟶ N.X) :
    gpair (r • m) n = r • gpair (M := M) (N := N) m n := by
  have h : (r • m) ⊗ₘ n = r • (m ⊗ₘ n) := by
    rw [tensorHom_def, tensorHom_def,
      MonoidalLinear.smul_whiskerRight, Linear.smul_comp]
  rw [gpair_def, gpair_def, h, Linear.smul_comp]

/-- The pairing is ℂ-homogeneous in its right argument. -/
theorem gpair_smul [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D] {R : D} [MonObj R] {M : Mod D R} {N : Mod D R}
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    (r : ℂ) {X Y : D} (m : X ⟶ M.X) (n : Y ⟶ N.X) :
    gpair m (r • n) = r • gpair (M := M) (N := N) m n := by
  have h : m ⊗ₘ (r • n) = r • (m ⊗ₘ n) := by
    rw [tensorHom_def', tensorHom_def',
      MonoidalLinear.whiskerLeft_smul, Linear.smul_comp]
  rw [gpair_def, gpair_def, h, Linear.smul_comp]

end Homogeneous

/-! ### The bundled bilinear pairing -/

section Bundled

/-- The pairing as a ℂ-bilinear map of hom-modules, transported
along a chosen morphism `s` from the intended source into the
tensor product of the two given sources.  The four graded blocks of
the comparison map of `RS.gammaPairComparison` are the four
instances of this construction. -/
noncomputable def gpairLin
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D] {R : D} [MonObj R] [Preadditive D]
    [MonoidalPreadditive D] [Linear ℂ D] [MonoidalLinear ℂ D]
    (M N : Mod D R) {W X Y : D}
    (s : W ⟶ X ⊗ Y) :
    (X ⟶ M.X) →ₗ[ℂ] (Y ⟶ N.X) →ₗ[ℂ] (W ⟶ modTensor R M N) :=
  LinearMap.mk₂ ℂ (fun m n => s ≫ gpair m n)
    (fun m m' n => by rw [add_gpair, Preadditive.comp_add])
    (fun r m n => by rw [smul_gpair, Linear.comp_smul])
    (fun m n n' => by rw [gpair_add, Preadditive.comp_add])
    (fun r m n => by rw [gpair_smul, Linear.comp_smul])

@[simp]
theorem gpairLin_apply [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D] {R : D} [MonObj R] [Preadditive D]
    [MonoidalPreadditive D] [Linear ℂ D] [MonoidalLinear ℂ D]
    (M N : Mod D R) {W X Y : D} (s : W ⟶ X ⊗ Y)
    (m : X ⟶ M.X) (n : Y ⟶ N.X) :
    gpairLin M N s m n = s ≫ gpair m n := rfl

end Bundled

end Pairing

/-! ## The balance law -/

section Balance

variable {D : Type u}

/-- **The balance law**: a scalar may be moved from the left
argument of the pairing to the right one, at the cost of braiding
the scalar past the left source.  This is the defining relation of
the relative tensor product, `RS.modTensor_condition`, written in
the language of the pairing. -/
theorem gpair_balance
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] {R : D} [MonObj R] {M : Mod D R} {N : Mod D R}
    {X Y Z : D} (a : X ⟶ R) (m : Y ⟶ M.X)
    (n : Z ⟶ N.X) :
    gpair (gact a m) n =
      (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫
        gpair (M := M) m (gact a n) := by
  have hl : ((a ⊗ₘ m) ⊗ₘ n) ≫ actLeft R M.X ▷ N.X ≫
      modTensorπ R M N = gpair (gact a m) n := by
    rw [← Category.assoc, ← tensorHom_id, tensorHom_comp_tensorHom,
      Category.comp_id]
    rfl
  have hr : (m ⊗ₘ (a ⊗ₘ n)) ≫ M.X ◁ actLeft R N.X ≫
      modTensorπ R M N = gpair (M := M) m (gact a n) := by
    rw [← Category.assoc, ← id_tensorHom, tensorHom_comp_tensorHom,
      Category.comp_id]
    rfl
  have hleg : M.X ◁ actLeft R N.X ≫ modTensorπ R M N =
      (α_ M.X R N.X).inv ≫ actRight R M.X ▷ N.X ≫
        modTensorπ R M N := by
    have h := modTensor_condition R M N
    rw [modTensorLegM, modTensorLegN] at h
    rw [h]
    simp only [Category.assoc]
    rw [Iso.inv_hom_id_assoc]
  have hbr : (β_ X Y).hom ▷ Z ≫ ((m ⊗ₘ a) ⊗ₘ n) =
      ((a ⊗ₘ m) ⊗ₘ n) ≫ (β_ R M.X).hom ▷ N.X := by
    rw [← tensorHom_id ((β_ X Y).hom) Z,
      ← tensorHom_id ((β_ R M.X).hom) N.X,
      tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id,
      ← BraidedCategory.braiding_naturality]
  have hsym : (β_ R M.X).hom ▷ N.X ≫ actRight R M.X ▷ N.X =
      actLeft R M.X ▷ N.X := by
    rw [← comp_whiskerRight, actRight,
      SymmetricCategory.symmetry_assoc]
  rw [← hl, ← hr, hleg, ← associator_naturality_assoc,
    Iso.hom_inv_id_assoc, reassoc_of% hbr, reassoc_of% hsym]

/-! ### The transported balance law -/

section Bundled

/-- The balance law with both sources reindexed, in the form used
to discharge the eight balancing hypotheses: the two source
identifications may be replaced by a single comparison morphism. -/
theorem gpairLin_balance_comp
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] {R : D} [MonObj R] {M : Mod D R} {N : Mod D R}
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    {W V X Y Z : D} (s₁ : W ⟶ V ⊗ Z)
    (s₂ : V ⟶ X ⊗ Y) (a : X ⟶ R) (m : Y ⟶ M.X) (n : Z ⟶ N.X) :
    gpairLin M N s₁ (gactLin s₂ a m) n =
      (s₁ ≫ (s₂ ≫ (β_ X Y).hom) ▷ Z ≫ (α_ Y X Z).hom) ≫
        gpair (M := M) m (gact a n) := by
  rw [gpairLin_apply, gactLin_apply, comp_gpair, gpair_balance,
    comp_whiskerRight]
  simp only [Category.assoc]

/-- **The transported balance law**: given a coherence identity
between the two ways of reindexing the sources, a scalar may be
moved from the left argument of the pairing to the right one. -/
theorem gpairLin_balance
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] {R : D} [MonObj R] {M : Mod D R} {N : Mod D R}
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    {W V U X Y Z : D} (s₁ : W ⟶ V ⊗ Z)
    (s₂ : V ⟶ X ⊗ Y) (s₃ : W ⟶ Y ⊗ U) (s₄ : U ⟶ X ⊗ Z)
    (h : s₁ ≫ (s₂ ≫ (β_ X Y).hom) ▷ Z ≫ (α_ Y X Z).hom =
      s₃ ≫ Y ◁ s₄)
    (a : X ⟶ R) (m : Y ⟶ M.X) (n : Z ⟶ N.X) :
    gpairLin M N s₁ (gactLin s₂ a m) n =
      gpairLin M N s₃ m (gactLin s₄ a n) := by
  rw [gpairLin_balance_comp, h, gpairLin_apply, gactLin_apply,
    gpair_comp]
  simp only [Category.assoc]

/-- **The transported balance law with a Koszul sign**: the
coherence identity may hold only up to sign, and then so does the
balance law.  The sign arises from `RS.OddLine.braid_neg`, in
exactly the two cases where the scalar and the left argument are
both odd. -/
theorem gpairLin_balance_neg
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] {R : D} [MonObj R] {M : Mod D R} {N : Mod D R}
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    {W V U X Y Z : D} (s₁ : W ⟶ V ⊗ Z)
    (s₂ : V ⟶ X ⊗ Y) (s₃ : W ⟶ Y ⊗ U) (s₄ : U ⟶ X ⊗ Z)
    (h : s₁ ≫ (s₂ ≫ (β_ X Y).hom) ▷ Z ≫ (α_ Y X Z).hom =
      -(s₃ ≫ Y ◁ s₄))
    (a : X ⟶ R) (m : Y ⟶ M.X) (n : Z ⟶ N.X) :
    gpairLin M N s₁ (gactLin s₂ a m) n =
      -gpairLin M N s₃ m (gactLin s₄ a n) := by
  rw [gpairLin_balance_comp, h, Preadditive.neg_comp, gpairLin_apply,
    gactLin_apply, gpair_comp]
  simp only [Category.assoc]

end Bundled

end Balance

/-! ## The action law -/

section ActLaw

variable {D : Type u}

/-- **The action law**: the descended action of `R` on the
relative tensor product is the action on the left factor of a
pairing, up to the associator of the three sources. -/
theorem gact_gpair [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    {R : D} [MonObj R] [IsCommMonObj R] {M : Mod D R} {N : Mod D R}
    {X Y Z : D} (a : X ⟶ R) (m : Y ⟶ M.X)
    (n : Z ⟶ N.X) :
    gact (M := (modTensorMod R M N).X) a (gpair m n) =
      (α_ X Y Z).inv ≫ gpair (gact a m) n := by
  have hl : ((a ⊗ₘ m) ⊗ₘ n) ≫ actLeft R M.X ▷ N.X ≫
      modTensorπ R M N = gpair (gact a m) n := by
    rw [← Category.assoc, ← tensorHom_id, tensorHom_comp_tensorHom,
      Category.comp_id]
    rfl
  have hr : (a ⊗ₘ (m ⊗ₘ n)) ≫ R ◁ modTensorπ R M N ≫
      modTensorAct R M N =
      gact (M := (modTensorMod R M N).X) a (gpair m n) := by
    rw [← Category.assoc, ← id_tensorHom, tensorHom_comp_tensorHom,
      Category.comp_id]
    rfl
  rw [← hl, ← hr, whiskerLeft_modTensorπ_act]
  simp only [Category.assoc]
  rw [← associator_inv_naturality_assoc]

/-- The action law with the descended action named explicitly.
This is `RS.gact_gpair` retyped along `RS.modTensorMod_X`, and is
the form in which the law is transported. -/
theorem gpair_modTensorAct
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    {R : D} [MonObj R] [IsCommMonObj R] {M : Mod D R} {N : Mod D R}
    {X Y Z : D} (a : X ⟶ R) (m : Y ⟶ M.X)
    (n : Z ⟶ N.X) :
    (a ⊗ₘ gpair (M := M) (N := N) m n) ≫ modTensorAct R M N =
      (α_ X Y Z).inv ≫ gpair (gact a m) n :=
  gact_gpair a m n

section Bundled

/-- **The transported action law**: given a coherence identity
between the two ways of reindexing the sources, acting on the
relative tensor product is acting on the left factor. -/
theorem gpairLin_act [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    {R : D} [MonObj R] [IsCommMonObj R] {M : Mod D R} {N : Mod D R}
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    {W V U X Y Z : D} (s₁ : W ⟶ X ⊗ V)
    (s₂ : V ⟶ Y ⊗ Z) (s₃ : W ⟶ U ⊗ Z) (s₄ : U ⟶ X ⊗ Y)
    (h : s₁ ≫ X ◁ s₂ ≫ (α_ X Y Z).inv = s₃ ≫ s₄ ▷ Z)
    (a : X ⟶ R) (m : Y ⟶ M.X) (n : Z ⟶ N.X) :
    s₁ ≫ (a ⊗ₘ gpairLin M N s₂ m n) ≫ modTensorAct R M N =
      gpairLin M N s₃ (gactLin s₄ a m) n := by
  have e : (a ⊗ₘ (s₂ ≫ gpair (M := M) (N := N) m n)) ≫
      modTensorAct R M N =
      X ◁ s₂ ≫ (a ⊗ₘ gpair (M := M) (N := N) m n) ≫
        modTensorAct R M N := by
    rw [← Category.assoc, ← id_tensorHom, tensorHom_comp_tensorHom,
      Category.id_comp]
  rw [gpairLin_apply, e, gpair_modTensorAct, gpairLin_apply,
    gactLin_apply, comp_gpair, reassoc_of% h]

end Bundled

end ActLaw

/-! ## Coherence for the four source identifications -/

section Coherence

variable {D : Type u}

/-- Braiding past the unit on the left turns the left unitor into
the right one. -/
theorem leftUnitor_inv_braiding
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (Y : D) :
    (λ_ Y).inv ≫ (β_ (𝟙_ D) Y).hom = (ρ_ Y).inv := by
  rw [← cancel_mono (ρ_ Y).hom, Category.assoc, braiding_rightUnitor,
    Iso.inv_hom_id, Iso.inv_hom_id]

/-- Braiding past the unit on the right turns the right unitor into
the left one. -/
theorem rightUnitor_inv_braiding
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (Y : D) :
    (ρ_ Y).inv ≫ (β_ Y (𝟙_ D)).hom = (λ_ Y).inv := by
  rw [← cancel_mono (λ_ Y).hom, Category.assoc, braiding_leftUnitor,
    Iso.inv_hom_id, Iso.inv_hom_id]

/-- **The Koszul sign**: braiding the square trivialisation of the
odd line past itself is `RS.OddLine.braid_neg`. -/
theorem oddLine_sq_inv_braiding
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D]
    (L : OddLine D) :
    L.sq.inv ≫ (β_ L.obj L.obj).hom = -L.sq.inv := by
  rw [L.braid_neg, Preadditive.comp_neg, Category.comp_id]

/-- Reassociating the square trivialisation against a left unitor:
the odd-even-odd source identifications agree. -/
theorem oddLine_sq_leftUnitor
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D]
    (L : OddLine D) :
    L.sq.inv ≫ (λ_ L.obj).inv ▷ L.obj ≫
        (α_ (𝟙_ D) L.obj L.obj).hom =
      (λ_ (𝟙_ D)).inv ≫ (𝟙_ D) ◁ L.sq.inv := by
  have hc : (λ_ L.obj).inv ▷ L.obj ≫
      (α_ (𝟙_ D) L.obj L.obj).hom = (λ_ (L.obj ⊗ L.obj)).inv := by
    monoidal
  rw [hc]
  exact leftUnitor_inv_naturality L.sq.inv

/-- The same identity read from the other end. -/
theorem oddLine_sq_leftUnitor'
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D]
    (L : OddLine D) :
    (λ_ (𝟙_ D)).inv ≫ (𝟙_ D) ◁ L.sq.inv ≫
        (α_ (𝟙_ D) L.obj L.obj).inv =
      L.sq.inv ≫ (λ_ L.obj).inv ▷ L.obj := by
  rw [← reassoc_of% oddLine_sq_leftUnitor L, Iso.hom_inv_id,
    Category.comp_id]

/-- Reassociating the square trivialisation against a right
unitor: the odd-odd-even source identifications agree. -/
theorem oddLine_sq_rightUnitor
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D]
    (L : OddLine D) :
    (λ_ (𝟙_ D)).inv ≫ L.sq.inv ▷ (𝟙_ D) ≫
        (α_ L.obj L.obj (𝟙_ D)).hom =
      L.sq.inv ≫ L.obj ◁ (ρ_ L.obj).inv := by
  have hc : (ρ_ (L.obj ⊗ L.obj)).inv ≫
      (α_ L.obj L.obj (𝟙_ D)).hom = L.obj ◁ (ρ_ L.obj).inv := by
    monoidal
  rw [unitors_inv_equal, ← Category.assoc,
    ← rightUnitor_inv_naturality, Category.assoc, hc]

/-- The same identity read from the other end. -/
theorem oddLine_sq_rightUnitor'
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D]
    (L : OddLine D) :
    L.sq.inv ≫ L.obj ◁ (ρ_ L.obj).inv ≫
        (α_ L.obj L.obj (𝟙_ D)).inv =
      (λ_ (𝟙_ D)).inv ≫ L.sq.inv ▷ (𝟙_ D) := by
  rw [← reassoc_of% oddLine_sq_rightUnitor L, Iso.hom_inv_id,
    Category.comp_id]

/-- **The odd-odd-odd coherence identity**, the one identity not
implied by coherence alone: it is the first triangle identity of
the self-duality of the odd line. -/
theorem oddLine_sq_assoc
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D]
    (L : OddLine D) :
    (λ_ L.obj).inv ≫ L.sq.inv ▷ L.obj ≫
        (α_ L.obj L.obj L.obj).hom =
      (ρ_ L.obj).inv ≫ L.obj ◁ L.sq.inv := by
  have h2 : L.sq.inv ▷ L.obj ≫ (α_ L.obj L.obj L.obj).hom =
      (λ_ L.obj).hom ≫ (ρ_ L.obj).inv ≫ L.obj ◁ L.sq.inv := by
    rw [← reassoc_of% L.evaluation_coevaluation,
      ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id,
      MonoidalCategory.whiskerLeft_id, Category.comp_id]
  rw [h2, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The same identity read from the other end. -/
theorem oddLine_sq_assoc'
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D]
    (L : OddLine D) :
    (ρ_ L.obj).inv ≫ L.obj ◁ L.sq.inv ≫
        (α_ L.obj L.obj L.obj).inv =
      (λ_ L.obj).inv ≫ L.sq.inv ▷ L.obj := by
  rw [← reassoc_of% oddLine_sq_assoc L, Iso.hom_inv_id,
    Category.comp_id]

end Coherence

/-! ## The eight balancing laws -/

section Eight

variable {D : Type u}

/-- Balancing at parity pattern even-even-even. -/
theorem gpair_balanced_eee
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D] {R : D} [MonObj R]
    (M : Mod D R) (N : Mod D R)
    (b : 𝟙_ D ⟶ R) (m : 𝟙_ D ⟶ M.X)
    (n : 𝟙_ D ⟶ N.X) :
    gpairLin M N (λ_ (𝟙_ D)).inv (gactLin (λ_ (𝟙_ D)).inv b m) n =
      gpairLin M N (λ_ (𝟙_ D)).inv m
        (gactLin (λ_ (𝟙_ D)).inv b n) := by
  refine gpairLin_balance _ _ _ _ ?_ b m n
  rw [leftUnitor_inv_braiding]
  monoidal

/-- Balancing at parity pattern even-odd-odd. -/
theorem gpair_balanced_eoo
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D] (L : OddLine D) {R : D}
    [MonObj R] (M : Mod D R) (N : Mod D R)
    (b : 𝟙_ D ⟶ R) (m : L.obj ⟶ M.X)
    (n : L.obj ⟶ N.X) :
    gpairLin M N L.sq.inv (gactLin (λ_ L.obj).inv b m) n =
      gpairLin M N L.sq.inv m (gactLin (λ_ L.obj).inv b n) := by
  refine gpairLin_balance _ _ _ _ ?_ b m n
  rw [leftUnitor_inv_braiding]
  monoidal

/-- Balancing at parity pattern odd-even-odd: the scalar is odd and
the left argument even, so there is no sign. -/
theorem gpair_balanced_oeo
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D] (L : OddLine D) {R : D}
    [MonObj R] (M : Mod D R) (N : Mod D R)
    (c : L.obj ⟶ R) (m : 𝟙_ D ⟶ M.X)
    (n : L.obj ⟶ N.X) :
    gpairLin M N L.sq.inv (gactLin (ρ_ L.obj).inv c m) n =
      gpairLin M N (λ_ (𝟙_ D)).inv m (gactLin L.sq.inv c n) := by
  refine gpairLin_balance _ _ _ _ ?_ c m n
  rw [rightUnitor_inv_braiding]
  exact oddLine_sq_leftUnitor L

/-- Balancing at parity pattern odd-odd-even: the scalar and the
left argument are both odd, so the Koszul sign appears. -/
theorem gpair_balanced_ooe
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D] (L : OddLine D) {R : D}
    [MonObj R] (M : Mod D R) (N : Mod D R)
    (c : L.obj ⟶ R) (m : L.obj ⟶ M.X)
    (n : 𝟙_ D ⟶ N.X) :
    gpairLin M N (λ_ (𝟙_ D)).inv (gactLin L.sq.inv c m) n =
      -gpairLin M N L.sq.inv m (gactLin (ρ_ L.obj).inv c n) := by
  refine gpairLin_balance_neg _ _ _ _ ?_ c m n
  rw [oddLine_sq_inv_braiding, neg_whiskerRight,
    Preadditive.neg_comp, Preadditive.comp_neg, neg_inj]
  exact oddLine_sq_rightUnitor L

/-- Balancing at parity pattern even-even-odd. -/
theorem gpair_balanced_eeo
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D] (L : OddLine D) {R : D}
    [MonObj R] (M : Mod D R) (N : Mod D R)
    (b : 𝟙_ D ⟶ R) (m : 𝟙_ D ⟶ M.X)
    (n : L.obj ⟶ N.X) :
    gpairLin M N (λ_ L.obj).inv (gactLin (λ_ (𝟙_ D)).inv b m) n =
      gpairLin M N (λ_ L.obj).inv m (gactLin (λ_ L.obj).inv b n) := by
  refine gpairLin_balance _ _ _ _ ?_ b m n
  rw [leftUnitor_inv_braiding]
  monoidal

/-- Balancing at parity pattern even-odd-even. -/
theorem gpair_balanced_eoe
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D] (L : OddLine D) {R : D}
    [MonObj R] (M : Mod D R) (N : Mod D R)
    (b : 𝟙_ D ⟶ R) (m : L.obj ⟶ M.X)
    (n : 𝟙_ D ⟶ N.X) :
    gpairLin M N (ρ_ L.obj).inv (gactLin (λ_ L.obj).inv b m) n =
      gpairLin M N (ρ_ L.obj).inv m
        (gactLin (λ_ (𝟙_ D)).inv b n) := by
  refine gpairLin_balance _ _ _ _ ?_ b m n
  rw [leftUnitor_inv_braiding]
  monoidal

/-- Balancing at parity pattern odd-even-even: the left argument is
even, so there is no sign. -/
theorem gpair_balanced_oee
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D] (L : OddLine D) {R : D}
    [MonObj R] (M : Mod D R) (N : Mod D R)
    (c : L.obj ⟶ R) (m : 𝟙_ D ⟶ M.X)
    (n : 𝟙_ D ⟶ N.X) :
    gpairLin M N (ρ_ L.obj).inv (gactLin (ρ_ L.obj).inv c m) n =
      gpairLin M N (λ_ L.obj).inv m (gactLin (ρ_ L.obj).inv c n) := by
  refine gpairLin_balance _ _ _ _ ?_ c m n
  rw [rightUnitor_inv_braiding]
  monoidal

/-- Balancing at parity pattern odd-odd-odd: the scalar and the
left argument are both odd, so the Koszul sign appears. -/
theorem gpair_balanced_ooo
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D] (L : OddLine D) {R : D}
    [MonObj R] (M : Mod D R) (N : Mod D R)
    (c : L.obj ⟶ R) (m : L.obj ⟶ M.X)
    (n : L.obj ⟶ N.X) :
    gpairLin M N (λ_ L.obj).inv (gactLin L.sq.inv c m) n =
      -gpairLin M N (ρ_ L.obj).inv m (gactLin L.sq.inv c n) := by
  refine gpairLin_balance_neg _ _ _ _ ?_ c m n
  rw [oddLine_sq_inv_braiding, neg_whiskerRight,
    Preadditive.neg_comp, Preadditive.comp_neg, neg_inj]
  exact oddLine_sq_assoc L

end Eight

/-! ## The eight action laws -/

section EightAct

variable {D : Type u}

/-- The action law at parity pattern even-even-even. -/
theorem gpair_act_eee
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    {R : D} [MonObj R] [IsCommMonObj R] (M : Mod D R) (N : Mod D R)
    (x : 𝟙_ D ⟶ R) (m : 𝟙_ D ⟶ M.X)
    (n : 𝟙_ D ⟶ N.X) :
    gactLin (M := (modTensorMod R M N).X) (λ_ (𝟙_ D)).inv x
        (gpairLin M N (λ_ (𝟙_ D)).inv m n) =
      gpairLin M N (λ_ (𝟙_ D)).inv
        (gactLin (λ_ (𝟙_ D)).inv x m) n :=
  gpairLin_act _ _ _ _ (by monoidal) x m n

/-- The action law at parity pattern even-odd-odd. -/
theorem gpair_act_eoo
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) {R : D} [MonObj R] [IsCommMonObj R] (M : Mod D R)
    (N : Mod D R)
    (x : 𝟙_ D ⟶ R) (m : L.obj ⟶ M.X)
    (n : L.obj ⟶ N.X) :
    gactLin (M := (modTensorMod R M N).X) (λ_ (𝟙_ D)).inv x
        (gpairLin M N L.sq.inv m n) =
      gpairLin M N L.sq.inv (gactLin (λ_ L.obj).inv x m) n :=
  gpairLin_act _ _ _ _ (oddLine_sq_leftUnitor' L) x m n

/-- The action law at parity pattern even-even-odd. -/
theorem gpair_act_eeo
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) {R : D} [MonObj R] [IsCommMonObj R] (M : Mod D R)
    (N : Mod D R)
    (x : 𝟙_ D ⟶ R) (m : 𝟙_ D ⟶ M.X)
    (n : L.obj ⟶ N.X) :
    gactLin (M := (modTensorMod R M N).X) (λ_ L.obj).inv x
        (gpairLin M N (λ_ L.obj).inv m n) =
      gpairLin M N (λ_ L.obj).inv (gactLin (λ_ (𝟙_ D)).inv x m) n :=
  gpairLin_act _ _ _ _ (by monoidal) x m n

/-- The action law at parity pattern even-odd-even. -/
theorem gpair_act_eoe
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) {R : D} [MonObj R] [IsCommMonObj R] (M : Mod D R)
    (N : Mod D R)
    (x : 𝟙_ D ⟶ R) (m : L.obj ⟶ M.X)
    (n : 𝟙_ D ⟶ N.X) :
    gactLin (M := (modTensorMod R M N).X) (λ_ L.obj).inv x
        (gpairLin M N (ρ_ L.obj).inv m n) =
      gpairLin M N (ρ_ L.obj).inv (gactLin (λ_ L.obj).inv x m) n :=
  gpairLin_act _ _ _ _ (by monoidal) x m n

/-- The action law at parity pattern odd-even-even. -/
theorem gpair_act_oee
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) {R : D} [MonObj R] [IsCommMonObj R] (M : Mod D R)
    (N : Mod D R)
    (u : L.obj ⟶ R) (m : 𝟙_ D ⟶ M.X)
    (n : 𝟙_ D ⟶ N.X) :
    gactLin (M := (modTensorMod R M N).X) (ρ_ L.obj).inv u
        (gpairLin M N (λ_ (𝟙_ D)).inv m n) =
      gpairLin M N (ρ_ L.obj).inv (gactLin (ρ_ L.obj).inv u m) n :=
  gpairLin_act _ _ _ _ (by monoidal) u m n

/-- The action law at parity pattern odd-odd-odd. -/
theorem gpair_act_ooo
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) {R : D} [MonObj R] [IsCommMonObj R] (M : Mod D R)
    (N : Mod D R)
    (u : L.obj ⟶ R) (m : L.obj ⟶ M.X)
    (n : L.obj ⟶ N.X) :
    gactLin (M := (modTensorMod R M N).X) (ρ_ L.obj).inv u
        (gpairLin M N L.sq.inv m n) =
      gpairLin M N (λ_ L.obj).inv (gactLin L.sq.inv u m) n :=
  gpairLin_act _ _ _ _ (oddLine_sq_assoc' L) u m n

/-- The action law at parity pattern odd-even-odd. -/
theorem gpair_act_oeo
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) {R : D} [MonObj R] [IsCommMonObj R] (M : Mod D R)
    (N : Mod D R)
    (u : L.obj ⟶ R) (m : 𝟙_ D ⟶ M.X)
    (n : L.obj ⟶ N.X) :
    gactLin (M := (modTensorMod R M N).X) L.sq.inv u
        (gpairLin M N (λ_ L.obj).inv m n) =
      gpairLin M N L.sq.inv (gactLin (ρ_ L.obj).inv u m) n :=
  gpairLin_act _ _ _ _ (by monoidal) u m n

/-- The action law at parity pattern odd-odd-even. -/
theorem gpair_act_ooe
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) {R : D} [MonObj R] [IsCommMonObj R] (M : Mod D R)
    (N : Mod D R)
    (u : L.obj ⟶ R) (m : L.obj ⟶ M.X)
    (n : 𝟙_ D ⟶ N.X) :
    gactLin (M := (modTensorMod R M N).X) L.sq.inv u
        (gpairLin M N (ρ_ L.obj).inv m n) =
      gpairLin M N (λ_ (𝟙_ D)).inv (gactLin L.sq.inv u m) n :=
  gpairLin_act _ _ _ _ (oddLine_sq_rightUnitor' L) u m n

end EightAct

/-! ## The comparison map -/

section Comparison

variable {D : Type u}

open SuperCommAlgebra.Mod

/-- The even block of the comparison map: the pairing on the
even-even and odd-odd blocks, factored through the even part of
the tensor product of super modules by its universal property. -/
noncomputable def gammaPairEven
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (M : Mod D R)
    (N : Mod D R) :
    ((gammaModule D L R M.X).tensor (gammaModule D L R N.X)).even
      →ₗ[ℂ] (gammaModule D L R (modTensorMod R M N).X).even :=
  liftEven (gammaModule D L R M.X) (gammaModule D L R N.X)
    (gpairLin M N (λ_ (𝟙_ D)).inv) (gpairLin M N L.sq.inv)
    (gpair_balanced_eee M N) (gpair_balanced_eoo L M N)
    (gpair_balanced_oeo L M N) (gpair_balanced_ooe L M N)

/-- The odd block of the comparison map: the pairing on the
even-odd and odd-even blocks, factored through the odd part of the
tensor product of super modules by its universal property. -/
noncomputable def gammaPairOdd
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (M : Mod D R)
    (N : Mod D R) :
    ((gammaModule D L R M.X).tensor (gammaModule D L R N.X)).odd
      →ₗ[ℂ] (gammaModule D L R (modTensorMod R M N).X).odd :=
  liftOdd (gammaModule D L R M.X) (gammaModule D L R N.X)
    (gpairLin M N (λ_ L.obj).inv) (gpairLin M N (ρ_ L.obj).inv)
    (gpair_balanced_eeo L M N) (gpair_balanced_eoe L M N)
    (gpair_balanced_oee L M N) (gpair_balanced_ooo L M N)

/-- The even block on even-even generators. -/
@[simp] theorem gammaPairEven_tmulEE
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (M : Mod D R)
    (N : Mod D R)
    (m : 𝟙_ D ⟶ M.X) (n : 𝟙_ D ⟶ N.X) :
    gammaPairEven L R M N
        (tmulEE (gammaModule D L R M.X) (gammaModule D L R N.X)
          m n) = gpairLin M N (λ_ (𝟙_ D)).inv m n :=
  liftEven_tmulEE (gammaModule D L R M.X) (gammaModule D L R N.X)
    (gpairLin M N (λ_ (𝟙_ D)).inv) (gpairLin M N L.sq.inv)
    (gpair_balanced_eee M N) (gpair_balanced_eoo L M N)
    (gpair_balanced_oeo L M N) (gpair_balanced_ooe L M N) m n

/-- The even block on odd-odd generators. -/
@[simp] theorem gammaPairEven_tmulOO
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (M : Mod D R)
    (N : Mod D R)
    (m : L.obj ⟶ M.X) (n : L.obj ⟶ N.X) :
    gammaPairEven L R M N
        (tmulOO (gammaModule D L R M.X) (gammaModule D L R N.X)
          m n) = gpairLin M N L.sq.inv m n :=
  liftEven_tmulOO (gammaModule D L R M.X) (gammaModule D L R N.X)
    (gpairLin M N (λ_ (𝟙_ D)).inv) (gpairLin M N L.sq.inv)
    (gpair_balanced_eee M N) (gpair_balanced_eoo L M N)
    (gpair_balanced_oeo L M N) (gpair_balanced_ooe L M N) m n

/-- The odd block on even-odd generators. -/
@[simp] theorem gammaPairOdd_tmulEO
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (M : Mod D R)
    (N : Mod D R)
    (m : 𝟙_ D ⟶ M.X) (n : L.obj ⟶ N.X) :
    gammaPairOdd L R M N
        (tmulEO (gammaModule D L R M.X) (gammaModule D L R N.X)
          m n) = gpairLin M N (λ_ L.obj).inv m n :=
  liftOdd_tmulEO (gammaModule D L R M.X) (gammaModule D L R N.X)
    (gpairLin M N (λ_ L.obj).inv) (gpairLin M N (ρ_ L.obj).inv)
    (gpair_balanced_eeo L M N) (gpair_balanced_eoe L M N)
    (gpair_balanced_oee L M N) (gpair_balanced_ooo L M N) m n

/-- The odd block on odd-even generators. -/
@[simp] theorem gammaPairOdd_tmulOE
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (M : Mod D R)
    (N : Mod D R)
    (m : L.obj ⟶ M.X) (n : 𝟙_ D ⟶ N.X) :
    gammaPairOdd L R M N
        (tmulOE (gammaModule D L R M.X) (gammaModule D L R N.X)
          m n) = gpairLin M N (ρ_ L.obj).inv m n :=
  liftOdd_tmulOE (gammaModule D L R M.X) (gammaModule D L R N.X)
    (gpairLin M N (λ_ L.obj).inv) (gpairLin M N (ρ_ L.obj).inv)
    (gpair_balanced_eeo L M N) (gpair_balanced_eoe L M N)
    (gpair_balanced_oee L M N) (gpair_balanced_ooo L M N) m n

/-- The even block intertwines the action of an even scalar. -/
theorem gammaPairEven_actEE
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (M : Mod D R)
    (N : Mod D R)
    (x : 𝟙_ D ⟶ R)
    (t : ((gammaModule D L R M.X).tensor
      (gammaModule D L R N.X)).even) :
    gammaPairEven L R M N
        (((gammaModule D L R M.X).tensor
          (gammaModule D L R N.X)).actEE x t) =
      (gammaModule D L R (modTensorMod R M N).X).actEE x
        (gammaPairEven L R M N t) := by
  have key : (gammaPairEven L R M N).comp
        (((gammaModule D L R M.X).tensor
          (gammaModule D L R N.X)).actEE x) =
      ((gammaModule D L R (modTensorMod R M N).X).actEE x).comp
        (gammaPairEven L R M N) := by
    refine liftEven_unique _ _ _ _ ?_ ?_
    · intro m n
      show gammaPairEven L R M N (tmulEE _ _
          ((gammaModule D L R M.X).actEE x m) n) =
        (gammaModule D L R (modTensorMod R M N).X).actEE x
          (gammaPairEven L R M N (tmulEE _ _ m n))
      erw [gammaPairEven_tmulEE, gammaPairEven_tmulEE]
      exact (gpair_act_eee M N x m n).symm
    · intro m n
      show gammaPairEven L R M N (tmulOO _ _
          ((gammaModule D L R M.X).actEO x m) n) =
        (gammaModule D L R (modTensorMod R M N).X).actEE x
          (gammaPairEven L R M N (tmulOO _ _ m n))
      erw [gammaPairEven_tmulOO, gammaPairEven_tmulOO]
      exact (gpair_act_eoo L M N x m n).symm
  exact LinearMap.congr_fun key t

/-- The odd block intertwines the action of an even scalar. -/
theorem gammaPairOdd_actEO
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (M : Mod D R)
    (N : Mod D R)
    (x : 𝟙_ D ⟶ R)
    (t : ((gammaModule D L R M.X).tensor
      (gammaModule D L R N.X)).odd) :
    gammaPairOdd L R M N
        (((gammaModule D L R M.X).tensor
          (gammaModule D L R N.X)).actEO x t) =
      (gammaModule D L R (modTensorMod R M N).X).actEO x
        (gammaPairOdd L R M N t) := by
  have key : (gammaPairOdd L R M N).comp
        (((gammaModule D L R M.X).tensor
          (gammaModule D L R N.X)).actEO x) =
      ((gammaModule D L R (modTensorMod R M N).X).actEO x).comp
        (gammaPairOdd L R M N) := by
    refine liftOdd_unique _ _ _ _ ?_ ?_
    · intro m n
      show gammaPairOdd L R M N (tmulEO _ _
          ((gammaModule D L R M.X).actEE x m) n) =
        (gammaModule D L R (modTensorMod R M N).X).actEO x
          (gammaPairOdd L R M N (tmulEO _ _ m n))
      erw [gammaPairOdd_tmulEO, gammaPairOdd_tmulEO]
      exact (gpair_act_eeo L M N x m n).symm
    · intro m n
      show gammaPairOdd L R M N (tmulOE _ _
          ((gammaModule D L R M.X).actEO x m) n) =
        (gammaModule D L R (modTensorMod R M N).X).actEO x
          (gammaPairOdd L R M N (tmulOE _ _ m n))
      erw [gammaPairOdd_tmulOE, gammaPairOdd_tmulOE]
      exact (gpair_act_eoe L M N x m n).symm
  exact LinearMap.congr_fun key t

/-- The two blocks intertwine the action of an odd scalar on the
even part. -/
theorem gammaPairOdd_actOE
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (M : Mod D R)
    (N : Mod D R)
    (u : L.obj ⟶ R)
    (t : ((gammaModule D L R M.X).tensor
      (gammaModule D L R N.X)).even) :
    gammaPairOdd L R M N
        (((gammaModule D L R M.X).tensor
          (gammaModule D L R N.X)).actOE u t) =
      (gammaModule D L R (modTensorMod R M N).X).actOE u
        (gammaPairEven L R M N t) := by
  have key : (gammaPairOdd L R M N).comp
        (((gammaModule D L R M.X).tensor
          (gammaModule D L R N.X)).actOE u) =
      ((gammaModule D L R (modTensorMod R M N).X).actOE u).comp
        (gammaPairEven L R M N) := by
    refine liftEven_unique _ _ _ _ ?_ ?_
    · intro m n
      show gammaPairOdd L R M N (tmulOE _ _
          ((gammaModule D L R M.X).actOE u m) n) =
        (gammaModule D L R (modTensorMod R M N).X).actOE u
          (gammaPairEven L R M N (tmulEE _ _ m n))
      erw [gammaPairOdd_tmulOE, gammaPairEven_tmulEE]
      exact (gpair_act_oee L M N u m n).symm
    · intro m n
      show gammaPairOdd L R M N (tmulEO _ _
          ((gammaModule D L R M.X).actOO u m) n) =
        (gammaModule D L R (modTensorMod R M N).X).actOE u
          (gammaPairEven L R M N (tmulOO _ _ m n))
      erw [gammaPairOdd_tmulEO, gammaPairEven_tmulOO]
      exact (gpair_act_ooo L M N u m n).symm
  exact LinearMap.congr_fun key t

/-- The two blocks intertwine the action of an odd scalar on the
odd part. -/
theorem gammaPairEven_actOO
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (M : Mod D R)
    (N : Mod D R)
    (u : L.obj ⟶ R)
    (t : ((gammaModule D L R M.X).tensor
      (gammaModule D L R N.X)).odd) :
    gammaPairEven L R M N
        (((gammaModule D L R M.X).tensor
          (gammaModule D L R N.X)).actOO u t) =
      (gammaModule D L R (modTensorMod R M N).X).actOO u
        (gammaPairOdd L R M N t) := by
  have key : (gammaPairEven L R M N).comp
        (((gammaModule D L R M.X).tensor
          (gammaModule D L R N.X)).actOO u) =
      ((gammaModule D L R (modTensorMod R M N).X).actOO u).comp
        (gammaPairOdd L R M N) := by
    refine liftOdd_unique _ _ _ _ ?_ ?_
    · intro m n
      show gammaPairEven L R M N (tmulOO _ _
          ((gammaModule D L R M.X).actOE u m) n) =
        (gammaModule D L R (modTensorMod R M N).X).actOO u
          (gammaPairOdd L R M N (tmulEO _ _ m n))
      erw [gammaPairEven_tmulOO, gammaPairOdd_tmulEO]
      exact (gpair_act_oeo L M N u m n).symm
    · intro m n
      show gammaPairEven L R M N (tmulEE _ _
          ((gammaModule D L R M.X).actOO u m) n) =
        (gammaModule D L R (modTensorMod R M N).X).actOO u
          (gammaPairOdd L R M N (tmulOE _ _ m n))
      erw [gammaPairEven_tmulEE, gammaPairOdd_tmulOE]
      exact (gpair_act_ooe L M N u m n).symm
  exact LinearMap.congr_fun key t

/-- **The comparison map of Deligne's (2.11.1)**: the tensor
product over the Γ-algebra of the two Γ-modules maps to the
Γ-module of the relative tensor product of the two module objects.

The two blocks are the pairing `RS.gpair` conjugated by the four
source identifications, and they descend by the universal property
of `RS.SuperCommAlgebra.Mod.tensor` because the eight balancing
laws hold; that they are morphisms of super modules is the eight
action laws. -/
noncomputable def gammaPairComparison
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] (M : Mod D R)
    (N : Mod D R) :
    (gammaModule D L R M.X).tensor (gammaModule D L R N.X) ⟶
      gammaModule D L R (modTensorMod R M N).X where
  evenMap := gammaPairEven L R M N
  oddMap := gammaPairOdd L R M N
  map_actEE := gammaPairEven_actEE L R M N
  map_actEO := gammaPairOdd_actEO L R M N
  map_actOE := gammaPairOdd_actOE L R M N
  map_actOO := gammaPairEven_actOO L R M N

end Comparison

end RS
