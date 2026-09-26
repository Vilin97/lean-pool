/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowDatum

/-!
# The symmetric power duality datum

Duality data transfer along module maps, and its instance of
record: the symmetric powers of a dual pair form a dual pair,
by transferring the power datum along the symmetriser section
and projection.  The transfer needs no compatibility between the
chosen maps — linearity is compositional; the zigzag laws of the
transferred datum are where retraction and self-adjointness
enter, and they live with the pairing calculus.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

section Transfer

/-- **Duality data transfer**: a duality datum for a pair of
modules induces one on any pair connected to it by module maps —
the pairing pulls back along maps into the pair, the copairing
pushes forward along maps out of it.  Linearity is inherited
compositionally. -/
noncomputable def ModDualityDatum.transfer
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {P : Mod D A} {P' : Mod D A}
    {Q : Mod D A} {Q' : Mod D A}
    (d : ModDualityDatum A P P') (s : Q ⟶ P) (s' : Q' ⟶ P')
    (r : P ⟶ Q) (r' : P' ⟶ Q') : ModDualityDatum A Q Q' where
  pair := modTensorMap A s' s ≫ d.pair
  copair := d.copair ≫ modTensorMap A r r'
  pair_linear := by
    let := modTensorModObj A Q' Q
    let := modTensorModObj A P' P
    have hp : modTensorAct A P' P ≫ d.pair =
        (A ◁ d.pair) ≫ μ[A] := d.pair_linear
    change modTensorAct A Q' Q ≫ modTensorMap A s' s ≫ d.pair =
      (A ◁ (modTensorMap A s' s ≫ d.pair)) ≫ μ[A]
    rw [← Category.assoc, modTensorAct_map, Category.assoc, hp,
      ← MonoidalCategory.whiskerLeft_comp_assoc]
  copair_linear := by
    let := modTensorModObj A Q Q'
    let := modTensorModObj A P P'
    have hc : μ[A] ≫ d.copair =
        (A ◁ d.copair) ≫ modTensorAct A P P' := d.copair_linear
    change μ[A] ≫ d.copair ≫ modTensorMap A r r' =
      (A ◁ (d.copair ≫ modTensorMap A r r')) ≫
        modTensorAct A Q Q'
    rw [← Category.assoc, hc, Category.assoc, modTensorAct_map,
      ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp]

end Transfer

section SymBundles

/-- The symmetriser projection, as a morphism of bundled
modules; the mirror of `symPowσMod`. -/
noncomputable def symPowπMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D] {X : D} [ModObj A X]
    (n : ℕ) :
    modPowMod A X n ⟶ symPowMod A X n :=
  letI := symPowModObj A X n
  letI := modPowModObj A X n
  Mod.Hom.mk (symPowπ A X (n + 1))
    (isModHom :=
      ⟨(whiskerLeft_symPowπ_symPowAct A X n).symm⟩)

end SymBundles

section SymDatum

/-- **The symmetric power duality datum**: the symmetric powers
of a dual pair form a dual pair, by transferring the power datum
along the symmetriser section and projection. -/
noncomputable def symDualityDatum
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    ModDualityDatum A (symPowMod A M.X n) (symPowMod A M'.X n) :=
  (powDualityDatum A M M' d n).transfer A
    (symPowσMod A n) (symPowσMod A n)
    (symPowπMod A n) (symPowπMod A n)

end SymDatum

end RS
