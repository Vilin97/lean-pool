/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ZigzagCarrier
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SymDatum
import LeanPool.RegtsSevenster.RS.Classical.Deligne.PairPerm

/-!
# Transfer of the zigzag laws along retractions

The zigzag laws pass from a duality datum to its transfer along a
section–retraction pair, given the self-adjointness of the
composite idempotent across the pairing.  The transferred zig
factors as section, original zig, retraction: the idempotent
slides across the pairing once and then dissolves into the
retraction.  Instantiated at the symmetriser section and
projection, this gives the zigzag laws of the symmetric-power
datum from those of the power datum — Deligne's 1.15.1.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

section Equivariance

end Equivariance

section Transfer

/-- **Retraction images contract through the transferred
contraction**: precomposing the transferred zig contraction with
the retraction image is the section, the original contraction,
and the retraction — the idempotent slides across the pairing
and dissolves into the retraction. -/
theorem map_zigContract
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {P : Mod D A} {P' : Mod D A}
    {Q : Mod D A} {Q' : Mod D A} (d₀ : ModDualityDatum A P P') (s : Q ⟶ P)
    (s' : Q' ⟶ P') (r : P ⟶ Q) (r' : P' ⟶ Q')
    (hsr : s ≫ r = 𝟙 Q)
    (hadj : modTensorMap A (r' ≫ s') (𝟙 P) ≫ d₀.pair =
      modTensorMap A (𝟙 P') (r ≫ s) ≫ d₀.pair) :
    (modTensorMap A r r' ▷ Q.X) ≫
      zigContract A (d₀.transfer A s s' r r').pair
        (d₀.transfer A s s' r r').pair_linear =
      (modTensor A P P' ◁ s.hom) ≫
        zigContract A d₀.pair d₀.pair_linear ≫ r.hom := by
  apply modTensor_whiskerR_hom_ext A P P' Q.X
  have hpair : (d₀.transfer A s s' r r').pair =
      modTensorMap A s' s ≫ d₀.pair := rfl
  -- The inner pairing occurrence: idempotent slide and
  -- dissolution into the retraction.
  have hstep1 : (r'.hom ⊗ₘ 𝟙 Q.X) ≫ modTensorπ A Q' Q =
      modTensorπ A P' Q ≫ modTensorMap A r' (𝟙 Q) :=
    (modTensorπ_map A r' (𝟙 Q)).symm
  have hstep2 : (𝟙 P'.X ⊗ₘ s.hom) ≫ modTensorπ A P' P =
      modTensorπ A P' Q ≫ modTensorMap A (𝟙 P') s :=
    (modTensorπ_map A (𝟙 P') s).symm
  have hmaps : modTensorMap A r' (𝟙 Q) ≫ modTensorMap A s' s =
      modTensorMap A (𝟙 P') s ≫
        modTensorMap A (r' ≫ s') (𝟙 P) := by
    rw [← modTensorMap_comp, ← modTensorMap_comp,
      Category.id_comp, Category.id_comp, Category.comp_id]
  have hs3 : s ≫ r ≫ s = s := by
    rw [← Category.assoc, hsr, Category.id_comp]
  have hinner : (r'.hom ⊗ₘ 𝟙 Q.X) ≫
      (modTensorπ A Q' Q ≫ (d₀.transfer A s s' r r').pair) =
      (𝟙 P'.X ⊗ₘ s.hom) ≫
        (modTensorπ A P' P ≫ d₀.pair) := by
    rw [hpair, ← Category.assoc, hstep1, Category.assoc,
      ← Category.assoc (modTensorMap A r' (𝟙 Q)), hmaps,
      Category.assoc, hadj,
      ← Category.assoc (modTensorMap A (𝟙 P') s),
      ← modTensorMap_comp, Category.id_comp, hs3,
      ← Category.assoc, ← hstep2, Category.assoc]
  -- Reduce the left side to the raw word and slide.
  have hA : ((r.hom ⊗ₘ r'.hom) ▷ Q.X) ≫
      (α_ Q.X Q'.X Q.X).hom =
      (α_ P.X P'.X Q.X).hom ≫
        (r.hom ⊗ₘ (r'.hom ⊗ₘ 𝟙 Q.X)) := by
    simpa using associator_naturality r.hom r'.hom (𝟙 Q.X)
  have hB : (r.hom ⊗ₘ (r'.hom ⊗ₘ 𝟙 Q.X)) ≫
      (Q.X ◁ (modTensorπ A Q' Q ≫
        (d₀.transfer A s s' r r').pair)) =
      r.hom ⊗ₘ ((r'.hom ⊗ₘ 𝟙 Q.X) ≫
        (modTensorπ A Q' Q ≫
          (d₀.transfer A s s' r r').pair)) := by
    simpa using MonoidalCategory.tensorHom_comp_tensorHom
      r.hom (r'.hom ⊗ₘ 𝟙 Q.X) (𝟙 Q.X)
      (modTensorπ A Q' Q ≫ (d₀.transfer A s s' r r').pair)
  have hC : r.hom ⊗ₘ ((𝟙 P'.X ⊗ₘ s.hom) ≫
      (modTensorπ A P' P ≫ d₀.pair)) =
      (P.X ◁ (𝟙 P'.X ⊗ₘ s.hom)) ≫
        (r.hom ⊗ₘ (modTensorπ A P' P ≫ d₀.pair)) := by
    simpa using (MonoidalCategory.tensorHom_comp_tensorHom
      (𝟙 P.X) (𝟙 P'.X ⊗ₘ s.hom) r.hom
      (modTensorπ A P' P ≫ d₀.pair)).symm
  have hD : (r.hom ⊗ₘ (modTensorπ A P' P ≫ d₀.pair)) ≫
      actRight A Q.X =
      (P.X ◁ (modTensorπ A P' P ≫ d₀.pair)) ≫
        actRight A P.X ≫ r.hom := by
    have hd1 : r.hom ⊗ₘ (modTensorπ A P' P ≫ d₀.pair) =
        (P.X ◁ (modTensorπ A P' P ≫ d₀.pair)) ≫
          (r.hom ▷ A) :=
      MonoidalCategory.tensorHom_def' _ _
    rw [hd1, Category.assoc, ← actRight_natural_mod]
  have hE : (α_ P.X P'.X Q.X).hom ≫
      (P.X ◁ (𝟙 P'.X ⊗ₘ s.hom)) =
      ((P.X ⊗ P'.X) ◁ s.hom) ≫ (α_ P.X P'.X P.X).hom := by
    simp
  conv_lhs => rw [← comp_whiskerRight_assoc, modTensorπ_map,
    comp_whiskerRight, Category.assoc,
    whiskerRight_modTensorπ_zigContract, reassoc_of% hA,
    reassoc_of% hB, hinner, hC, Category.assoc, hD,
    reassoc_of% hE]
  conv_rhs => rw [← whisker_exchange_assoc,
    whiskerRight_modTensorπ_zigContract_assoc]

/-- **The transferred carrier zig identity**: the zig of the
transferred datum factors as section, original zig, retraction. -/
theorem transfer_carrier_zig
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {P : Mod D A} {P' : Mod D A}
    {Q : Mod D A} {Q' : Mod D A} (d₀ : ModDualityDatum A P P') (s : Q ⟶ P)
    (s' : Q' ⟶ P') (r : P ⟶ Q) (r' : P' ⟶ Q')
    (hz₀ : ModZigzagDatum A d₀)
    (hsr : s ≫ r = 𝟙 Q)
    (hadj : modTensorMap A (r' ≫ s') (𝟙 P) ≫ d₀.pair =
      modTensorMap A (𝟙 P') (r ≫ s) ≫ d₀.pair) :
    (λ_ Q.X).inv ≫
      ((η[A] ≫ (d₀.transfer A s s' r r').copair) ▷ Q.X) ≫
      zigContract A (d₀.transfer A s s' r r').pair
        (d₀.transfer A s s' r r').pair_linear = 𝟙 Q.X := by
  have hcop : (d₀.transfer A s s' r r').copair =
      d₀.copair ≫ modTensorMap A r r' := rfl
  have hins : (λ_ Q.X).inv ≫
      ((η[A] ≫ d₀.copair) ▷ Q.X) ≫
      (modTensor A P P' ◁ s.hom) =
      s.hom ≫ (λ_ P.X).inv ≫ ((η[A] ≫ d₀.copair) ▷ P.X) := by
    rw [← whisker_exchange, ← leftUnitor_inv_naturality_assoc]
  rw [hcop, ← Category.assoc η[A], comp_whiskerRight,
    Category.assoc, map_zigContract A d₀ s s' r r' hsr hadj,
    ← Category.assoc, ← Category.assoc, Category.assoc
      ((λ_ Q.X).inv), hins, Category.assoc, Category.assoc,
    zigzag_carrier_zig_assoc A hz₀]
  have : s.hom ≫ r.hom = 𝟙 Q.X := by
    have h2 := congrArg Mod.Hom.hom hsr
    simpa using h2
  exact this

/-- **Retraction images contract through the transferred zag
contraction**: the mirror of `map_zigContract`. -/
theorem map_zagContract
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {P : Mod D A} {P' : Mod D A}
    {Q : Mod D A} {Q' : Mod D A} (d₀ : ModDualityDatum A P P') (s : Q ⟶ P)
    (s' : Q' ⟶ P') (r : P ⟶ Q) (r' : P' ⟶ Q')
    (hsr' : s' ≫ r' = 𝟙 Q')
    (hadj : modTensorMap A (r' ≫ s') (𝟙 P) ≫ d₀.pair =
      modTensorMap A (𝟙 P') (r ≫ s) ≫ d₀.pair) :
    (Q'.X ◁ modTensorMap A r r') ≫
      zagContract A (d₀.transfer A s s' r r').pair
        (d₀.transfer A s s' r r').pair_linear =
      (s'.hom ▷ modTensor A P P') ≫
        zagContract A d₀.pair d₀.pair_linear ≫ r'.hom := by
  apply modTensor_whisker_hom_ext A P P' Q'.X
  have hpair : (d₀.transfer A s s' r r').pair =
      modTensorMap A s' s ≫ d₀.pair := rfl
  have hstep1 : (𝟙 Q'.X ⊗ₘ r.hom) ≫ modTensorπ A Q' Q =
      modTensorπ A Q' P ≫ modTensorMap A (𝟙 Q') r :=
    (modTensorπ_map A (𝟙 Q') r).symm
  have hstep2 : (s'.hom ⊗ₘ 𝟙 P.X) ≫ modTensorπ A P' P =
      modTensorπ A Q' P ≫ modTensorMap A s' (𝟙 P) :=
    (modTensorπ_map A s' (𝟙 P)).symm
  have hmaps : modTensorMap A (𝟙 Q') r ≫ modTensorMap A s' s =
      modTensorMap A s' (𝟙 P) ≫
        modTensorMap A (𝟙 P') (r ≫ s) := by
    rw [← modTensorMap_comp, ← modTensorMap_comp,
      Category.id_comp, Category.id_comp, Category.comp_id]
  have hs3 : s' ≫ r' ≫ s' = s' := by
    rw [← Category.assoc, hsr', Category.id_comp]
  have hinner : (𝟙 Q'.X ⊗ₘ r.hom) ≫
      (modTensorπ A Q' Q ≫ (d₀.transfer A s s' r r').pair) =
      (s'.hom ⊗ₘ 𝟙 P.X) ≫
        (modTensorπ A P' P ≫ d₀.pair) := by
    rw [hpair, ← Category.assoc, hstep1, Category.assoc,
      ← Category.assoc (modTensorMap A (𝟙 Q') r), hmaps,
      Category.assoc, ← hadj,
      ← Category.assoc (modTensorMap A s' (𝟙 P)),
      ← modTensorMap_comp, Category.id_comp, hs3,
      ← Category.assoc, ← hstep2, Category.assoc]
  have hA : (Q'.X ◁ (r.hom ⊗ₘ r'.hom)) ≫
      (α_ Q'.X Q.X Q'.X).inv =
      (α_ Q'.X P.X P'.X).inv ≫
        ((𝟙 Q'.X ⊗ₘ r.hom) ⊗ₘ r'.hom) := by
    simpa using associator_inv_naturality (𝟙 Q'.X) r.hom r'.hom
  have hB : ((𝟙 Q'.X ⊗ₘ r.hom) ⊗ₘ r'.hom) ≫
      ((modTensorπ A Q' Q ≫
        (d₀.transfer A s s' r r').pair) ▷ Q'.X) =
      ((𝟙 Q'.X ⊗ₘ r.hom) ≫
        (modTensorπ A Q' Q ≫
          (d₀.transfer A s s' r r').pair)) ⊗ₘ r'.hom := by
    simpa using MonoidalCategory.tensorHom_comp_tensorHom
      (𝟙 Q'.X ⊗ₘ r.hom) r'.hom
      (modTensorπ A Q' Q ≫ (d₀.transfer A s s' r r').pair)
      (𝟙 Q'.X)
  have hC : ((s'.hom ⊗ₘ 𝟙 P.X) ≫
      (modTensorπ A P' P ≫ d₀.pair)) ⊗ₘ r'.hom =
      ((s'.hom ⊗ₘ 𝟙 P.X) ⊗ₘ 𝟙 P'.X) ≫
        ((modTensorπ A P' P ≫ d₀.pair) ⊗ₘ r'.hom) := by
    simpa using (MonoidalCategory.tensorHom_comp_tensorHom
      (s'.hom ⊗ₘ 𝟙 P.X) (𝟙 P'.X)
      (modTensorπ A P' P ≫ d₀.pair) r'.hom).symm
  have hD : ((modTensorπ A P' P ≫ d₀.pair) ⊗ₘ r'.hom) ≫
      actLeft A Q'.X =
      ((modTensorπ A P' P ≫ d₀.pair) ▷ P'.X) ≫
        actLeft A P'.X ≫ r'.hom := by
    have := r'.isModHom
    have hd1 : (modTensorπ A P' P ≫ d₀.pair) ⊗ₘ r'.hom =
        ((modTensorπ A P' P ≫ d₀.pair) ▷ P'.X) ≫
          (A ◁ r'.hom) :=
      MonoidalCategory.tensorHom_def _ _
    rw [hd1, Category.assoc, ← actLeft_natural]
  have hE : (α_ Q'.X P.X P'.X).inv ≫
      ((s'.hom ⊗ₘ 𝟙 P.X) ⊗ₘ 𝟙 P'.X) =
      (s'.hom ▷ (P.X ⊗ P'.X)) ≫
        (α_ P'.X P.X P'.X).inv := by
    simp
  conv_lhs => rw [← MonoidalCategory.whiskerLeft_comp_assoc,
    modTensorπ_map, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, whiskerLeft_modTensorπ_zagContract,
    reassoc_of% hA, reassoc_of% hB, hinner, hC,
    Category.assoc, hD, reassoc_of% hE]
  conv_rhs => rw [whisker_exchange_assoc,
    whiskerLeft_modTensorπ_zagContract_assoc]

/-- **The transferred carrier zag identity**: the mirror
factorization through the dual-side section and retraction. -/
theorem transfer_carrier_zag
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {P : Mod D A} {P' : Mod D A}
    {Q : Mod D A} {Q' : Mod D A} (d₀ : ModDualityDatum A P P') (s : Q ⟶ P)
    (s' : Q' ⟶ P') (r : P ⟶ Q) (r' : P' ⟶ Q')
    (hz₀ : ModZigzagDatum A d₀)
    (hsr' : s' ≫ r' = 𝟙 Q')
    (hadj : modTensorMap A (r' ≫ s') (𝟙 P) ≫ d₀.pair =
      modTensorMap A (𝟙 P') (r ≫ s) ≫ d₀.pair) :
    (ρ_ Q'.X).inv ≫
      (Q'.X ◁ (η[A] ≫ (d₀.transfer A s s' r r').copair)) ≫
      zagContract A (d₀.transfer A s s' r r').pair
        (d₀.transfer A s s' r r').pair_linear = 𝟙 Q'.X := by
  have hcop : (d₀.transfer A s s' r r').copair =
      d₀.copair ≫ modTensorMap A r r' := rfl
  have hins : (ρ_ Q'.X).inv ≫
      (Q'.X ◁ (η[A] ≫ d₀.copair)) ≫
      (s'.hom ▷ modTensor A P P') =
      s'.hom ≫ (ρ_ P'.X).inv ≫
        (P'.X ◁ (η[A] ≫ d₀.copair)) := by
    rw [whisker_exchange, ← rightUnitor_inv_naturality_assoc]
  rw [hcop, ← Category.assoc η[A],
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    map_zagContract A d₀ s s' r r' hsr' hadj,
    ← Category.assoc, ← Category.assoc, Category.assoc
      ((ρ_ Q'.X).inv), hins, Category.assoc, Category.assoc,
    zigzag_carrier_zag_assoc A hz₀]
  have : s'.hom ≫ r'.hom = 𝟙 Q'.X := by
    have h2 := congrArg Mod.Hom.hom hsr'
    simpa using h2
  exact this

/-- **The zigzag laws transfer along retractions**: given the
self-adjointness of the composite idempotents across the pairing,
the transferred datum satisfies the zigzag laws. -/
theorem modZigzagDatum_transfer
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] {P : Mod D A} {P' : Mod D A}
    {Q : Mod D A} {Q' : Mod D A} (d₀ : ModDualityDatum A P P') (s : Q ⟶ P)
    (s' : Q' ⟶ P') (r : P ⟶ Q) (r' : P' ⟶ Q')
    (hz₀ : ModZigzagDatum A d₀)
    (hsr : s ≫ r = 𝟙 Q) (hsr' : s' ≫ r' = 𝟙 Q')
    (hadj : modTensorMap A (r' ≫ s') (𝟙 P) ≫ d₀.pair =
      modTensorMap A (𝟙 P') (r ≫ s) ≫ d₀.pair) :
    ModZigzagDatum A (d₀.transfer A s s' r r') :=
  modZigzagDatum_of_carrier A
    (transfer_carrier_zig A d₀ s s' r r' hz₀ hsr hadj)
    (transfer_carrier_zag A d₀ s s' r r' hz₀ hsr' hadj)

end Transfer

section SymInstance

/-- **The symmetric-power datum inherits the zigzag laws**
(Deligne 1.15.1): the transfer along the symmetriser section and
projection, with the self-adjointness of the symmetriser across
the nested pairing as the idempotent-slide input. -/
theorem symDualityDatum_zigzag
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [CategoryTheory.Linear ℂ D] [MonoidalLinear ℂ D]
    (d : ModDualityDatum A M M')
    (n : ℕ)
    (hz : ModZigzagDatum A (powDualityDatum A M M' d n)) :
    ModZigzagDatum A (symDualityDatum A M M' d n) := by
  have hsr : symPowσMod A n ≫ symPowπMod A n =
      𝟙 (symPowMod A M.X n) :=
    Mod.hom_ext _ _ (symPowσ_symPowπ A M.X (n + 1))
  have hsr' : symPowσMod A n ≫ symPowπMod A n =
      𝟙 (symPowMod A M'.X n) :=
    Mod.hom_ext _ _ (symPowσ_symPowπ A M'.X (n + 1))
  have h1 : (symPowπMod A n ≫ symPowσMod A n :
      modPowMod A M'.X n ⟶ modPowMod A M'.X n).hom =
      symPowIdem A M'.X (n + 1) :=
    symPowπ_symPowσ A M'.X (n + 1)
  have h2 : (symPowπMod A n ≫ symPowσMod A n :
      modPowMod A M.X n ⟶ modPowMod A M.X n).hom =
      symPowIdem A M.X (n + 1) :=
    symPowπ_symPowσ A M.X (n + 1)
  have hadj : modTensorMap A (symPowπMod A n ≫ symPowσMod A n)
      (𝟙 (modPowMod A M.X n)) ≫
      (powDualityDatum A M M' d n).pair =
      modTensorMap A (𝟙 (modPowMod A M'.X n))
        (symPowπMod A n ≫ symPowσMod A n) ≫
        (powDualityDatum A M M' d n).pair := by
    apply modTensor_hom_ext A (modPowMod A M'.X n)
      (modPowMod A M.X n)
    have hp : (powDualityDatum A M M' d n).pair =
        modPowPairing A M M' d n := rfl
    rw [← Category.assoc, modTensorπ_map, ← Category.assoc,
      modTensorπ_map, hp, Category.assoc, Category.assoc,
      modTensorπ_modPowPairing, h1, h2]
    exact symPowIdem_pairPow_tensor A M M' d (n + 1)
  exact modZigzagDatum_transfer A (powDualityDatum A M M' d n)
    (symPowσMod A n) (symPowσMod A n)
    (symPowπMod A n) (symPowπMod A n) hz hsr hsr' hadj

end SymInstance

end RS
