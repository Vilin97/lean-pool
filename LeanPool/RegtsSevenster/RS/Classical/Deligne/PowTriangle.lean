/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowChain
import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainMulLaws

/-!
# The triangle scalar of the power chain

The copairing powers of a duality datum retract against the
nested power pairing: under the scalar zigzag, the pairing
evaluates every chain unit to the unit of the base.  This is the
nonvanishing engine of the Key Lemma's chain.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

section SwapMap

/-- The braiding of the module tensor product is natural. -/
theorem modTensorMap_swap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] {P : Mod D A} {P' : Mod D A}
    {Q : Mod D A} {Q' : Mod D A}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    modTensorMap A f g ≫ modTensorSwap A P' Q' =
      modTensorSwap A P Q ≫ modTensorMap A g f := by
  apply modTensor_hom_ext
  rw [modTensorπ_map_assoc, modTensorπ_swap,
    modTensorπ_swap_assoc, ← Category.assoc,
    BraidedCategory.braiding_naturality, Category.assoc,
    modTensorπ_map]

end SwapMap

/-- The nested pairing at arity one is the pairing, through the
singleton isomorphisms. -/
theorem modPowOne_pairPow
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    ((modPowOne A M'.X).inv ⊗ₘ (modPowOne A M.X).inv) ≫
        pairPow A M M' d 1 = pairRaw A M M' d := by
  have hinv : ∀ (X : D) [ModObj A X], (modPowOne A X).inv =
      (λ_ X).inv ≫ modPowπ A X 1 := by
    intro X _
    erw [modPowOne, Iso.trans_inv]
    rfl
  erw [hinv, hinv, ← MonoidalCategory.tensorHom_comp_tensorHom,
    Category.assoc]
  refine ((congrArg (fun t =>
    ((λ_ M'.X).inv ⊗ₘ (λ_ M.X).inv) ≫ t)
    (modPowπ_tensor_pairPow A M M' d 1)).trans ?_)
  rw [rawPair_succ, rawPair_zero, powPeel_zero]
  change ((λ_ M'.X).inv ⊗ₘ (λ_ M.X).inv) ≫
      ((𝟙_ D ⊗ M'.X) ◁ (λ_ M.X ≪≫ (ρ_ M.X).symm).hom) ≫
      (α_ (𝟙_ D) M'.X (M.X ⊗ 𝟙_ D)).hom ≫
      (𝟙_ D ◁ (α_ M'.X M.X (𝟙_ D)).inv) ≫
      (𝟙_ D ◁ (pairRaw A M M' d ▷ 𝟙_ D)) ≫
      (𝟙_ D ◁ (β_ A (𝟙_ D)).hom) ≫
      (α_ (𝟙_ D) (𝟙_ D) A).inv ≫
      (((λ_ (𝟙_ D)).hom ≫ η[A]) ▷ A) ≫ μ[A] =
    pairRaw A M M' d
  rw [Iso.trans_hom, braiding_tensorUnit_right,
    comp_whiskerRight]
  simp only [Category.assoc]
  rw [MonObj.one_mul]
  dsimp only [Iso.symm_hom]
  monoidal

/-- The Mod-internal power pairing at arity zero is the datum's
pairing, through the singleton stages. -/
theorem toZero_modPowPairing
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    modTensorMap A (toModPowModZero A M') (toModPowModZero A M) ≫
        modPowPairing A M M' d 0 = d.pair := by
  apply modTensor_hom_ext
  rw [modTensorπ_map_assoc, modTensorπ_modPowPairing]
  rw [show (toModPowModZero A M').hom = (modPowOne A M'.X).inv
      from rfl,
    show (toModPowModZero A M).hom = (modPowOne A M.X).inv
      from rfl]
  exact (modPowOne_pairPow A M M' d).trans rfl

/-- **The seed retracts against the pairing**: under the scalar
zigzag, the bottom chain unit evaluates to the unit of the
base. -/
theorem powSeed_pairing
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (hzig : d.copair ≫ modTensorSwap A M M' ≫ d.pair = 𝟙 A) :
    powSeed A M M' d ≫
        modTensorSwap A (modPowMod A M.X 0) (modPowMod A M'.X 0) ≫
        modPowPairing A M M' d 0 = η[A] := by
  erw [powSeed, Category.assoc]
  have hX : modTensorMap A (toModPowModZero A M)
      (toModPowModZero A M') ≫
      modTensorSwap A (modPowMod A M.X 0) (modPowMod A M'.X 0) ≫
      modPowPairing A M M' d 0 =
    modTensorSwap A M M' ≫
      modTensorMap A (toModPowModZero A M')
        (toModPowModZero A M) ≫
      modPowPairing A M M' d 0 := by
    rw [← Category.assoc, modTensorMap_swap, Category.assoc]
  refine ((congrArg (fun t =>
    copairUnit A M M' d ≫ t) hX).trans ?_)
  rw [toZero_modPowPairing, copairUnit, Category.assoc, hzig,
    Category.comp_id]

section PowEpi

/-- The module-power projection is an epimorphism. -/
instance epi_modPowπ [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] (A : D)
    [MonObj A] (X : D) [ModObj A X]
    (n : ℕ) : Epi (modPowπ A X n) :=
  ⟨fun _ _ w => modPow_hom_ext A X w⟩

/-- The tensor product of two module-power projections is an
epimorphism. -/
instance epi_modPowπ_tensorHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (X : D) [ModObj A X] (Y : D) [ModObj A Y]
    (m n : ℕ) :
    Epi (modPowπ A X m ⊗ₘ modPowπ A Y n) := by
  rw [MonoidalCategory.tensorHom_def]
  infer_instance

/-- A tensor pair of power projections whiskered on the right is
an epimorphism. -/
instance epi_modPowπ_tensorHom_whiskerRight
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (X : D) [ModObj A X] (Y : D) [ModObj A Y]
    (m n : ℕ) (W : D) :
    Epi ((modPowπ A X m ⊗ₘ modPowπ A Y n) ▷ W) := by
  rw [MonoidalCategory.tensorHom_def, comp_whiskerRight]
  have h1 : Epi ((modPowπ A X m ▷ tensorPow D Y n) ▷ W) := by
    rw [show (modPowπ A X m ▷ tensorPow D Y n) ▷ W =
        (α_ (tensorPow D X m) (tensorPow D Y n) W).hom ≫
          (modPowπ A X m ▷ (tensorPow D Y n ⊗ W)) ≫
          (α_ (modPow A X m) (tensorPow D Y n) W).inv by
      simp [MonoidalCategory.whiskerRight_tensor]]
    infer_instance
  have h2 : Epi ((modPow A X m ◁ modPowπ A Y n) ▷ W) := by
    rw [MonoidalCategory.whisker_assoc]
    infer_instance
  exact epi_comp _ _

/-- A tensor square of power projection pairs is an
epimorphism. -/
instance epi_modPowπ_tensorHom_tensorHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (X : D) [ModObj A X] (Y : D) [ModObj A Y] (Z' : D)
    (W' : D) [ModObj A Z'] [ModObj A W']
    (a b c e : ℕ) :
    Epi ((modPowπ A X a ⊗ₘ modPowπ A Y b) ⊗ₘ
      (modPowπ A Z' c ⊗ₘ modPowπ A W' e)) := by
  rw [MonoidalCategory.tensorHom_def]
  have h2 : Epi ((modPow A X a ⊗ modPow A Y b) ◁
      (modPowπ A Z' c ⊗ₘ modPowπ A W' e)) := by
    rw [MonoidalCategory.tensorHom_def,
      MonoidalCategory.whiskerLeft_comp]
    have h3 : Epi ((modPow A X a ⊗ modPow A Y b) ◁
        (modPow A Z' c ◁ modPowπ A W' e)) := by
      rw [show (modPow A X a ⊗ modPow A Y b) ◁
          (modPow A Z' c ◁ modPowπ A W' e) =
        (α_ (modPow A X a ⊗ modPow A Y b) (modPow A Z' c)
            (tensorPow D W' e)).inv ≫
          (((modPow A X a ⊗ modPow A Y b) ⊗ modPow A Z' c) ◁
            modPowπ A W' e) ≫
          (α_ (modPow A X a ⊗ modPow A Y b) (modPow A Z' c)
            (modPow A W' e)).hom by simp]
      infer_instance
    exact epi_comp _ _
  exact epi_comp _ _

/-- A left-whiskered power projection whiskered on the right is
an epimorphism. -/
instance epi_whiskerLeft_modPowπ_whiskerRight'
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (X : D) [ModObj A X]
    (n : ℕ)
    (Q W : D) : Epi ((Q ◁ modPowπ A X n) ▷ W) := by
  rw [MonoidalCategory.whisker_assoc]
  infer_instance

end PowEpi

section InterchangeMap

/-- The interchange followed by a functorial map computes under
the stage projections: the raw crossing feeds the two module
maps. -/
@[reassoc]
theorem tensorHom_π_interchange_map
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (N₁ : Mod D A) (N₂ : Mod D A)
    (P₁ : Mod D A) (P₂ : Mod D A)
    {Q R : Mod D A}
    (f : modTensorMod A N₁ P₁ ⟶ Q)
    (g : modTensorMod A N₂ P₂ ⟶ R) :
    (modTensorπ A N₁ N₂ ⊗ₘ modTensorπ A P₁ P₂) ≫
      interchange A N₁ N₂ P₁ P₂ ≫ modTensorMap A f g =
    tensorμ N₁.X N₂.X P₁.X P₂.X ≫
      ((modTensorπ A N₁ P₁ ≫ f.hom) ⊗ₘ
        (modTensorπ A N₂ P₂ ≫ g.hom)) ≫
      modTensorπ A Q R := by
  have h5 : (modTensorπ A N₁ N₂ ⊗ₘ modTensorπ A P₁ P₂) ≫
      interchange A N₁ N₂ P₁ P₂ ≫ modTensorMap A f g =
    ((modTensorπ A N₁ N₂ ⊗ₘ modTensorπ A P₁ P₂) ≫
      interchange A N₁ N₂ P₁ P₂) ≫ modTensorMap A f g :=
    (Category.assoc _ _ _).symm
  rw [h5, tensorHom_π_interchange, rawInterchangeπ,
    rawInterchange]
  simp only [Category.assoc]
  have h6 : modTensorπ A (modTensorMod A N₁ P₁)
      (modTensorMod A N₂ P₂) ≫ modTensorMap A f g =
    (f.hom ⊗ₘ g.hom) ≫ modTensorπ A Q R :=
    modTensorπ_map A f g
  conv_lhs => arg 2; erw [Category.assoc]
  refine congrArg (CategoryStruct.comp _) ?_
  refine (congrArg (CategoryStruct.comp _) h6).trans ?_
  erw [← Category.assoc]
  change ((modTensorπ A N₁ P₁ ⊗ₘ modTensorπ A N₂ P₂) ≫
      (f.hom ⊗ₘ g.hom)) ≫ modTensorπ A Q R = _
  erw [MonoidalCategory.tensorHom_comp_tensorHom]

end InterchangeMap

/-- The transition core under the stage projections: the raw
interchange, the aligned multiplications, and the pairing of the
joined arity. -/
private theorem powDeltaCore_layer1
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    (modTensorπ A (modPowMod A M.X n) (modPowMod A M'.X n) ⊗ₘ
      modTensorπ A (modPowMod A M.X 0) (modPowMod A M'.X 0)) ≫
      interchange A (modPowMod A M.X n) (modPowMod A M'.X n)
        (modPowMod A M.X 0) (modPowMod A M'.X 0) ≫
      modTensorMap A
        (modTensorSwapMod A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          powMulMod A M.X 0 n ≫
          modPowCastMod A M.X
            (by omega : 0 + 1 + n + 1 = n + 2))
        (powMulMod A M'.X n 0) ≫
      modTensorSwap A (modPowMod A M.X (n + 1))
        (modPowMod A M'.X (n + 1)) ≫
      modPowPairing A M M' d (n + 1) =
    tensorμ (modPow A M.X (n + 1)) (modPow A M'.X (n + 1))
        (modPow A M.X (0 + 1)) (modPow A M'.X (0 + 1)) ≫
      (((β_ (modPow A M.X (n + 1)) (modPow A M.X (0 + 1))).hom ≫
          modPowMul A M.X (0 + 1) (n + 1) ≫
          modPowCast A M.X (by omega : 0 + 1 + n + 1 = n + 2)) ⊗ₘ
        modPowMul A M'.X (n + 1) (0 + 1)) ≫
      (β_ (modPow A M.X (n + 2)) (modPow A M'.X (n + 2))).hom ≫
      pairPow A M M' d (n + 2) := by
  rw [tensorHom_π_interchange_map_assoc, modTensorπ_swap_assoc,
    modTensorπ_modPowPairing]
  have hF : modTensorπ A (modPowMod A M.X n)
      (modPowMod A M.X 0) ≫
      (modTensorSwapMod A (modPowMod A M.X n)
          (modPowMod A M.X 0) ≫
        powMulMod A M.X 0 n ≫
        modPowCastMod A M.X
          (by omega : 0 + 1 + n + 1 = n + 2)).hom =
    (β_ (modPow A M.X (n + 1)) (modPow A M.X (0 + 1))).hom ≫
      modPowMul A M.X (0 + 1) (n + 1) ≫
      modPowCast A M.X (by omega : 0 + 1 + n + 1 = n + 2) := by
    change modTensorπ A (modPowMod A M.X n) (modPowMod A M.X 0) ≫
      modTensorSwap A (modPowMod A M.X n) (modPowMod A M.X 0) ≫
      powMulDesc A M.X 0 n ≫
      modPowCast A M.X (by omega : 0 + 1 + n + 1 = n + 2) = _
    rw [modTensorπ_swap_assoc, modTensorπ_powMulDesc_assoc]
    rfl
  have hG : modTensorπ A (modPowMod A M'.X n)
      (modPowMod A M'.X 0) ≫ (powMulMod A M'.X n 0).hom =
    modPowMul A M'.X (n + 1) (0 + 1) := by
    change modTensorπ A (modPowMod A M'.X n)
      (modPowMod A M'.X 0) ≫ powMulDesc A M'.X n 0 = _
    exact modTensorπ_powMulDesc A M'.X n 0
  rw [hF, hG]
  rfl

/-- The generic coherence core of the raw multiplicativity: the
inserted pair peels off and multiplies. -/
private theorem rawMult_core
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A]
    {Y Y' P S : D}
    (p : Y' ⊗ Y ⟶ A) (r : S ⊗ P ⟶ A) :
    (α_ P S ((𝟙_ D ⊗ Y) ⊗ (𝟙_ D ⊗ Y'))).hom ≫
      (P ◁ (α_ S (𝟙_ D ⊗ Y) (𝟙_ D ⊗ Y')).inv) ≫
      (P ◁ ((β_ S (𝟙_ D ⊗ Y)).hom ▷ (𝟙_ D ⊗ Y'))) ≫
      (P ◁ (α_ (𝟙_ D ⊗ Y) S (𝟙_ D ⊗ Y')).hom) ≫
      (α_ P (𝟙_ D ⊗ Y) (S ⊗ (𝟙_ D ⊗ Y'))).inv ≫
      (β_ (P ⊗ (𝟙_ D ⊗ Y)) (S ⊗ (𝟙_ D ⊗ Y'))).hom ≫
      (((α_ S (𝟙_ D) Y').inv ≫
          ((ρ_ S).hom ▷ Y')) ⊗ₘ
        ((β_ P (𝟙_ D ⊗ Y)).hom ≫
          (((λ_ Y).hom ≫ (ρ_ Y).inv) ▷ P) ≫
          (α_ Y (𝟙_ D) P).hom ≫
          (Y ◁ (λ_ P).hom))) ≫
      (α_ S Y' (Y ⊗ P)).hom ≫
      (S ◁ (α_ Y' Y P).inv) ≫
      (S ◁ (p ▷ P)) ≫
      (S ◁ (β_ A P).hom) ≫
      (α_ S P A).inv ≫ (r ▷ A) ≫ μ[A] =
    ((P ⊗ S) ◁ ((β_ (𝟙_ D ⊗ Y) (𝟙_ D ⊗ Y')).hom ≫
        ((λ_ Y').hom ⊗ₘ (λ_ Y).hom) ≫ p)) ≫
      ((β_ P S).hom ≫ r) ▷ A ≫ μ[A] := by
  rw [BraidedCategory.braiding_tensor_left_hom P (𝟙_ D ⊗ Y)
    (S ⊗ (𝟙_ D ⊗ Y'))]
  rw [BraidedCategory.braiding_tensor_right_hom P S
    (𝟙_ D ⊗ Y')]
  rw [BraidedCategory.braiding_tensor_right_hom (𝟙_ D ⊗ Y) S
    (𝟙_ D ⊗ Y')]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc S (p ▷ P)
    ((β_ A P).hom),
    BraidedCategory.braiding_naturality_left p P,
    MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc,
    ← MonoidalCategory.whiskerLeft_comp]
  have hcancel1 : (α_ S (𝟙_ D ⊗ Y) (𝟙_ D ⊗ Y')).inv ≫
      ((β_ S (𝟙_ D ⊗ Y)).hom ▷ (𝟙_ D ⊗ Y')) ≫
      (α_ (𝟙_ D ⊗ Y) S (𝟙_ D ⊗ Y')).hom ≫
      ((α_ (𝟙_ D ⊗ Y) S (𝟙_ D ⊗ Y')).inv ≫
        ((β_ (𝟙_ D ⊗ Y) S).hom ▷ (𝟙_ D ⊗ Y')) ≫
        (α_ S (𝟙_ D ⊗ Y) (𝟙_ D ⊗ Y')).hom ≫
        (S ◁ (β_ (𝟙_ D ⊗ Y) (𝟙_ D ⊗ Y')).hom) ≫
        (α_ S (𝟙_ D ⊗ Y') (𝟙_ D ⊗ Y)).inv) =
    (α_ S (𝟙_ D ⊗ Y) (𝟙_ D ⊗ Y')).inv ≫
      ((β_ S (𝟙_ D ⊗ Y)).hom ≫ (β_ (𝟙_ D ⊗ Y) S).hom) ▷
        (𝟙_ D ⊗ Y') ≫
      (α_ S (𝟙_ D ⊗ Y) (𝟙_ D ⊗ Y')).hom ≫
      (S ◁ (β_ (𝟙_ D ⊗ Y) (𝟙_ D ⊗ Y')).hom) ≫
      (α_ S (𝟙_ D ⊗ Y') (𝟙_ D ⊗ Y)).inv := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc,
      comp_whiskerRight]
  rw [SymmetricCategory.symmetry] at hcancel1
  simp only [MonoidalCategory.id_whiskerRight,
    Category.id_comp, Iso.inv_hom_id_assoc] at hcancel1
  rw [← MonoidalCategory.whiskerLeft_comp_assoc P
      (α_ S (𝟙_ D ⊗ Y) (𝟙_ D ⊗ Y')).inv
      ((β_ S (𝟙_ D ⊗ Y)).hom ▷ (𝟙_ D ⊗ Y')),
    ← MonoidalCategory.whiskerLeft_comp_assoc P _
      (α_ (𝟙_ D ⊗ Y) S (𝟙_ D ⊗ Y')).hom]
  have hb : (((α_ S (𝟙_ D ⊗ Y) (𝟙_ D ⊗ Y')).inv ≫
      (β_ S (𝟙_ D ⊗ Y)).hom ▷ (𝟙_ D ⊗ Y')) ≫
      (α_ (𝟙_ D ⊗ Y) S (𝟙_ D ⊗ Y')).hom) ≫
      ((α_ (𝟙_ D ⊗ Y) S (𝟙_ D ⊗ Y')).inv ≫
        ((β_ (𝟙_ D ⊗ Y) S).hom ▷ (𝟙_ D ⊗ Y')) ≫
        (α_ S (𝟙_ D ⊗ Y) (𝟙_ D ⊗ Y')).hom ≫
        (S ◁ (β_ (𝟙_ D ⊗ Y) (𝟙_ D ⊗ Y')).hom) ≫
        (α_ S (𝟙_ D ⊗ Y') (𝟙_ D ⊗ Y)).inv) =
    (S ◁ (β_ (𝟙_ D ⊗ Y) (𝟙_ D ⊗ Y')).hom) ≫
      (α_ S (𝟙_ D ⊗ Y') (𝟙_ D ⊗ Y)).inv := by
    simp only [Category.assoc]
    exact hcancel1
  rw [← MonoidalCategory.whiskerLeft_comp_assoc P _ _,
    congrArg (fun t => P ◁ t) hb]
  rw [BraidedCategory.braiding_tensor_left_hom Y' Y P]
  have hslot2 : (β_ P (𝟙_ D ⊗ Y)).hom ≫
      (((λ_ Y).hom ≫ (ρ_ Y).inv) ▷ P) ≫
      (α_ Y (𝟙_ D) P).hom ≫ (Y ◁ (λ_ P).hom) =
    (P ◁ (λ_ Y).hom) ≫ (β_ P Y).hom := by
    rw [MonoidalCategory.comp_whiskerRight, Category.assoc,
      show ((ρ_ Y).inv ▷ P) ≫ (α_ Y (𝟙_ D) P).hom ≫
        (Y ◁ (λ_ P).hom) = 𝟙 (Y ⊗ P) from by monoidal,
      Category.comp_id,
      ← BraidedCategory.braiding_naturality_right]
  rw [hslot2]
  conv_lhs => rw [MonoidalCategory.tensorHom_def]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc S
      (α_ Y' Y P).inv (α_ Y' Y P).hom, Iso.inv_hom_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]
  rw [associator_naturality_right_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc S _ _,
    ← MonoidalCategory.whiskerLeft_comp Y' (β_ P Y).hom
      (β_ Y P).hom,
    SymmetricCategory.symmetry, MonoidalCategory.whiskerLeft_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]
  rw [show (α_ S (𝟙_ D) Y').inv ≫ (ρ_ S).hom ▷ Y' =
    S ◁ (λ_ Y').hom from by monoidal]
  rw [← associator_naturality_left_assoc]
  rw [← comp_whiskerRight_assoc]
  have hcancel3 : ((α_ P S (𝟙_ D ⊗ Y')).inv ≫
      ((β_ P S).hom ▷ (𝟙_ D ⊗ Y')) ≫
      (α_ S P (𝟙_ D ⊗ Y')).hom ≫
      (S ◁ (β_ P (𝟙_ D ⊗ Y')).hom) ≫
      (α_ S (𝟙_ D ⊗ Y') P).inv) ≫
      ((S ◁ (λ_ Y').hom) ▷ P) =
    (α_ P S (𝟙_ D ⊗ Y')).inv ≫
      ((P ⊗ S) ◁ (λ_ Y').hom) ≫
      ((β_ P S).hom ▷ Y') ≫
      (α_ S P Y').hom ≫
      (S ◁ (β_ P Y').hom) ≫
      (α_ S Y' P).inv := by
    simp only [Category.assoc]
    rw [← associator_inv_naturality_middle,
      ← MonoidalCategory.whiskerLeft_comp_assoc S
        (β_ P (𝟙_ D ⊗ Y')).hom ((λ_ Y').hom ▷ P),
      ← BraidedCategory.braiding_naturality_right P
        (λ_ Y').hom,
      MonoidalCategory.whiskerLeft_comp]
    simp only [Category.assoc]
    rw [← associator_naturality_right_assoc,
      ← whisker_exchange_assoc]
  rw [congrArg (fun t => t ▷ (𝟙_ D ⊗ Y)) hcancel3]
  simp only [comp_whiskerRight, Category.assoc]
  rw [← associator_naturality_right_assoc,
    whisker_exchange_assoc, whisker_exchange_assoc]
  refine congrArg (CategoryStruct.comp _) ?_
  rw [← associator_naturality_right_assoc]
  rw [← whisker_exchange_assoc, ← whisker_exchange_assoc,
    ← whisker_exchange_assoc, ← whisker_exchange_assoc,
    ← whisker_exchange_assoc]
  have hcancel4 : ((S ◁ (β_ P Y').hom) ▷ Y) ≫
      ((α_ S Y' P).inv ▷ Y) ≫ (α_ (S ⊗ Y') P Y).hom ≫
      (α_ S Y' (P ⊗ Y)).hom ≫ (S ◁ (α_ Y' P Y).inv) ≫
      (S ◁ ((β_ Y' P).hom ▷ Y)) =
    (α_ S (P ⊗ Y') Y).hom := by
    have hmid : ((α_ S Y' P).inv ▷ Y) ≫
        (α_ (S ⊗ Y') P Y).hom ≫ (α_ S Y' (P ⊗ Y)).hom ≫
        (S ◁ (α_ Y' P Y).inv) =
      (α_ S (Y' ⊗ P) Y).hom := by monoidal
    rw [reassoc_of% hmid]
    rw [associator_naturality_middle_assoc,
      ← MonoidalCategory.whiskerLeft_comp,
      ← comp_whiskerRight, SymmetricCategory.symmetry,
      MonoidalCategory.id_whiskerRight,
      MonoidalCategory.whiskerLeft_id, Category.comp_id]
  rw [reassoc_of% hcancel4]
  rw [whisker_exchange_assoc, whisker_exchange_assoc]
  monoidal

/-- The raw multiplicativity of the nested pairing at an aligned
insertion: the peel of the joined pairing extracts the inserted
block. -/
private theorem powDeltaCore_raw
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    tensorμ (tensorPow D M.X (n + 1)) (tensorPow D M'.X (n + 1))
        (tensorPow D M.X (0 + 1)) (tensorPow D M'.X (0 + 1)) ≫
      (((β_ (tensorPow D M.X (n + 1))
            (tensorPow D M.X (0 + 1))).hom ≫
          (tensorPowConcat M.X (0 + 1) (n + 1)).hom ≫
          powCast M.X
            (by omega : 0 + 1 + (n + 1) = n + 1 + 1)) ⊗ₘ
        (tensorPowConcat M'.X (n + 1) (0 + 1)).hom) ≫
      (β_ (tensorPow D M.X (n + 1 + 1))
        (tensorPow D M'.X (n + 1 + 1))).hom ≫
      rawPair A M M' d (n + 1 + 1) =
    (((β_ (tensorPow D M.X (n + 1))
          (tensorPow D M'.X (n + 1))).hom ≫
        rawPair A M M' d (n + 1)) ⊗ₘ
      ((β_ (tensorPow D M.X (0 + 1))
          (tensorPow D M'.X (0 + 1))).hom ≫
        rawPair A M M' d (0 + 1))) ≫ μ[A] := by
  rw [rawPair_succ]
  have hslide : (((β_ (tensorPow D M.X (n + 1))
        (tensorPow D M.X (0 + 1))).hom ≫
      (tensorPowConcat M.X (0 + 1) (n + 1)).hom ≫
      powCast M.X (by omega : 0 + 1 + (n + 1) = n + 1 + 1)) ⊗ₘ
      (tensorPowConcat M'.X (n + 1) (0 + 1)).hom) ≫
      (β_ (tensorPow D M.X (n + 1 + 1))
        (tensorPow D M'.X (n + 1 + 1))).hom =
    (β_ (tensorPow D M.X (n + 1) ⊗ tensorPow D M.X (0 + 1))
        (tensorPow D M'.X (n + 1) ⊗
          tensorPow D M'.X (0 + 1))).hom ≫
      ((tensorPowConcat M'.X (n + 1) (0 + 1)).hom ⊗ₘ
        ((β_ (tensorPow D M.X (n + 1))
            (tensorPow D M.X (0 + 1))).hom ≫
          (tensorPowConcat M.X (0 + 1) (n + 1)).hom ≫
          powCast M.X
            (by omega : 0 + 1 + (n + 1) = n + 1 + 1))) :=
    BraidedCategory.braiding_naturality _ _
  rw [reassoc_of% hslide]
  have hpeelcast : ∀ {a b : ℕ} (h : a = b)
      (hs : a + 1 = b + 1),
      powCast M.X hs ≫ (powPeel M.X b).hom =
        (powPeel M.X a).hom ≫ (M.X ◁ powCast M.X h) := by
    intro a b h hs
    subst h
    rw [powCast_irrel M.X hs rfl, powCast_rfl,
      Category.id_comp, powCast_rfl,
      MonoidalCategory.whiskerLeft_id, Category.comp_id]
  have hMword : ((β_ (tensorPow D M.X (n + 1))
        (tensorPow D M.X (0 + 1))).hom ≫
      (tensorPowConcat M.X (0 + 1) (n + 1)).hom ≫
      powCast M.X (by omega : 0 + 1 + (n + 1) = n + 1 + 1)) ≫
      (powPeel M.X (n + 1)).hom =
    (β_ (tensorPow D M.X (n + 1))
        (tensorPow D M.X (0 + 1))).hom ≫
      (((λ_ M.X).hom ≫ (ρ_ M.X).inv) ▷
        tensorPow D M.X (n + 1)) ≫
      (α_ M.X (tensorPow D M.X 0)
        (tensorPow D M.X (n + 1))).hom ≫
      (M.X ◁ (λ_ (tensorPow D M.X (n + 1))).hom) := by
    rw [show powCast M.X
        (by omega : 0 + 1 + (n + 1) = n + 1 + 1) =
      powCast M.X (by omega : 0 + 1 + (n + 1) = 0 + (n + 1) + 1)
        ≫ powCast M.X (by omega : 0 + (n + 1) + 1 = n + 1 + 1)
      from (powCast_comp M.X _ _).symm]
    simp only [Category.assoc]
    rw [hpeelcast (by omega : 0 + (n + 1) = n + 1),
      reassoc_of% (concat_peel_head M.X 0 (n + 1)),
      powPeel_zero, tensorPowConcat_zero_left]
    repeat' erw [← MonoidalCategory.whiskerLeft_comp]
    have hslot : ((λ_ (tensorPow D M.X (n + 1))).hom ≫
        powCast M.X (by omega : n + 1 = 0 + (n + 1))) ≫
        powCast M.X (by omega : 0 + (n + 1) = n + 1) =
      (λ_ (tensorPow D M.X (n + 1))).hom := by
      rw [Category.assoc, powCast_comp,
        powCast_irrel M.X _ rfl, powCast_rfl, Category.comp_id]
    exact congrArg (fun t =>
      (β_ (tensorPow D M.X (n + 1))
          (tensorPow D M.X (0 + 1))).hom ≫
        (λ_ M.X ≪≫ (ρ_ M.X).symm).hom ▷
          tensorPow D M.X (n + 1) ≫
        (α_ M.X (tensorPow D M.X 0)
          (tensorPow D M.X (n + 1))).hom ≫
        (M.X ◁ t)) hslot
  have hmr : ∀ {X₁ X₂ Y₂ Z₁ : D} (a : X₁ ⟶ Z₁) (b : X₂ ⟶ Y₂)
      (f : Y₂ ⟶ M.X ⊗ tensorPow D M.X (n + 1))
      {Z : D} (h : Z₁ ⊗ (M.X ⊗ tensorPow D M.X (n + 1)) ⟶ Z),
      (a ⊗ₘ b) ≫ (Z₁ ◁ (f : Y₂ ⟶ _)) ≫ h =
        (a ⊗ₘ (b ≫ f)) ≫ h := by
    intro X₁ X₂ Y₂ Z₁ a b f Z h
    rw [← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      Category.comp_id]
  rw [hmr]
  rw [congrArg (fun t =>
    (tensorPowConcat M'.X (n + 1) (0 + 1)).hom ⊗ₘ t) hMword]
  have hraw1 : rawPair A M M' d (0 + 1) =
      ((λ_ M'.X).hom ⊗ₘ (λ_ M.X).hom) ≫ pairRaw A M M' d := by
    rw [rawPair_succ, rawPair_zero, powPeel_zero]
    change ((𝟙_ D ⊗ M'.X) ◁ (λ_ M.X ≪≫ (ρ_ M.X).symm).hom) ≫
        (α_ (𝟙_ D) M'.X (M.X ⊗ 𝟙_ D)).hom ≫
        (𝟙_ D ◁ (α_ M'.X M.X (𝟙_ D)).inv) ≫
        (𝟙_ D ◁ (pairRaw A M M' d ▷ 𝟙_ D)) ≫
        (𝟙_ D ◁ (β_ A (𝟙_ D)).hom) ≫
        (α_ (𝟙_ D) (𝟙_ D) A).inv ≫
        (((λ_ (𝟙_ D)).hom ≫ η[A]) ▷ A) ≫ μ[A] = _
    rw [Iso.trans_hom, braiding_tensorUnit_right,
      comp_whiskerRight]
    simp only [Category.assoc]
    rw [MonObj.one_mul]
    dsimp only [Iso.symm_hom]
    monoidal
  rw [hraw1]
  rw [show (tensorPowConcat M'.X (n + 1) (0 + 1)).hom =
    (α_ (tensorPow D M'.X (n + 1)) (tensorPow D M'.X 0)
        M'.X).inv ≫
      ((ρ_ (tensorPow D M'.X (n + 1))).hom ▷ M'.X) from rfl]
  conv_rhs => rw [MonoidalCategory.tensorHom_def']
  simp only [tensorμ, Category.assoc]
  exact rawMult_core A (pairRaw A M M' d)
    (rawPair A M M' d (n + 1))

/-- The transition core at the raw power level: the peel of the
joined pairing extracts the inserted pair. -/
private theorem powDeltaCore_layer2
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    tensorμ (modPow A M.X (n + 1)) (modPow A M'.X (n + 1))
        (modPow A M.X (0 + 1)) (modPow A M'.X (0 + 1)) ≫
      (((β_ (modPow A M.X (n + 1)) (modPow A M.X (0 + 1))).hom ≫
          modPowMul A M.X (0 + 1) (n + 1) ≫
          modPowCast A M.X (by omega : 0 + 1 + n + 1 = n + 2)) ⊗ₘ
        modPowMul A M'.X (n + 1) (0 + 1)) ≫
      (β_ (modPow A M.X (n + 2)) (modPow A M'.X (n + 2))).hom ≫
      pairPow A M M' d (n + 2) =
    (((β_ (modPow A M.X (n + 1)) (modPow A M'.X (n + 1))).hom ≫
        pairPow A M M' d (n + 1)) ⊗ₘ
      ((β_ (modPow A M.X (0 + 1)) (modPow A M'.X (0 + 1))).hom ≫
        pairPow A M M' d (0 + 1))) ≫ μ[A] := by
  rw [← cancel_epi
    ((modPowπ A M.X (n + 1) ⊗ₘ modPowπ A M'.X (n + 1)) ⊗ₘ
      (modPowπ A M.X (0 + 1) ⊗ₘ modPowπ A M'.X (0 + 1)))]
  rw [reassoc_of% (tensorμ_natural (modPowπ A M.X (n + 1))
    (modPowπ A M'.X (n + 1)) (modPowπ A M.X (0 + 1))
    (modPowπ A M'.X (0 + 1)))]
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  have hS1 : (modPowπ A M.X (n + 1) ⊗ₘ
      modPowπ A M.X (0 + 1)) ≫
      ((β_ (modPow A M.X (n + 1)) (modPow A M.X (0 + 1))).hom ≫
        modPowMul A M.X (0 + 1) (n + 1) ≫
        modPowCast A M.X (by omega : 0 + 1 + n + 1 = n + 2)) =
    (β_ (tensorPow D M.X (n + 1))
        (tensorPow D M.X (0 + 1))).hom ≫
      (tensorPowConcat M.X (0 + 1) (n + 1)).hom ≫
      powCast M.X (by omega : 0 + 1 + (n + 1) = n + 2) ≫
      modPowπ A M.X (n + 2) := by
    rw [BraidedCategory.braiding_naturality_assoc,
      reassoc_of% (modPowπ_tensor_modPowMul A M.X (0 + 1)
        (n + 1)),
      modPowπ_cast]
  have hS2 : (modPowπ A M'.X (n + 1) ⊗ₘ
      modPowπ A M'.X (0 + 1)) ≫
      modPowMul A M'.X (n + 1) (0 + 1) =
    (tensorPowConcat M'.X (n + 1) (0 + 1)).hom ≫
      modPowπ A M'.X (n + 1 + (0 + 1)) :=
    modPowπ_tensor_modPowMul A M'.X (n + 1) (0 + 1)
  rw [hS1, hS2]
  have hR1 : (modPowπ A M.X (n + 1) ⊗ₘ
      modPowπ A M'.X (n + 1)) ≫
      (β_ (modPow A M.X (n + 1)) (modPow A M'.X (n + 1))).hom ≫
      pairPow A M M' d (n + 1) =
    (β_ (tensorPow D M.X (n + 1))
        (tensorPow D M'.X (n + 1))).hom ≫
      rawPair A M M' d (n + 1) := by
    rw [BraidedCategory.braiding_naturality_assoc,
      modPowπ_tensor_pairPow]
  have hR2 : (modPowπ A M.X (0 + 1) ⊗ₘ
      modPowπ A M'.X (0 + 1)) ≫
      (β_ (modPow A M.X (0 + 1)) (modPow A M'.X (0 + 1))).hom ≫
      pairPow A M M' d (0 + 1) =
    (β_ (tensorPow D M.X (0 + 1))
        (tensorPow D M'.X (0 + 1))).hom ≫
      rawPair A M M' d (0 + 1) := by
    rw [BraidedCategory.braiding_naturality_assoc,
      modPowπ_tensor_pairPow]
  rw [hR1, hR2]
  have hsplit : ((β_ (tensorPow D M.X (n + 1))
        (tensorPow D M.X (0 + 1))).hom ≫
      (tensorPowConcat M.X (0 + 1) (n + 1)).hom ≫
      powCast M.X (by omega : 0 + 1 + (n + 1) = n + 2) ≫
      modPowπ A M.X (n + 2)) ⊗ₘ
    ((tensorPowConcat M'.X (n + 1) (0 + 1)).hom ≫
      modPowπ A M'.X (n + 1 + (0 + 1))) =
    (((β_ (tensorPow D M.X (n + 1))
          (tensorPow D M.X (0 + 1))).hom ≫
        (tensorPowConcat M.X (0 + 1) (n + 1)).hom ≫
        powCast M.X (by omega : 0 + 1 + (n + 1) = n + 2)) ⊗ₘ
      (tensorPowConcat M'.X (n + 1) (0 + 1)).hom) ≫
    (modPowπ A M.X (n + 2) ⊗ₘ
      modPowπ A M'.X (n + 1 + (0 + 1))) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.assoc]
  rw [hsplit]
  have hβfinal : (modPowπ A M.X (n + 2) ⊗ₘ
      modPowπ A M'.X (n + 1 + (0 + 1))) ≫
      (β_ (modPow A M.X (n + 2)) (modPow A M'.X (n + 2))).hom ≫
      pairPow A M M' d (n + 2) =
    (β_ (tensorPow D M.X (n + 2))
        (tensorPow D M'.X (n + 2))).hom ≫
      rawPair A M M' d (n + 2) := by
    change (modPowπ A M.X (n + 2) ⊗ₘ modPowπ A M'.X (n + 2)) ≫
      (β_ (modPow A M.X (n + 2)) (modPow A M'.X (n + 2))).hom ≫
      pairPow A M M' d (n + 2) = _
    rw [BraidedCategory.braiding_naturality_assoc,
      modPowπ_tensor_pairPow]
  rw [Category.assoc
    (((β_ (tensorPow D M.X (n + 1))
        (tensorPow D M.X (0 + 1))).hom ≫
      (tensorPowConcat M.X (0 + 1) (n + 1)).hom ≫
      powCast M.X (by omega : 0 + 1 + (n + 1) = n + 2)) ⊗ₘ
      (tensorPowConcat M'.X (n + 1) (0 + 1)).hom)
    (modPowπ A M.X (n + 2) ⊗ₘ
      modPowπ A M'.X (n + 1 + (0 + 1)))]
  rw [hβfinal]
  exact powDeltaCore_raw A M M' d n

/-- **Multiplicativity of the pairing against the transition
core**: the interchange followed by the aligned multiplications
and the pairing of the joined stage evaluates as the product of
the stage pairings. -/
theorem powDeltaCore_pairing
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    interchange A (modPowMod A M.X n) (modPowMod A M'.X n)
        (modPowMod A M.X 0) (modPowMod A M'.X 0) ≫
      modTensorMap A
        (modTensorSwapMod A (modPowMod A M.X n)
            (modPowMod A M.X 0) ≫
          powMulMod A M.X 0 n ≫
          modPowCastMod A M.X (by omega : 0 + 1 + n + 1 = n + 2))
        (powMulMod A M'.X n 0) ≫
      modTensorSwap A (modPowMod A M.X (n + 1))
        (modPowMod A M'.X (n + 1)) ≫
      modPowPairing A M M' d (n + 1) =
    ((modTensorSwap A (modPowMod A M.X n) (modPowMod A M'.X n) ≫
        modPowPairing A M M' d n) ⊗ₘ
      (modTensorSwap A (modPowMod A M.X 0)
          (modPowMod A M'.X 0) ≫
        modPowPairing A M M' d 0)) ≫ μ[A] := by
  rw [← cancel_epi
    (modTensorπ A (modPowMod A M.X n) (modPowMod A M'.X n) ⊗ₘ
      modTensorπ A (modPowMod A M.X 0) (modPowMod A M'.X 0))]
  refine (powDeltaCore_layer1 A M M' d n).trans
    ((powDeltaCore_layer2 A M M' d n).trans ?_)
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  have h1 : modTensorπ A (modPowMod A M.X n)
      (modPowMod A M'.X n) ≫
      modTensorSwap A (modPowMod A M.X n) (modPowMod A M'.X n) ≫
      modPowPairing A M M' d n =
    (β_ (modPow A M.X (n + 1)) (modPow A M'.X (n + 1))).hom ≫
      pairPow A M M' d (n + 1) := by
    rw [modTensorπ_swap_assoc, modTensorπ_modPowPairing]
    rfl
  have h0 : modTensorπ A (modPowMod A M.X 0)
      (modPowMod A M'.X 0) ≫
      modTensorSwap A (modPowMod A M.X 0) (modPowMod A M'.X 0) ≫
      modPowPairing A M M' d 0 =
    (β_ (modPow A M.X (0 + 1)) (modPow A M'.X (0 + 1))).hom ≫
      pairPow A M M' d (0 + 1) := by
    rw [modTensorπ_swap_assoc, modTensorπ_modPowPairing]
    rfl
  rw [h1, h0]
  rfl

/-- **The transition retracts against the pairing**: under the
scalar zigzag, one insertion peels off against one zigzag. -/
theorem powDelta_pairing
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (hzig : d.copair ≫ modTensorSwap A M M' ≫ d.pair = 𝟙 A)
    (n : ℕ) :
    powDelta A M M' d n ≫
        modTensorSwap A (modPowMod A M.X (n + 1))
          (modPowMod A M'.X (n + 1)) ≫
        modPowPairing A M M' d (n + 1) =
      modTensorSwap A (modPowMod A M.X n)
          (modPowMod A M'.X n) ≫
        modPowPairing A M M' d n := by
  have hflat : powDelta A M M' d n ≫
      modTensorSwap A (modPowMod A M.X (n + 1))
        (modPowMod A M'.X (n + 1)) ≫
      modPowPairing A M M' d (n + 1) =
    (ρ_ (powStage A M M' n)).inv ≫
      (powStage A M M' n ◁ powSeed A M M' d) ≫
      (interchange A (modPowMod A M.X n) (modPowMod A M'.X n)
          (modPowMod A M.X 0) (modPowMod A M'.X 0) ≫
        modTensorMap A
          (modTensorSwapMod A (modPowMod A M.X n)
              (modPowMod A M.X 0) ≫
            powMulMod A M.X 0 n ≫
            modPowCastMod A M.X
              (by omega : 0 + 1 + n + 1 = n + 2))
          (powMulMod A M'.X n 0) ≫
        modTensorSwap A (modPowMod A M.X (n + 1))
          (modPowMod A M'.X (n + 1)) ≫
        modPowPairing A M M' d (n + 1)) := by
    rw [powDelta]
    repeat' erw [Category.assoc]
  refine hflat.trans ?_
  refine ((congrArg (fun t =>
    (ρ_ (powStage A M M' n)).inv ≫
    (powStage A M M' n ◁ powSeed A M M' d) ≫ t)
    (powDeltaCore_pairing A M M' d n)).trans ?_)
  have hseed' : (powStage A M M' n ◁ powSeed A M M' d) ≫
      ((modTensorSwap A (modPowMod A M.X n)
          (modPowMod A M'.X n) ≫ modPowPairing A M M' d n) ⊗ₘ
        (modTensorSwap A (modPowMod A M.X 0)
          (modPowMod A M'.X 0) ≫ modPowPairing A M M' d 0)) ≫
      μ[A] =
    ((modTensorSwap A (modPowMod A M.X n)
        (modPowMod A M'.X n) ≫ modPowPairing A M M' d n) ⊗ₘ
      η[A]) ≫ μ[A] := by
    rw [← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      Category.id_comp, powSeed_pairing A M M' d hzig]
    rfl
  refine ((congrArg (fun t =>
    (ρ_ (powStage A M M' n)).inv ≫ t) hseed').trans ?_)
  rw [MonoidalCategory.tensorHom_def]
  simp only [Category.assoc]
  rw [MonObj.mul_one]
  rw [rightUnitor_naturality]
  exact Iso.inv_hom_id_assoc (ρ_ (powStage A M M' n)) _

/-- **The chain units retract against the pairing**: every
copairing power evaluates to the unit of the base. -/
theorem powUnitStage_pairing
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (hzig : d.copair ≫ modTensorSwap A M M' ≫ d.pair = 𝟙 A) :
    ∀ n : ℕ, powUnitStage A M M' d n ≫
        modTensorSwap A (modPowMod A M.X n)
          (modPowMod A M'.X n) ≫
        modPowPairing A M M' d n = η[A]
  | 0 => powSeed_pairing A M M' d hzig
  | (n + 1) => by
    change (powUnitStage A M M' d n ≫ powDelta A M M' d n) ≫ _ = _
    rw [Category.assoc, powDelta_pairing A M M' d hzig n]
    exact powUnitStage_pairing A M M' d hzig n

/-- **Scalar extraction at the head of the `M'`-power**: the tail
action on the `M'`-power extracts as the scalar multiplying the
pairing from the left. -/
theorem rawPair_actHead
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') (n : ℕ) :
    (powTailAct A M'.X n ▷ tensorPow D M.X (n + 1)) ≫
        rawPair A M M' d (n + 1) =
      (α_ A (tensorPow D M'.X (n + 1))
          (tensorPow D M.X (n + 1))).hom ≫
        (A ◁ rawPair A M M' d (n + 1)) ≫ μ[A] := by
  have hsplit : powTailAct A M'.X n ▷
      tensorPow D M.X (n + 1) =
    ((α_ A (tensorPow D M'.X n) M'.X).inv ▷
      tensorPow D M.X (n + 1)) ≫
    (((β_ A (tensorPow D M'.X n)).hom ▷ M'.X) ▷
      tensorPow D M.X (n + 1)) ≫
    ((α_ (tensorPow D M'.X n) A M'.X).hom ▷
      tensorPow D M.X (n + 1)) ≫
    ((tensorPow D M'.X n ◁ (β_ M'.X A).inv) ▷
      tensorPow D M.X (n + 1)) ≫
    ((tensorPow D M'.X n ◁ actRight A M'.X) ▷
      tensorPow D M.X (n + 1)) := by
    rw [show powTailAct A M'.X n =
      (α_ A (tensorPow D M'.X n) M'.X).inv ≫
        ((β_ A (tensorPow D M'.X n)).hom ▷ M'.X) ≫
        (α_ (tensorPow D M'.X n) A M'.X).hom ≫
        (tensorPow D M'.X n ◁ actLeft A M'.X) from rfl,
      show actLeft A M'.X = (β_ M'.X A).inv ≫
        actRight A M'.X from by
        rw [actRight, Iso.inv_hom_id_assoc]]
    conv_rhs => rw [← comp_whiskerRight, ← comp_whiskerRight,
      ← comp_whiskerRight, ← comp_whiskerRight]
    refine congrArg (· ▷ tensorPow D M.X (n + 1)) ?_
    simp only [MonoidalCategory.whiskerLeft_comp]
    rfl
  have hsplit2 : (powTailAct A M'.X n ▷
      tensorPow D M.X (n + 1)) ≫ rawPair A M M' d (n + 1) =
    ((α_ A (tensorPow D M'.X n) M'.X).inv ▷
      tensorPow D M.X (n + 1)) ≫
    (((β_ A (tensorPow D M'.X n)).hom ▷ M'.X) ▷
      tensorPow D M.X (n + 1)) ≫
    ((α_ (tensorPow D M'.X n) A M'.X).hom ▷
      tensorPow D M.X (n + 1)) ≫
    ((tensorPow D M'.X n ◁ (β_ M'.X A).inv) ▷
      tensorPow D M.X (n + 1)) ≫
    ((tensorPow D M'.X n ◁ actRight A M'.X) ▷
      tensorPow D M.X (n + 1)) ≫ rawPair A M M' d (n + 1) := by
    rw [hsplit]
    exact (Category.assoc _ _ _).trans
      (congrArg (CategoryStruct.comp _)
        ((Category.assoc _ _ _).trans
          (congrArg (CategoryStruct.comp _)
            ((Category.assoc _ _ _).trans
              (congrArg (CategoryStruct.comp _)
                (Category.assoc _ _ _))))))
  rw [hsplit2, rawPair_actRight_last A M M' d n]
  rw [show (β_ M'.X A).inv = (β_ A M'.X).hom from by
    rw [← cancel_epi (β_ M'.X A).hom, Iso.hom_inv_id,
      SymmetricCategory.symmetry]]
  conv_rhs => rw [← IsCommMonObj.mul_comm A,
    BraidedCategory.braiding_naturality_right_assoc,
    BraidedCategory.braiding_tensor_right_hom A
      (tensorPow D M'.X (n + 1))
      (tensorPow D M.X (n + 1))]
  have hβexp : (β_ A (tensorPow D M'.X (n + 1))).hom =
      (α_ A (tensorPow D M'.X n) M'.X).inv ≫
        ((β_ A (tensorPow D M'.X n)).hom ▷ M'.X) ≫
        (α_ (tensorPow D M'.X n) A M'.X).hom ≫
        (tensorPow D M'.X n ◁ (β_ A M'.X).hom) ≫
        (α_ (tensorPow D M'.X n) M'.X A).inv :=
    BraidedCategory.braiding_tensor_right_hom A
      (tensorPow D M'.X n) M'.X
  conv_rhs => rw [hβexp]
  monoidal

/-- The head action extracts through the descended pairing. -/
theorem pairPow_actHead
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') (n : ℕ) :
    (modPowAct A M'.X n ▷ modPow A M.X (n + 1)) ≫
        pairPow A M M' d (n + 1) =
      (α_ A (modPow A M'.X (n + 1))
          (modPow A M.X (n + 1))).hom ≫
        (A ◁ pairPow A M M' d (n + 1)) ≫ μ[A] := by
  refine (cancel_epi ((A ⊗ modPow A M'.X (n + 1)) ◁
    modPowπ A M.X (n + 1))).mp ?_
  refine (cancel_epi ((A ◁ modPowπ A M'.X (n + 1)) ▷
    tensorPow D M.X (n + 1))).mp ?_
  have hL1 : ((A ⊗ modPow A M'.X (n + 1)) ◁
      modPowπ A M.X (n + 1)) ≫
      (modPowAct A M'.X n ▷ modPow A M.X (n + 1)) =
    (modPowAct A M'.X n ▷ tensorPow D M.X (n + 1)) ≫
      (modPow A M'.X (n + 1) ◁ modPowπ A M.X (n + 1)) :=
    whisker_exchange _ _
  have hL2 : ((A ◁ modPowπ A M'.X (n + 1)) ▷
      tensorPow D M.X (n + 1)) ≫
      (modPowAct A M'.X n ▷ tensorPow D M.X (n + 1)) =
    (powTailAct A M'.X n ▷ tensorPow D M.X (n + 1)) ≫
      (modPowπ A M'.X (n + 1) ▷ tensorPow D M.X (n + 1)) := by
    rw [← comp_whiskerRight, whiskerLeft_modPowπ_modPowAct,
      comp_whiskerRight]
  have hL3 : (modPowπ A M'.X (n + 1) ▷
      tensorPow D M.X (n + 1)) ≫
      (modPow A M'.X (n + 1) ◁ modPowπ A M.X (n + 1)) ≫
      pairPow A M M' d (n + 1) =
    rawPair A M M' d (n + 1) := by
    rw [← MonoidalCategory.tensorHom_def_assoc,
      modPowπ_tensor_pairPow]
  conv_lhs => rw [reassoc_of% hL1, reassoc_of% hL2, hL3,
    rawPair_actHead A M M' d n]
  have hR1 : ((A ◁ modPowπ A M'.X (n + 1)) ▷
      tensorPow D M.X (n + 1)) ≫
      ((A ⊗ modPow A M'.X (n + 1)) ◁ modPowπ A M.X (n + 1)) ≫
      (α_ A (modPow A M'.X (n + 1))
        (modPow A M.X (n + 1))).hom =
    (α_ A (tensorPow D M'.X (n + 1))
        (tensorPow D M.X (n + 1))).hom ≫
      (A ◁ (modPowπ A M'.X (n + 1) ⊗ₘ
        modPowπ A M.X (n + 1))) := by
    rw [← MonoidalCategory.tensorHom_def_assoc]
    have hnat := associator_naturality (𝟙 A)
      (modPowπ A M'.X (n + 1)) (modPowπ A M.X (n + 1))
    simp only [MonoidalCategory.id_tensorHom] at hnat
    exact hnat
  conv_rhs => rw [reassoc_of% hR1,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    modPowπ_tensor_pairPow]

/-- **The power pairing is linear**: it is a map of modules into
the regular module. -/
theorem modPowPairing_linear
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (n : ℕ) :
    haveI := modTensorModObj A (modPowMod A M'.X n)
      (modPowMod A M.X n)
    actLeft A (modTensor A (modPowMod A M'.X n)
        (modPowMod A M.X n)) ≫ modPowPairing A M M' d n =
      (A ◁ modPowPairing A M M' d n) ≫ μ[A] := by
  let := modTensorModObj A (modPowMod A M'.X n)
    (modPowMod A M.X n)
  apply modTensor_whisker_hom_ext A (modPowMod A M'.X n)
    (modPowMod A M.X n) A
  conv_lhs => rw [show actLeft A (modTensor A
      (modPowMod A M'.X n) (modPowMod A M.X n)) =
    modTensorAct A (modPowMod A M'.X n) (modPowMod A M.X n)
    from rfl]
  conv_lhs => rw [whiskerLeft_modTensorπ_act_assoc,
    modTensorπ_modPowPairing]
  conv_rhs => rw [← MonoidalCategory.whiskerLeft_comp_assoc,
    modTensorπ_modPowPairing]
  change (α_ A (modPow A M'.X (n + 1))
      (modPow A M.X (n + 1))).inv ≫
    (modPowAct A M'.X n ▷ modPow A M.X (n + 1)) ≫
    pairPow A M M' d (n + 1) =
    (A ◁ pairPow A M M' d (n + 1)) ≫ μ[A]
  rw [pairPow_actHead A M M' d n, Iso.inv_hom_id_assoc]

end RS
