/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SymMul
import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainAlgebra

/-!
# The local splitting chain

The algebra of Deligne's 2.10: for a point of an object, the chain
of plain symmetric powers with transitions multiplication by the
point.  The colimit is the quotient of the symmetric algebra
identifying the point with the unit; the stages, the seed, the
stage multiplication, and the stage units are pinned here, and the
laws assemble the colimit into a commutative algebra through the
generic chain kit.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- The stages of the local splitting chain: the plain symmetric
powers, one letter up. -/
noncomputable def splitStage
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] [Linear ℂ D]
    (Y : D)
    (n : ℕ) : D :=
  symPow (𝟙_ D) Y (n + 1)

/-- The seed of the local splitting chain: the point, in the
singleton power. -/
noncomputable def splitSeed
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] [Linear ℂ D]
    (Y : D) (pt : 𝟙_ D ⟶ Y) : 𝟙_ D ⟶ splitStage Y 0 :=
  pt ≫ (symPowOne (𝟙_ D) Y).inv

/-- The transition of the local splitting chain: multiplication
by the seed. -/
noncomputable def splitDelta
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Y : D) (pt : 𝟙_ D ⟶ Y)
    (n : ℕ) :
    splitStage Y n ⟶ splitStage Y (n + 1) :=
  (ρ_ (splitStage Y n)).inv ≫
    (splitStage Y n ◁ splitSeed Y pt) ≫
    symMul (𝟙_ D) Y (n + 1) 1

/-- The stage multiplication of the local splitting chain. -/
noncomputable def splitMu
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Y : D)
    (i j : ℕ) :
    splitStage Y i ⊗ splitStage Y j ⟶ splitStage Y (i + 1 + j) :=
  symMul (𝟙_ D) Y (i + 1) (j + 1) ≫
    symPowCast (𝟙_ D) Y
      (by omega : i + 1 + (j + 1) = i + 1 + j + 1)

/-- The stage units of the local splitting chain: the powers of
the point. -/
noncomputable def splitUnitStage
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Y : D) (pt : 𝟙_ D ⟶ Y) :
    (n : ℕ) → (𝟙_ D ⟶ splitStage Y n)
  | 0 => splitSeed Y pt
  | (n + 1) => splitUnitStage Y pt n ≫ splitDelta Y pt n

/-- The stage units ride along the transitions. -/
theorem splitUnitStage_succ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Y : D) (pt : 𝟙_ D ⟶ Y)
    (n : ℕ) :
    splitUnitStage Y pt n ≫ splitDelta Y pt n =
      splitUnitStage Y pt (n + 1) :=
  rfl

/-! ## Stage laws

The transitions, the stage multiplication and the seed satisfy the
five stagewise laws consumed by the chain kit, derived from the
symmetric-multiplication laws one letter up.  The arity transports
over definitionally equal indices collapse to identities. -/

/-- Arity transports of the symmetric powers compose. -/
private theorem splitPowCast_comp
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasFiniteBiproducts D] [HasCoequalizers D] [Linear ℂ D]
    (Y : D)
    {a b c : ℕ} (h : a = b)
    (h' : b = c) :
    symPowCast (𝟙_ D) Y h ≫ symPowCast (𝟙_ D) Y h' =
      symPowCast (𝟙_ D) Y (h.trans h') := by
  subst h h'
  rw [symPowCast_rfl, Category.id_comp]

/-- Commutativity of the symmetric multiplication, with both sides
transported to a common arity. -/
private theorem splitSymMul_comm_cast
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Y : D)
    {a b c : ℕ} (h : b + a = c)
    (h' : a + b = c) :
    (β_ (symPow (𝟙_ D) Y a) (symPow (𝟙_ D) Y b)).hom ≫
        symMul (𝟙_ D) Y b a ≫ symPowCast (𝟙_ D) Y h =
      symMul (𝟙_ D) Y a b ≫ symPowCast (𝟙_ D) Y h' := by
  subst h
  rw [symPowCast_rfl, Category.comp_id]
  exact symMul_comm (𝟙_ D) Y a b

/-- The right seed law at the symmetric-power level, spelt
uniformly in the powers with the seed abstracted. -/
private theorem symMul_seed_right
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Y : D)
    (s : 𝟙_ D ⟶ symPow (𝟙_ D) Y 1)
    (a b c : ℕ) (hc : a + b = c) (h₁ : a + (b + 1) = c + 1) :
    (symPow (𝟙_ D) Y a ◁
        ((ρ_ (symPow (𝟙_ D) Y b)).inv ≫
          (symPow (𝟙_ D) Y b ◁ s) ≫ symMul (𝟙_ D) Y b 1)) ≫
        symMul (𝟙_ D) Y a (b + 1) ≫ symPowCast (𝟙_ D) Y h₁ =
      (symMul (𝟙_ D) Y a b ≫ symPowCast (𝟙_ D) Y hc) ≫
        (ρ_ (symPow (𝟙_ D) Y c)).inv ≫
        (symPow (𝟙_ D) Y c ◁ s) ≫ symMul (𝟙_ D) Y c 1 := by
  subst hc
  have hk₁ : symPowCast (𝟙_ D) Y h₁ = 𝟙 _ := rfl
  rw [hk₁, Category.comp_id, symPowCast_rfl, Category.comp_id]
  have hassoc := symMul_assoc (𝟙_ D) Y a b 1
  have hk₂ : symPowCast (𝟙_ D) Y
      (by omega : a + (b + 1) = a + b + 1) = 𝟙 _ := rfl
  rw [hk₂, Category.comp_id] at hassoc
  have h2 : (symPow (𝟙_ D) Y a ◁ symMul (𝟙_ D) Y b 1) ≫
      symMul (𝟙_ D) Y a (b + 1) =
      (α_ (symPow (𝟙_ D) Y a) (symPow (𝟙_ D) Y b)
          (symPow (𝟙_ D) Y 1)).inv ≫
        (symMul (𝟙_ D) Y a b ▷ symPow (𝟙_ D) Y 1) ≫
        symMul (𝟙_ D) Y (a + b) 1 := by
    rw [Iso.eq_inv_comp]
    exact hassoc.symm
  have hcoh : (symPow (𝟙_ D) Y a ◁
      (ρ_ (symPow (𝟙_ D) Y b)).inv) ≫
      (α_ (symPow (𝟙_ D) Y a) (symPow (𝟙_ D) Y b) (𝟙_ D)).inv =
      (ρ_ (symPow (𝟙_ D) Y a ⊗ symPow (𝟙_ D) Y b)).inv := by
    monoidal
  rw [MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    Category.assoc, h2,
    MonoidalCategory.associator_inv_naturality_right_assoc,
    reassoc_of% hcoh, whisker_exchange_assoc]
  rw [reassoc_of% (MonoidalCategory.rightUnitor_inv_naturality
    (symMul (𝟙_ D) Y a b)).symm]

/-- **Right transition law**: transitioning the second factor and
multiplying is multiplying and transitioning, since the transition
is right multiplication by the seed. -/
theorem splitDelta_mu_right
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Y : D) (pt : 𝟙_ D ⟶ Y)
    (i j : ℕ) :
    (splitStage Y i ◁ splitDelta Y pt j) ≫ splitMu Y i (j + 1) =
      splitMu Y i j ≫ splitDelta Y pt (i + 1 + j) :=
  symMul_seed_right Y (splitSeed Y pt) (i + 1) (j + 1)
    (i + 1 + j + 1) (by omega) (by omega)

/-- **Right seed law**: multiplying by the seed on the right is the
transition, through the right unitor. -/
theorem splitSeed_mu_right
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Y : D) (pt : 𝟙_ D ⟶ Y)
    (i : ℕ) :
    (splitStage Y i ◁ splitSeed Y pt) ≫ splitMu Y i 0 =
      (ρ_ (splitStage Y i)).hom ≫ splitDelta Y pt i := by
  show (splitStage Y i ◁ splitSeed Y pt) ≫
      symMul (𝟙_ D) Y (i + 1) (0 + 1) ≫
      symPowCast (𝟙_ D) Y
        (by omega : i + 1 + (0 + 1) = i + 1 + 0 + 1) =
    (ρ_ (splitStage Y i)).hom ≫ (ρ_ (splitStage Y i)).inv ≫
      (splitStage Y i ◁ splitSeed Y pt) ≫ symMul (𝟙_ D) Y (i + 1) 1
  have hk : symPowCast (𝟙_ D) Y
      (by omega : i + 1 + (0 + 1) = i + 1 + 0 + 1) = 𝟙 _ := rfl
  erw [hk, Category.comp_id, Iso.hom_inv_id_assoc]

/-- Associativity of the symmetric multiplication with all four
arity transports abstracted, spelt uniformly in the powers. -/
private theorem symMul_assoc_cast
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Y : D)
    (a b g ab bg s t : ℕ)
    (h₁ : a + b = ab) (h₂ : ab + g = t) (h₃ : b + g = bg)
    (h₄ : a + bg = s) (h₅ : s = t) :
    ((symMul (𝟙_ D) Y a b ≫ symPowCast (𝟙_ D) Y h₁) ▷
        symPow (𝟙_ D) Y g) ≫
      (symMul (𝟙_ D) Y ab g ≫ symPowCast (𝟙_ D) Y h₂) =
    (α_ (symPow (𝟙_ D) Y a) (symPow (𝟙_ D) Y b)
        (symPow (𝟙_ D) Y g)).hom ≫
      (symPow (𝟙_ D) Y a ◁
        (symMul (𝟙_ D) Y b g ≫ symPowCast (𝟙_ D) Y h₃)) ≫
      (symMul (𝟙_ D) Y a bg ≫ symPowCast (𝟙_ D) Y h₄) ≫
      symPowCast (𝟙_ D) Y h₅ := by
  subst h₁ h₃ h₂ h₄
  simp only [symPowCast_rfl, Category.comp_id]
  exact symMul_assoc (𝟙_ D) Y a b g

/-- **Associativity of the stage multiplication**, up to the index
transport of `i + 1 + (j + 1 + k) = i + 1 + j + 1 + k`. -/
theorem splitMu_assoc
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Y : D)
    (i j k : ℕ) :
    (splitMu Y i j ▷ splitStage Y k) ≫ splitMu Y (i + 1 + j) k =
      (α_ (splitStage Y i) (splitStage Y j) (splitStage Y k)).hom ≫
        (splitStage Y i ◁ splitMu Y j k) ≫
        splitMu Y i (j + 1 + k) ≫
        chainCast (splitStage Y)
          (by omega : i + 1 + (j + 1 + k) = i + 1 + j + 1 + k) :=
  symMul_assoc_cast Y (i + 1) (j + 1) (k + 1) (i + 1 + j + 1)
    (j + 1 + k + 1) (i + 1 + (j + 1 + k) + 1)
    (i + 1 + j + 1 + k + 1) (by omega) (by omega) (by omega)
    (by omega) (by omega)

/-- **Commutativity of the stage multiplication**, up to the index
transport of `j + 1 + i = i + 1 + j`. -/
theorem splitMu_comm [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Y : D)
    (i j : ℕ) :
    (β_ (splitStage Y i) (splitStage Y j)).hom ≫ splitMu Y j i ≫
        chainCast (splitStage Y)
          (by omega : j + 1 + i = i + 1 + j) =
      splitMu Y i j := by
  show (β_ (symPow (𝟙_ D) Y (i + 1))
        (symPow (𝟙_ D) Y (j + 1))).hom ≫
      (symMul (𝟙_ D) Y (j + 1) (i + 1) ≫
        symPowCast (𝟙_ D) Y
          (by omega : j + 1 + (i + 1) = j + 1 + i + 1)) ≫
      symPowCast (𝟙_ D) Y
        (by omega : j + 1 + i + 1 = i + 1 + j + 1) =
    symMul (𝟙_ D) Y (i + 1) (j + 1) ≫
      symPowCast (𝟙_ D) Y
        (by omega : i + 1 + (j + 1) = i + 1 + j + 1)
  rw [Category.assoc, splitPowCast_comp]
  exact splitSymMul_comm_cast Y _ _

/-- The transitions commute with the index transports. -/
private theorem chainCast_splitDelta
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Y : D) (pt : 𝟙_ D ⟶ Y)
    {a b : ℕ} (h : a = b) :
    chainCast (splitStage Y) h ≫ splitDelta Y pt b =
      splitDelta Y pt a ≫
        chainCast (splitStage Y) (congrArg Nat.succ h) := by
  subst h
  rw [chainCast_rfl, Category.id_comp]
  show splitDelta Y pt a = splitDelta Y pt a ≫ 𝟙 _
  rw [Category.comp_id]

/-- **Left transition law**: transitioning the first factor and
multiplying is multiplying and transitioning, up to the index
transport, through the braiding and the right transition law. -/
theorem splitDelta_mu_left
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Y : D) (pt : 𝟙_ D ⟶ Y)
    (i j : ℕ) :
    (splitDelta Y pt i ▷ splitStage Y j) ≫ splitMu Y (i + 1) j =
      splitMu Y i j ≫ splitDelta Y pt (i + 1 + j) ≫
        chainCast (splitStage Y)
          (Nat.add_right_comm (i + 1) j 1) := by
  have hnat : (splitDelta Y pt i ▷ splitStage Y j) ≫
      (β_ (splitStage Y (i + 1)) (splitStage Y j)).hom =
      (β_ (splitStage Y i) (splitStage Y j)).hom ≫
        (splitStage Y j ◁ splitDelta Y pt i) :=
    BraidedCategory.braiding_naturality_left _ _
  have h5 : (β_ (splitStage Y i) (splitStage Y j)).hom ≫
      splitMu Y j i =
      splitMu Y i j ≫ chainCast (splitStage Y)
        (by omega : i + 1 + j = j + 1 + i) := by
    rw [← splitMu_comm Y i j, Category.assoc, Category.assoc,
      chainCast_trans]
    have hk : chainCast (splitStage Y)
        (by omega : j + 1 + i = j + 1 + i) = 𝟙 _ := rfl
    rw [hk, Category.comp_id]
  rw [← splitMu_comm Y (i + 1) j, reassoc_of% hnat,
    reassoc_of% (splitDelta_mu_right Y pt j i), reassoc_of% h5,
    reassoc_of% (chainCast_splitDelta Y pt
      (by omega : i + 1 + j = j + 1 + i)),
    chainCast_trans]

/-- A one-step chain morphism is the transition followed by the
index transport. -/
private theorem splitChainMap_eq
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Y : D) (pt : 𝟙_ D ⟶ Y)
    {a b : ℕ} (hab : a + 1 = b)
    (h : a ≤ b) :
    chainMap (splitStage Y) (splitDelta Y pt) h =
      splitDelta Y pt a ≫ chainCast (splitStage Y) hab := by
  subst hab
  rw [chainCast_rfl, Category.comp_id]
  exact chainMap_le_succ (splitStage Y) (splitDelta Y pt) a

/-- **Left seed law**: multiplying by the seed on the left is the
one-step chain morphism, through the braiding of the unit. -/
theorem splitSeed_mu_left
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Y : D) (pt : 𝟙_ D ⟶ Y)
    (j : ℕ) :
    (splitSeed Y pt ▷ splitStage Y j) ≫ splitMu Y 0 j =
      (λ_ (splitStage Y j)).hom ≫
        chainMap (splitStage Y) (splitDelta Y pt)
          (Nat.le_add_left j (0 + 1)) := by
  have hmap : chainMap (splitStage Y) (splitDelta Y pt)
      (Nat.le_add_left j (0 + 1)) =
      splitDelta Y pt j ≫ chainCast (splitStage Y)
        (by omega : j + 1 + 0 = 0 + 1 + j) :=
    splitChainMap_eq Y pt (by omega) _
  have hnat : (splitSeed Y pt ▷ splitStage Y j) ≫
      (β_ (splitStage Y 0) (splitStage Y j)).hom =
      (β_ (𝟙_ D) (splitStage Y j)).hom ≫
        (splitStage Y j ◁ splitSeed Y pt) :=
    BraidedCategory.braiding_naturality_left _ _
  rw [hmap, ← splitMu_comm Y 0 j, reassoc_of% hnat,
    reassoc_of% (splitSeed_mu_right Y pt j),
    braiding_tensorUnit_left, Category.assoc,
    Iso.inv_hom_id_assoc]

section Colimit

/-- **The local splitting algebra**: the colimit of the chain of
symmetric powers along multiplication by the point. -/
noncomputable def splitAlgebra
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Y : D) (pt : 𝟙_ D ⟶ Y) [HasColimitsOfShape SmallNat.{v} D] : D :=
  chainColimit (splitStage Y) (splitDelta Y pt)

/-- The unit of the local splitting algebra: the included seed. -/
noncomputable def splitAlgebraUnit
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Y : D) (pt : 𝟙_ D ⟶ Y) [HasColimitsOfShape SmallNat.{v} D] :
    𝟙_ D ⟶ splitAlgebra Y pt :=
  chainColimitUnit (splitStage Y) (splitDelta Y pt)
    (splitSeed Y pt)

/-- **The local splitting algebra as a monoid object**: the unit is
the included seed and the multiplication is assembled from the stage
multiplications through the chain kit. -/
@[reducible]
noncomputable def splitAlgebraMonObj
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Y : D) (pt : 𝟙_ D ⟶ Y) [HasColimitsOfShape SmallNat.{v} D]
    [∀ Z : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight Z)]
    [∀ Z : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft Z)] :
    MonObj (splitAlgebra Y pt) :=
  chainColimitMonObj (splitStage Y) (splitDelta Y pt) (splitMu Y)
    (splitDelta_mu_left Y pt) (splitDelta_mu_right Y pt)
    (splitSeed Y pt) (splitSeed_mu_left Y pt)
    (splitSeed_mu_right Y pt) (splitMu_assoc Y)

/-- **The local splitting algebra is commutative.** -/
theorem splitAlgebra_isCommMonObj
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (Y : D) (pt : 𝟙_ D ⟶ Y) [HasColimitsOfShape SmallNat.{v} D]
    [∀ Z : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight Z)]
    [∀ Z : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft Z)] :
    @IsCommMonObj D _ _ _ (splitAlgebra Y pt)
      (splitAlgebraMonObj Y pt) :=
  chainColimit_isCommMonObj (splitStage Y) (splitDelta Y pt)
    (splitMu Y) (splitDelta_mu_left Y pt)
    (splitDelta_mu_right Y pt) (splitSeed Y pt)
    (splitSeed_mu_left Y pt) (splitSeed_mu_right Y pt)
    (splitMu_assoc Y) (splitMu_comm Y)

end Colimit

end RS
