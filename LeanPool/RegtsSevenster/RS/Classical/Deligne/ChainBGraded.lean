/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainB
import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainIns
import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainMulHet
import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainShift

/-!
# The shifted splitting chains

The off-diagonal lines of the two-index stage lattice: for a
starting bidegree the chain climbs both arities in step, and its
colimit is the corresponding graded component of the splitting
algebra.  The balanced line recovers the degree-zero algebra
carrier.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **The shifted graded component**: the colimit of the
two-index stages along the line through the starting bidegree,
climbing both arities by the seed transition. -/
noncomputable def chainBdeg
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    (p₀ q₀ : ℕ) : D :=
  chainColimit (fun k => chainStage2 A M M' (p₀ + k) (q₀ + k))
    (fun k => chainDelta2 A M M' d (p₀ + k) (q₀ + k))

/-- The stage insertion of a shifted graded component. -/
noncomputable def chainBdegι
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    (p₀ q₀ k : ℕ) :
    chainStage2 A M M' (p₀ + k) (q₀ + k) ⟶
      chainBdeg A M M' d p₀ q₀ :=
  chainColimitι
    (fun k => chainStage2 A M M' (p₀ + k) (q₀ + k))
    (fun k => chainDelta2 A M M' d (p₀ + k) (q₀ + k)) k

/-- The stage insertions commute with the transitions. -/
theorem chainDelta2_chainBdegι
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    (p₀ q₀ k : ℕ) :
    chainDelta2 A M M' d (p₀ + k) (q₀ + k) ≫
        chainBdegι A M M' d p₀ q₀ (k + 1) =
      chainBdegι A M M' d p₀ q₀ k :=
  delta_chainColimitι
    (fun k => chainStage2 A M M' (p₀ + k) (q₀ + k))
    (fun k => chainDelta2 A M M' d (p₀ + k) (q₀ + k)) k

/-- The family cast of a line agrees with the two-index stage
transport. -/
theorem chainCast_line
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (p₀ q₀ : ℕ) {a b : ℕ} (h : a = b) :
    chainCast (fun k => chainStage2 A M M' (p₀ + k) (q₀ + k))
        h =
      chainStage2Cast A M M' (by omega : p₀ + a = p₀ + b)
        (by omega : q₀ + a = q₀ + b) := by
  subst h
  rw [chainCast_rfl, chainStage2Cast_rfl]

/-- **The stagewise multiplication of two lines**: the two-index
stage multiplication, transported onto the sum line. -/
noncomputable def chainBdegMulStage
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (p₀ q₀ r₀ s₀ i j : ℕ) :
    chainStage2 A M M' (p₀ + i) (q₀ + i) ⊗
      chainStage2 A M M' (r₀ + j) (s₀ + j) ⟶
    chainStage2 A M M' (p₀ + r₀ + (i + 1 + j))
      (q₀ + s₀ + (i + 1 + j)) :=
  chainMul2 A M M' (p₀ + i) (q₀ + i) (r₀ + j) (s₀ + j) ≫
    chainStage2Cast A M M'
      (by omega : p₀ + i + 1 + (r₀ + j) = p₀ + r₀ + (i + 1 + j))
      (by omega : q₀ + i + 1 + (s₀ + j) = q₀ + s₀ + (i + 1 + j))

/-- The right transition square of the line multiplication. -/
theorem chainBdegMulStage_delta_right
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') (p₀ q₀ r₀ s₀ i j : ℕ) :
    (chainStage2 A M M' (p₀ + i) (q₀ + i) ◁
        chainDelta2 A M M' d (r₀ + j) (s₀ + j)) ≫
      chainBdegMulStage A M M' p₀ q₀ r₀ s₀ i (j + 1) =
    chainBdegMulStage A M M' p₀ q₀ r₀ s₀ i j ≫
      chainDelta2 A M M' d (p₀ + r₀ + (i + 1 + j))
        (q₀ + s₀ + (i + 1 + j)) := by
  rw [chainBdegMulStage, chainBdegMulStage, ← Category.assoc,
    show chainMul2 A M M' (p₀ + i) (q₀ + i) (r₀ + (j + 1))
        (s₀ + (j + 1)) =
      chainMul2 A M M' (p₀ + i) (q₀ + i) (r₀ + j + 1)
        (s₀ + j + 1) from rfl,
    chainDelta2_mul_right A M M' d (p₀ + i) (q₀ + i)
      (r₀ + j) (s₀ + j),
    Category.assoc]
  conv_rhs => rw [Category.assoc,
    chainStage2Cast_delta2 A M M' d
      (by omega : p₀ + i + 1 + (r₀ + j) =
        p₀ + r₀ + (i + 1 + j))
      (by omega : q₀ + i + 1 + (s₀ + j) =
        q₀ + s₀ + (i + 1 + j))]

/-- The left transition square of the line multiplication. -/
theorem chainBdegMulStage_delta_left
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') (p₀ q₀ r₀ s₀ i j : ℕ) :
    (chainDelta2 A M M' d (p₀ + i) (q₀ + i) ▷
        chainStage2 A M M' (r₀ + j) (s₀ + j)) ≫
      chainBdegMulStage A M M' p₀ q₀ r₀ s₀ (i + 1) j =
    chainBdegMulStage A M M' p₀ q₀ r₀ s₀ i j ≫
      chainDelta2 A M M' d (p₀ + r₀ + (i + 1 + j))
        (q₀ + s₀ + (i + 1 + j)) ≫
      chainStage2Cast A M M'
        (by omega : p₀ + r₀ + (i + 1 + j) + 1 =
          p₀ + r₀ + (i + 1 + 1 + j))
        (by omega : q₀ + s₀ + (i + 1 + j) + 1 =
          q₀ + s₀ + (i + 1 + 1 + j)) := by
  rw [chainBdegMulStage, chainBdegMulStage,
    ← Category.assoc,
    show chainMul2 A M M' (p₀ + (i + 1)) (q₀ + (i + 1))
        (r₀ + j) (s₀ + j) =
      chainMul2 A M M' (p₀ + i + 1) (q₀ + i + 1)
        (r₀ + j) (s₀ + j) from rfl,
    chainDelta2_mul_left A M M' d (p₀ + i) (q₀ + i)
      (r₀ + j) (s₀ + j),
    Category.assoc]
  conv_rhs => rw [Category.assoc,
    reassoc_of% (chainStage2Cast_delta2 A M M' d
      (by omega : p₀ + i + 1 + (r₀ + j) =
        p₀ + r₀ + (i + 1 + j))
      (by omega : q₀ + i + 1 + (s₀ + j) =
        q₀ + s₀ + (i + 1 + j)))]
  simp only [Category.assoc, chainStage2Cast_trans]

section ZeroLine

/-- The stage identification of the balanced line. -/
noncomputable def chainBdegZeroStageIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (k : ℕ) :
    chainStage2 A M M' (0 + k) (0 + k) ≅ chainStage A M M' k
    where
  hom := chainStage2Cast A M M' (Nat.zero_add k)
    (Nat.zero_add k)
  inv := chainStage2Cast A M M' (Nat.zero_add k).symm
    (Nat.zero_add k).symm
  hom_inv_id := by
    show chainStage2Cast A M M' (Nat.zero_add k)
        (Nat.zero_add k) ≫
      chainStage2Cast A M M' (Nat.zero_add k).symm
        (Nat.zero_add k).symm =
      𝟙 (chainStage2 A M M' (0 + k) (0 + k))
    rw [chainStage2Cast_trans]
    exact chainStage2Cast_rfl A M M' _ _
  inv_hom_id := by
    show chainStage2Cast A M M' (Nat.zero_add k).symm
        (Nat.zero_add k).symm ≫
      chainStage2Cast A M M' (Nat.zero_add k)
        (Nat.zero_add k) =
      𝟙 (chainStage2 A M M' k k)
    rw [chainStage2Cast_trans]
    exact chainStage2Cast_rfl A M M' _ _

private theorem chainBdegZeroStage_compatibility
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    (k : ℕ) :
    chainDelta2 A M M' d (0 + k) (0 + k) ≫
        (chainBdegZeroStageIso A M M' (k + 1)).hom =
      (chainBdegZeroStageIso A M M' k).hom ≫ chainDelta2 A M M' d k k := by
  dsimp only [chainBdegZeroStageIso]
  exact (chainStage2Cast_delta2 A M M' d (Nat.zero_add k) (Nat.zero_add k)).symm

/-- **The balanced line is the degree-zero algebra carrier**: the
zero-offset line's colimit is the splitting-chain algebra. -/
noncomputable def chainBdegZeroIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M') :
    chainBdeg A M M' d 0 0 ≅ chainB A M M' d :=
  chainColimitMapIso
    (fun k => chainStage2 A M M' (0 + k) (0 + k))
    (fun k => chainDelta2 A M M' d (0 + k) (0 + k))
    (chainDelta A M M' d)
    (chainBdegZeroStageIso A M M')
    (chainBdegZeroStage_compatibility A M M' d)

end ZeroLine

/-- The stages of the raised line are the shifted stages of the
line. -/
noncomputable def chainBdegSuccStageIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (p₀ q₀ k : ℕ) :
    chainStage2 A M M' (p₀ + 1 + k) (q₀ + 1 + k) ≅
      chainStage2 A M M' (p₀ + (k + 1)) (q₀ + (k + 1)) where
  hom := chainStage2Cast A M M' (by omega) (by omega)
  inv := chainStage2Cast A M M' (by omega) (by omega)
  hom_inv_id := by
    rw [chainStage2Cast_trans]
    exact chainStage2Cast_rfl A M M' _ _
  inv_hom_id := by
    rw [chainStage2Cast_trans]
    exact chainStage2Cast_rfl A M M' _ _

private theorem chainBdegSuccStage_compatibility
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    (p₀ q₀ : ℕ)
    (k : ℕ) :
    chainDelta2 A M M' d (p₀ + 1 + k) (q₀ + 1 + k) ≫
        (chainBdegSuccStageIso A M M' p₀ q₀ (k + 1)).hom =
      (chainBdegSuccStageIso A M M' p₀ q₀ k).hom ≫
        chainDelta2 A M M' d (p₀ + (k + 1)) (q₀ + (k + 1)) := by
  dsimp only [chainBdegSuccStageIso]
  exact (chainStage2Cast_delta2 A M M' d
    (by omega : p₀ + 1 + k = p₀ + (k + 1))
    (by omega : q₀ + 1 + k = q₀ + (k + 1))).symm

/-- **The raised line is the line**: shifting both offsets by one
is passing to the tail of the chain, which has the same
colimit. -/
noncomputable def chainBdegSuccIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    (p₀ q₀ : ℕ) :
    chainBdeg A M M' d (p₀ + 1) (q₀ + 1) ≅
      chainBdeg A M M' d p₀ q₀ :=
  (chainColimitMapIso
    (fun k => chainStage2 A M M' (p₀ + 1 + k) (q₀ + 1 + k))
    (fun k => chainDelta2 A M M' d (p₀ + 1 + k) (q₀ + 1 + k))
    (fun k => chainDelta2 A M M' d (p₀ + (k + 1)) (q₀ + (k + 1)))
    (chainBdegSuccStageIso A M M' p₀ q₀)
    (chainBdegSuccStage_compatibility A M M' d p₀ q₀)) ≪≫
  chainColimitTailIso
    (fun k => chainStage2 A M M' (p₀ + k) (q₀ + k))
    (fun k => chainDelta2 A M M' d (p₀ + k) (q₀ + k))

section MulColimit

/-- **The graded multiplication**: two lines multiply into the
sum line at the colimit level. -/
noncomputable def chainBdegMul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    (d : ModDualityDatum A M M')
    (p₀ q₀ r₀ s₀ : ℕ) :
    chainBdeg A M M' d p₀ q₀ ⊗ chainBdeg A M M' d r₀ s₀ ⟶
      chainBdeg A M M' d (p₀ + r₀) (q₀ + s₀) :=
  chainColimitMulHet
    (fun k => chainStage2 A M M' (p₀ + k) (q₀ + k))
    (fun k => chainStage2 A M M' (r₀ + k) (s₀ + k))
    (fun k => chainStage2 A M M' (p₀ + r₀ + k) (q₀ + s₀ + k))
    (fun k => chainDelta2 A M M' d (p₀ + k) (q₀ + k))
    (fun k => chainDelta2 A M M' d (r₀ + k) (s₀ + k))
    (fun k => chainDelta2 A M M' d (p₀ + r₀ + k)
      (q₀ + s₀ + k))
    (chainBdegMulStage A M M' p₀ q₀ r₀ s₀)
    (chainBdegMulStage_delta_left A M M' d p₀ q₀ r₀ s₀)
    (chainBdegMulStage_delta_right A M M' d p₀ q₀ r₀ s₀)

/-- Transport of a graded component along offset equalities. -/
noncomputable def chainBdegCast
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    {p₀ q₀ p₀' q₀' : ℕ} (hp : p₀ = p₀') (hq : q₀ = q₀') :
    chainBdeg A M M' d p₀ q₀ ⟶ chainBdeg A M M' d p₀' q₀' :=
  eqToHom (by rw [hp, hq])

/-- The trivial offset transport is the identity. -/
@[simp]
theorem chainBdegCast_rfl
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    (p₀ q₀ : ℕ) :
    chainBdegCast A M M' d (rfl : p₀ = p₀) (rfl : q₀ = q₀) =
      𝟙 _ := rfl

/-- Offset transports compose. -/
@[reassoc (attr := simp)]
theorem chainBdegCast_trans
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    {p₀ q₀ p₀' q₀' p₀'' q₀'' : ℕ}
    (hp : p₀ = p₀') (hq : q₀ = q₀')
    (hp' : p₀' = p₀'') (hq' : q₀' = q₀'') :
    chainBdegCast A M M' d hp hq ≫
        chainBdegCast A M M' d hp' hq' =
      chainBdegCast A M M' d (hp.trans hp') (hq.trans hq') := by
  subst hp hq hp' hq'
  simp

/-- On stages, the graded multiplication is the stagewise line
multiplication. -/
@[reassoc]
theorem ι_tensorHom_chainBdegMul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    (d : ModDualityDatum A M M')
    (p₀ q₀ r₀ s₀ i j : ℕ) :
    (chainBdegι A M M' d p₀ q₀ i ⊗ₘ
      chainBdegι A M M' d r₀ s₀ j) ≫
      chainBdegMul A M M' d p₀ q₀ r₀ s₀ =
    chainBdegMulStage A M M' p₀ q₀ r₀ s₀ i j ≫
      chainBdegι A M M' d (p₀ + r₀) (q₀ + s₀) (i + 1 + j) :=
  ι_tensorHom_chainColimitMulHet _ _ _ _ _ _ _ _ _ i j

end MulColimit

section LineIns

/-- The stage insertion transported onto the line. -/
noncomputable def chainBdegInsPStage
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (p₀ q₀ k : ℕ) :
    M'.X ⊗ chainStage2 A M M' (p₀ + k) (q₀ + k) ⟶
      chainStage2 A M M' (p₀ + 1 + k) (q₀ + k) :=
  chainInsP A M M' (p₀ + k) (q₀ + k) ≫
    chainStage2Cast A M M'
      (by omega : p₀ + k + 1 = p₀ + 1 + k)
      (by omega : q₀ + k = q₀ + k)

/-- The line insertion commutes with the transitions. -/
theorem chainBdegInsPStage_delta
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (p₀ q₀ k : ℕ) :
    (M'.X ◁ chainDelta2 A M M' d (p₀ + k) (q₀ + k)) ≫
        chainBdegInsPStage A M M' p₀ q₀ (k + 1) =
      chainBdegInsPStage A M M' p₀ q₀ k ≫
        chainDelta2 A M M' d (p₀ + 1 + k) (q₀ + k) := by
  rw [chainBdegInsPStage, chainBdegInsPStage,
    show chainInsP A M M' (p₀ + (k + 1)) (q₀ + (k + 1)) =
      chainInsP A M M' (p₀ + k + 1) (q₀ + k + 1) from rfl,
    ← Category.assoc,
    chainInsP_delta2 A M M' d (p₀ + k) (q₀ + k),
    Category.assoc]
  conv_rhs => rw [Category.assoc,
    chainStage2Cast_delta2 A M M' d
      (by omega : p₀ + k + 1 = p₀ + 1 + k)
      (by omega : q₀ + k = q₀ + k)]

/-- The line insertion absorbs the chain maps under the
inclusions. -/
theorem lineIns_chainMap_ι
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    (p₀ q₀ : ℕ) {a b : ℕ} (h : a ≤ b) :
    (M'.X ◁ chainMap
        (fun k => chainStage2 A M M' (p₀ + k) (q₀ + k))
        (fun k => chainDelta2 A M M' d (p₀ + k) (q₀ + k)) h) ≫
        chainBdegInsPStage A M M' p₀ q₀ b ≫
        chainBdegι A M M' d (p₀ + 1) q₀ b =
      chainBdegInsPStage A M M' p₀ q₀ a ≫
        chainBdegι A M M' d (p₀ + 1) q₀ a := by
  induction b, h using Nat.le_induction with
  | base =>
    rw [chainMap_self, MonoidalCategory.whiskerLeft_id,
      Category.id_comp]
  | succ b hab ih =>
    rw [chainMap_succ_of_le _ _ hab,
      MonoidalCategory.whiskerLeft_comp, Category.assoc,
      ← Category.assoc (M'.X ◁ chainDelta2 A M M' d
        (p₀ + b) (q₀ + b)),
      chainBdegInsPStage_delta A M M' d p₀ q₀ b,
      Category.assoc, chainDelta2_chainBdegι]
    exact ih

/-- The insertion cocone over the line diagram. -/
noncomputable def chainBdegInsPCocone
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    (p₀ q₀ : ℕ) :
    Cocone (chainDiagram
        (fun k => chainStage2 A M M' (p₀ + k) (q₀ + k))
        (fun k => chainDelta2 A M M' d (p₀ + k) (q₀ + k)) ⋙
      tensorLeft M'.X) :=
  Cocone.mk (chainBdeg A M M' d (p₀ + 1) q₀)
    { app := fun k =>
        chainBdegInsPStage A M M' p₀ q₀
            (smallNatEquiv.inverse.obj k) ≫
          chainBdegι A M M' d (p₀ + 1) q₀
            (smallNatEquiv.inverse.obj k)
      naturality := fun {k k'} f => by
        show (M'.X ◁ chainMap
            (fun k => chainStage2 A M M' (p₀ + k) (q₀ + k))
            (fun k => chainDelta2 A M M' d (p₀ + k) (q₀ + k))
            (leOfHom (smallNatEquiv.inverse.map f))) ≫
            (chainBdegInsPStage A M M' p₀ q₀
                (smallNatEquiv.inverse.obj k') ≫
              chainBdegι A M M' d (p₀ + 1) q₀
                (smallNatEquiv.inverse.obj k')) =
          (chainBdegInsPStage A M M' p₀ q₀
              (smallNatEquiv.inverse.obj k) ≫
            chainBdegι A M M' d (p₀ + 1) q₀
              (smallNatEquiv.inverse.obj k)) ≫
            𝟙 (chainBdeg A M M' d (p₀ + 1) q₀)
        rw [Category.comp_id]
        exact lineIns_chainMap_ι A M M' d p₀ q₀
          (leOfHom (smallNatEquiv.inverse.map f)) }

/-- **The colimit-level line insertion.** -/
noncomputable def chainBdegInsP
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    (d : ModDualityDatum A M M')
    (p₀ q₀ : ℕ) :
    M'.X ⊗ chainBdeg A M M' d p₀ q₀ ⟶
      chainBdeg A M M' d (p₀ + 1) q₀ :=
  ((preservesColimitIso (tensorLeft M'.X)
      (chainDiagram
        (fun k => chainStage2 A M M' (p₀ + k) (q₀ + k))
        (fun k => chainDelta2 A M M' d (p₀ + k) (q₀ + k)))).hom ≫
    colimit.desc _ (chainBdegInsPCocone A M M' d p₀ q₀) :
    (tensorLeft M'.X).obj _ ⟶ chainBdeg A M M' d (p₀ + 1) q₀)

/-- On a stage, the line insertion is insert-then-include. -/
@[reassoc]
theorem whiskerLeft_ι_chainBdegInsP
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    (d : ModDualityDatum A M M')
    (p₀ q₀ k : ℕ) :
    (M'.X ◁ chainBdegι A M M' d p₀ q₀ k) ≫
        chainBdegInsP A M M' d p₀ q₀ =
      chainBdegInsPStage A M M' p₀ q₀ k ≫
        chainBdegι A M M' d (p₀ + 1) q₀ k := by
  show (tensorLeft M'.X).map (colimit.ι (chainDiagram _ _)
      (smallNatEquiv.functor.obj k)) ≫ _ = _
  erw [chainBdegInsP, ι_preservesColimitIso_hom_assoc]
  exact colimit.ι_desc (chainBdegInsPCocone A M M' d p₀ q₀)
    (smallNatEquiv.functor.obj k)

end LineIns

end RS
