/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainBGradedLaws

/-!
# The graded splitting algebra carrier

The full splitting algebra is the sum over the integer degrees of
the graded components: degree `a` is the line through the
starting bidegree `((−a)⁺, a⁺)`, so nonnegative degrees extend
the `M`-arity and negative degrees the `M'`-arity.  The balanced
degree is the algebra of the splitting chain, carrying the unit.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **The graded component at an integer degree**: the line
through `((−a)⁺, a⁺)` — nonnegative degrees raise the `M`-arity,
negative degrees the `M'`-arity. -/
noncomputable def chainBGrComponent
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    (a : ℤ) : D :=
  chainBdeg A M M' d (-a).toNat a.toNat

/-- The degree-zero component is the splitting-chain algebra. -/
noncomputable def chainBGrComponentZeroIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M') :
    chainBGrComponent A M M' d 0 ≅ chainB A M M' d :=
  chainBdegZeroIso A M M' d

/-- The iterated line shift: raising both offsets `n` times is
the identity on the colimit. -/
noncomputable def chainBdegShiftIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    (p₀ q₀ : ℕ) : (n : ℕ) →
    (chainBdeg A M M' d (p₀ + n) (q₀ + n) ≅
      chainBdeg A M M' d p₀ q₀)
  | 0 => Iso.refl _
  | (n + 1) =>
    chainBdegSuccIso A M M' d (p₀ + n) (q₀ + n) ≪≫
      chainBdegShiftIso A M M' d p₀ q₀ n

/-- **The pairwise offsets normalise to the sum degree**: the
line through the sum of two components' offsets is the raised
line of the sum-degree component. -/
noncomputable def chainBGrCompNormIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    (a b : ℤ) :
    chainBdeg A M M' d ((-a).toNat + (-b).toNat)
        (a.toNat + b.toNat) ≅
      chainBGrComponent A M M' d (a + b) :=
  eqToIso (congrArg₂ (chainBdeg A M M' d)
    (by omega : (-a).toNat + (-b).toNat =
      (-(a + b)).toNat + (a.toNat + b.toNat - (a + b).toNat))
    (by omega : a.toNat + b.toNat =
      (a + b).toNat +
        (a.toNat + b.toNat - (a + b).toNat))) ≪≫
  chainBdegShiftIso A M M' d (-(a + b)).toNat (a + b).toNat
    (a.toNat + b.toNat - (a + b).toNat)

section MulColimit

/-- **The pairwise graded product**: two components multiply into
the sum-degree component through the offset normalisation. -/
noncomputable def chainBGrCompMul
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
    (a b : ℤ) :
    chainBGrComponent A M M' d a ⊗ chainBGrComponent A M M' d b ⟶
      chainBGrComponent A M M' d (a + b) :=
  chainBdegMul A M M' d (-a).toNat a.toNat (-b).toNat b.toNat ≫
    (chainBGrCompNormIso A M M' d a b).hom

end MulColimit

section Carrier

/-- **The graded splitting algebra carrier**: the sum of the
graded components over all integer degrees. -/
noncomputable def chainBGr
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D] [HasColimitsOfShape (Discrete ℤ) D]
    (d : ModDualityDatum A M M') : D :=
  ∐ fun a : ℤ => chainBGrComponent A M M' d a

/-- The inclusion of a graded component. -/
noncomputable def chainBGrι
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D] [HasColimitsOfShape (Discrete ℤ) D]
    (d : ModDualityDatum A M M')
    (a : ℤ) : chainBGrComponent A M M' d a ⟶ chainBGr A M M' d :=
  Sigma.ι (fun a : ℤ => chainBGrComponent A M M' d a) a

/-- **The unit of the graded splitting algebra**: the unit of the
balanced algebra, in degree zero. -/
noncomputable def chainBGrUnit
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D] [HasColimitsOfShape (Discrete ℤ) D]
    (d : ModDualityDatum A M M') :
    𝟙_ D ⟶ chainBGr A M M' d :=
  chainBUnit A M M' d ≫
    (chainBGrComponentZeroIso A M M' d).inv ≫
    chainBGrι A M M' d 0

/-- The projection onto the degree-zero component: the identity
in degree zero and zero elsewhere. -/
noncomputable def chainBGrProjZero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D] [HasColimitsOfShape (Discrete ℤ) D]
    (d : ModDualityDatum A M M') :
    chainBGr A M M' d ⟶ chainBGrComponent A M M' d 0 :=
  Sigma.desc fun b =>
    if h : b = 0 then
      eqToHom (by rw [h])
    else 0

/-- The degree-zero inclusion is split by the projection. -/
@[reassoc (attr := simp)]
theorem chainBGrι_projZero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D] [HasColimitsOfShape (Discrete ℤ) D]
    (d : ModDualityDatum A M M') :
    chainBGrι A M M' d 0 ≫ chainBGrProjZero A M M' d =
      𝟙 (chainBGrComponent A M M' d 0) := by
  rw [chainBGrι, chainBGrProjZero]
  erw [Sigma.ι_desc]
  simp

/-- **The graded unit does not vanish** when the balanced unit
does not: the degree-zero retraction detects it. -/
theorem chainBGrUnit_ne_zero
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D] [HasColimitsOfShape (Discrete ℤ) D]
    (d : ModDualityDatum A M M')
    (h : chainBUnit A M M' d ≠ 0) :
    chainBGrUnit A M M' d ≠ 0 := by
  intro h0
  apply h
  have := congrArg (fun t => t ≫ chainBGrProjZero A M M' d ≫
    (chainBGrComponentZeroIso A M M' d).hom) h0
  simpa [chainBGrUnit, Category.assoc] using this

end Carrier

section GradedMul

/-- The multiply-then-include maps against a fixed left component
form a cocone over the right degree. -/
noncomputable def chainBGrMulStageCocone
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    [HasColimitsOfShape (Discrete ℤ) D]
    (d : ModDualityDatum A M M') (a : ℤ) :
    Cocone (Discrete.functor
        (fun b : ℤ => chainBGrComponent A M M' d b) ⋙
      tensorLeft (chainBGrComponent A M M' d a)) :=
  Cocone.mk (chainBGr A M M' d)
    (Discrete.natTrans fun b =>
      chainBGrCompMul A M M' d a b.as ≫
        chainBGrι A M M' d (a + b.as))

/-- The left-component stage of the graded multiplication: a fixed
component multiplies the whole carrier degreewise. -/
noncomputable def chainBGrMulStage
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    [HasColimitsOfShape (Discrete ℤ) D]
    [∀ X : D, PreservesColimitsOfShape (Discrete ℤ) (tensorLeft X)]
    (d : ModDualityDatum A M M')
    (a : ℤ) :
    chainBGrComponent A M M' d a ⊗ chainBGr A M M' d ⟶
      chainBGr A M M' d :=
  ((preservesColimitIso
      (tensorLeft (chainBGrComponent A M M' d a))
      (Discrete.functor
        fun b : ℤ => chainBGrComponent A M M' d b)).hom ≫
    colimit.desc _ (chainBGrMulStageCocone A M M' d a) :
    (tensorLeft (chainBGrComponent A M M' d a)).obj
        (colimit (Discrete.functor
          fun b : ℤ => chainBGrComponent A M M' d b)) ⟶
      chainBGr A M M' d)

/-- On a right component, the stage multiplication is the pairwise
product followed by the sum-degree inclusion. -/
@[reassoc]
theorem whiskerLeft_ι_chainBGrMulStage
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    [HasColimitsOfShape (Discrete ℤ) D]
    [∀ X : D, PreservesColimitsOfShape (Discrete ℤ) (tensorLeft X)]
    (d : ModDualityDatum A M M') (a b : ℤ) :
    (chainBGrComponent A M M' d a ◁ chainBGrι A M M' d b) ≫
        chainBGrMulStage A M M' d a =
      chainBGrCompMul A M M' d a b ≫
        chainBGrι A M M' d (a + b) := by
  show (tensorLeft (chainBGrComponent A M M' d a)).map
      (colimit.ι (Discrete.functor
        fun b : ℤ => chainBGrComponent A M M' d b) ⟨b⟩) ≫
      chainBGrMulStage A M M' d a =
    chainBGrCompMul A M M' d a b ≫ chainBGrι A M M' d (a + b)
  rw [chainBGrMulStage, ι_preservesColimitIso_hom_assoc]
  exact colimit.ι_desc (chainBGrMulStageCocone A M M' d a) ⟨b⟩

/-- The stage multiplications form a cocone over the left
degree. -/
noncomputable def chainBGrMulCocone
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    [HasColimitsOfShape (Discrete ℤ) D]
    [∀ X : D, PreservesColimitsOfShape (Discrete ℤ) (tensorLeft X)]
    (d : ModDualityDatum A M M') :
    Cocone (Discrete.functor
        (fun a : ℤ => chainBGrComponent A M M' d a) ⋙
      tensorRight (chainBGr A M M' d)) :=
  Cocone.mk (chainBGr A M M' d)
    (Discrete.natTrans fun a => chainBGrMulStage A M M' d a.as)

/-- **The multiplication of the graded splitting algebra**: the
pairwise graded products assembled over both degrees. -/
noncomputable def chainBGrMul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    [HasColimitsOfShape (Discrete ℤ) D]
    [∀ X : D, PreservesColimitsOfShape (Discrete ℤ) (tensorLeft X)]
    (d : ModDualityDatum A M M') :
    chainBGr A M M' d ⊗ chainBGr A M M' d ⟶ chainBGr A M M' d :=
  ((preservesColimitIso (tensorRight (chainBGr A M M' d))
      (Discrete.functor
        fun a : ℤ => chainBGrComponent A M M' d a)).hom ≫
    colimit.desc _ (chainBGrMulCocone A M M' d) :
    (tensorRight (chainBGr A M M' d)).obj
        (colimit (Discrete.functor
          fun a : ℤ => chainBGrComponent A M M' d a)) ⟶
      chainBGr A M M' d)

/-- On a left component, the multiplication is the stage
multiplication. -/
@[reassoc]
theorem ι_whiskerRight_chainBGrMul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    [HasColimitsOfShape (Discrete ℤ) D]
    [∀ X : D, PreservesColimitsOfShape (Discrete ℤ) (tensorLeft X)]
    (d : ModDualityDatum A M M')
    (a : ℤ) :
    (chainBGrι A M M' d a ▷ chainBGr A M M' d) ≫
        chainBGrMul A M M' d =
      chainBGrMulStage A M M' d a := by
  show (tensorRight (chainBGr A M M' d)).map
      (colimit.ι (Discrete.functor
        fun a : ℤ => chainBGrComponent A M M' d a) ⟨a⟩) ≫
      chainBGrMul A M M' d =
    chainBGrMulStage A M M' d a
  rw [chainBGrMul, ι_preservesColimitIso_hom_assoc]
  exact colimit.ι_desc (chainBGrMulCocone A M M' d) ⟨a⟩

/-- **Defining equation of the graded multiplication**: on a pair
of components it is the pairwise product followed by the
sum-degree inclusion. -/
@[reassoc]
theorem ι_tensorHom_chainBGrMul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    [HasColimitsOfShape (Discrete ℤ) D]
    [∀ X : D, PreservesColimitsOfShape (Discrete ℤ) (tensorLeft X)]
    (d : ModDualityDatum A M M')
    (a b : ℤ) :
    (chainBGrι A M M' d a ⊗ₘ chainBGrι A M M' d b) ≫
        chainBGrMul A M M' d =
      chainBGrCompMul A M M' d a b ≫
        chainBGrι A M M' d (a + b) := by
  rw [tensorHom_def', Category.assoc,
    ι_whiskerRight_chainBGrMul, whiskerLeft_ι_chainBGrMulStage]

end GradedMul

section ZeroDegreeMul

-- Raised budget: the graded chain's structure maps unfold
-- through the colimit cocone and the duality datum together.
/-- Under the degree-zero identification, the stage insertions of
the balanced line are the stage transports followed by the stage
inclusions of the splitting-chain algebra. -/
@[reassoc]
theorem chainBdegι_chainBdegZeroIso_hom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M') (k : ℕ) :
    chainBdegι A M M' d 0 0 k ≫
        (chainBdegZeroIso A M M' d).hom =
      chainStage2Cast A M M' (Nat.zero_add k) (Nat.zero_add k) ≫
        chainColimitι (chainStage A M M')
          (chainDelta A M M' d) k :=
  ι_chainColimitMapIso_hom _ _ _ _ _ k

-- Raised budget: the graded chain's structure maps unfold
-- through the colimit cocone and the duality datum together.

end ZeroDegreeMul

section GradedComm

/-- The iterated shift commutes with the offset transports. -/
theorem chainBdegShiftIso_hom_cast
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    {p₀ q₀ p₀' q₀' n n' : ℕ}
    (hp : p₀ = p₀') (hq : q₀ = q₀') (hn : n = n') :
    chainBdegCast A M M' d
        (by omega : p₀ + n = p₀' + n')
        (by omega : q₀ + n = q₀' + n') ≫
      (chainBdegShiftIso A M M' d p₀' q₀' n').hom =
    (chainBdegShiftIso A M M' d p₀ q₀ n).hom ≫
      chainBdegCast A M M' d hp hq := by
  subst hp hq hn
  rw [chainBdegCast_rfl, chainBdegCast_rfl, Category.id_comp,
    Category.comp_id]

/-- Degree transports on a component are offset transports. -/
theorem chainBGrComponent_eqToHom_cast
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M') {x y : ℤ} (h : x = y) :
    eqToHom (congrArg (chainBGrComponent A M M' d) h) =
      chainBdegCast A M M' d
        (by rw [h] : (-x).toNat = (-y).toNat)
        (by rw [h] : x.toNat = y.toNat) := by
  subst h
  rfl

/-- Line transports along paired offset equalities are offset
transports. -/
theorem chainBdeg_eqToHom_cast
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    {p₀ q₀ p₀' q₀' : ℕ} (hp : p₀ = p₀') (hq : q₀ = q₀') :
    eqToHom (congrArg₂ (chainBdeg A M M' d) hp hq) =
      chainBdegCast A M M' d hp hq := by
  subst hp hq
  rfl

/-- The normaliser decomposes as an offset transport followed by
the iterated shift. -/
theorem chainBGrCompNormIso_hom_eq
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    (a b : ℤ) :
    (chainBGrCompNormIso A M M' d a b).hom =
      chainBdegCast A M M' d
          (by omega : (-a).toNat + (-b).toNat =
            (-(a + b)).toNat +
              (a.toNat + b.toNat - (a + b).toNat))
          (by omega : a.toNat + b.toNat =
            (a + b).toNat +
              (a.toNat + b.toNat - (a + b).toNat)) ≫
        (chainBdegShiftIso A M M' d (-(a + b)).toNat
          (a + b).toNat
          (a.toNat + b.toNat - (a + b).toNat)).hom := by
  refine (Iso.trans_hom _ _).trans ?_
  refine eq_whisker ?_ _
  refine (eqToIso.hom _).trans ?_
  exact chainBdeg_eqToHom_cast A M M' d _ _

/-- **The offset normalisation is braiding-compatible**: the
normaliser of the swapped degrees followed by the sum-degree
transport is the offset transport followed by the normaliser. -/
theorem chainBGrCompNormIso_comm
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    (a b : ℤ) :
    (chainBGrCompNormIso A M M' d b a).hom ≫
        eqToHom (congrArg (chainBGrComponent A M M' d)
          (Int.add_comm b a)) =
      chainBdegCast A M M' d
          (by omega : (-b).toNat + (-a).toNat =
            (-a).toNat + (-b).toNat)
          (by omega : b.toNat + a.toNat =
            a.toNat + b.toNat) ≫
        (chainBGrCompNormIso A M M' d a b).hom := by
  refine (eq_whisker (chainBGrCompNormIso_hom_eq A M M' d b a)
    _).trans ?_
  refine (whisker_eq _ (chainBGrComponent_eqToHom_cast A M M' d
    (Int.add_comm b a))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _ (chainBdegShiftIso_hom_cast A M M' d
    (by omega : (-(b + a)).toNat = (-(a + b)).toNat)
    (by omega : (b + a).toNat = (a + b).toNat)
    (by omega : b.toNat + a.toNat - (b + a).toNat =
      a.toNat + b.toNat - (a + b).toNat)).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (eq_whisker
    ((chainBdegCast_trans A M M' d _ _ _ _).trans
      (chainBdegCast_trans A M M' d
        (by omega : (-b).toNat + (-a).toNat =
          (-a).toNat + (-b).toNat)
        (by omega : b.toNat + a.toNat = a.toNat + b.toNat)
        (by omega : (-a).toNat + (-b).toNat =
          (-(a + b)).toNat +
            (a.toNat + b.toNat - (a + b).toNat))
        (by omega : a.toNat + b.toNat =
          (a + b).toNat +
            (a.toNat + b.toNat - (a + b).toNat))).symm)
    _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact whisker_eq _
    (chainBGrCompNormIso_hom_eq A M M' d a b).symm

section MulColimit2

/-- **Commutativity of the pairwise graded product**: the
braiding followed by the swapped product is the product, up to
the sum-degree transport. -/
theorem chainBGrCompMul_comm
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
    (a b : ℤ) :
    (β_ (chainBGrComponent A M M' d a)
        (chainBGrComponent A M M' d b)).hom ≫
        chainBGrCompMul A M M' d b a ≫
        eqToHom (congrArg (chainBGrComponent A M M' d)
          (Int.add_comm b a)) =
      chainBGrCompMul A M M' d a b := by
  show (β_ (chainBGrComponent A M M' d a)
      (chainBGrComponent A M M' d b)).hom ≫
      (chainBdegMul A M M' d (-b).toNat b.toNat (-a).toNat
          a.toNat ≫
        (chainBGrCompNormIso A M M' d b a).hom) ≫
      eqToHom (congrArg (chainBGrComponent A M M' d)
        (Int.add_comm b a)) =
    chainBdegMul A M M' d (-a).toNat a.toNat (-b).toNat
        b.toNat ≫
      (chainBGrCompNormIso A M M' d a b).hom
  refine (whisker_eq _ (Category.assoc _ _ _)).trans ?_
  refine (whisker_eq _ (whisker_eq _
    (chainBGrCompNormIso_comm A M M' d a b))).trans ?_
  refine (whisker_eq _ (Category.assoc _ _ _).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact eq_whisker (chainBdegMul_comm A M M' d (-a).toNat
    a.toNat (-b).toNat b.toNat) _

end MulColimit2

section CarrierComm

/-- Degree transports are absorbed by the inclusions. -/
theorem eqToHom_chainBGrι
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D] [HasColimitsOfShape (Discrete ℤ) D]
    (d : ModDualityDatum A M M')
    {x y : ℤ} (h : x = y) :
    eqToHom (congrArg (chainBGrComponent A M M' d) h) ≫
      chainBGrι A M M' d y = chainBGrι A M M' d x := by
  subst h
  simp

/-- Maps out of the carrier tensored on the right are determined
by their restrictions to the components. -/
theorem chainBGr_tensorRight_hom_ext
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D] [HasColimitsOfShape (Discrete ℤ) D]
    [∀ X : D, PreservesColimitsOfShape (Discrete ℤ) (tensorLeft X)]
    (d : ModDualityDatum A M M')
    {X Z : D} {f g : chainBGr A M M' d ⊗ X ⟶ Z}
    (w : ∀ a : ℤ, (chainBGrι A M M' d a ▷ X) ≫ f =
      (chainBGrι A M M' d a ▷ X) ≫ g) : f = g := by
  apply (cancel_epi (preservesColimitIso (tensorRight X)
    (Discrete.functor
      fun a : ℤ => chainBGrComponent A M M' d a)).inv).mp
  apply colimit.hom_ext
  intro k
  obtain ⟨a⟩ := k
  rw [ι_preservesColimitIso_inv_assoc,
    ι_preservesColimitIso_inv_assoc]
  exact w a

/-- Maps out of the carrier tensored on the left are determined
by their restrictions to the components. -/
theorem tensorLeft_chainBGr_hom_ext
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D] [HasColimitsOfShape (Discrete ℤ) D]
    [∀ X : D, PreservesColimitsOfShape (Discrete ℤ) (tensorLeft X)]
    (d : ModDualityDatum A M M')
    {X Z : D} {f g : X ⊗ chainBGr A M M' d ⟶ Z}
    (w : ∀ b : ℤ, (X ◁ chainBGrι A M M' d b) ≫ f =
      (X ◁ chainBGrι A M M' d b) ≫ g) : f = g := by
  apply (cancel_epi (preservesColimitIso (tensorLeft X)
    (Discrete.functor
      fun b : ℤ => chainBGrComponent A M M' d b)).inv).mp
  apply colimit.hom_ext
  intro k
  obtain ⟨b⟩ := k
  rw [ι_preservesColimitIso_inv_assoc,
    ι_preservesColimitIso_inv_assoc]
  exact w b

/-- Maps out of a tensor square of the carrier agree once they
agree on all pairs of components. -/
theorem chainBGr_pair_hom_ext
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D] [HasColimitsOfShape (Discrete ℤ) D]
    [∀ X : D, PreservesColimitsOfShape (Discrete ℤ) (tensorLeft X)]
    (d : ModDualityDatum A M M')
    {Z : D}
    {f g : chainBGr A M M' d ⊗ chainBGr A M M' d ⟶ Z}
    (w : ∀ a b : ℤ,
      (chainBGrι A M M' d a ⊗ₘ chainBGrι A M M' d b) ≫ f =
        (chainBGrι A M M' d a ⊗ₘ chainBGrι A M M' d b) ≫ g) :
    f = g := by
  apply tensorLeft_chainBGr_hom_ext A M M' d
  intro b
  apply chainBGr_tensorRight_hom_ext A M M' d
  intro a
  rw [← Category.assoc, ← Category.assoc,
    show chainBGrι A M M' d a ▷ chainBGrComponent A M M' d b ≫
        chainBGr A M M' d ◁ chainBGrι A M M' d b =
      chainBGrι A M M' d a ⊗ₘ chainBGrι A M M' d b from
        (tensorHom_def _ _).symm]
  exact w a b

/-- **The graded multiplication is commutative**: the braiding
followed by the multiplication is the multiplication. -/
theorem chainBGrMul_comm
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    [HasColimitsOfShape (Discrete ℤ) D]
    [∀ X : D, PreservesColimitsOfShape (Discrete ℤ) (tensorLeft X)]
    (d : ModDualityDatum A M M') :
    (β_ (chainBGr A M M' d) (chainBGr A M M' d)).hom ≫
        chainBGrMul A M M' d =
      chainBGrMul A M M' d := by
  apply chainBGr_pair_hom_ext A M M' d
  intro a b
  rw [← Category.assoc, BraidedCategory.braiding_naturality,
    Category.assoc, ι_tensorHom_chainBGrMul A M M' d b a,
    ι_tensorHom_chainBGrMul A M M' d a b,
    ← eqToHom_chainBGrι A M M' d (Int.add_comm b a)]
  refine Eq.trans ?_
    (eq_whisker (chainBGrCompMul_comm A M M' d a b) _)
  simp only [Category.assoc]

end CarrierComm

end GradedComm

/-! ## The stage-level seed law on the left -/

/-- **The left unit law of the seed** at two indices: multiplying
by the seed on the left is the transition, through the unit
braiding. -/
theorem chainSeed_mul2_left
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (p q : ℕ) :
    (chainSeed A M M' d ▷ chainStage2 A M M' p q) ≫
        chainMul2 A M M' 0 0 p q =
      (λ_ (chainStage2 A M M' p q)).hom ≫
        chainDelta2 A M M' d p q ≫
        chainStage2Cast A M M' (by omega : p + 1 = 0 + 1 + p)
          (by omega : q + 1 = 0 + 1 + q) := by
  have hcm : chainMul2 A M M' 0 0 p q =
      (β_ (chainStage2 A M M' 0 0)
        (chainStage2 A M M' p q)).hom ≫
      chainMul2 A M M' p q 0 0 ≫
      chainStage2Cast A M M' (by omega : p + 1 + 0 = 0 + 1 + p)
        (by omega : q + 1 + 0 = 0 + 1 + q) :=
    (chainMul2_comm A M M' 0 0 p q).symm
  have hnat : (chainSeed A M M' d ▷ chainStage2 A M M' p q) ≫
      (β_ (chainStage2 A M M' 0 0)
        (chainStage2 A M M' p q)).hom =
    (β_ (𝟙_ D) (chainStage2 A M M' p q)).hom ≫
      (chainStage2 A M M' p q ◁ chainSeed A M M' d) :=
    BraidedCategory.braiding_naturality_left
      (chainSeed A M M' d) (chainStage2 A M M' p q)
  refine Eq.trans (whisker_eq _ hcm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker hnat _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    (chainSeed_mul2_right A M M' d p q) _)) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (eq_whisker (braiding_tensorUnit_left
    (chainStage2 A M M' p q)) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Iso.inv_hom_id_assoc _ _)) ?_
  rfl

/-! ## Stage computation of the shift and the normalisation -/

/-- The iterated shift peels off one raise at a time. -/
theorem chainBdegShiftIso_succ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    (p₀ q₀ n : ℕ) :
    chainBdegShiftIso A M M' d p₀ q₀ (n + 1) =
      chainBdegSuccIso A M M' d (p₀ + n) (q₀ + n) ≪≫
        chainBdegShiftIso A M M' d p₀ q₀ n := rfl

-- Raised budget: the graded chain's structure maps unfold
-- through the colimit cocone and the duality datum together.
/-- Under the tail identification, the stage insertions of the
raised line are the stage transports followed by the next stage
insertions of the line. -/
@[reassoc]
theorem chainBdegι_chainBdegSuccIso_hom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M') (p₀ q₀ k : ℕ) :
    chainBdegι A M M' d (p₀ + 1) (q₀ + 1) k ≫
        (chainBdegSuccIso A M M' d p₀ q₀).hom =
      chainStage2Cast A M M'
          (by omega : p₀ + 1 + k = p₀ + (k + 1))
          (by omega : q₀ + 1 + k = q₀ + (k + 1)) ≫
        chainBdegι A M M' d p₀ q₀ (k + 1) := by
  refine Eq.trans (whisker_eq _ (Iso.trans_hom _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (ι_chainColimitMapIso_hom _ _ _ _ _ k) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (ι_chainColimitTail
    (fun k => chainStage2 A M M' (p₀ + k) (q₀ + k))
    (fun k => chainDelta2 A M M' d (p₀ + k) (q₀ + k)) k)) ?_
  rfl

-- Raised budget: the graded chain's structure maps unfold
-- through the colimit cocone and the duality datum together.
/-- Under the iterated shift, the stage insertions of the raised
line are the stage transports followed by the shifted stage
insertions of the line. -/
theorem chainBdegι_chainBdegShiftIso_hom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M') (p₀ q₀ : ℕ) :
    ∀ n k : ℕ,
    chainBdegι A M M' d (p₀ + n) (q₀ + n) k ≫
        (chainBdegShiftIso A M M' d p₀ q₀ n).hom =
      chainStage2Cast A M M'
          (by omega : p₀ + n + k = p₀ + (k + n))
          (by omega : q₀ + n + k = q₀ + (k + n)) ≫
        chainBdegι A M M' d p₀ q₀ (k + n)
  | 0, k => by
    refine Eq.trans (Category.comp_id _) ?_
    exact (chainStage2Cast_chainBdegι A M M' d p₀ q₀
      (rfl : k = k + 0)).symm
  | (n + 1), k => by
    refine Eq.trans (whisker_eq _ (congrArg Iso.hom
      (chainBdegShiftIso_succ A M M' d p₀ q₀ n))) ?_
    refine Eq.trans (whisker_eq _ (Iso.trans_hom _ _)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (chainBdegι_chainBdegSuccIso_hom A M M' d
        (p₀ + n) (q₀ + n) k) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (chainBdegι_chainBdegShiftIso_hom A M M' d p₀ q₀ n (k + 1))) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (chainStage2Cast_trans A M M' _ _ _ _) _) ?_
    refine Eq.trans (whisker_eq _
      (chainStage2Cast_chainBdegι A M M' d p₀ q₀
        (by omega : k + 1 + n = k + (n + 1))).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact eq_whisker (chainStage2Cast_trans A M M' _ _ _ _) _

/-- Under the offset normalisation, the stage insertions of the
summed line are the stage transports followed by the shifted stage
insertions of the sum-degree component. -/
@[reassoc]
theorem chainBdegι_chainBGrCompNormIso_hom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M') (a b : ℤ) (k : ℕ) :
    chainBdegι A M M' d ((-a).toNat + (-b).toNat)
        (a.toNat + b.toNat) k ≫
        (chainBGrCompNormIso A M M' d a b).hom =
      chainStage2Cast A M M'
          (by omega : (-a).toNat + (-b).toNat + k =
            (-(a + b)).toNat +
              (k + (a.toNat + b.toNat - (a + b).toNat)))
          (by omega : a.toNat + b.toNat + k =
            (a + b).toNat +
              (k + (a.toNat + b.toNat - (a + b).toNat))) ≫
        chainBdegι A M M' d (-(a + b)).toNat (a + b).toNat
          (k + (a.toNat + b.toNat - (a + b).toNat)) := by
  refine Eq.trans (whisker_eq _
    (chainBGrCompNormIso_hom_eq A M M' d a b)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (chainBdegι_cast A M M' d _ _ k) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _
    (chainBdegι_chainBdegShiftIso_hom A M M' d
      (-(a + b)).toNat (a + b).toNat
      (a.toNat + b.toNat - (a + b).toNat) k)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact eq_whisker (chainStage2Cast_trans A M M' _ _ _ _) _

/-! ## Tensor surgery -/

/-- Absorb a whiskered morphism into the first tensor factor. -/
private theorem tensorHom_whiskerRight_comp
    [Category.{v} D] [MonoidalCategory D]
    {X₁ X₂ Y₁ Y₂ Z₁ W : D} (a : X₁ ⟶ Y₁) (b : X₂ ⟶ Y₂)
    (f : Y₁ ⟶ Z₁) (r : Z₁ ⊗ Y₂ ⟶ W) :
    (a ⊗ₘ b) ≫ (f ▷ Y₂) ≫ r = ((a ≫ f) ⊗ₘ b) ≫ r := by
  rw [← MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    Category.comp_id]

/-- Absorb a whiskered morphism into the second tensor factor. -/
private theorem tensorHom_whiskerLeft_comp [Category.{v} D] [MonoidalCategory D]
    {X₁ X₂ Y₁ Y₂ Z₂ W : D} (a : X₁ ⟶ Y₁) (b : X₂ ⟶ Y₂)
    (g : Y₂ ⟶ Z₂) (r : Y₁ ⊗ Z₂ ⟶ W) :
    (a ⊗ₘ b) ≫ (Y₁ ◁ g) ≫ r = (a ⊗ₘ (b ≫ g)) ≫ r := by
  rw [← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    Category.comp_id]

/-- Extract a prefix of the first tensor factor as a whisker. -/
private theorem compTensorHom_whiskerRight_split
    [Category.{v} D] [MonoidalCategory D]
    {V₁ W₁ U₁ X₂ U₂ Z : D} (x : V₁ ⟶ W₁) (q₁ : W₁ ⟶ U₁)
    (q₂ : X₂ ⟶ U₂) (r : U₁ ⊗ U₂ ⟶ Z) :
    ((x ≫ q₁) ⊗ₘ q₂) ≫ r = (x ▷ X₂) ≫ (q₁ ⊗ₘ q₂) ≫ r := by
  rw [MonoidalCategory.tensorHom_def,
    MonoidalCategory.tensorHom_def, comp_whiskerRight]
  simp only [Category.assoc]

/-- Extract a prefix of the second tensor factor as a whisker. -/
private theorem compTensorHom_whiskerLeft_split
    [Category.{v} D] [MonoidalCategory D]
    {X₁ U₁ V₂ W₂ U₂ Z : D} (q₁ : X₁ ⟶ U₁) (x : V₂ ⟶ W₂)
    (q₂ : W₂ ⟶ U₂) (r : U₁ ⊗ U₂ ⟶ Z) :
    (q₁ ⊗ₘ (x ≫ q₂)) ≫ r = (X₁ ◁ x) ≫ (q₁ ⊗ₘ q₂) ≫ r := by
  rw [MonoidalCategory.tensorHom_def',
    MonoidalCategory.tensorHom_def',
    MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]

/-! ## Component insertions -/

/-- The stage insertion of a graded component. -/
noncomputable def chainBGrCompι
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    (a : ℤ) (k : ℕ) :
    chainStage2 A M M' ((-a).toNat + k) (a.toNat + k) ⟶
      chainBGrComponent A M M' d a :=
  chainBdegι A M M' d (-a).toNat a.toNat k

/-- Stage transports along a stage equality are absorbed by the
component insertions. -/
theorem chainStage2Cast_chainBGrCompι
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M') (x : ℤ) {a b : ℕ} (h : a = b) :
    chainStage2Cast A M M'
        (by omega : (-x).toNat + a = (-x).toNat + b)
        (by omega : x.toNat + a = x.toNat + b) ≫
      chainBGrCompι A M M' d x b = chainBGrCompι A M M' d x a :=
  chainStage2Cast_chainBdegι A M M' d (-x).toNat x.toNat h

/-- The component insertions absorb the transitions. -/
theorem chainDelta2_chainBGrCompι
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    (x : ℤ) (k : ℕ) :
    chainDelta2 A M M' d ((-x).toNat + k) (x.toNat + k) ≫
        chainBGrCompι A M M' d x (k + 1) =
      chainBGrCompι A M M' d x k :=
  chainDelta2_chainBdegι A M M' d (-x).toNat x.toNat k

/-- Degree transports intertwine the component insertions with
the stage transports. -/
theorem chainBGrCompι_eqToHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M')
    {x y : ℤ} (h : x = y) (k : ℕ) :
    chainBGrCompι A M M' d x k ≫
        eqToHom (congrArg (chainBGrComponent A M M' d) h) =
      chainStage2Cast A M M'
          (by omega : (-x).toNat + k = (-y).toNat + k)
          (by omega : x.toNat + k = y.toNat + k) ≫
        chainBGrCompι A M M' d y k := by
  subst h
  simp only [eqToHom_refl, Category.comp_id]
  exact (chainStage2Cast_chainBGrCompι A M M' d x
    (rfl : k = k)).symm

/-! ## Stage computation and associativity of the pairwise
product -/

section CompMulStages

/-- Maps out of a component tensored on the left are determined
by the stages. -/
theorem tensorLeft_chainBGrComp_hom_ext
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    (d : ModDualityDatum A M M') (b : ℤ) {X Z : D}
    {f g : X ⊗ chainBGrComponent A M M' d b ⟶ Z}
    (w : ∀ j : ℕ, (X ◁ chainBGrCompι A M M' d b j) ≫ f =
      (X ◁ chainBGrCompι A M M' d b j) ≫ g) : f = g :=
  tensorLeft_chainColimit_hom_ext
    (fun k => chainStage2 A M M' ((-b).toNat + k) (b.toNat + k))
    (fun k => chainDelta2 A M M' d ((-b).toNat + k)
      (b.toNat + k))
    (fun j => w j)

/-- Maps out of a triple tensor of components agree once they
agree on all triples of stages. -/
theorem chainBGrComp_triple_hom_ext
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
    (a b c : ℤ) {Z : D}
    {f g : (chainBGrComponent A M M' d a ⊗
      chainBGrComponent A M M' d b) ⊗
      chainBGrComponent A M M' d c ⟶ Z}
    (w : ∀ i j k : ℕ,
      ((chainBGrCompι A M M' d a i ⊗ₘ
          chainBGrCompι A M M' d b j) ⊗ₘ
          chainBGrCompι A M M' d c k) ≫ f =
        ((chainBGrCompι A M M' d a i ⊗ₘ
          chainBGrCompι A M M' d b j) ⊗ₘ
          chainBGrCompι A M M' d c k) ≫ g) : f = g :=
  chainBdeg_triple_hom_ext A M M' d (-a).toNat a.toNat
    (-b).toNat b.toNat (-c).toNat c.toNat
    (fun i j k => w i j k)

/-- **Defining equation of the pairwise graded product on
stages**: the two-index stage multiplication, transported and
inserted at the shifted stage of the sum-degree component. -/
@[reassoc]
theorem ι_tensorHom_chainBGrCompMul
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
    (a b : ℤ) (i j : ℕ) :
    (chainBGrCompι A M M' d a i ⊗ₘ
        chainBGrCompι A M M' d b j) ≫
        chainBGrCompMul A M M' d a b =
      (chainMul2 A M M' ((-a).toNat + i) (a.toNat + i)
          ((-b).toNat + j) (b.toNat + j) ≫
        chainStage2Cast A M M'
          (by omega : (-a).toNat + i + 1 + ((-b).toNat + j) =
            (-(a + b)).toNat +
              (i + 1 + j +
                (a.toNat + b.toNat - (a + b).toNat)))
          (by omega : a.toNat + i + 1 + (b.toNat + j) =
            (a + b).toNat +
              (i + 1 + j +
                (a.toNat + b.toNat - (a + b).toNat)))) ≫
        chainBGrCompι A M M' d (a + b)
          (i + 1 + j + (a.toNat + b.toNat - (a + b).toNat)) := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (ι_tensorHom_chainBdegMul A M M' d
    (-a).toNat a.toNat (-b).toNat b.toNat i j) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _
    (chainBdegι_chainBGrCompNormIso_hom A M M' d a b
      (i + 1 + j))) ?_
  refine Eq.trans (eq_whisker (show
      chainBdegMulStage A M M' (-a).toNat a.toNat (-b).toNat
        b.toNat i j =
      chainMul2 A M M' ((-a).toNat + i) (a.toNat + i)
          ((-b).toNat + j) (b.toNat + j) ≫
        chainStage2Cast A M M'
          (by omega : (-a).toNat + i + 1 + ((-b).toNat + j) =
            (-a).toNat + (-b).toNat + (i + 1 + j))
          (by omega : a.toNat + i + 1 + (b.toNat + j) =
            a.toNat + b.toNat + (i + 1 + j)) from rfl) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    (chainStage2Cast_trans A M M' _ _ _ _) _)) ?_
  exact (Category.assoc _ _ _).symm

/-- **Associativity of the pairwise graded product**: the two
bracketings of a triple product agree up to the sum-degree
transport reassociating the degrees. -/
theorem chainBGrCompMul_assoc
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
    (a b c : ℤ) :
    (chainBGrCompMul A M M' d a b ▷
        chainBGrComponent A M M' d c) ≫
        chainBGrCompMul A M M' d (a + b) c =
      (α_ (chainBGrComponent A M M' d a)
          (chainBGrComponent A M M' d b)
          (chainBGrComponent A M M' d c)).hom ≫
        (chainBGrComponent A M M' d a ◁
          chainBGrCompMul A M M' d b c) ≫
        chainBGrCompMul A M M' d a (b + c) ≫
        eqToHom (congrArg (chainBGrComponent A M M' d)
          (Int.add_assoc a b c).symm) := by
  apply chainBGrComp_triple_hom_ext A M M' d a b c
  intro i j k
  have hass := chainMul2_assoc A M M' ((-a).toNat + i)
    (a.toNat + i) ((-b).toNat + j) (b.toNat + j)
    ((-c).toNat + k) (c.toNat + k)
  rw [show chainStage2Cast A M M'
        (by omega : (-a).toNat + i + 1 + ((-b).toNat + j) + 1 +
            ((-c).toNat + k) =
          (-a).toNat + i + 1 + ((-b).toNat + j) + 1 +
            ((-c).toNat + k))
        (by omega : a.toNat + i + 1 + (b.toNat + j) + 1 +
            (c.toNat + k) =
          a.toNat + i + 1 + (b.toNat + j) + 1 +
            (c.toNat + k)) =
      𝟙 _ from chainStage2Cast_rfl A M M' _ _,
    Category.comp_id] at hass
  rw [tensorHom_whiskerRight_comp,
    ι_tensorHom_chainBGrCompMul A M M' d a b i j,
    compTensorHom_whiskerRight_split,
    ι_tensorHom_chainBGrCompMul A M M' d (a + b) c
      (i + 1 + j + (a.toNat + b.toNat - (a + b).toNat)) k,
    associator_naturality_assoc,
    tensorHom_whiskerLeft_comp,
    ι_tensorHom_chainBGrCompMul A M M' d b c j k,
    compTensorHom_whiskerLeft_split,
    ι_tensorHom_chainBGrCompMul_assoc A M M' d a (b + c) i
      (j + 1 + k + (b.toNat + c.toNat - (b + c).toNat)),
    chainBGrCompι_eqToHom A M M' d (Int.add_assoc a b c).symm
      (i + 1 + (j + 1 + k +
          (b.toNat + c.toNat - (b + c).toNat)) +
        (a.toNat + (b + c).toNat - (a + (b + c)).toNat)),
    MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (chainStage2Cast_whiskerRight_chainMul2 A M M'
      (by omega : (-a).toNat + i + 1 + ((-b).toNat + j) =
        (-(a + b)).toNat +
          (i + 1 + j + (a.toNat + b.toNat - (a + b).toNat)))
      (by omega : a.toNat + i + 1 + (b.toNat + j) =
        (a + b).toNat +
          (i + 1 + j + (a.toNat + b.toNat - (a + b).toNat)))
      ((-c).toNat + k) (c.toNat + k)),
    reassoc_of% (whiskerLeft_chainStage2Cast_chainMul2 A M M'
      ((-a).toNat + i) (a.toNat + i)
      (by omega : (-b).toNat + j + 1 + ((-c).toNat + k) =
        (-(b + c)).toNat +
          (j + 1 + k + (b.toNat + c.toNat - (b + c).toNat)))
      (by omega : b.toNat + j + 1 + (c.toNat + k) =
        (b + c).toNat +
          (j + 1 + k + (b.toNat + c.toNat - (b + c).toNat)))),
    reassoc_of% hass]
  rw [← chainStage2Cast_chainBGrCompι A M M' d (a + b + c)
    (by omega :
      i + 1 + j + (a.toNat + b.toNat - (a + b).toNat) + 1 + k +
        ((a + b).toNat + c.toNat - (a + b + c).toNat) =
      i + 1 + (j + 1 + k +
          (b.toNat + c.toNat - (b + c).toNat)) +
        (a.toNat + (b + c).toNat - (a + (b + c)).toNat))]
  simp only [chainStage2Cast_trans_assoc]

end CompMulStages

/-! ## Associativity of the graded multiplication -/

section CarrierAssoc

/-- Sandwich extensionality: maps out of a tensor product with
the carrier in the middle slot are determined by the components
there. -/
theorem chainBGr_sandwich_hom_ext
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D] [HasColimitsOfShape (Discrete ℤ) D]
    [∀ X : D, PreservesColimitsOfShape (Discrete ℤ) (tensorLeft X)]
    (d : ModDualityDatum A M M')
    (X Y : D) {Z : D}
    {f g : X ⊗ (chainBGr A M M' d ⊗ Y) ⟶ Z}
    (w : ∀ b : ℤ, (X ◁ chainBGrι A M M' d b ▷ Y) ≫ f =
      (X ◁ chainBGrι A M M' d b ▷ Y) ≫ g) : f = g := by
  apply (cancel_epi (preservesColimitIso
    (tensorRight Y ⋙ tensorLeft X)
    (Discrete.functor
      fun b : ℤ => chainBGrComponent A M M' d b)).inv).mp
  apply colimit.hom_ext
  intro k
  obtain ⟨b⟩ := k
  rw [ι_preservesColimitIso_inv_assoc,
    ι_preservesColimitIso_inv_assoc]
  exact w b

/-- Maps out of a tensor square of the carrier whiskered on the
right agree once they agree on all pairs of components. -/
theorem chainBGr_pair_whiskerRight_hom_ext
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D] [HasColimitsOfShape (Discrete ℤ) D]
    [∀ X : D, PreservesColimitsOfShape (Discrete ℤ) (tensorLeft X)]
    (d : ModDualityDatum A M M') {X Z : D}
    {f g : (chainBGr A M M' d ⊗ chainBGr A M M' d) ⊗ X ⟶ Z}
    (w : ∀ a b : ℤ,
      ((chainBGrι A M M' d a ⊗ₘ chainBGrι A M M' d b) ▷ X) ≫
          f =
        ((chainBGrι A M M' d a ⊗ₘ chainBGrι A M M' d b) ▷ X) ≫
          g) :
    f = g := by
  apply (cancel_epi (α_ (chainBGr A M M' d) (chainBGr A M M' d)
    X).inv).mp
  apply chainBGr_tensorRight_hom_ext A M M' d
  intro a
  apply chainBGr_sandwich_hom_ext A M M' d
    (chainBGrComponent A M M' d a) X
  intro b
  have hpre : (chainBGrComponent A M M' d a ◁
      chainBGrι A M M' d b ▷ X) ≫
      (chainBGrι A M M' d a ▷ (chainBGr A M M' d ⊗ X)) ≫
        (α_ (chainBGr A M M' d) (chainBGr A M M' d) X).inv =
    (α_ (chainBGrComponent A M M' d a)
        (chainBGrComponent A M M' d b) X).inv ≫
      ((chainBGrι A M M' d a ⊗ₘ chainBGrι A M M' d b) ▷ X) := by
    rw [whisker_exchange_assoc,
      associator_inv_naturality_middle,
      associator_inv_naturality_left_assoc,
      ← comp_whiskerRight, ← tensorHom_def]
  rw [reassoc_of% hpre, reassoc_of% hpre]
  exact congrArg (CategoryStruct.comp _) (w a b)

/-- Maps out of a triple tensor of the carrier agree once they
agree on all triples of components. -/
theorem chainBGr_triple_hom_ext
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D] [HasColimitsOfShape (Discrete ℤ) D]
    [∀ X : D, PreservesColimitsOfShape (Discrete ℤ) (tensorLeft X)]
    (d : ModDualityDatum A M M')
    {Z : D}
    {f g : (chainBGr A M M' d ⊗ chainBGr A M M' d) ⊗
      chainBGr A M M' d ⟶ Z}
    (w : ∀ a b c : ℤ,
      ((chainBGrι A M M' d a ⊗ₘ chainBGrι A M M' d b) ⊗ₘ
          chainBGrι A M M' d c) ≫ f =
        ((chainBGrι A M M' d a ⊗ₘ chainBGrι A M M' d b) ⊗ₘ
          chainBGrι A M M' d c) ≫ g) : f = g := by
  apply tensorLeft_chainBGr_hom_ext A M M' d
  intro c
  apply chainBGr_pair_whiskerRight_hom_ext A M M' d
  intro a b
  rw [← Category.assoc, ← Category.assoc,
    show (chainBGrι A M M' d a ⊗ₘ chainBGrι A M M' d b) ▷
          chainBGrComponent A M M' d c ≫
        (chainBGr A M M' d ⊗ chainBGr A M M' d) ◁
          chainBGrι A M M' d c =
      (chainBGrι A M M' d a ⊗ₘ chainBGrι A M M' d b) ⊗ₘ
        chainBGrι A M M' d c from (tensorHom_def _ _).symm]
  exact w a b c

/-- **Associativity of the graded multiplication**: the two
bracketings of a triple product agree. -/
theorem chainBGrMul_assoc
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    [HasColimitsOfShape (Discrete ℤ) D]
    [∀ X : D, PreservesColimitsOfShape (Discrete ℤ) (tensorLeft X)]
    (d : ModDualityDatum A M M') :
    (chainBGrMul A M M' d ▷ chainBGr A M M' d) ≫
        chainBGrMul A M M' d =
      (α_ (chainBGr A M M' d) (chainBGr A M M' d)
          (chainBGr A M M' d)).hom ≫
        (chainBGr A M M' d ◁ chainBGrMul A M M' d) ≫
        chainBGrMul A M M' d := by
  apply chainBGr_triple_hom_ext A M M' d
  intro a b c
  rw [tensorHom_whiskerRight_comp,
    ι_tensorHom_chainBGrMul A M M' d a b,
    compTensorHom_whiskerRight_split,
    ι_tensorHom_chainBGrMul A M M' d (a + b) c,
    associator_naturality_assoc,
    tensorHom_whiskerLeft_comp,
    ι_tensorHom_chainBGrMul A M M' d b c,
    compTensorHom_whiskerLeft_split,
    ι_tensorHom_chainBGrMul A M M' d a (b + c),
    ← eqToHom_chainBGrι A M M' d (Int.add_assoc a b c).symm]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (chainBGrCompMul_assoc A M M' d a b c) _) ?_
  simp only [Category.assoc]

end CarrierAssoc

/-! ## The unit laws -/

section UnitLaws

-- Raised budget: the graded chain's structure maps unfold
-- through the colimit cocone and the duality datum together.
/-- **The unit lands at the bottom stage**: through the
degree-zero identification, the unit of the balanced algebra is
the seed at the bottom stage of the degree-zero component. -/
theorem chainBUnit_chainBGrComponentZeroIso_inv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    (d : ModDualityDatum A M M') :
    chainBUnit A M M' d ≫
        (chainBGrComponentZeroIso A M M' d).inv =
      chainSeed A M M' d ≫ chainBGrCompι A M M' d 0 0 := by
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine whisker_eq _ ?_
  refine (Iso.comp_inv_eq _).mpr ?_
  refine Eq.trans ?_
    (chainBdegι_chainBdegZeroIso_hom A M M' d 0).symm
  exact (Category.id_comp _).symm

/-- The stage rule of the pairwise product at degree zero on the
left, with the balanced-line arities normalised. -/
theorem ι_tensorHom_chainBGrCompMul_zero_left
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    (d : ModDualityDatum A M M') (b : ℤ) (j : ℕ) :
    (chainBGrCompι A M M' d 0 0 ⊗ₘ
        chainBGrCompι A M M' d b j) ≫
        chainBGrCompMul A M M' d 0 b =
      (chainMul2 A M M' 0 0 ((-b).toNat + j) (b.toNat + j) ≫
        chainStage2Cast A M M'
          (by omega : 0 + 1 + ((-b).toNat + j) =
            (-(0 + b)).toNat +
              (0 + 1 + j +
                ((0 : ℤ).toNat + b.toNat - (0 + b).toNat)))
          (by omega : 0 + 1 + (b.toNat + j) =
            (0 + b).toNat +
              (0 + 1 + j +
                ((0 : ℤ).toNat + b.toNat - (0 + b).toNat)))) ≫
        chainBGrCompι A M M' d (0 + b)
          (0 + 1 + j +
            ((0 : ℤ).toNat + b.toNat - (0 + b).toNat)) :=
  ι_tensorHom_chainBGrCompMul A M M' d 0 b 0 j

-- Raised budget: the graded chain's structure maps unfold
-- through the colimit cocone and the duality datum together.
/-- **The left unit law of the pairwise graded product**: the
included unit against a component multiplies as the left unitor,
through the sum-degree transport. -/
@[reassoc]
theorem chainBGrCompMul_unit_left
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
    (b : ℤ) :
    ((chainBUnit A M M' d ≫
        (chainBGrComponentZeroIso A M M' d).inv) ▷
        chainBGrComponent A M M' d b) ≫
      chainBGrCompMul A M M' d 0 b ≫
      eqToHom (congrArg (chainBGrComponent A M M' d)
        (Int.zero_add b)) =
    (λ_ (chainBGrComponent A M M' d b)).hom := by
  apply tensorLeft_chainBGrComp_hom_ext A M M' d b
  intro j
  rw [leftUnitor_naturality]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker (whisker_exchange
    (chainBUnit A M M' d ≫
      (chainBGrComponentZeroIso A M M' d).inv)
    (chainBGrCompι A M M' d b j)) _) ?_
  refine Eq.trans (eq_whisker
    (MonoidalCategory.tensorHom_def _ _).symm _) ?_
  refine Eq.trans (eq_whisker (congrArg
    (fun t => t ⊗ₘ chainBGrCompι A M M' d b j)
    (chainBUnit_chainBGrComponentZeroIso_inv A M M' d)) _) ?_
  refine Eq.trans (compTensorHom_whiskerRight_split
    (chainSeed A M M' d) (chainBGrCompι A M M' d 0 0)
    (chainBGrCompι A M M' d b j) _) ?_
  refine Eq.trans (whisker_eq _
    ((Category.assoc _ _ _).symm.trans
      ((eq_whisker (ι_tensorHom_chainBGrCompMul_zero_left
          A M M' d b j) _).trans
        ((Category.assoc _ _ _).trans
          (whisker_eq _ (chainBGrCompι_eqToHom A M M' d
            (Int.zero_add b) (0 + 1 + j +
              ((0 : ℤ).toNat + b.toNat -
                (0 + b).toNat)))))))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    ((Category.assoc _ _ _).symm.trans
      (eq_whisker (chainSeed_mul2_left A M M' d
        ((-b).toNat + j) (b.toNat + j)) _)) _) ?_
  simp only [Category.assoc, chainStage2Cast_trans_assoc]
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (chainStage2Cast_chainBGrCompι A M M' d b
      (by omega : j + 1 = 0 + 1 + j +
        ((0 : ℤ).toNat + b.toNat - (0 + b).toNat))))) ?_
  exact whisker_eq _ (chainDelta2_chainBGrCompι A M M' d b j)

end UnitLaws

section CarrierUnit

/-- **The left unit law of the graded splitting algebra**: the
unit against the carrier is the left unitor. -/
theorem chainBGrUnit_mul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    [HasColimitsOfShape (Discrete ℤ) D]
    [∀ X : D, PreservesColimitsOfShape (Discrete ℤ) (tensorLeft X)]
    (d : ModDualityDatum A M M') :
    (chainBGrUnit A M M' d ▷ chainBGr A M M' d) ≫
        chainBGrMul A M M' d =
      (λ_ (chainBGr A M M' d)).hom := by
  apply tensorLeft_chainBGr_hom_ext A M M' d
  intro b
  rw [chainBGrUnit, MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc]
  rw [ι_whiskerRight_chainBGrMul A M M' d 0,
    whisker_exchange_assoc, whisker_exchange_assoc,
    whiskerLeft_ι_chainBGrMulStage A M M' d 0 b,
    ← eqToHom_chainBGrι A M M' d (Int.zero_add b),
    ← MonoidalCategory.comp_whiskerRight_assoc,
    chainBGrCompMul_unit_left_assoc A M M' d b,
    leftUnitor_naturality]

/-- **The right unit law of the graded splitting algebra**: the
carrier against the unit is the right unitor. -/
theorem chainBGrMul_unit
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    [HasColimitsOfShape (Discrete ℤ) D]
    [∀ X : D, PreservesColimitsOfShape (Discrete ℤ) (tensorLeft X)]
    (d : ModDualityDatum A M M') :
    (chainBGr A M M' d ◁ chainBGrUnit A M M' d) ≫
        chainBGrMul A M M' d =
      (ρ_ (chainBGr A M M' d)).hom := by
  rw [← chainBGrMul_comm A M M' d, ← Category.assoc,
    BraidedCategory.braiding_naturality_right,
    Category.assoc, chainBGrUnit_mul A M M' d,
    braiding_tensorUnit_right, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-! ## The monoid object -/

/-- **The graded splitting algebra is a monoid object**: the
degree-zero unit and the graded multiplication satisfy the
monoid laws. -/
@[reducible]
noncomputable def chainBGrMonObj
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    [HasColimitsOfShape (Discrete ℤ) D]
    [∀ X : D, PreservesColimitsOfShape (Discrete ℤ) (tensorLeft X)]
    (d : ModDualityDatum A M M') :
    MonObj (chainBGr A M M' d) where
  one := chainBGrUnit A M M' d
  mul := chainBGrMul A M M' d
  one_mul := chainBGrUnit_mul A M M' d
  mul_one := chainBGrMul_unit A M M' d
  mul_assoc := chainBGrMul_assoc A M M' d

/-- **The graded splitting algebra is commutative**. -/
theorem chainBGr_isCommMonObj
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    [HasColimitsOfShape SmallNat.{v} D]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorRight X)]
    [∀ X : D, PreservesColimitsOfShape SmallNat.{v} (tensorLeft X)]
    [HasColimitsOfShape (Discrete ℤ) D]
    [∀ X : D, PreservesColimitsOfShape (Discrete ℤ) (tensorLeft X)]
    (d : ModDualityDatum A M M') :
    letI := chainBGrMonObj A M M' d
    IsCommMonObj (chainBGr A M M' d) :=
  letI := chainBGrMonObj A M M' d
  ⟨chainBGrMul_comm A M M' d⟩

end CarrierUnit

end RS
