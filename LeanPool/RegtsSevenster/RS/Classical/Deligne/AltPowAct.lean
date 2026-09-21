/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.AltPow
import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowAct

/-!
# The monoid action on alternating powers

The antisymmetric counterpart of the symmetric-power module
structure of `PowAct.lean`: over an internal commutative monoid `A`
and a left module `X` in a symmetric monoidal category, the
descended action on the module power commutes with the
antisymmetriser's action — the antisymmetriser is a `ℂ`-linear
combination of permutations, each of which the action passes — so
the action descends through the splitting of `AltPow.lean`, making
every positive alternating power a module.

* `altPow_whiskerLeft_hom_ext`: morphisms out of a left-whiskered
  alternating power are determined by the whiskered projection,
  which is split epi.
* `modPowAct_altPowIdem`: the descended action commutes with the
  antisymmetriser's action.
* `altPowAct`/`altPowModObj`: the action on the alternating power,
  with `altPowσ` a module map.
* `altPowMod`: the bundled module.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## Whiskered extensionality for the alternating power -/

section AltWhisker

/-- Morphisms out of a left-whiskered alternating power are
determined by the whiskered projection, which is split epi. -/
theorem altPow_whiskerLeft_hom_ext
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (P : D) (n : ℕ) {Z : D}
    {k l : P ⊗ altPow A X n ⟶ Z}
    (h : (P ◁ altPowπ A X n) ≫ k = (P ◁ altPowπ A X n) ≫ l) :
    k = l := by
  have hsec : (P ◁ altPowσ A X n) ≫ (P ◁ altPowπ A X n) = 𝟙 _ := by
    rw [← MonoidalCategory.whiskerLeft_comp, altPowσ_altPowπ,
      MonoidalCategory.whiskerLeft_id]
  calc k = ((P ◁ altPowσ A X n) ≫ (P ◁ altPowπ A X n)) ≫ k := by
        rw [hsec, Category.id_comp]
    _ = ((P ◁ altPowσ A X n) ≫ (P ◁ altPowπ A X n)) ≫ l := by
        rw [Category.assoc, Category.assoc, h]
    _ = l := by rw [hsec, Category.id_comp]

end AltWhisker

/-! ## The alternating power as a module -/

section AltAct

/-- **The descended action commutes with the antisymmetriser's
action**: the antisymmetriser is a `ℂ`-linear combination of
permutations, each of which the action passes. -/
theorem modPowAct_altPowIdem
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) :
    modPowAct A X n ≫ altPowIdem A X (n + 1) =
      (A ◁ altPowIdem A X (n + 1)) ≫ modPowAct A X n :=
  modPowAct_alg A X n (antisymmetriser (n + 1))

/-- **The monoid action on the alternating power**, through the
section and the descended action. -/
noncomputable def altPowAct
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [Linear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) :
    A ⊗ altPow A X (n + 1) ⟶ altPow A X (n + 1) :=
  (A ◁ altPowσ A X (n + 1)) ≫ modPowAct A X n ≫
    altPowπ A X (n + 1)

/-- Defining equation of the alternating-power action. -/
@[reassoc (attr := simp)]
theorem whiskerLeft_altPowπ_altPowAct
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) :
    (A ◁ altPowπ A X (n + 1)) ≫ altPowAct A X n =
      modPowAct A X n ≫ altPowπ A X (n + 1) := by
  rw [altPowAct, ← whiskerLeft_comp_assoc, altPowπ_altPowσ,
    reassoc_of% (modPowAct_altPowIdem A X n).symm, altPowIdem_π]

/-- Unitality of the alternating-power action. -/
theorem altPowAct_one
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) :
    η[A] ▷ altPow A X (n + 1) ≫ altPowAct A X n =
      (λ_ (altPow A X (n + 1))).hom := by
  apply altPow_whiskerLeft_hom_ext A X (𝟙_ D) (n + 1)
  rw [whisker_exchange_assoc, whiskerLeft_altPowπ_altPowAct,
    reassoc_of% (modPowAct_one A X n), leftUnitor_naturality]

/-- Associativity of the alternating-power action. -/
theorem altPowAct_mul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) :
    μ[A] ▷ altPow A X (n + 1) ≫ altPowAct A X n =
      (α_ A A (altPow A X (n + 1))).hom ≫
        (A ◁ altPowAct A X n) ≫ altPowAct A X n := by
  apply altPow_whiskerLeft_hom_ext A X (A ⊗ A) (n + 1)
  conv_lhs => rw [whisker_exchange_assoc,
    whiskerLeft_altPowπ_altPowAct,
    reassoc_of% (modPowAct_mul A X n)]
  conv_rhs => rw [associator_naturality_right_assoc,
    ← whiskerLeft_comp_assoc, whiskerLeft_altPowπ_altPowAct,
    whiskerLeft_comp_assoc, whiskerLeft_altPowπ_altPowAct]

/-- **The alternating power of a module is a module**, in every
positive arity. -/
@[implicit_reducible]
noncomputable def altPowModObj
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) :
    ModObj A (altPow A X (n + 1)) where
  smul := altPowAct A X n
  one_smul := altPowAct_one A X n
  mul_smul := altPowAct_mul A X n

/-- The alternating power of a module, bundled as a module. -/
noncomputable def altPowMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) : Mod D A :=
  letI := altPowModObj A X n
  ⟨altPow A X (n + 1)⟩

@[simp] theorem altPowMod_X
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [MonoidalPreadditive D] [HasCoequalizers D] [IsCommMonObj A]
    [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (n : ℕ) :
    (altPowMod A X n).X = altPow A X (n + 1) := rfl

end AltAct

end RS
