/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowMerge

/-!
# Module-level inverses of the merge maps

The merge isomorphism of `PowMerge.lean` upgrades to the category
of modules: the split intertwines the actions, so it bundles as a
module map inverse to the bundled power multiplication
`powMulMod`.  From it, the two insertions of a single factor into
a module power — at the front, through the braiding, and at the
back — become isomorphisms of modules.

* `powMulModInv`: the split as a map of modules, with the
  roundtrips `powMulMod_powMulModInv` and
  `powMulModInv_powMulMod`.
* `powFrontMod`/`powFrontModInv`: the front insertion — the
  `M`-side leg of the chain transition `powDelta` — and its
  inverse, with roundtrips.
* `powBackMod`/`powBackModInv`: the back insertion and its
  inverse, with roundtrips.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## The split as a module map -/

/-- **The split intertwines the module actions**: the inverse of
an equivariant isomorphism is equivariant, by cancelling the
descended power multiplication on the right. -/
theorem powSplit_act [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (a b : ℕ) :
    modPowAct A X (a + 1 + b) ≫ powSplit A X a b =
      (A ◁ powSplit A X a b) ≫
        modTensorAct A (modPowMod A X a) (modPowMod A X b) := by
  have : IsIso (powMulDesc A X a b) :=
    ⟨powSplit A X a b, powMulDesc_powSplit A X a b,
      powSplit_powMulDesc A X a b⟩
  rw [← cancel_mono (powMulDesc A X a b), Category.assoc,
    Category.assoc, powSplit_powMulDesc, Category.comp_id,
    powMulDesc_act, ← MonoidalCategory.whiskerLeft_comp_assoc,
    powSplit_powMulDesc, MonoidalCategory.whiskerLeft_id,
    Category.id_comp]

/-- **The module-level inverse of the merge**: the split bundled
as a map of modules. -/
noncomputable def powMulModInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (a b : ℕ) :
    modPowMod A X (a + 1 + b) ⟶
      modTensorMod A (modPowMod A X a) (modPowMod A X b) :=
  Mod.Hom.mk' (powSplit A X a b) (powSplit_act A X a b)

/-- The bundled merge and its inverse compose to the identity on
the module tensor product. -/
@[reassoc (attr := simp)]
theorem powMulMod_powMulModInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (a b : ℕ) :
    powMulMod A X a b ≫ powMulModInv A X a b =
      𝟙 (modTensorMod A (modPowMod A X a) (modPowMod A X b)) := by
  apply Mod.hom_ext
  change powMulDesc A X a b ≫ powSplit A X a b = 𝟙 _
  exact powMulDesc_powSplit A X a b

/-- The bundled inverse and the merge compose to the identity on
the module power. -/
@[reassoc (attr := simp)]
theorem powMulModInv_powMulMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (a b : ℕ) :
    powMulModInv A X a b ≫ powMulMod A X a b =
      𝟙 (modPowMod A X (a + 1 + b)) := by
  apply Mod.hom_ext
  change powSplit A X a b ≫ powMulDesc A X a b = 𝟙 _
  exact powSplit_powMulDesc A X a b

/-! ## Transport and braiding helpers at the module level -/

/-- Two opposite arity transports of module powers cancel. -/
@[reassoc (attr := simp)]
theorem modPowCastMod_comp_id
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    {a b : ℕ} (h : a + 1 = b + 1)
    (h' : b + 1 = a + 1) :
    modPowCastMod A X h ≫ modPowCastMod A X h' =
      𝟙 (modPowMod A X a) := by
  apply Mod.hom_ext
  change modPowCast A X h ≫ modPowCast A X h' = 𝟙 _
  calc modPowCast A X h ≫ modPowCast A X h'
      = modPowCast A X (h.trans h') := eqToHom_trans _ _
    _ = 𝟙 _ := modPowCast_rfl A X (a + 1)

/-- The braiding of the module tensor product is an involution at
the module level. -/
@[reassoc (attr := simp)]
theorem modTensorSwapMod_modTensorSwapMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A]
    (P Q : Mod D A) :
    modTensorSwapMod A P Q ≫ modTensorSwapMod A Q P =
      𝟙 (modTensorMod A P Q) := by
  apply Mod.hom_ext
  change modTensorSwap A P Q ≫ modTensorSwap A Q P = 𝟙 _
  exact modTensorSwap_modTensorSwap A P Q

/-! ## The front insertion -/

/-- **The front insertion**: merge a fresh factor onto the front
of a module power, through the braiding.  This is the `M`-side leg
of the chain transition `powDelta`. -/
noncomputable def powFrontMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (n : ℕ) :
    modTensorMod A (modPowMod A X n) (modPowMod A X 0) ⟶
      modPowMod A X (n + 1) :=
  modTensorSwapMod A (modPowMod A X n) (modPowMod A X 0) ≫
    powMulMod A X 0 n ≫
    modPowCastMod A X (by omega : 0 + 1 + n + 1 = n + 2)

/-- The inverse of the front insertion. -/
noncomputable def powFrontModInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (n : ℕ) :
    modPowMod A X (n + 1) ⟶
      modTensorMod A (modPowMod A X n) (modPowMod A X 0) :=
  modPowCastMod A X (by omega : n + 1 + 1 = 0 + 1 + n + 1) ≫
    powMulModInv A X 0 n ≫
    modTensorSwapMod A (modPowMod A X 0) (modPowMod A X n)

/-- The front insertion and its inverse compose to the identity
on the module tensor product. -/
@[reassoc (attr := simp)]
theorem powFrontMod_powFrontModInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (n : ℕ) :
    powFrontMod A X n ≫ powFrontModInv A X n =
      𝟙 (modTensorMod A (modPowMod A X n) (modPowMod A X 0)) := by
  rw [powFrontMod, powFrontModInv]
  simp only [Category.assoc]
  rw [modPowCastMod_comp_id_assoc A X
      (by omega : 0 + 1 + n + 1 = n + 2)
      (by omega : n + 1 + 1 = 0 + 1 + n + 1),
    powMulMod_powMulModInv_assoc A X 0 n,
    modTensorSwapMod_modTensorSwapMod]

/-- The inverse of the front insertion and the front insertion
compose to the identity on the module power. -/
@[reassoc (attr := simp)]
theorem powFrontModInv_powFrontMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (n : ℕ) :
    powFrontModInv A X n ≫ powFrontMod A X n =
      𝟙 (modPowMod A X (n + 1)) := by
  rw [powFrontModInv, powFrontMod]
  simp only [Category.assoc]
  rw [modTensorSwapMod_modTensorSwapMod_assoc A
      (modPowMod A X 0) (modPowMod A X n),
    powMulModInv_powMulMod_assoc A X 0 n,
    modPowCastMod_comp_id A X
      (by omega : n + 1 + 1 = 0 + 1 + n + 1)
      (by omega : 0 + 1 + n + 1 = n + 1 + 1)]

/-! ## The back insertion -/

/-- **The back insertion**: merge a fresh factor onto the back of
a module power — the bundled merge with a singleton right
block. -/
noncomputable def powBackMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (n : ℕ) :
    modTensorMod A (modPowMod A X n) (modPowMod A X 0) ⟶
      modPowMod A X (n + 1) :=
  powMulMod A X n 0

/-- The inverse of the back insertion. -/
noncomputable def powBackModInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (n : ℕ) :
    modPowMod A X (n + 1) ⟶
      modTensorMod A (modPowMod A X n) (modPowMod A X 0) :=
  powMulModInv A X n 0

/-- The back insertion and its inverse compose to the identity on
the module tensor product. -/
@[reassoc (attr := simp)]
theorem powBackMod_powBackModInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (n : ℕ) :
    powBackMod A X n ≫ powBackModInv A X n =
      𝟙 (modTensorMod A (modPowMod A X n) (modPowMod A X 0)) :=
  powMulMod_powMulModInv A X n 0

/-- The inverse of the back insertion and the back insertion
compose to the identity on the module power. -/
@[reassoc (attr := simp)]
theorem powBackModInv_powBackMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (X : D) [ModObj A X]
    (n : ℕ) :
    powBackModInv A X n ≫ powBackMod A X n =
      𝟙 (modPowMod A X (n + 1)) :=
  powMulModInv_powMulMod A X n 0

end RS
