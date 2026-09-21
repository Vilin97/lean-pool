/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SplitComplement

/-!
# Factor extraction on the dual module

The mirror of the splitting extraction: over the same splitting
data, the unit of the splitting algebra is a direct factor of
the base change of the *dual* module.  The dual insertion
extends `B`-linearly to an evaluation on the base change of the
dual; the copairing, with the primal factor pushed into the
algebra, supplies a coevaluation; the section identity again
makes the pair a retract, and the kernel of the induced linear
idempotent is the complement.  No braiding is needed anywhere:
the copairing already presents the primal factor on the left.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **The dual coevaluation core**: push the primal factor into
the algebra — the module tensor product lands in the base change
of the dual module.  No swap is needed: the primal factor is
already on the left. -/
noncomputable def splitCoevalCoreDual
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] {M : Mod D A} {M' : Mod D A}
    (B : D) [MonObj B] (φ : A ⟶ B) [IsMonHom φ] (v : M.X ⟶ B)
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B]) :
    modTensor A M M' ⟶ baseChange φ M' :=
  modTensorMap A (insHom A B φ v hv) (𝟙 M')

/-- Defining equation of the dual coevaluation core. -/
@[reassoc]
theorem modTensorπ_splitCoevalCoreDual
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] {M : Mod D A} {M' : Mod D A}
    (B : D) [MonObj B] (φ : A ⟶ B) [IsMonHom φ] (v : M.X ⟶ B)
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B]) :
    modTensorπ A M M' ≫ splitCoevalCoreDual A B φ v hv =
      (v ▷ M'.X) ≫ modTensorπ A (restrictRegular φ) M' := by
  rw [splitCoevalCoreDual]
  refine Eq.trans
    (modTensorπ_map A (insHom A B φ v hv) (𝟙 M')) ?_
  exact eq_whisker (by simp) _

/-- **Evaluating the dual coevaluation core multiplies the two
insertions**: the core composite is any descended pair product.
Unlike the primal statement, no braiding step is needed. -/
theorem splitCoevalCoreDual_splitEval
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] {M : Mod D A} {M' : Mod D A}
    (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    (v : M.X ⟶ B) (w : M'.X ⟶ B)
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])
    (p : modTensor A M M' ⟶ B)
    (hp : modTensorπ A M M' ≫ p = (v ⊗ₘ w) ≫ μ[B]) :
    splitCoevalCoreDual A B φ v hv ≫ splitEval A B φ w hw =
      p := by
  apply modTensor_hom_ext
  rw [hp, modTensorπ_splitCoevalCoreDual_assoc A B φ v hv]
  have h1 : (v ▷ M'.X) ≫
      modTensorπ A (restrictRegular φ) M' ≫
        splitEval A B φ w hw =
      (v ▷ M'.X) ≫ (B ◁ w) ≫ μ[B] :=
    whisker_eq _ (modTensorπ_splitEval A B φ w hw)
  have h2 : (v ▷ M'.X) ≫ (B ◁ w) ≫ μ[B] =
      (v ⊗ₘ w) ≫ μ[B] := by
    rw [← MonoidalCategory.tensorHom_def_assoc]
  exact (Category.assoc _ _ _).trans (h1.trans h2)

/-- **The dual coevaluation**: the copair element with its
primal factor pushed into the algebra, multiplied against the
algebra. -/
noncomputable def splitCoevalDual
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A}
    {M' : Mod D A} (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (d : ModDualityDatum A M M')
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B]) :
    B ⟶ baseChange φ M' :=
  (ρ_ B).inv ≫
    (B ◁ (η[A] ≫ d.copair ≫
      splitCoevalCoreDual A B φ v hv)) ≫
    baseChangeAct φ M'

/-- **The dual coevaluation is linear over the algebra.** -/
@[reassoc]
theorem mul_splitCoevalDual
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A}
    {M' : Mod D A} (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (d : ModDualityDatum A M M')
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B]) :
    μ[B] ≫ splitCoevalDual A B φ v d hv =
      (B ◁ splitCoevalDual A B φ v d hv) ≫
        baseChangeAct φ M' := by
  letI := baseChangeModObj φ M'
  have hact : (μ[B] ▷ baseChange φ M') ≫ baseChangeAct φ M' =
      (α_ B B (baseChange φ M')).hom ≫
        (B ◁ baseChangeAct φ M') ≫ baseChangeAct φ M' :=
    mul_actLeft B (baseChange φ M')
  rw [splitCoevalDual]
  rw [rightUnitor_inv_naturality_assoc]
  rw [← whisker_exchange_assoc]
  rw [hact]
  simp only [MonoidalCategory.whiskerLeft_comp,
    Category.assoc]
  simp only [associator_naturality_right_assoc]
  rw [reassoc_of% (show (ρ_ (B ⊗ B)).inv ≫
    (α_ B B (𝟙_ D)).hom = B ◁ (ρ_ B).inv from by monoidal)]

/-- **The dual retract identity**: over splitting data, the dual
coevaluation followed by the dual evaluation is the identity —
the algebra is a direct factor of the base change of the dual
module. -/
theorem splitCoevalDual_splitEval
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A}
    {M' : Mod D A} (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (w : M'.X ⟶ B) (d : ModDualityDatum A M M')
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])
    (p : modTensor A M M' ⟶ B)
    (hp : modTensorπ A M M' ≫ p = (v ⊗ₘ w) ≫ μ[B])
    (hδ : η[A] ≫ d.copair ≫ p = η[B]) :
    splitCoevalDual A B φ v d hv ≫ splitEval A B φ w hw =
      𝟙 B := by
  have hx : (η[A] ≫ d.copair ≫
      splitCoevalCoreDual A B φ v hv) ≫
        splitEval A B φ w hw = η[B] := by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
    refine Eq.trans (whisker_eq _ (whisker_eq _
      (splitCoevalCoreDual_splitEval A B φ v w hv hw
        p hp))) ?_
    exact hδ
  show ((ρ_ B).inv ≫
      (B ◁ (η[A] ≫ d.copair ≫
        splitCoevalCoreDual A B φ v hv)) ≫
      baseChangeAct φ M') ≫ splitEval A B φ w hw = 𝟙 B
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (baseChangeAct_splitEval A B φ w hw))) ?_
  refine Eq.trans
    (whisker_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    (MonoidalCategory.whiskerLeft_comp B _ _).symm _)) ?_
  refine Eq.trans (whisker_eq _ (eq_whisker
    (congrArg (fun t => B ◁ t) hx) _)) ?_
  refine Eq.trans (whisker_eq _ (MonObj.mul_one B)) ?_
  exact (ρ_ B).inv_hom_id

/-- The dual coevaluation, as a module morphism from the regular
module. -/
noncomputable def splitCoevalDualMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A}
    {M' : Mod D A} (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (d : ModDualityDatum A M M')
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B]) :
    regularMod B ⟶ baseChangeMod φ M' :=
  Mod.Hom.mk' (splitCoevalDual A B φ v d hv)
    (by exact mul_splitCoevalDual A B φ v d hv)

/-- **The dual split idempotent** on the base change of the dual
module: evaluate, then coevaluate. -/
noncomputable def splitIdemDual
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A}
    {M' : Mod D A} (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (w : M'.X ⟶ B) (d : ModDualityDatum A M M')
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    baseChange φ M' ⟶ baseChange φ M' :=
  splitEval A B φ w hw ≫ splitCoevalDual A B φ v d hv

/-- The dual split idempotent is idempotent. -/
theorem splitIdemDual_idem
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A}
    {M' : Mod D A} (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (w : M'.X ⟶ B) (d : ModDualityDatum A M M')
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])
    (p : modTensor A M M' ⟶ B)
    (hp : modTensorπ A M M' ≫ p = (v ⊗ₘ w) ≫ μ[B])
    (hδ : η[A] ≫ d.copair ≫ p = η[B]) :
    splitIdemDual A B φ v w d hv hw ≫
        splitIdemDual A B φ v w d hv hw =
      splitIdemDual A B φ v w d hv hw := by
  rw [splitIdemDual, Category.assoc,
    ← Category.assoc (splitCoevalDual A B φ v d hv),
    splitCoevalDual_splitEval A B φ v w d hv hw p hp hδ,
    Category.id_comp]

/-- The dual split idempotent is linear over the algebra. -/
theorem baseChangeAct_splitIdemDual
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A}
    {M' : Mod D A} (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (w : M'.X ⟶ B) (d : ModDualityDatum A M M')
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    baseChangeAct φ M' ≫ splitIdemDual A B φ v w d hv hw =
      (B ◁ splitIdemDual A B φ v w d hv hw) ≫
        baseChangeAct φ M' := by
  rw [splitIdemDual, ← Category.assoc,
    baseChangeAct_splitEval A B φ w hw, Category.assoc,
    mul_splitCoevalDual A B φ v d hv,
    MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]

section Complement

/-- **The dual complement carrier**: the kernel of the dual
split idempotent. -/
noncomputable def splitComplDual
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasCoequalizers D] (A : D) [MonObj A] [IsCommMonObj A]
    {M : Mod D A} {M' : Mod D A} (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (w : M'.X ⟶ B) (d : ModDualityDatum A M M') [HasKernels D]
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) : D :=
  kernel (splitIdemDual A B φ v w d hv hw)

/-- The action of the algebra descends to the dual
complement. -/
noncomputable def splitComplActDual
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D] (A : D)
    [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A} (B : D)
    [MonObj B] [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (w : M'.X ⟶ B) (d : ModDualityDatum A M M') [HasKernels D]
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    B ⊗ splitComplDual A B φ v w d hv hw ⟶
      splitComplDual A B φ v w d hv hw :=
  kernel.lift _
    ((B ◁ kernel.ι (splitIdemDual A B φ v w d hv hw)) ≫
      baseChangeAct φ M') (by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (baseChangeAct_splitIdemDual A B φ v w d hv hw)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    refine Eq.trans (eq_whisker (congrArg (fun t => B ◁ t)
      (kernel.condition
        (splitIdemDual A B φ v w d hv hw))) _) ?_
    rw [MonoidalPreadditive.whiskerLeft_zero,
      Limits.zero_comp]
    rfl)

/-- Defining equation of the dual complement action. -/
@[reassoc]
theorem splitComplActDual_ι
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D] (A : D)
    [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A} (B : D)
    [MonObj B] [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (w : M'.X ⟶ B) (d : ModDualityDatum A M M') [HasKernels D]
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    splitComplActDual A B φ v w d hv hw ≫
        kernel.ι (splitIdemDual A B φ v w d hv hw) =
      (B ◁ kernel.ι (splitIdemDual A B φ v w d hv hw)) ≫
        baseChangeAct φ M' :=
  kernel.lift_ι _ _ _

/-- The unit law of the dual complement action. -/
theorem splitComplActDual_one
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D] (A : D)
    [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A} (B : D)
    [MonObj B] [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (w : M'.X ⟶ B) (d : ModDualityDatum A M M') [HasKernels D]
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    (η[B] ▷ splitComplDual A B φ v w d hv hw) ≫
        splitComplActDual A B φ v w d hv hw =
      (λ_ (splitComplDual A B φ v w d hv hw)).hom := by
  letI := baseChangeModObj φ M'
  have hι : ((η[B] ▷ splitComplDual A B φ v w d hv hw) ≫
      splitComplActDual A B φ v w d hv hw) ≫
      kernel.ι (splitIdemDual A B φ v w d hv hw) =
      (λ_ (splitComplDual A B φ v w d hv hw)).hom ≫
        kernel.ι (splitIdemDual A B φ v w d hv hw) := by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (splitComplActDual_ι A B φ v w d hv hw)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (whisker_exchange η[B] (kernel.ι
        (splitIdemDual A B φ v w d hv hw))).symm _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (one_actLeft B (baseChange φ M'))) ?_
    exact leftUnitor_naturality _
  exact (cancel_mono
    (kernel.ι (splitIdemDual A B φ v w d hv hw))).mp hι

/-- The multiplication law of the dual complement action. -/
theorem splitComplActDual_mul
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D] (A : D)
    [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A} (B : D)
    [MonObj B] [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (w : M'.X ⟶ B) (d : ModDualityDatum A M M') [HasKernels D]
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    (μ[B] ▷ splitComplDual A B φ v w d hv hw) ≫
        splitComplActDual A B φ v w d hv hw =
      (α_ B B (splitComplDual A B φ v w d hv hw)).hom ≫
        (B ◁ splitComplActDual A B φ v w d hv hw) ≫
        splitComplActDual A B φ v w d hv hw := by
  letI := baseChangeModObj φ M'
  have hι : ((μ[B] ▷ splitComplDual A B φ v w d hv hw) ≫
      splitComplActDual A B φ v w d hv hw) ≫
      kernel.ι (splitIdemDual A B φ v w d hv hw) =
      ((α_ B B (splitComplDual A B φ v w d hv hw)).hom ≫
        (B ◁ splitComplActDual A B φ v w d hv hw) ≫
        splitComplActDual A B φ v w d hv hw) ≫
      kernel.ι (splitIdemDual A B φ v w d hv hw) := by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (splitComplActDual_ι A B φ v w d hv hw)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (whisker_exchange μ[B] (kernel.ι
        (splitIdemDual A B φ v w d hv hw))).symm _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (mul_actLeft B (baseChange φ M'))) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (associator_naturality_right B B (kernel.ι
        (splitIdemDual A B φ v w d hv hw))) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine whisker_eq _ ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (splitComplActDual_ι A B φ v w d hv hw)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    refine Eq.trans (eq_whisker (congrArg (fun t => B ◁ t)
      (splitComplActDual_ι A B φ v w d hv hw)) _) ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _) _) ?_
    exact Category.assoc _ _ _
  exact (cancel_mono
    (kernel.ι (splitIdemDual A B φ v w d hv hw))).mp hι

/-- The dual complement, as a module over the algebra. -/
@[implicit_reducible]
noncomputable def splitComplModObjDual
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D] (A : D)
    [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A} (B : D)
    [MonObj B] [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (w : M'.X ⟶ B) (d : ModDualityDatum A M M') [HasKernels D]
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    ModObj B (splitComplDual A B φ v w d hv hw) where
  smul := splitComplActDual A B φ v w d hv hw
  one_smul := splitComplActDual_one A B φ v w d hv hw
  mul_smul := splitComplActDual_mul A B φ v w d hv hw

/-- The dual complement, bundled. -/
noncomputable def splitComplModDual
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D] (A : D)
    [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A} (B : D)
    [MonObj B] [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (w : M'.X ⟶ B) (d : ModDualityDatum A M M') [HasKernels D]
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) : Mod D B :=
  letI := splitComplModObjDual A B φ v w d hv hw
  ⟨splitComplDual A B φ v w d hv hw⟩

/-- The projection onto the dual complement: the complementary
idempotent, corestricted to the kernel. -/
noncomputable def splitComplProjDual
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasCoequalizers D] (A : D) [MonObj A] [IsCommMonObj A]
    {M : Mod D A} {M' : Mod D A} (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (w : M'.X ⟶ B) (d : ModDualityDatum A M M') [HasKernels D]
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])
    (p : modTensor A M M' ⟶ B)
    (hp : modTensorπ A M M' ≫ p = (v ⊗ₘ w) ≫ μ[B])
    (hδ : η[A] ≫ d.copair ≫ p = η[B]) :
    baseChange φ M' ⟶ splitComplDual A B φ v w d hv hw :=
  kernel.lift _ (𝟙 (baseChange φ M') -
    splitIdemDual A B φ v w d hv hw) (by
    rw [Preadditive.sub_comp, Category.id_comp,
      splitIdemDual_idem A B φ v w d hv hw p hp hδ,
      sub_self])

/-- Defining equation of the dual projection. -/
@[reassoc]
theorem splitComplProjDual_ι
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasCoequalizers D] (A : D) [MonObj A] [IsCommMonObj A]
    {M : Mod D A} {M' : Mod D A} (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (w : M'.X ⟶ B) (d : ModDualityDatum A M M') [HasKernels D]
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])
    (p : modTensor A M M' ⟶ B)
    (hp : modTensorπ A M M' ≫ p = (v ⊗ₘ w) ≫ μ[B])
    (hδ : η[A] ≫ d.copair ≫ p = η[B]) :
    splitComplProjDual A B φ v w d hv hw p hp hδ ≫
        kernel.ι (splitIdemDual A B φ v w d hv hw) =
      𝟙 (baseChange φ M') -
        splitIdemDual A B φ v w d hv hw :=
  kernel.lift_ι _ _ _

/-- **The decomposition of the dual base change**, carrier
level: the algebra summand against the dual complement. -/
noncomputable def splitDecompDual
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasCoequalizers D] (A : D) [MonObj A] [IsCommMonObj A]
    {M : Mod D A} {M' : Mod D A} (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (w : M'.X ⟶ B) (d : ModDualityDatum A M M') [HasKernels D]
    [HasBinaryBiproducts D]
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])
    (p : modTensor A M M' ⟶ B)
    (hp : modTensorπ A M M' ≫ p = (v ⊗ₘ w) ≫ μ[B])
    (hδ : η[A] ≫ d.copair ≫ p = η[B]) :
    baseChange φ M' ≅
      B ⊞ splitComplDual A B φ v w d hv hw where
  hom := biprod.lift (splitEval A B φ w hw)
    (splitComplProjDual A B φ v w d hv hw p hp hδ)
  inv := biprod.desc (splitCoevalDual A B φ v d hv)
    (kernel.ι (splitIdemDual A B φ v w d hv hw))
  hom_inv_id := by
    rw [biprod.lift_desc,
      splitComplProjDual_ι A B φ v w d hv hw p hp hδ]
    rw [show splitEval A B φ w hw ≫
      splitCoevalDual A B φ v d hv =
        splitIdemDual A B φ v w d hv hw from rfl]
    rw [add_sub_cancel]
  inv_hom_id := by
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, Category.comp_id]
      apply biprod.hom_ext
      · rw [Category.assoc, biprod.lift_fst, biprod.inl_fst,
          splitCoevalDual_splitEval A B φ v w d hv hw p hp hδ]
      · rw [Category.assoc, biprod.lift_snd, biprod.inl_snd]
        refine (cancel_mono (kernel.ι
          (splitIdemDual A B φ v w d hv hw))).mp ?_
        refine Eq.trans (Category.assoc _ _ _) ?_
        refine Eq.trans (whisker_eq _
          (splitComplProjDual_ι A B φ v w d hv hw
            p hp hδ)) ?_
        rw [Preadditive.comp_sub, Category.comp_id]
        refine Eq.trans ?_ (Limits.zero_comp (f := kernel.ι
          (splitIdemDual A B φ v w d hv hw))).symm
        rw [show splitCoevalDual A B φ v d hv ≫
          splitIdemDual A B φ v w d hv hw =
            (splitCoevalDual A B φ v d hv ≫
              splitEval A B φ w hw) ≫
              splitCoevalDual A B φ v d hv from
          (Category.assoc _ _ _).symm]
        rw [splitCoevalDual_splitEval A B φ v w d hv hw
            p hp hδ,
          Category.id_comp, sub_self]
    · rw [biprod.inr_desc_assoc, Category.comp_id]
      apply biprod.hom_ext
      · rw [Category.assoc, biprod.lift_fst, biprod.inr_fst]
        haveI : IsSplitMono (splitCoevalDual A B φ v d hv) :=
          IsSplitMono.mk' ⟨splitEval A B φ w hw,
            splitCoevalDual_splitEval A B φ v w d hv hw
              p hp hδ⟩
        refine (cancel_mono
          (splitCoevalDual A B φ v d hv)).mp ?_
        rw [Limits.zero_comp, Category.assoc]
        exact kernel.condition _
      · rw [Category.assoc, biprod.lift_snd, biprod.inr_snd]
        refine (cancel_mono (kernel.ι
          (splitIdemDual A B φ v w d hv hw))).mp ?_
        refine Eq.trans (Category.assoc _ _ _) ?_
        refine Eq.trans (whisker_eq _
          (splitComplProjDual_ι A B φ v w d hv hw
            p hp hδ)) ?_
        rw [Preadditive.comp_sub, Category.comp_id]
        have h1 : kernel.ι (splitIdemDual A B φ v w d hv hw) ≫
            splitIdemDual A B φ v w d hv hw = 0 :=
          kernel.condition _
        refine Eq.trans (congrArg (fun t =>
          kernel.ι (splitIdemDual A B φ v w d hv hw) - t)
          h1) ?_
        refine Eq.trans (sub_zero _) ?_
        exact (Category.id_comp _).symm

/-- The dual projection is linear over the algebra. -/
@[reassoc]
theorem baseChangeAct_splitComplProjDual
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D] (A : D)
    [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A} (B : D)
    [MonObj B] [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (w : M'.X ⟶ B) (d : ModDualityDatum A M M') [HasKernels D]
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])
    (p : modTensor A M M' ⟶ B)
    (hp : modTensorπ A M M' ≫ p = (v ⊗ₘ w) ≫ μ[B])
    (hδ : η[A] ≫ d.copair ≫ p = η[B]) :
    baseChangeAct φ M' ≫
        splitComplProjDual A B φ v w d hv hw p hp hδ =
      (B ◁ splitComplProjDual A B φ v w d hv hw p hp hδ) ≫
        splitComplActDual A B φ v w d hv hw := by
  refine (cancel_mono (kernel.ι
    (splitIdemDual A B φ v w d hv hw))).mp ?_
  have hL : (baseChangeAct φ M' ≫
      splitComplProjDual A B φ v w d hv hw p hp hδ) ≫
      kernel.ι (splitIdemDual A B φ v w d hv hw) =
      baseChangeAct φ M' -
        (B ◁ splitIdemDual A B φ v w d hv hw) ≫
          baseChangeAct φ M' := by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (splitComplProjDual_ι A B φ v w d hv hw p hp hδ)) ?_
    rw [Preadditive.comp_sub, Category.comp_id,
      baseChangeAct_splitIdemDual A B φ v w d hv hw]
  have hR : ((B ◁
      splitComplProjDual A B φ v w d hv hw p hp hδ) ≫
      splitComplActDual A B φ v w d hv hw) ≫
      kernel.ι (splitIdemDual A B φ v w d hv hw) =
      baseChangeAct φ M' -
        (B ◁ splitIdemDual A B φ v w d hv hw) ≫
          baseChangeAct φ M' := by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (splitComplActDual_ι A B φ v w d hv hw)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    refine Eq.trans (eq_whisker (congrArg (fun t => B ◁ t)
      (splitComplProjDual_ι A B φ v w d hv hw
        p hp hδ)) _) ?_
    rw [show B ◁ (𝟙 (baseChange φ M') -
        splitIdemDual A B φ v w d hv hw) =
      B ◁ 𝟙 (baseChange φ M') -
        B ◁ splitIdemDual A B φ v w d hv hw from
      Functor.map_sub (F := tensorLeft B)]
    rw [Preadditive.sub_comp,
      MonoidalCategory.whiskerLeft_id, Category.id_comp]
  exact hL.trans hR.symm

/-- Morphisms out of a tensored biproduct are determined by the
two whiskered injections. -/
private theorem whisker_biprod_ext
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasBinaryBiproducts D]
    {P X Y Z : D}
    {f g : P ⊗ (X ⊞ Y) ⟶ Z}
    (h1 : (P ◁ biprod.inl) ≫ f = (P ◁ biprod.inl) ≫ g)
    (h2 : (P ◁ biprod.inr) ≫ f = (P ◁ biprod.inr) ≫ g) :
    f = g := by
  have htot : 𝟙 (P ⊗ (X ⊞ Y)) =
      (P ◁ biprod.fst) ≫ (P ◁ biprod.inl) +
      (P ◁ biprod.snd) ≫ (P ◁ biprod.inr) := by
    rw [← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalPreadditive.whiskerLeft_add, biprod.total,
      MonoidalCategory.whiskerLeft_id]
  calc f = 𝟙 (P ⊗ (X ⊞ Y)) ≫ f := (Category.id_comp f).symm
    _ = ((P ◁ biprod.fst) ≫ (P ◁ biprod.inl) +
        (P ◁ biprod.snd) ≫ (P ◁ biprod.inr)) ≫ f := by
        rw [← htot]
    _ = (P ◁ biprod.fst) ≫ ((P ◁ biprod.inl) ≫ g) +
        (P ◁ biprod.snd) ≫ ((P ◁ biprod.inr) ≫ g) := by
        rw [Preadditive.add_comp]
        simp only [Category.assoc]
        rw [h1, h2]
    _ = ((P ◁ biprod.fst) ≫ (P ◁ biprod.inl) +
        (P ◁ biprod.snd) ≫ (P ◁ biprod.inr)) ≫ g := by
        rw [Preadditive.add_comp]
        simp only [Category.assoc]
    _ = 𝟙 (P ⊗ (X ⊞ Y)) ≫ g := by rw [← htot]
    _ = g := Category.id_comp g

/-- The dual decomposition intertwines the actions, forward
direction. -/
theorem baseChangeAct_splitDecompDualHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D] (A : D)
    [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A} (B : D)
    [MonObj B] [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (w : M'.X ⟶ B) (d : ModDualityDatum A M M') [HasKernels D]
    [HasBinaryBiproducts D]
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])
    (p : modTensor A M M' ⟶ B)
    (hp : modTensorπ A M M' ≫ p = (v ⊗ₘ w) ≫ μ[B])
    (hδ : η[A] ≫ d.copair ≫ p = η[B]) :
    baseChangeAct φ M' ≫
      biprod.lift (splitEval A B φ w hw)
        (splitComplProjDual A B φ v w d hv hw p hp hδ) =
    (B ◁ biprod.lift (splitEval A B φ w hw)
        (splitComplProjDual A B φ v w d hv hw p hp hδ)) ≫
      modBiprodAct B (regularMod B)
        (splitComplModDual A B φ v w d hv hw) := by
  apply biprod.hom_ext
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (biprod.lift_fst _ _)) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (modBiprodAct_fst B (regularMod B)
        (splitComplModDual A B φ v w d hv hw))) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    refine Eq.trans (eq_whisker (congrArg (fun t => B ◁ t)
      (biprod.lift_fst (splitEval A B φ w hw)
        (splitComplProjDual A B φ v w d hv hw
          p hp hδ))) _) ?_
    exact (baseChangeAct_splitEval A B φ w hw).symm
  · refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (biprod.lift_snd _ _)) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _
      (modBiprodAct_snd B (regularMod B)
        (splitComplModDual A B φ v w d hv hw))) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    refine Eq.trans (eq_whisker (congrArg (fun t => B ◁ t)
      (biprod.lift_snd (splitEval A B φ w hw)
        (splitComplProjDual A B φ v w d hv hw
          p hp hδ))) _) ?_
    exact
      (baseChangeAct_splitComplProjDual A B φ v w d hv hw
        p hp hδ).symm

/-- The dual decomposition intertwines the actions, inverse
direction. -/
theorem modBiprodAct_splitDecompDualInv
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D] (A : D)
    [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A} (B : D)
    [MonObj B] [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (w : M'.X ⟶ B) (d : ModDualityDatum A M M') [HasKernels D]
    [HasBinaryBiproducts D]
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    modBiprodAct B (regularMod B)
        (splitComplModDual A B φ v w d hv hw) ≫
      biprod.desc (splitCoevalDual A B φ v d hv)
        (kernel.ι (splitIdemDual A B φ v w d hv hw)) =
    (B ◁ biprod.desc (splitCoevalDual A B φ v d hv)
        (kernel.ι (splitIdemDual A B φ v w d hv hw))) ≫
      baseChangeAct φ M' := by
  apply whisker_biprod_ext
  · refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (actLeft_modBiprodInl B (regularMod B)
        (splitComplModDual A B φ v w d hv hw)).symm _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (biprod.inl_desc _ _)) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    refine Eq.trans (eq_whisker (congrArg (fun t => B ◁ t)
      (biprod.inl_desc (splitCoevalDual A B φ v d hv)
        (kernel.ι
          (splitIdemDual A B φ v w d hv hw)))) _) ?_
    exact (mul_splitCoevalDual A B φ v d hv).symm
  · refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (actLeft_modBiprodInr B (regularMod B)
        (splitComplModDual A B φ v w d hv hw)).symm _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (whisker_eq _ (biprod.inr_desc _ _)) ?_
    refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (eq_whisker
      (MonoidalCategory.whiskerLeft_comp B _ _).symm _) ?_
    refine Eq.trans (eq_whisker (congrArg (fun t => B ◁ t)
      (biprod.inr_desc (splitCoevalDual A B φ v d hv)
        (kernel.ι
          (splitIdemDual A B φ v w d hv hw)))) _) ?_
    exact (splitComplActDual_ι A B φ v w d hv hw).symm

end Complement

section RetractDual

/-- The kernel inclusion of the dual complement, as a module
map. -/
noncomputable def splitComplInclDual
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D] (A : D)
    [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A} (B : D)
    [MonObj B] [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (w : M'.X ⟶ B) (d : ModDualityDatum A M M') [HasKernels D]
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    splitComplModDual A B φ v w d hv hw ⟶
      baseChangeMod φ M' :=
  Mod.Hom.mk' (kernel.ι (splitIdemDual A B φ v w d hv hw))
    (by exact splitComplActDual_ι A B φ v w d hv hw)

/-- The projection onto the dual complement, as a module map. -/
noncomputable def splitComplProjModDual
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D] (A : D)
    [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A} (B : D)
    [MonObj B] [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (w : M'.X ⟶ B) (d : ModDualityDatum A M M') [HasKernels D]
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])
    (p : modTensor A M M' ⟶ B)
    (hp : modTensorπ A M M' ≫ p = (v ⊗ₘ w) ≫ μ[B])
    (hδ : η[A] ≫ d.copair ≫ p = η[B]) :
    baseChangeMod φ M' ⟶
      splitComplModDual A B φ v w d hv hw :=
  Mod.Hom.mk'
    (splitComplProjDual A B φ v w d hv hw p hp hδ) (by
      exact baseChangeAct_splitComplProjDual A B φ v w d
        hv hw p hp hδ)

/-- **The dual complement is a retract of the base change**, at
the carrier. -/
theorem splitComplDual_ι_proj
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [HasCoequalizers D] (A : D) [MonObj A] [IsCommMonObj A]
    {M : Mod D A} {M' : Mod D A} (B : D) [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (w : M'.X ⟶ B) (d : ModDualityDatum A M M') [HasKernels D]
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])
    (p : modTensor A M M' ⟶ B)
    (hp : modTensorπ A M M' ≫ p = (v ⊗ₘ w) ≫ μ[B])
    (hδ : η[A] ≫ d.copair ≫ p = η[B]) :
    kernel.ι (splitIdemDual A B φ v w d hv hw) ≫
        splitComplProjDual A B φ v w d hv hw p hp hδ =
      𝟙 (splitComplDual A B φ v w d hv hw) := by
  refine (cancel_mono
    (kernel.ι (splitIdemDual A B φ v w d hv hw))).mp ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _
    (splitComplProjDual_ι A B φ v w d hv hw p hp hδ)) ?_
  rw [Preadditive.comp_sub, Category.comp_id]
  have h1 : kernel.ι (splitIdemDual A B φ v w d hv hw) ≫
      splitIdemDual A B φ v w d hv hw = 0 :=
    kernel.condition _
  refine Eq.trans (congrArg (fun t =>
    kernel.ι (splitIdemDual A B φ v w d hv hw) - t) h1) ?_
  refine Eq.trans (sub_zero _) ?_
  exact (Category.id_comp _).symm

/-- **The dual complement is a retract of the base change**, as
modules. -/
theorem splitComplInclDual_proj
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D] (A : D)
    [MonObj A] [IsCommMonObj A] {M : Mod D A} {M' : Mod D A} (B : D)
    [MonObj B] [IsCommMonObj B] (φ : A ⟶ B) [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (w : M'.X ⟶ B) (d : ModDualityDatum A M M') [HasKernels D]
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B])
    (p : modTensor A M M' ⟶ B)
    (hp : modTensorπ A M M' ≫ p = (v ⊗ₘ w) ≫ μ[B])
    (hδ : η[A] ≫ d.copair ≫ p = η[B]) :
    splitComplInclDual A B φ v w d hv hw ≫
        splitComplProjModDual A B φ v w d hv hw p hp hδ =
      𝟙 (splitComplModDual A B φ v w d hv hw) := by
  apply Mod.Hom.ext
  exact splitComplDual_ι_proj A B φ v w d hv hw p hp hδ

end RetractDual

end RS
