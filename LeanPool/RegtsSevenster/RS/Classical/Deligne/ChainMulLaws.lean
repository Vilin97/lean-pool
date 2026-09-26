/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainMul
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.TensorMuBraid

/-!
# Commutativity and associativity of the chain multiplication

The chain multiplication braids and reassociates exactly as the
symmetric multiplication it descends from.  Both laws are proved by
cancelling the jointly epimorphic stage projections and reducing to
the corresponding `symMul` laws together with the coherence of the
interchange `tensorμ`.  Transports of chain stages along equalities
of arities are packaged as `chainStageCast`.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## Stage transports -/

section StageCast

/-- Transport of a chain stage along an equality of arities. -/
noncomputable def chainStageCast
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    {j k : ℕ} (h : j = k) :
    chainStage A M M' j ⟶ chainStage A M M' k :=
  eqToHom (congrArg (chainStage A M M') h)

/-- The trivial transport is the identity. -/
@[simp]
theorem chainStageCast_rfl
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (k : ℕ) :
    chainStageCast A M M' (rfl : k = k) = 𝟙 _ := rfl

/-- Stage transports compose. -/
@[reassoc (attr := simp)]
theorem chainStageCast_trans
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    {i j k : ℕ} (h : i = j) (h' : j = k) :
    chainStageCast A M M' h ≫ chainStageCast A M M' h' =
      chainStageCast A M M' (h.trans h') := by
  subst h h'
  simp

/-- The stage projection intertwines the symmetric-power and stage
transports. -/
@[reassoc]
theorem modTensorπ_chainStageCast
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    {j k : ℕ} (h : j = k) :
    modTensorπ A (symPowMod A M'.X j) (symPowMod A M.X j) ≫
        chainStageCast A M M' h =
      (symPowCast A M'.X (congrArg Nat.succ h) ⊗ₘ
          symPowCast A M.X (congrArg Nat.succ h)) ≫
        modTensorπ A (symPowMod A M'.X k) (symPowMod A M.X k) := by
  subst h
  simp only [chainStageCast_rfl, symPowCast_rfl,
    MonoidalCategory.id_tensorHom_id]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

end StageCast

/-! ## Epimorphy of whiskered stage projections -/

section EpiKit

/-- The module-tensor projection is an epimorphism. -/
instance epi_modTensorπ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] (N : Mod D A) (P : Mod D A) :
    Epi (modTensorπ A N P) :=
  ⟨fun _ _ w => modTensor_hom_ext A N P w⟩

/-- The right-whiskered module-tensor projection is an
epimorphism. -/
instance epi_modTensorπ_whiskerRight
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] (N : Mod D A) (P : Mod D A)
    (W : D) :
    Epi (modTensorπ A N P ▷ W) :=
  ⟨fun _ _ w => modTensor_whiskerR_hom_ext A N P W w⟩

/-- The left-whiskered module-tensor projection is an
epimorphism. -/
instance epi_whiskerLeft_modTensorπ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (N : Mod D A) (P : Mod D A)
    (Q : D) :
    Epi (Q ◁ modTensorπ A N P) :=
  ⟨fun _ _ w => modTensor_whisker_hom_ext A N P Q w⟩

/-- Whiskering the module-tensor coequalizer on the right and then
on the left still yields a colimit cofork. -/
noncomputable def modTensorWhiskerRLIsColimit
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] (N : Mod D A) (P : Mod D A)
    (W Q : D) :
    IsColimit (Cofork.ofπ (Q ◁ (modTensorπ A N P ▷ W))
      (by rw [← MonoidalCategory.whiskerLeft_comp,
        ← comp_whiskerRight, modTensor_condition,
        comp_whiskerRight, MonoidalCategory.whiskerLeft_comp]) :
      Cofork (Q ◁ (modTensorLegM A N P ▷ W))
        (Q ◁ (modTensorLegN A N P ▷ W))) :=
  isColimitCoforkMapOfIsColimit (tensorLeft Q) _
    (modTensorWhiskerRIsColimit A N P W)

/-- The doubly whiskered module-tensor projection is an
epimorphism. -/
instance epi_whiskerLeft_modTensorπ_whiskerRight
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] (N : Mod D A) (P : Mod D A)
    (W Q : D) :
    Epi (Q ◁ (modTensorπ A N P ▷ W)) :=
  epi_of_isColimit_cofork (modTensorWhiskerRLIsColimit A N P W Q)

/-- A projection whiskered on the right by two objects is an
epimorphism. -/
instance epi_modTensorπ_whiskerRight_whiskerRight
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] (N : Mod D A) (P : Mod D A)
    (V W : D) :
    Epi ((modTensorπ A N P ▷ V) ▷ W) := by
  rw [show (modTensorπ A N P ▷ V) ▷ W =
      (α_ (N.X ⊗ P.X) V W).hom ≫
        (modTensorπ A N P ▷ (V ⊗ W)) ≫
        (α_ (modTensor A N P) V W).inv by
    simp [MonoidalCategory.whiskerRight_tensor]]
  infer_instance

/-- A projection whiskered on the left and then on the right is an
epimorphism. -/
instance epi_whiskerLeft_modTensorπ_whiskerRight'
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] (N : Mod D A) (P : Mod D A)
    (Q W : D) :
    Epi ((Q ◁ modTensorπ A N P) ▷ W) := by
  rw [MonoidalCategory.whisker_assoc]
  infer_instance

/-- A projection whiskered on the left by two objects is an
epimorphism. -/
instance epi_whiskerLeft_whiskerLeft_modTensorπ
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (N : Mod D A) (P : Mod D A)
    (Q R : D) :
    Epi (Q ◁ (R ◁ modTensorπ A N P)) := by
  rw [show Q ◁ (R ◁ modTensorπ A N P) =
      (α_ Q R (N.X ⊗ P.X)).inv ≫
        ((Q ⊗ R) ◁ modTensorπ A N P) ≫
        (α_ Q R (modTensor A N P)).hom by monoidal]
  infer_instance

/-- The tensor product of two module-tensor projections is an
epimorphism. -/
instance epi_modTensorπ_tensorHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] (N : Mod D A) (P : Mod D A) (Q : Mod D A)
    (R : Mod D A) :
    Epi (modTensorπ A N P ⊗ₘ modTensorπ A Q R) := by
  rw [MonoidalCategory.tensorHom_def]
  infer_instance

/-- The right-whiskered tensor product of two projections is an
epimorphism. -/
instance epi_modTensorπ_tensorHom_whiskerRight
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] (N : Mod D A) (P : Mod D A) (Q : Mod D A)
    (R : Mod D A)
    (W : D) :
    Epi ((modTensorπ A N P ⊗ₘ modTensorπ A Q R) ▷ W) := by
  rw [MonoidalCategory.tensorHom_def, comp_whiskerRight]
  infer_instance

/-- The left-whiskered tensor product of two projections is an
epimorphism. -/
instance epi_modTensorπ_tensorHom_whiskerLeft
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] (N : Mod D A) (P : Mod D A) (Q : Mod D A)
    (R : Mod D A)
    (W : D) :
    Epi (W ◁ (modTensorπ A N P ⊗ₘ modTensorπ A Q R)) := by
  rw [MonoidalCategory.tensorHom_def,
    MonoidalCategory.whiskerLeft_comp]
  infer_instance

/-- The tensored triple of module-tensor projections is an
epimorphism. -/
instance epi_modTensorπ_tensorHom_tensorHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] (N : Mod D A) (P : Mod D A) (Q : Mod D A)
    (R : Mod D A) (S : Mod D A) (T : Mod D A) :
    Epi ((modTensorπ A N P ⊗ₘ modTensorπ A Q R) ⊗ₘ
      modTensorπ A S T) := by
  rw [MonoidalCategory.tensorHom_def]
  infer_instance

end EpiKit

/-! ## Symmetric-power laws with transported arities -/

section SymCast

/-- Commutativity of the symmetric multiplication, with both sides
transported to a common arity. -/
private theorem symMul_comm_cast
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] (X : D) [ModObj A X]
    {a b c : ℕ} (h : b + a = c)
    (h' : a + b = c) :
    (β_ (symPow A X a) (symPow A X b)).hom ≫ symMul A X b a ≫
        symPowCast A X h =
      symMul A X a b ≫ symPowCast A X h' := by
  subst h
  rw [symPowCast_rfl, Category.comp_id]
  exact symMul_comm A X a b

end SymCast

/-! ## Commutativity of the chain multiplication -/

section ChainComm

private theorem chainMul_comm_factors
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (m n : ℕ)
    (h₀ : n + 1 + m = m + 1 + n) :
    (((β_ (symPow A M'.X (m + 1))
        (symPow A M'.X (n + 1))).hom ≫
        symMul A M'.X (n + 1) (m + 1)) ≫
        symPowCast A M'.X (congrArg Nat.succ h₀) =
      symMul A M'.X (m + 1) (n + 1)) ∧
    (((β_ (symPow A M.X (m + 1))
        (symPow A M.X (n + 1))).hom ≫
        symMul A M.X (n + 1) (m + 1)) ≫
        symPowCast A M.X (congrArg Nat.succ h₀) =
      symMul A M.X (m + 1) (n + 1)) := by
  have hfac₁ :
      (β_ (symPow A M'.X (m + 1)) (symPow A M'.X (n + 1))).hom ≫
          symMul A M'.X (n + 1) (m + 1) ≫
          symPowCast A M'.X (congrArg Nat.succ h₀) =
        symMul A M'.X (m + 1) (n + 1) ≫
          symPowCast A M'.X
            (rfl : m + 1 + (n + 1) = m + 1 + (n + 1)) :=
    symMul_comm_cast A M'.X (congrArg Nat.succ h₀) rfl
  have hfac₂ :
      (β_ (symPow A M.X (m + 1)) (symPow A M.X (n + 1))).hom ≫
          symMul A M.X (n + 1) (m + 1) ≫
          symPowCast A M.X (congrArg Nat.succ h₀) =
        symMul A M.X (m + 1) (n + 1) ≫
          symPowCast A M.X
            (rfl : m + 1 + (n + 1) = m + 1 + (n + 1)) :=
    symMul_comm_cast A M.X (congrArg Nat.succ h₀) rfl
  have hkill₁ : symMul A M'.X (m + 1) (n + 1) ≫
      symPowCast A M'.X
        (rfl : m + 1 + (n + 1) = m + 1 + (n + 1)) =
      symMul A M'.X (m + 1) (n + 1) := by
    rw [symPowCast_rfl, Category.comp_id]
  have hkill₂ : symMul A M.X (m + 1) (n + 1) ≫
      symPowCast A M.X
        (rfl : m + 1 + (n + 1) = m + 1 + (n + 1)) =
      symMul A M.X (m + 1) (n + 1) := by
    rw [symPowCast_rfl, Category.comp_id]
  have hfacL₁ : ((β_ (symPow A M'.X (m + 1))
        (symPow A M'.X (n + 1))).hom ≫
        symMul A M'.X (n + 1) (m + 1)) ≫
        symPowCast A M'.X (congrArg Nat.succ h₀) =
      symMul A M'.X (m + 1) (n + 1) :=
    (Category.assoc _ _ _).trans (hfac₁.trans hkill₁)
  have hfacL₂ : ((β_ (symPow A M.X (m + 1))
        (symPow A M.X (n + 1))).hom ≫
        symMul A M.X (n + 1) (m + 1)) ≫
        symPowCast A M.X (congrArg Nat.succ h₀) =
      symMul A M.X (m + 1) (n + 1) :=
    (Category.assoc _ _ _).trans (hfac₂.trans hkill₂)
  exact ⟨hfacL₁, hfacL₂⟩

/-- **Commutativity of the chain multiplication**, up to the stage
transport of `n + 1 + m = m + 1 + n`. -/
theorem chainMul_comm
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (m n : ℕ) :
    (β_ (chainStage A M M' m) (chainStage A M M' n)).hom ≫
        chainMul A M M' n m ≫
        chainStageCast A M M' (by omega : n + 1 + m = m + 1 + n) =
      chainMul A M M' m n := by
  have h₀ : n + 1 + m = m + 1 + n := by omega
  obtain ⟨hfacL₁, hfacL₂⟩ := chainMul_comm_factors A M M' m n h₀
  have hβ :
      (modTensorπ A (symPowMod A M'.X m) (symPowMod A M.X m) ⊗ₘ
        modTensorπ A (symPowMod A M'.X n) (symPowMod A M.X n)) ≫
        (β_ (chainStage A M M' m) (chainStage A M M' n)).hom =
      (β_ (symPow A M'.X (m + 1) ⊗ symPow A M.X (m + 1))
          (symPow A M'.X (n + 1) ⊗ symPow A M.X (n + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X n) (symPowMod A M.X n) ⊗ₘ
          modTensorπ A (symPowMod A M'.X m) (symPowMod A M.X m)) :=
    BraidedCategory.braiding_naturality _ _
  refine (cancel_epi
    (modTensorπ A (symPowMod A M'.X m) (symPowMod A M.X m) ⊗ₘ
      modTensorπ A (symPowMod A M'.X n) (symPowMod A M.X n))).mp ?_
  have e1 : (modTensorπ A (symPowMod A M'.X m)
          (symPowMod A M.X m) ⊗ₘ
        modTensorπ A (symPowMod A M'.X n) (symPowMod A M.X n)) ≫
        ((β_ (chainStage A M M' m) (chainStage A M M' n)).hom ≫
          chainMul A M M' n m ≫ chainStageCast A M M' h₀) =
      (β_ (symPow A M'.X (m + 1) ⊗ symPow A M.X (m + 1))
          (symPow A M'.X (n + 1) ⊗ symPow A M.X (n + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X n) (symPowMod A M.X n) ⊗ₘ
          modTensorπ A (symPowMod A M'.X m) (symPowMod A M.X m)) ≫
        chainMul A M M' n m ≫ chainStageCast A M M' h₀ :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ (chainMul A M M' n m ≫
        chainStageCast A M M' h₀)) hβ).trans
        (Category.assoc _ _ _))
  have e2 : (β_ (symPow A M'.X (m + 1) ⊗ symPow A M.X (m + 1))
          (symPow A M'.X (n + 1) ⊗ symPow A M.X (n + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X n) (symPowMod A M.X n) ⊗ₘ
          modTensorπ A (symPowMod A M'.X m) (symPowMod A M.X m)) ≫
        chainMul A M M' n m ≫ chainStageCast A M M' h₀ =
      (β_ (symPow A M'.X (m + 1) ⊗ symPow A M.X (m + 1))
          (symPow A M'.X (n + 1) ⊗ symPow A M.X (n + 1))).hom ≫
        tensorμ (symPow A M'.X (n + 1)) (symPow A M.X (n + 1))
          (symPow A M'.X (m + 1)) (symPow A M.X (m + 1)) ≫
        (symMul A M'.X (n + 1) (m + 1) ⊗ₘ
          symMul A M.X (n + 1) (m + 1)) ≫
        (modTensorπ A (symPowMod A M'.X (n + 1 + m))
          (symPowMod A M.X (n + 1 + m)) ≫
          chainStageCast A M M' h₀) :=
    congrArg (CategoryStruct.comp _)
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ chainStageCast A M M' h₀)
          (tensorHom_π_chainMul A M M' n m)).trans
          ((Category.assoc _ _ _).trans
            (congrArg (CategoryStruct.comp _)
              (Category.assoc _ _ _)))))
  have e3 : (β_ (symPow A M'.X (m + 1) ⊗ symPow A M.X (m + 1))
          (symPow A M'.X (n + 1) ⊗ symPow A M.X (n + 1))).hom ≫
        tensorμ (symPow A M'.X (n + 1)) (symPow A M.X (n + 1))
          (symPow A M'.X (m + 1)) (symPow A M.X (m + 1)) ≫
        (symMul A M'.X (n + 1) (m + 1) ⊗ₘ
          symMul A M.X (n + 1) (m + 1)) ≫
        (modTensorπ A (symPowMod A M'.X (n + 1 + m))
          (symPowMod A M.X (n + 1 + m)) ≫
          chainStageCast A M M' h₀) =
      (β_ (symPow A M'.X (m + 1) ⊗ symPow A M.X (m + 1))
          (symPow A M'.X (n + 1) ⊗ symPow A M.X (n + 1))).hom ≫
        tensorμ (symPow A M'.X (n + 1)) (symPow A M.X (n + 1))
          (symPow A M'.X (m + 1)) (symPow A M.X (m + 1)) ≫
        (symMul A M'.X (n + 1) (m + 1) ⊗ₘ
          symMul A M.X (n + 1) (m + 1)) ≫
        ((symPowCast A M'.X (congrArg Nat.succ h₀) ⊗ₘ
          symPowCast A M.X (congrArg Nat.succ h₀)) ≫
          modTensorπ A (symPowMod A M'.X (m + 1 + n))
            (symPowMod A M.X (m + 1 + n))) :=
    congrArg (CategoryStruct.comp _)
      (congrArg (CategoryStruct.comp _)
        (congrArg (CategoryStruct.comp _)
          (modTensorπ_chainStageCast A M M' h₀)))
  have e4 : (β_ (symPow A M'.X (m + 1) ⊗ symPow A M.X (m + 1))
          (symPow A M'.X (n + 1) ⊗ symPow A M.X (n + 1))).hom ≫
        tensorμ (symPow A M'.X (n + 1)) (symPow A M.X (n + 1))
          (symPow A M'.X (m + 1)) (symPow A M.X (m + 1)) ≫
        (symMul A M'.X (n + 1) (m + 1) ⊗ₘ
          symMul A M.X (n + 1) (m + 1)) ≫
        ((symPowCast A M'.X (congrArg Nat.succ h₀) ⊗ₘ
          symPowCast A M.X (congrArg Nat.succ h₀)) ≫
          modTensorπ A (symPowMod A M'.X (m + 1 + n))
            (symPowMod A M.X (m + 1 + n))) =
      tensorμ (symPow A M'.X (m + 1)) (symPow A M.X (m + 1))
          (symPow A M'.X (n + 1)) (symPow A M.X (n + 1)) ≫
        ((β_ (symPow A M'.X (m + 1)) (symPow A M'.X (n + 1))).hom
          ⊗ₘ (β_ (symPow A M.X (m + 1))
            (symPow A M.X (n + 1))).hom) ≫
        (symMul A M'.X (n + 1) (m + 1) ⊗ₘ
          symMul A M.X (n + 1) (m + 1)) ≫
        ((symPowCast A M'.X (congrArg Nat.succ h₀) ⊗ₘ
          symPowCast A M.X (congrArg Nat.succ h₀)) ≫
          modTensorπ A (symPowMod A M'.X (m + 1 + n))
            (symPowMod A M.X (m + 1 + n))) :=
    tensorμ_braiding_assoc _ _ _ _ _
  have e5 : tensorμ (symPow A M'.X (m + 1)) (symPow A M.X (m + 1))
          (symPow A M'.X (n + 1)) (symPow A M.X (n + 1)) ≫
        ((β_ (symPow A M'.X (m + 1)) (symPow A M'.X (n + 1))).hom
          ⊗ₘ (β_ (symPow A M.X (m + 1))
            (symPow A M.X (n + 1))).hom) ≫
        (symMul A M'.X (n + 1) (m + 1) ⊗ₘ
          symMul A M.X (n + 1) (m + 1)) ≫
        ((symPowCast A M'.X (congrArg Nat.succ h₀) ⊗ₘ
          symPowCast A M.X (congrArg Nat.succ h₀)) ≫
          modTensorπ A (symPowMod A M'.X (m + 1 + n))
            (symPowMod A M.X (m + 1 + n))) =
      tensorμ (symPow A M'.X (m + 1)) (symPow A M.X (m + 1))
          (symPow A M'.X (n + 1)) (symPow A M.X (n + 1)) ≫
        (((β_ (symPow A M'.X (m + 1))
            (symPow A M'.X (n + 1))).hom ≫
            symMul A M'.X (n + 1) (m + 1)) ⊗ₘ
          ((β_ (symPow A M.X (m + 1))
            (symPow A M.X (n + 1))).hom ≫
            symMul A M.X (n + 1) (m + 1))) ≫
        ((symPowCast A M'.X (congrArg Nat.succ h₀) ⊗ₘ
          symPowCast A M.X (congrArg Nat.succ h₀)) ≫
          modTensorπ A (symPowMod A M'.X (m + 1 + n))
            (symPowMod A M.X (m + 1 + n))) :=
    congrArg (CategoryStruct.comp _)
      (MonoidalCategory.tensorHom_comp_tensorHom_assoc _ _ _ _ _)
  have e6 : tensorμ (symPow A M'.X (m + 1)) (symPow A M.X (m + 1))
          (symPow A M'.X (n + 1)) (symPow A M.X (n + 1)) ≫
        (((β_ (symPow A M'.X (m + 1))
            (symPow A M'.X (n + 1))).hom ≫
            symMul A M'.X (n + 1) (m + 1)) ⊗ₘ
          ((β_ (symPow A M.X (m + 1))
            (symPow A M.X (n + 1))).hom ≫
            symMul A M.X (n + 1) (m + 1))) ≫
        ((symPowCast A M'.X (congrArg Nat.succ h₀) ⊗ₘ
          symPowCast A M.X (congrArg Nat.succ h₀)) ≫
          modTensorπ A (symPowMod A M'.X (m + 1 + n))
            (symPowMod A M.X (m + 1 + n))) =
      tensorμ (symPow A M'.X (m + 1)) (symPow A M.X (m + 1))
          (symPow A M'.X (n + 1)) (symPow A M.X (n + 1)) ≫
        ((((β_ (symPow A M'.X (m + 1))
            (symPow A M'.X (n + 1))).hom ≫
            symMul A M'.X (n + 1) (m + 1)) ≫
            symPowCast A M'.X (congrArg Nat.succ h₀)) ⊗ₘ
          (((β_ (symPow A M.X (m + 1))
            (symPow A M.X (n + 1))).hom ≫
            symMul A M.X (n + 1) (m + 1)) ≫
            symPowCast A M.X (congrArg Nat.succ h₀))) ≫
        modTensorπ A (symPowMod A M'.X (m + 1 + n))
          (symPowMod A M.X (m + 1 + n)) :=
    congrArg (CategoryStruct.comp _)
      (MonoidalCategory.tensorHom_comp_tensorHom_assoc _ _ _ _ _)
  have e7 : tensorμ (symPow A M'.X (m + 1)) (symPow A M.X (m + 1))
          (symPow A M'.X (n + 1)) (symPow A M.X (n + 1)) ≫
        ((((β_ (symPow A M'.X (m + 1))
            (symPow A M'.X (n + 1))).hom ≫
            symMul A M'.X (n + 1) (m + 1)) ≫
            symPowCast A M'.X (congrArg Nat.succ h₀)) ⊗ₘ
          (((β_ (symPow A M.X (m + 1))
            (symPow A M.X (n + 1))).hom ≫
            symMul A M.X (n + 1) (m + 1)) ≫
            symPowCast A M.X (congrArg Nat.succ h₀))) ≫
        modTensorπ A (symPowMod A M'.X (m + 1 + n))
          (symPowMod A M.X (m + 1 + n)) =
      tensorμ (symPow A M'.X (m + 1)) (symPow A M.X (m + 1))
          (symPow A M'.X (n + 1)) (symPow A M.X (n + 1)) ≫
        (symMul A M'.X (m + 1) (n + 1) ⊗ₘ
          symMul A M.X (m + 1) (n + 1)) ≫
        modTensorπ A (symPowMod A M'.X (m + 1 + n))
          (symPowMod A M.X (m + 1 + n)) :=
    congrArg (CategoryStruct.comp _)
      (congrArg (fun t => t ≫
        modTensorπ A (symPowMod A M'.X (m + 1 + n))
          (symPowMod A M.X (m + 1 + n)))
        (congrArg₂ (· ⊗ₘ ·) hfacL₁ hfacL₂))
  exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans
    (e6.trans (e7.trans (tensorHom_π_chainMul A M M' m n).symm))))))

end ChainComm

/-! ## Tensor surgery and the associativity core -/

section TensorSurgery

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

/-- **The coherence core of associativity**: two interchanged pair
multiplications reassociate through `tensorμ` whenever each factor
satisfies the corresponding one-object associativity law. -/
private theorem chainMulAssoc_core
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    {a₁ a₂ c₁ c₂ e₁ e₂ x₁ x₂ z₁ z₂
      t₁ t₂ Z : D}
    {u₁ : a₁ ⊗ c₁ ⟶ x₁} {u₂ : a₂ ⊗ c₂ ⟶ x₂}
    {w₁ : c₁ ⊗ e₁ ⟶ z₁} {w₂ : c₂ ⊗ e₂ ⟶ z₂}
    {v₁ : x₁ ⊗ e₁ ⟶ t₁} {v₂ : x₂ ⊗ e₂ ⟶ t₂}
    {v'₁ : a₁ ⊗ z₁ ⟶ t₁} {v'₂ : a₂ ⊗ z₂ ⟶ t₂}
    (h₁ : (u₁ ▷ e₁) ≫ v₁ =
      (α_ a₁ c₁ e₁).hom ≫ (a₁ ◁ w₁) ≫ v'₁)
    (h₂ : (u₂ ▷ e₂) ≫ v₂ =
      (α_ a₂ c₂ e₂).hom ≫ (a₂ ◁ w₂) ≫ v'₂)
    (out : t₁ ⊗ t₂ ⟶ Z) :
    ((tensorμ a₁ a₂ c₁ c₂ ≫ (u₁ ⊗ₘ u₂)) ▷ (e₁ ⊗ e₂)) ≫
        tensorμ x₁ x₂ e₁ e₂ ≫ (v₁ ⊗ₘ v₂) ≫ out =
      (α_ (a₁ ⊗ a₂) (c₁ ⊗ c₂) (e₁ ⊗ e₂)).hom ≫
        ((a₁ ⊗ a₂) ◁ (tensorμ c₁ c₂ e₁ e₂ ≫ (w₁ ⊗ₘ w₂))) ≫
        tensorμ a₁ a₂ z₁ z₂ ≫ (v'₁ ⊗ₘ v'₂) ≫ out := by
  conv_lhs => rw [comp_whiskerRight, Category.assoc,
    tensorμ_natural_left_assoc,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, h₁, h₂,
    ← MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    tensor_associativity_assoc]
  conv_rhs => rw [MonoidalCategory.whiskerLeft_comp,
    Category.assoc, tensorμ_natural_right_assoc,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc]

end TensorSurgery

/-! ## Associativity of the chain multiplication -/

section ChainAssoc

private theorem chainMul_assoc_left
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (m n p : ℕ) :
    ((modTensorπ A (symPowMod A M'.X m)
          (symPowMod A M.X m) ⊗ₘ
        modTensorπ A (symPowMod A M'.X n) (symPowMod A M.X n)) ⊗ₘ
        modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X p)) ≫
        ((chainMul A M M' m n ▷ chainStage A M M' p) ≫
          chainMul A M M' (m + 1 + n) p ≫
          chainStageCast A M M'
            (rfl : m + 1 + n + 1 + p = m + 1 + n + 1 + p)) =
    ((tensorμ (symPow A M'.X (m + 1)) (symPow A M.X (m + 1))
          (symPow A M'.X (n + 1)) (symPow A M.X (n + 1)) ≫
        (symMul A M'.X (m + 1) (n + 1) ⊗ₘ
          symMul A M.X (m + 1) (n + 1))) ▷
        (symPow A M'.X (p + 1) ⊗ symPow A M.X (p + 1))) ≫
        tensorμ (symPow A M'.X (m + 1 + n + 1))
          (symPow A M.X (m + 1 + n + 1))
          (symPow A M'.X (p + 1)) (symPow A M.X (p + 1)) ≫
        (symMul A M'.X (m + 1 + n + 1) (p + 1) ⊗ₘ
          symMul A M.X (m + 1 + n + 1) (p + 1)) ≫
        modTensorπ A (symPowMod A M'.X (m + 1 + n + 1 + p))
          (symPowMod A M.X (m + 1 + n + 1 + p)) := by
  have hK : chainMul A M M' (m + 1 + n) p ≫
      chainStageCast A M M'
        (rfl : m + 1 + n + 1 + p = m + 1 + n + 1 + p) =
      chainMul A M M' (m + 1 + n) p := by
    rw [chainStageCast_rfl, Category.comp_id]
  have l1 : ((modTensorπ A (symPowMod A M'.X m)
          (symPowMod A M.X m) ⊗ₘ
        modTensorπ A (symPowMod A M'.X n) (symPowMod A M.X n)) ⊗ₘ
        modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X p)) ≫
        ((chainMul A M M' m n ▷ chainStage A M M' p) ≫
          chainMul A M M' (m + 1 + n) p ≫
          chainStageCast A M M'
            (rfl : m + 1 + n + 1 + p = m + 1 + n + 1 + p)) =
      ((modTensorπ A (symPowMod A M'.X m) (symPowMod A M.X m) ⊗ₘ
        modTensorπ A (symPowMod A M'.X n) (symPowMod A M.X n)) ⊗ₘ
        modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X p)) ≫
        ((chainMul A M M' m n ▷ chainStage A M M' p) ≫
          chainMul A M M' (m + 1 + n) p) :=
    congrArg (CategoryStruct.comp _)
      (congrArg (CategoryStruct.comp _) hK)
  have l2 : ((modTensorπ A (symPowMod A M'.X m)
          (symPowMod A M.X m) ⊗ₘ
        modTensorπ A (symPowMod A M'.X n) (symPowMod A M.X n)) ⊗ₘ
        modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X p)) ≫
        ((chainMul A M M' m n ▷ chainStage A M M' p) ≫
          chainMul A M M' (m + 1 + n) p) =
      (((modTensorπ A (symPowMod A M'.X m) (symPowMod A M.X m) ⊗ₘ
        modTensorπ A (symPowMod A M'.X n) (symPowMod A M.X n)) ≫
        chainMul A M M' m n) ⊗ₘ
        modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X p)) ≫
        chainMul A M M' (m + 1 + n) p :=
    tensorHom_whiskerRight_comp _ _ _ _
  have l3 : (((modTensorπ A (symPowMod A M'.X m)
          (symPowMod A M.X m) ⊗ₘ
        modTensorπ A (symPowMod A M'.X n) (symPowMod A M.X n)) ≫
        chainMul A M M' m n) ⊗ₘ
        modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X p)) ≫
        chainMul A M M' (m + 1 + n) p =
      ((tensorμ (symPow A M'.X (m + 1)) (symPow A M.X (m + 1))
          (symPow A M'.X (n + 1)) (symPow A M.X (n + 1)) ≫
        (symMul A M'.X (m + 1) (n + 1) ⊗ₘ
          symMul A M.X (m + 1) (n + 1)) ≫
        modTensorπ A (symPowMod A M'.X (m + 1 + n))
          (symPowMod A M.X (m + 1 + n))) ⊗ₘ
        modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X p)) ≫
        chainMul A M M' (m + 1 + n) p :=
    congrArg (fun t => (t ⊗ₘ
      modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X p)) ≫
      chainMul A M M' (m + 1 + n) p)
      (tensorHom_π_chainMul A M M' m n)
  have l4 : ((tensorμ (symPow A M'.X (m + 1)) (symPow A M.X (m + 1))
          (symPow A M'.X (n + 1)) (symPow A M.X (n + 1)) ≫
        (symMul A M'.X (m + 1) (n + 1) ⊗ₘ
          symMul A M.X (m + 1) (n + 1)) ≫
        modTensorπ A (symPowMod A M'.X (m + 1 + n))
          (symPowMod A M.X (m + 1 + n))) ⊗ₘ
        modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X p)) ≫
        chainMul A M M' (m + 1 + n) p =
      (((tensorμ (symPow A M'.X (m + 1)) (symPow A M.X (m + 1))
          (symPow A M'.X (n + 1)) (symPow A M.X (n + 1)) ≫
        (symMul A M'.X (m + 1) (n + 1) ⊗ₘ
          symMul A M.X (m + 1) (n + 1))) ≫
        modTensorπ A (symPowMod A M'.X (m + 1 + n))
          (symPowMod A M.X (m + 1 + n))) ⊗ₘ
        modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X p)) ≫
        chainMul A M M' (m + 1 + n) p :=
    congrArg (fun t => (t ⊗ₘ
      modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X p)) ≫
      chainMul A M M' (m + 1 + n) p)
      (Category.assoc _ _ _).symm
  have l5 : (((tensorμ (symPow A M'.X (m + 1))
          (symPow A M.X (m + 1))
          (symPow A M'.X (n + 1)) (symPow A M.X (n + 1)) ≫
        (symMul A M'.X (m + 1) (n + 1) ⊗ₘ
          symMul A M.X (m + 1) (n + 1))) ≫
        modTensorπ A (symPowMod A M'.X (m + 1 + n))
          (symPowMod A M.X (m + 1 + n))) ⊗ₘ
        modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X p)) ≫
        chainMul A M M' (m + 1 + n) p =
      ((tensorμ (symPow A M'.X (m + 1)) (symPow A M.X (m + 1))
          (symPow A M'.X (n + 1)) (symPow A M.X (n + 1)) ≫
        (symMul A M'.X (m + 1) (n + 1) ⊗ₘ
          symMul A M.X (m + 1) (n + 1))) ▷
        (symPow A M'.X (p + 1) ⊗ symPow A M.X (p + 1))) ≫
        (modTensorπ A (symPowMod A M'.X (m + 1 + n))
          (symPowMod A M.X (m + 1 + n)) ⊗ₘ
          modTensorπ A (symPowMod A M'.X p)
            (symPowMod A M.X p)) ≫
        chainMul A M M' (m + 1 + n) p :=
    compTensorHom_whiskerRight_split _ _ _ _
  have l6 : ((tensorμ (symPow A M'.X (m + 1)) (symPow A M.X (m + 1))
          (symPow A M'.X (n + 1)) (symPow A M.X (n + 1)) ≫
        (symMul A M'.X (m + 1) (n + 1) ⊗ₘ
          symMul A M.X (m + 1) (n + 1))) ▷
        (symPow A M'.X (p + 1) ⊗ symPow A M.X (p + 1))) ≫
        (modTensorπ A (symPowMod A M'.X (m + 1 + n))
          (symPowMod A M.X (m + 1 + n)) ⊗ₘ
          modTensorπ A (symPowMod A M'.X p)
            (symPowMod A M.X p)) ≫
        chainMul A M M' (m + 1 + n) p =
      ((tensorμ (symPow A M'.X (m + 1)) (symPow A M.X (m + 1))
          (symPow A M'.X (n + 1)) (symPow A M.X (n + 1)) ≫
        (symMul A M'.X (m + 1) (n + 1) ⊗ₘ
          symMul A M.X (m + 1) (n + 1))) ▷
        (symPow A M'.X (p + 1) ⊗ symPow A M.X (p + 1))) ≫
        tensorμ (symPow A M'.X (m + 1 + n + 1))
          (symPow A M.X (m + 1 + n + 1))
          (symPow A M'.X (p + 1)) (symPow A M.X (p + 1)) ≫
        (symMul A M'.X (m + 1 + n + 1) (p + 1) ⊗ₘ
          symMul A M.X (m + 1 + n + 1) (p + 1)) ≫
        modTensorπ A (symPowMod A M'.X (m + 1 + n + 1 + p))
          (symPowMod A M.X (m + 1 + n + 1 + p)) :=
    congrArg (CategoryStruct.comp _)
      (tensorHom_π_chainMul A M M' (m + 1 + n) p)
  -- Right bridge: from the reassociated side to the instantiated
  -- core's right-hand side.
  exact l1.trans (l2.trans (l3.trans (l4.trans (l5.trans (l6)))))

private theorem chainMul_assoc_rightTail
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (m n p : ℕ)
    (h₂ : m + 1 + (n + 1 + p) = m + 1 + n + 1 + p) :
    (modTensorπ A (symPowMod A M'.X m)
          (symPowMod A M.X m) ⊗ₘ
        modTensorπ A (symPowMod A M'.X (n + 1 + p))
          (symPowMod A M.X (n + 1 + p))) ≫
        (chainMul A M M' m (n + 1 + p) ≫
          chainStageCast A M M' h₂) =
    tensorμ (symPow A M'.X (m + 1)) (symPow A M.X (m + 1))
          (symPow A M'.X (n + 1 + p + 1))
          (symPow A M.X (n + 1 + p + 1)) ≫
        ((symMul A M'.X (m + 1) (n + 1 + p + 1) ≫
          symPowCast A M'.X (congrArg Nat.succ h₂)) ⊗ₘ
          (symMul A M.X (m + 1) (n + 1 + p + 1) ≫
            symPowCast A M.X (congrArg Nat.succ h₂))) ≫
        modTensorπ A (symPowMod A M'.X (m + 1 + n + 1 + p))
          (symPowMod A M.X (m + 1 + n + 1 + p)) := by
  have r6 : (modTensorπ A (symPowMod A M'.X m)
          (symPowMod A M.X m) ⊗ₘ
        modTensorπ A (symPowMod A M'.X (n + 1 + p))
          (symPowMod A M.X (n + 1 + p))) ≫
        (chainMul A M M' m (n + 1 + p) ≫
          chainStageCast A M M' h₂) =
      tensorμ (symPow A M'.X (m + 1)) (symPow A M.X (m + 1))
          (symPow A M'.X (n + 1 + p + 1))
          (symPow A M.X (n + 1 + p + 1)) ≫
        (symMul A M'.X (m + 1) (n + 1 + p + 1) ⊗ₘ
          symMul A M.X (m + 1) (n + 1 + p + 1)) ≫
        (modTensorπ A (symPowMod A M'.X (m + 1 + (n + 1 + p)))
          (symPowMod A M.X (m + 1 + (n + 1 + p))) ≫
          chainStageCast A M M' h₂) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ chainStageCast A M M' h₂)
        (tensorHom_π_chainMul A M M' m (n + 1 + p))).trans
        ((Category.assoc _ _ _).trans
          (congrArg (CategoryStruct.comp _)
            (Category.assoc _ _ _))))
  have r7 : modTensorπ A (symPowMod A M'.X (m + 1 + (n + 1 + p)))
        (symPowMod A M.X (m + 1 + (n + 1 + p))) ≫
        chainStageCast A M M' h₂ =
      (symPowCast A M'.X (congrArg Nat.succ h₂) ⊗ₘ
        symPowCast A M.X (congrArg Nat.succ h₂)) ≫
        modTensorπ A (symPowMod A M'.X (m + 1 + n + 1 + p))
          (symPowMod A M.X (m + 1 + n + 1 + p)) :=
    modTensorπ_chainStageCast A M M' h₂
  have r8 : (symMul A M'.X (m + 1) (n + 1 + p + 1) ⊗ₘ
        symMul A M.X (m + 1) (n + 1 + p + 1)) ≫
        ((symPowCast A M'.X (congrArg Nat.succ h₂) ⊗ₘ
          symPowCast A M.X (congrArg Nat.succ h₂)) ≫
          modTensorπ A (symPowMod A M'.X (m + 1 + n + 1 + p))
            (symPowMod A M.X (m + 1 + n + 1 + p))) =
      ((symMul A M'.X (m + 1) (n + 1 + p + 1) ≫
        symPowCast A M'.X (congrArg Nat.succ h₂)) ⊗ₘ
        (symMul A M.X (m + 1) (n + 1 + p + 1) ≫
          symPowCast A M.X (congrArg Nat.succ h₂))) ≫
        modTensorπ A (symPowMod A M'.X (m + 1 + n + 1 + p))
          (symPowMod A M.X (m + 1 + n + 1 + p)) :=
    MonoidalCategory.tensorHom_comp_tensorHom_assoc _ _ _ _ _
  have rTail : (modTensorπ A (symPowMod A M'.X m)
          (symPowMod A M.X m) ⊗ₘ
        modTensorπ A (symPowMod A M'.X (n + 1 + p))
          (symPowMod A M.X (n + 1 + p))) ≫
        (chainMul A M M' m (n + 1 + p) ≫
          chainStageCast A M M' h₂) =
      tensorμ (symPow A M'.X (m + 1)) (symPow A M.X (m + 1))
          (symPow A M'.X (n + 1 + p + 1))
          (symPow A M.X (n + 1 + p + 1)) ≫
        ((symMul A M'.X (m + 1) (n + 1 + p + 1) ≫
          symPowCast A M'.X (congrArg Nat.succ h₂)) ⊗ₘ
          (symMul A M.X (m + 1) (n + 1 + p + 1) ≫
            symPowCast A M.X (congrArg Nat.succ h₂))) ≫
        modTensorπ A (symPowMod A M'.X (m + 1 + n + 1 + p))
          (symPowMod A M.X (m + 1 + n + 1 + p)) :=
    r6.trans ((congrArg (CategoryStruct.comp _)
      (congrArg (CategoryStruct.comp _) r7)).trans
      (congrArg (CategoryStruct.comp _) r8))
  exact rTail

/-- **Associativity of the chain multiplication**, up to the stage
transports onto the common arity `m + 1 + n + 1 + p`. -/
theorem chainMul_assoc
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (m n p : ℕ) :
    (chainMul A M M' m n ▷ chainStage A M M' p) ≫
        chainMul A M M' (m + 1 + n) p ≫
        chainStageCast A M M'
          (by omega : m + 1 + n + 1 + p = m + 1 + n + 1 + p) =
      (α_ (chainStage A M M' m) (chainStage A M M' n)
          (chainStage A M M' p)).hom ≫
        (chainStage A M M' m ◁ chainMul A M M' n p) ≫
        chainMul A M M' m (n + 1 + p) ≫
        chainStageCast A M M'
          (by omega : m + 1 + (n + 1 + p) = m + 1 + n + 1 + p) := by
  have h₂ : m + 1 + (n + 1 + p) = m + 1 + n + 1 + p := by omega
  have hcore := chainMulAssoc_core
    (symMul_assoc A M'.X (m + 1) (n + 1) (p + 1))
    (symMul_assoc A M.X (m + 1) (n + 1) (p + 1))
    (modTensorπ A (symPowMod A M'.X (m + 1 + n + 1 + p))
      (symPowMod A M.X (m + 1 + n + 1 + p)))
  refine (cancel_epi
    ((modTensorπ A (symPowMod A M'.X m) (symPowMod A M.X m) ⊗ₘ
        modTensorπ A (symPowMod A M'.X n) (symPowMod A M.X n)) ⊗ₘ
      modTensorπ A (symPowMod A M'.X p)
        (symPowMod A M.X p))).mp ?_
  -- Left bridge: from the whiskered chain multiplication to the
  -- instantiated core's left-hand side.
  have hleft := chainMul_assoc_left A M M' m n p
  have hα : ((modTensorπ A (symPowMod A M'.X m)
          (symPowMod A M.X m) ⊗ₘ
        modTensorπ A (symPowMod A M'.X n) (symPowMod A M.X n)) ⊗ₘ
        modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X p)) ≫
        (α_ (chainStage A M M' m) (chainStage A M M' n)
          (chainStage A M M' p)).hom =
      (α_ (symPow A M'.X (m + 1) ⊗ symPow A M.X (m + 1))
          (symPow A M'.X (n + 1) ⊗ symPow A M.X (n + 1))
          (symPow A M'.X (p + 1) ⊗ symPow A M.X (p + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X m) (symPowMod A M.X m) ⊗ₘ
          (modTensorπ A (symPowMod A M'.X n)
            (symPowMod A M.X n) ⊗ₘ
            modTensorπ A (symPowMod A M'.X p)
              (symPowMod A M.X p))) :=
    associator_naturality _ _ _
  have r1 : ((modTensorπ A (symPowMod A M'.X m)
          (symPowMod A M.X m) ⊗ₘ
        modTensorπ A (symPowMod A M'.X n) (symPowMod A M.X n)) ⊗ₘ
        modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X p)) ≫
        ((α_ (chainStage A M M' m) (chainStage A M M' n)
          (chainStage A M M' p)).hom ≫
          (chainStage A M M' m ◁ chainMul A M M' n p) ≫
          chainMul A M M' m (n + 1 + p) ≫
          chainStageCast A M M' h₂) =
      (α_ (symPow A M'.X (m + 1) ⊗ symPow A M.X (m + 1))
          (symPow A M'.X (n + 1) ⊗ symPow A M.X (n + 1))
          (symPow A M'.X (p + 1) ⊗ symPow A M.X (p + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X m) (symPowMod A M.X m) ⊗ₘ
          (modTensorπ A (symPowMod A M'.X n)
            (symPowMod A M.X n) ⊗ₘ
            modTensorπ A (symPowMod A M'.X p)
              (symPowMod A M.X p))) ≫
        ((chainStage A M M' m ◁ chainMul A M M' n p) ≫
          chainMul A M M' m (n + 1 + p) ≫
          chainStageCast A M M' h₂) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫
        ((chainStage A M M' m ◁ chainMul A M M' n p) ≫
          chainMul A M M' m (n + 1 + p) ≫
          chainStageCast A M M' h₂)) hα).trans
        (Category.assoc _ _ _))
  have r2 : (α_ (symPow A M'.X (m + 1) ⊗ symPow A M.X (m + 1))
          (symPow A M'.X (n + 1) ⊗ symPow A M.X (n + 1))
          (symPow A M'.X (p + 1) ⊗ symPow A M.X (p + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X m) (symPowMod A M.X m) ⊗ₘ
          (modTensorπ A (symPowMod A M'.X n)
            (symPowMod A M.X n) ⊗ₘ
            modTensorπ A (symPowMod A M'.X p)
              (symPowMod A M.X p))) ≫
        ((chainStage A M M' m ◁ chainMul A M M' n p) ≫
          chainMul A M M' m (n + 1 + p) ≫
          chainStageCast A M M' h₂) =
      (α_ (symPow A M'.X (m + 1) ⊗ symPow A M.X (m + 1))
          (symPow A M'.X (n + 1) ⊗ symPow A M.X (n + 1))
          (symPow A M'.X (p + 1) ⊗ symPow A M.X (p + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X m) (symPowMod A M.X m) ⊗ₘ
          ((modTensorπ A (symPowMod A M'.X n)
            (symPowMod A M.X n) ⊗ₘ
            modTensorπ A (symPowMod A M'.X p)
              (symPowMod A M.X p)) ≫
            chainMul A M M' n p)) ≫
        (chainMul A M M' m (n + 1 + p) ≫
          chainStageCast A M M' h₂) :=
    congrArg (CategoryStruct.comp _)
      (tensorHom_whiskerLeft_comp _ _ _ _)
  have r3 : (α_ (symPow A M'.X (m + 1) ⊗ symPow A M.X (m + 1))
          (symPow A M'.X (n + 1) ⊗ symPow A M.X (n + 1))
          (symPow A M'.X (p + 1) ⊗ symPow A M.X (p + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X m) (symPowMod A M.X m) ⊗ₘ
          ((modTensorπ A (symPowMod A M'.X n)
            (symPowMod A M.X n) ⊗ₘ
            modTensorπ A (symPowMod A M'.X p)
              (symPowMod A M.X p)) ≫
            chainMul A M M' n p)) ≫
        (chainMul A M M' m (n + 1 + p) ≫
          chainStageCast A M M' h₂) =
      (α_ (symPow A M'.X (m + 1) ⊗ symPow A M.X (m + 1))
          (symPow A M'.X (n + 1) ⊗ symPow A M.X (n + 1))
          (symPow A M'.X (p + 1) ⊗ symPow A M.X (p + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X m) (symPowMod A M.X m) ⊗ₘ
          (tensorμ (symPow A M'.X (n + 1)) (symPow A M.X (n + 1))
            (symPow A M'.X (p + 1)) (symPow A M.X (p + 1)) ≫
            (symMul A M'.X (n + 1) (p + 1) ⊗ₘ
              symMul A M.X (n + 1) (p + 1)) ≫
            modTensorπ A (symPowMod A M'.X (n + 1 + p))
              (symPowMod A M.X (n + 1 + p)))) ≫
        (chainMul A M M' m (n + 1 + p) ≫
          chainStageCast A M M' h₂) :=
    congrArg (fun t =>
      (α_ (symPow A M'.X (m + 1) ⊗ symPow A M.X (m + 1))
          (symPow A M'.X (n + 1) ⊗ symPow A M.X (n + 1))
          (symPow A M'.X (p + 1) ⊗ symPow A M.X (p + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X m)
          (symPowMod A M.X m) ⊗ₘ t) ≫
        (chainMul A M M' m (n + 1 + p) ≫
          chainStageCast A M M' h₂))
      (tensorHom_π_chainMul A M M' n p)
  have r4 : (α_ (symPow A M'.X (m + 1) ⊗ symPow A M.X (m + 1))
          (symPow A M'.X (n + 1) ⊗ symPow A M.X (n + 1))
          (symPow A M'.X (p + 1) ⊗ symPow A M.X (p + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X m) (symPowMod A M.X m) ⊗ₘ
          (tensorμ (symPow A M'.X (n + 1)) (symPow A M.X (n + 1))
            (symPow A M'.X (p + 1)) (symPow A M.X (p + 1)) ≫
            (symMul A M'.X (n + 1) (p + 1) ⊗ₘ
              symMul A M.X (n + 1) (p + 1)) ≫
            modTensorπ A (symPowMod A M'.X (n + 1 + p))
              (symPowMod A M.X (n + 1 + p)))) ≫
        (chainMul A M M' m (n + 1 + p) ≫
          chainStageCast A M M' h₂) =
      (α_ (symPow A M'.X (m + 1) ⊗ symPow A M.X (m + 1))
          (symPow A M'.X (n + 1) ⊗ symPow A M.X (n + 1))
          (symPow A M'.X (p + 1) ⊗ symPow A M.X (p + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X m) (symPowMod A M.X m) ⊗ₘ
          ((tensorμ (symPow A M'.X (n + 1)) (symPow A M.X (n + 1))
            (symPow A M'.X (p + 1)) (symPow A M.X (p + 1)) ≫
            (symMul A M'.X (n + 1) (p + 1) ⊗ₘ
              symMul A M.X (n + 1) (p + 1))) ≫
            modTensorπ A (symPowMod A M'.X (n + 1 + p))
              (symPowMod A M.X (n + 1 + p)))) ≫
        (chainMul A M M' m (n + 1 + p) ≫
          chainStageCast A M M' h₂) :=
    congrArg (fun t =>
      (α_ (symPow A M'.X (m + 1) ⊗ symPow A M.X (m + 1))
          (symPow A M'.X (n + 1) ⊗ symPow A M.X (n + 1))
          (symPow A M'.X (p + 1) ⊗ symPow A M.X (p + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X m)
          (symPowMod A M.X m) ⊗ₘ t) ≫
        (chainMul A M M' m (n + 1 + p) ≫
          chainStageCast A M M' h₂))
      (Category.assoc _ _ _).symm
  have r5 : (α_ (symPow A M'.X (m + 1) ⊗ symPow A M.X (m + 1))
          (symPow A M'.X (n + 1) ⊗ symPow A M.X (n + 1))
          (symPow A M'.X (p + 1) ⊗ symPow A M.X (p + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X m) (symPowMod A M.X m) ⊗ₘ
          ((tensorμ (symPow A M'.X (n + 1)) (symPow A M.X (n + 1))
            (symPow A M'.X (p + 1)) (symPow A M.X (p + 1)) ≫
            (symMul A M'.X (n + 1) (p + 1) ⊗ₘ
              symMul A M.X (n + 1) (p + 1))) ≫
            modTensorπ A (symPowMod A M'.X (n + 1 + p))
              (symPowMod A M.X (n + 1 + p)))) ≫
        (chainMul A M M' m (n + 1 + p) ≫
          chainStageCast A M M' h₂) =
      (α_ (symPow A M'.X (m + 1) ⊗ symPow A M.X (m + 1))
          (symPow A M'.X (n + 1) ⊗ symPow A M.X (n + 1))
          (symPow A M'.X (p + 1) ⊗ symPow A M.X (p + 1))).hom ≫
        ((symPow A M'.X (m + 1) ⊗ symPow A M.X (m + 1)) ◁
          (tensorμ (symPow A M'.X (n + 1)) (symPow A M.X (n + 1))
            (symPow A M'.X (p + 1)) (symPow A M.X (p + 1)) ≫
            (symMul A M'.X (n + 1) (p + 1) ⊗ₘ
              symMul A M.X (n + 1) (p + 1)))) ≫
        (modTensorπ A (symPowMod A M'.X m) (symPowMod A M.X m) ⊗ₘ
          modTensorπ A (symPowMod A M'.X (n + 1 + p))
            (symPowMod A M.X (n + 1 + p))) ≫
        (chainMul A M M' m (n + 1 + p) ≫
          chainStageCast A M M' h₂) :=
    congrArg (CategoryStruct.comp _)
      (compTensorHom_whiskerLeft_split _ _ _ _)
  have rTail := chainMul_assoc_rightTail A M M' m n p h₂
  exact hleft.trans
    (hcore.trans (r1.trans (r2.trans (r3.trans (r4.trans
      (r5.trans (congrArg (CategoryStruct.comp _)
        (congrArg (CategoryStruct.comp _) rTail))))))).symm)

end ChainAssoc

end RS
