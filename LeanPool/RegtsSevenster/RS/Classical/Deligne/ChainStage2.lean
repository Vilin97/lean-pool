/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainMulLaws
import LeanPool.RegtsSevenster.RS.Classical.Deligne.ChainDelta

/-!
# The two-index splitting-chain stages

The unbalanced generalisation of the splitting chain: stages carry
two independent symmetric-power arities, one for each slot of the
dual pair.  The balanced chain is the diagonal.  The stage
multiplication, its commutativity and associativity laws, and the
seed transitions all restate the balanced machinery at two free
indices; the substrate for the graded splitting algebra.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## The two-index stages -/

/-- A two-index stage of the splitting chain: the module tensor
product of independently sized symmetric powers of the dual
pair. -/
noncomputable def chainStage2
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (p q : ℕ) : D :=
  modTensor A (symPowMod A M'.X p) (symPowMod A M.X q)

/-- The diagonal of the two-index stages is the balanced stage. -/
@[simp]
theorem chainStage2_diag
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (k : ℕ) :
    chainStage2 A M M' k k = chainStage A M M' k := rfl

/-! ## Stage transports -/

section Stage2Cast

/-- Transport of a two-index stage along equalities of arities. -/
noncomputable def chainStage2Cast
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    {p q p' q' : ℕ}
    (hp : p = p') (hq : q = q') :
    chainStage2 A M M' p q ⟶ chainStage2 A M M' p' q' :=
  eqToHom (congrArg₂ (chainStage2 A M M') hp hq)

/-- The trivial transport is the identity. -/
@[simp]
theorem chainStage2Cast_rfl
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (p q : ℕ) :
    chainStage2Cast A M M' (rfl : p = p) (rfl : q = q) =
      𝟙 _ := rfl

/-- Stage transports compose. -/
@[reassoc (attr := simp)]
theorem chainStage2Cast_trans
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    {p q p' q' p'' q'' : ℕ}
    (hp : p = p') (hq : q = q') (hp' : p' = p'')
    (hq' : q' = q'') :
    chainStage2Cast A M M' hp hq ≫
        chainStage2Cast A M M' hp' hq' =
      chainStage2Cast A M M' (hp.trans hp') (hq.trans hq') := by
  subst hp hq hp' hq'
  simp

/-- The stage projection intertwines the symmetric-power and
two-index stage transports. -/
@[reassoc]
theorem modTensorπ_chainStage2Cast
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    {p q p' q' : ℕ}
    (hp : p = p') (hq : q = q') :
    modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q) ≫
        chainStage2Cast A M M' hp hq =
      (symPowCast A M'.X (congrArg Nat.succ hp) ⊗ₘ
          symPowCast A M.X (congrArg Nat.succ hq)) ≫
        modTensorπ A (symPowMod A M'.X p')
          (symPowMod A M.X q') := by
  subst hp hq
  simp only [chainStage2Cast_rfl, symPowCast_rfl,
    MonoidalCategory.id_tensorHom_id]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

end Stage2Cast

/-! ## The two-index stage multiplication -/

/-- **The two-index chain multiplication**: two stages interchange
and multiply into the stage of the slotwise summed arities. -/
noncomputable def chainMul2
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (p q r s : ℕ) :
    chainStage2 A M M' p q ⊗ chainStage2 A M M' r s ⟶
      chainStage2 A M M' (p + 1 + r) (q + 1 + s) :=
  interchange A (symPowMod A M'.X p) (symPowMod A M.X q)
      (symPowMod A M'.X r) (symPowMod A M.X s) ≫
    modTensorMap A (symMulMod A M'.X p r) (symMulMod A M.X q s)

/-- Defining equation of the two-index chain multiplication: under
the stage projections it is the raw crossing followed by the
slotwise symmetric multiplications. -/
theorem tensorHom_π_chainMul2
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (p q r s : ℕ) :
    (modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r) (symPowMod A M.X s)) ≫
      chainMul2 A M M' p q r s =
    tensorμ (symPow A M'.X (p + 1)) (symPow A M.X (q + 1))
        (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) ≫
      (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
        symMul A M.X (q + 1) (s + 1)) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r))
        (symPowMod A M.X (q + 1 + s)) := by
  have h5 : (modTensorπ A (symPowMod A M'.X p)
        (symPowMod A M.X q) ⊗ₘ
      modTensorπ A (symPowMod A M'.X r) (symPowMod A M.X s)) ≫
      chainMul2 A M M' p q r s =
    ((modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q) ⊗ₘ
      modTensorπ A (symPowMod A M'.X r) (symPowMod A M.X s)) ≫
      interchange A (symPowMod A M'.X p) (symPowMod A M.X q)
        (symPowMod A M'.X r) (symPowMod A M.X s)) ≫
      modTensorMap A (symMulMod A M'.X p r)
        (symMulMod A M.X q s) := by
    rw [chainMul2]
    exact (Category.assoc _ _ _).symm
  rw [h5, tensorHom_π_interchange, rawInterchangeπ,
    rawInterchange]
  simp only [Category.assoc]
  have h6 : modTensorπ A
      (modTensorMod A (symPowMod A M'.X p) (symPowMod A M'.X r))
      (modTensorMod A (symPowMod A M.X q) (symPowMod A M.X s)) ≫
      modTensorMap A (symMulMod A M'.X p r)
        (symMulMod A M.X q s) =
    ((symMulMod A M'.X p r).hom ⊗ₘ (symMulMod A M.X q s).hom) ≫
      modTensorπ A (symPowMod A M'.X (p + 1 + r))
        (symPowMod A M.X (q + 1 + s)) :=
    modTensorπ_map A (symMulMod A M'.X p r)
      (symMulMod A M.X q s)
  show tensorμ (symPow A M'.X (p + 1)) (symPow A M.X (q + 1))
      (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) ≫
    (modTensorπ A (symPowMod A M'.X p) (symPowMod A M'.X r) ⊗ₘ
      modTensorπ A (symPowMod A M.X q) (symPowMod A M.X s)) ≫
    modTensorπ A
      (modTensorMod A (symPowMod A M'.X p) (symPowMod A M'.X r))
      (modTensorMod A (symPowMod A M.X q) (symPowMod A M.X s)) ≫
    modTensorMap A (symMulMod A M'.X p r)
      (symMulMod A M.X q s) = _
  refine congrArg (CategoryStruct.comp _) ?_
  refine (congrArg (CategoryStruct.comp _) h6).trans ?_
  rw [show (symMulMod A M'.X p r).hom = symMulDesc A M'.X p r
      from rfl,
    show (symMulMod A M.X q s).hom = symMulDesc A M.X q s from
      rfl, ← Category.assoc]
  show ((modTensorπ A (symPowMod A M'.X p)
        (symPowMod A M'.X r) ⊗ₘ
      modTensorπ A (symPowMod A M.X q) (symPowMod A M.X s)) ≫
      (symMulDesc A M'.X p r ⊗ₘ symMulDesc A M.X q s)) ≫
    modTensorπ A (symPowMod A M'.X (p + 1 + r))
      (symPowMod A M.X (q + 1 + s)) = _
  rw [MonoidalCategory.tensorHom_comp_tensorHom,
    modTensorπ_symMulDesc, modTensorπ_symMulDesc]
  rfl

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

/-! ## Commutativity of the two-index multiplication -/

section Chain2Comm

/-- **Commutativity of the two-index chain multiplication**, up to
the slotwise stage transports. -/
theorem chainMul2_comm
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (p q r s : ℕ) :
    (β_ (chainStage2 A M M' p q) (chainStage2 A M M' r s)).hom ≫
        chainMul2 A M M' r s p q ≫
        chainStage2Cast A M M'
          (by omega : r + 1 + p = p + 1 + r)
          (by omega : s + 1 + q = q + 1 + s) =
      chainMul2 A M M' p q r s := by
  have hp₀ : r + 1 + p = p + 1 + r := by omega
  have hq₀ : s + 1 + q = q + 1 + s := by omega
  have hfac₁ :
      (β_ (symPow A M'.X (p + 1)) (symPow A M'.X (r + 1))).hom ≫
          symMul A M'.X (r + 1) (p + 1) ≫
          symPowCast A M'.X (congrArg Nat.succ hp₀) =
        symMul A M'.X (p + 1) (r + 1) ≫
          symPowCast A M'.X
            (rfl : p + 1 + (r + 1) = p + 1 + (r + 1)) :=
    symMul_comm_cast A M'.X (congrArg Nat.succ hp₀) rfl
  have hfac₂ :
      (β_ (symPow A M.X (q + 1)) (symPow A M.X (s + 1))).hom ≫
          symMul A M.X (s + 1) (q + 1) ≫
          symPowCast A M.X (congrArg Nat.succ hq₀) =
        symMul A M.X (q + 1) (s + 1) ≫
          symPowCast A M.X
            (rfl : q + 1 + (s + 1) = q + 1 + (s + 1)) :=
    symMul_comm_cast A M.X (congrArg Nat.succ hq₀) rfl
  have hkill₁ : symMul A M'.X (p + 1) (r + 1) ≫
      symPowCast A M'.X
        (rfl : p + 1 + (r + 1) = p + 1 + (r + 1)) =
      symMul A M'.X (p + 1) (r + 1) := by
    rw [symPowCast_rfl, Category.comp_id]
  have hkill₂ : symMul A M.X (q + 1) (s + 1) ≫
      symPowCast A M.X
        (rfl : q + 1 + (s + 1) = q + 1 + (s + 1)) =
      symMul A M.X (q + 1) (s + 1) := by
    rw [symPowCast_rfl, Category.comp_id]
  have hfacL₁ : ((β_ (symPow A M'.X (p + 1))
        (symPow A M'.X (r + 1))).hom ≫
        symMul A M'.X (r + 1) (p + 1)) ≫
        symPowCast A M'.X (congrArg Nat.succ hp₀) =
      symMul A M'.X (p + 1) (r + 1) :=
    (Category.assoc _ _ _).trans (hfac₁.trans hkill₁)
  have hfacL₂ : ((β_ (symPow A M.X (q + 1))
        (symPow A M.X (s + 1))).hom ≫
        symMul A M.X (s + 1) (q + 1)) ≫
        symPowCast A M.X (congrArg Nat.succ hq₀) =
      symMul A M.X (q + 1) (s + 1) :=
    (Category.assoc _ _ _).trans (hfac₂.trans hkill₂)
  have hβ :
      (modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r) (symPowMod A M.X s)) ≫
        (β_ (chainStage2 A M M' p q) (chainStage2 A M M' r s)).hom =
      (β_ (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
          (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X r) (symPowMod A M.X s) ⊗ₘ
          modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q)) :=
    BraidedCategory.braiding_naturality _ _
  refine (cancel_epi
    (modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q) ⊗ₘ
      modTensorπ A (symPowMod A M'.X r) (symPowMod A M.X s))).mp ?_
  have e1 : (modTensorπ A (symPowMod A M'.X p)
          (symPowMod A M.X q) ⊗ₘ
        modTensorπ A (symPowMod A M'.X r) (symPowMod A M.X s)) ≫
        ((β_ (chainStage2 A M M' p q)
            (chainStage2 A M M' r s)).hom ≫
          chainMul2 A M M' r s p q ≫
          chainStage2Cast A M M' hp₀ hq₀) =
      (β_ (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
          (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X r) (symPowMod A M.X s) ⊗ₘ
          modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q)) ≫
        chainMul2 A M M' r s p q ≫
        chainStage2Cast A M M' hp₀ hq₀ :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ (chainMul2 A M M' r s p q ≫
        chainStage2Cast A M M' hp₀ hq₀)) hβ).trans
        (Category.assoc _ _ _))
  have e2 : (β_ (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
          (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X r) (symPowMod A M.X s) ⊗ₘ
          modTensorπ A (symPowMod A M'.X p) (symPowMod A M.X q)) ≫
        chainMul2 A M M' r s p q ≫
        chainStage2Cast A M M' hp₀ hq₀ =
      (β_ (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
          (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).hom ≫
        tensorμ (symPow A M'.X (r + 1)) (symPow A M.X (s + 1))
          (symPow A M'.X (p + 1)) (symPow A M.X (q + 1)) ≫
        (symMul A M'.X (r + 1) (p + 1) ⊗ₘ
          symMul A M.X (s + 1) (q + 1)) ≫
        (modTensorπ A (symPowMod A M'.X (r + 1 + p))
          (symPowMod A M.X (s + 1 + q)) ≫
          chainStage2Cast A M M' hp₀ hq₀) :=
    congrArg (CategoryStruct.comp _)
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ chainStage2Cast A M M' hp₀ hq₀)
          (tensorHom_π_chainMul2 A M M' r s p q)).trans
          ((Category.assoc _ _ _).trans
            (congrArg (CategoryStruct.comp _)
              (Category.assoc _ _ _)))))
  have e3 : (β_ (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
          (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).hom ≫
        tensorμ (symPow A M'.X (r + 1)) (symPow A M.X (s + 1))
          (symPow A M'.X (p + 1)) (symPow A M.X (q + 1)) ≫
        (symMul A M'.X (r + 1) (p + 1) ⊗ₘ
          symMul A M.X (s + 1) (q + 1)) ≫
        (modTensorπ A (symPowMod A M'.X (r + 1 + p))
          (symPowMod A M.X (s + 1 + q)) ≫
          chainStage2Cast A M M' hp₀ hq₀) =
      (β_ (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
          (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).hom ≫
        tensorμ (symPow A M'.X (r + 1)) (symPow A M.X (s + 1))
          (symPow A M'.X (p + 1)) (symPow A M.X (q + 1)) ≫
        (symMul A M'.X (r + 1) (p + 1) ⊗ₘ
          symMul A M.X (s + 1) (q + 1)) ≫
        ((symPowCast A M'.X (congrArg Nat.succ hp₀) ⊗ₘ
          symPowCast A M.X (congrArg Nat.succ hq₀)) ≫
          modTensorπ A (symPowMod A M'.X (p + 1 + r))
            (symPowMod A M.X (q + 1 + s))) :=
    congrArg (CategoryStruct.comp _)
      (congrArg (CategoryStruct.comp _)
        (congrArg (CategoryStruct.comp _)
          (modTensorπ_chainStage2Cast A M M' hp₀ hq₀)))
  have e4 : (β_ (symPow A M'.X (p + 1) ⊗ symPow A M.X (q + 1))
          (symPow A M'.X (r + 1) ⊗ symPow A M.X (s + 1))).hom ≫
        tensorμ (symPow A M'.X (r + 1)) (symPow A M.X (s + 1))
          (symPow A M'.X (p + 1)) (symPow A M.X (q + 1)) ≫
        (symMul A M'.X (r + 1) (p + 1) ⊗ₘ
          symMul A M.X (s + 1) (q + 1)) ≫
        ((symPowCast A M'.X (congrArg Nat.succ hp₀) ⊗ₘ
          symPowCast A M.X (congrArg Nat.succ hq₀)) ≫
          modTensorπ A (symPowMod A M'.X (p + 1 + r))
            (symPowMod A M.X (q + 1 + s))) =
      tensorμ (symPow A M'.X (p + 1)) (symPow A M.X (q + 1))
          (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) ≫
        ((β_ (symPow A M'.X (p + 1)) (symPow A M'.X (r + 1))).hom
          ⊗ₘ (β_ (symPow A M.X (q + 1))
            (symPow A M.X (s + 1))).hom) ≫
        (symMul A M'.X (r + 1) (p + 1) ⊗ₘ
          symMul A M.X (s + 1) (q + 1)) ≫
        ((symPowCast A M'.X (congrArg Nat.succ hp₀) ⊗ₘ
          symPowCast A M.X (congrArg Nat.succ hq₀)) ≫
          modTensorπ A (symPowMod A M'.X (p + 1 + r))
            (symPowMod A M.X (q + 1 + s))) :=
    tensorμ_braiding_assoc _ _ _ _ _
  have e5 : tensorμ (symPow A M'.X (p + 1)) (symPow A M.X (q + 1))
          (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) ≫
        ((β_ (symPow A M'.X (p + 1)) (symPow A M'.X (r + 1))).hom
          ⊗ₘ (β_ (symPow A M.X (q + 1))
            (symPow A M.X (s + 1))).hom) ≫
        (symMul A M'.X (r + 1) (p + 1) ⊗ₘ
          symMul A M.X (s + 1) (q + 1)) ≫
        ((symPowCast A M'.X (congrArg Nat.succ hp₀) ⊗ₘ
          symPowCast A M.X (congrArg Nat.succ hq₀)) ≫
          modTensorπ A (symPowMod A M'.X (p + 1 + r))
            (symPowMod A M.X (q + 1 + s))) =
      tensorμ (symPow A M'.X (p + 1)) (symPow A M.X (q + 1))
          (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) ≫
        (((β_ (symPow A M'.X (p + 1))
            (symPow A M'.X (r + 1))).hom ≫
            symMul A M'.X (r + 1) (p + 1)) ⊗ₘ
          ((β_ (symPow A M.X (q + 1))
            (symPow A M.X (s + 1))).hom ≫
            symMul A M.X (s + 1) (q + 1))) ≫
        ((symPowCast A M'.X (congrArg Nat.succ hp₀) ⊗ₘ
          symPowCast A M.X (congrArg Nat.succ hq₀)) ≫
          modTensorπ A (symPowMod A M'.X (p + 1 + r))
            (symPowMod A M.X (q + 1 + s))) :=
    congrArg (CategoryStruct.comp _)
      (MonoidalCategory.tensorHom_comp_tensorHom_assoc _ _ _ _ _)
  have e6 : tensorμ (symPow A M'.X (p + 1)) (symPow A M.X (q + 1))
          (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) ≫
        (((β_ (symPow A M'.X (p + 1))
            (symPow A M'.X (r + 1))).hom ≫
            symMul A M'.X (r + 1) (p + 1)) ⊗ₘ
          ((β_ (symPow A M.X (q + 1))
            (symPow A M.X (s + 1))).hom ≫
            symMul A M.X (s + 1) (q + 1))) ≫
        ((symPowCast A M'.X (congrArg Nat.succ hp₀) ⊗ₘ
          symPowCast A M.X (congrArg Nat.succ hq₀)) ≫
          modTensorπ A (symPowMod A M'.X (p + 1 + r))
            (symPowMod A M.X (q + 1 + s))) =
      tensorμ (symPow A M'.X (p + 1)) (symPow A M.X (q + 1))
          (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) ≫
        ((((β_ (symPow A M'.X (p + 1))
            (symPow A M'.X (r + 1))).hom ≫
            symMul A M'.X (r + 1) (p + 1)) ≫
            symPowCast A M'.X (congrArg Nat.succ hp₀)) ⊗ₘ
          (((β_ (symPow A M.X (q + 1))
            (symPow A M.X (s + 1))).hom ≫
            symMul A M.X (s + 1) (q + 1)) ≫
            symPowCast A M.X (congrArg Nat.succ hq₀))) ≫
        modTensorπ A (symPowMod A M'.X (p + 1 + r))
          (symPowMod A M.X (q + 1 + s)) :=
    congrArg (CategoryStruct.comp _)
      (MonoidalCategory.tensorHom_comp_tensorHom_assoc _ _ _ _ _)
  have e7 : tensorμ (symPow A M'.X (p + 1)) (symPow A M.X (q + 1))
          (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) ≫
        ((((β_ (symPow A M'.X (p + 1))
            (symPow A M'.X (r + 1))).hom ≫
            symMul A M'.X (r + 1) (p + 1)) ≫
            symPowCast A M'.X (congrArg Nat.succ hp₀)) ⊗ₘ
          (((β_ (symPow A M.X (q + 1))
            (symPow A M.X (s + 1))).hom ≫
            symMul A M.X (s + 1) (q + 1)) ≫
            symPowCast A M.X (congrArg Nat.succ hq₀))) ≫
        modTensorπ A (symPowMod A M'.X (p + 1 + r))
          (symPowMod A M.X (q + 1 + s)) =
      tensorμ (symPow A M'.X (p + 1)) (symPow A M.X (q + 1))
          (symPow A M'.X (r + 1)) (symPow A M.X (s + 1)) ≫
        (symMul A M'.X (p + 1) (r + 1) ⊗ₘ
          symMul A M.X (q + 1) (s + 1)) ≫
        modTensorπ A (symPowMod A M'.X (p + 1 + r))
          (symPowMod A M.X (q + 1 + s)) :=
    congrArg (CategoryStruct.comp _)
      (congrArg (fun t => t ≫
        modTensorπ A (symPowMod A M'.X (p + 1 + r))
          (symPowMod A M.X (q + 1 + s)))
        (congrArg₂ (· ⊗ₘ ·) hfacL₁ hfacL₂))
  exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans
    (e6.trans (e7.trans
      (tensorHom_π_chainMul2 A M M' p q r s).symm))))))

end Chain2Comm

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

/-! ## Associativity of the two-index multiplication -/

section Chain2Assoc

/-- **Associativity of the two-index chain multiplication**, up to
the slotwise stage transports onto the common arities. -/
theorem chainMul2_assoc
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (a b c d e f : ℕ) :
    (chainMul2 A M M' a b c d ▷ chainStage2 A M M' e f) ≫
        chainMul2 A M M' (a + 1 + c) (b + 1 + d) e f ≫
        chainStage2Cast A M M'
          (by omega : a + 1 + c + 1 + e = a + 1 + c + 1 + e)
          (by omega : b + 1 + d + 1 + f = b + 1 + d + 1 + f) =
      (α_ (chainStage2 A M M' a b) (chainStage2 A M M' c d)
          (chainStage2 A M M' e f)).hom ≫
        (chainStage2 A M M' a b ◁ chainMul2 A M M' c d e f) ≫
        chainMul2 A M M' a b (c + 1 + e) (d + 1 + f) ≫
        chainStage2Cast A M M'
          (by omega :
            a + 1 + (c + 1 + e) = a + 1 + c + 1 + e)
          (by omega :
            b + 1 + (d + 1 + f) = b + 1 + d + 1 + f) := by
  have hp₂ : a + 1 + (c + 1 + e) = a + 1 + c + 1 + e := by omega
  have hq₂ : b + 1 + (d + 1 + f) = b + 1 + d + 1 + f := by omega
  have hK : chainMul2 A M M' (a + 1 + c) (b + 1 + d) e f ≫
      chainStage2Cast A M M'
        (rfl : a + 1 + c + 1 + e = a + 1 + c + 1 + e)
        (rfl : b + 1 + d + 1 + f = b + 1 + d + 1 + f) =
      chainMul2 A M M' (a + 1 + c) (b + 1 + d) e f := by
    rw [chainStage2Cast_rfl, Category.comp_id]
  have hcore := chainMulAssoc_core
    (symMul_assoc A M'.X (a + 1) (c + 1) (e + 1))
    (symMul_assoc A M.X (b + 1) (d + 1) (f + 1))
    (modTensorπ A (symPowMod A M'.X (a + 1 + c + 1 + e))
      (symPowMod A M.X (b + 1 + d + 1 + f)))
  refine (cancel_epi
    ((modTensorπ A (symPowMod A M'.X a) (symPowMod A M.X b) ⊗ₘ
        modTensorπ A (symPowMod A M'.X c) (symPowMod A M.X d)) ⊗ₘ
      modTensorπ A (symPowMod A M'.X e)
        (symPowMod A M.X f))).mp ?_
  -- Left bridge: from the whiskered chain multiplication to the
  -- instantiated core's left-hand side.
  have l1 : ((modTensorπ A (symPowMod A M'.X a)
          (symPowMod A M.X b) ⊗ₘ
        modTensorπ A (symPowMod A M'.X c) (symPowMod A M.X d)) ⊗ₘ
        modTensorπ A (symPowMod A M'.X e) (symPowMod A M.X f)) ≫
        ((chainMul2 A M M' a b c d ▷ chainStage2 A M M' e f) ≫
          chainMul2 A M M' (a + 1 + c) (b + 1 + d) e f ≫
          chainStage2Cast A M M'
            (rfl : a + 1 + c + 1 + e = a + 1 + c + 1 + e)
            (rfl : b + 1 + d + 1 + f = b + 1 + d + 1 + f)) =
      ((modTensorπ A (symPowMod A M'.X a) (symPowMod A M.X b) ⊗ₘ
        modTensorπ A (symPowMod A M'.X c) (symPowMod A M.X d)) ⊗ₘ
        modTensorπ A (symPowMod A M'.X e) (symPowMod A M.X f)) ≫
        ((chainMul2 A M M' a b c d ▷ chainStage2 A M M' e f) ≫
          chainMul2 A M M' (a + 1 + c) (b + 1 + d) e f) :=
    congrArg (CategoryStruct.comp _)
      (congrArg (CategoryStruct.comp _) hK)
  have l2 : ((modTensorπ A (symPowMod A M'.X a)
          (symPowMod A M.X b) ⊗ₘ
        modTensorπ A (symPowMod A M'.X c) (symPowMod A M.X d)) ⊗ₘ
        modTensorπ A (symPowMod A M'.X e) (symPowMod A M.X f)) ≫
        ((chainMul2 A M M' a b c d ▷ chainStage2 A M M' e f) ≫
          chainMul2 A M M' (a + 1 + c) (b + 1 + d) e f) =
      (((modTensorπ A (symPowMod A M'.X a) (symPowMod A M.X b) ⊗ₘ
        modTensorπ A (symPowMod A M'.X c) (symPowMod A M.X d)) ≫
        chainMul2 A M M' a b c d) ⊗ₘ
        modTensorπ A (symPowMod A M'.X e) (symPowMod A M.X f)) ≫
        chainMul2 A M M' (a + 1 + c) (b + 1 + d) e f :=
    tensorHom_whiskerRight_comp _ _ _ _
  have l3 : (((modTensorπ A (symPowMod A M'.X a)
          (symPowMod A M.X b) ⊗ₘ
        modTensorπ A (symPowMod A M'.X c) (symPowMod A M.X d)) ≫
        chainMul2 A M M' a b c d) ⊗ₘ
        modTensorπ A (symPowMod A M'.X e) (symPowMod A M.X f)) ≫
        chainMul2 A M M' (a + 1 + c) (b + 1 + d) e f =
      ((tensorμ (symPow A M'.X (a + 1)) (symPow A M.X (b + 1))
          (symPow A M'.X (c + 1)) (symPow A M.X (d + 1)) ≫
        (symMul A M'.X (a + 1) (c + 1) ⊗ₘ
          symMul A M.X (b + 1) (d + 1)) ≫
        modTensorπ A (symPowMod A M'.X (a + 1 + c))
          (symPowMod A M.X (b + 1 + d))) ⊗ₘ
        modTensorπ A (symPowMod A M'.X e) (symPowMod A M.X f)) ≫
        chainMul2 A M M' (a + 1 + c) (b + 1 + d) e f :=
    congrArg (fun t => (t ⊗ₘ
      modTensorπ A (symPowMod A M'.X e) (symPowMod A M.X f)) ≫
      chainMul2 A M M' (a + 1 + c) (b + 1 + d) e f)
      (tensorHom_π_chainMul2 A M M' a b c d)
  have l4 : ((tensorμ (symPow A M'.X (a + 1))
          (symPow A M.X (b + 1))
          (symPow A M'.X (c + 1)) (symPow A M.X (d + 1)) ≫
        (symMul A M'.X (a + 1) (c + 1) ⊗ₘ
          symMul A M.X (b + 1) (d + 1)) ≫
        modTensorπ A (symPowMod A M'.X (a + 1 + c))
          (symPowMod A M.X (b + 1 + d))) ⊗ₘ
        modTensorπ A (symPowMod A M'.X e) (symPowMod A M.X f)) ≫
        chainMul2 A M M' (a + 1 + c) (b + 1 + d) e f =
      (((tensorμ (symPow A M'.X (a + 1)) (symPow A M.X (b + 1))
          (symPow A M'.X (c + 1)) (symPow A M.X (d + 1)) ≫
        (symMul A M'.X (a + 1) (c + 1) ⊗ₘ
          symMul A M.X (b + 1) (d + 1))) ≫
        modTensorπ A (symPowMod A M'.X (a + 1 + c))
          (symPowMod A M.X (b + 1 + d))) ⊗ₘ
        modTensorπ A (symPowMod A M'.X e) (symPowMod A M.X f)) ≫
        chainMul2 A M M' (a + 1 + c) (b + 1 + d) e f :=
    congrArg (fun t => (t ⊗ₘ
      modTensorπ A (symPowMod A M'.X e) (symPowMod A M.X f)) ≫
      chainMul2 A M M' (a + 1 + c) (b + 1 + d) e f)
      (Category.assoc _ _ _).symm
  have l5 : (((tensorμ (symPow A M'.X (a + 1))
          (symPow A M.X (b + 1))
          (symPow A M'.X (c + 1)) (symPow A M.X (d + 1)) ≫
        (symMul A M'.X (a + 1) (c + 1) ⊗ₘ
          symMul A M.X (b + 1) (d + 1))) ≫
        modTensorπ A (symPowMod A M'.X (a + 1 + c))
          (symPowMod A M.X (b + 1 + d))) ⊗ₘ
        modTensorπ A (symPowMod A M'.X e) (symPowMod A M.X f)) ≫
        chainMul2 A M M' (a + 1 + c) (b + 1 + d) e f =
      ((tensorμ (symPow A M'.X (a + 1)) (symPow A M.X (b + 1))
          (symPow A M'.X (c + 1)) (symPow A M.X (d + 1)) ≫
        (symMul A M'.X (a + 1) (c + 1) ⊗ₘ
          symMul A M.X (b + 1) (d + 1))) ▷
        (symPow A M'.X (e + 1) ⊗ symPow A M.X (f + 1))) ≫
        (modTensorπ A (symPowMod A M'.X (a + 1 + c))
          (symPowMod A M.X (b + 1 + d)) ⊗ₘ
          modTensorπ A (symPowMod A M'.X e)
            (symPowMod A M.X f)) ≫
        chainMul2 A M M' (a + 1 + c) (b + 1 + d) e f :=
    compTensorHom_whiskerRight_split _ _ _ _
  have l6 : ((tensorμ (symPow A M'.X (a + 1))
          (symPow A M.X (b + 1))
          (symPow A M'.X (c + 1)) (symPow A M.X (d + 1)) ≫
        (symMul A M'.X (a + 1) (c + 1) ⊗ₘ
          symMul A M.X (b + 1) (d + 1))) ▷
        (symPow A M'.X (e + 1) ⊗ symPow A M.X (f + 1))) ≫
        (modTensorπ A (symPowMod A M'.X (a + 1 + c))
          (symPowMod A M.X (b + 1 + d)) ⊗ₘ
          modTensorπ A (symPowMod A M'.X e)
            (symPowMod A M.X f)) ≫
        chainMul2 A M M' (a + 1 + c) (b + 1 + d) e f =
      ((tensorμ (symPow A M'.X (a + 1)) (symPow A M.X (b + 1))
          (symPow A M'.X (c + 1)) (symPow A M.X (d + 1)) ≫
        (symMul A M'.X (a + 1) (c + 1) ⊗ₘ
          symMul A M.X (b + 1) (d + 1))) ▷
        (symPow A M'.X (e + 1) ⊗ symPow A M.X (f + 1))) ≫
        tensorμ (symPow A M'.X (a + 1 + c + 1))
          (symPow A M.X (b + 1 + d + 1))
          (symPow A M'.X (e + 1)) (symPow A M.X (f + 1)) ≫
        (symMul A M'.X (a + 1 + c + 1) (e + 1) ⊗ₘ
          symMul A M.X (b + 1 + d + 1) (f + 1)) ≫
        modTensorπ A (symPowMod A M'.X (a + 1 + c + 1 + e))
          (symPowMod A M.X (b + 1 + d + 1 + f)) :=
    congrArg (CategoryStruct.comp _)
      (tensorHom_π_chainMul2 A M M' (a + 1 + c) (b + 1 + d) e f)
  -- Right bridge: from the reassociated side to the instantiated
  -- core's right-hand side.
  have hα : ((modTensorπ A (symPowMod A M'.X a)
          (symPowMod A M.X b) ⊗ₘ
        modTensorπ A (symPowMod A M'.X c) (symPowMod A M.X d)) ⊗ₘ
        modTensorπ A (symPowMod A M'.X e) (symPowMod A M.X f)) ≫
        (α_ (chainStage2 A M M' a b) (chainStage2 A M M' c d)
          (chainStage2 A M M' e f)).hom =
      (α_ (symPow A M'.X (a + 1) ⊗ symPow A M.X (b + 1))
          (symPow A M'.X (c + 1) ⊗ symPow A M.X (d + 1))
          (symPow A M'.X (e + 1) ⊗ symPow A M.X (f + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X a) (symPowMod A M.X b) ⊗ₘ
          (modTensorπ A (symPowMod A M'.X c)
            (symPowMod A M.X d) ⊗ₘ
            modTensorπ A (symPowMod A M'.X e)
              (symPowMod A M.X f))) :=
    associator_naturality _ _ _
  have r1 : ((modTensorπ A (symPowMod A M'.X a)
          (symPowMod A M.X b) ⊗ₘ
        modTensorπ A (symPowMod A M'.X c) (symPowMod A M.X d)) ⊗ₘ
        modTensorπ A (symPowMod A M'.X e) (symPowMod A M.X f)) ≫
        ((α_ (chainStage2 A M M' a b) (chainStage2 A M M' c d)
          (chainStage2 A M M' e f)).hom ≫
          (chainStage2 A M M' a b ◁ chainMul2 A M M' c d e f) ≫
          chainMul2 A M M' a b (c + 1 + e) (d + 1 + f) ≫
          chainStage2Cast A M M' hp₂ hq₂) =
      (α_ (symPow A M'.X (a + 1) ⊗ symPow A M.X (b + 1))
          (symPow A M'.X (c + 1) ⊗ symPow A M.X (d + 1))
          (symPow A M'.X (e + 1) ⊗ symPow A M.X (f + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X a) (symPowMod A M.X b) ⊗ₘ
          (modTensorπ A (symPowMod A M'.X c)
            (symPowMod A M.X d) ⊗ₘ
            modTensorπ A (symPowMod A M'.X e)
              (symPowMod A M.X f))) ≫
        ((chainStage2 A M M' a b ◁ chainMul2 A M M' c d e f) ≫
          chainMul2 A M M' a b (c + 1 + e) (d + 1 + f) ≫
          chainStage2Cast A M M' hp₂ hq₂) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫
        ((chainStage2 A M M' a b ◁ chainMul2 A M M' c d e f) ≫
          chainMul2 A M M' a b (c + 1 + e) (d + 1 + f) ≫
          chainStage2Cast A M M' hp₂ hq₂)) hα).trans
        (Category.assoc _ _ _))
  have r2 : (α_ (symPow A M'.X (a + 1) ⊗ symPow A M.X (b + 1))
          (symPow A M'.X (c + 1) ⊗ symPow A M.X (d + 1))
          (symPow A M'.X (e + 1) ⊗ symPow A M.X (f + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X a) (symPowMod A M.X b) ⊗ₘ
          (modTensorπ A (symPowMod A M'.X c)
            (symPowMod A M.X d) ⊗ₘ
            modTensorπ A (symPowMod A M'.X e)
              (symPowMod A M.X f))) ≫
        ((chainStage2 A M M' a b ◁ chainMul2 A M M' c d e f) ≫
          chainMul2 A M M' a b (c + 1 + e) (d + 1 + f) ≫
          chainStage2Cast A M M' hp₂ hq₂) =
      (α_ (symPow A M'.X (a + 1) ⊗ symPow A M.X (b + 1))
          (symPow A M'.X (c + 1) ⊗ symPow A M.X (d + 1))
          (symPow A M'.X (e + 1) ⊗ symPow A M.X (f + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X a) (symPowMod A M.X b) ⊗ₘ
          ((modTensorπ A (symPowMod A M'.X c)
            (symPowMod A M.X d) ⊗ₘ
            modTensorπ A (symPowMod A M'.X e)
              (symPowMod A M.X f)) ≫
            chainMul2 A M M' c d e f)) ≫
        (chainMul2 A M M' a b (c + 1 + e) (d + 1 + f) ≫
          chainStage2Cast A M M' hp₂ hq₂) :=
    congrArg (CategoryStruct.comp _)
      (tensorHom_whiskerLeft_comp _ _ _ _)
  have r3 : (α_ (symPow A M'.X (a + 1) ⊗ symPow A M.X (b + 1))
          (symPow A M'.X (c + 1) ⊗ symPow A M.X (d + 1))
          (symPow A M'.X (e + 1) ⊗ symPow A M.X (f + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X a) (symPowMod A M.X b) ⊗ₘ
          ((modTensorπ A (symPowMod A M'.X c)
            (symPowMod A M.X d) ⊗ₘ
            modTensorπ A (symPowMod A M'.X e)
              (symPowMod A M.X f)) ≫
            chainMul2 A M M' c d e f)) ≫
        (chainMul2 A M M' a b (c + 1 + e) (d + 1 + f) ≫
          chainStage2Cast A M M' hp₂ hq₂) =
      (α_ (symPow A M'.X (a + 1) ⊗ symPow A M.X (b + 1))
          (symPow A M'.X (c + 1) ⊗ symPow A M.X (d + 1))
          (symPow A M'.X (e + 1) ⊗ symPow A M.X (f + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X a) (symPowMod A M.X b) ⊗ₘ
          (tensorμ (symPow A M'.X (c + 1)) (symPow A M.X (d + 1))
            (symPow A M'.X (e + 1)) (symPow A M.X (f + 1)) ≫
            (symMul A M'.X (c + 1) (e + 1) ⊗ₘ
              symMul A M.X (d + 1) (f + 1)) ≫
            modTensorπ A (symPowMod A M'.X (c + 1 + e))
              (symPowMod A M.X (d + 1 + f)))) ≫
        (chainMul2 A M M' a b (c + 1 + e) (d + 1 + f) ≫
          chainStage2Cast A M M' hp₂ hq₂) :=
    congrArg (fun t =>
      (α_ (symPow A M'.X (a + 1) ⊗ symPow A M.X (b + 1))
          (symPow A M'.X (c + 1) ⊗ symPow A M.X (d + 1))
          (symPow A M'.X (e + 1) ⊗ symPow A M.X (f + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X a)
          (symPowMod A M.X b) ⊗ₘ t) ≫
        (chainMul2 A M M' a b (c + 1 + e) (d + 1 + f) ≫
          chainStage2Cast A M M' hp₂ hq₂))
      (tensorHom_π_chainMul2 A M M' c d e f)
  have r4 : (α_ (symPow A M'.X (a + 1) ⊗ symPow A M.X (b + 1))
          (symPow A M'.X (c + 1) ⊗ symPow A M.X (d + 1))
          (symPow A M'.X (e + 1) ⊗ symPow A M.X (f + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X a) (symPowMod A M.X b) ⊗ₘ
          (tensorμ (symPow A M'.X (c + 1)) (symPow A M.X (d + 1))
            (symPow A M'.X (e + 1)) (symPow A M.X (f + 1)) ≫
            (symMul A M'.X (c + 1) (e + 1) ⊗ₘ
              symMul A M.X (d + 1) (f + 1)) ≫
            modTensorπ A (symPowMod A M'.X (c + 1 + e))
              (symPowMod A M.X (d + 1 + f)))) ≫
        (chainMul2 A M M' a b (c + 1 + e) (d + 1 + f) ≫
          chainStage2Cast A M M' hp₂ hq₂) =
      (α_ (symPow A M'.X (a + 1) ⊗ symPow A M.X (b + 1))
          (symPow A M'.X (c + 1) ⊗ symPow A M.X (d + 1))
          (symPow A M'.X (e + 1) ⊗ symPow A M.X (f + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X a) (symPowMod A M.X b) ⊗ₘ
          ((tensorμ (symPow A M'.X (c + 1)) (symPow A M.X (d + 1))
            (symPow A M'.X (e + 1)) (symPow A M.X (f + 1)) ≫
            (symMul A M'.X (c + 1) (e + 1) ⊗ₘ
              symMul A M.X (d + 1) (f + 1))) ≫
            modTensorπ A (symPowMod A M'.X (c + 1 + e))
              (symPowMod A M.X (d + 1 + f)))) ≫
        (chainMul2 A M M' a b (c + 1 + e) (d + 1 + f) ≫
          chainStage2Cast A M M' hp₂ hq₂) :=
    congrArg (fun t =>
      (α_ (symPow A M'.X (a + 1) ⊗ symPow A M.X (b + 1))
          (symPow A M'.X (c + 1) ⊗ symPow A M.X (d + 1))
          (symPow A M'.X (e + 1) ⊗ symPow A M.X (f + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X a)
          (symPowMod A M.X b) ⊗ₘ t) ≫
        (chainMul2 A M M' a b (c + 1 + e) (d + 1 + f) ≫
          chainStage2Cast A M M' hp₂ hq₂))
      (Category.assoc _ _ _).symm
  have r5 : (α_ (symPow A M'.X (a + 1) ⊗ symPow A M.X (b + 1))
          (symPow A M'.X (c + 1) ⊗ symPow A M.X (d + 1))
          (symPow A M'.X (e + 1) ⊗ symPow A M.X (f + 1))).hom ≫
        (modTensorπ A (symPowMod A M'.X a) (symPowMod A M.X b) ⊗ₘ
          ((tensorμ (symPow A M'.X (c + 1)) (symPow A M.X (d + 1))
            (symPow A M'.X (e + 1)) (symPow A M.X (f + 1)) ≫
            (symMul A M'.X (c + 1) (e + 1) ⊗ₘ
              symMul A M.X (d + 1) (f + 1))) ≫
            modTensorπ A (symPowMod A M'.X (c + 1 + e))
              (symPowMod A M.X (d + 1 + f)))) ≫
        (chainMul2 A M M' a b (c + 1 + e) (d + 1 + f) ≫
          chainStage2Cast A M M' hp₂ hq₂) =
      (α_ (symPow A M'.X (a + 1) ⊗ symPow A M.X (b + 1))
          (symPow A M'.X (c + 1) ⊗ symPow A M.X (d + 1))
          (symPow A M'.X (e + 1) ⊗ symPow A M.X (f + 1))).hom ≫
        ((symPow A M'.X (a + 1) ⊗ symPow A M.X (b + 1)) ◁
          (tensorμ (symPow A M'.X (c + 1)) (symPow A M.X (d + 1))
            (symPow A M'.X (e + 1)) (symPow A M.X (f + 1)) ≫
            (symMul A M'.X (c + 1) (e + 1) ⊗ₘ
              symMul A M.X (d + 1) (f + 1)))) ≫
        (modTensorπ A (symPowMod A M'.X a) (symPowMod A M.X b) ⊗ₘ
          modTensorπ A (symPowMod A M'.X (c + 1 + e))
            (symPowMod A M.X (d + 1 + f))) ≫
        (chainMul2 A M M' a b (c + 1 + e) (d + 1 + f) ≫
          chainStage2Cast A M M' hp₂ hq₂) :=
    congrArg (CategoryStruct.comp _)
      (compTensorHom_whiskerLeft_split _ _ _ _)
  have r6 : (modTensorπ A (symPowMod A M'.X a)
          (symPowMod A M.X b) ⊗ₘ
        modTensorπ A (symPowMod A M'.X (c + 1 + e))
          (symPowMod A M.X (d + 1 + f))) ≫
        (chainMul2 A M M' a b (c + 1 + e) (d + 1 + f) ≫
          chainStage2Cast A M M' hp₂ hq₂) =
      tensorμ (symPow A M'.X (a + 1)) (symPow A M.X (b + 1))
          (symPow A M'.X (c + 1 + e + 1))
          (symPow A M.X (d + 1 + f + 1)) ≫
        (symMul A M'.X (a + 1) (c + 1 + e + 1) ⊗ₘ
          symMul A M.X (b + 1) (d + 1 + f + 1)) ≫
        (modTensorπ A (symPowMod A M'.X (a + 1 + (c + 1 + e)))
          (symPowMod A M.X (b + 1 + (d + 1 + f))) ≫
          chainStage2Cast A M M' hp₂ hq₂) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ chainStage2Cast A M M' hp₂ hq₂)
        (tensorHom_π_chainMul2 A M M' a b
          (c + 1 + e) (d + 1 + f))).trans
        ((Category.assoc _ _ _).trans
          (congrArg (CategoryStruct.comp _)
            (Category.assoc _ _ _))))
  have r7 : modTensorπ A (symPowMod A M'.X (a + 1 + (c + 1 + e)))
        (symPowMod A M.X (b + 1 + (d + 1 + f))) ≫
        chainStage2Cast A M M' hp₂ hq₂ =
      (symPowCast A M'.X (congrArg Nat.succ hp₂) ⊗ₘ
        symPowCast A M.X (congrArg Nat.succ hq₂)) ≫
        modTensorπ A (symPowMod A M'.X (a + 1 + c + 1 + e))
          (symPowMod A M.X (b + 1 + d + 1 + f)) :=
    modTensorπ_chainStage2Cast A M M' hp₂ hq₂
  have r8 : (symMul A M'.X (a + 1) (c + 1 + e + 1) ⊗ₘ
        symMul A M.X (b + 1) (d + 1 + f + 1)) ≫
        ((symPowCast A M'.X (congrArg Nat.succ hp₂) ⊗ₘ
          symPowCast A M.X (congrArg Nat.succ hq₂)) ≫
          modTensorπ A (symPowMod A M'.X (a + 1 + c + 1 + e))
            (symPowMod A M.X (b + 1 + d + 1 + f))) =
      ((symMul A M'.X (a + 1) (c + 1 + e + 1) ≫
        symPowCast A M'.X (congrArg Nat.succ hp₂)) ⊗ₘ
        (symMul A M.X (b + 1) (d + 1 + f + 1) ≫
          symPowCast A M.X (congrArg Nat.succ hq₂))) ≫
        modTensorπ A (symPowMod A M'.X (a + 1 + c + 1 + e))
          (symPowMod A M.X (b + 1 + d + 1 + f)) :=
    MonoidalCategory.tensorHom_comp_tensorHom_assoc _ _ _ _ _
  have rTail : (modTensorπ A (symPowMod A M'.X a)
          (symPowMod A M.X b) ⊗ₘ
        modTensorπ A (symPowMod A M'.X (c + 1 + e))
          (symPowMod A M.X (d + 1 + f))) ≫
        (chainMul2 A M M' a b (c + 1 + e) (d + 1 + f) ≫
          chainStage2Cast A M M' hp₂ hq₂) =
      tensorμ (symPow A M'.X (a + 1)) (symPow A M.X (b + 1))
          (symPow A M'.X (c + 1 + e + 1))
          (symPow A M.X (d + 1 + f + 1)) ≫
        ((symMul A M'.X (a + 1) (c + 1 + e + 1) ≫
          symPowCast A M'.X (congrArg Nat.succ hp₂)) ⊗ₘ
          (symMul A M.X (b + 1) (d + 1 + f + 1) ≫
            symPowCast A M.X (congrArg Nat.succ hq₂))) ≫
        modTensorπ A (symPowMod A M'.X (a + 1 + c + 1 + e))
          (symPowMod A M.X (b + 1 + d + 1 + f)) :=
    r6.trans ((congrArg (CategoryStruct.comp _)
      (congrArg (CategoryStruct.comp _) r7)).trans
      (congrArg (CategoryStruct.comp _) r8))
  exact (l1.trans (l2.trans (l3.trans (l4.trans
      (l5.trans l6))))).trans
    (hcore.trans (r1.trans (r2.trans (r3.trans (r4.trans
      (r5.trans (congrArg (CategoryStruct.comp _)
        (congrArg (CategoryStruct.comp _) rTail))))))).symm)

end Chain2Assoc

/-! ## The two-index transitions -/

section Chain2Delta

/-- **The two-index chain transition**: multiplication by the
seed, which raises both arities by one. -/
noncomputable def chainDelta2
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (p q : ℕ) :
    chainStage2 A M M' p q ⟶ chainStage2 A M M' (p + 1) (q + 1) :=
  (ρ_ (chainStage2 A M M' p q)).inv ≫
    MonoidalCategory.whiskerLeft (chainStage2 A M M' p q)
      (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) ≫
    chainMul2 A M M' p q 0 0

/-- **The right unit law of the seed** at two indices: multiplying
by the seed on the right is the transition. -/
theorem chainSeed_mul2_right
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (p q : ℕ) :
    (chainStage2 A M M' p q ◁ chainSeed A M M' d) ≫
        chainMul2 A M M' p q 0 0 =
      (ρ_ (chainStage2 A M M' p q)).hom ≫
        chainDelta2 A M M' d p q := by
  rw [chainDelta2, Iso.hom_inv_id_assoc]
  exact rfl

/-- **The right transition square** at two indices: inserting the
seed in the second factor and multiplying is multiplying and then
inserting the seed. -/
theorem chainDelta2_mul_right
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (i j k l : ℕ) :
    (chainStage2 A M M' i j ◁ chainDelta2 A M M' d k l) ≫
        chainMul2 A M M' i j (k + 1) (l + 1) =
      chainMul2 A M M' i j k l ≫
        chainDelta2 A M M' d (i + 1 + k) (j + 1 + l) := by
  rw [chainDelta2, chainDelta2]
  rw [MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    Category.assoc]
  have hass := chainMul2_assoc A M M' i j k l 0 0
  rw [show chainStage2Cast A M M'
        (by omega : i + 1 + (k + 1 + 0) = i + 1 + k + 1 + 0)
        (by omega : j + 1 + (l + 1 + 0) = j + 1 + l + 1 + 0) =
      𝟙 _ from chainStage2Cast_rfl A M M' _ _,
    Category.comp_id] at hass
  rw [show chainMul2 A M M' (i + 1 + k) (j + 1 + l) 0 0 ≫
      𝟙 (chainStage2 A M M'
        (i + 1 + (k + 1 + 0)) (j + 1 + (l + 1 + 0))) =
    chainMul2 A M M' (i + 1 + k) (j + 1 + l) 0 0 from
      Category.comp_id _] at hass
  have hkey : (chainStage2 A M M' i j ◁
      chainMul2 A M M' k l 0 0) ≫
      chainMul2 A M M' i j (k + 1) (l + 1) =
    (α_ (chainStage2 A M M' i j) (chainStage2 A M M' k l)
        (chainStage2 A M M' 0 0)).inv ≫
      (chainMul2 A M M' i j k l ▷ chainStage2 A M M' 0 0) ≫
      chainMul2 A M M' (i + 1 + k) (j + 1 + l) 0 0 := by
    have h := congrArg (fun t =>
      (α_ (chainStage2 A M M' i j) (chainStage2 A M M' k l)
        (chainStage2 A M M' 0 0)).inv ≫ t) hass
    simp only [Iso.inv_hom_id_assoc] at h
    exact h.symm
  rw [hkey]
  have h1 : (chainStage2 A M M' i j ◁
      MonoidalCategory.whiskerLeft (chainStage2 A M M' k l)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
      (α_ (chainStage2 A M M' i j) (chainStage2 A M M' k l)
        (chainStage2 A M M' 0 0)).inv =
    (α_ (chainStage2 A M M' i j) (chainStage2 A M M' k l)
        (𝟙_ D)).inv ≫
      MonoidalCategory.whiskerLeft
        (chainStage2 A M M' i j ⊗ chainStage2 A M M' k l)
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) :=
    associator_inv_naturality_right _ _ _
  rw [reassoc_of% h1]
  have h2 : (chainStage2 A M M' i j ◁
      (ρ_ (chainStage2 A M M' k l)).inv) ≫
      (α_ (chainStage2 A M M' i j) (chainStage2 A M M' k l)
        (𝟙_ D)).inv =
    (ρ_ (chainStage2 A M M' i j ⊗
      chainStage2 A M M' k l)).inv := by
    monoidal
  rw [reassoc_of% h2]
  have h3 : (MonoidalCategory.whiskerLeft
      (chainStage2 A M M' i j ⊗ chainStage2 A M M' k l)
      (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d)) ≫
      (chainMul2 A M M' i j k l ▷ chainStage2 A M M' 0 0) =
    (chainMul2 A M M' i j k l ▷ 𝟙_ D) ≫
      MonoidalCategory.whiskerLeft
        (chainStage2 A M M' (i + 1 + k) (j + 1 + l))
        (Y₂ := chainStage2 A M M' 0 0) (chainSeed A M M' d) :=
    whisker_exchange _ _
  rw [reassoc_of% h3]
  have h4 : (ρ_ (chainStage2 A M M' i j ⊗
      chainStage2 A M M' k l)).inv ≫
      (chainMul2 A M M' i j k l ▷ 𝟙_ D) =
    chainMul2 A M M' i j k l ≫
      (ρ_ (chainStage2 A M M' (i + 1 + k) (j + 1 + l))).inv := by
    rw [rightUnitor_inv_naturality]
  rw [reassoc_of% h4]

/-- Transitions transport along index casts. -/
theorem chainStage2Cast_delta2
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    {a b a' b' : ℕ} (ha : a = a') (hb : b = b') :
    chainStage2Cast A M M' ha hb ≫ chainDelta2 A M M' d a' b' =
      chainDelta2 A M M' d a b ≫
        chainStage2Cast A M M' (by omega : a + 1 = a' + 1)
          (by omega : b + 1 = b' + 1) := by
  subst ha hb
  rw [chainStage2Cast_rfl, chainStage2Cast_rfl,
    Category.id_comp, Category.comp_id]

/-- **The left transition square** at two indices: inserting the
seed in the first factor and multiplying is multiplying and then
inserting the seed, up to the index transports. -/
theorem chainDelta2_mul_left
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D] [MonoidalLinear ℂ D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M')
    (i j k l : ℕ) :
    (chainDelta2 A M M' d i j ▷ chainStage2 A M M' k l) ≫
        chainMul2 A M M' (i + 1) (j + 1) k l =
      chainMul2 A M M' i j k l ≫
        chainDelta2 A M M' d (i + 1 + k) (j + 1 + l) ≫
        chainStage2Cast A M M'
          (Nat.add_right_comm (i + 1) k 1)
          (Nat.add_right_comm (j + 1) l 1) := by
  have hcm : chainMul2 A M M' (i + 1) (j + 1) k l =
      (β_ (chainStage2 A M M' (i + 1) (j + 1))
        (chainStage2 A M M' k l)).hom ≫
      chainMul2 A M M' k l (i + 1) (j + 1) ≫
      chainStage2Cast A M M'
        (by omega : k + 1 + (i + 1) = i + 1 + 1 + k)
        (by omega : l + 1 + (j + 1) = j + 1 + 1 + l) :=
    (chainMul2_comm A M M' (i + 1) (j + 1) k l).symm
  rw [hcm]
  have hnat : (chainDelta2 A M M' d i j ▷
      chainStage2 A M M' k l) ≫
      (β_ (chainStage2 A M M' (i + 1) (j + 1))
        (chainStage2 A M M' k l)).hom =
    (β_ (chainStage2 A M M' i j) (chainStage2 A M M' k l)).hom ≫
      (chainStage2 A M M' k l ◁ chainDelta2 A M M' d i j) := by
    rw [BraidedCategory.braiding_naturality_left]
  rw [reassoc_of% hnat]
  rw [reassoc_of% (chainDelta2_mul_right A M M' d k l i j)]
  have hcm2 : (β_ (chainStage2 A M M' i j)
        (chainStage2 A M M' k l)).hom ≫
      chainMul2 A M M' k l i j =
    chainMul2 A M M' i j k l ≫ chainStage2Cast A M M'
      (by omega : i + 1 + k = k + 1 + i)
      (by omega : j + 1 + l = l + 1 + j) := by
    have h := chainMul2_comm A M M' i j k l
    rw [← h, Category.assoc, Category.assoc,
      chainStage2Cast_trans, chainStage2Cast_rfl,
      Category.comp_id]
  rw [reassoc_of% hcm2]
  rw [reassoc_of% (chainStage2Cast_delta2 A M M' d
    (by omega : i + 1 + k = k + 1 + i)
    (by omega : j + 1 + l = l + 1 + j))]
  rw [chainStage2Cast_trans]

end Chain2Delta

end RS
