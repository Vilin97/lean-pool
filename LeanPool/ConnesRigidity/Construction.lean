/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.SetTheory.Cardinal.Free
import LeanPool.ConnesRigidity.Foundation.GroupTheory.SpecialLinear.Basic
import LeanPool.ConnesRigidity.Foundation.GroupTheory.Sp4Basic

/-!
Zhou's construction of the two groups in §2. The concrete tensor kernel,
retraction, acting group, and semidirect-product boundary follow the paper.
This file contains no declaration block recorded as a code transfer; its
public code dependencies are attributed in their defining modules.
-/

namespace Connes
namespace Construction

/-- Characteristic-two scalar field. Paper: §2. -/
abbrev k := ZMod 2
/-- Polynomial coefficient ring. Paper: §2. -/
abbrev R := Polynomial k
/-- Polynomial module for the construction. Paper: §2. -/
abbrev A := Fin 3 → R
/-- Acting-group carrier. Paper: §2. -/
abbrev H := SpecialLinear.SL3 × Sp4.Group

/-- Countable discrete wrapper for the acting group. Paper: §2. -/
noncomputable def actingGroup : CountableDiscreteGroup where
  Carrier := H
  group := inferInstance
  countable := by infer_instance

namespace PaperKernel

noncomputable section

/-- Countability of tensor products with countable factors. Paper: §2. -/
noncomputable instance tensorCountable
    {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module k M] [Module k N] [Countable M] [Countable N] :
    Countable (TensorProduct k M N) := by
  change Countable (Quotient (addConGen (TensorProduct.Eqv k M N)).toSetoid)
  infer_instance

/-- Tensor square used by the paper's symmetric kernel. Paper: §2. -/
abbrev TensorAA := TensorProduct k A A

/-- Countability of the tensor square. Paper: §2. -/
noncomputable instance tensorAACountable : Countable TensorAA := by
  infer_instance

/-- Flip on the tensor square. Paper: §2. -/
def flip : TensorAA ≃ₗ[k] TensorAA := TensorProduct.comm k A A

/-- Flip-fixed symmetric tensor module. Paper: §2. -/
def C : Submodule k TensorAA where
  carrier := {x | flip x = x}
  zero_mem' := by simp [flip]
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [map_add, hx, hy]
  smul_mem' := by
    intro a x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [map_smul, hx]

/-- Diagonal element of the paper's symmetric tensor module. Paper: §2. -/
def diagonal (a : A) : C :=
  ⟨a ⊗ₜ[k] a, by simp [flip, C]⟩

/-- Matrix-indexed finite symplectic module. Paper: §2. -/
abbrev PaperV := OpenAIPort.ModTwoSpace

/- The sum index records the ordered symplectic basis used by `Sp₄(F₂)`. -/
/-- Dual of the finite symplectic module. Paper: §2. -/
abbrev VStar := PaperV →ₗ[k] k

/-- Countability of the finite dual module. Paper: §2. -/
noncomputable instance vStarCountable : Countable VStar := by
  exact (show Function.Injective (fun f : PaperV →ₗ[k] k => f.toFun) from
    fun f g h => LinearMap.ext fun v => congrFun h v).countable

/-- Coefficientwise product on the polynomial module. Paper: §2. -/
noncomputable def hadamard (p q : R) : R :=
  let fp : ℕ →₀ k := AddMonoidAlgebra.coeffEquiv p.toFinsupp
  let fq : ℕ →₀ k := AddMonoidAlgebra.coeffEquiv q.toFinsupp
  Polynomial.ofFinsupp <| AddMonoidAlgebra.coeffEquiv.symm
    (Finsupp.zipWith (· * ·) (by simp) fp fq)

/-- Coefficient formula for the polynomial module product. Paper: §2. -/
@[simp] theorem coeff_hadamard (p q : R) (n : ℕ) :
    (hadamard p q).coeff n = p.coeff n * q.coeff n := by
  simp [hadamard, Polynomial.toFinsupp_apply]

/-- Additivity of the first coefficientwise product input. Paper: §2. -/
theorem hadamard_add_left (p q r : R) :
    hadamard (p + q) r = hadamard p r + hadamard q r := by
  ext n
  simp only [coeff_hadamard, Polynomial.coeff_add]
  ring

/-- Additivity of the second coefficientwise product input. Paper: §2. -/
theorem hadamard_add_right (p q r : R) :
    hadamard p (q + r) = hadamard p q + hadamard p r := by
  ext n
  simp only [coeff_hadamard, Polynomial.coeff_add]
  ring

/-- Scalar compatibility of the first coefficientwise product input. Paper: §2. -/
theorem hadamard_smul_left (c : k) (p q : R) :
    hadamard (c • p) q = c • hadamard p q := by
  ext n
  simp only [coeff_hadamard, Polynomial.coeff_smul, smul_eq_mul]
  ring

/-- Scalar compatibility of the second coefficientwise product input. Paper: §2. -/
theorem hadamard_smul_right (c : k) (p q : R) :
    hadamard p (c • q) = c • hadamard p q := by
  ext n
  simp only [coeff_hadamard, Polynomial.coeff_smul, smul_eq_mul]
  ring

/-- Squaring for the coefficientwise product over the Boolean field. Paper: §2. -/
theorem hadamard_square (p : R) : hadamard p p = p := by
  ext n
  simp only [coeff_hadamard]
  simpa only [pow_two] using ZMod.pow_card (p.coeff n)

/-- Coordinatewise coefficientwise product on the polynomial module. Paper: §2. -/
def coordHadamard (a b : A) : A := fun i => hadamard (a i) (b i)

/-- Bilinear map used to construct the paper retraction. Paper: §2. -/
def coordHadamardLinear : A →ₗ[k] A →ₗ[k] A where
  toFun a :=
    { toFun := fun b => coordHadamard a b
      map_add' := by
        intro b c
        funext i
        exact hadamard_add_right _ _ _
      map_smul' := by
        intro c b
        funext i
        exact hadamard_smul_right _ _ _ }
  map_add' := by
    intro a b
    apply LinearMap.ext
    intro c
    funext i
    change hadamard ((a + b) i) (c i) =
      hadamard (a i) (c i) + hadamard (b i) (c i)
    exact hadamard_add_left _ _ _
  map_smul' := by
    intro c a
    apply LinearMap.ext
    intro b
    funext i
    change hadamard ((c • a) i) (b i) =
      c • hadamard (a i) (b i)
    exact hadamard_smul_left _ _ _

/-- Linear map on the tensor square underlying the paper retraction. Paper: §2. -/
def deltaTensor : TensorAA →ₗ[k] A := TensorProduct.lift coordHadamardLinear

/-- Equivariant-retraction candidate on the flip-fixed tensor module. Paper: §2. -/
def delta : C →ₗ[k] A := deltaTensor.domRestrict C

/-- The retraction returns the original vector on diagonal tensors. Paper: §2. -/
theorem delta_diagonal (a : A) : delta (diagonal a) = a := by
  funext i
  change hadamard (a i) (a i) = a i
  exact hadamard_square (a i)

/-- First summand of the paper's abelian kernel. Paper: §2. -/
abbrev AVStar := TensorProduct k A VStar

/-- Countability of the tensor-dual summand. Paper: §2. -/
noncomputable instance avStarCountable : Countable AVStar := by
  infer_instance

/-- Binary product presentation of the paper's direct-sum kernel. Paper: §2. -/
abbrev D := AVStar × C

/-- Countability of the paper-shaped kernel. Paper: §2. -/
noncomputable instance dCountable : Countable D := by
  infer_instance

/-- Countability of the multiplicative paper-shaped kernel. Paper: §2. -/
noncomputable instance paperGammaKernelCountable :
    Countable (Multiplicative D) := by
  change Countable D
  infer_instance

/-- Carrier of the paper-shaped semidirect group associated to a kernel action. Paper: §2. -/
abbrev paperGammaCarrier
    (action : H →* MulAut (Multiplicative D)) :=
  SemidirectProduct (Multiplicative D) H action

/-- Paper-shaped semidirect group associated to a kernel action. Paper: §2. -/
noncomputable abbrev paperGammaOf
    (action : H →* MulAut (Multiplicative D)) : CountableDiscreteGroup where
  Carrier := paperGammaCarrier action
  group := inferInstance
  countable := by
    exact SemidirectProduct.equivProd.injective.countable

end
end PaperKernel

end Construction
end Connes
