/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Data.Opposite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.MulOpposite
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import LeanPool.Monlib4.LinearAlgebra.LinearMapOp

/-!

# Some results on the opposite vector space

This file contains the construction of the basis of an opposite space; and the construction of the
opposite inner product space.

-/


open Module

variable {R H : Type _} [Ring R] [AddCommGroup H] [Module R H] {ι : Type _}

namespace Basis

/-- Compatibility alias for the basis on a multiplicative opposite space. -/
noncomputable abbrev mulOpposite (b : Module.Basis ι R H) :
    Module.Basis ι R Hᵐᵒᵖ :=
  Module.Basis.mulOpposite b

theorem mulOpposite_apply (b : Module.Basis ι R H) (i : ι) :
    b.mulOpposite i = MulOpposite.op (b i) :=
  Module.Basis.mulOpposite_apply b i

theorem mulOpposite_repr_eq (b : Module.Basis ι R H) :
    b.mulOpposite.repr = (MulOpposite.opLinearEquiv R).symm.trans b.repr :=
  Module.Basis.mulOpposite_repr_eq b

end Basis

theorem Basis.mulOpposite_repr_apply (b : Basis ι R H) (x : Hᵐᵒᵖ) :
    b.mulOpposite.repr x = b.repr (MulOpposite.unop x) :=
  (Basis.repr_unop_eq_mulOpposite_repr b x).symm

theorem mulOpposite_finiteDimensional {R H : Type _} [DivisionRing R] [AddCommGroup H]
    [Module R H] [FiniteDimensional R H] : FiniteDimensional R Hᵐᵒᵖ := by
  infer_instance

/-- The named inner-product data on a multiplicative opposite space. -/
abbrev MulOpposite.hasInner {𝕜 H : Type _} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] : Inner 𝕜 Hᵐᵒᵖ :=
  inferInstance

theorem MulOpposite.inner_eq {𝕜 H : Type _} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (x y : Hᵐᵒᵖ) :
    inner 𝕜 x y = inner 𝕜 (MulOpposite.unop x) (MulOpposite.unop y) :=
  (MulOpposite.inner_unop x y).symm

theorem MulOpposite.inner_eq' {𝕜 H : Type _} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (x y : H) :
    inner 𝕜 (MulOpposite.op x) (MulOpposite.op y) = inner 𝕜 x y :=
  MulOpposite.inner_op x y

/-- The named inner-product-space structure on a multiplicative opposite space. -/
abbrev MulOpposite.innerProductSpace {𝕜 H : Type _} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] : InnerProductSpace 𝕜 Hᵐᵒᵖ :=
  inferInstance

theorem Basis.orthonormal_iff_mulOpposite {𝕜 H : Type _} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {ι : Type _} (b : Basis ι 𝕜 H) :
    Orthonormal 𝕜 b ↔ Orthonormal 𝕜 b.mulOpposite :=
  (Basis.mulOpposite_is_orthonormal_iff b).symm

theorem Basis.mulOpposite_is_orthonormal_iff {𝕜 H : Type _} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {ι : Type _}
    (b : Module.Basis ι 𝕜 H) :
    Orthonormal 𝕜 b ↔ Orthonormal 𝕜 b.mulOpposite :=
  (Module.Basis.mulOpposite_is_orthonormal_iff b).symm

instance MulOpposite.starModule {R H : Type _} [Star R] [SMul R H] [Star H] [StarModule R H] :
    StarModule R Hᵐᵒᵖ
    where star_smul r a := by simp_rw [star, MulOpposite.unop_smul, star_smul, MulOpposite.op_smul]

theorem MulOpposite.opContinuousLinearEquiv_adjoint {𝕜 A : Type*}
  [RCLike 𝕜] [NormedAddCommGroup A] [InnerProductSpace 𝕜 A] [CompleteSpace A] :
  ContinuousLinearMap.adjoint
    (MulOpposite.opContinuousLinearEquiv 𝕜 (M:=A)).toContinuousLinearMap
    = (MulOpposite.opContinuousLinearEquiv 𝕜 (M:=A)).symm.toContinuousLinearMap :=
by
  ext x
  apply ext_inner_left 𝕜
  intro y
  simp [ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem MulOpposite.opLinearEquiv_adjoint {𝕜 A : Type*} [RCLike 𝕜] [NormedAddCommGroup A]
  [InnerProductSpace 𝕜 A] [FiniteDimensional 𝕜 A] :
    LinearMap.adjoint (MulOpposite.opLinearEquiv 𝕜 (M:=A)).toLinearMap
      = (MulOpposite.opLinearEquiv 𝕜 (M:=A)).symm.toLinearMap :=
by
  haveI : CompleteSpace A := FiniteDimensional.complete 𝕜 A
  calc LinearMap.adjoint (MulOpposite.opLinearEquiv 𝕜 (M:=A)).toLinearMap
        = ContinuousLinearMap.adjoint
        (MulOpposite.opContinuousLinearEquiv 𝕜 (M:=A)).toContinuousLinearMap := rfl
      _ = (MulOpposite.opLinearEquiv 𝕜 (M:=A)).symm.toLinearMap := by
        rw [MulOpposite.opContinuousLinearEquiv_adjoint]; rfl

theorem LinearMap.op_adjoint {𝕜 A : Type*} [RCLike 𝕜] [NormedAddCommGroup A]
  [InnerProductSpace 𝕜 A] [FiniteDimensional 𝕜 A] (x : A →ₗ[𝕜] A) :
    LinearMap.adjoint x.op = (LinearMap.adjoint x).op :=
  calc LinearMap.adjoint x.op = LinearMap.adjoint ((MulOpposite.opLinearEquiv 𝕜 (M:=A)).toLinearMap
      ∘ₗ x ∘ₗ (MulOpposite.opLinearEquiv 𝕜 (M:=A)).symm.toLinearMap) := rfl
    _ = (LinearMap.adjoint x).op := by
      simp [← MulOpposite.opLinearEquiv_adjoint]
      simp [MulOpposite.opLinearEquiv_adjoint]
      rfl
