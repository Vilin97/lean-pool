/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!

# Tensor product of inner product spaces

Compatibility lemmas for Monlib's tensor-product inner-product API. The core
inner product space structure now lives in Mathlib.

-/

open scoped TensorProduct BigOperators

namespace TensorProduct

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Compatibility alias for Monlib's named tensor-product inner structure. -/
noncomputable abbrev Inner : _root_.Inner 𝕜 (E ⊗[𝕜] F) :=
  inferInstance

/-- Compatibility alias for Monlib's named tensor-product normed additive group. -/
noncomputable abbrev normedAddCommGroup : NormedAddCommGroup (E ⊗[𝕜] F) :=
  inferInstance

/-- Compatibility alias for Monlib's named tensor-product inner product space. -/
noncomputable abbrev innerProductSpace : InnerProductSpace 𝕜 (E ⊗[𝕜] F) :=
  inferInstance

/-- Inner products distribute over addition on the left in a tensor product. -/
protected theorem inner_add_left (x y z : E ⊗[𝕜] F) :
    inner 𝕜 (x + y) z = inner 𝕜 x z + inner 𝕜 y z :=
  inner_add_left x y z

/-- The inner product with zero on the right is zero in a tensor product. -/
protected theorem inner_zero_right (x : E ⊗[𝕜] F) :
    inner 𝕜 x (0 : E ⊗[𝕜] F) = 0 :=
  inner_zero_right x

/-- Conjugate symmetry of the tensor-product inner product. -/
protected theorem inner_conj_symm (x y : E ⊗[𝕜] F) :
    starRingEnd 𝕜 (inner 𝕜 x y) = inner 𝕜 y x :=
  inner_conj_symm y x

/-- The inner product with zero on the left is zero in a tensor product. -/
protected theorem inner_zero_left (x : E ⊗[𝕜] F) :
    inner 𝕜 (0 : E ⊗[𝕜] F) x = 0 :=
  inner_zero_left x

/-- Inner products distribute over addition on the right in a tensor product. -/
protected theorem inner_add_right (x y z : E ⊗[𝕜] F) :
    inner 𝕜 x (y + z) = inner 𝕜 x y + inner 𝕜 x z :=
  inner_add_right x y z

/-- A finite sum in the left argument may be pulled out of the tensor-product inner product. -/
protected theorem inner_sum {n : Type*} [Fintype n] (x : n → E ⊗[𝕜] F)
    (y : E ⊗[𝕜] F) : inner 𝕜 (∑ i, x i) y = ∑ i, inner 𝕜 (x i) y := by
  simpa using (sum_inner (𝕜 := 𝕜) Finset.univ x y)

/-- A finite sum in the right argument may be pulled out of the tensor-product inner product. -/
protected theorem sum_inner {n : Type*} [Fintype n] (y : E ⊗[𝕜] F)
    (x : n → E ⊗[𝕜] F) : inner 𝕜 y (∑ i, x i) = ∑ i, inner 𝕜 y (x i) := by
  simpa using (inner_sum (𝕜 := 𝕜) Finset.univ x y)

/-- The real part of `⟪x, x⟫` is nonnegative in a tensor product. -/
protected theorem inner_nonneg_re (x : E ⊗[𝕜] F) :
    0 ≤ RCLike.re (inner 𝕜 x x) :=
  inner_self_nonneg

/-- A tensor-product element can be expanded as a finite sum of pure tensors. -/
theorem eq_span {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (x : E ⊗[𝕜] F) :
    ∃ (α : Module.Basis.ofVectorSpaceIndex 𝕜 E × Module.Basis.ofVectorSpaceIndex 𝕜 F → E)
      (β : Module.Basis.ofVectorSpaceIndex 𝕜 E × Module.Basis.ofVectorSpaceIndex 𝕜 F → F),
      ∑ i, α i ⊗ₜ[𝕜] β i = x := by
  let b₁ := Module.Basis.ofVectorSpace 𝕜 E
  let b₂ := Module.Basis.ofVectorSpace 𝕜 F
  rw [← Module.Basis.sum_repr (b₁.tensorProduct b₂) x]
  simp_rw [Module.Basis.tensorProduct_apply', TensorProduct.smul_tmul']
  exact ⟨fun i => ((b₁.tensorProduct b₂).repr x) i • b₁ i.fst, fun i => b₂ i.snd, rfl⟩

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 H]

/-- The adjoint of the left unitor is its inverse. -/
theorem lid_adjoint :
    LinearMap.adjoint (TensorProduct.lid 𝕜 E).toLinearMap =
      (TensorProduct.lid 𝕜 E).symm.toLinearMap := by
  simpa [TensorProduct.toLinearEquiv_lidIsometry] using
    LinearIsometryEquiv.adjoint_toLinearMap_eq_symm (TensorProduct.lidIsometry 𝕜 E)

/-- The adjoint of the symmetry is its inverse. -/
theorem comm_adjoint :
    LinearMap.adjoint (TensorProduct.comm 𝕜 E F).toLinearMap =
      (TensorProduct.comm 𝕜 E F).symm.toLinearMap := by
  simpa [TensorProduct.toLinearEquiv_commIsometry] using
    LinearIsometryEquiv.adjoint_toLinearMap_eq_symm (TensorProduct.commIsometry 𝕜 E F)

/-- The adjoint of the associator is its inverse. -/
theorem assoc_adjoint :
    LinearMap.adjoint (TensorProduct.assoc 𝕜 E F G).toLinearMap =
      (TensorProduct.assoc 𝕜 E F G).symm.toLinearMap := by
  simpa [TensorProduct.toLinearEquiv_assocIsometry] using
    LinearIsometryEquiv.adjoint_toLinearMap_eq_symm (TensorProduct.assocIsometry 𝕜 E F G)

/-- The adjoint of the inverse associator is the associator. -/
theorem assoc_symm_adjoint :
    LinearMap.adjoint ((TensorProduct.assoc 𝕜 E F G).symm).toLinearMap =
      (TensorProduct.assoc 𝕜 E F G).toLinearMap := by
  simpa [TensorProduct.toLinearEquiv_assocIsometry] using
    LinearIsometryEquiv.adjoint_toLinearMap_eq_symm (TensorProduct.assocIsometry 𝕜 E F G).symm

/-- The adjoint of a tensor map is the tensor map of the adjoints. -/
theorem map_adjoint (f : E →ₗ[𝕜] F) (g : G →ₗ[𝕜] H) :
    LinearMap.adjoint (TensorProduct.map f g) =
      TensorProduct.map (LinearMap.adjoint f) (LinearMap.adjoint g) :=
  TensorProduct.adjoint_map f g

/-- The adjoint of the inverse left unitor is the left unitor. -/
theorem lid_symm_adjoint :
    LinearMap.adjoint (TensorProduct.lid 𝕜 E).symm.toLinearMap =
      (TensorProduct.lid 𝕜 E).toLinearMap := by
  simpa [TensorProduct.toLinearEquiv_lidIsometry] using
    LinearIsometryEquiv.adjoint_toLinearMap_eq_symm (TensorProduct.lidIsometry 𝕜 E).symm

/-- The adjoint of the inverse symmetry is the symmetry. -/
theorem comm_symm_adjoint :
    LinearMap.adjoint (TensorProduct.comm 𝕜 E F).symm.toLinearMap =
      (TensorProduct.comm 𝕜 E F).toLinearMap := by
  simpa [TensorProduct.toLinearEquiv_commIsometry] using
    LinearIsometryEquiv.adjoint_toLinearMap_eq_symm (TensorProduct.commIsometry 𝕜 E F).symm

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- Equality of tensor-product elements can be tested against pure tensors. -/
theorem inner_ext_iff' (x y : E ⊗[𝕜] F) :
    x = y ↔ ∀ (a : E) (b : F), inner 𝕜 x (a ⊗ₜ[𝕜] b) = inner 𝕜 y (a ⊗ₜ[𝕜] b) :=
  TensorProduct.ext_iff_inner_right (x := x) (y := y)

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- Equality of pure tensors can be tested against pure tensors. -/
theorem inner_ext_iff (x z : E) (y w : F) :
    x ⊗ₜ[𝕜] y = z ⊗ₜ[𝕜] w ↔
      ∀ (a : E) (b : F),
        inner 𝕜 (x ⊗ₜ[𝕜] y) (a ⊗ₜ[𝕜] b) =
          inner 𝕜 (z ⊗ₜ[𝕜] w) (a ⊗ₜ[𝕜] b) :=
  TensorProduct.ext_iff_inner_right (x := x ⊗ₜ[𝕜] y) (y := z ⊗ₜ[𝕜] w)

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- A tensor is zero iff its inner product against every pure tensor is zero. -/
theorem forall_inner_eq_zero (x : E ⊗[𝕜] F) :
    (∀ (a : E) (b : F), inner 𝕜 x (a ⊗ₜ[𝕜] b) = 0) ↔ x = 0 := by
  constructor
  · intro h
    rw [TensorProduct.inner_ext_iff' x 0]
    intro a b
    simp [h a b]
  · intro hx a b
    simp [hx]

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 H] in
/-- Equality in a fourfold tensor product can be tested against pure tensors. -/
theorem inner_ext_fourfold_iff' (x y : (E ⊗[𝕜] F) ⊗[𝕜] (G ⊗[𝕜] H)) :
    x = y ↔ ∀ (a : E) (b : F) (c : G) (d : H),
      inner 𝕜 x ((a ⊗ₜ[𝕜] b) ⊗ₜ[𝕜] (c ⊗ₜ[𝕜] d)) =
        inner 𝕜 y ((a ⊗ₜ[𝕜] b) ⊗ₜ[𝕜] (c ⊗ₜ[𝕜] d)) := by
  constructor
  · intro h a b c d
    rw [h]
  · intro h
    rw [TensorProduct.ext_iff_inner_right]
    intro p q
    induction p with
    | zero => simp
    | tmul a b =>
        induction q with
        | zero => simp
        | tmul c d => exact h a b c d
        | add q₁ q₂ hq₁ hq₂ => simp [TensorProduct.tmul_add, inner_add_right, hq₁, hq₂]
    | add p₁ p₂ hp₁ hp₂ => simp [TensorProduct.add_tmul, inner_add_right, hp₁, hp₂]

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 H] in
/-- A fourfold tensor is zero iff its inner product against every pure tensor is zero. -/
theorem forall_fourfold_inner_eq_zero (x : (E ⊗[𝕜] F) ⊗[𝕜] (G ⊗[𝕜] H)) :
    (∀ (a : E) (b : F) (c : G) (d : H),
      inner 𝕜 x ((a ⊗ₜ[𝕜] b) ⊗ₜ[𝕜] (c ⊗ₜ[𝕜] d)) = 0) ↔ x = 0 := by
  constructor
  · intro h
    rw [TensorProduct.inner_ext_fourfold_iff']
    intro a b c d
    simp [h]
  · intro hx a b c d
    simp [hx]

end TensorProduct
