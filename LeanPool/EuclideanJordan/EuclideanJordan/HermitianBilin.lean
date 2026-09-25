/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.HermitianMat.Jordan
public import LeanPool.EuclideanJordan.EuclideanJordan.Vendor.HermitianMat.Inner



/-!
# The Jordan product on `H_n(𝕜)` as a bundled bilinear map

`EuclideanJordan/Vendor/HermitianMat/Jordan.lean` supplies `HermitianMat.symmMul`, the
Jordan product `A ∘ B = ½(AB + BA)`, together with the scoped `HermMul` instances that make
it the `*` of a `NonUnitalNonAssocCommRing`. Several results in this library are stated over
the *unbundled* form of the product instead — an ℝ-bilinear map `m : J →ₗ[ℝ] J →ₗ[ℝ] J`, see
`EuclideanJordan/Bridge.lean` for why. This file supplies that form for the concrete carrier,
so those results can be instantiated on `H_n(𝕜)`.

The bilinearity proofs go through `symmMul_toMat` and `symmMul_comm`; the ℝ-linearity (rather
than 𝕜-linearity) is the right statement because `HermitianMat n 𝕜` is only an ℝ-module —
a 𝕜-multiple of a Hermitian matrix need not be Hermitian.
-/

@[expose] public section

noncomputable section

open scoped Matrix

namespace EuclideanJordan

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]

theorem symmMul_add_rightG (a b c : HermitianMat n 𝕜) :
    a.symmMul (b + c) = a.symmMul b + a.symmMul c := by
  ext1
  simp only [HermitianMat.symmMul_toMat, HermitianMat.mat_add]
  rw [Matrix.mul_add, Matrix.add_mul, ← smul_add]
  congr 1
  abel

omit [DecidableEq n] in
theorem symmMul_smul_rightG (t : ℝ) (a b : HermitianMat n 𝕜) :
    a.symmMul (t • b) = t • a.symmMul b := by
  ext1
  simp only [HermitianMat.symmMul_toMat, HermitianMat.mat_smul]
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add, smul_comm]

/-- The Euclidean Jordan product `x ∘ y = ½(xy + yx)` on `H_n(𝕜)` as an ℝ-bilinear map. -/
def jordanBilinG (𝕜 : Type*) [RCLike 𝕜] :
    HermitianMat n 𝕜 →ₗ[ℝ] HermitianMat n 𝕜 →ₗ[ℝ] HermitianMat n 𝕜 :=
  LinearMap.mk₂ ℝ (fun a b => a.symmMul b)
    (fun a a' b => by
      change (a + a').symmMul b = a.symmMul b + a'.symmMul b
      rw [HermitianMat.symmMul_comm, symmMul_add_rightG]
      rw [HermitianMat.symmMul_comm (A := b) (B := a),
        HermitianMat.symmMul_comm (A := b) (B := a')])
    (fun t a b => by
      change (t • a).symmMul b = t • a.symmMul b
      rw [HermitianMat.symmMul_comm, symmMul_smul_rightG,
        HermitianMat.symmMul_comm (A := b) (B := a)])
    (fun a b b' => symmMul_add_rightG a b b')
    (fun t a b => symmMul_smul_rightG t a b)

@[simp]
theorem jordanBilin_applyG (a b : HermitianMat n 𝕜) :
    jordanBilinG 𝕜 a b = a.symmMul b := rfl

end EuclideanJordan
