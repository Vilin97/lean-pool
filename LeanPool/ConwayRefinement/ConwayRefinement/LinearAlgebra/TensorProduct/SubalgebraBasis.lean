/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Base change of a basis over a subalgebra

Let `Ĝ` be a commutative `K`-algebra, `S ⊆ Ĝ` a `K`-subalgebra, and `B` an `S`-basis of `Ĝ`.
For any commutative `K`-algebra `L`, the elements `B i ⊗ 1` are a basis of `Ĝ ⊗[K] L` over the
image of `S ⊗[K] L`: every element is uniquely a finite sum `∑ j(xᵢ) (B i ⊗ 1)` with
`xᵢ ∈ S ⊗[K] L`, where `j : S ⊗[K] L → Ĝ ⊗[K] L` is induced by the inclusion.
-/

universe u v w x

open scoped TensorProduct

public noncomputable section

namespace Subalgebra

variable {K : Type u} {G : Type v} {L : Type w} {ι : Type x}
variable [CommRing K] [CommRing G] [Algebra K G] [CommRing L] [Algebra K L]
variable (S : Subalgebra K G) (B : Module.Basis ι S G)

/-- The inclusion `S ⊗[K] L → Ĝ ⊗[K] L`. -/
def tensorInclusion : S ⊗[K] L →ₐ[K] G ⊗[K] L :=
  Algebra.TensorProduct.map S.val (AlgHom.id K L)

theorem tensorInclusion_tmul (s : S) (l : L) :
    S.tensorInclusion (s ⊗ₜ[K] l) = (s : G) ⊗ₜ[K] l :=
  Algebra.TensorProduct.map_tmul _ _ _ _

theorem tensorInclusion_zero : S.tensorInclusion (0 : S ⊗[K] L) = 0 :=
  map_zero _

theorem tensorInclusion_add (x y : S ⊗[K] L) :
    S.tensorInclusion (x + y) = S.tensorInclusion x + S.tensorInclusion y :=
  map_add _ x y

theorem tensorInclusion_mul (x y : S ⊗[K] L) :
    S.tensorInclusion (x * y) = S.tensorInclusion x * S.tensorInclusion y :=
  map_mul _ x y

variable [DecidableEq ι]

/-- The coordinate equivalence `Ĝ ⊗[K] L ≃ ι →₀ (S ⊗[K] L)` induced by the basis. -/
def tensorBasisRepr : G ⊗[K] L ≃ₗ[K] ι →₀ (S ⊗[K] L) :=
  (LinearEquiv.rTensor L (B.repr.restrictScalars K)) ≪≫ₗ
    TensorProduct.finsuppLeft K K S L ι

theorem tensorBasisRepr_tmul (g : G) (l : L) :
    S.tensorBasisRepr B (g ⊗ₜ[K] l) =
      (B.repr g).sum fun i s ↦ Finsupp.single i (s ⊗ₜ[K] l) := by
  rw [tensorBasisRepr, LinearEquiv.trans_apply, LinearEquiv.rTensor_tmul,
    TensorProduct.finsuppLeft_apply_tmul]
  rfl

/-- The key formula: the coordinates of `j(x) · (B i ⊗ 1)` are `single i x`. -/
theorem tensorBasisRepr_tensorInclusion_mul (x : S ⊗[K] L) (i : ι) :
    S.tensorBasisRepr B (S.tensorInclusion x * (B i ⊗ₜ[K] 1)) = Finsupp.single i x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, zero_mul, map_zero, Finsupp.single_zero]
  | tmul s l =>
    rw [tensorInclusion_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, tensorBasisRepr_tmul]
    have hsmul : (s : G) * B i = s • B i := rfl
    rw [hsmul, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
      Finsupp.sum_single_index]
    rw [TensorProduct.zero_tmul, Finsupp.single_zero]
  | add x y hx hy =>
    rw [map_add, add_mul, map_add, hx, hy, Finsupp.single_add]

theorem tensorBasisRepr_sum (s : Finset ι) (x : ι → S ⊗[K] L) :
    S.tensorBasisRepr B (∑ i ∈ s, S.tensorInclusion (x i) * (B i ⊗ₜ[K] 1)) =
      ∑ i ∈ s, Finsupp.single i (x i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ S.tensorBasisRepr_tensorInclusion_mul B (x i) i

omit [DecidableEq ι] in
/-- Linear independence of `B i ⊗ 1` over `S ⊗[K] L`. -/
theorem eq_zero_of_sum_tensorInclusion_mul_eq_zero (s : Finset ι) (x : ι → S ⊗[K] L)
    (h : ∑ i ∈ s, S.tensorInclusion (x i) * (B i ⊗ₜ[K] 1) = 0) : ∀ i ∈ s, x i = 0 := by
  classical
  intro i hi
  have h1 := congrArg (S.tensorBasisRepr B) h
  rw [S.tensorBasisRepr_sum B, map_zero] at h1
  have h2 := congrArg (fun f : ι →₀ (S ⊗[K] L) ↦ f i) h1
  simp only [Finsupp.finsetSum_apply, Finsupp.coe_zero, Pi.zero_apply] at h2
  rw [Finset.sum_eq_single i (fun j _ hj ↦ Finsupp.single_eq_of_ne hj.symm)
    (fun hni ↦ absurd hi hni), Finsupp.single_eq_same] at h2
  exact h2

omit [DecidableEq ι] in
/-- Spanning: every element of `Ĝ ⊗[K] L` is a combination of the `B i ⊗ 1` over
`S ⊗[K] L`. -/
theorem exists_eq_sum_tensorInclusion_mul (g : G ⊗[K] L) :
    ∃ (s : Finset ι) (x : ι → S ⊗[K] L),
      g = ∑ i ∈ s, S.tensorInclusion (x i) * (B i ⊗ₜ[K] 1) := by
  classical
  refine ⟨(S.tensorBasisRepr B g).support, fun i ↦ S.tensorBasisRepr B g i, ?_⟩
  apply (S.tensorBasisRepr B).injective
  rw [S.tensorBasisRepr_sum B]
  exact (Finsupp.sum_single (S.tensorBasisRepr B g)).symm

end Subalgebra
