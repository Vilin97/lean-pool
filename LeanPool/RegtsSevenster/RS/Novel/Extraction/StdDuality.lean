/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.ProdSum
import LeanPool.RegtsSevenster.RS.Novel.Extraction.StdSuper

/-!
# The standard form as a morphism of super vector spaces

The §5.1 conventions at the categorical level: the orthosymplectic
form on the standard super space is an even morphism
`stdSuperPair ⊗ stdSuperPair ⟶ 𝟙` in SuperVect, and it is supersymmetric —
composing with the Koszul braiding returns the form.  The even
block is symmetric; the odd block is antisymmetric, and the Koszul
sign of the braiding on the odd⊗odd summand exactly compensates.
-/

namespace RS

open scoped TensorProduct

/-- The even form as a bilinear map. -/
noncomputable def stdFormEvenBilin (k : ℕ) :
    (Fin k → ℂ) →ₗ[ℂ] (Fin k → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (stdFormEven k)
    (fun x x' y => by
      unfold stdFormEven
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by
        change (x i + x' i) * y i = _
        ring))
    (fun c x y => by
      unfold stdFormEven
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by
        change (c * x i) * y i = _
        ring))
    (fun x y y' => by
      unfold stdFormEven
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by
        change x i * (y i + y' i) = _
        ring))
    (fun c x y => by
      unfold stdFormEven
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by
        change x i * (c * y i) = _
        ring))

/-- The odd form as a bilinear map. -/
noncomputable def stdFormOddBilin (ℓ : ℕ) :
    (Fin (2 * ℓ) → ℂ) →ₗ[ℂ] (Fin (2 * ℓ) → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (stdFormOdd ℓ)
    (fun x x' y => by
      unfold stdFormOdd
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by
        change -(oddPartnerSign ℓ i : ℂ) * (x i + x' i) * y (oddPartner ℓ i) = _
        ring))
    (fun c x y => by
      unfold stdFormOdd
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by
        change -(oddPartnerSign ℓ i : ℂ) * (c * x i) * y (oddPartner ℓ i) = _
        ring))
    (fun x y y' => by
      unfold stdFormOdd
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by
        change -(oddPartnerSign ℓ i : ℂ) * x i *
          (y (oddPartner ℓ i) + y' (oddPartner ℓ i)) = _
        ring))
    (fun c x y => by
      unfold stdFormOdd
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by
        change -(oddPartnerSign ℓ i : ℂ) * x i *
          (c * y (oddPartner ℓ i)) = _
        ring))

/-- The standard form as an even morphism
`stdSuperPair ⊗ stdSuperPair ⟶ 𝟙` of super vector spaces. -/
noncomputable def stdForm (k ℓ : ℕ) :
    SuperVect.Hom
      (SuperVect.tensorObj (stdSuperPair k ℓ) (stdSuperPair k ℓ))
      SuperVect.tensorUnit := by
  refine ⟨?_, ?_⟩
  · change ((Fin k → ℂ) ⊗[ℂ] (Fin k → ℂ)) ×
        ((Fin (2 * ℓ) → ℂ) ⊗[ℂ] (Fin (2 * ℓ) → ℂ)) →ₗ[ℂ] ℂ
    exact LinearMap.coprod (TensorProduct.lift (stdFormEvenBilin k))
      (TensorProduct.lift (stdFormOddBilin ℓ))
  · change ((Fin k → ℂ) ⊗[ℂ] (Fin (2 * ℓ) → ℂ)) ×
        ((Fin (2 * ℓ) → ℂ) ⊗[ℂ] (Fin k → ℂ)) →ₗ[ℂ] PUnit
    exact 0

/-- The even form is symmetric. -/
theorem stdFormEven_comm (k : ℕ) (x y : Fin k → ℂ) :
    stdFormEven k x y = stdFormEven k y x := by
  unfold stdFormEven
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

end RS
