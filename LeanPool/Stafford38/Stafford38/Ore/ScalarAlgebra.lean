/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Ore.Associativity
import LeanPool.Stafford38.Stafford38.Ore.CoordinateStage

/-!
# Scalar algebra structure on an Ore extension

If the coefficient ring is a `k`-algebra and the derivation kills `k`, then
the canonical image of `k` is central in the normal-form Ore ring.
-/

namespace Stafford38.OreScalarAlgebra

open Polynomial
open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity

noncomputable section

variable {k B : Type*} [CommRing k] [Ring B] [Algebra k B]

/-- Scalars killed by the derivation remain central after adjoining the Ore
variable. -/
theorem normalScalar_commutes (D : OreDivisionDerivation B)
    (hD : ∀ c : k, D (algebraMap k B c) = 0) (c : k) (z : NormalOre D) :
    normalCoefficient D (algebraMap k B c) * z =
      z * normalCoefficient D (algebraMap k B c) := by
  rcases normalForm_surjective D z with ⟨p, rfl⟩
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [normalForm_add, mul_add, add_mul, hp, hq]
  | monomial n b =>
      rw [normalForm_monomial]
      let s : NormalOre D := normalCoefficient D (algebraMap k B c)
      let a : NormalOre D := normalCoefficient D b
      let x : NormalOre D := normalVariable D
      have hsa : Commute s a := by
        change normalCoefficient D (algebraMap k B c) * normalCoefficient D b =
          normalCoefficient D b * normalCoefficient D (algebraMap k B c)
        rw [← (normalCoefficient D).map_mul, ← (normalCoefficient D).map_mul,
          Algebra.commutes c b]
      have hsx : Commute s x := by
        change normalCoefficient D (algebraMap k B c) * normalVariable D =
          normalVariable D * normalCoefficient D (algebraMap k B c)
        have h := normalVariable_mul_coefficient D (algebraMap k B c)
        rw [hD c, map_zero, add_zero] at h
        exact h.symm
      exact (hsa.mul_right (hsx.pow_right n)).eq

/-- The scalar algebra structure induced by the canonical coefficient map. -/
def normalOreAlgebra (D : OreDivisionDerivation B)
    (hD : ∀ c : k, D (algebraMap k B c) = 0) : Algebra k (NormalOre D) :=
  RingHom.toAlgebra'
    ((normalCoefficient D).comp (algebraMap k B))
    (normalScalar_commutes D hD)

theorem normalOreAlgebra_algebraMap (D : OreDivisionDerivation B)
    (hD : ∀ c : k, D (algebraMap k B c) = 0) :
    @algebraMap k (NormalOre D) _ _ (normalOreAlgebra D hD) =
      (normalCoefficient D).comp (algebraMap k B) := rfl


end
end Stafford38.OreScalarAlgebra
