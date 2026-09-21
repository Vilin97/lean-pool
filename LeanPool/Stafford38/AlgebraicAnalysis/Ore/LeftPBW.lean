/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Ore.Associativity
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Left PBW basis for a derivation Ore extension

The normal-form Ore
ring is a left module over its coefficient field even when the derivation is
nonzero (and hence the coefficient field is not central).  Transporting the
ordinary polynomial monomial basis across the checked normal-form equivalence
gives the expected basis `1, ∂, ∂², ...`.

The iterated tower still needs the commuting derivations to be extended over
earlier stages.  Nothing in this file postulates such extensions.
-/

namespace AlgebraicAnalysis.OreLeftPBW

open Polynomial
open Module
open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity

noncomputable section


variable {K : Type*} [Field K]

/-- The coefficient field acts on an Ore extension by multiplication on the
left through the canonical coefficient embedding.  Centrality is neither
assumed nor needed. -/
instance normalOreLeftModule (D : OreDivisionDerivation K) :
    Module K (NormalOre D) :=
  Module.compHom (NormalOre D) (normalCoefficient D)

theorem normalForm_smul_left (D : OreDivisionDerivation K)
    (c : K) (p : Polynomial K) :
    normalForm D (c • p) = c • normalForm D p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [smul_add, normalForm_add, normalForm_add, hp, hq, smul_add]
  | monomial n b =>
      rw [Polynomial.smul_monomial, normalForm_monomial,
        normalForm_monomial]
      change normalCoefficient D (c * b) * normalVariable D ^ n =
        normalCoefficient D c *
          (normalCoefficient D b * normalVariable D ^ n)
      rw [map_mul, mul_assoc]

/-- Coefficient-left Ore normal form as a linear equivalence over the
coefficient field. -/
def leftNormalFormLinearEquiv (D : OreDivisionDerivation K) :
    Polynomial K ≃ₗ[K] NormalOre D :=
  { normalFormAddEquiv D with
    map_smul' := normalForm_smul_left D }

@[simp] theorem leftNormalFormLinearEquiv_apply
    (D : OreDivisionDerivation K) (p : Polynomial K) :
    leftNormalFormLinearEquiv D p = normalForm D p := rfl

/-- The powers of the Ore variable form a left basis over the coefficient
field. -/
def orePBWBasis (D : OreDivisionDerivation K) : Basis ℕ K (NormalOre D) :=
  (Polynomial.basisMonomials K).map (leftNormalFormLinearEquiv D)

@[simp] theorem orePBWBasis_apply (D : OreDivisionDerivation K) (n : ℕ) :
    orePBWBasis D n = normalVariable D ^ n := by
  rw [orePBWBasis, Basis.map_apply, Polynomial.coe_basisMonomials]
  change normalForm D (Polynomial.monomial n 1) = normalVariable D ^ n
  rw [normalForm_monomial, map_one, one_mul]

/-- Every element has a unique finite coefficient-left expansion in powers
of the Ore variable. -/
theorem orePBW_repr_symm_single (D : OreDivisionDerivation K)
    (n : ℕ) (c : K) :
    (orePBWBasis D).repr.symm (Finsupp.single n c) =
      normalCoefficient D c * normalVariable D ^ n := by
  rw [(orePBWBasis D).repr_symm_single, orePBWBasis_apply]
  rfl


end
end AlgebraicAnalysis.OreLeftPBW
