/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.ExtensionBehavior
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicIdeleValue
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
/-!
# Norm-one correction for the normalized cyclotomic idele value

The positive archimedean section over `ℚ` gives the source term in the
cyclotomic norm-one reduction.  After taking a positive
`[K : ℚ]`-th root of the absolute norm of an idele, scalar extension of
that section cancels the absolute norm.  Its rational cyclotomic Artin
value is trivial, so the normalized value is unchanged.
-/

open scoped NNReal NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable (K : Type) [Field K] [NumberField K]

/-- Every idele has the same normalized cyclotomic value as an actual
norm-one idele. -/
theorem
    exists_normOneIdele_same_normalizedCyclotomicZHatIdeleValue
    (a : IdeleGroup K) :
    ∃ b : IdeleGroup.normOneSubgroup (K := K),
      normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul (b : IdeleGroup K)) =
        normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul a) := by
  let d := Module.finrank ℚ K
  have hd : d ≠ 0 := Module.finrank_pos.ne'
  let r : ℝ≥0ˣ := IdeleGroup.absoluteNorm a
  have hrpos : 0 < (r : ℝ≥0) :=
    pos_iff_ne_zero.mpr r.ne_zero
  let s0 : ℝ≥0 := (r : ℝ≥0) ^ ((d : ℝ)⁻¹)
  have hs0pos : 0 < s0 := by
    exact NNReal.rpow_pos hrpos
  let s : ℝ≥0ˣ := Units.mk0 s0 hs0pos.ne'
  have hs_pow : s ^ d = r := by
    apply Units.ext
    change s0 ^ d = (r : ℝ≥0)
    exact NNReal.rpow_inv_natCast_pow (r : ℝ≥0) hd
  let c : IdeleGroup K :=
    relativeIdeleBaseChangeMulEquiv
      (K := ℚ) (L := K)
      (RelativeIdeleGroup.inclusion ℚ K
        (rationalPositiveArchimedeanIdele s))
  have hc_absoluteNorm :
      IdeleGroup.absoluteNorm c = r⁻¹ := by
    change
      IdeleGroup.absoluteNorm
          (relativeIdeleBaseChangeMulEquiv
            (K := ℚ) (L := K)
            (RelativeIdeleGroup.inclusion ℚ K
              (rationalPositiveArchimedeanIdele s))) =
        r⁻¹
    rw [
      IdeleGroup.absoluteNorm_relativeIdeleBaseChange_inclusion_of_finite_eq_one
        (L := K) (rationalPositiveArchimedeanIdele s) rfl,
      rationalPositiveArchimedeanIdele_absoluteNorm,
      inv_pow, hs_pow]
  have hs_value :
      rationalCyclotomicZHatIdeleValue
          (rationalPositiveArchimedeanIdele s) =
        1 := by
    rw [rationalCyclotomicZHatIdeleValue_apply,
      rationalCyclotomicZHatGlobalArtin_rationalPositiveArchimedeanIdele,
      map_one]
  have hc_value :
      normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul c) =
        0 := by
    change
      normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul
            (relativeIdeleBaseChangeMulEquiv
              (K := ℚ) (L := K)
              (RelativeIdeleGroup.inclusion ℚ K
                (rationalPositiveArchimedeanIdele s)))) =
        0
    rw [normalizedCyclotomicZHatIdeleValue_baseIdeleInclusion,
      hs_value]
    simp
  refine ⟨⟨a * c, ?_⟩, ?_⟩
  · change IdeleGroup.absoluteNorm (a * c) = 1
    rw [map_mul, hc_absoluteNorm]
    simp [r]
  · change
      normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul a + Additive.ofMul c) =
        normalizedCyclotomicZHatIdeleValue K
          (Additive.ofMul a)
    rw [map_add, hc_value, add_zero]

end Reciprocity
end GlobalClassFieldTheory
