/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.BoundaryOrthants
/-!
# Bounded augmented reference map

The reference map is scaled pointwise by an invariant positive factor derived from its coordinate
`ℓ¹` size. This avoids choosing maxima while still placing every coordinate strictly inside
`(-1/2, 1/2)`. Adding the signed-interval coordinate then gives strict endpoint orthant signs.
-/

namespace NRR

variable {p : ℕ} {hp : Nat.Prime p}

namespace PrimeConfigurationModel

/-- Coordinate `ℓ¹` size of the reference vector. -/
noncomputable def referenceL1 (M : PrimeConfigurationModel hp) (x : M.Point) : ℝ :=
  ∑ i : Fin p, |M.reference x i|

 theorem referenceL1_nonneg (M : PrimeConfigurationModel hp) (x : M.Point) :
    0 ≤ M.referenceL1 x :=
  Finset.sum_nonneg fun i _ => abs_nonneg _

 theorem continuous_referenceL1 (M : PrimeConfigurationModel hp) :
    Continuous M.referenceL1 := by
  unfold referenceL1
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp
      (continuous_induced_dom.comp M.reference.continuous)).abs

 theorem referenceL1_smul
    (M : PrimeConfigurationModel hp)
    (g : PrimeSymmetry p) (x : M.Point) :
    M.referenceL1 (g • x) = M.referenceL1 x := by
  unfold referenceL1
  rw [M.reference_smul]
  simp only [PrimeSymmetry.smul_zeroSum_apply]
  simpa using
    (PrimeSymmetry.toPerm p g).symm.sum_comp
      (fun i => |M.reference x i|)

/-- Positive invariant scale used to bound every reference coordinate. -/
noncomputable def referenceScale (M : PrimeConfigurationModel hp) (x : M.Point) : ℝ :=
  1 / (2 * (1 + M.referenceL1 x))

 theorem referenceScale_pos (M : PrimeConfigurationModel hp) (x : M.Point) :
    0 < M.referenceScale x := by
  unfold referenceScale
  exact one_div_pos.mpr (mul_pos (by norm_num)
    (by linarith [M.referenceL1_nonneg x]))

 theorem continuous_referenceScale (M : PrimeConfigurationModel hp) :
    Continuous M.referenceScale := by
  unfold referenceScale
  apply Continuous.div continuous_const
    (continuous_const.mul (continuous_const.add M.continuous_referenceL1))
  intro x
  have hpos : 0 < 2 * (1 + M.referenceL1 x) :=
    mul_pos (by norm_num) (by linarith [M.referenceL1_nonneg x])
  exact hpos.ne'

 theorem referenceScale_smul
    (M : PrimeConfigurationModel hp)
    (g : PrimeSymmetry p) (x : M.Point) :
    M.referenceScale (g • x) = M.referenceScale x := by
  simp [referenceScale, referenceL1_smul]

 theorem abs_reference_le_l1
    (M : PrimeConfigurationModel hp) (x : M.Point) (i : Fin p) :
    |M.reference x i| ≤ M.referenceL1 x := by
  unfold referenceL1
  exact Finset.single_le_sum (fun j _ => abs_nonneg (M.reference x j))
    (Finset.mem_univ i)

/-- The scaled reference vector. -/
noncomputable def scaledReference
    (M : PrimeConfigurationModel hp) : C(M.Point, ZeroSum p) where
  toFun x := ⟨fun i => M.referenceScale x * M.reference x i, by
    rw [← Finset.mul_sum]
    simp⟩
  continuous_toFun := by
    refine continuous_induced_rng.2 ?_
    exact continuous_pi fun i =>
      M.continuous_referenceScale.mul
        ((continuous_apply i).comp
          (continuous_induced_dom.comp M.reference.continuous))

@[simp] theorem scaledReference_apply
    (M : PrimeConfigurationModel hp) (x : M.Point) (i : Fin p) :
    M.scaledReference x i = M.referenceScale x * M.reference x i := rfl

 theorem scaledReference_smul
    (M : PrimeConfigurationModel hp)
    (g : PrimeSymmetry p) (x : M.Point) :
    M.scaledReference (g • x) = g • M.scaledReference x := by
  apply ZeroSum.ext
  intro i
  simp [scaledReference_apply, referenceScale_smul, M.reference_smul,
    PrimeSymmetry.smul_zeroSum_apply]

 theorem abs_scaledReference_lt_half
    (M : PrimeConfigurationModel hp) (x : M.Point) (i : Fin p) :
    |M.scaledReference x i| < 1 / 2 := by
  have hS : 0 ≤ M.referenceL1 x := M.referenceL1_nonneg x
  have hi : |M.reference x i| ≤ M.referenceL1 x :=
    M.abs_reference_le_l1 x i
  have hden : 0 < 2 * (1 + M.referenceL1 x) := by positivity
  rw [scaledReference_apply, abs_mul, abs_of_pos (M.referenceScale_pos x)]
  unfold referenceScale
  rw [one_div_mul_eq_div]
  apply (div_lt_iff₀ hden).2
  nlinarith

/-- Action on a model point and signed-interval coordinate. -/
def smulPointInterval
    (M : PrimeConfigurationModel hp)
    (g : PrimeSymmetry p)
    (z : M.Point × SignedInterval) : M.Point × SignedInterval :=
  (g • z.1, z.2)

/-- Reference vector augmented by the interval coordinate in the diagonal direction. -/
noncomputable def augmentedReference
    (M : PrimeConfigurationModel hp) :
    M.Point × SignedInterval → (Fin p → ℝ) :=
  fun z i => M.scaledReference z.1 i + (z.2 : ℝ)

 theorem continuous_augmentedReference (M : PrimeConfigurationModel hp) :
    Continuous M.augmentedReference := by
  unfold augmentedReference
  exact continuous_pi fun i =>
    ((continuous_apply i).comp
      (continuous_induced_dom.comp (M.scaledReference.continuous.comp continuous_fst))).add
      (SignedInterval.continuous_coord.comp continuous_snd)

 theorem augmentedReference_smul
    (M : PrimeConfigurationModel hp)
    (g : PrimeSymmetry p) (z : M.Point × SignedInterval) :
    M.augmentedReference (M.smulPointInterval g z) =
      g • M.augmentedReference z := by
  funext i
  simp [augmentedReference, smulPointInterval, M.scaledReference_smul,
    PrimeSymmetry.smul_coordinate_apply]

 theorem coordinateMean_augmentedReference
    (M : PrimeConfigurationModel hp) (z : M.Point × SignedInterval) :
    coordinateMean hp.pos (M.augmentedReference z) = (z.2 : ℝ) := by
  change coordinateMean hp.pos
    (reconstructCoordinates p (M.scaledReference z.1, (z.2 : ℝ))) = _
  exact coordinateMean_reconstruct hp.pos _ _

 theorem coordinateDeviation_augmentedReference
    (M : PrimeConfigurationModel hp) (z : M.Point × SignedInterval) :
    coordinateDeviation hp.pos (M.augmentedReference z) = M.scaledReference z.1 := by
  change coordinateDeviation hp.pos
    (reconstructCoordinates p (M.scaledReference z.1, (z.2 : ℝ))) = _
  exact coordinateDeviation_reconstruct hp.pos _ _

 theorem scaledReference_eq_zero_iff
    (M : PrimeConfigurationModel hp) (x : M.Point) :
    M.scaledReference x = 0 ↔ M.reference x = 0 := by
  constructor
  · intro h
    apply ZeroSum.ext
    intro i
    have hi := congrArg (fun v : ZeroSum p => v i) h
    simp only [scaledReference_apply, ZeroSum.zero_apply] at hi
    exact (mul_eq_zero.mp hi).resolve_left (M.referenceScale_pos x).ne'
  · intro h
    apply ZeroSum.ext
    intro i
    simp [scaledReference_apply, h]

 theorem augmentedReference_eq_zero_iff
    (M : PrimeConfigurationModel hp) (z : M.Point × SignedInterval) :
    M.augmentedReference z = 0 ↔
      M.reference z.1 = 0 ∧ z.2 = SignedInterval.center := by
  rw [coordinate_eq_zero_iff hp.pos]
  rw [M.coordinateDeviation_augmentedReference, M.coordinateMean_augmentedReference]
  rw [M.scaledReference_eq_zero_iff]
  constructor
  · rintro ⟨href, ht⟩
    refine ⟨href, ?_⟩
    apply Subtype.ext
    simpa using ht
  · rintro ⟨href, hcenter⟩
    refine ⟨href, ?_⟩
    rw [hcenter]
    rfl

 theorem augmentedReference_left_mem_negative
    (M : PrimeConfigurationModel hp) (x : M.Point) :
    M.augmentedReference (x, SignedInterval.left) ∈ negativeOrthant p := by
  intro i
  have h := M.abs_scaledReference_lt_half x i
  rw [abs_lt] at h
  change M.scaledReference x i + (-1 : ℝ) < 0
  linarith

 theorem augmentedReference_right_mem_positive
    (M : PrimeConfigurationModel hp) (x : M.Point) :
    M.augmentedReference (x, SignedInterval.right) ∈ positiveOrthant p := by
  intro i
  have h := M.abs_scaledReference_lt_half x i
  rw [abs_lt] at h
  change 0 < M.scaledReference x i + (1 : ℝ)
  linarith

end PrimeConfigurationModel

end NRR
