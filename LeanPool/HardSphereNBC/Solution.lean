/-
Copyright (c) 2026 ukiyois, OpenCode agent sessions. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ukiyois, OpenCode agent sessions
-/
import LeanPool.HardSphereNBC.HardSphereCompound
import LeanPool.HardSphereNBC.HardSphereClosePair
import LeanPool.HardSphereNBC.HardSphereForkPackingCoordinates

/-!
# Proved solution

The substantive proof development is in the `lean/` directory.  This module
exposes the same declarations as `Challenge.lean` and connects them to the
machine-checked flat-coordinate and fork-packing theorems.
-/

namespace PalomarHS

open HsVirial
open MeasureTheory

theorem main_result
    {k d : Nat} (hk : 2 ≤ k) :
    let _ : NeZero k := ⟨by omega⟩
    (k.factorial : ℝ) *
        |hardSphereBk (k := k) (d := d)| =
      ∑ T ∈ treeUniverse (V := Fin k),
        hardSphereNBCVolumeFlat (k := k) (d := d) T := by
  exact hardSphere_nbc_volume_identity_flat hk

theorem signed_coefficient_sign
    {k d : Nat} (hk : 2 ≤ k) :
    let _ : NeZero k := ⟨by omega⟩
    hardSphereBk (k := k) (d := d) =
      (-1 : ℝ) ^ (k - 1) * |hardSphereBk (k := k) (d := d)| := by
  let _ : NeZero k := ⟨by omega⟩
  have hfacpos : 0 < (k.factorial : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos k)
  have habs :
      |hardSphereBk (k := k) (d := d)| =
        (k.factorial : ℝ)⁻¹ *
          ∫ r : HardSphereConfiguration k d, |hardSphereOmega r| := by
    unfold hardSphereBk
    rw [abs_mul, abs_inv, abs_of_pos hfacpos,
      abs_integral_hardSphereOmega_eq_integral_abs]
  calc
    hardSphereBk (k := k) (d := d) =
        (k.factorial : ℝ)⁻¹ *
          ∫ r : HardSphereConfiguration k d, hardSphereOmega r := rfl
    _ = (k.factorial : ℝ)⁻¹ *
          ((-1 : ℝ) ^ (k - 1) *
            ∫ r : HardSphereConfiguration k d, |hardSphereOmega r|) := by
      rw [integral_hardSphereOmega_eq_sign_mul_abs]
    _ = (-1 : ℝ) ^ (k - 1) *
          ((k.factorial : ℝ)⁻¹ *
            ∫ r : HardSphereConfiguration k d, |hardSphereOmega r|) := by
      ring
    _ = (-1 : ℝ) ^ (k - 1) *
          |hardSphereBk (k := k) (d := d)| := by
      rw [habs]

theorem nbc_region_measure_le_fork_avoidance
    {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hP : hardSphereForkPacking T P) :
    (volume : Measure (HardSphereConfiguration k 3))
        (nbcRegion (V := Fin k)
          (hardSphereActiveExact (k := k) (d := 3)) T) ≤
      volume (hardSphereForkAvoidanceRegion T P) := by
  exact hardSphere_nbc_region_measure_le_forkAvoidance hP

theorem nbc_region_subset_fork_packing_separated
    {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hP : hardSphereForkPacking T P) :
    nbcRegion (V := Fin k)
        (hardSphereActiveExact (k := k) (d := 3)) T ⊆
      hardSphereForkPackingSeparatedRegion P := by
  exact hardSphere_nbc_region_subset_forkPackingSeparatedRegion hP

theorem fork_packing_two_mul_card_le_pred
    {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hP : hardSphereForkPacking T P) :
    2 * P.card ≤ k - 1 := by
  exact hardSphereForkPacking_two_mul_card_le_pred hP

theorem nbc_region_real_volume_le_kappa
    {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    (volume : Measure (HardSphereConfiguration k 3)).real
        (nbcRegion (V := Fin k)
          (hardSphereActiveExact (k := k) (d := 3)) T) ≤
      hardSphereKappa ^ (k - 1) := by
  exact hardSphereNBCRegion_real_volume_le_kappa hT

theorem nbc_region_real_volume_le_fork_factor
    {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    hardSphereNBCVolume (k := k) (d := 3) T ≤
      (17 / 32 : ℝ) ^ hardSphereNu T * hardSphereKappa ^ (k - 1) := by
  exact hardSphereNBCRegion_real_volume_le_forkFactor hT

theorem close_pair_real_volume :
    (volume : Measure (HSPosition 3 × HSPosition 3)).real
        hardSphereClosePairRegion =
      5 * Real.pi ^ 2 / 6 := by
  exact hardSphereClosePairRegion_real_volume

theorem separated_pair_real_volume_ratio :
    (volume : Measure (HSPosition 3 × HSPosition 3)).real
        hardSphereSeparatedPairRegion =
      (17 / 32 : ℝ) * hardSphereKappa ^ 2 := by
  exact hardSphereSeparatedPairRegion_real_volume_ratio

end PalomarHS
