/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Transmission.Transmission
import LeanPool.BrillNoetherGraphs.Demazure.InvSet

/-!
# Output shifts of ASP permutations and transmission witnesses

Changing the ASP shift while keeping the inversion set fixed translates every
output value.  We use the convention

`outputShift τ c (n) = τ n - c`.

Thus its slipface is translated in the *first* coordinate,
`(outputShift τ c).s a b = τ.s (a + c) b`.  A transmission witness for `τ`
therefore becomes one for `outputShift τ c` by adding `c` chips at the first
marked point.  This is the useful normalization convention because both the
slipface inequality and the prescribed degree move by the same integer `c`.
-/

namespace Utilities

/-- Change the output normalization of an ASP permutation, leaving its
inversion set unchanged.  Positive `c` subtracts `c` from every output. -/
noncomputable def outputShift (τ : AspPerm) (c : ℤ) : AspPerm :=
  (AspSet.ofAspPerm τ).toAspPerm (τ.χ + c)

/-- Output shifts preserve the inversion set. -/
@[simp] theorem inv_set_outputShift (τ : AspPerm) (c : ℤ) :
    invSet (outputShift τ c) = invSet τ := by
  exact AspSet.invSet_of_toAspPerm (AspSet.ofAspPerm τ) (τ.χ + c)

/-- The ASP shift parameter increases by the output-shift amount. -/
@[simp] theorem outputShift_chi (τ : AspPerm) (c : ℤ) :
    (outputShift τ c).χ = τ.χ + c := by
  exact AspSet.chi_of_toAspPerm (AspSet.ofAspPerm τ) (τ.χ + c)

private theorem outputShift_outset (τ : AspPerm) (c n : ℤ) :
    (outputShift τ c).outset n = τ.outset n := by
  ext m
  rw [← AspPerm.invset_iff_outset, ← AspPerm.invset_iff_outset,
    inv_set_outputShift]

private theorem outputShift_inset (τ : AspPerm) (c n : ℤ) :
    (outputShift τ c).inset n = τ.inset n := by
  ext m
  rw [← AspPerm.invset_iff_inset, ← AspPerm.invset_iff_inset,
    inv_set_outputShift]

/-- Pointwise form of the output-shift convention. -/
@[simp] theorem outputShift_apply (τ : AspPerm) (c n : ℤ) :
    outputShift τ c n = τ n - c := by
  rw [AspPerm.reconstruction (outputShift τ c) n, outputShift_chi,
    outputShift_outset, outputShift_inset, AspPerm.reconstruction τ n]
  omega

/-- The slipface of an output-shifted permutation is translated in its first
coordinate. -/
@[simp] theorem outputShift_s (τ : AspPerm) (c a b : ℤ) :
    (outputShift τ c).s a b = τ.s (a + c) b := by
  rw [AspPerm.s_eq_se_card, AspPerm.s_eq_se_card]
  have hse : (outputShift τ c).seFinset a b =
      τ.seFinset (a + c) b := by
    ext n
    simp only [AspPerm.mem_se, outputShift_apply]
    omega
  rw [hse]

/-- Output shifts form an additive action on ASP permutations. -/
@[simp] theorem outputShift_zero (τ : AspPerm) :
    outputShift τ 0 = τ := by
  apply AspPerm.eq_of_inv_set_eq_of_chi_eq
  · simp
  · simp

/-- Successive output shifts add. -/
@[simp] theorem outputShift_add (τ : AspPerm) (c d : ℤ) :
    outputShift (outputShift τ c) d = outputShift τ (c + d) := by
  apply AspPerm.eq_of_inv_set_eq_of_chi_eq
  · simp
  · simp [add_assoc]

/-- For a fixed ASP permutation, the output-shift parameter is faithful. -/
theorem outputShift_injective (τ : AspPerm) :
    Function.Injective (outputShift τ) := by
  intro c d h
  have hChi := congrArg AspPerm.χ h
  simp only [outputShift_chi] at hChi
  omega

/-- The inverse shift cancels an output shift. -/
@[simp] theorem outputShift_neg_add (τ : AspPerm) (c : ℤ) :
    outputShift (outputShift τ c) (-c) = τ := by
  apply AspPerm.eq_of_inv_set_eq_of_chi_eq
  · simp
  · simp

/-- Canonical shift-zero representative of the fixed inversion set of `τ`. -/
noncomputable def shiftZeroPerm (τ : AspPerm) : AspPerm :=
  outputShift τ (-τ.χ)

@[simp] theorem shiftZeroPerm_chi (τ : AspPerm) :
    (shiftZeroPerm τ).χ = 0 := by
  simp [shiftZeroPerm]

@[simp] theorem inv_set_shiftZeroPerm (τ : AspPerm) :
    invSet (shiftZeroPerm τ) = invSet τ := by
  simp [shiftZeroPerm]

/-- Recovering the original output normalization from its shift-zero
representative. -/
@[simp] theorem shiftZeroPerm_restore (τ : AspPerm) :
    outputShift (shiftZeroPerm τ) τ.χ = τ := by
  simp [shiftZeroPerm]

/-- A single transmission inequality is transported by an output shift after
adding the same number of chips at the first mark. -/
theorem transmissionInequality_outputShift
    {G : CFGraph} (u v : G.V) (τ : AspPerm) (D : CFDiv G)
    (c a b : ℤ) :
    TransmissionInequality G u v (outputShift τ c)
      (D + c • oneChip u) a b ↔
    TransmissionInequality G u v τ D (a + c) b := by
  unfold TransmissionInequality
  rw [outputShift_s]
  have htwist : D + c • oneChip u + a • oneChip u - b • oneChip v =
      D + (a + c) • oneChip u - b • oneChip v := by
    rw [add_assoc, ← add_zsmul, add_comm c a]
  rw [htwist]
  suffices hslip : τ.s (a + 1 + c) b = τ.s (a + c + 1) b by
    rw [hslip]
  exact congrArg (fun x : ℤ => τ.s x b) (by omega)

/-- Adding `c` chips at the first mark transports a full transmission witness
to the output-shifted permutation. -/
theorem satisfiesTransmission_outputShift
    {G : CFGraph} (u v : G.V) (τ : AspPerm) (D : CFDiv G) (c : ℤ)
    (h : SatisfiesTransmission G u v τ D) :
    SatisfiesTransmission G u v (outputShift τ c) (D + c • oneChip u) := by
  constructor
  · rw [deg.map_add, map_zsmul, deg_one_chip, h.1, outputShift_chi]
    ring
  · intro a b
    exact (transmissionInequality_outputShift u v τ D c a b).mpr (h.2 (a + c) b)

/-- Output shifting is an equivalence on transmission witnesses. -/
theorem satisfiesTransmission_outputShift_iff
    {G : CFGraph} (u v : G.V) (τ : AspPerm) (D : CFDiv G) (c : ℤ) :
    SatisfiesTransmission G u v (outputShift τ c) (D + c • oneChip u) ↔
      SatisfiesTransmission G u v τ D := by
  constructor
  · intro h
    have h' := satisfiesTransmission_outputShift u v
      (outputShift τ c) (D + c • oneChip u) (-c) h
    simpa [outputShift_neg_add] using h'
  · exact satisfiesTransmission_outputShift u v τ D c

/-- Existence is invariant under output normalization. -/
theorem transmissionExists_outputShift_iff
    {G : CFGraph} (u v : G.V) (τ : AspPerm) (c : ℤ) :
    TransmissionExists G u v (outputShift τ c) ↔
      TransmissionExists G u v τ := by
  constructor
  · rintro ⟨E, hE⟩
    refine ⟨E + (-c) • oneChip u, ?_⟩
    apply (satisfiesTransmission_outputShift_iff u v τ
      (E + (-c) • oneChip u) c).mp
    convert hE using 1
    rw [add_assoc, ← add_zsmul]
    simp
  · rintro ⟨D, hD⟩
    exact ⟨D + c • oneChip u,
      satisfiesTransmission_outputShift u v τ D c hD⟩

/-- Every transmission-existence problem is canonically equivalent to its
shift-zero representative.  This is the normal form a finite search should
use. -/
theorem transmissionExists_shiftZeroPerm_iff
    {G : CFGraph} (u v : G.V) (τ : AspPerm) :
    TransmissionExists G u v (shiftZeroPerm τ) ↔
      TransmissionExists G u v τ := by
  exact transmissionExists_outputShift_iff u v τ (-τ.χ)

end Utilities
