/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.Packing

/-!
# Stability of the six-point packing score

This file controls the score when its parameter or the underlying center distances change.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

namespace SixPointPacking

variable {configuration configuration' : SixPointConfiguration}

/-- Increasing the score parameter adds an explicit virtual-diameter gain. -/
theorem score_eq_add_gain (packing : SixPointPacking configuration) {s β : ℝ} (hs : 0 < s)
    (hsβ : s < β) :
    packing.score β = packing.score s + packing.virtualDiameter * (β - s) / (2 * s * β) := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hβ0 : β ≠ 0 := ne_of_gt (hs.trans hsβ)
  simp only [score]
  field_simp
  ring

/-- The packing score is nondecreasing in its positive parameter. -/
theorem score_mono (packing : SixPointPacking configuration) {s β : ℝ} (hs : 0 < s)
    (hsβ : s < β) : packing.score s ≤ packing.score β := by
  rw [packing.score_eq_add_gain hs hsβ]
  exact le_add_of_nonneg_right <| div_nonneg
    (mul_nonneg packing.virtualDiameter_nonneg (sub_nonneg.mpr hsβ.le))
    (mul_nonneg (mul_nonneg (by norm_num) hs.le) (hs.trans hsβ).le)

/-- Transport a packing when every relevant same-color distance can only increase. -/
def transport (packing : SixPointPacking configuration)
    (hdistance : ∀ i j : packing.support, i ≠ j → i.1.1 = j.1.1 →
      dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) ≤
        dist (configuration' i.1.1 i.1.2) (configuration' j.1.1 j.1.2)) :
    SixPointPacking configuration' where
  support := packing.support
  meets_color := packing.meets_color
  radius := packing.radius
  same_color_disjoint i j hij hcolor :=
    (packing.same_color_disjoint i j hij hcolor).trans (hdistance i j hij hcolor)

@[simp]
theorem transport_totalRadius (packing : SixPointPacking configuration)
    (hdistance : ∀ i j : packing.support, i ≠ j → i.1.1 = j.1.1 →
      dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) ≤
        dist (configuration' i.1.1 i.1.2) (configuration' j.1.1 j.1.2)) :
    (packing.transport hdistance).totalRadius = packing.totalRadius := rfl

/-- An upper perturbation of all supported distances bounds the transported virtual diameter. -/
theorem transport_virtualDiameter_le_add (packing : SixPointPacking configuration)
    (hdistance : ∀ i j : packing.support, i ≠ j → i.1.1 = j.1.1 →
      dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) ≤
        dist (configuration' i.1.1 i.1.2) (configuration' j.1.1 j.1.2))
    {eta : ℝ} (hperturb : ∀ i j : packing.support,
      dist (configuration' i.1.1 i.1.2) (configuration' j.1.1 j.1.2) ≤
        dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) + eta) :
    (packing.transport hdistance).virtualDiameter ≤ packing.virtualDiameter + eta := by
  unfold virtualDiameter
  apply Finset.sup'_le
  intro i hi
  apply Finset.sup'_le
  intro j hj
  calc
    dist (configuration' i.1.1 i.1.2) (configuration' j.1.1 j.1.2) +
          packing.radius i + packing.radius j ≤
        (dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) + eta) +
          packing.radius i + packing.radius j := by
      simpa only [transport] using
        add_le_add_left (add_le_add_left (hperturb i j) (packing.radius i)) (packing.radius j)
    _ = (dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) +
          packing.radius i + packing.radius j) + eta := by ring
    _ ≤ packing.virtualDiameter + eta :=
      add_le_add_left (packing.pair_le_virtualDiameter i j) eta

/-- A lower perturbation of all supported distances bounds the original virtual diameter. -/
theorem virtualDiameter_le_transport_add (packing : SixPointPacking configuration)
    (hdistance : ∀ i j : packing.support, i ≠ j → i.1.1 = j.1.1 →
      dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) ≤
        dist (configuration' i.1.1 i.1.2) (configuration' j.1.1 j.1.2))
    {eta : ℝ} (hperturb : ∀ i j : packing.support,
      dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) ≤
        dist (configuration' i.1.1 i.1.2) (configuration' j.1.1 j.1.2) + eta) :
    packing.virtualDiameter ≤ (packing.transport hdistance).virtualDiameter + eta := by
  unfold virtualDiameter
  apply Finset.sup'_le
  intro i hi
  apply Finset.sup'_le
  intro j hj
  calc
    dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) +
          packing.radius i + packing.radius j ≤
        (dist (configuration' i.1.1 i.1.2) (configuration' j.1.1 j.1.2) + eta) +
          packing.radius i + packing.radius j := by
      exact add_le_add_left (add_le_add_left (hperturb i j) (packing.radius i))
        (packing.radius j)
    _ = (dist (configuration' i.1.1 i.1.2) (configuration' j.1.1 j.1.2) +
          packing.radius i + packing.radius j) + eta := by ring
    _ ≤ (packing.transport hdistance).virtualDiameter + eta := by
      simpa only [transport] using
        add_le_add_left ((packing.transport hdistance).pair_le_virtualDiameter i j) eta

/-- Pairwise center errors bound the change in virtual diameter by the same error. -/
theorem abs_transport_virtualDiameter_sub_le (packing : SixPointPacking configuration)
    (hdistance : ∀ i j : packing.support, i ≠ j → i.1.1 = j.1.1 →
      dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) ≤
        dist (configuration' i.1.1 i.1.2) (configuration' j.1.1 j.1.2))
    {eta : ℝ} (hperturb : ∀ i j : packing.support,
      |dist (configuration' i.1.1 i.1.2) (configuration' j.1.1 j.1.2) -
        dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2)| ≤ eta) :
    |(packing.transport hdistance).virtualDiameter - packing.virtualDiameter| ≤ eta := by
  rw [abs_sub_le_iff]
  constructor
  · exact sub_le_iff_le_add'.2 <| packing.transport_virtualDiameter_le_add hdistance fun i j ↦
      sub_le_iff_le_add'.1 (abs_sub_le_iff.1 (hperturb i j)).1
  · exact sub_le_iff_le_add'.2 <| packing.virtualDiameter_le_transport_add hdistance fun i j ↦
      sub_le_iff_le_add'.1 (abs_sub_le_iff.1 (hperturb i j)).2

/-- A controlled diameter error preserves strict positivity after increasing the parameter. -/
theorem score_pos_of_virtualDiameter_error (packing : SixPointPacking configuration)
    (packing' : SixPointPacking configuration') {s β lower eta : ℝ} (hs : 0 < s) (hsβ : s < β)
    (hscore : 0 ≤ packing.score s) (hlower_pos : 0 < lower)
    (hlower : lower ≤ packing.virtualDiameter)
    (htotal : packing'.totalRadius = packing.totalRadius)
    (hvirtual : packing'.virtualDiameter ≤ packing.virtualDiameter + eta)
    (herror : s * eta < lower * (β - s)) : 0 < packing'.score β := by
  have hβ : 0 < β := hs.trans hsβ
  have hvisual : 0 < packing.virtualDiameter := hlower_pos.trans_le hlower
  have hbase : packing.virtualDiameter ≤ packing.totalRadius * (2 * s) := by
    rw [score, sub_nonneg] at hscore
    exact (div_le_iff₀ (by positivity : 0 < 2 * s)).1 hscore
  have hgain : lower * (β - s) ≤ packing.virtualDiameter * (β - s) :=
    mul_le_mul_of_nonneg_right hlower (sub_nonneg.mpr hsβ.le)
  have hscaledVirtual := mul_le_mul_of_nonneg_left hvirtual hs.le
  have hscaledBase := mul_le_mul_of_nonneg_left hbase hβ.le
  have hdiameter : packing'.virtualDiameter < packing.totalRadius * (2 * β) := by
    rw [← mul_lt_mul_iff_of_pos_left hs]
    calc
      s * packing'.virtualDiameter ≤ s * (packing.virtualDiameter + eta) := hscaledVirtual
      _ < β * packing.virtualDiameter := by nlinarith
      _ ≤ β * (packing.totalRadius * (2 * s)) := hscaledBase
      _ = s * (packing.totalRadius * (2 * β)) := by ring
  rw [score, htotal, sub_pos]
  exact (div_lt_iff₀ (by positivity : 0 < 2 * β)).2 hdiameter

/-- A transported packing has positive score when its center error is below the score gain. -/
theorem transport_score_pos (packing : SixPointPacking configuration)
    (hdistance : ∀ i j : packing.support, i ≠ j → i.1.1 = j.1.1 →
      dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2) ≤
        dist (configuration' i.1.1 i.1.2) (configuration' j.1.1 j.1.2))
    {s β lower eta : ℝ} (hs : 0 < s) (hsβ : s < β) (hscore : 0 ≤ packing.score s)
    (hlower_pos : 0 < lower) (hlower : lower ≤ packing.virtualDiameter)
    (herror : s * eta < lower * (β - s))
    (hperturb : ∀ i j : packing.support,
      |dist (configuration' i.1.1 i.1.2) (configuration' j.1.1 j.1.2) -
        dist (configuration i.1.1 i.1.2) (configuration j.1.1 j.1.2)| ≤ eta) :
    0 < (packing.transport hdistance).score β := by
  refine packing.score_pos_of_virtualDiameter_error (packing.transport hdistance) hs hsβ hscore
    hlower_pos hlower (packing.transport_totalRadius hdistance) ?_ herror
  exact sub_le_iff_le_add'.1
    (abs_sub_le_iff.1 (packing.abs_transport_virtualDiameter_sub_le hdistance hperturb)).1

end SixPointPacking

end LeanPool.Besicovitch
