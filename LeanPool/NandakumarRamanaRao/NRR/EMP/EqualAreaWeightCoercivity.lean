/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import Mathlib.Tactic
import LeanPool.NandakumarRamanaRao.NRR.EMP.EqualAreaWeightOutward
import LeanPool.NandakumarRamanaRao.NRR.EMP.NormalizedAreaDeviation
/-!
# Coercivity gauge for the augmented equal-area deviation field

The normalized area-deviation map lives on the zero-sum hyperplane.  To apply the
Euclidean outward-field theorem without choosing a basis of that hyperplane, we add
back the constant direction: the augmented field is the area deviation of the
mean-subtracted weights plus the weight mean in every coordinate.

A continuous homogeneous gauge detects both components.  Its restriction to the
Euclidean unit sphere has a positive minimum, giving a uniform outward radius.
-/

noncomputable section

open NRR Geometry RealInnerProductSpace

namespace NRR
namespace EMP

variable {n : Nat}

private abbrev WeightE (n : Nat) := EuclideanSpace Real (Fin n)

/-- Sum of positive coordinates of a weight vector. -/
noncomputable def positiveWeightMass (w : Fin n → Real) : Real :=
  ∑ i, max (w i) 0

lemma positiveWeightMass_nonneg (w : Fin n → Real) :
    0 ≤ positiveWeightMass w := by
  exact Finset.sum_nonneg fun _ _ => le_max_right _ _

/-- A homogeneous gauge separating the normalized and constant directions. -/
noncomputable def weightCoercivityGauge (w : Fin n → Real) : Real :=
  positiveWeightMass (normalizeWeight w) + |weightMean w|

lemma continuous_weightCoercivityGauge :
    Continuous (fun w : WeightE n => weightCoercivityGauge (fun i => w i)) := by
  unfold weightCoercivityGauge positiveWeightMass normalizeWeight weightMean weightSum
  fun_prop

lemma weightCoercivityGauge_nonneg (w : Fin n → Real) :
    0 ≤ weightCoercivityGauge w :=
  add_nonneg (positiveWeightMass_nonneg _) (abs_nonneg _)

lemma normalizeWeight_add_mean (w : Fin n → Real) (i : Fin n) :
    normalizeWeight w i + weightMean w = w i := by
  simp [normalizeWeight_apply]

lemma weightCoercivityGauge_pos_of_ne_zero
    (hn : 0 < n) (w : Fin n → Real) (hw : w ≠ 0) :
    0 < weightCoercivityGauge w := by
  have hnorm : ∑ i, normalizeWeight w i = 0 :=
    WeightNormalized_normalizeWeight w hn
  have hnonneg := weightCoercivityGauge_nonneg w
  refine lt_of_le_of_ne hnonneg ?_
  intro hzero
  have hsum : positiveWeightMass (normalizeWeight w) + |weightMean w| = 0 := by
    simpa [weightCoercivityGauge] using hzero.symm
  have hparts : positiveWeightMass (normalizeWeight w) = 0 ∧ weightMean w = 0 := by
    have hpnonneg := positiveWeightMass_nonneg (normalizeWeight w)
    have habsnonneg := abs_nonneg (weightMean w)
    have hp : positiveWeightMass (normalizeWeight w) = 0 := by linarith
    have habs : |weightMean w| = 0 := by linarith
    exact ⟨hp, abs_eq_zero.mp habs⟩
  have hle : ∀ i, normalizeWeight w i ≤ 0 := by
    intro i
    have hterm_le : max (normalizeWeight w i) 0 ≤
        positiveWeightMass (normalizeWeight w) := by
      unfold positiveWeightMass
      exact Finset.single_le_sum
        (fun j _ => le_max_right (normalizeWeight w j) 0)
        (Finset.mem_univ i)
    have hterm_nonneg : 0 ≤ max (normalizeWeight w i) 0 := le_max_right _ _
    have hterm : max (normalizeWeight w i) 0 = 0 := by linarith [hparts.1]
    exact max_eq_right_iff.mp hterm
  have heq : ∀ i, normalizeWeight w i = 0 := by
    intro i
    have hrest : (∑ j ∈ Finset.univ.erase i, normalizeWeight w j) ≤ 0 := by
      exact Finset.sum_nonpos fun j _ => hle j
    have hsplit :
        (∑ j ∈ Finset.univ.erase i, normalizeWeight w j) +
            normalizeWeight w i = 0 := by
      calc
        (∑ j ∈ Finset.univ.erase i, normalizeWeight w j) +
              normalizeWeight w i = ∑ j, normalizeWeight w j := by
            exact Finset.sum_erase_add Finset.univ (normalizeWeight w) (Finset.mem_univ i)
        _ = 0 := hnorm
    have hge : 0 ≤ normalizeWeight w i := by linarith
    exact le_antisymm (hle i) hge
  apply hw
  funext i
  calc
    w i = normalizeWeight w i + weightMean w :=
      (normalizeWeight_add_mean w i).symm
    _ = 0 := by rw [heq i, hparts.2, add_zero]

lemma weightCoercivityGauge_smul
    {r : Real} (hr : 0 ≤ r) (w : Fin n → Real) :
    weightCoercivityGauge (fun i => r * w i) = r * weightCoercivityGauge w := by
  have hmean : weightMean (fun i => r * w i) = r * weightMean w := by
    unfold weightMean weightSum
    rw [← Finset.mul_sum]
    ring
  have hnorm : normalizeWeight (fun i => r * w i) =
      fun i => r * normalizeWeight w i := by
    funext i
    simp only [normalizeWeight_apply, hmean]
    ring
  have hmax : ∀ i, max (r * normalizeWeight w i) 0 =
      r * max (normalizeWeight w i) 0 := by
    intro i
    rcases le_total 0 (normalizeWeight w i) with hi | hi
    · rw [max_eq_left hi, max_eq_left (mul_nonneg hr hi)]
    · rw [max_eq_right hi, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hr hi)]
      simp
  unfold weightCoercivityGauge positiveWeightMass
  rw [hnorm, hmean, abs_mul, abs_of_nonneg hr]
  simp_rw [hmax]
  rw [← Finset.mul_sum]
  ring

/-- The coercivity gauge has a positive lower bound on the Euclidean unit sphere. -/
theorem exists_positive_gauge_lower_bound_on_sphere
    (hn : 0 < n) :
    ∃ c : Real, 0 < c ∧
      ∀ x : WeightE n, ‖x‖ = 1 →
        c ≤ weightCoercivityGauge (fun i => x i) := by
  have hcont := continuous_weightCoercivityGauge (n := n)
  obtain ⟨x0, hx0⟩ := IsCompact.exists_isMinOn
    (isCompact_sphere (0 : WeightE n) 1)
    (by
      let i0 : Fin n := ⟨0, hn⟩
      refine ⟨EuclideanSpace.single i0 1, ?_⟩
      simp)
    hcont.continuousOn
  refine ⟨weightCoercivityGauge (fun i => x0 i), ?_, ?_⟩
  · apply weightCoercivityGauge_pos_of_ne_zero hn
    intro hzero
    have hxzero : (x0 : WeightE n) = 0 := by
      ext i
      exact congrFun hzero i
    have hxmem := hx0.1
    simp [hxzero] at hxmem
  · intro x hx
    exact hx0.2 (by simpa [Metric.mem_sphere, dist_eq_norm] using hx)

/-- The augmented deviation field on the full Euclidean weight space. -/
noncomputable def augmentedAreaDeviation
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (w : WeightE n) : WeightE n :=
  (WithLp.equiv 2 (Fin n → Real)).symm fun i =>
    areaDeviation K s (normalizeWeight fun j => w j) i +
      weightMean (fun j => w j)

@[simp] lemma augmentedAreaDeviation_apply
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (w : WeightE n) (i : Fin n) :
    augmentedAreaDeviation K s w i =
      areaDeviation K s (normalizeWeight fun j => w j) i +
        weightMean (fun j => w j) := rfl

lemma continuous_augmentedAreaDeviation
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hs : Function.Injective s) :
    Continuous (augmentedAreaDeviation K s) := by
  apply continuous_induced_rng.2
  apply continuous_pi
  intro i
  dsimp [augmentedAreaDeviation, normalizeWeight, weightMean]
  have hcoord (k : Fin n) : Continuous (fun w : WeightE n => w k) :=
    (continuous_apply k).comp continuous_induced_dom
  have hsum : Continuous (fun w : WeightE n => ∑ k : Fin n, w k) :=
    continuous_finsetSum (Finset.univ : Finset (Fin n)) fun k _ => hcoord k
  have hnorm : Continuous (fun w : WeightE n => (fun j => w j - (∑ k, w k) / (n : ℝ))) := by
    apply continuous_pi
    intro j
    exact (hcoord j).sub (hsum.div_const (n : ℝ))
  have hdev : Continuous (fun w : WeightE n => areaDeviation K s (fun j => w j - (∑ k, w k) / (n
    : ℝ)) i) :=
    ((continuous_apply i).comp (continuous_areaDeviation_weights K s hs)).comp hnorm
  have hmean : Continuous (fun w : WeightE n => (∑ k, w k) / (n : ℝ)) :=
    hsum.div_const (n : ℝ)
  exact hdev.add hmean

lemma augmentedPairing_eq
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hn : 0 < n) (hs : Function.Injective s)
    (w : WeightE n) :
    inner Real w (augmentedAreaDeviation K s w) =
      deviationPairing K s (normalizeWeight fun i => w i) +
        (n : Real) * (weightMean fun i => w i) ^ 2 := by
  let u : Fin n → Real := normalizeWeight fun i => w i
  let m : Real := weightMean fun i => w i
  have hu : WeightNormalized u := WeightNormalized_normalizeWeight _ hn
  have hdev : ∑ i, areaDeviation K s u i = 0 :=
    sum_areaDeviation_eq_zero K s u hn hs
  have hsumu : ∑ i, u i = 0 := hu
  have hwdecomp : ∀ i, w i = u i + m := by
    intro i
    exact (normalizeWeight_add_mean (fun j => w j) i).symm
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    augmentedAreaDeviation_apply]
  change (∑ i, (areaDeviation K s u i + m) * w i) =
    deviationPairing K s u + (n : Real) * m ^ 2
  unfold deviationPairing
  calc
    (∑ i, (areaDeviation K s u i + m) * w i) =
        ∑ i, (areaDeviation K s u i + m) * (u i + m) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hwdecomp i]
    _ = (∑ i, u i * areaDeviation K s u i) +
          m * (∑ i, areaDeviation K s u i) +
          m * (∑ i, u i) +
          ∑ _i : Fin n, m ^ 2 := by
      simp_rw [show ∀ i : Fin n,
          (areaDeviation K s u i + m) * (u i + m) =
            u i * areaDeviation K s u i +
              m * areaDeviation K s u i + m * u i + m ^ 2 by
        intro i
        ring]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = (∑ i, u i * areaDeviation K s u i) + (n : Real) * m ^ 2 := by
      rw [hdev, hsumu]
      simp [Finset.sum_const, nsmul_eq_mul]

lemma augmentedAreaDeviation_zero_gives_equalArea
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hn : 0 < n) (hs : Function.Injective s)
    (w : WeightE n)
    (hw : augmentedAreaDeviation K s w = 0) :
    IsEqualAreaWeight K s (normalizeWeight fun i => w i) := by
  have hcoord : ∀ i, areaDeviation K s (normalizeWeight fun j => w j) i +
      weightMean (fun j => w j) = 0 := by
    intro i
    have := congrArg (fun z : WeightE n => z i) hw
    simpa using this
  have hsum := congrArg (fun f : Fin n → Real => ∑ i, f i)
    (funext hcoord)
  have hdev : ∑ i, areaDeviation K s (normalizeWeight fun j => w j) i = 0 :=
    sum_areaDeviation_eq_zero K s _ hn hs
  have hmean : weightMean (fun j => w j) = 0 := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hsum
    have hnR : (n : Real) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    rw [hdev, zero_add] at hsum
    have hsum' : (n : Real) * weightMean (fun j => w j) = 0 := by
      simpa using hsum
    exact (mul_eq_zero.mp hsum').resolve_left hnR
  intro i
  have hi := hcoord i
  rw [hmean, add_zero] at hi
  simp only [areaDeviation_apply, sub_eq_zero] at hi
  simpa [equalAreaTarget] using hi

end EMP
end NRR

namespace NRR
namespace EMP

open Geometry RealInnerProductSpace

variable {n : Nat}

private abbrev WeightE' (n : Nat) := EuclideanSpace Real (Fin n)

lemma max_normalized_weight_nonneg
    (hn : 0 < n) (w : Fin n → Real)
    (k : Fin n) (hk : ∀ i, w i ≤ w k)
    (hw : WeightNormalized w) :
    0 ≤ w k := by
  by_contra hkneg
  have hklt : w k < 0 := lt_of_not_ge hkneg
  have hall : ∀ i, w i < 0 := fun i => lt_of_le_of_lt (hk i) hklt
  have hsumneg : ∑ i, w i < 0 := by
    have hle : ∀ i ∈ (Finset.univ : Finset (Fin n)), w i ≤ 0 := by
      intro i hi
      exact le_of_lt (hall i)
    have hlt : ∃ i ∈ (Finset.univ : Finset (Fin n)), w i < 0 :=
      ⟨⟨0, hn⟩, Finset.mem_univ _, hall ⟨0, hn⟩⟩
    simpa using Finset.sum_lt_sum hle hlt
  have hsumzero : ∑ i, w i = 0 := by
    simpa [WeightNormalized, weightSum] using hw
  linarith

lemma positiveWeightMass_le_card_mul_max
    (hn : 0 < n) (w : Fin n → Real)
    (k : Fin n) (hk : ∀ i, w i ≤ w k)
    (hw : WeightNormalized w) :
    positiveWeightMass w ≤ (n : Real) * w k := by
  have hk0 := max_normalized_weight_nonneg hn w k hk hw
  unfold positiveWeightMass
  calc
    ∑ i, max (w i) 0 ≤ ∑ _i : Fin n, w k := by
      apply Finset.sum_le_sum
      intro i _
      exact max_le (hk i) hk0
    _ = (n : Real) * w k := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_comm]

lemma augmentedPairing_pos_of_gauge_large
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hn : 0 < n) (hs : Function.Injective s)
    (w : WeightE' n)
    (hlarge :
      (n : Real) * (powerGapBound K s + 1) +
          (powerGapBound K s * K.area + 1) <
        weightCoercivityGauge (fun i => w i)) :
    0 < inner Real w (augmentedAreaDeviation K s w) := by
  let u : Fin n → Real := normalizeWeight fun i => w i
  let m : Real := weightMean fun i => w i
  have hu : WeightNormalized u := WeightNormalized_normalizeWeight _ hn
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ u
    ⟨(⟨0, hn⟩ : Fin n), Finset.mem_univ _⟩
  have hkmax : ∀ i, u i ≤ u k := fun i => hk i (Finset.mem_univ i)
  have hk0 : 0 ≤ u k := max_normalized_weight_nonneg hn u k hkmax hu
  have hdevLB := deviationPairing_lower_bound_of_max K s hn hs u hu k
  have hK0 : 0 ≤ K.area := le_of_lt (SolidConvexBody.ofConvexBody K).area_pos
  have hC0 : 0 ≤ powerGapBound K s := powerGapBound_nonneg K s
  have hsplit :
      (n : Real) * (powerGapBound K s + 1) < positiveWeightMass u ∨
      powerGapBound K s * K.area + 1 < |m| := by
    unfold weightCoercivityGauge at hlarge
    exact lt_or_lt_of_add_lt_add hlarge
  rw [augmentedPairing_eq K s hn hs w]
  rcases hsplit with hmass | hmean
  · have hmassUB := positiveWeightMass_le_card_mul_max hn u k hkmax hu
    have hnR : 0 < (n : Real) := Nat.cast_pos.mpr hn
    have hklarge : powerGapBound K s < u k := by
      nlinarith
    have hdevpos := deviationPairing_pos_of_max_gt K s hn hs u hu k hklarge
    positivity
  · have hmSq : powerGapBound K s * K.area < m ^ 2 := by
      have hB : 0 ≤ powerGapBound K s * K.area := mul_nonneg hC0 hK0
      have habs0 : 0 ≤ |m| := abs_nonneg m
      nlinarith [sq_abs m]
    have hnR : 1 ≤ (n : Real) := by exact_mod_cast hn
    have hdevCoarse : -(powerGapBound K s * K.area) ≤ deviationPairing K s u := by
      calc
        -(powerGapBound K s * K.area) ≤
            (u k - powerGapBound K s) * K.area := by
              nlinarith
        _ ≤ deviationPairing K s u := hdevLB
    nlinarith

/-- A radius on which the augmented area-deviation field is strictly outward. -/
noncomputable def equalAreaOutwardRadius
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hn : 0 < n) : Real :=
  let c := Classical.choose (exists_positive_gauge_lower_bound_on_sphere hn)
  let T := (n : Real) * (powerGapBound K s + 1) +
    (powerGapBound K s * K.area + 1)
  (T + 1) / c

lemma equalAreaOutwardRadius_pos
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hn : 0 < n) :
    0 < equalAreaOutwardRadius K s hn := by
  let c := Classical.choose (exists_positive_gauge_lower_bound_on_sphere hn)
  have hc : 0 < c := (Classical.choose_spec
    (exists_positive_gauge_lower_bound_on_sphere hn)).1
  have hC0 := powerGapBound_nonneg K s
  have hK0 : 0 ≤ K.area := le_of_lt (SolidConvexBody.ofConvexBody K).area_pos
  unfold equalAreaOutwardRadius
  dsimp only
  positivity

lemma augmentedAreaDeviation_outward_on_radius
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane)
    (hn : 0 < n) (hs : Function.Injective s)
    (x : WeightE' n) (hx : ‖x‖ = 1) :
    0 < inner Real x
      (augmentedAreaDeviation K s
        (equalAreaOutwardRadius K s hn • x)) := by
  have h_gauge : weightCoercivityGauge (fun i => (equalAreaOutwardRadius K s hn • x) i) > (n :
    ℝ) * (powerGapBound K s + 1) + (powerGapBound K s * K.area + 1) := by
    have h_gauge_eq : weightCoercivityGauge (fun i => (equalAreaOutwardRadius K s hn • x) i) =
      (equalAreaOutwardRadius K s hn) * weightCoercivityGauge (fun i => x i) := by
      have h1 : (fun i => (equalAreaOutwardRadius K s hn • x) i) = (equalAreaOutwardRadius K s
        hn) • (fun i => x i) := rfl
      rw [h1]
      exact weightCoercivityGauge_smul (equalAreaOutwardRadius_pos K s hn |> le_of_lt) (fun i =>
        x i)
    have hspec := Classical.choose_spec (exists_positive_gauge_lower_bound_on_sphere hn)
    have hx_lb := hspec.2 x hx
    rw [h_gauge_eq]
    unfold equalAreaOutwardRadius
    have hpos_min := hspec.1
    have hT_nonneg : 0 ≤ (n : ℝ) * (powerGapBound K s + 1) + (powerGapBound K s * K.area + 1) :=
      add_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (add_nonneg (powerGapBound_nonneg K s) zero_le_one))
        (add_nonneg (mul_nonneg (powerGapBound_nonneg K s) K.area_nonneg) zero_le_one)
    have hG_ge : ((n : ℝ) * (powerGapBound K s + 1) + (powerGapBound K s * K.area + 1) + 1) /
      Classical.choose (exists_positive_gauge_lower_bound_on_sphere hn) * Classical.choose
      (exists_positive_gauge_lower_bound_on_sphere hn)
        ≤ ((n : ℝ) * (powerGapBound K s + 1) + (powerGapBound K s * K.area + 1) + 1) /
          Classical.choose (exists_positive_gauge_lower_bound_on_sphere hn) *
          weightCoercivityGauge (fun i => x i) :=
      mul_le_mul_of_nonneg_left hx_lb (div_nonneg (by linarith) (le_of_lt hpos_min))
    have h_cancel : ((n : ℝ) * (powerGapBound K s + 1) + (powerGapBound K s * K.area + 1) + 1) /
      Classical.choose (exists_positive_gauge_lower_bound_on_sphere hn) * Classical.choose
      (exists_positive_gauge_lower_bound_on_sphere hn)
        = (n : ℝ) * (powerGapBound K s + 1) + (powerGapBound K s * K.area + 1) + 1 :=
      div_mul_cancel₀ _ (ne_of_gt hpos_min)
    linarith
  have hpos := NRR.EMP.augmentedPairing_pos_of_gauge_large K s hn hs (equalAreaOutwardRadius K s
    hn • x) h_gauge
  rw [inner_smul_left] at hpos
  exact (mul_pos_iff_of_pos_left (equalAreaOutwardRadius_pos K s hn)).mp hpos

end EMP
end NRR
