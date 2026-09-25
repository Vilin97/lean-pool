/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.PointwiseSplits

/-! # Descendant Cardinality -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section52

open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section
/-!
# Section 5.2 internals: GeometrySeries

Descendant geometry, geometric series, and small-tail estimates.
-/

/-- Cardinality of scale-`n` descendants of `cu_m`. -/
theorem section52_descendantsAtScale_originCube_large_card
    (d m : ℕ) {n : ℤ} (hn : n ≤ (m : ℤ)) :
    (descendantsAtScale (originCube d (m : ℤ)) n).card =
      (3 ^ d) ^ Int.toNat ((m : ℤ) - n) := by
  rw [descendantsAtScale_eq_descendantsAtDepth (originCube d (m : ℤ)) hn]
  exact descendantsAtDepth_card (originCube d (m : ℤ)) (Int.toNat ((m : ℤ) - n))

/-- Real `1 / xi` root of the number of scale-`n` descendants of `cu_m`. -/
theorem section52_descendantsAtScale_originCube_large_card_rpow
    (d ξ m : ℕ) {n : ℤ} (hn : n ≤ (m : ℤ)) :
    (((descendantsAtScale (originCube d (m : ℤ)) n).card : ℝ) ^
        (1 / (ξ : ℝ))) =
      Real.rpow (3 : ℝ)
        (((d : ℝ) / (ξ : ℝ)) * (Int.toNat ((m : ℤ) - n) : ℝ)) := by
  have h3_nonneg : 0 ≤ (3 : ℝ) := by norm_num
  rw [section52_descendantsAtScale_originCube_large_card d m hn]
  have hcast :
      (((3 ^ d) ^ Int.toNat ((m : ℤ) - n) : ℕ) : ℝ) =
        ((3 : ℝ) ^ (d * Int.toNat ((m : ℤ) - n))) := by
    rw [Nat.cast_pow, Nat.cast_pow]
    rw [← pow_mul]
    norm_num
  rw [hcast]
  rw [← Real.rpow_natCast (3 : ℝ) (d * Int.toNat ((m : ℤ) - n))]
  rw [← Real.rpow_mul h3_nonneg]
  congr 1
  rw [Nat.cast_mul]
  ring_nf

/-- Cardinality of unit descendants of a nonnegative-scale origin cube. -/
theorem section52_descendantsAtScale_originCube_int_zero_card
    (d : ℕ) {n : ℤ} (hn : 0 ≤ n) :
    (descendantsAtScale (originCube d n) 0).card =
      (3 ^ d) ^ Int.toNat n := by
  rw [descendantsAtScale_eq_descendantsAtDepth (originCube d n) hn]
  simpa [originCube] using descendantsAtDepth_card (originCube d n) (Int.toNat n)

/-- Real `1 / xi` root of the number of unit descendants of a scale-`n` cube. -/
theorem section52_descendantsAtScale_originCube_int_zero_card_rpow
    (d ξ : ℕ) {n : ℤ} (hn : 0 ≤ n) :
    (((descendantsAtScale (originCube d n) 0).card : ℝ) ^
        (1 / (ξ : ℝ))) =
      Real.rpow (3 : ℝ) (((d : ℝ) / (ξ : ℝ)) * (Int.toNat n : ℝ)) := by
  have h3_nonneg : 0 ≤ (3 : ℝ) := by norm_num
  rw [section52_descendantsAtScale_originCube_int_zero_card d hn]
  have hcast :
      (((3 ^ d) ^ Int.toNat n : ℕ) : ℝ) =
        ((3 : ℝ) ^ (d * Int.toNat n)) := by
    rw [Nat.cast_pow, Nat.cast_pow]
    rw [← pow_mul]
    norm_num
  rw [hcast]
  rw [← Real.rpow_natCast (3 : ℝ) (d * Int.toNat n)]
  rw [← Real.rpow_mul h3_nonneg]
  congr 1
  rw [Nat.cast_mul]
  ring_nf

/-- Square root of the number of unit descendants of a scale-`n` cube. -/
theorem section52_descendantsAtScale_originCube_int_zero_card_sqrt
    (d : ℕ) {n : ℤ} (hn : 0 ≤ n) :
    Real.sqrt ((descendantsAtScale (originCube d n) 0).card : ℝ) =
      Real.rpow (3 : ℝ) (((d : ℝ) / 2) * (Int.toNat n : ℝ)) := by
  have h3_nonneg : 0 ≤ (3 : ℝ) := by norm_num
  rw [Real.sqrt_eq_rpow]
  rw [section52_descendantsAtScale_originCube_int_zero_card d hn]
  have hcast :
      (((3 ^ d) ^ Int.toNat n : ℕ) : ℝ) =
        ((3 : ℝ) ^ (d * Int.toNat n)) := by
    rw [Nat.cast_pow, Nat.cast_pow]
    rw [← pow_mul]
    norm_num
  rw [hcast]
  rw [← Real.rpow_natCast (3 : ℝ) (d * Int.toNat n)]
  rw [← Real.rpow_mul h3_nonneg]
  congr 1
  rw [Nat.cast_mul]
  ring_nf

/-- Inverse of the number of unit descendants of a nonnegative-scale origin cube. -/
theorem section52_descendantsAtScale_originCube_int_zero_card_inv
    (d : ℕ) {n : ℤ} (hn : 0 ≤ n) :
    (((descendantsAtScale (originCube d n) 0).card : ℝ)⁻¹) =
      Real.rpow (3 : ℝ) (-(d : ℝ) * (Int.toNat n : ℝ)) := by
  have h3_nonneg : 0 ≤ (3 : ℝ) := by norm_num
  rw [section52_descendantsAtScale_originCube_int_zero_card d hn]
  have hcast :
      (((3 ^ d) ^ Int.toNat n : ℕ) : ℝ) =
        ((3 : ℝ) ^ (d * Int.toNat n)) := by
    rw [Nat.cast_pow, Nat.cast_pow]
    rw [← pow_mul]
    norm_num
  rw [hcast]
  rw [← Real.rpow_natCast (3 : ℝ) (d * Int.toNat n)]
  rw [show ((d * Int.toNat n : ℕ) : ℝ) =
      (d : ℝ) * (Int.toNat n : ℝ) by rw [Nat.cast_mul]]
  simpa [neg_mul] using
    (Real.rpow_neg h3_nonneg ((d : ℝ) * (Int.toNat n : ℝ))).symm

/--
For manuscript large scales, the `q = 1` depth from `cu_m` to scale `n` plus
the absolute scale `n` is exactly `m`.
-/
theorem section52LargeScaleSet_toNat_sub_add_toNat
    {m : ℕ} {n : ℤ} (hn : n ∈ section52LargeScaleSet m) :
    Int.toNat ((m : ℤ) - n) + Int.toNat n = m := by
  rcases Finset.mem_image.mp hn with ⟨l, hl, rfl⟩
  have hl_le : l ≤ m := Nat.le_of_lt (Finset.mem_range.mp hl)
  have hsub :
      Int.toNat ((m : ℤ) - ((m : ℤ) - (l : ℤ))) = l := by
    have hdiff : (m : ℤ) - ((m : ℤ) - (l : ℤ)) = (l : ℤ) := by ring
    simp [hdiff]
  have hscale :
      Int.toNat ((m : ℤ) - (l : ℤ)) = m - l := by
    have hsub_int : (m : ℤ) - (l : ℤ) = ((m - l : ℕ) : ℤ) := by
      omega
    rw [hsub_int]
    simp
  rw [hsub, hscale]
  omega

/-- `Int.toNat` is injective on the nonnegative manuscript large scales. -/
theorem section52LargeScaleSet_toNat_injOn (m : ℕ) :
    Set.InjOn Int.toNat (↑(section52LargeScaleSet m) : Set ℤ) := by
  intro n hn k hk hnk
  have hn_nonneg : 0 ≤ n := section52LargeScaleSet_mem_nonneg hn
  have hk_nonneg : 0 ≤ k := section52LargeScaleSet_mem_nonneg hk
  have hn_cast : ((Int.toNat n : ℕ) : ℤ) = n :=
    Int.toNat_of_nonneg hn_nonneg
  have hk_cast : ((Int.toNat k : ℕ) : ℤ) = k :=
    Int.toNat_of_nonneg hk_nonneg
  omega

/-- The raw geometric powers underlying `q = 1` normalized weights are summable. -/
theorem summable_rpow_three_neg_mul_nat {gap : ℝ} (hgap : 0 < gap) :
    Summable (fun n : ℕ => Real.rpow (3 : ℝ) (-gap * (n : ℝ))) := by
  have hdisc_pos : 0 < geometricDiscount gap 1 :=
    geometricDiscount_pos (by simpa using hgap)
  refine
    ((summable_geometricWeight_one hgap).mul_left
      ((geometricDiscount gap 1)⁻¹)).congr ?_
  intro n
  rw [geometricWeight_one_eq]
  field_simp [hdisc_pos.ne']

/-- Closed form of the raw `q = 1` geometric-power series. -/
theorem tsum_rpow_three_neg_mul_nat_eq_inv_geometricDiscount {gap : ℝ}
    (hgap : 0 < gap) :
    (∑' n : ℕ, Real.rpow (3 : ℝ) (-gap * (n : ℝ))) =
      (geometricDiscount gap 1)⁻¹ := by
  have hdisc_pos : 0 < geometricDiscount gap 1 :=
    geometricDiscount_pos (by simpa using hgap)
  calc
    (∑' n : ℕ, Real.rpow (3 : ℝ) (-gap * (n : ℝ))) =
        ∑' n : ℕ, (geometricDiscount gap 1)⁻¹ * geometricWeight gap 1 n := by
          refine tsum_congr ?_
          intro n
          rw [geometricWeight_one_eq]
          field_simp [hdisc_pos.ne']
    _ = (geometricDiscount gap 1)⁻¹ *
        ∑' n : ℕ, geometricWeight gap 1 n := by
          rw [tsum_mul_left]
    _ = (geometricDiscount gap 1)⁻¹ := by
          rw [tsum_geometricWeight_one_eq_one hgap, mul_one]

theorem section52SmallTailWeight_eq_rpow {s : ℝ} (hs : 0 < s) (m : ℕ) :
    section52SmallTailWeight s m =
      Real.rpow (3 : ℝ) (-s * (m : ℝ)) := by
  unfold section52SmallTailWeight
  have h3 : 0 < (3 : ℝ) := by norm_num
  have hdisc_pos : 0 < geometricDiscount s 1 :=
    geometricDiscount_pos (by simpa using hs)
  calc
    (∑' j : ℕ, geometricWeight s 1 (j + m)) =
        ∑' j : ℕ,
          geometricDiscount s 1 *
            Real.rpow (3 : ℝ) (-s * ((j + m : ℕ) : ℝ)) := by
          refine tsum_congr ?_
          intro j
          rw [geometricWeight_one_eq]
    _ =
        ∑' j : ℕ,
          (geometricDiscount s 1 *
            Real.rpow (3 : ℝ) (-s * (m : ℝ))) *
            Real.rpow (3 : ℝ) (-s * (j : ℝ)) := by
          refine tsum_congr ?_
          intro j
          calc
            geometricDiscount s 1 *
                Real.rpow (3 : ℝ) (-s * ((j + m : ℕ) : ℝ)) =
              geometricDiscount s 1 *
                Real.rpow (3 : ℝ) (-s * (m : ℝ) + -s * (j : ℝ)) := by
                congr 1
                norm_num
                ring_nf
            _ =
              geometricDiscount s 1 *
                (Real.rpow (3 : ℝ) (-s * (m : ℝ)) *
                  Real.rpow (3 : ℝ) (-s * (j : ℝ))) := by
                exact congrArg (fun t => geometricDiscount s 1 * t)
                  (Real.rpow_add h3 (-s * (m : ℝ)) (-s * (j : ℝ)))
            _ =
              (geometricDiscount s 1 *
                Real.rpow (3 : ℝ) (-s * (m : ℝ))) *
                Real.rpow (3 : ℝ) (-s * (j : ℝ)) := by ring
    _ =
        (geometricDiscount s 1 *
          Real.rpow (3 : ℝ) (-s * (m : ℝ))) *
          ∑' j : ℕ, Real.rpow (3 : ℝ) (-s * (j : ℝ)) := by
          rw [tsum_mul_left]
    _ =
        (geometricDiscount s 1 *
          Real.rpow (3 : ℝ) (-s * (m : ℝ))) *
          (geometricDiscount s 1)⁻¹ := by
          rw [tsum_rpow_three_neg_mul_nat_eq_inv_geometricDiscount hs]
    _ = Real.rpow (3 : ℝ) (-s * (m : ℝ)) := by
          field_simp [hdisc_pos.ne']

/--
The finite manuscript large-scale set is dominated by the full raw geometric
tail with the same positive gap.
-/
theorem section52LargeScaleSet_raw_rpow_sum_le_inv_geometricDiscount
    {gap : ℝ} (m : ℕ) (hgap : 0 < gap) :
    (∑ n ∈ section52LargeScaleSet m,
        Real.rpow (3 : ℝ) (-gap * (Int.toNat n : ℝ))) ≤
      (geometricDiscount gap 1)⁻¹ := by
  classical
  have hraw_summable := summable_rpow_three_neg_mul_nat hgap
  have hsum_image :
      (∑ n ∈ section52LargeScaleSet m,
          Real.rpow (3 : ℝ) (-gap * (Int.toNat n : ℝ))) =
        ∑ k ∈ (section52LargeScaleSet m).image Int.toNat,
          Real.rpow (3 : ℝ) (-gap * (k : ℝ)) := by
    rw [Finset.sum_image]
    · exact section52LargeScaleSet_toNat_injOn m
  rw [hsum_image]
  calc
    (∑ k ∈ (section52LargeScaleSet m).image Int.toNat,
        Real.rpow (3 : ℝ) (-gap * (k : ℝ))) ≤
        ∑' k : ℕ, Real.rpow (3 : ℝ) (-gap * (k : ℝ)) :=
          hraw_summable.sum_le_tsum
            ((section52LargeScaleSet m).image Int.toNat)
            (fun k _hk => Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    _ = (geometricDiscount gap 1)⁻¹ :=
          tsum_rpow_three_neg_mul_nat_eq_inv_geometricDiscount hgap

/-- A one-step geometric discount is always at most one. -/
theorem geometricDiscount_one_le_one (s : ℝ) :
    geometricDiscount s 1 ≤ 1 := by
  unfold geometricDiscount
  have hpow_nonneg : 0 ≤ Real.rpow (3 : ℝ) (-s * 1) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  linarith

theorem geometricWeight_one_le_inv_discount_mul_gap_decay_mul_geometricWeight
    {s r : ℝ} (hs : 0 < s) (_hsr : s < r) (N : ℕ) :
    geometricWeight r 1 N ≤
      (geometricDiscount s 1)⁻¹ *
        Real.rpow (3 : ℝ) (-(r - s) * (N : ℝ)) *
          geometricWeight s 1 N := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  have hdisc_s_pos : 0 < geometricDiscount s 1 :=
    geometricDiscount_pos (by simpa using hs)
  have hdisc_r_le_one : geometricDiscount r 1 ≤ 1 :=
    geometricDiscount_one_le_one r
  have hpow_r_nonneg :
      0 ≤ Real.rpow (3 : ℝ) (-r * (N : ℝ)) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hpow_eq :
      Real.rpow (3 : ℝ) (-(r - s) * (N : ℝ)) *
          Real.rpow (3 : ℝ) (-s * (N : ℝ)) =
        Real.rpow (3 : ℝ) (-r * (N : ℝ)) := by
    calc
      Real.rpow (3 : ℝ) (-(r - s) * (N : ℝ)) *
          Real.rpow (3 : ℝ) (-s * (N : ℝ)) =
        Real.rpow (3 : ℝ)
          (-(r - s) * (N : ℝ) + -s * (N : ℝ)) := by
          exact (Real.rpow_add h3 (-(r - s) * (N : ℝ)) (-s * (N : ℝ))).symm
      _ = Real.rpow (3 : ℝ) (-r * (N : ℝ)) := by
          congr 1
          ring
  have hpow_eq' :
      Real.rpow (3 : ℝ) (-(r * (N : ℝ))) =
        Real.rpow (3 : ℝ) (-((N : ℝ) * (r - s))) *
          Real.rpow (3 : ℝ) (-((N : ℝ) * s)) := by
    rw [show -(r * (N : ℝ)) = -r * (N : ℝ) by ring]
    rw [← hpow_eq]
    congr 2 <;> ring
  calc
    geometricWeight r 1 N =
        geometricDiscount r 1 * Real.rpow (3 : ℝ) (-r * (N : ℝ)) := by
          rw [geometricWeight_one_eq]
    _ ≤ 1 * Real.rpow (3 : ℝ) (-r * (N : ℝ)) :=
          mul_le_mul_of_nonneg_right hdisc_r_le_one hpow_r_nonneg
    _ =
        (geometricDiscount s 1)⁻¹ *
          Real.rpow (3 : ℝ) (-(r - s) * (N : ℝ)) *
            geometricWeight s 1 N := by
          rw [geometricWeight_one_eq]
          field_simp [hdisc_s_pos.ne']
          exact hpow_eq'

theorem inv_geometricDiscount_one_le_five_inv_of_pos_lt_one
  {s : ℝ} (hs : 0 < s) (hs_lt_one : s < 1) :
    (geometricDiscount s 1)⁻¹ ≤ 5 * s⁻¹ :=
  Book.Ch02.inv_geometricDiscount_le_five_inv
    (s := s) (p := 1) hs hs_lt_one.le (by norm_num)

theorem upper_unitCube_source_rpow_half_nonneg
    {d : ℕ} [NeZero d] (m : ℕ) {s : ℝ} (hs : 0 < s) (a : RegCoeffField d) :
    0 ≤
      Real.rpow
        ((descendantsAtScale (originCube d (m : ℤ)) 0).sup'
          (descendantsAtScale_nonempty (originCube d (m : ℤ))
            (by simp [originCube]))
          (fun U => Ch04.LambdaSqCoeffField U s (.finite 1) a))
        (1 / 2 : ℝ) := by
  exact Real.rpow_nonneg (by
    classical
    let D : Finset (TriadicCube d) := descendantsAtScale (originCube d (m : ℤ)) 0
    let hD : D.Nonempty := descendantsAtScale_nonempty (originCube d (m : ℤ))
      (by simp [originCube])
    rcases hD with ⟨U, hU⟩
    exact
      (Ch04.LambdaSqCoeffField_finite_nonneg U a hs
        (by norm_num : (1 : ℝ) ≤ 1)).trans
        (Finset.le_sup'
          (s := D) (f := fun U => Ch04.LambdaSqCoeffField U s (.finite 1) a) hU)) _

theorem lower_unitCube_source_rpow_half_nonneg
    {d : ℕ} [NeZero d] (m : ℕ) {s : ℝ} (hs : 0 < s) (a : RegCoeffField d) :
    0 ≤
      Real.rpow
        ((descendantsAtScale (originCube d (m : ℤ)) 0).sup'
          (descendantsAtScale_nonempty (originCube d (m : ℤ))
            (by simp [originCube]))
          (fun U => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹))
        (1 / 2 : ℝ) := by
  exact Real.rpow_nonneg (by
    classical
    let D : Finset (TriadicCube d) := descendantsAtScale (originCube d (m : ℤ)) 0
    let hD : D.Nonempty := descendantsAtScale_nonempty (originCube d (m : ℤ))
      (by simp [originCube])
    rcases hD with ⟨U, hU⟩
    exact
      (inv_nonneg.mpr
        (Ch04.lambdaSqCoeffField_finite_nonneg U a hs
          (by norm_num : (1 : ℝ) ≤ 1))).trans
        (Finset.le_sup'
          (s := D)
          (f := fun U => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹) hU)) _

theorem translateCube_originCube_zero_eq_of_scale_zero
    {d : ℕ} (Q : TriadicCube d) (hQ : Q.scale = 0) :
    translateCube (Book.Ch04.scaleTranslationShift 0 Q) (originCube d 0) = Q := by
  cases Q with
  | mk scale index =>
      change scale = 0 at hQ
      subst scale
      simp [originCube, translateCube, Book.Ch04.scaleTranslationShift]

theorem upper_unitDescendantSup_momentRoot_le_card_mul_origin
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {s : ℝ} {ξ m : ℕ} (hs : 0 < s) (hξ_one : 1 ≤ ξ)
    (hSourceInt :
      Integrable
        (fun a : RegCoeffField d =>
          (Ch04.LambdaSqCoeffField (originCube d 0) s (.finite 1) a) ^ ξ) P) :
    let D := descendantsAtScale (originCube d (m : ℤ)) 0
    let hD : D.Nonempty :=
      descendantsAtScale_nonempty (originCube d (m : ℤ)) (by simp [originCube])
    Ch04.annealedMomentRoot P ξ
      (fun a : RegCoeffField d =>
        D.sup' hD (fun U => Ch04.LambdaSqCoeffField U s (.finite 1) a)) ≤
      (D.card : ℝ) ^ (1 / (ξ : ℝ)) *
        Ch04.LambdaMomentAtScale P 0 s ξ := by
  classical
  intro D hD
  let : IsProbabilityMeasure P := hP.isProbability
  let X : TriadicCube d → RegCoeffField d → ℝ :=
    fun U a => Ch04.LambdaSqCoeffField U s (.finite 1) a
  let X0 : RegCoeffField d → ℝ :=
    fun a => Ch04.LambdaSqCoeffField (originCube d 0) s (.finite 1) a
  have hK_nonneg : 0 ≤ Ch04.LambdaMomentAtScale P 0 s ξ :=
    Ch04.LambdaMomentAtScale_nonneg P 0 ξ hs
  have hX_nonneg : ∀ U ∈ D, ∀ a, 0 ≤ X U a := by
    intro U _hU a
    exact Ch04.LambdaSqCoeffField_finite_nonneg U a hs
      (by norm_num : (1 : ℝ) ≤ 1)
  have hX_aemeas : ∀ U ∈ D, AEMeasurable (X U) P := by
    intro U _hU
    exact hP.aemeasurable_LambdaSqCoeffField_finite_one U hs
  have hX0_aemeas : AEMeasurable X0 P := by
    exact hP.aemeasurable_LambdaSqCoeffField_finite_one (originCube d 0) hs
  have hX0_abs_int : Integrable (fun a : RegCoeffField d => |X0 a| ^ ξ) P := by
    refine hSourceInt.congr ?_
    filter_upwards with a
    rw [abs_of_nonneg]
    exact Ch04.LambdaSqCoeffField_finite_nonneg (originCube d 0) a hs
      (by norm_num : (1 : ℝ) ≤ 1)
  have hX_int : ∀ U ∈ D, Integrable (fun a : RegCoeffField d => |X U a| ^ ξ) P := by
    intro U hU
    have hscale : U.scale = 0 := scale_eq_of_mem_descendantsAtScale hU
    let z : Fin d → ℤ := Book.Ch04.scaleTranslationShift 0 U
    have hUeq : U = translateCube z (originCube d 0) := by
      simpa [z] using (translateCube_originCube_zero_eq_of_scale_zero U hscale).symm
    have hae :
        (fun a : RegCoeffField d => X U a) =ᵐ[P]
          fun a => X0 (translateReg (intVecToRealVec z) a) := by
      have hcov :=
        Ch04.LambdaSqCoeffField_originCube_zero_translateByInt_ae
          hP hStruct.stationary z s (.finite 1)
      simpa [X, X0, hUeq] using hcov
    have hmap :
        Measure.map (X U) P = Measure.map X0 P := by
      calc
        Measure.map (X U) P =
            Measure.map (fun a : RegCoeffField d => X0 (translateReg (intVecToRealVec z) a)) P :=
              Measure.map_congr hae
        _ = Measure.map X0 (Measure.map (translateReg (intVecToRealVec z)) P) := by
              symm
              exact AEMeasurable.map_map_of_aemeasurable
                (by simpa [hStruct.stationary z] using hX0_aemeas)
                (measurable_translateReg (intVecToRealVec z)).aemeasurable
        _ = Measure.map X0 P := by
              rw [hStruct.stationary z]
    exact integrable_abs_pow_of_map_eq_map_aemeasurable
      (hX_aemeas U hU) hX0_aemeas hmap hX0_abs_int
  have hX_root :
      ∀ U ∈ D,
        (∫ a, |X U a| ^ ξ ∂P) ^ (1 / (ξ : ℝ)) ≤
          Ch04.LambdaMomentAtScale P 0 s ξ := by
    intro U hU
    have hscale : U.scale = 0 := scale_eq_of_mem_descendantsAtScale hU
    let z : Fin d → ℤ := Book.Ch04.scaleTranslationShift 0 U
    have hUeq : U = translateCube z (originCube d 0) := by
      simpa [z] using (translateCube_originCube_zero_eq_of_scale_zero U hscale).symm
    have hae :
        (fun a : RegCoeffField d => X U a) =ᵐ[P]
          fun a => X0 (translateReg (intVecToRealVec z) a) := by
      have hcov :=
        Ch04.LambdaSqCoeffField_originCube_zero_translateByInt_ae
          hP hStruct.stationary z s (.finite 1)
      simpa [X, X0, hUeq] using hcov
    have hmap :
        Measure.map (X U) P = Measure.map X0 P := by
      calc
        Measure.map (X U) P =
            Measure.map (fun a : RegCoeffField d => X0 (translateReg (intVecToRealVec z) a)) P :=
              Measure.map_congr hae
        _ = Measure.map X0 (Measure.map (translateReg (intVecToRealVec z)) P) := by
              symm
              exact AEMeasurable.map_map_of_aemeasurable
                (by simpa [hStruct.stationary z] using hX0_aemeas)
                (measurable_translateReg (intVecToRealVec z)).aemeasurable
        _ = Measure.map X0 P := by
              rw [hStruct.stationary z]
    have hint :
        ∫ a, |X U a| ^ ξ ∂P = ∫ a, |X0 a| ^ ξ ∂P :=
      integral_abs_pow_eq_of_map_eq_map_aemeasurable
        (hX_aemeas U hU) hX0_aemeas hmap
    calc
      (∫ a, |X U a| ^ ξ ∂P) ^ (1 / (ξ : ℝ))
          = (∫ a, |X0 a| ^ ξ ∂P) ^ (1 / (ξ : ℝ)) := by rw [hint]
      _ ≤ Ch04.LambdaMomentAtScale P 0 s ξ := by
            apply le_of_eq
            unfold Ch04.LambdaMomentAtScale Ch04.annealedMomentRoot X0
            congr 2 with a
            rw [abs_of_nonneg]
            exact Ch04.LambdaSqCoeffField_finite_nonneg (originCube d 0) a hs
              (by norm_num : (1 : ℝ) ≤ 1)
  have hsup :=
    Ch04.integral_finsetSup_abs_pow_rpow_inv_le_card_rpow_mul
      (μ := P) (s := D) hD (p := ξ)
      hξ_one hK_nonneg X hX_aemeas hX_int hX_root
  calc
    Ch04.annealedMomentRoot P ξ
        (fun a : RegCoeffField d =>
          D.sup' hD (fun U => Ch04.LambdaSqCoeffField U s (.finite 1) a))
        =
      (∫ a, (D.sup' hD (fun U => |X U a|)) ^ ξ ∂P) ^
          (1 / (ξ : ℝ)) := by
        unfold Ch04.annealedMomentRoot
        congr 2 with a
        congr 1
        apply le_antisymm
        · refine Finset.sup'_le hD _ ?_
          intro U hU
          calc
            X U a = |X U a| := (abs_of_nonneg (hX_nonneg U hU a)).symm
            _ ≤ D.sup' hD (fun U => |X U a|) :=
                Finset.le_sup' (f := fun U => |X U a|) hU
        · refine Finset.sup'_le hD _ ?_
          intro U hU
          calc
            |X U a| = X U a := abs_of_nonneg (hX_nonneg U hU a)
            _ ≤ D.sup' hD (fun U => X U a) :=
                Finset.le_sup' (f := fun U => X U a) hU
    _ ≤ (D.card : ℝ) ^ (1 / (ξ : ℝ)) *
        Ch04.LambdaMomentAtScale P 0 s ξ := hsup

theorem lower_unitDescendantSup_momentRoot_le_card_mul_origin
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    {s : ℝ} {ξ m : ℕ} (hs : 0 < s) (hξ_one : 1 ≤ ξ)
    (hSourceInt :
      Integrable
        (fun a : RegCoeffField d =>
          ((Ch04.lambdaSqCoeffField (originCube d 0) s (.finite 1) a)⁻¹) ^ ξ) P) :
    let D := descendantsAtScale (originCube d (m : ℤ)) 0
    let hD : D.Nonempty :=
      descendantsAtScale_nonempty (originCube d (m : ℤ)) (by simp [originCube])
    Ch04.annealedMomentRoot P ξ
      (fun a : RegCoeffField d =>
        D.sup' hD (fun U => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹)) ≤
      (D.card : ℝ) ^ (1 / (ξ : ℝ)) *
        Ch04.lambdaInvMomentAtScale P 0 s ξ := by
  classical
  intro D hD
  let : IsProbabilityMeasure P := hP.isProbability
  let X : TriadicCube d → RegCoeffField d → ℝ :=
    fun U a => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹
  let X0 : RegCoeffField d → ℝ :=
    fun a => (Ch04.lambdaSqCoeffField (originCube d 0) s (.finite 1) a)⁻¹
  have hK_nonneg : 0 ≤ Ch04.lambdaInvMomentAtScale P 0 s ξ :=
    Ch04.lambdaInvMomentAtScale_nonneg P 0 ξ hs
  have hX_nonneg : ∀ U ∈ D, ∀ a, 0 ≤ X U a := by
    intro U _hU a
    exact inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg U a hs
        (by norm_num : (1 : ℝ) ≤ 1))
  have hX_aemeas : ∀ U ∈ D, AEMeasurable (X U) P := by
    intro U _hU
    exact hP.aemeasurable_lambdaSqCoeffField_finite_one_inv U hs
  have hX0_aemeas : AEMeasurable X0 P := by
    exact hP.aemeasurable_lambdaSqCoeffField_finite_one_inv (originCube d 0) hs
  have hX0_abs_int : Integrable (fun a : RegCoeffField d => |X0 a| ^ ξ) P := by
    refine hSourceInt.congr ?_
    filter_upwards with a
    rw [abs_of_nonneg]
    exact inv_nonneg.mpr
      (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d 0) a hs
        (by norm_num : (1 : ℝ) ≤ 1))
  have hX_int : ∀ U ∈ D, Integrable (fun a : RegCoeffField d => |X U a| ^ ξ) P := by
    intro U hU
    have hscale : U.scale = 0 := scale_eq_of_mem_descendantsAtScale hU
    let z : Fin d → ℤ := Book.Ch04.scaleTranslationShift 0 U
    have hUeq : U = translateCube z (originCube d 0) := by
      simpa [z] using (translateCube_originCube_zero_eq_of_scale_zero U hscale).symm
    have hae :
        (fun a : RegCoeffField d => X U a) =ᵐ[P]
          fun a => X0 (translateReg (intVecToRealVec z) a) := by
      have hcov :=
        Ch04.lambdaSqCoeffField_originCube_zero_translateByInt_ae
          hP hStruct.stationary z s (.finite 1)
      filter_upwards [by simpa [X, X0, hUeq] using! hcov] with a ha
      simpa [X, X0, hUeq] using congrArg Inv.inv ha
    have hmap :
        Measure.map (X U) P = Measure.map X0 P := by
      calc
        Measure.map (X U) P =
            Measure.map (fun a : RegCoeffField d => X0 (translateReg (intVecToRealVec z) a)) P :=
              Measure.map_congr hae
        _ = Measure.map X0 (Measure.map (translateReg (intVecToRealVec z)) P) := by
              symm
              exact AEMeasurable.map_map_of_aemeasurable
                (by simpa [hStruct.stationary z] using hX0_aemeas)
                (measurable_translateReg (intVecToRealVec z)).aemeasurable
        _ = Measure.map X0 P := by
              rw [hStruct.stationary z]
    exact integrable_abs_pow_of_map_eq_map_aemeasurable
      (hX_aemeas U hU) hX0_aemeas hmap hX0_abs_int
  have hX_root :
      ∀ U ∈ D,
        (∫ a, |X U a| ^ ξ ∂P) ^ (1 / (ξ : ℝ)) ≤
          Ch04.lambdaInvMomentAtScale P 0 s ξ := by
    intro U hU
    have hscale : U.scale = 0 := scale_eq_of_mem_descendantsAtScale hU
    let z : Fin d → ℤ := Book.Ch04.scaleTranslationShift 0 U
    have hUeq : U = translateCube z (originCube d 0) := by
      simpa [z] using (translateCube_originCube_zero_eq_of_scale_zero U hscale).symm
    have hae :
        (fun a : RegCoeffField d => X U a) =ᵐ[P]
          fun a => X0 (translateReg (intVecToRealVec z) a) := by
      have hcov :=
        Ch04.lambdaSqCoeffField_originCube_zero_translateByInt_ae
          hP hStruct.stationary z s (.finite 1)
      filter_upwards [by simpa [X, X0, hUeq] using! hcov] with a ha
      simpa [X, X0, hUeq] using congrArg Inv.inv ha
    have hmap :
        Measure.map (X U) P = Measure.map X0 P := by
      calc
        Measure.map (X U) P =
            Measure.map (fun a : RegCoeffField d => X0 (translateReg (intVecToRealVec z) a)) P :=
              Measure.map_congr hae
        _ = Measure.map X0 (Measure.map (translateReg (intVecToRealVec z)) P) := by
              symm
              exact AEMeasurable.map_map_of_aemeasurable
                (by simpa [hStruct.stationary z] using hX0_aemeas)
                (measurable_translateReg (intVecToRealVec z)).aemeasurable
        _ = Measure.map X0 P := by
              rw [hStruct.stationary z]
    have hint :
        ∫ a, |X U a| ^ ξ ∂P = ∫ a, |X0 a| ^ ξ ∂P :=
      integral_abs_pow_eq_of_map_eq_map_aemeasurable
        (hX_aemeas U hU) hX0_aemeas hmap
    calc
      (∫ a, |X U a| ^ ξ ∂P) ^ (1 / (ξ : ℝ))
          = (∫ a, |X0 a| ^ ξ ∂P) ^ (1 / (ξ : ℝ)) := by rw [hint]
      _ ≤ Ch04.lambdaInvMomentAtScale P 0 s ξ := by
            apply le_of_eq
            unfold Ch04.lambdaInvMomentAtScale Ch04.annealedMomentRoot X0
            congr 2 with a
            rw [abs_of_nonneg]
            exact inv_nonneg.mpr
              (Ch04.lambdaSqCoeffField_finite_nonneg (originCube d 0) a hs
                (by norm_num : (1 : ℝ) ≤ 1))
  have hsup :=
    Ch04.integral_finsetSup_abs_pow_rpow_inv_le_card_rpow_mul
      (μ := P) (s := D) hD (p := ξ)
      hξ_one hK_nonneg X hX_aemeas hX_int hX_root
  calc
    Ch04.annealedMomentRoot P ξ
        (fun a : RegCoeffField d =>
          D.sup' hD (fun U => (Ch04.lambdaSqCoeffField U s (.finite 1) a)⁻¹))
        =
      (∫ a, (D.sup' hD (fun U => |X U a|)) ^ ξ ∂P) ^
          (1 / (ξ : ℝ)) := by
        unfold Ch04.annealedMomentRoot
        congr 2 with a
        congr 1
        apply le_antisymm
        · refine Finset.sup'_le hD _ ?_
          intro U hU
          calc
            X U a = |X U a| := (abs_of_nonneg (hX_nonneg U hU a)).symm
            _ ≤ D.sup' hD (fun U => |X U a|) :=
                Finset.le_sup' (f := fun U => |X U a|) hU
        · refine Finset.sup'_le hD _ ?_
          intro U hU
          calc
            |X U a| = X U a := abs_of_nonneg (hX_nonneg U hU a)
            _ ≤ D.sup' hD (fun U => X U a) :=
                Finset.le_sup' (f := fun U => X U a) hU
    _ ≤ (D.card : ℝ) ^ (1 / (ξ : ℝ)) *
        Ch04.lambdaInvMomentAtScale P 0 s ξ := hsup

end

end Section52
end Ch05
end Book
end Homogenization
