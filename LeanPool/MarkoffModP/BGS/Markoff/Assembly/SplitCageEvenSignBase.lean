/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Assembly.GiantOrbit
import LeanPool.MarkoffModP.BGS.Markoff.Core.EvenSignAction

/-!
# Even-sign stability of a split-cage base component

If `u` has full split-torus order `p - 1`, then `-u` has order at least
`(p - 1) / 2`. Thus negating a split-maximal trace still produces a
coordinate above the endgame threshold whenever

`p ^ (5 / 6) ≤ (p - 1) / 2`.

Every even sign change preserves or negates each normalized coordinate.
Consequently, under the usual large-order-to-base hypothesis, all four even
sign images of a split-cage base lie in its Gamma orbit.
-/

namespace BGS.Markoff

noncomputable section

@[simp]
theorem splitTorusTrace_neg
    {F : Type*} [Field F] (u : Fˣ) :
    splitTorusTrace (-u) = -splitTorusTrace u := by
  simp [splitTorusTrace]
  ring

/-- A split-maximal trace is represented by a full-order split-torus unit. -/
theorem exists_fullOrder_splitUnit_of_isSplitMaximalTrace
    (p : ℕ) [Fact p.Prime] (hpSeven : 7 ≤ p)
    (t : ZMod p) (hmax : IsSplitMaximalTrace p t) :
    ∃ u : (ZMod p)ˣ,
      splitTorusTrace u = t ∧
      orderOf u = p - 1 ∧
      (u : ZMod p) ^ 2 ≠ 1 := by
  have hpTwo : p ≠ 2 := by omega
  have htNonparabolic :=
    splitMaximalTrace_sq_ne_four p hpSeven t hmax
  rcases exists_split_or_quadraticNormOneTrace
      p hpTwo t htNonparabolic with
    ⟨u, htrace, huSq⟩ | ⟨u, htrace, huSq⟩
  · refine ⟨u, htrace, ?_, huSq⟩
    calc
      orderOf u = rotationOrder t := by
        rw [← htrace, rotationOrder_splitTorusTrace u huSq]
      _ = p - 1 := hmax
  · exfalso
    have hrotation : rotationOrder t = orderOf u := by
      rw [← htrace, rotationOrder_quadraticNormOneTrace p u huSq]
    have horder : orderOf u = p - 1 := by
      rw [← hmax]
      exact hrotation.symm
    have hdvd := orderOf_dvd_natCard u
    rw [quadraticNormOneTorus_natCard, horder] at hdvd
    have hdvdTwo : p - 1 ∣ 2 := by
      have hsub := Nat.dvd_sub hdvd (dvd_refl (p - 1))
      have heq : (p + 1) - (p - 1) = 2 := by omega
      rw [heq] at hsub
      exact hsub
    have hle : p - 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvdTwo
    omega

/-- Negating a full-order unit loses at most a factor of two in its order. -/
theorem half_card_sub_one_le_orderOf_neg_of_fullOrder
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (u : (ZMod p)ˣ) (huOrder : orderOf u = p - 1) :
    (p - 1) / 2 ≤ orderOf (-u) := by
  have hnegOneOrder : orderOf (-1 : (ZMod p)ˣ) = 2 := by
    rw [← orderOf_units, Units.coe_neg_one, orderOf_neg_one,
      ringChar.eq (ZMod p) p, if_neg hpTwo]
  have huEq : u = (-1 : (ZMod p)ˣ) * (-u) := by simp
  have hdvd :
      p - 1 ∣ 2 * orderOf (-u) := by
    have hproduct :=
      (Commute.all (-1 : (ZMod p)ˣ) (-u)).orderOf_mul_dvd_mul_orderOf
    rw [← huEq, huOrder, hnegOneOrder] at hproduct
    exact hproduct
  have hle : p - 1 ≤ 2 * orderOf (-u) :=
    Nat.le_of_dvd
      (Nat.mul_pos (by norm_num) (orderOf_pos (-u))) hdvd
  omega

/-- The negated trace of a full-order split unit has rotation order at least
half the split-torus cardinality. -/
theorem half_card_sub_one_le_rotationOrder_neg_splitTorusTrace
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (u : (ZMod p)ˣ)
    (huOrder : orderOf u = p - 1)
    (huSq : (u : ZMod p) ^ 2 ≠ 1) :
    (p - 1) / 2 ≤ rotationOrder (-splitTorusTrace u) := by
  have hnegSq : ((-u : (ZMod p)ˣ) : ZMod p) ^ 2 ≠ 1 := by
    intro hsq
    apply huSq
    simpa using hsq
  rw [← splitTorusTrace_neg,
    rotationOrder_splitTorusTrace (-u) hnegSq]
  exact half_card_sub_one_le_orderOf_neg_of_fullOrder
    p hpTwo u huOrder

/-- Normalization sends a signed point's selected coordinate either to the
original normalized coordinate or to its negative. -/
theorem normalizedCoordinateAt_evenSign_smul_eq_or_eq_neg
    {R : Type*} [CommRing R] [Invertible (3 : R)]
    (axis : NormalizedCoordinateAxis) (s : EvenSign)
    (x : PuncturedMarkoffSurface R) :
    normalizedCoordinateAt axis
        (normalizedSurfaceOfPunctured
          (puncturedNormalizationEquiv R (s • x))).1 =
      normalizedCoordinateAt axis
        (normalizedSurfaceOfPunctured
          (puncturedNormalizationEquiv R x)).1 ∨
    normalizedCoordinateAt axis
        (normalizedSurfaceOfPunctured
          (puncturedNormalizationEquiv R (s • x))).1 =
      -normalizedCoordinateAt axis
        (normalizedSurfaceOfPunctured
          (puncturedNormalizationEquiv R x)).1 := by
  cases axis <;> cases s <;>
    simp [normalizedCoordinateAt, normalizedSurfaceOfPunctured,
      puncturedNormalizationEquiv_coe, toNormalized,
      evenSign_smul_punctured_coe, evenSign_smul_surface_coe,
      evenSignPoint]

/-- Under the explicit half-order threshold, every even sign image of a
split-cage base lies in the base Gamma component. -/
theorem samePuncturedComponent_evenSign_smul_of_splitCageBase
    (p : ℕ) [Fact p.Prime] [Invertible (3 : ZMod p)]
    (hpSeven : 7 ≤ p)
    (c : PuncturedMarkoffSurface (ZMod p))
    (hbase : IsInSplitCage p
      (normalizedSurfaceOfPunctured
        (puncturedNormalizationEquiv (ZMod p) c)))
    (hhalfThreshold :
      (p : ℝ) ^ (5 / 6 : ℝ) ≤ (((p - 1) / 2 : ℕ) : ℝ))
    (hlarge : ∀ z : NormalizedMarkoffSurface (ZMod p),
      (p : ℝ) ^ (5 / 6 : ℝ) ≤
          maximalCoordinateRotationOrder z.1 →
      SameNormalizedComponent
        (normalizedSurfaceOfPunctured
          (puncturedNormalizationEquiv (ZMod p) c)) z) :
    ∀ s : EvenSign, SamePuncturedComponent c (s • c) := by
  intro s
  apply (samePuncturedComponent_iff_sameNormalizedComponent c (s • c)).2
  let base :=
    normalizedSurfaceOfPunctured
      (puncturedNormalizationEquiv (ZMod p) c)
  let signed :=
    normalizedSurfaceOfPunctured
      (puncturedNormalizationEquiv (ZMod p) (s • c))
  obtain ⟨axis, hmax⟩ := hbase
  let t := normalizedCoordinateAt axis base.1
  have hmaxT : IsSplitMaximalTrace p t := by
    simpa [t, base] using hmax
  obtain ⟨u, htrace, huOrder, huSq⟩ :=
    exists_fullOrder_splitUnit_of_isSplitMaximalTrace
      p hpSeven t hmaxT
  have hnegOrder :
      (p - 1) / 2 ≤ rotationOrder (-t) := by
    rw [← htrace]
    exact half_card_sub_one_le_rotationOrder_neg_splitTorusTrace
      p (by omega) u huOrder huSq
  have hcoordinate :=
    normalizedCoordinateAt_evenSign_smul_eq_or_eq_neg axis s c
  have hcoordinateOrder :
      (p - 1) / 2 ≤
        rotationOrder (normalizedCoordinateAt axis signed.1) := by
    rcases hcoordinate with hpositive | hnegative
    · rw [show normalizedCoordinateAt axis signed.1 = t by
          simpa [signed, base, t] using hpositive,
        hmaxT]
      exact Nat.div_le_self _ _
    · rw [show normalizedCoordinateAt axis signed.1 = -t by
          simpa [signed, base, t] using hnegative]
      exact hnegOrder
  have hcoordinateLe :
      rotationOrder (normalizedCoordinateAt axis signed.1) ≤
        maximalCoordinateRotationOrder signed.1 := by
    cases axis
    · exact rotationOrder_first_le_maximalCoordinateRotationOrder signed.1
    · exact rotationOrder_second_le_maximalCoordinateRotationOrder signed.1
    · exact rotationOrder_third_le_maximalCoordinateRotationOrder signed.1
  apply hlarge signed
  exact hhalfThreshold.trans (by
    exact_mod_cast hcoordinateOrder.trans hcoordinateLe)

end

end BGS.Markoff
