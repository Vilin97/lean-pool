/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Leibniz

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Nonpositive
import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.LeftNeighborhood
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.NaturalPrincipal

/-!
# Power remainders for the Cantor–Bendixson value

The product rule for a positive power is valid up to a remainder of strictly smaller value.
The induction also bounds the value of each translated partial product. This supplies the
interior convolution estimates without assuming multiplicativity or knowing the principal
factor of a product.

The multiplicity is a natural-number scalar in the series ring. The estimates hold in every
characteristic over a commutative coefficient ring. Nonvanishing of this scalar, which is needed
when the main term is to survive cancellation, is a separate assertion.

In the proofs, V reads the Cantor–Bendixson value in NatOrdinal, and T denotes translated weak
truncation. Products of values are natural ordinal products, while products of series are Hahn
products. The final canonical principal factors determine the comparison hypothesis.
-/

public noncomputable section

open Set Filter Topology

universe u v

namespace HahnSeries

private theorem small_values_mul_lt (B C : Ordinal.AdditivePrincipalAboveOne.{u})
    {a c : NatOrdinal.{u}} (hp : B.principalFactor ≤ C.principalFactor)
    (ha : a < NatOrdinal.of B.val) (hc : c < NatOrdinal.of C.val) :
    a * c < NatOrdinal.of B.residualFactor * NatOrdinal.of C.val := by
  have ha' : a.val < B.residualFactor * B.principalFactor := by
    rw [B.residualFactor_mul_principalFactor]
    exact ha
  have hc' : c.val < C.residualFactor * C.principalFactor := by
    rw [C.residualFactor_mul_principalFactor]
    exact hc
  obtain ⟨x, hx, hxa⟩ := (Ordinal.lt_mul_iff_of_isSuccLimit
    B.principalFactor_isInfiniteMultiplicativelyPrincipal.isSuccLimit).mp ha'
  obtain ⟨y, hy, hyc⟩ := (Ordinal.lt_mul_iff_of_isSuccLimit
    C.principalFactor_isInfiniteMultiplicativelyPrincipal.isSuccLimit).mp hc'
  have hρB : 0 < NatOrdinal.of B.residualFactor :=
    pos_iff_ne_zero.mpr B.residualFactor_isAdditivelyPrincipal.ne_zero
  have hρC : 0 < NatOrdinal.of C.residualFactor :=
    pos_iff_ne_zero.mpr C.residualFactor_isAdditivelyPrincipal.ne_zero
  have hfinal := NatOrdinal.naturalMul_mul_lt_of_lt
    (ρ₁ := NatOrdinal.of B.residualFactor) (ρ₂ := NatOrdinal.of C.residualFactor)
    (π₁ := NatOrdinal.of B.principalFactor) (π₂ := NatOrdinal.of C.principalFactor)
    (α₁ := NatOrdinal.of x) (α₂ := NatOrdinal.of y)
    C.principalFactor_isMultiplicativelyPrincipal hp hx hy (mul_pos hρB hρC)
  rw [mul_assoc, C.naturalResidual_mul_naturalPrincipal] at hfinal
  exact (mul_le_mul' (NatOrdinal.of.le_iff_le.mpr hxa.le)
    (NatOrdinal.of.le_iff_le.mpr hyc.le)).trans_lt hfinal

variable {G : Type u} {R : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

section Ring

variable [Ring R]

/-- The product-rule error for a positive power times another Hahn series, using weak truncation. -/
def leibnizPowerRemainder (b d : HahnSeries G R) (m : ℕ) (γ : G) : HahnSeries G R :=
  translate (-γ) (truncLE γ (b ^ (m + 1) * d)) -
    (m + 1) • (translate (-γ) (truncLE γ b) * (b ^ m * d)) -
    b ^ (m + 1) * translate (-γ) (truncLE γ d)

/-- The power remainder is the translated product truncation minus its two product-rule terms. -/
theorem leibnizPowerRemainder_eq (b d : HahnSeries G R) (m : ℕ) (γ : G) :
    leibnizPowerRemainder b d m γ =
      translate (-γ) (truncLE γ (b ^ (m + 1) * d)) -
        (m + 1) • (translate (-γ) (truncLE γ b) * (b ^ m * d)) -
        b ^ (m + 1) * translate (-γ) (truncLE γ d) := (rfl)

/-- Nonpositive inputs give a power remainder with nonpositive support. -/
theorem support_leibnizPowerRemainder (b d : HahnSeries G R)
    (hb : b.support ⊆ Iic 0) (hd : d.support ⊆ Iic 0) (m : ℕ) (γ : G) :
    (leibnizPowerRemainder b d m γ).support ⊆ Iic 0 := by
  rw [leibnizPowerRemainder_eq]
  apply (nonpositiveSubring G R).sub_mem
  · apply (nonpositiveSubring G R).sub_mem
    · exact support_translated_truncLE _ _
    · apply (nonpositiveSubring G R).nsmul_mem
      exact (nonpositiveSubring G R).mul_mem (support_translated_truncLE _ _)
        ((nonpositiveSubring G R).mul_mem ((nonpositiveSubring G R).pow_mem hb m) hd)
  · exact (nonpositiveSubring G R).mul_mem ((nonpositiveSubring G R).pow_mem hb (m + 1))
      (support_translated_truncLE _ _)

end Ring

variable [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G]
  [Nontrivial G] [CompleteSpace G] [CommRing R]

local notation "V" => (fun b : HahnSeries G R ↦ NatOrdinal.of (cantorBendixsonValue b))
local notation:max "T" x:arg "," c:arg => translate (-c) (truncLE c x)

private theorem partial_product_truncation_bound (b c : HahnSeries G R)
    (hb : b.support ⊆ Iic 0) (hc : c.support ⊆ Iic 0)
    (B C : Ordinal.AdditivePrincipalAboveOne.{u})
    (hB : b.cantorBendixsonValue = B.val) (hC : c.cantorBendixsonValue = C.val)
    (hp : B.principalFactor ≤ C.principalFactor) (m : ℕ)
    (hP : ∀ᶠ γ in 𝓝[<] (0 : G), V (leibnizPowerRemainder b c m γ) <
      NatOrdinal.of B.val ^ m * NatOrdinal.of B.residualFactor * NatOrdinal.of C.val) :
    ∀ᶠ γ in 𝓝[<] (0 : G), ∀ t : NatOrdinal.{u}, t < NatOrdinal.of B.val →
      t * V (T (b ^ (m + 1) * c), γ) <
        NatOrdinal.of B.val ^ (m + 1) * NatOrdinal.of B.residualFactor * NatOrdinal.of C.val := by
  have hb0 : b.cantorBendixsonValue ≠ 0 := by rw [hB]; exact B.2.1.ne_zero
  have hc0 : c.cantorBendixsonValue ≠ 0 := by rw [hC]; exact C.2.1.ne_zero
  filter_upwards [hP,
    (b.eventually_value_translated_truncLE_lt hb0).filter_mono nhdsWithin_le_nhds,
    (c.eventually_value_translated_truncLE_lt hc0).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with γ hP hbγ hcγ hγ t ht
  have hbt : V (T b, γ) < NatOrdinal.of B.val :=
    NatOrdinal.of.lt_iff_lt.mpr (by simpa only [hB] using hbγ (ne_of_lt hγ))
  have hct : V (T c, γ) < NatOrdinal.of C.val :=
    NatOrdinal.of.lt_iff_lt.mpr (by simpa only [hC] using hcγ (ne_of_lt hγ))
  let v := NatOrdinal.of B.val
  let w := NatOrdinal.of C.val
  let r := NatOrdinal.of B.residualFactor
  have hv : 0 < v := pos_iff_ne_zero.mpr B.2.1.ne_zero
  have hw : 0 < w := pos_iff_ne_zero.mpr C.2.1.ne_zero
  have hr : 0 < r := pos_iff_ne_zero.mpr B.residualFactor_isAdditivelyPrincipal.ne_zero
  have hpows (n : ℕ) : (b ^ n).support ⊆ Iic (0 : G) :=
    (nonpositiveSubring G R).pow_mem hb n
  have hpv (n : ℕ) : V (b ^ n) ≤ v ^ n := by
    simpa only [hB] using b.cantorBendixsonValue_pow_le hb n
  have hpc : V (b ^ m * c) ≤ v ^ m * w := by
    have h := (b ^ m).cantorBendixsonValue_mul_le c (hpows m) hc
    rw [hC] at h
    exact h.trans (mul_le_mul_left (hpv m) _)
  have hA : V ((m + 1) • (T b, γ * (b ^ m * c))) ≤ V (T b, γ) * (v ^ m * w) :=
    (cantorBendixsonValue_nsmul_le _ _).trans
      ((cantorBendixsonValue_mul_le _ _ (b.support_translated_truncLE γ)
        ((nonpositiveSubring G R).mul_mem (hpows m) hc)).trans (mul_le_mul_right hpc _))
  have hD : V (b ^ (m + 1) * T c, γ) ≤ v ^ (m + 1) * V (T c, γ) :=
    (cantorBendixsonValue_mul_le _ _ (hpows (m + 1)) (c.support_translated_truncLE γ)).trans
      (mul_le_mul_left (hpv (m + 1)) _)
  have hval : V (T (b ^ (m + 1) * c), γ) ≤
      max (max (V (T b, γ) * (v ^ m * w)) (v ^ (m + 1) * V (T c, γ)))
        (v ^ m * r * w) := by
    have he : T (b ^ (m + 1) * c), γ =
        (m + 1) • (T b, γ * (b ^ m * c)) + b ^ (m + 1) * T c, γ +
          leibnizPowerRemainder b c m γ := by
      rw [leibnizPowerRemainder_eq]
      abel
    rw [he]
    exact (cantorBendixsonValue_add_le _ _).trans
      (max_le_max ((cantorBendixsonValue_add_le _ _).trans (max_le_max hA hD)) hP.le)
  have h1 : t * (V (T b, γ) * (v ^ m * w)) < v ^ (m + 1) * r * w := by
    calc
      _ = (t * V (T b, γ)) * (v ^ m * w) := by ring
      _ < (r * v) * (v ^ m * w) :=
        mul_lt_mul_of_pos_right (small_values_mul_lt B B le_rfl ht hbt)
          (mul_pos (pow_pos hv m) hw)
      _ = _ := by ring
  have h2 : t * (v ^ (m + 1) * V (T c, γ)) < v ^ (m + 1) * r * w := by
    calc
      _ = v ^ (m + 1) * (t * V (T c, γ)) := by ring
      _ < v ^ (m + 1) * (r * w) :=
        mul_lt_mul_of_pos_left (small_values_mul_lt B C hp ht hct) (pow_pos hv (m + 1))
      _ = _ := by ring
  have h3 : t * (v ^ m * r * w) < v ^ (m + 1) * r * w := by
    calc
      _ < v * (v ^ m * r * w) :=
        mul_lt_mul_of_pos_right ht (mul_pos (mul_pos (pow_pos hv m) hr) hw)
      _ = _ := by ring
  have hmono : Monotone fun x : NatOrdinal.{u} ↦ t * x := fun _ _ h ↦ mul_le_mul_right h t
  apply (mul_le_mul_right hval t).trans_lt
  rw [hmono.map_max, hmono.map_max]
  exact max_lt (max_lt h1 h2) h3

/-- The power-product remainder is eventually below the natural product of the remaining
powers, the first value's residual factor, and the second value. -/
theorem eventually_cantorBendixsonValue_leibnizPowerRemainder_lt (b c : HahnSeries G R)
    (hb : b.support ⊆ Iic 0) (hc : c.support ⊆ Iic 0)
    (B C : Ordinal.AdditivePrincipalAboveOne.{u})
    (hB : b.cantorBendixsonValue = B.val) (hC : c.cantorBendixsonValue = C.val)
    (hp : B.principalFactor ≤ C.principalFactor) (m : ℕ) :
    ∀ᶠ γ in 𝓝[<] (0 : G), NatOrdinal.of (leibnizPowerRemainder b c m γ).cantorBendixsonValue <
      NatOrdinal.of B.val ^ m * NatOrdinal.of B.residualFactor * NatOrdinal.of C.val := by
  induction m with
  | zero =>
    simpa only [leibnizPowerRemainder_eq, zero_add, pow_one, pow_zero, one_mul, one_nsmul]
      using b.eventually_cantorBendixsonValue_leibnizRemainder_lt c hb hc B C hB hC hp
  | succ m ih =>
    have hQ := partial_product_truncation_bound b c hb hc B C hB hC hp m ih
    have hb0 : b.cantorBendixsonValue ≠ 0 := by rw [hB]; exact B.2.1.ne_zero
    have hcut := (b.eventually_value_translated_truncLE_lt hb0).filter_mono
      (nhdsWithin_le_nhds (s := Iio (0 : G)))
    obtain ⟨η, hη, hηall⟩ := eventually_nhdsLT_iff_exists.mp (hQ.and (ih.and hcut))
    let d := b ^ (m + 1) * c
    have hd : d.support ⊆ Iic (0 : G) :=
      (nonpositiveSubring G R).mul_mem ((nonpositiveSubring G R).pow_mem hb (m + 1)) hc
    let v := NatOrdinal.of B.val
    let w := NatOrdinal.of C.val
    let r := NatOrdinal.of B.residualFactor
    have hv : 0 < v := pos_iff_ne_zero.mpr B.2.1.ne_zero
    have hw : 0 < w := pos_iff_ne_zero.mpr C.2.1.ne_zero
    have hr : 0 < r := pos_iff_ne_zero.mpr B.residualFactor_isAdditivelyPrincipal.ne_zero
    have hbound : 0 < v ^ (m + 1) * r * w := mul_pos (mul_pos (pow_pos hv _) hr) hw
    filter_upwards [Ioo_mem_nhdsLT hη] with γ hγ
    have herr : V (T (b * d), γ - T b, γ * d - b * T d, γ) < v ^ (m + 1) * r * w := by
      apply cantorBendixsonValue_leibnizRemainder_lt_of_forall b d hb hd hγ.2 hbound
      intro x y hγx hx hγy hy _
      have htx : V (T b, x) < v := by
        apply NatOrdinal.of.lt_iff_lt.mpr
        rw [← hB]
        exact (hηall x (hγ.1.trans hγx) hx).2.2 hx.ne
      exact (cantorBendixsonValue_mul_le _ _ (b.support_translated_truncLE x)
        (d.support_translated_truncLE y)).trans_lt
          ((hηall y (hγ.1.trans hγy) hy).1 _ htx)
    have hprev : V (b * leibnizPowerRemainder b c m γ) < v ^ (m + 1) * r * w := by
      have hmul := b.cantorBendixsonValue_mul_le (leibnizPowerRemainder b c m γ) hb
        (support_leibnizPowerRemainder b c hb hc m γ)
      rw [hB] at hmul
      apply hmul.trans_lt
      calc
        _ < v * (v ^ m * r * w) :=
          mul_lt_mul_of_pos_left (hηall γ hγ.1 hγ.2).2.1 hv
        _ = _ := by ring
    have he : leibnizPowerRemainder b c (m + 1) γ =
        b * leibnizPowerRemainder b c m γ +
          (T (b * d), γ - T b, γ * d - b * T d, γ) := by
      rw [leibnizPowerRemainder_eq, leibnizPowerRemainder_eq]
      have hpow : b ^ (m + 1 + 1) * c = b * d := by dsimp only [d]; ring
      rw [hpow]
      dsimp only [d]
      simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring
    rw [he]
    exact (cantorBendixsonValue_add_le _ _).trans_lt (max_lt hprev herr)

/-- The pure-power remainder has the corresponding strict bound, including exponent one. -/
theorem eventually_cantorBendixsonValue_powerRemainder_lt (b : HahnSeries G R)
    (hb : b.support ⊆ Iic 0) (B : Ordinal.AdditivePrincipalAboveOne.{u})
    (hB : b.cantorBendixsonValue = B.val) (m : ℕ) :
    ∀ᶠ γ in 𝓝[<] (0 : G),
      NatOrdinal.of (translate (-γ) (truncLE γ (b ^ (m + 1))) -
        (m + 1) • (translate (-γ) (truncLE γ b) * b ^ m)).cantorBendixsonValue <
        NatOrdinal.of B.val ^ m * NatOrdinal.of B.residualFactor := by
  cases m with
  | zero =>
    apply Filter.Eventually.of_forall
    intro γ
    simp only [zero_add, pow_one, pow_zero, mul_one, one_nsmul, sub_self,
      cantorBendixsonValue_zero, NatOrdinal.of_zero, one_mul]
    exact pos_iff_ne_zero.mpr B.residualFactor_isAdditivelyPrincipal.ne_zero
  | succ m =>
    filter_upwards [eventually_cantorBendixsonValue_leibnizPowerRemainder_lt
      b b hb hb B B hB hB le_rfl m] with γ hγ
    have he : T (b ^ (m + 1 + 1)), γ - (m + 1 + 1) • (T b, γ * b ^ (m + 1)) =
        leibnizPowerRemainder b b m γ := by
      rw [leibnizPowerRemainder_eq, ← pow_succ]
      simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring
    rw [he]
    convert hγ using 1
    ring

end HahnSeries
