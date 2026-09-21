/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Convolution
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Multiplication
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.MultiplicativelyPrincipal

import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.NaturalPrincipal

/-!
# Leibniz remainders for the Cantor–Bendixson value

For nonpositive Hahn series, the endpoint pairs of the finite convolution give the two
product-rule terms. All remaining pairs have both coordinates strictly between the cutoff
and zero. Strict local rank decrease and the canonical ordinal factorisation then bound the
remainder by the first value's residual factor times the second value, provided the first
principal factor is no larger. Multiplication in this bound is Hessenberg multiplication.

These are remainder estimates for the ambient Cantor–Bendixson value, not claims about the
ordinary support-order value on a general exponent group. They use ordered uniform exponent
groups that are Cauchy complete and ring coefficients; neither density nor characteristic zero
is assumed.
-/

public noncomputable section

open Set Filter Topology
open scoped NatOrdinal

universe u v

namespace HahnSeries

variable {G : Type u} {R : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [Ring R]

/-- Removing the two endpoint terms leaves only interior convolution products, up to value zero.
A common strict positive bound on those products therefore bounds the Leibniz remainder. -/
theorem cantorBendixsonValue_leibnizRemainder_lt_of_forall (b d : HahnSeries G R)
    (hb : b.support ⊆ Iic 0) (hd : d.support ⊆ Iic 0) {γ : G} (hγ : γ < 0)
    {ρ : Ordinal.{u}} (hρ : 0 < ρ)
    (hterm : ∀ x y : G, γ < x → x < 0 → γ < y → y < 0 → x + y = γ →
      (translate (-x) (truncLE x b) * translate (-y) (truncLE y d)).cantorBendixsonValue < ρ) :
    (translate (-γ) (truncLE γ (b * d)) - translate (-γ) (truncLE γ b) * d -
      b * translate (-γ) (truncLE γ d)).cantorBendixsonValue < ρ := by
  classical
  let I := b.closedSupportAddFiber d γ
  let I' := insert (γ, 0) (insert (0, γ) I)
  let F : G × G → HahnSeries G R := fun p ↦
    translate (-p.1) (truncLE p.1 b) * translate (-p.2) (truncLE p.2 d)
  have hzero (p : G × G) (hp : p ∉ I) (he : p.1 + p.2 = γ) :
      (F p).cantorBendixsonValue = 0 := by
    have hnot : p.1 ∉ b.closedSupport ∨ p.2 ∉ d.closedSupport := by
      simpa only [I, mem_closedSupportAddFiber, he, and_true, not_and_or] using hp
    have hmul := (translate (-p.1) (truncLE p.1 b)).cantorBendixsonValue_mul_le
      (translate (-p.2) (truncLE p.2 d)) (b.support_translated_truncLE p.1)
      (d.support_translated_truncLE p.2)
    apply le_antisymm _ zero_le
    rcases hnot with hp | hp
    · rw [cantorBendixsonValue_translated_truncLE, ite_eq_right hp,
        NatOrdinal.of_zero, zero_mul] at hmul
      exact hmul
    · rw [d.cantorBendixsonValue_translated_truncLE, ite_eq_right hp,
        NatOrdinal.of_zero, mul_zero] at hmul
      exact hmul
  have hsub : I ⊆ I' := fun _ hp ↦
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp)
  have hsum : (∑ p ∈ I', F p - ∑ p ∈ I, F p).cantorBendixsonValue = 0 := by
    rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
    apply cantorBendixsonValue_sum_eq_zero
    intro p hp
    obtain ⟨hin, hout⟩ := Finset.mem_sdiff.mp hp
    apply hzero p hout
    rcases Finset.mem_insert.mp hin with rfl | hin
    · exact add_zero γ
    rcases Finset.mem_insert.mp hin with rfl | hin
    · exact zero_add γ
    · exact (hout hin).elim
  have hconv : (translate (-γ) (truncLE γ (b * d)) - ∑ p ∈ I', F p).cantorBendixsonValue = 0 := by
    have hz := cantorBendixsonValue_sub_le
      (translate (-γ) (truncLE γ (b * d)) - ∑ p ∈ I, F p)
      (∑ p ∈ I', F p - ∑ p ∈ I, F p)
    rw [sub_sub_sub_cancel_right, b.cantorBendixsonValue_convolution_error d γ,
      hsum, max_self] at hz
    exact le_antisymm hz zero_le
  let J := (I'.erase (γ, 0)).erase (0, γ)
  have hne : (0, γ) ≠ (γ, (0 : G)) := fun he ↦ hγ.ne' (congrArg Prod.fst he)
  have hγI : (γ, (0 : G)) ∈ I' := Finset.mem_insert_self _ _
  have h0I : (0, γ) ∈ I'.erase (γ, 0) :=
    Finset.mem_erase.mpr ⟨hne, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
  have hsplit : ∑ p ∈ I', F p = F (γ, 0) + (F (0, γ) + ∑ p ∈ J, F p) := by
    rw [Finset.add_sum_erase _ _ h0I, Finset.add_sum_erase _ _ hγI]
  have hFγ : F (γ, 0) = translate (-γ) (truncLE γ b) * d := by
    simp only [F, neg_zero, translate_zero_apply, truncLE_eq_self_of_support_subset_Iic hd]
  have hF0 : F (0, γ) = b * translate (-γ) (truncLE γ d) := by
    simp only [F, neg_zero, translate_zero_apply, truncLE_eq_self_of_support_subset_Iic hb]
  have hrem : (translate (-γ) (truncLE γ (b * d)) - translate (-γ) (truncLE γ b) * d -
      b * translate (-γ) (truncLE γ d) - ∑ p ∈ J, F p).cantorBendixsonValue = 0 := by
    have he : translate (-γ) (truncLE γ (b * d)) - translate (-γ) (truncLE γ b) * d -
        b * translate (-γ) (truncLE γ d) - ∑ p ∈ J, F p =
        translate (-γ) (truncLE γ (b * d)) - ∑ p ∈ I', F p := by
      rw [hsplit, hFγ, hF0]
      abel
    rw [he]
    exact hconv
  rw [cantorBendixsonValue_eq_of_sub_value_eq_zero _ _ hrem]
  apply cantorBendixsonValue_sum_lt _ _ hρ
  intro p hp
  obtain ⟨hp0, hp⟩ := Finset.mem_erase.mp hp
  obtain ⟨hpγ, hp⟩ := Finset.mem_erase.mp hp
  have hpI : p ∈ I := by
    rcases Finset.mem_insert.mp hp with hp | hp
    · exact (hpγ hp).elim
    rcases Finset.mem_insert.mp hp with hp | hp
    · exact (hp0 hp).elim
    · exact hp
  obtain ⟨hpb, hpd, he⟩ := (b.mem_closedSupportAddFiber d γ p).mp hpI
  have hx : p.1 ≤ 0 := closure_minimal hb isClosed_Iic ((b.mem_closedSupport _).mp hpb)
  have hy : p.2 ≤ 0 := closure_minimal hd isClosed_Iic ((d.mem_closedSupport _).mp hpd)
  have hx0 : p.1 ≠ 0 := by
    intro hz
    exact hp0 (Prod.ext hz (by simpa only [hz, zero_add] using he))
  have hy0 : p.2 ≠ 0 := by
    intro hz
    exact hpγ (Prod.ext (by simpa only [hz, add_zero] using he) hz)
  have hxlt := lt_of_le_of_ne hx hx0
  have hylt := lt_of_le_of_ne hy hy0
  apply hterm _ _ _ hxlt _ hylt he
  · rw [← he]
    simpa only [add_zero] using add_lt_add_right hylt p.1
  · rw [← he]
    simpa only [zero_add] using add_lt_add_left hxlt p.2

omit [Nontrivial G] [CompleteSpace G] in
private theorem eventually_truncation_value_lt_wpow (b : HahnSeries G R) (α : NatOrdinal.{u})
    (hb : NatOrdinal.of b.cantorBendixsonValue ≤ ω^ α) :
    ∀ᶠ c in 𝓝 (0 : G), c ≠ 0 →
      NatOrdinal.of (translate (-c) (truncLE c b)).cantorBendixsonValue < ω^ α := by
  classical
  by_cases hz : b.cantorBendixsonValue = 0
  · have hn := (b.cantorBendixsonValue_eq_zero_iff).mp hz
    have hev := isClosed_closure.isOpen_compl.mem_nhds hn
    filter_upwards [hev] with c hc _
    rw [b.cantorBendixsonValue_translated_truncLE,
      ite_eq_right (by simpa only [mem_closedSupport, mem_compl_iff] using hc), NatOrdinal.of_zero]
    exact NatOrdinal.wpow_pos _
  · filter_upwards [b.eventually_value_translated_truncLE_lt hz] with c hc hne
    exact lt_of_lt_of_le (hc hne) hb

/-- A successor exponent bound on the first value gives the corresponding strict remainder bound.
This includes zero values and a second value at most one. -/
theorem eventually_cantorBendixsonValue_leibnizRemainder_lt_of_le_wpow (b d : HahnSeries G R)
    (hb : b.support ⊆ Iic 0) (hd : d.support ⊆ Iic 0) (α β : NatOrdinal.{u})
    (hv : NatOrdinal.of b.cantorBendixsonValue ≤ ω^ (α + 1))
    (hw : NatOrdinal.of d.cantorBendixsonValue ≤ ω^ β) :
    ∀ᶠ γ in 𝓝[<] (0 : G),
      NatOrdinal.of (translate (-γ) (truncLE γ (b * d)) -
        translate (-γ) (truncLE γ b) * d -
        b * translate (-γ) (truncLE γ d)).cantorBendixsonValue < ω^ (α + β) := by
  classical
  have hev := (b.eventually_truncation_value_lt_wpow (α + 1) hv).and
    (d.eventually_truncation_value_lt_wpow β hw)
  obtain ⟨η, hη, hηv⟩ := mem_nhdsLE_iff_exists_Ioc_subset.mp
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds hev)
  filter_upwards [Ioo_mem_nhdsLT hη] with γ hγ
  apply cantorBendixsonValue_leibnizRemainder_lt_of_forall b d hb hd hγ.2 (NatOrdinal.wpow_pos _)
  intro x y hγx hx hγy hy _
  have hxv := (hηv ⟨hγ.1.trans hγx, hx.le⟩).1 hx.ne
  have hyv := (hηv ⟨hγ.1.trans hγy, hy.le⟩).2 hy.ne
  have hxle : NatOrdinal.of (translate (-x) (truncLE x b)).cantorBendixsonValue ≤ ω^ α := by
    by_cases hm : x ∈ b.closedSupport
    · rw [b.cantorBendixsonValue_translated_truncLE, ite_eq_left hm,
        NatOrdinal.of_omega0_opow] at hxv ⊢
      exact NatOrdinal.wpow_le_wpow.mpr
        (Order.lt_add_one_iff.mp (NatOrdinal.wpow_lt_wpow.mp hxv))
    · rw [b.cantorBendixsonValue_translated_truncLE, ite_eq_right hm, NatOrdinal.of_zero]
      exact zero_le
  have hprod := (translate (-x) (truncLE x b)).cantorBendixsonValue_mul_le
    (translate (-y) (truncLE y d)) (b.support_translated_truncLE x)
    (d.support_translated_truncLE y)
  apply hprod.trans_lt
  apply (mul_le_mul_left hxle _).trans_lt
  by_cases hm : y ∈ d.closedSupport
  · rw [d.cantorBendixsonValue_translated_truncLE, ite_eq_left hm,
      NatOrdinal.of_omega0_opow] at hyv ⊢
    rw [← NatOrdinal.wpow_add]
    apply NatOrdinal.wpow_lt_wpow.mpr
    exact add_lt_add_right (NatOrdinal.wpow_lt_wpow.mp hyv) α
  · rw [d.cantorBendixsonValue_translated_truncLE, ite_eq_right hm,
      NatOrdinal.of_zero, mul_zero]
    exact NatOrdinal.wpow_pos _

/-- If the first value has no larger final canonical factor, the Leibniz remainder is eventually
strictly below the natural product of its residual factor with the second value. -/
theorem eventually_cantorBendixsonValue_leibnizRemainder_lt (b d : HahnSeries G R)
    (hb : b.support ⊆ Iic 0) (hd : d.support ⊆ Iic 0)
    (B D : Ordinal.AdditivePrincipalAboveOne.{u})
    (hB : b.cantorBendixsonValue = B.val) (hD : d.cantorBendixsonValue = D.val)
    (hp : B.principalFactor ≤ D.principalFactor) :
    ∀ᶠ γ in 𝓝[<] (0 : G),
      NatOrdinal.of (translate (-γ) (truncLE γ (b * d)) -
        translate (-γ) (truncLE γ b) * d -
        b * translate (-γ) (truncLE γ d)).cantorBendixsonValue <
          NatOrdinal.of B.residualFactor * NatOrdinal.of D.val := by
  classical
  have hb0 : b.cantorBendixsonValue ≠ 0 := by rw [hB]; exact B.2.1.ne_zero
  have hd0 : d.cantorBendixsonValue ≠ 0 := by rw [hD]; exact D.2.1.ne_zero
  have hev := (b.eventually_value_translated_truncLE_lt hb0).and
    (d.eventually_value_translated_truncLE_lt hd0)
  obtain ⟨η, hη, hηv⟩ := mem_nhdsLE_iff_exists_Ioc_subset.mp
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds hev)
  have hρB : 0 < NatOrdinal.of B.residualFactor :=
    pos_iff_ne_zero.mpr B.residualFactor_isAdditivelyPrincipal.ne_zero
  have hρD : 0 < NatOrdinal.of D.residualFactor :=
    pos_iff_ne_zero.mpr D.residualFactor_isAdditivelyPrincipal.ne_zero
  filter_upwards [Ioo_mem_nhdsLT hη] with γ hγ
  apply cantorBendixsonValue_leibnizRemainder_lt_of_forall b d hb hd hγ.2
    (ρ := (NatOrdinal.of B.residualFactor * NatOrdinal.of D.val).val)
    (show (0 : NatOrdinal) < NatOrdinal.of B.residualFactor * NatOrdinal.of D.val from
      mul_pos hρB (pos_iff_ne_zero.mpr D.2.1.ne_zero))
  intro x y hγx hx hγy hy _
  have hxv := (hηv ⟨hγ.1.trans hγx, hx.le⟩).1 hx.ne
  have hyv := (hηv ⟨hγ.1.trans hγy, hy.le⟩).2 hy.ne
  rw [hB, ← B.residualFactor_mul_principalFactor] at hxv
  rw [hD, ← D.residualFactor_mul_principalFactor] at hyv
  obtain ⟨a, ha, hax⟩ := (Ordinal.lt_mul_iff_of_isSuccLimit
    B.principalFactor_isInfiniteMultiplicativelyPrincipal.isSuccLimit).mp hxv
  obtain ⟨c, hc, hcy⟩ := (Ordinal.lt_mul_iff_of_isSuccLimit
    D.principalFactor_isInfiniteMultiplicativelyPrincipal.isSuccLimit).mp hyv
  have hmul := (translate (-x) (truncLE x b)).cantorBendixsonValue_mul_le
    (translate (-y) (truncLE y d)) (b.support_translated_truncLE x)
    (d.support_translated_truncLE y)
  have hfinal := NatOrdinal.naturalMul_mul_lt_of_lt
    (ρ₁ := NatOrdinal.of B.residualFactor) (ρ₂ := NatOrdinal.of D.residualFactor)
    (π₁ := NatOrdinal.of B.principalFactor) (π₂ := NatOrdinal.of D.principalFactor)
    (α₁ := NatOrdinal.of a) (α₂ := NatOrdinal.of c)
    D.principalFactor_isMultiplicativelyPrincipal hp ha hc (mul_pos hρB hρD)
  rw [mul_assoc, D.naturalResidual_mul_naturalPrincipal] at hfinal
  exact (hmul.trans (mul_le_mul' hax.le hcy.le)).trans_lt hfinal

end HahnSeries
