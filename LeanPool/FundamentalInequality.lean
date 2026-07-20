/-
Copyright (c) 2026 Alessandro Linzi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Linzi
-/

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.Tower
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# The Fundamental Inequality of Valued Fields

Source: url:https://github.com/linzialessandro/FundamentalInequality
Authors: Alessandro Linzi
Status: verified
Main declarations: `Valuation.fundamentalInequality`, `Valuation.ramificationIndex`
Tags: valued-fields, number-theory, valuation-theory
MSC: 12J20
-/

/-!
# Ramification Index, Residue Degree, and the Fundamental Inequality

This file defines the ramification index `e(w/v)` and residue degree `f(w/v)`
for an extension of valued fields `(L | K, w | v)`, and proves the fundamental
inequality `[L : K] ≥ e(w/v) · f(w/v)` for finite extensions.

## Main definitions

- `Valuation.ramificationIndex` : The index `[w(L×) : v(K×)]`.
- `Valuation.residueDegree` : The degree `[Lw : Kv]` of the residue field extension.

## Main results

- `Valuation.valuation_independence` : Elements with valuations in distinct cosets
  and residues that are linearly independent form a linearly independent set over `K`.
- `Valuation.fundamentalInequality` : `e(w/v) * f(w/v) ≤ [L : K]`.

## References

* [F.-V. Kuhlmann, *Valued Fields*, Chapter 4, §4.4]
-/

open Valuation

noncomputable section

section ResidueDegree

variable {K : Type*} [Field K] {ΓK : Type*} [LinearOrderedCommGroupWithZero ΓK]
    (vK : Valuation K ΓK)
variable {L : Type*} [Field L] {ΓL : Type*} [LinearOrderedCommGroupWithZero ΓL]
    (vL : Valuation L ΓL)
variable [Algebra K L]

/-- The residue degree `f(w/v)` of a valued field extension. -/
def Valuation.residueDegree [vK.HasExtension vL] : ℕ :=
  Module.finrank (IsLocalRing.ResidueField vK.valuationSubring)
    (IsLocalRing.ResidueField vL.valuationSubring)

end ResidueDegree

section RamificationIndex

variable (K : Type*) [Field K]
variable {L : Type*} [Field L] {ΓL : Type*} [LinearOrderedCommGroupWithZero ΓL]
    (vL : Valuation L ΓL)
variable [Algebra K L]

/-- The ramification index `e(w/v)` of a valued field extension. It depends only on the base
field `K`, the valuation `w = vL`, and the algebra structure `K → L`. -/
def Valuation.ramificationIndex : ℕ :=
  MonoidWithZeroHom.valueGroup (.ofClass (vL.comap (algebraMap K L))) |>.relIndex
    (MonoidWithZeroHom.valueGroup (.ofClass vL))

end RamificationIndex

section FundamentalInequality

variable {K : Type*} [Field K] {ΓK : Type*} [LinearOrderedCommGroupWithZero ΓK]
    (vK : Valuation K ΓK)
variable {L : Type*} [Field L] {ΓL : Type*} [LinearOrderedCommGroupWithZero ΓL]
    (vL : Valuation L ΓL)
variable [Algebra K L] [vK.HasExtension vL]

/-- If a finite sum is zero, and all elements are non-zero, then at least two elements must have
the same valuation. -/
lemma Valuation.sum_eq_zero_implies_val_eq
    {I : Type*} [Fintype I] [Nonempty I]
    (f : I → L)
    (h_sum : ∑ i, f i = 0)
    (h_nz : ∀ i, f i ≠ 0) :
    ∃ i j, i ≠ j ∧ vL (f i) = vL (f j) := by
  classical
  by_contra h_dist
  push Not at h_dist
  obtain ⟨j, hj, hj_max⟩ :=
    Finset.exists_max_image Finset.univ (fun i => vL (f i)) Finset.univ_nonempty
  have h_strict : ∀ i ∈ Finset.univ \ {j}, vL (f i) < vL (f j) := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    have h_le := hj_max i (Finset.mem_univ i)
    exact lt_of_le_of_ne h_le (h_dist i j hi.2)
  have h_val := Valuation.map_sum_eq_of_lt vL hj h_strict
  rw [h_sum, Valuation.map_zero] at h_val
  have h_val_nz : vL (f j) ≠ 0 := by
    intro h_zero
    apply h_nz j
    exact vL.zero_iff.mp h_zero
  exact h_val_nz h_val.symm

/-- Elements with valuations in strictly distinct cosets modulo v(K×) are linearly independent
over K. -/
lemma Valuation.linearIndependent_of_val_distinct_coset
    {I : Type*} [Nonempty I]
    (z : I → L)
    (hz_nz : ∀ i, z i ≠ 0)
    (hz_dist : ∀ i j, i ≠ j → ∀ (c d : K), c ≠ 0 → d ≠ 0 →
      vL (algebraMap K L c * z i) ≠ vL (algebraMap K L d * z j)) :
    LinearIndependent K z := by
  rw [linearIndependent_iff']
  intro s g hg
  by_contra h_not_zero
  push Not at h_not_zero
  classical
  set s_nz := s.filter (fun i => g i ≠ 0) with hs_nz
  have h_snz_nonempty : s_nz.Nonempty := by
    obtain ⟨x, hx, hgx⟩ := h_not_zero
    use x
    rw [hs_nz, Finset.mem_filter]
    exact ⟨hx, hgx⟩
  haveI : Nonempty s_nz := h_snz_nonempty.to_subtype
  let f : s_nz → L := fun ⟨i, _⟩ => (algebraMap K L (g i)) * z i
  have hf_sum : ∑ i : s_nz, f i = 0 := by
    have h1 : ∑ i : s_nz, f i = ∑ i ∈ s_nz, (algebraMap K L (g i) * z i) :=
      Finset.sum_attach s_nz (fun i => algebraMap K L (g i) * z i)
    rw [h1]
    have h2 : ∑ i ∈ s_nz, algebraMap K L (g i) * z i = ∑ i ∈ s, algebraMap K L (g i) * z i := by
      apply Finset.sum_subset
      · rw [hs_nz]; exact Finset.filter_subset _ _
      · intro i hi his_nz
        rw [hs_nz, Finset.mem_filter, not_and] at his_nz
        have hgi : g i = 0 := by
          by_contra h_ne
          exact his_nz hi h_ne
        rw [hgi, map_zero, zero_mul]
    rw [h2]
    have h3 : ∑ i ∈ s, algebraMap K L (g i) * z i = ∑ i ∈ s, g i • z i := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Algebra.smul_def (g i) (z i)).symm
    rw [h3]
    exact hg
  have hf_nz : ∀ i : s_nz, f i ≠ 0 := by
    intro ⟨i, hi⟩
    have hi_prop : i ∈ s_nz := hi
    rw [hs_nz, Finset.mem_filter] at hi_prop
    have h_alg_nz : algebraMap K L (g i) ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap K L).injective).mpr hi_prop.2
    exact mul_ne_zero h_alg_nz (hz_nz i)
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, hij, hval⟩ := Valuation.sum_eq_zero_implies_val_eq vL f hf_sum hf_nz
  have hij' : i ≠ j := fun h => hij (Subtype.ext h)
  have hi_prop : i ∈ s_nz := hi
  have hj_prop : j ∈ s_nz := hj
  rw [hs_nz, Finset.mem_filter] at hi_prop hj_prop
  exact hz_dist i j hij' (g i) (g j) hi_prop.2 hj_prop.2 hval

/-- Elements with no-cancellation property are linearly independent over K. -/
lemma Valuation.linearIndependent_of_val_no_cancel
    {J : Type*} [Fintype J]
    (u : J → L)
    (hu_nz : ∀ j, u j ≠ 0)
    (hu_no_cancel : ∀ (d : J → K), (∃ j, d j ≠ 0) →
      ∃ j0, vL (∑ j, algebraMap K L (d j) * u j) = vL (algebraMap K L (d j0) * u j0) ∧
      ∀ j, vL (algebraMap K L (d j) * u j) ≤ vL (algebraMap K L (d j0) * u j0)) :
    LinearIndependent K u := by
  rw [Fintype.linearIndependent_iff]
  intro d hd
  by_contra h_not_zero
  push Not at h_not_zero
  obtain ⟨j0, hj0_eq, hj0_le⟩ := hu_no_cancel d h_not_zero
  have hd_sum : ∑ j, algebraMap K L (d j) * u j = 0 := by
    have h_smul : ∑ j, algebraMap K L (d j) * u j = ∑ j, d j • u j := by
      apply Finset.sum_congr rfl
      intro j _
      exact (Algebra.smul_def (d j) (u j)).symm
    rw [h_smul, hd]
  rw [hd_sum, Valuation.map_zero] at hj0_eq
  obtain ⟨j_nz, hj_nz_d⟩ := h_not_zero
  have h_le := hj0_le j_nz
  rw [← hj0_eq] at h_le
  have h_zero : vL (algebraMap K L (d j_nz) * u j_nz) = 0 := by
    exact le_antisymm h_le zero_le
  have h_mul_zero := vL.zero_iff.mp h_zero
  cases mul_eq_zero.mp h_mul_zero with
  | inl h_alg =>
    exact hj_nz_d ((map_eq_zero_iff _ (algebraMap K L).injective).mp h_alg)
  | inr h_u =>
    exact hu_nz j_nz h_u

/-- Valuation Independence.
If elements have valuations in distinct cosets and residues that are linearly independent,
then their products are linearly independent over K. -/
lemma Valuation.valuation_independence
    {I J : Type*} [Finite I] [Fintype J] [Nonempty I]
    (z : I → L) (hz_nz : ∀ i, z i ≠ 0)
    (hz_dist : ∀ i j, i ≠ j → ∀ (c d : K), c ≠ 0 → d ≠ 0 →
      vL (algebraMap K L c * z i) ≠ vL (algebraMap K L d * z j))
    (u : J → L) (hu_val_one : ∀ j, vL (u j) = 1)
    (hu_no_cancel : ∀ (d : J → K), (∃ j, d j ≠ 0) →
      ∃ j0, vL (∑ j, algebraMap K L (d j) * u j) = vL (algebraMap K L (d j0) * u j0) ∧
      ∀ j, vL (algebraMap K L (d j) * u j) ≤ vL (algebraMap K L (d j0) * u j0)) :
    LinearIndependent K (fun (ij : I × J) ↦ z ij.1 * u ij.2) := by
  classical
  haveI : Fintype I := Fintype.ofFinite I
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra h_not_zero
  push Not at h_not_zero
  obtain ⟨⟨i_nz, j_nz⟩, hc_nz⟩ := h_not_zero
  let g : I → L := fun i => ∑ j, algebraMap K L (c (i, j)) * u j
  have h_sum : ∑ i, z i * g i = 0 := by
    have h1 : ∑ (ij : I × J), c ij • (z ij.1 * u ij.2) =
        ∑ (ij : I × J), algebraMap K L (c ij) * (z ij.1 * u ij.2) := by
      apply Finset.sum_congr rfl
      intro ij _
      exact Algebra.smul_def (c ij) (z ij.1 * u ij.2)
    rw [h1] at hc
    have h2 : ∑ (ij : I × J), algebraMap K L (c ij) * (z ij.1 * u ij.2) =
        ∑ i, ∑ j, algebraMap K L (c (i, j)) * (z i * u j) := by
      exact Fintype.sum_prod_type (fun (p : I × J) => algebraMap K L (c p) * (z p.1 * u p.2))
    rw [h2] at hc
    have h3 : ∑ i, ∑ j, algebraMap K L (c (i, j)) * (z i * u j) = ∑ i, z i * g i := by
      apply Finset.sum_congr rfl
      intro i _
      have h4 : ∑ j, algebraMap K L (c (i, j)) * (z i * u j) =
          ∑ j, z i * (algebraMap K L (c (i, j)) * u j) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [h4, ← Finset.mul_sum]
    rw [h3] at hc
    exact hc
  set s_I := Finset.filter (fun i => ∃ j, c (i, j) ≠ 0) Finset.univ with hs_I
  have hs_I_nonempty : s_I.Nonempty := by
    use i_nz
    rw [hs_I, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨j_nz, hc_nz⟩⟩
  haveI : Nonempty s_I := hs_I_nonempty.to_subtype
  let f : s_I → L := fun ⟨i, _⟩ => z i * g i
  have hf_sum : ∑ i : s_I, f i = 0 := by
    have hs1 : ∑ i : s_I, f i = ∑ i ∈ s_I, z i * g i := Finset.sum_attach s_I (fun i => z i * g i)
    rw [hs1]
    have hs2 : ∑ i ∈ s_I, z i * g i = ∑ i ∈ Finset.univ, z i * g i := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hi_notin
      rw [Finset.mem_filter, not_and, not_exists] at hi_notin
      have h_all_zero : ∀ j, c (i, j) = 0 := by
        intro j
        have h_no_ex := hi_notin (Finset.mem_univ i)
        push Not at h_no_ex
        exact h_no_ex j
      have hgi : g i = 0 := by
        have hz : ∀ j, algebraMap K L (c (i, j)) * u j = 0 := by
          intro j
          rw [h_all_zero j, map_zero, zero_mul]
        exact Finset.sum_eq_zero (fun j _ => hz j)
      rw [hgi, mul_zero]
    rw [hs2]
    exact h_sum
  have hf_nz : ∀ i : s_I, f i ≠ 0 := by
    intro ⟨i, hi⟩
    have hi_prop : i ∈ s_I := hi
    rw [hs_I, Finset.mem_filter] at hi_prop
    obtain ⟨j_ex, hc_ex⟩ := hi_prop.2
    obtain ⟨j0, hj0_eq, hj0_le⟩ := hu_no_cancel (fun j => c (i, j)) ⟨j_ex, hc_ex⟩
    have h_val_g : vL (g i) = vL (algebraMap K L (c (i, j0))) := by
      rw [hj0_eq, Valuation.map_mul, hu_val_one j0, mul_one]
    have h_c_nz : c (i, j0) ≠ 0 := by
      intro hc_zero
      have h_ex_le := hj0_le j_ex
      rw [hc_zero, map_zero, zero_mul, Valuation.map_zero] at h_ex_le
      have h_ex_val_zero := le_antisymm h_ex_le zero_le
      have h_ex_mul_zero := vL.zero_iff.mp h_ex_val_zero
      cases mul_eq_zero.mp h_ex_mul_zero with
      | inl h_alg => exact hc_ex ((map_eq_zero_iff _ (algebraMap K L).injective).mp h_alg)
      | inr h_u =>
        have h_val_u := hu_val_one j_ex
        rw [h_u, Valuation.map_zero] at h_val_u
        exact zero_ne_one h_val_u
    have h_g_nz : g i ≠ 0 := by
      intro hg_zero
      have h_vL_g : vL (g i) = 0 := by rw [hg_zero, Valuation.map_zero]
      rw [h_vL_g] at h_val_g
      have h_alg_zero := vL.zero_iff.mp h_val_g.symm
      exact h_c_nz ((map_eq_zero_iff _ (algebraMap K L).injective).mp h_alg_zero)
    exact mul_ne_zero (hz_nz i) h_g_nz
  obtain ⟨⟨i1, hi1⟩, ⟨i2, hi2⟩, hi12, hval⟩ :=
    Valuation.sum_eq_zero_implies_val_eq vL f hf_sum hf_nz
  have hi1_prop : i1 ∈ s_I := hi1
  have hi2_prop : i2 ∈ s_I := hi2
  rw [hs_I, Finset.mem_filter] at hi1_prop hi2_prop
  obtain ⟨j1_ex, hc1_ex⟩ := hi1_prop.2
  obtain ⟨j2_ex, hc2_ex⟩ := hi2_prop.2
  obtain ⟨j1_0, hj1_eq, _⟩ := hu_no_cancel (fun j => c (i1, j)) ⟨j1_ex, hc1_ex⟩
  obtain ⟨j2_0, hj2_eq, _⟩ := hu_no_cancel (fun j => c (i2, j)) ⟨j2_ex, hc2_ex⟩
  have h_val_g1 : vL (g i1) = vL (algebraMap K L (c (i1, j1_0))) := by
    rw [hj1_eq, Valuation.map_mul, hu_val_one j1_0, mul_one]
  have h_val_g2 : vL (g i2) = vL (algebraMap K L (c (i2, j2_0))) := by
    rw [hj2_eq, Valuation.map_mul, hu_val_one j2_0, mul_one]
  have h_c1_nz : c (i1, j1_0) ≠ 0 := by
    intro hc_zero
    have h_v_zero : vL (g i1) = 0 := by
      rw [h_val_g1, hc_zero, map_zero, Valuation.map_zero]
    have h_g_zero : g i1 = 0 := vL.zero_iff.mp h_v_zero
    have h_f_nz := hf_nz ⟨i1, hi1⟩
    have h_f_eq : f ⟨i1, hi1⟩ = 0 := by
      change z i1 * g i1 = 0
      rw [h_g_zero, mul_zero]
    exact h_f_nz h_f_eq
  have h_c2_nz : c (i2, j2_0) ≠ 0 := by
    intro hc_zero
    have h_v_zero : vL (g i2) = 0 := by
      rw [h_val_g2, hc_zero, map_zero, Valuation.map_zero]
    have h_g_zero : g i2 = 0 := vL.zero_iff.mp h_v_zero
    have h_f_nz := hf_nz ⟨i2, hi2⟩
    have h_f_eq : f ⟨i2, hi2⟩ = 0 := by
      change z i2 * g i2 = 0
      rw [h_g_zero, mul_zero]
    exact h_f_nz h_f_eq
  have hval' : vL (algebraMap K L (c (i1, j1_0)) * z i1) =
      vL (algebraMap K L (c (i2, j2_0)) * z i2) := by
    change vL (z i1 * g i1) = vL (z i2 * g i2) at hval
    rw [Valuation.map_mul, Valuation.map_mul] at hval
    rw [h_val_g1, h_val_g2] at hval
    rw [mul_comm (vL (z i1)), mul_comm (vL (z i2))] at hval
    rw [← Valuation.map_mul, ← Valuation.map_mul] at hval
    exact hval
  have hij' : i1 ≠ i2 := fun h => hi12 (Subtype.ext h)
  exact hz_dist i1 i2 hij' (c (i1, j1_0)) (c (i2, j2_0)) h_c1_nz h_c2_nz hval'

/-- For a family `u` of elements of valuation one whose residues are linearly independent over the
base residue field, no nontrivial `K`-linear combination cancels: there is an index attaining the
maximal valuation, equal to the valuation of the whole sum. -/
lemma Valuation.exists_max_val_no_cancel
    {J : Type*} [Fintype J] [Nonempty J]
    (u : J → L) (u_sub : J → vL.valuationSubring) (hu_eq : ∀ j, (u_sub j : L) = u j)
    (hu_val_one : ∀ j, vL (u j) = 1)
    (hu_res_indep : LinearIndependent (IsLocalRing.ResidueField vK.valuationSubring)
      (fun j => IsLocalRing.residue vL.valuationSubring (u_sub j))) :
    ∀ (d : J → K), (∃ j, d j ≠ 0) →
      ∃ j0, vL (∑ j, algebraMap K L (d j) * u j) = vL (algebraMap K L (d j0) * u j0) ∧
      ∀ j, vL (algebraMap K L (d j) * u j) ≤ vL (algebraMap K L (d j0) * u j0) := by
  intro d hd
  obtain ⟨j0, hj0_max⟩ :=
    Finset.exists_max_image Finset.univ (fun j => vK (d j)) Finset.univ_nonempty
  have hd_j0_nz : d j0 ≠ 0 := by
    obtain ⟨j_nz, hd_nz_val⟩ := hd
    have h_le := hj0_max.2 j_nz (Finset.mem_univ _)
    have h_pos : 0 < vK (d j_nz) :=
      lt_of_le_of_ne zero_le (Ne.symm ((Valuation.zero_iff vK).not.mpr hd_nz_val))
    have h_pos_j0 := lt_of_lt_of_le h_pos h_le
    exact (Valuation.zero_iff vK).not.mp (Ne.symm (ne_of_lt h_pos_j0))
  use j0
  have h_alg_nz : algebraMap K L (d j0) ≠ 0 :=
    (map_eq_zero_iff _ (algebraMap K L).injective).not.mpr hd_j0_nz
  have h_sum_fact : (∑ j, algebraMap K L (d j) * u j) =
      algebraMap K L (d j0) * ∑ j, algebraMap K L (d j * (d j0)⁻¹) * u j := by
    have h_symm : algebraMap K L (d j0) * ∑ j, algebraMap K L (d j * (d j0)⁻¹) * u j =
        ∑ j, algebraMap K L (d j) * u j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      calc algebraMap K L (d j0) * (algebraMap K L (d j * (d j0)⁻¹) * u j)
        _ = algebraMap K L (d j0) * (algebraMap K L (d j) * algebraMap K L (d j0)⁻¹ * u j) := by
          rw [map_mul]
        _ = (algebraMap K L (d j0) * algebraMap K L (d j0)⁻¹) * algebraMap K L (d j) * u j := by
          ring
        _ = algebraMap K L (d j0 * (d j0)⁻¹) * algebraMap K L (d j) * u j := by rw [← map_mul]
        _ = algebraMap K L 1 * algebraMap K L (d j) * u j := by rw [mul_inv_cancel₀ hd_j0_nz]
        _ = algebraMap K L (d j) * u j := by rw [map_one, one_mul]
    exact h_symm.symm
  have h_c_le_one : ∀ j, vK (d j * (d j0)⁻¹) ≤ 1 := by
    intro j
    have h_le : vK (d j) ≤ vK (d j0) := hj0_max.2 j (Finset.mem_univ _)
    have hd_j0_pos : 0 < vK (d j0) :=
      lt_of_le_of_ne zero_le (Ne.symm ((Valuation.zero_iff vK).not.mpr hd_j0_nz))
    rw [map_mul, map_inv₀]
    exact (mul_inv_le_iff₀ hd_j0_pos).mpr (by { rw [one_mul]; exact h_le })
  have h_c_vL_le_one : ∀ j, vL (algebraMap K L (d j * (d j0)⁻¹)) ≤ 1 := by
    intro j
    exact (Valuation.HasExtension.val_map_le_one_iff vK vL (d j * (d j0)⁻¹)).mpr (h_c_le_one j)
  have h_sum_subring_val : vL (∑ j, algebraMap K L (d j * (d j0)⁻¹) * u j) = 1 := by
    have h_c_vK_le_one : ∀ j, d j * (d j0)⁻¹ ∈ vK.valuationSubring := by
      intro j
      exact (Valuation.mem_valuationSubring_iff vK _).mpr (h_c_le_one j)
    let c_sub_K : J → vK.valuationSubring := fun j => ⟨d j * (d j0)⁻¹, h_c_vK_le_one j⟩
    have h_c_sub_K_j0 : c_sub_K j0 = 1 := by
      ext
      change d j0 * (d j0)⁻¹ = 1
      rw [mul_inv_cancel₀ hd_j0_nz]
    let c_res : J → IsLocalRing.ResidueField vK.valuationSubring := fun j =>
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal vK.valuationSubring) (c_sub_K j)
    have h_c_res_j0 : c_res j0 = 1 := by
      change Ideal.Quotient.mk _ (c_sub_K j0) = 1
      rw [h_c_sub_K_j0, map_one]
    have h_c_sub : ∀ j, algebraMap K L (d j * (d j0)⁻¹) ∈ vL.valuationSubring := by
      intro j
      exact (Valuation.mem_valuationSubring_iff vL _).mpr (h_c_vL_le_one j)
    let c_sub : J → vL.valuationSubring :=
      fun j => ⟨algebraMap K L (d j * (d j0)⁻¹), h_c_sub j⟩
    have h_sum_eq_coe : (∑ j, algebraMap K L (d j * (d j0)⁻¹) * u j) =
        (↑(∑ j : J, c_sub j * u_sub j) : L) := by
      rw [AddSubmonoidClass.coe_finsetSum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Submonoid.coe_mul, hu_eq j]
    have h_res_sum : Ideal.Quotient.mk (IsLocalRing.maximalIdeal vL.valuationSubring)
        (∑ j : J, c_sub j * u_sub j) =
        ∑ j : J, c_res j • IsLocalRing.residue vL.valuationSubring (u_sub j) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      have h_mul : Ideal.Quotient.mk (IsLocalRing.maximalIdeal vL.valuationSubring)
            (c_sub j * u_sub j) =
          Ideal.Quotient.mk _ (c_sub j) * Ideal.Quotient.mk _ (u_sub j) :=
        map_mul (Ideal.Quotient.mk (IsLocalRing.maximalIdeal vL.valuationSubring)) _ _
      rw [h_mul]
      have h_c_sub_map : Ideal.Quotient.mk _ (c_sub j) =
          algebraMap (IsLocalRing.ResidueField vK.valuationSubring)
            (IsLocalRing.ResidueField vL.valuationSubring) (c_res j) := by
        have h_eq : c_sub j = algebraMap vK.valuationSubring vL.valuationSubring (c_sub_K j) := by
          ext
          rfl
        rw [h_eq]
        change IsLocalRing.residue _
            (algebraMap vK.valuationSubring vL.valuationSubring (c_sub_K j)) =
          algebraMap _ _ (IsLocalRing.residue _ (c_sub_K j))
        rw [IsLocalRing.ResidueField.algebraMap_residue]
      rw [h_c_sub_map]
      exact (Algebra.smul_def (c_res j) (IsLocalRing.residue vL.valuationSubring (u_sub j))).symm
    have h_lin_comb_nz :
        ∑ j : J, c_res j • IsLocalRing.residue vL.valuationSubring (u_sub j) ≠ 0 := by
      intro h_zero
      rw [Fintype.linearIndependent_iff] at hu_res_indep
      have h_all_zero := hu_res_indep c_res h_zero
      have h_j0_zero := h_all_zero j0
      rw [h_c_res_j0] at h_j0_zero
      exact one_ne_zero h_j0_zero
    have h_sum_unit : IsUnit (∑ j : J, c_sub j * u_sub j) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, IsLocalRing.residue_def]
      rw [h_res_sum]
      exact h_lin_comb_nz
    rw [h_sum_eq_coe]
    have h_val_sub := ValuationSubring.valuation_eq_one_iff vL.valuationSubring
        (∑ j : J, c_sub j * u_sub j)
    rw [h_val_sub] at h_sum_unit
    exact (Valuation.isEquiv_valuation_valuationSubring vL).eq_one_iff_eq_one.mpr h_sum_unit
  rw [h_sum_fact, Valuation.map_mul, h_sum_subring_val, mul_one]
  refine ⟨by rw [Valuation.map_mul, hu_val_one j0, mul_one], fun j => ?_⟩
  rw [Valuation.map_mul, hu_val_one j, mul_one, Valuation.map_mul, hu_val_one j0, mul_one]
  have h_le_one := h_c_vL_le_one j
  have hd_j0_alg_pos : 0 < vL (algebraMap K L (d j0)) :=
    lt_of_le_of_ne zero_le (Ne.symm ((Valuation.zero_iff vL).not.mpr h_alg_nz))
  have h_le_one' : vL (algebraMap K L (d j)) * (vL (algebraMap K L (d j0)))⁻¹ ≤ 1 := by
    rw [← map_inv₀, ← map_mul, ← map_inv₀, ← map_mul]
    exact h_le_one
  have h_le_one'' := (mul_inv_le_iff₀ hd_j0_alg_pos).mp h_le_one'
  rwa [one_mul] at h_le_one''

/-- The fundamental inequality for finite extensions of valued fields.
`[L : K] ≥ e(w/v) · f(w/v)`
-/
theorem Valuation.fundamentalInequality [FiniteDimensional K L] :
    Valuation.ramificationIndex K vL * Valuation.residueDegree vK vL ≤ Module.finrank K L := by
  let e := Valuation.ramificationIndex K vL
  let f := Valuation.residueDegree vK vL
  change e * f ≤ _
  by_cases he : e = 0
  · rw [he, zero_mul]
    exact Nat.zero_le _
  by_cases hf : f = 0
  · rw [hf, mul_zero]
    exact Nat.zero_le _
  have h_f_pos : 0 < f := Nat.pos_of_ne_zero hf
  haveI h_fin_Kv_Lv : Module.Finite (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring) :=
    Module.finite_of_finrank_pos h_f_pos
  let Kv := IsLocalRing.ResidueField vK.valuationSubring
  let Lv := IsLocalRing.ResidueField vL.valuationSubring
  let b_res := Module.finBasis Kv Lv
  choose u_sub hu_sub using fun (j : Fin f) => Ideal.Quotient.mk_surjective (b_res j)
  let u : Fin f → L := fun j => (u_sub j : L)
  let A := MonoidWithZeroHom.valueGroup (.ofClass (vL.comap (algebraMap K L)))
  let B := MonoidWithZeroHom.valueGroup (.ofClass vL)
  let Q := B ⧸ A.comap B.subtype
  have hQ_fin : Finite Q := Nat.finite_of_card_ne_zero he
  haveI : Fintype Q := Fintype.ofFinite Q
  have h_card' : Fintype.card Q = e := by
    rw [← Nat.card_eq_fintype_card]
    exact rfl
  let eqv : Q ≃ Fin e := Fintype.equivFinOfCardEq h_card'
  let z_sub : Fin e → B := fun i => Quotient.out (eqv.symm i)
  have hz_val : ∀ i, ((z_sub i).val : ΓL) ∈ Set.range vL := by
    intro i
    have hi : (z_sub i).val ∈ B := (z_sub i).property
    have h_eq : Units.val '' B = Set.range vL \ {0} :=
      MonoidWithZeroHom.valueGroup_eq_range (.ofClass vL)
    have h_in : ((z_sub i).val : ΓL) ∈ Units.val '' B := Set.mem_image_of_mem _ hi
    rw [h_eq] at h_in
    exact h_in.1
  choose z hz using fun i => hz_val i
  have hz_nz : ∀ i, z i ≠ 0 := by
    intro i
    have hz_eq := hz i
    by_contra h_z_zero
    rw [h_z_zero, Valuation.map_zero] at hz_eq
    have h_unit_zero : ((z_sub i).val : ΓL) = 0 := hz_eq.symm
    have h_unit_ne_zero : ((z_sub i).val : ΓL) ≠ 0 := Units.ne_zero _
    exact h_unit_ne_zero h_unit_zero
  have hz_dist : ∀ i j, i ≠ j → ∀ c d : K, c ≠ 0 → d ≠ 0 →
      vL (algebraMap K L c * z i) ≠ vL (algebraMap K L d * z j) := by
    intro i j hij c d hc hd h_eq
    have hc_alg_nz : algebraMap K L c ≠ 0 :=
      (map_eq_zero_iff _ (algebraMap K L).injective).not.mpr hc
    have hd_alg_nz : algebraMap K L d ≠ 0 :=
      (map_eq_zero_iff _ (algebraMap K L).injective).not.mpr hd
    have h1 : vL (algebraMap K L c * z i) = vL (algebraMap K L c) * vL (z i) :=
      Valuation.map_mul _ _ _
    have h2 : vL (algebraMap K L d * z j) = vL (algebraMap K L d) * vL (z j) :=
      Valuation.map_mul _ _ _
    rw [h1, h2] at h_eq
    have h_vi : vL (z i) = ((z_sub i).val : ΓL) := hz i
    have h_vj : vL (z j) = ((z_sub j).val : ΓL) := hz j
    rw [h_vi, h_vj] at h_eq
    have h_vc : vL (algebraMap K L c) ≠ 0 := by
      intro h
      exact hc_alg_nz (vL.zero_iff.mp h)
    have h_vd : vL (algebraMap K L d) ≠ 0 := by
      intro h
      exact hd_alg_nz (vL.zero_iff.mp h)
    have h_c_unit : IsUnit (vL (algebraMap K L c)) := IsUnit.mk0 _ h_vc
    have h_d_unit : IsUnit (vL (algebraMap K L d)) := IsUnit.mk0 _ h_vd
    have h_eq_unit : h_c_unit.unit * (z_sub i).val = h_d_unit.unit * (z_sub j).val := by
      ext
      exact h_eq
    have hd_mem : h_d_unit.unit ∈ B := MonoidWithZeroHom.mem_valueGroup _ ⟨algebraMap K L d, rfl⟩
    have hc_mem : h_c_unit.unit ∈ B := MonoidWithZeroHom.mem_valueGroup _ ⟨algebraMap K L c, rfl⟩
    have h_ratio_val : ((z_sub i : B)⁻¹ * (z_sub j : B)).val =
        (⟨h_c_unit.unit, hc_mem⟩ : B).val * (⟨h_d_unit.unit, hd_mem⟩ : B)⁻¹.val := by
      change ((z_sub i).val)⁻¹ * (z_sub j).val = h_c_unit.unit * (h_d_unit.unit)⁻¹
      apply mul_left_cancel (a := (z_sub i).val * h_d_unit.unit)
      have h_lhs : (z_sub i).val * h_d_unit.unit * (((z_sub i).val)⁻¹ * (z_sub j).val) =
          h_d_unit.unit * (z_sub j).val := by
        calc (z_sub i).val * h_d_unit.unit * (((z_sub i).val)⁻¹ * (z_sub j).val)
          _ = (z_sub i).val * ((z_sub i).val)⁻¹ * h_d_unit.unit * (z_sub j).val := by ac_rfl
          _ = 1 * h_d_unit.unit * (z_sub j).val := by rw [mul_inv_cancel (z_sub i).val]
          _ = h_d_unit.unit * (z_sub j).val := by rw [one_mul]
      have h_rhs : (z_sub i).val * h_d_unit.unit * (h_c_unit.unit * (h_d_unit.unit)⁻¹) =
          h_c_unit.unit * (z_sub i).val := by
        calc (z_sub i).val * h_d_unit.unit * (h_c_unit.unit * (h_d_unit.unit)⁻¹)
          _ = h_d_unit.unit * (h_d_unit.unit)⁻¹ * h_c_unit.unit * (z_sub i).val := by ac_rfl
          _ = 1 * h_c_unit.unit * (z_sub i).val := by rw [mul_inv_cancel h_d_unit.unit]
          _ = h_c_unit.unit * (z_sub i).val := by rw [one_mul]
      rw [h_lhs, h_rhs]
      exact h_eq_unit.symm
    have h_z_ratio_in_A : ((z_sub i : B)⁻¹ * (z_sub j : B)) ∈ A.comap B.subtype := by
      rw [Subgroup.mem_comap]
      change ((z_sub i : B)⁻¹ * (z_sub j : B)).val ∈ A
      rw [h_ratio_val]
      have h_d_in_A : h_d_unit.unit ∈ A := MonoidWithZeroHom.mem_valueGroup _ ⟨d, rfl⟩
      have h_c_in_A : h_c_unit.unit ∈ A := MonoidWithZeroHom.mem_valueGroup _ ⟨c, rfl⟩
      exact Subgroup.mul_mem A h_c_in_A (Subgroup.inv_mem A h_d_in_A)
    have h_eq_out : (Quotient.mk _ (Quotient.out (eqv.symm i)) : Q) =
        Quotient.mk _ (Quotient.out (eqv.symm j)) := QuotientGroup.eq.mpr h_z_ratio_in_A
    rw [Quotient.out_eq, Quotient.out_eq] at h_eq_out
    exact hij (eqv.symm.injective h_eq_out)
  have hu_val_one : ∀ j, vL (u j) = 1 := by
    intro j
    have h_nz_res : b_res j ≠ 0 := (Module.finBasis Kv Lv).linearIndependent.ne_zero j
    have hx : Ideal.Quotient.mk (IsLocalRing.maximalIdeal vL.valuationSubring) (u_sub j) ≠ 0 := by
      rw [hu_sub j]
      exact h_nz_res
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, IsLocalRing.mem_maximalIdeal,
         mem_nonunits_iff, not_not] at hx
    have h_val_sub := ValuationSubring.valuation_eq_one_iff vL.valuationSubring (u_sub j)
    rw [h_val_sub] at hx
    have h_equiv := Valuation.isEquiv_valuation_valuationSubring vL
    exact h_equiv.eq_one_iff_eq_one.mpr hx
  haveI : Nonempty (Fin e) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero he)
  haveI : Nonempty (Fin f) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hf)
  have hu_res_indep : LinearIndependent Kv
      (fun j => IsLocalRing.residue vL.valuationSubring (u_sub j)) := by
    have h_eq : (fun j => IsLocalRing.residue vL.valuationSubring (u_sub j)) = b_res := by
      funext j
      rw [IsLocalRing.residue_def, hu_sub j]
    rw [h_eq]
    exact b_res.linearIndependent
  have hu_no_cancel :=
    Valuation.exists_max_val_no_cancel vK vL u u_sub (fun j => rfl) hu_val_one hu_res_indep
  have h_indep := Valuation.valuation_independence vL z hz_nz hz_dist u hu_val_one hu_no_cancel
  have h_card := LinearIndependent.fintype_card_le_finrank h_indep
  have h_card_prod : Fintype.card (Fin e × Fin f) = e * f := by simp
  rw [h_card_prod] at h_card
  exact h_card

end FundamentalInequality
