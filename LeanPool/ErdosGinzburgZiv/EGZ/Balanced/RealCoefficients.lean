/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.BalancedCombination
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Combination
import LeanPool.ErdosGinzburgZiv.EGZ.Convex.FiniteHull
import Mathlib.Algebra.BigOperators.Field

/-!
# Real balanced coefficients

The geometric part of balanced rounding: centrality puts the center in the
image of a capped simplex. The cap can be selected at the largest centrality,
so the resulting coefficients do not depend on the centrality parameter.
-/

open scoped BigOperators

namespace EGZ.BalancedCombination

namespace Data

variable {d : ℕ} (D : Data d)

theorem exists_support_ge (ξ : RealCoord d →ᵃ[ℝ] ℝ) :
    ∃ q : D.support, ξ D.center.real ≤ ξ q.val.real := by
  classical
  by_contra! h
  have hsub : IntCoord.real '' (↑D.support : Set (IntCoord d)) ⊆
      {q | ξ q < ξ D.center.real} := by
    rintro q ⟨z, hz, rfl⟩
    exact h ⟨z, hz⟩
  have hc := convexHull_min hsub (Convex.affine_preimage ξ (convex_Iio _))
    (intrinsicInterior_subset D.center_mem_interior)
  exact (lt_irrefl _ (show ξ D.center.real < ξ D.center.real from hc))

theorem exists_positive_centrality :
    ∃ θ : ℝ, 0 < θ ∧ IsCentral D.support D.weight θ D.center.real := by
  classical
  let : Nonempty D.support := D.support_nonempty.to_subtype
  let m := Finset.univ.inf' Finset.univ_nonempty D.weight
  have hm : 0 < m := (Finset.lt_inf'_iff _).mpr (fun q _ ↦ D.weight_pos q)
  refine ⟨m / ∑ q, D.weight q, div_pos hm D.totalWeight_pos, ?_⟩
  intro ξ
  rw [div_mul_cancel₀ _ (ne_of_gt D.totalWeight_pos)]
  obtain ⟨q, hq⟩ := D.exists_support_ge ξ
  calc
    m ≤ D.weight q := Finset.inf'_le _ (Finset.mem_univ q)
    _ = (if ξ D.center.real ≤ ξ q.val.real then D.weight q else 0) := by simp [hq]
    _ ≤ ∑ r, if ξ D.center.real ≤ ξ r.val.real then D.weight r else 0 :=
      Finset.single_le_sum (f := fun r ↦ if ξ D.center.real ≤ ξ r.val.real then D.weight r else 0)
        (fun r _ ↦ by split_ifs; exact (D.weight_pos r).le; exact le_rfl) (Finset.mem_univ q)

/-- The largest admissible centrality depends only on the weighted data. -/
noncomputable def maxCentrality : ℝ :=
  sSup {θ | IsCentral D.support D.weight θ D.center.real}

theorem centrality_le_max {θ : ℝ}
    (hθ : IsCentral D.support D.weight θ D.center.real) : θ ≤ D.maxCentrality := by
  exact le_csSup ⟨1, fun _ h ↦ D.centrality_le_one h⟩ hθ

theorem maxCentrality_pos : 0 < D.maxCentrality := by
  obtain ⟨θ, hθ, hc⟩ := D.exists_positive_centrality
  exact hθ.trans_le (D.centrality_le_max hc)

theorem isCentral_maxCentrality :
    IsCentral D.support D.weight D.maxCentrality D.center.real := by
  intro ξ
  apply (le_div_iff₀ D.totalWeight_pos).mp
  obtain ⟨θ, _, hθ⟩ := D.exists_positive_centrality
  exact csSup_le ⟨θ, hθ⟩ (fun t ht ↦ (le_div_iff₀ D.totalWeight_pos).mpr (ht ξ))

theorem maxCentrality_le_one : D.maxCentrality ≤ 1 :=
  D.centrality_le_one D.isCentral_maxCentrality

/-- The linear barycenter map on all coefficient vectors. -/
def barycenter : (D.support → ℝ) →ₗ[ℝ] RealCoord d where
  toFun β := ∑ q, β q • q.val.real
  map_add' β γ := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r β := by simp [Finset.smul_sum, mul_smul]

/-- A simplex with an individual upper bound on each coefficient. -/
def cappedSimplex (θ : ℝ) : Set (D.support → ℝ) :=
  Set.Icc 0 (fun q ↦ D.weight q / (θ * ∑ r, D.weight r)) ∩
    {β | ∑ q, β q = 1}

theorem cappedSimplex_convex (θ : ℝ) : Convex ℝ (D.cappedSimplex θ) := by
  refine (convex_Icc _ _).inter ?_
  intro β hβ γ hγ a b _ _ hab
  change (∑ q, (a * β q + b * γ q)) = 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hβ, hγ]
  simpa using hab

theorem cappedSimplex_compact (θ : ℝ) : IsCompact (D.cappedSimplex θ) := by
  exact isCompact_Icc.inter_right (isClosed_eq
    (continuous_finsetSum _ (fun q _ ↦ continuous_apply q)) continuous_const)

theorem capped_barycenter_exists {θ : ℝ} (hθ : 0 < θ)
    (hcentral : IsCentral D.support D.weight θ D.center.real) :
    ∃ β : D.support → ℝ, (∀ q, 0 ≤ β q) ∧ (∑ q, β q = 1) ∧
      (∑ q, β q • q.val.real = D.center.real) ∧
      ∀ q, β q ≤ D.weight q / (θ * ∑ r, D.weight r) := by
  classical
  have hden : 0 < θ * ∑ r, D.weight r := mul_pos hθ D.totalWeight_pos
  have hconv := (D.cappedSimplex_convex θ).linear_image D.barycenter
  have hcomp := (D.cappedSimplex_compact θ).image
    D.barycenter.continuous_of_finiteDimensional
  have hmem : D.center.real ∈ D.barycenter '' D.cappedSimplex θ := by
    by_contra hnot
    obtain ⟨f, u, hfu, huc⟩ := geometric_hahn_banach_closed_point hconv hcomp.isClosed hnot
    let ξ : RealCoord d →ᵃ[ℝ] ℝ := f.toLinearMap.toAffineMap
    let H := ∑ q : D.support, if ξ D.center.real ≤ ξ q.val.real then D.weight q else 0
    have hH : θ * ∑ r, D.weight r ≤ H := hcentral ξ
    have hHpos : 0 < H := hden.trans_le hH
    let β : D.support → ℝ := fun q ↦
      if ξ D.center.real ≤ ξ q.val.real then D.weight q / H else 0
    have hβpos : ∀ q, 0 ≤ β q := by
      intro q
      dsimp [β]
      split_ifs
      · exact (div_pos (D.weight_pos q) hHpos).le
      · exact le_rfl
    have hβsum : ∑ q, β q = 1 := by
      calc
        ∑ q, β q = H / H := by simp [β, H, Finset.sum_div, ite_div]
        _ = 1 := div_self (ne_of_gt hHpos)
    have hβcap : ∀ q, β q ≤ D.weight q / (θ * ∑ r, D.weight r) := by
      intro q
      dsimp [β]
      split_ifs
      · exact div_le_div_of_nonneg_left (D.weight_pos q).le hden hH
      · exact (div_pos (D.weight_pos q) hden).le
    have hβmem : β ∈ D.cappedSimplex θ := ⟨⟨hβpos, hβcap⟩, hβsum⟩
    have hfc : f D.center.real ≤ f (D.barycenter β) := by
      change f D.center.real ≤ f (∑ q, β q • q.val.real)
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      calc
        f D.center.real = ∑ q, β q * f D.center.real := by
          rw [← Finset.sum_mul, hβsum, one_mul]
        _ ≤ ∑ q, β q * f q.val.real := by
          apply Finset.sum_le_sum
          intro q _
          by_cases hq : ξ D.center.real ≤ ξ q.val.real
          · exact mul_le_mul_of_nonneg_left hq (hβpos q)
          · simp [β, hq]
    exact (hfc.trans_lt (hfu _ ⟨β, hβmem, rfl⟩)).not_ge huc.le
  obtain ⟨β, hβ, hbc⟩ := hmem
  exact ⟨β, hβ.1.1, hβ.2, hbc, hβ.1.2⟩

theorem coefficients_of_mem_convexHull {x : RealCoord d}
    (hx : x ∈ convexHull ℝ (IntCoord.real '' (↑D.support : Set (IntCoord d)))) :
    ∃ β : D.support → ℝ, (∀ q, 0 ≤ β q) ∧ (∑ q, β q = 1) ∧
      ∑ q, β q • q.val.real = x := by
  classical
  apply convexHull_min (t := {x | ∃ β : D.support → ℝ,
      (∀ q, 0 ≤ β q) ∧ (∑ q, β q = 1) ∧ ∑ q, β q • q.val.real = x}) ?_ ?_ hx
  · rintro x ⟨z, hz, rfl⟩
    refine ⟨fun q ↦ if q = ⟨z, hz⟩ then 1 else 0, ?_, ?_, ?_⟩
    · intro q; dsimp; split_ifs <;> norm_num
    · simp
    · simp [ite_smul]
  · rintro x ⟨β, hβ0, hβsum, rfl⟩ y ⟨γ, hγ0, hγsum, rfl⟩ a b ha hb hab
    refine ⟨fun q ↦ a * β q + b * γ q, ?_, ?_, ?_⟩
    · intro q
      exact add_nonneg (mul_nonneg ha (hβ0 q)) (mul_nonneg hb (hγ0 q))
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hβsum, hγsum]
      simpa using hab
    · simp [add_smul, Finset.sum_add_distrib, Finset.smul_sum, mul_smul]

theorem positive_barycenter_exists :
    ∃ β : D.support → ℝ, (∀ q, 0 < β q) ∧ (∑ q, β q = 1) ∧
      ∑ q, β q • q.val.real = D.center.real := by
  classical
  let : Nonempty D.support := D.support_nonempty.to_subtype
  let γ : D.support → ℝ := fun _ ↦ (Fintype.card D.support : ℝ)⁻¹
  have hcard : 0 < (Fintype.card D.support : ℝ) := by exact_mod_cast Fintype.card_pos
  have hγpos : ∀ q, 0 < γ q := fun _ ↦ inv_pos.mpr hcard
  have hγsum : ∑ q, γ q = 1 := by
    simp only [γ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (ne_of_gt hcard)
  let x := ∑ q, γ q • q.val.real
  have hx : x ∈ convexHull ℝ (IntCoord.real '' (↑D.support : Set (IntCoord d))) := by
    exact mem_convexHull_of_exists_fintype γ (fun q ↦ q.val.real)
      (fun q ↦ (hγpos q).le) hγsum (fun q ↦ ⟨q.val, q.property, rfl⟩) rfl
  by_cases hcx : D.center.real = x
  · exact ⟨γ, hγpos, hγsum, hcx.symm⟩
  obtain ⟨z, hz, a, b, ha, hb, hab, hcomb⟩ :=
    EGZ.exists_openSegment_of_mem_intrinsicInterior D.center_mem_interior hx hcx
  obtain ⟨β, hβpos, hβsum, hβz⟩ := D.coefficients_of_mem_convexHull hz
  refine ⟨fun q ↦ a * γ q + b * β q, ?_, ?_, ?_⟩
  · intro q
    exact add_pos_of_pos_of_nonneg (mul_pos ha (hγpos q)) (mul_nonneg hb.le (hβpos q))
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hγsum, hβsum]
    simpa using hab
  · calc
      _ = a • (∑ q, γ q • q.val.real) + b • (∑ q, β q • q.val.real) := by
        simp [add_smul, Finset.sum_add_distrib, Finset.smul_sum, mul_smul]
      _ = D.center.real := by rw [hβz]; exact hcomb

/-- Strict positive coefficients with an arbitrarily small relaxation of
the optimal cap. Both the coefficients and the cap depend only on `D`. -/
theorem positive_capped_barycenter_exists {η : ℝ} (hη : 0 < η) :
    ∃ β : D.support → ℝ, (∀ q, 0 < β q) ∧ (∑ q, β q = 1) ∧
      (∑ q, β q • q.val.real = D.center.real) ∧
      ∀ q, β q < (1 + η) * D.weight q /
        (D.maxCentrality * ∑ r, D.weight r) := by
  classical
  let : Nonempty D.support := D.support_nonempty.to_subtype
  obtain ⟨u, hu0, husum, huc, hucap⟩ :=
    D.capped_barycenter_exists D.maxCentrality_pos D.isCentral_maxCentrality
  obtain ⟨v, hv0, hvsum, hvc⟩ := D.positive_barycenter_exists
  let cap : D.support → ℝ := fun q ↦ D.weight q /
    (D.maxCentrality * ∑ r, D.weight r)
  have hcap : ∀ q, 0 < cap q := fun q ↦
    div_pos (D.weight_pos q) (mul_pos D.maxCentrality_pos D.totalWeight_pos)
  let m := Finset.univ.inf' Finset.univ_nonempty cap
  have hm : 0 < m := (Finset.lt_inf'_iff _).mpr (fun q _ ↦ hcap q)
  have hmcap : ∀ q, m ≤ cap q := fun q ↦ Finset.inf'_le _ (Finset.mem_univ q)
  let t := min (1 / 2 : ℝ) (η * m / 2)
  have ht : 0 < t := lt_min (by norm_num) (by positivity)
  have htone : t < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have htsmall : t < η * m := by
    have htbound : t ≤ η * m / 2 := min_le_right _ _
    nlinarith [mul_pos hη hm]
  have hvone : ∀ q, v q ≤ 1 := by
    intro q
    rw [← hvsum]
    exact Finset.single_le_sum (fun r _ ↦ (hv0 r).le) (Finset.mem_univ q)
  refine ⟨fun q ↦ (1 - t) * u q + t * v q, ?_, ?_, ?_, ?_⟩
  · intro q
    exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) (hu0 q)) (mul_pos ht (hv0 q))
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, husum, hvsum]
    ring
  · simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum, huc, hvc]
    rw [← add_smul]
    simp
  · intro q
    have hu : u q ≤ cap q := hucap q
    have hfirst : (1 - t) * u q ≤ cap q := by nlinarith [mul_nonneg ht.le (hu0 q)]
    have hsecond : t * v q ≤ t := by nlinarith [hvone q]
    have hslack : t < η * cap q := htsmall.trans_le (mul_le_mul_of_nonneg_left (hmcap q) hη.le)
    have htotal : (1 - t) * u q + t * v q < (1 + η) * cap q := by nlinarith
    simpa only [cap, mul_div_assoc] using htotal

theorem relaxed_max_cap_le {η θ : ℝ} (hη : 0 ≤ η) (hθ : 0 < θ)
    (hc : IsCentral D.support D.weight θ D.center.real) (q : D.support) :
    (1 + η) * D.weight q / (D.maxCentrality * ∑ r, D.weight r) ≤
      (1 + η) * D.weight q / (θ * ∑ r, D.weight r) := by
  exact div_le_div_of_nonneg_left (mul_nonneg (by linarith) (D.weight_pos q).le)
    (mul_pos hθ D.totalWeight_pos)
    (mul_le_mul_of_nonneg_right (D.centrality_le_max hc) D.totalWeight_pos.le)

end Data

end EGZ.BalancedCombination
