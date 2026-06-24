/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Basic
import LeanPool.LeanModularForms.GeneralizedResidueTheory.CauchyPrimitive
import LeanPool.LeanModularForms.GeneralizedResidueTheory.PrincipalValue
import LeanPool.LeanModularForms.GeneralizedResidueTheory.Homotopy.Invariance
import LeanPool.LeanModularForms.GeneralizedResidueTheory.Residue

/-!
# Null-Homologous Curves: Definitions and Convexity Bridge

A closed piecewise C^1 immersion is **null-homologous** in an open set U when its
winding number around every point outside U is zero. This is the topological
condition required by the generalized residue theorem of Hungerbuhler-Wasem.

## Main definitions

* `IsNullHomologous` -- null-homologous curve in an open set

## Main results

* `ftc_piecewise_contour` -- FTC for piecewise C¹ contours
* `integrand_intervalIntegrable_of_avoids` -- integrability of winding integrand
* `isNullHomologous_of_convex` -- every closed curve in a convex open set
  is null-homologous (bridge lemma)
-/

open Complex Set Filter Topology MeasureTheory intervalIntegral

noncomputable section

/-- A closed piecewise C^1 immersion gamma is null-homologous in an open set U if:
1. gamma is a closed curve
2. gamma lies entirely in U
3. The winding number of gamma around every point outside U is zero.

This matches the definition in Hungerbuhler-Wasem (arXiv:1808.00997v2). -/
structure IsNullHomologous (γ : PiecewiseC1Immersion) (U : Set ℂ) : Prop where
  closed : γ.toPiecewiseC1Curve.IsClosed
  image_subset : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U
  winding_zero : ∀ z, z ∉ U →
    generalizedWindingNumber' γ.toFun γ.a γ.b z = 0

private lemma ftc_no_interior_partition {F : ℂ → ℂ} {f : ℂ → ℂ}
    (γ : PiecewiseC1Curve) (a' b' : ℝ)
    (h_int : IntervalIntegrable
      (fun t => f (γ.toFun t) * deriv γ.toFun t) volume γ.a γ.b)
    (hFγ_cont : ContinuousOn (F ∘ γ.toFun) (Icc γ.a γ.b))
    (hFγ_deriv_off : ∀ t ∈ Ioo γ.a γ.b, t ∉ (↑γ.partition : Set ℝ) →
      HasDerivAt (F ∘ γ.toFun) (f (γ.toFun t) * deriv γ.toFun t) t)
    (ha'b' : a' ≤ b') (hsub : Icc a' b' ⊆ Icc γ.a γ.b)
    (hempty : γ.partition.filter (fun t => a' < t ∧ t < b') = ∅) :
    ∫ t in a'..b', f (γ.toFun t) * deriv γ.toFun t =
      F (γ.toFun b') - F (γ.toFun a') := by
  have ha'_bds := hsub (left_mem_Icc.mpr ha'b')
  have hb'_bds := hsub (right_mem_Icc.mpr ha'b')
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha'b'
    (hFγ_cont.mono hsub)
  · intro t ht
    apply hFγ_deriv_off t
      ⟨lt_of_le_of_lt ha'_bds.1 ht.1, lt_of_lt_of_le ht.2 hb'_bds.2⟩
    intro ht_P
    exact Finset.notMem_empty t (hempty ▸ Finset.mem_filter.mpr ⟨ht_P, ht.1, ht.2⟩)
  · exact h_int.mono_set (uIcc_subset_uIcc
      (Set.mem_uIcc_of_le ha'_bds.1 ha'_bds.2)
      (Set.mem_uIcc_of_le hb'_bds.1 hb'_bds.2))

private lemma partition_filter_card_lt_left (P : Finset ℝ) {a' b' c : ℝ}
    (hc_part : c ∈ P) (hac : a' < c) (hcb : c < b') :
    (P.filter (fun t => a' < t ∧ t < c)).card
      < (P.filter (fun t => a' < t ∧ t < b')).card := by
  apply Finset.card_lt_card
  constructor
  · intro t ht
    simp only [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, ht.2.1, lt_trans ht.2.2 hcb⟩
  · intro hsub
    have hcmem := hsub (Finset.mem_filter.mpr ⟨hc_part, hac, hcb⟩)
    simp only [Finset.mem_filter] at hcmem
    exact lt_irrefl c hcmem.2.2

private lemma partition_filter_card_lt_right (P : Finset ℝ) {a' b' c : ℝ}
    (hc_part : c ∈ P) (hac : a' < c) (hcb : c < b') :
    (P.filter (fun t => c < t ∧ t < b')).card
      < (P.filter (fun t => a' < t ∧ t < b')).card := by
  apply Finset.card_lt_card
  constructor
  · intro t ht
    simp only [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, lt_trans hac ht.2.1, ht.2.2⟩
  · intro hsub
    have hcmem := hsub (Finset.mem_filter.mpr ⟨hc_part, hac, hcb⟩)
    simp only [Finset.mem_filter] at hcmem
    exact lt_irrefl c hcmem.2.1

private lemma ftc_inductive_step {F : ℂ → ℂ} {f : ℂ → ℂ}
    (γ : PiecewiseC1Curve) (m : ℕ) (a' b' c : ℝ)
    (h_int : IntervalIntegrable
      (fun t => f (γ.toFun t) * deriv γ.toFun t) volume γ.a γ.b)
    (ih : ∀ (a' b' : ℝ),
      (γ.partition.filter (fun t => a' < t ∧ t < b')).card ≤ m →
      a' ≤ b' → Icc a' b' ⊆ Icc γ.a γ.b →
      a' ∈ γ.partition → b' ∈ γ.partition →
      ∫ t in a'..b', f (γ.toFun t) * deriv γ.toFun t =
        F (γ.toFun b') - F (γ.toFun a'))
    (hcard : (γ.partition.filter (fun t => a' < t ∧ t < b')).card ≤ m + 1)
    (ha'b' : a' ≤ b') (hsub : Icc a' b' ⊆ Icc γ.a γ.b)
    (ha'P : a' ∈ γ.partition) (hb'P : b' ∈ γ.partition)
    (hc_part : c ∈ γ.partition) (hac : a' < c) (hcb : c < b') :
    ∫ t in a'..b', f (γ.toFun t) * deriv γ.toFun t =
      F (γ.toFun b') - F (γ.toFun a') := by
  have hc_bds : c ∈ Icc γ.a γ.b := hsub ⟨le_of_lt hac, le_of_lt hcb⟩
  have h_int_ac := h_int.mono_set (uIcc_subset_uIcc
    (Set.mem_uIcc_of_le (hsub (left_mem_Icc.mpr ha'b')).1
      (hsub (left_mem_Icc.mpr ha'b')).2)
    (Set.mem_uIcc_of_le hc_bds.1 hc_bds.2))
  have h_int_cb := h_int.mono_set (uIcc_subset_uIcc
    (Set.mem_uIcc_of_le hc_bds.1 hc_bds.2)
    (Set.mem_uIcc_of_le (hsub (right_mem_Icc.mpr ha'b')).1
      (hsub (right_mem_Icc.mpr ha'b')).2))
  have hcard_ac : (γ.partition.filter (fun t => a' < t ∧ t < c)).card ≤ m := by
    have := partition_filter_card_lt_left γ.partition hc_part hac hcb; omega
  have hcard_cb : (γ.partition.filter (fun t => c < t ∧ t < b')).card ≤ m := by
    have := partition_filter_card_lt_right γ.partition hc_part hac hcb; omega
  have h_ac := ih a' c hcard_ac (le_of_lt hac)
    (fun t ht => hsub ⟨ht.1, le_trans ht.2 (le_of_lt hcb)⟩) ha'P hc_part
  have h_cb := ih c b' hcard_cb (le_of_lt hcb)
    (fun t ht => hsub ⟨le_trans (le_of_lt hac) ht.1, ht.2⟩) hc_part hb'P
  rw [← intervalIntegral.integral_add_adjacent_intervals h_int_ac h_int_cb, h_ac, h_cb]
  ring

/-- FTC for piecewise C¹ contours (induction on partition points): on any
sub-interval `[a', b']` whose endpoints belong to the partition and that
contains at most `n` interior partition points, the integral of
`f(γ(t)) · γ'(t)` equals `F(γ(b')) - F(γ(a'))`, provided `F ∘ γ` is
continuous, its derivative equals the integrand off the partition, and the
integrand is interval-integrable. -/
lemma ftc_piecewise_contour_induction {F : ℂ → ℂ} {f : ℂ → ℂ}
    (γ : PiecewiseC1Curve) (n : ℕ) (a' b' : ℝ)
    (h_int : IntervalIntegrable
      (fun t => f (γ.toFun t) * deriv γ.toFun t) volume γ.a γ.b)
    (hFγ_cont : ContinuousOn (F ∘ γ.toFun) (Icc γ.a γ.b))
    (hFγ_deriv_off : ∀ t ∈ Ioo γ.a γ.b, t ∉ (↑γ.partition : Set ℝ) →
      HasDerivAt (F ∘ γ.toFun) (f (γ.toFun t) * deriv γ.toFun t) t)
    (hcard : (γ.partition.filter (fun t => a' < t ∧ t < b')).card ≤ n)
    (ha'b' : a' ≤ b') (hsub : Icc a' b' ⊆ Icc γ.a γ.b)
    (ha'P : a' ∈ γ.partition) (hb'P : b' ∈ γ.partition) :
    ∫ t in a'..b', f (γ.toFun t) * deriv γ.toFun t =
      F (γ.toFun b') - F (γ.toFun a') := by
  induction n generalizing a' b' with
  | zero =>
    exact ftc_no_interior_partition γ a' b' h_int hFγ_cont
      hFγ_deriv_off ha'b' hsub (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))
  | succ m ih =>
    by_cases hempty : γ.partition.filter (fun t => a' < t ∧ t < b') = ∅
    · exact ftc_no_interior_partition γ a' b' h_int hFγ_cont hFγ_deriv_off ha'b' hsub hempty
    · obtain ⟨c, hc_filt⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      simp only [Finset.mem_filter] at hc_filt
      exact ftc_inductive_step γ m a' b' c h_int
        (fun a'' b'' hc' hab'' hsub'' haP'' hbP'' =>
          ih a'' b'' hc' hab'' hsub'' haP'' hbP'')
        hcard ha'b' hsub ha'P hb'P hc_filt.1 hc_filt.2.1 hc_filt.2.2

/-- Fundamental theorem of calculus for piecewise C¹ contours: if `F` is a
primitive of `f` on `U` (i.e. `HasDerivAt F (f z) z` for every `z ∈ U`) and
`γ` is a piecewise C¹ curve lying in `U`, then
`∫_γ f(z) dz = F(γ(b)) - F(γ(a))`. -/
theorem ftc_piecewise_contour {F : ℂ → ℂ} {f : ℂ → ℂ}
    (γ : PiecewiseC1Curve) (U : Set ℂ) (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hF_prim : ∀ z ∈ U, HasDerivAt F (f z) z)
    (h_int : IntervalIntegrable
      (fun t => f (γ.toFun t) * deriv γ.toFun t) volume γ.a γ.b) :
    ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t =
      F (γ.toFun γ.b) - F (γ.toFun γ.a) := by
  have hFγ_cont : ContinuousOn (F ∘ γ.toFun) (Icc γ.a γ.b) :=
    (ContinuousOn.comp (fun z hz => (hF_prim z hz).continuousAt.continuousWithinAt)
      γ.continuous_toFun (fun t ht => hγ_in_U t ht))
  have hFγ_deriv_off : ∀ t ∈ Ioo γ.a γ.b, t ∉ (↑γ.partition : Set ℝ) →
      HasDerivAt (F ∘ γ.toFun) (f (γ.toFun t) * deriv γ.toFun t) t := by
    intro t ht_Ioo ht_nP
    convert (hF_prim (γ.toFun t) (hγ_in_U t (Ioo_subset_Icc_self ht_Ioo))).comp_of_eq t
      (γ.smooth_off_partition t (Ioo_subset_Icc_self ht_Ioo) ht_nP).hasDerivAt rfl using 1
  exact ftc_piecewise_contour_induction γ _ γ.a γ.b h_int hFγ_cont hFγ_deriv_off
    le_rfl (le_of_lt γ.hab) (Subset.refl _)
    γ.endpoints_in_partition.1 γ.endpoints_in_partition.2

private lemma mem_Ioo_of_Icc_not_partition (γ : PiecewiseC1Curve)
    (t : ℝ) (ht_Icc : t ∈ Icc γ.a γ.b) (ht_not_part : t ∉ (γ.partition : Set ℝ)) :
    t ∈ Ioo γ.a γ.b := by
  constructor
  · by_contra h; push Not at h
    exact ht_not_part (le_antisymm h ht_Icc.1 ▸ γ.endpoints_in_partition.1)
  · by_contra h; push Not at h
    exact ht_not_part (le_antisymm ht_Icc.2 h ▸ γ.endpoints_in_partition.2)

/-- The integrand `(γ(t) - z)⁻¹ · γ'(t)` is interval-integrable whenever `z`
is not in the image of `γ`. The proof uses compactness of `[a, b]` to bound
`‖(γ(t) - z)⁻¹‖` and the piecewise C¹ bound on `‖γ'(t)‖`. -/
theorem integrand_intervalIntegrable_of_avoids (γ : PiecewiseC1Immersion)
    (z : ℂ) (h_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z) :
    IntervalIntegrable
      (fun t => (γ.toFun t - z)⁻¹ * deriv γ.toFun t) volume γ.a γ.b := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  have h_inv_cont : ContinuousOn (fun t => (γ.toFun t - z)⁻¹) (Icc γ.a γ.b) :=
    ContinuousOn.inv₀ (γ.continuous_toFun.sub continuousOn_const)
      (fun t ht => sub_ne_zero.mpr (h_avoids t ht))
  obtain ⟨M_inv, hM_inv⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (h_inv_cont.norm)
  obtain ⟨M_d, hM_d⟩ := piecewiseC1Immersion_deriv_bounded γ
  apply intervalIntegrable_of_piecewise_continuousOn_bounded
    (P := γ.partition) (M_inv * M_d) hab
  · intro t ⟨ht_Icc, ht_not_part⟩
    apply ContinuousWithinAt.mul
    · exact (h_inv_cont t ht_Icc).mono sdiff_subset
    · exact (γ.deriv_continuous_off_partition t
        (mem_Ioo_of_Icc_not_partition γ.toPiecewiseC1Curve t ht_Icc ht_not_part)
        ht_not_part).continuousWithinAt
  · intro t ht
    have h1 : ‖(γ.toFun t - z)⁻¹‖ ≤ M_inv := by
      simpa only [Real.norm_eq_abs, abs_norm] using hM_inv t ht
    calc ‖(γ.toFun t - z)⁻¹ * deriv γ.toFun t‖
        = ‖(γ.toFun t - z)⁻¹‖ * ‖deriv γ.toFun t‖ := norm_mul _ _
      _ ≤ M_inv * M_d :=
          mul_le_mul h1 (hM_d t ht) (norm_nonneg _) (le_trans (norm_nonneg _) h1)

/-- Every closed curve in a convex open set is null-homologous.

The proof uses:
1. `generalizedWindingNumber_eq_classical_away` to reduce the PV winding
   number to a classical contour integral (since z is not on the curve).
2. `holomorphic_convex_primitive` to obtain a primitive F of w |-> (w - z)^{-1}
   on the convex set U.
3. The fundamental theorem of calculus to evaluate the integral as
   F(gamma(b)) - F(gamma(a)) = 0 (since gamma is closed). -/
theorem isNullHomologous_of_convex (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U)
    (hU_ne : U.Nonempty) (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) :
    IsNullHomologous γ U where
  closed := hγ_closed
  image_subset := hγ_in_U
  winding_zero := by
    intro z hz
    have h_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z :=
      fun t ht heq => hz (heq ▸ hγ_in_U t ht)
    rw [generalizedWindingNumber_eq_classical_away γ.toPiecewiseC1Curve z h_avoids]
    have h_ne_z : ∀ w ∈ U, w - z ≠ 0 :=
      fun w hw => sub_ne_zero.mpr (fun heq => hz (heq ▸ hw))
    have h_holo : DifferentiableOn ℂ (fun w => (w - z)⁻¹) U := fun w hw =>
      ((differentiableAt_id.sub (differentiableAt_const z)).inv
        (h_ne_z w hw)).differentiableWithinAt
    obtain ⟨F, hF⟩ := holomorphic_convex_primitive hU_convex hU hU_ne h_holo
    have h_int := integrand_intervalIntegrable_of_avoids γ z h_avoids
    rw [ftc_piecewise_contour γ.toPiecewiseC1Curve U hγ_in_U hF h_int,
      congrArg F hγ_closed.symm, sub_self, mul_zero]


end
