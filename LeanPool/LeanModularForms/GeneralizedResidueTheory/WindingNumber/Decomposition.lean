/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.WindingNumber.CrossingAnalysis

/-!
# Winding Number: H-W Decomposition Theorems

The main decomposition results for generalized winding numbers,
showing how the winding number splits into an external integer
winding contribution and crossing angle contributions.

## Main Results

* `exp_pv_eq_exp_neg_crossing_angle` — FTC + direction limit for CPV
* `externalWindingContribution_isInt` — external winding is an integer
* `generalizedWindingNumber_eq_external_sub_angle` — H-W Prop 2.2 decomposition
* `generalizedWindingNumber_eq_neg_angleContribution_single` — N=0 specialization
* `generalizedWindingNumber_eq_neg_half_smooth_crossing` — smooth crossing gives -1/2
* `windingNumberWithAngles_union` — additivity over disjoint crossings
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- Endpoints of the curve do not cross `z₀` when the unique crossing is in the interior. -/
private lemma no_endpoint_crossing_of_unique_interior
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (honly : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = z₀ → t = t₀) :
    γ.toFun γ.a ≠ z₀ ∧ γ.toFun γ.b ≠ z₀ := by
  constructor
  · intro h; have := honly γ.a (left_mem_Icc.mpr γ.hab.le) h; linarith [ht₀.1]
  · intro h; have := honly γ.b (right_mem_Icc.mpr γ.hab.le) h; linarith [ht₀.2]

/-- CPV of `(z - z₀)⁻¹` exists when there is a unique crossing at `t₀`. -/
private lemma cpv_exists_of_unique_crossing
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (honly : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = z₀ → t = t₀)
    (hγ_meas : Measurable γ.toFun)
    (hC2 : ContDiffAt ℝ 2 γ.toFun t₀)
    (h_cont_deriv : ∃ a' b', t₀ ∈ Ioo a' b' ∧
      Icc a' b' ⊆ Icc γ.a γ.b ∧
      ContinuousOn (deriv γ.toFun) (Icc a' b')) :
    CauchyPrincipalValueExists'
      (fun z => (z - z₀)⁻¹) γ.toFun γ.a γ.b z₀ := by
  exact cpv_exists_inv_sub γ z₀ hγ_meas
    (no_endpoint_crossing_of_unique_interior γ z₀ t₀ ht₀ honly)
    (fun t ht hγt => by rw [honly t (Ioo_subset_Icc_self ht) hγt]; exact hC2)
    (fun t ht hγt => by rw [honly t (Ioo_subset_Icc_self ht) hγt]; exact h_cont_deriv)

/-- The Cauchy PV in canonical form equals the limit of the cutoff integrals. -/
private lemma cpv_inv_sub_eq_limit
    (γ : PiecewiseC1Immersion) (z₀ : ℂ) (L : ℂ)
    (hL : Tendsto (fun ε => ∫ t in γ.a..γ.b,
      if ‖γ.toFun t - z₀‖ > ε
      then (fun z => (z - z₀)⁻¹) (γ.toFun t) * deriv γ.toFun t
      else 0) (𝓝[>] 0) (𝓝 L)) :
    cauchyPrincipalValue' (·⁻¹)
      (fun t => γ.toFun t - z₀) γ.a γ.b 0 = L := by
  have hL' : Tendsto (fun ε => ∫ t in γ.a..γ.b,
      if ‖(fun t => γ.toFun t - z₀) t - 0‖ > ε
      then (·⁻¹) ((fun t => γ.toFun t - z₀) t) *
        deriv (fun t => γ.toFun t - z₀) t
      else 0) (𝓝[>] 0) (𝓝 L) := by
    exact hL.congr fun ε => by congr 1 with t; simp only [sub_zero, deriv_sub_const]
  unfold cauchyPrincipalValue'; exact hL'.limUnder_eq

/-- **FTC + direction limit**: For a closed piecewise C¹ immersion with unique crossing
at t₀ through z₀, the exponential of the Cauchy PV integral equals `exp(-i · α)` where
`α` is the crossing angle.

Proved by combining:
- PV existence (`cpv_exists_inv_sub`)
- Continuity of `exp` composed with the PV limit
- The core analysis (`tendsto_exp_cutoff_integral_crossing`)
- Uniqueness of limits in a T₂ space -/
theorem exp_pv_eq_exp_neg_crossing_angle
    (γ : PiecewiseC1Immersion)
    (hclosed : γ.toPiecewiseC1Curve.IsClosed) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (hcross : γ.toFun t₀ = z₀)
    (honly : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = z₀ → t = t₀)
    (hγ_meas : Measurable γ.toFun)
    (hC2 : ContDiffAt ℝ 2 γ.toFun t₀)
    (h_cont_deriv : ∃ a' b', t₀ ∈ Ioo a' b' ∧
      Icc a' b' ⊆ Icc γ.a γ.b ∧
      ContinuousOn (deriv γ.toFun) (Icc a' b')) :
    Complex.exp (cauchyPrincipalValue' (·⁻¹)
      (fun t => γ.toFun t - z₀) γ.a γ.b 0) =
    Complex.exp (-(I * angleAtCrossing γ t₀ ht₀)) := by
  obtain ⟨L, hL⟩ :=
    cpv_exists_of_unique_crossing γ z₀ t₀ ht₀ honly hγ_meas hC2 h_cont_deriv
  -- exp(R(ε)) → exp(L) by continuity; exp(R(ε)) → exp(-iα) by core analysis
  have h_exp_target :=
    tendsto_exp_cutoff_integral_crossing γ hclosed z₀ t₀ ht₀ hcross honly
  rw [cpv_inv_sub_eq_limit γ z₀ L hL]
  exact tendsto_nhds_unique
    (Complex.continuous_exp.continuousAt.tendsto.comp hL) h_exp_target

/-- The external winding contribution equals an integer when `exp(L) = exp(-iα)`.
Given that the CPV equals `L` and `L = -iα + n·(2πi)`, the external winding is `n`. -/
private lemma externalWindingContribution_eq_int_of_cpv_eq
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (L : ℂ) (n : ℤ)
    (hPV_eq : cauchyPrincipalValue' (·⁻¹)
      (fun t => γ.toFun t - z₀) γ.a γ.b 0 = L)
    (hn : L = -(I * ↑(angleAtCrossing γ t₀ ht₀)) + ↑n * (2 * ↑Real.pi * I)) :
    externalWindingContribution γ z₀ t₀ ht₀ = n := by
  unfold externalWindingContribution generalizedWindingNumber'
  rw [hPV_eq, hn]
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2pi_ne : (2 : ℂ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero hpi_ne
  have h2pii_ne : 2 * Real.pi * I ≠ 0 := mul_ne_zero h2pi_ne I_ne_zero
  field_simp
  ring

/-- The external winding contribution is always an integer.
This is the key structural result from H-W Proposition 2.2:
the generalized winding number decomposes as `N - α/(2π)` where
`α` is the crossing angle and `N ∈ ℤ` is the classical winding
of the modified curve.

The regularity hypotheses (`hγ_meas`, `hC2`, `h_cont_deriv`) ensure that the
Cauchy PV integral of `1/(z-z₀)` converges, so the generalized winding number
is well-defined (not the default value 0). -/
theorem externalWindingContribution_isInt
    (γ : PiecewiseC1Immersion)
    (hclosed : γ.toPiecewiseC1Curve.IsClosed) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (hcross : γ.toFun t₀ = z₀)
    (honly : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = z₀ → t = t₀)
    -- Regularity hypotheses (needed for PV existence):
    (hγ_meas : Measurable γ.toFun)
    (hC2 : ContDiffAt ℝ 2 γ.toFun t₀)
    (h_cont_deriv : ∃ a' b', t₀ ∈ Ioo a' b' ∧
      Icc a' b' ⊆ Icc γ.a γ.b ∧
      ContinuousOn (deriv γ.toFun) (Icc a' b')) :
    ∃ N : ℤ, externalWindingContribution γ z₀ t₀ ht₀ = N := by
  obtain ⟨L, hL⟩ :=
    cpv_exists_of_unique_crossing γ z₀ t₀ ht₀ honly hγ_meas hC2 h_cont_deriv
  have hPV_eq := cpv_inv_sub_eq_limit γ z₀ L hL
  -- exp(PV) = exp(-i·α) by FTC + direction limit, so exp(L) = exp(-iα)
  have h_exp := exp_pv_eq_exp_neg_crossing_angle γ hclosed z₀ t₀ ht₀
    hcross honly hγ_meas hC2 h_cont_deriv
  rw [hPV_eq] at h_exp
  -- From exp(L) = exp(-iα), get L = -iα + n·(2πi)
  rw [Complex.exp_eq_exp_iff_exists_int] at h_exp
  obtain ⟨n, hn⟩ := h_exp
  exact ⟨n, externalWindingContribution_eq_int_of_cpv_eq γ z₀ t₀ ht₀ L n hPV_eq hn⟩

/-- H-W Proposition 2.2: The generalized winding number decomposes as
the external winding integer minus the crossing angle contribution.
`n_{z₀}(γ) = N - α/(2π)` where `N` is the external winding. -/
theorem generalizedWindingNumber_eq_external_sub_angle
    (γ : PiecewiseC1Immersion)
    (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) :
    generalizedWindingNumber' γ.toFun γ.a γ.b z₀ =
      externalWindingContribution γ z₀ t₀ ht₀ -
        (angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * Real.pi) := by
  simp only [externalWindingContribution, add_sub_cancel_right]

/-- H-W Proposition 2.3 (specialized): For a closed piecewise C¹ immersion
passing through z₀ exactly once at t₀, with zero external winding, the
generalized winding number equals minus the crossing angle divided by 2π. -/
theorem generalizedWindingNumber_eq_neg_angleContribution_single
    (γ : PiecewiseC1Immersion)
    (_hclosed : γ.toPiecewiseC1Curve.IsClosed) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (_hcross : γ.toFun t₀ = z₀)
    (_honly : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = z₀ → t = t₀)
    (h_external : externalWindingContribution γ z₀ t₀ ht₀ = 0) :
    generalizedWindingNumber' γ.toFun γ.a γ.b z₀ =
      -((angleAtCrossing γ t₀ ht₀ : ℂ) /
        (2 * Real.pi)) := by
  have := generalizedWindingNumber_eq_external_sub_angle γ z₀ t₀ ht₀
  rw [h_external, zero_sub] at this
  exact this

/-- At a smooth crossing with zero external winding, contribution is -1/2. -/
theorem generalizedWindingNumber_eq_neg_half_smooth_crossing
    (γ : PiecewiseC1Immersion)
    (hclosed : γ.toPiecewiseC1Curve.IsClosed) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (hcross : γ.toFun t₀ = z₀)
    (honly : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = z₀ → t = t₀)
    (hsmooth : t₀ ∉ γ.toPiecewiseC1Curve.partition)
    (h_external : externalWindingContribution γ z₀ t₀ ht₀ = 0) :
    generalizedWindingNumber' γ.toFun γ.a γ.b z₀ =
      -(1 / 2) := by
  rw [generalizedWindingNumber_eq_neg_angleContribution_single
    γ hclosed z₀ t₀ ht₀ hcross honly h_external,
    angleAtCrossing_smooth γ t₀ ht₀ hsmooth]
  have : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [this]

/-- At a corner crossing with angle α and zero external winding,
contribution is -α/(2π). -/
theorem generalizedWindingNumber_eq_neg_corner_contribution
    (γ : PiecewiseC1Immersion)
    (hclosed : γ.toPiecewiseC1Curve.IsClosed) (z₀ : ℂ)
    (t₀ : ℝ) (α : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (hcross : γ.toFun t₀ = z₀)
    (honly : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = z₀ → t = t₀)
    (hangle : angleAtCrossing γ t₀ ht₀ = α)
    (h_external : externalWindingContribution γ z₀ t₀ ht₀ = 0) :
    generalizedWindingNumber' γ.toFun γ.a γ.b z₀ =
      -(α / (2 * Real.pi)) := by
  rw [generalizedWindingNumber_eq_neg_angleContribution_single
    γ hclosed z₀ t₀ ht₀ hcross honly h_external,
    hangle]

/-- The external winding contribution vanishes when a curve with the same
winding number has zero external winding. This lets you prove the external
winding is zero by exhibiting a homotopy to a "model" curve (e.g., a sector
curve) whose winding number equals `-α/(2π)`. -/
theorem externalWindingContribution_zero_of_windingNumber_eq
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (h_eq : generalizedWindingNumber' γ.toFun γ.a γ.b z₀ =
      -((angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * Real.pi))) :
    externalWindingContribution γ z₀ t₀ ht₀ = 0 := by
  simp only [externalWindingContribution, h_eq, neg_add_cancel]

/-- The external winding contribution is translation-invariant. -/
theorem externalWindingContribution_translate
    (γ : PiecewiseC1Immersion) (c : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (z₀ : ℂ) :
    externalWindingContribution (γ.translate c) (z₀ + c) t₀ ht₀ =
    externalWindingContribution γ z₀ t₀ ht₀ := by
  simp only [externalWindingContribution, angleAtCrossing_translate]
  congr 1
  change generalizedWindingNumber' (γ.translate c).toFun γ.a γ.b (z₀ + c) =
    generalizedWindingNumber' γ.toFun γ.a γ.b z₀
  unfold generalizedWindingNumber'
  congr 1
  show cauchyPrincipalValue' (·⁻¹)
      (fun t => (γ.translate c).toFun t - (z₀ + c)) γ.a γ.b 0 =
    cauchyPrincipalValue' (·⁻¹)
      (fun t => γ.toFun t - z₀) γ.a γ.b 0
  have h_eq : (fun t => (γ.translate c).toFun t - (z₀ + c)) =
      (fun t => γ.toFun t - z₀) := by
    ext t; simp only [PiecewiseC1Immersion.translate]; ring
  rw [h_eq]

/-- Winding number with angles is additive over disjoint crossing sets. -/
theorem windingNumberWithAngles_union
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (S T : Finset ℝ) (hST : Disjoint S T)
    (hS_in : ∀ t ∈ S, t ∈ Ioo γ.a γ.b)
    (hT_in : ∀ t ∈ T, t ∈ Ioo γ.a γ.b)
    (hS_at : ∀ t ∈ S, γ.toFun t = z₀)
    (hT_at : ∀ t ∈ T, γ.toFun t = z₀) :
    windingNumberWithAngles' γ z₀ (S ∪ T)
      (fun t ht => by
        simp only [Finset.mem_union] at ht
        exact ht.elim (hS_in t) (hT_in t))
      (fun t ht => by
        simp only [Finset.mem_union] at ht
        exact ht.elim (hS_at t) (hT_at t)) =
    windingNumberWithAngles' γ z₀ S hS_in hS_at +
    windingNumberWithAngles' γ z₀ T hT_in hT_at := by
  simp only [windingNumberWithAngles']
  symm
  convert Finset.sum_union ?_
  any_goals exact hST
  any_goals try infer_instance
  case convert_6 =>
    exact fun x =>
      if hx : x ∈ S then
        (angleAtCrossing γ x (hS_in x hx) : ℂ) /
          (2 * Real.pi)
      else if hx : x ∈ T then
        (angleAtCrossing γ x (hT_in x hx) : ℂ) /
          (2 * Real.pi)
      else 0
  · rw [Finset.sum_union hST]
    congr! 1
    · refine Finset.sum_bij (fun x hx => x)
        ?_ ?_ ?_ ?_ <;> aesop
    · refine Finset.sum_bij (fun x hx => x.val)
        ?_ ?_ ?_ ?_ <;> aesop
  · rw [← Finset.sum_union hST]
    refine Finset.sum_bij (fun x hx => x.val)
      ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) -- TODO: convert to simp only
    tauto

end
