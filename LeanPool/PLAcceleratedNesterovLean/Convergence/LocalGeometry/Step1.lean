/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Core.NesterovScheme
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Local Geometry Step 1: Hessian Bounds via Continuity

## Normal Hessian (from Morse-Bott)
On M, D²f(m) ≥ μ in normal directions (PL ⟹ Morse-Bott).
By continuity of D²f and compactness, this extends to U₊ with constant μ'.

## Hessian lower bound
Since D²f(m) ≥ 0 for m ∈ M (minimizer) and D²f is continuous,
D²f(x) ≥ -εI on a neighborhood, with ε arbitrarily small.

Both arguments use: continuous function ≥ threshold on compact set ⟹
                     ≥ (threshold - δ) on a neighborhood.
-/

noncomputable section

namespace PLAcceleratedNesterovLean

/-- A continuous function that is positive on a compact set is bounded below
    by a positive constant. -/
theorem continuous_pos_lower_bound_compact {X : Type*} [TopologicalSpace X]
    (g : X → ℝ) (K : Set X) (hK : IsCompact K) (hK_ne : K.Nonempty)
    (hg : Continuous g) (hpos : ∀ x ∈ K, 0 < g x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, c ≤ g x := by
  obtain ⟨x₀, hx₀K, hx₀min⟩ := IsCompact.exists_isMinOn hK hK_ne hg.continuousOn
  exact ⟨g x₀, hpos x₀ hx₀K, fun x hx => hx₀min hx⟩

/-- If g is continuous and g ≥ c on a compact set K, then g ≥ c - δ on a neighborhood
    of K for any δ > 0. (Open set version.) -/
theorem continuous_lower_bound_neighborhood {X : Type*} [TopologicalSpace X]
    (g : X → ℝ) (K : Set X) (_hK : IsCompact K)
    (hg : Continuous g) (c : ℝ) (hc : ∀ x ∈ K, c ≤ g x) (δ : ℝ) (hδ : 0 < δ) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ ∀ x ∈ V, c - δ ≤ g x := by
  refine ⟨g ⁻¹' Set.Ioi (c - δ), isOpen_Ioi.preimage hg, ?_, ?_⟩
  · intro x hx
    simp only [Set.mem_preimage, Set.mem_Ioi]
    linarith [hc x hx]
  · intro x hx
    simp only [Set.mem_preimage, Set.mem_Ioi] at hx
    linarith

/-- PSD at minimizers: if m is a global minimizer of a function f that is C² at m,
    then D²f(m) ≥ 0. -/
theorem hessian_psd_at_minimizer {d : ℕ}
    (f : E d → ℝ) (m : E d)
    (hmin : ∀ y, f m ≤ f y)
    (hf : ContDiffAt ℝ 2 f m) :
    ∀ ξ : E d, hessianQuadForm f m ξ ≥ 0 := by
  intro ξ
  by_contra hlt
  push Not at hlt
  -- Define the 1D restriction φ(t) = f(m + t•ξ) and its derivative Φ(t)
  set ψ : ℝ → E d := fun t => m + t • ξ with hψ_def
  set φ : ℝ → ℝ := f ∘ ψ with hφ_def
  -- φ has a global min at 0
  have hφ_min : ∀ t, φ 0 ≤ φ t := fun t => by
    simp only [hφ_def, Function.comp, hψ_def, zero_smul, add_zero]; exact hmin _
  -- ψ has derivative ξ at every point
  have hψ_da : ∀ t, HasDerivAt ψ ξ t := fun t => by
    have := ((hasDerivAt_id t).smul_const ξ).const_add m
    simp_all
  -- ψ(0) = m
  have hψ0 : ψ 0 = m := by simp only [hψ_def, zero_smul, add_zero]
  -- ψ is smooth (affine map)
  have hψ_smooth : ContDiff ℝ ⊤ ψ := by
    simp only [hψ_def]
    exact contDiff_const.add (contDiff_id.smul (contDiff_const (c := ξ)))
  -- φ is C² at 0 by composition
  have hφ_C2 : ContDiffAt ℝ 2 φ 0 := by
    refine ContDiffAt.comp 0 ?_ (hψ_smooth.of_le le_top).contDiffAt
    rw [hψ0]; exact hf
  -- f is differentiable at m (C² at m → differentiable at m)
  have hf_diffAt : DifferentiableAt ℝ f m :=
    hf.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  -- f is differentiable in a neighborhood of m (C² at m with finite order → C² near m)
  have hf_diff_ev : ∀ᶠ x in nhds m, DifferentiableAt ℝ f x :=
    (hf.eventually (Ne.symm (ne_of_beq_false rfl))).mono
      fun x hx => hx.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  -- f is differentiable along ψ near t = 0
  have hψ_tendsto : Filter.Tendsto ψ (nhds 0) (nhds m) := by
    have h : ContinuousAt ψ 0 := hψ_smooth.continuous.continuousAt
    rwa [ContinuousAt, hψ0] at h
  have hf_diff_along : ∀ᶠ t in nhds (0 : ℝ), DifferentiableAt ℝ f (ψ t) :=
    hψ_tendsto.eventually hf_diff_ev
  -- φ has derivative (fderiv ℝ f m) ξ at t = 0
  have hφ_da0 : HasDerivAt φ ((fderiv ℝ f m) ξ) 0 := by
    have hfda : HasFDerivAt f (fderiv ℝ f m) (ψ 0) := by
      rw [hψ0]; exact hf_diffAt.hasFDerivAt
    exact hfda.comp_hasDerivAt 0 (hψ_da 0)
  -- φ is differentiable in a neighborhood of 0 (from C² at 0)
  have hφ_diff_ev : ∀ᶠ t in nhds (0 : ℝ), DifferentiableAt ℝ φ t :=
    (hφ_C2.eventually (Ne.symm (ne_of_beq_false rfl))).mono
      fun t ht => ht.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  -- At t = 0: Φ(0) = (fderiv ℝ f m) ξ = 0 (first-order optimality)
  have hmin_local : IsLocalMin φ 0 := Filter.Eventually.of_forall hφ_min
  have hΦ0 : (fderiv ℝ f m) ξ = 0 :=
    hmin_local.hasDerivAt_eq_zero hφ_da0
  -- deriv φ 0 = 0
  have hderiv_φ_0 : deriv φ 0 = 0 := by rw [hφ_da0.deriv, hΦ0]
  -- Key step: show deriv φ is negative on (0, δ) for some δ > 0.
  -- This uses the fact that hessianQuadForm f m ξ < 0 is the derivative of
  -- t ↦ (fderiv ℝ f (ψ t)) ξ at t = 0, and that value is 0 at t = 0.
  -- So the derivative of deriv φ at 0 is negative, making deriv φ negative for small t > 0.
  suffices h : ∃ t : ℝ, 0 < t ∧ φ t < φ 0 by
    obtain ⟨t, ht_pos, ht_lt⟩ := h
    linarith [hφ_min t]
  -- Step A: The function G(x) = (fderiv ℝ f x) ξ is C¹ at m
  set G : E d → ℝ := fun x => (fderiv ℝ f x) ξ with hG_def
  have hG_C1_at : ContDiffAt ℝ 1 G m :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiffAt_const
  have hG_diffAt : DifferentiableAt ℝ G m :=
    hG_C1_at.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  -- Step B: G(m) = 0 (first-order optimality at the minimizer)
  have hG_zero : G m = 0 := hΦ0
  -- Step C: HasDerivAt (G ∘ ψ) ((fderiv ℝ G m) ξ) 0
  have hGψ_da : HasDerivAt (G ∘ ψ) ((fderiv ℝ G m) ξ) 0 := by
    have hfda : HasFDerivAt G (fderiv ℝ G m) (ψ 0) := by rw [hψ0]; exact hG_diffAt.hasFDerivAt
    exact hfda.comp_hasDerivAt 0 (hψ_da 0)
  -- Step D: (fderiv ℝ G m) ξ = hessianQuadForm f m ξ
  -- G agrees with (fun x => inner (gradient f x) ξ) in a neighborhood of m.
  -- By Filter.EventuallyEq.fderiv_eq, their fderivs at m are equal.
  have hval_eq : (fderiv ℝ G m) ξ = hessianQuadForm f m ξ := by
    have hG_eq_ev : G =ᶠ[nhds m] (fun x => @inner ℝ (E d) _ (gradient f x) ξ) := by
      simp_all
    -- gradient f is differentiable at m (f C² at m ⟹ fderiv C¹ at m ⟹ toDual⁻¹ ∘ fderiv diff at m)
    have hgrad_diffAt : DifferentiableAt ℝ (gradient f) m := by
      set e := (InnerProductSpace.toDual ℝ (E d)).symm.toContinuousLinearEquiv
      have h1 : DifferentiableAt ℝ (fderiv ℝ f) m :=
        ContDiffAt.differentiableAt
          (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2))
          (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
      exact e.differentiable.differentiableAt.comp m h1
    -- fderiv of G at m equals fderiv of the inner product function at m
    have hfderiv_eq := hG_eq_ev.fderiv_eq (𝕜 := ℝ)
    simp only [hfderiv_eq, hessianQuadForm]
    rw [fderiv_inner_apply (𝕜 := ℝ) hgrad_diffAt (differentiableAt_const ξ)]
    simp only [fderiv_fun_const, Pi.zero_apply,
      zero_apply, inner_zero_right, zero_add]
  -- Step E: Extract that G(ψ t) < 0 for small t > 0
  rw [hval_eq] at hGψ_da
  -- HasDerivAt (G ∘ ψ) (hessianQuadForm f m ξ) 0, value < 0, (G ∘ ψ)(0) = G m = 0
  set c := hessianQuadForm f m ξ with hc_def
  have hc_neg : c < 0 := hlt
  -- From HasDerivAt, get the isLittleO / IsBigOWith condition
  have hGψ_0 : (G ∘ ψ) 0 = 0 := by simp only [Function.comp, hψ_def, zero_smul, add_zero, hG_zero]
  have hε : (0 : ℝ) < -c / 2 := by linarith
  have hev : ∀ᶠ t in nhds (0 : ℝ), ‖(G ∘ ψ) t - (G ∘ ψ) 0 - c * (t - 0)‖ ≤ -c / 2 * ‖t - 0‖ := by
    have := (hGψ_da.isLittleO.def' hε).bound
    refine this.mono fun t ht => ?_
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using ht
  rw [hGψ_0] at hev
  simp only [sub_zero] at hev
  -- Combine the HasDerivAt bound with differentiability conditions and extract a single δ
  have hcombined : ∀ᶠ t in nhds (0 : ℝ),
      ‖(G ∘ ψ) t - c * t‖ ≤ -c / 2 * ‖t‖ ∧
      DifferentiableAt ℝ f (ψ t) ∧
      DifferentiableAt ℝ φ t := by
    simp_all
  rw [Metric.eventually_nhds_iff] at hcombined
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := hcombined
  -- For t with dist t 0 < δ: (G ∘ ψ) t = deriv φ t (by chain rule using differentiability of f)
  have hG_eq_deriv_near : ∀ t, dist t 0 < δ → (G ∘ ψ) t = deriv φ t := by
    intro t ht
    have hft := (hδ_bound ht).2.1
    simp only [Function.comp, hG_def]
    exact ((hft.hasFDerivAt.comp_hasDerivAt t (hψ_da t)).deriv).symm
  -- Take t = δ / 2
  have ht_pos : (0 : ℝ) < δ / 2 := by linarith
  have ht_dist : dist (δ / 2) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht_pos]; linarith
  have hbound := (hδ_bound ht_dist).1
  -- hbound : ‖G(ψ(δ/2)) - c * (δ/2)‖ ≤ (-c/2) * ‖δ/2‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht_pos] at hbound
  -- |G(ψ(δ/2)) - c*(δ/2)| ≤ (-c/2) * (δ/2)
  -- So G(ψ(δ/2)) ≤ c*(δ/2) + (-c/2)*(δ/2) = (c/2)*(δ/2) < 0
  have hG_neg : (G ∘ ψ) (δ / 2) < 0 := by
    have := abs_le.mp (le_of_le_of_eq hbound rfl)
    nlinarith
  -- deriv φ (δ/2) < 0
  rw [hG_eq_deriv_near _ ht_dist] at hG_neg
  -- Step F: Use strictAntiOn_of_deriv_neg to show φ decreases on [0, δ/2]
  have hderiv_neg : ∀ x ∈ Set.Ioo (0 : ℝ) (δ / 2), deriv φ x < 0 := by
    intro x ⟨hx_pos, hx_lt⟩
    have hx_dist : dist x 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hx_pos]; linarith
    have hbx := (hδ_bound hx_dist).1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx_pos] at hbx
    rw [← hG_eq_deriv_near x hx_dist]
    have := abs_le.mp (le_of_le_of_eq hbx rfl)
    nlinarith
  -- φ is continuous on [0, δ/2] (from differentiability in the ball)
  have hφ_cont_Icc : ContinuousOn φ (Set.Icc 0 (δ / 2)) := by
    have : DifferentiableOn ℝ φ (Set.Icc 0 (δ / 2)) := by
      intro t ht
      have ht_dist : dist t 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
        linarith [ht.2]
      exact ((hδ_bound ht_dist).2.2).differentiableWithinAt
    exact this.continuousOn
  -- interior of [0, δ/2] = (0, δ/2) for which we showed deriv < 0
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) (δ / 2)) := convex_Icc 0 (δ / 2)
  have hinterior : interior (Set.Icc (0 : ℝ) (δ / 2)) = Set.Ioo 0 (δ / 2) := by
    exact interior_Icc
  have hanti : StrictAntiOn φ (Set.Icc (0 : ℝ) (δ / 2)) :=
    strictAntiOn_of_deriv_neg hconv hφ_cont_Icc (by rwa [hinterior])
  -- φ(δ/2) < φ(0)
  exact ⟨δ / 2, ht_pos, hanti (Set.left_mem_Icc.mpr (le_of_lt ht_pos))
    (Set.right_mem_Icc.mpr (le_of_lt ht_pos)) ht_pos⟩

end PLAcceleratedNesterovLean
