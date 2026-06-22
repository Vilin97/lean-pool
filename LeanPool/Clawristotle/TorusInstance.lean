/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.TorusIntegration
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# FlatTorus3 Instance for T^3

Proves the remaining `FlatTorus3` axioms (Laplacian maximum principle, Killing
implies harmonic, curl-div implies harmonic) and assembles the full `FlatTorus3`
instance on `Fin 3 -> AddCircle 1`.
-/

open MeasureTheory Matrix Finset BigOperators Real Filter

noncomputable section

-- ============================================================================
-- ℝⁿ lemmas (proved in aristotle-in/, integrated here)
-- ============================================================================

/-- At a local maximum of a twice-differentiable function, the second derivative is nonpositive.
    Proved by Aristotle. -/
private theorem second_deriv_nonpos_at_local_max' {f : ℝ → ℝ} {x₀ : ℝ}
    (hmax : IsLocalMax f x₀)
    (hf' : ∀ᶠ x in nhds x₀, DifferentiableAt ℝ f x)
    (hf'' : DifferentiableAt ℝ (deriv f) x₀) :
    deriv (deriv f) x₀ ≤ 0 := by
  have h_first_deriv_zero : deriv f x₀ = 0 := IsLocalMax.deriv_eq_zero hmax
  by_contra h_contra; push Not at h_contra
  obtain ⟨ε, hε⟩ : ∃ ε > 0, ∀ x ∈ Set.Ioo x₀ (x₀ + ε), deriv f x > 0 := by
    have := Metric.tendsto_nhds_nhds.1 (hf''.hasDerivAt.isLittleO.tendsto_div_nhds_zero)
    obtain ⟨δ, δ_pos, H⟩ := this _ h_contra
    use δ, δ_pos
    intro x hx
    have := H (show |x - x₀| < δ from abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    simp_all only [gt_iff_lt, sub_zero, smul_eq_mul, div_eq_mul_inv, dist_zero_right, norm_mul,
      norm_eq_abs, norm_inv, Set.mem_Ioo]
    rw [← div_eq_mul_inv, div_lt_iff₀] at this <;>
      cases abs_cases (deriv f x - (x - x₀) * deriv (deriv f) x₀) <;>
      cases abs_cases (x - x₀) <;>
      nlinarith [mul_pos (sub_pos.mpr hx.1) h_contra]
  have h_mvt : ∀ x ∈ Set.Ioo x₀ (x₀ + ε),
      ∃ c ∈ Set.Ioo x₀ x, deriv f c = (f x - f x₀) / (x - x₀) := by
    intros x hx
    apply exists_deriv_eq_slope f hx.left
    · exact continuousOn_of_forall_continuousAt fun y hy =>
        if h : y = x₀ then by rw [h]; exact DifferentiableAt.continuousAt hf'.self_of_nhds
        else DifferentiableAt.continuousAt (differentiableAt_of_deriv_ne_zero
          (ne_of_gt (hε.2 y ⟨lt_of_le_of_ne hy.1 (Ne.symm h), by linarith [hy.2, hx.2]⟩)))
    · exact fun y hy => DifferentiableAt.differentiableWithinAt
        (differentiableAt_of_deriv_ne_zero (ne_of_gt (hε.2 y ⟨hy.1, hy.2.trans hx.2⟩)))
  have h_inc : ∀ x ∈ Set.Ioo x₀ (x₀ + ε), f x > f x₀ := by
    intro x hx; obtain ⟨c, hc₁, hc₂⟩ := h_mvt x hx
    have := hε.2 c ⟨by linarith [hc₁.1, hx.1], by linarith [hc₁.2, hx.2]⟩
    rw [eq_div_iff] at hc₂ <;> nlinarith [hc₁.1, hc₁.2]
  rcases Metric.eventually_nhds_iff.mp hmax with ⟨δ, hδ, hδ'⟩
  exact absurd (h_inc (x₀ + Min.min ε δ / 2) ⟨by linarith [lt_min hε.1 hδ],
      by linarith [min_le_left ε δ, min_le_right ε δ]⟩)
    (not_lt_of_ge <| hδ' <| mem_ball_iff_norm.mpr <| abs_lt.mpr
      ⟨by linarith [lt_min hε.1 hδ, min_le_left ε δ, min_le_right ε δ],
       by linarith [lt_min hε.1 hδ, min_le_left ε δ, min_le_right ε δ]⟩)

/-- Killing equation on ℝⁿ implies each component is harmonic. -/
private theorem killing_harmonic_rn' {n : ℕ} (b : (Fin n → ℝ) → (Fin n → ℝ))
    (hb : ∀ j, ContDiff ℝ 2 (fun y => b y j))
    (hKilling : ∀ x i j,
      fderiv ℝ (fun y => b y j) x (Pi.single i 1) +
      fderiv ℝ (fun y => b y i) x (Pi.single j 1) = 0)
    (j : Fin n) (x : Fin n → ℝ) :
    ∑ i : Fin n,
        fderiv ℝ (fun y => fderiv ℝ (fun z => b z j) y (Pi.single i 1)) x (Pi.single i 1) = 0 := by
  apply Finset.sum_eq_zero; intro i _
  have hK_fun : ∀ y, fderiv ℝ (fun z => b z j) y (Pi.single i 1) =
      -(fderiv ℝ (fun z => b z i) y (Pi.single j 1)) := by
    intro y; linarith [hKilling y i j]
  have hfun_eq : (fun y => fderiv ℝ (fun z => b z j) y (Pi.single i 1)) =
      (fun y => -(fderiv ℝ (fun z => b z i) y (Pi.single j 1))) := funext hK_fun
  rw [hfun_eq]
  have hdiff_j : Differentiable ℝ (fun y => fderiv ℝ (fun z => b z i) y (Pi.single j 1)) := by
    have : ContDiff ℝ 1 (fun y => fderiv ℝ (fun z => b z i) y (Pi.single j 1)) := by
      apply ContDiff.clm_apply
      · exact (hb i).fderiv_right le_rfl
      · exact contDiff_const
    exact this.differentiable one_ne_zero
  have hfun_neg : (fun y => -(fderiv ℝ (fun z => b z i) y (Pi.single j 1))) =
      -(fun y => fderiv ℝ (fun z => b z i) y (Pi.single j 1)) := by ext; simp
  rw [hfun_neg, fderiv_neg]
  simp only [_root_.neg_apply, neg_eq_zero]
  rw [clairaut_fderiv (fun z => b z i) x i j (hb i)]
  have hK_diag_fun : (fun y => fderiv ℝ (fun z => b z i) y (Pi.single i 1)) = fun _ => 0 := by
    ext y; linarith [hKilling y i i]
  rw [hK_diag_fun]; simp

/-- Irrotational + solenoidal → each component is harmonic on ℝⁿ. -/
private theorem curl_div_harmonic_rn' {n : ℕ} (F : (Fin n → ℝ) → (Fin n → ℝ))
    (hF : ∀ i, ContDiff ℝ 2 (fun y => F y i))
    (hcurl : ∀ x i j,
      fderiv ℝ (fun y => F y j) x (Pi.single i 1) =
      fderiv ℝ (fun y => F y i) x (Pi.single j 1))
    (hdiv : ∀ x, ∑ i : Fin n,
      fderiv ℝ (fun y => F y i) x (Pi.single i 1) = 0)
    (j : Fin n) (x : Fin n → ℝ) :
    ∑ i : Fin n,
        fderiv ℝ (fun y => fderiv ℝ (fun z => F z j) y (Pi.single i 1)) x (Pi.single i 1) = 0 := by
  have hcurl_fun : ∀ i, (fun y => fderiv ℝ (fun z => F z j) y (Pi.single i 1)) =
      (fun y => fderiv ℝ (fun z => F z i) y (Pi.single j 1)) := by
    intro i
    ext y
    exact hcurl y i j
  simp_rw [hcurl_fun]
  simp_rw [clairaut_fderiv (fun z => F z _) x _ j (hF _)]
  have hdiff_comp : ∀ i,
      DifferentiableAt ℝ (fun y => fderiv ℝ (fun z => F z i) y (Pi.single i 1)) x := by
    intro i
    have : ContDiff ℝ 1 (fun y => fderiv ℝ (fun z => F z i) y (Pi.single i 1)) :=
      ContDiff.clm_apply ((hF i).fderiv_right le_rfl) contDiff_const
    exact (this.differentiable one_ne_zero).differentiableAt
  have : ∑ i : Fin n,
        fderiv ℝ (fun y => fderiv ℝ (fun z => F z i) y (Pi.single i 1)) x (Pi.single j 1) =
      (∑ i : Fin n,
        fderiv ℝ (fun y => fderiv ℝ (fun z => F z i) y (Pi.single i 1)) x) (Pi.single j 1) :=
    (_root_.sum_apply _ _ _).symm
  rw [this]
  have hfsum : (∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ (fun z => F z i) y (Pi.single i 1)) x) =
      fderiv ℝ (fun y => ∑ i : Fin n, fderiv ℝ (fun z => F z i) y (Pi.single i 1)) x := by
    rw [fderiv_fun_sum (fun i _ => hdiff_comp i)]
  rw [hfsum]
  have hsum_fun :
      (fun y => ∑ i : Fin n, fderiv ℝ (fun z => F z i) y (Pi.single i 1)) = fun _ => 0 :=
    funext hdiv
  rw [hsum_fun]; simp

-- ============================================================================

/-- hLaplacianMaxNonpos: Δφ ≤ 0 at a global maximum.
    Second derivative test: at a maximum, the Hessian is negative semi-definite,
    so its trace (= Laplacian) ≤ 0. -/
theorem torus_hLaplacianMaxNonpos (φ : Torus3 → ℝ) (x₀ : Torus3)
    (hd : ContDiff ℝ 1 (periodicLift φ))
    (hmax : ∀ x, φ x ≤ φ x₀) :
    torusDivX (torusGradX φ) x₀ ≤ 0 := by
  simp only [torusDivX]
  -- Rewrite using periodicLift_torusGradX
  simp_rw [show ∀ i, (fun y => periodicLift (fun z => torusGradX φ z i) y) =
      (fun y => fderiv ℝ (periodicLift φ) y (Pi.single i 1)) from
      fun i => funext (periodicLift_torusGradX φ i)]
  -- Let x₀' be the canonical preimage of x₀
  set x₀' := (torusMk_surjective x₀).choose
  -- For each i, show the term is ≤ 0
  apply Finset.sum_nonpos; intro i _
  -- Let hᵢ y = fderiv ℝ (periodicLift φ) y (Pi.single i 1)
  -- Case split: either hᵢ is differentiable at x₀' or not
  by_cases hdiff : DifferentiableAt ℝ (fun y => fderiv ℝ (periodicLift φ) y (Pi.single i 1)) x₀'
  · -- Case: hᵢ is differentiable at x₀'. Use 1D second derivative test.
    -- Let gᵢ t = periodicLift φ (x₀' + t • eᵢ)
    let eᵢ : Fin 3 → ℝ := Pi.single i 1
    let gᵢ : ℝ → ℝ := fun t => periodicLift φ (x₀' + t • eᵢ)
    -- gᵢ has global max at 0
    have hmax_gi : IsLocalMax gᵢ 0 :=
      Filter.Eventually.mono Filter.univ_mem fun t _ => by
        simp only [gᵢ, zero_smul, add_zero, periodicLift, Function.comp_apply]
        rw [(torusMk_surjective x₀).choose_spec]
        exact hmax (torusMk (x₀' + t • eᵢ))
    -- Helper: the path t ↦ x₀' + t • eᵢ has derivative eᵢ
    have hpath_hd : ∀ t, HasDerivAt (fun s => x₀' + s • eᵢ) eᵢ t := fun t => by
      have hsmul : HasDerivAt (fun s : ℝ => s • eᵢ) eᵢ t := by
        have h := (hasDerivAt_id t).smul_const eᵢ
        simp only [id, one_smul] at h; exact h
      simpa using hsmul.const_add x₀'
    -- gᵢ is differentiable everywhere (since periodicLift φ is C¹)
    have hd_diff : Differentiable ℝ (periodicLift φ) := hd.differentiable one_ne_zero
    have hgi_diff : ∀ t, DifferentiableAt ℝ gᵢ t := fun t =>
      hd_diff.differentiableAt.comp t (hpath_hd t).differentiableAt
    -- deriv gᵢ = hᵢ ∘ (x₀' + · • eᵢ)
    have hderiv_gi : ∀ t, deriv gᵢ t = fderiv ℝ (periodicLift φ) (x₀' + t • eᵢ) eᵢ := fun t =>
      (hd_diff.differentiableAt.hasFDerivAt.comp_hasDerivAt t (hpath_hd t)).deriv
    -- deriv gᵢ is differentiable at 0 (since hᵢ is diff at x₀')
    have hderiv_gi_diff : DifferentiableAt ℝ (deriv gᵢ) 0 := by
      rw [show deriv gᵢ = fun t => fderiv ℝ (periodicLift φ) (x₀' + t • eᵢ) eᵢ from
            funext hderiv_gi]
      change DifferentiableAt ℝ
          ((fun y => fderiv ℝ (periodicLift φ) y eᵢ) ∘ (fun t : ℝ => x₀' + t • eᵢ)) 0
      apply DifferentiableAt.comp
      · simp only [zero_smul, add_zero]; exact hdiff
      · exact (hpath_hd 0).differentiableAt
    -- Apply 1D second derivative test
    have h1d : deriv (deriv gᵢ) 0 ≤ 0 :=
      second_deriv_nonpos_at_local_max' hmax_gi
        (Filter.Eventually.mono Filter.univ_mem (fun t _ => hgi_diff t))
        hderiv_gi_diff
    -- Connect: fderiv ℝ hᵢ x₀' eᵢ = deriv (deriv gᵢ) 0
    have hconnect : deriv (deriv gᵢ) 0 =
        fderiv ℝ (fun y => fderiv ℝ (periodicLift φ) y eᵢ) x₀' eᵢ := by
      rw [show deriv gᵢ = fun t : ℝ => fderiv ℝ (periodicLift φ) (x₀' + t • eᵢ) eᵢ from
            funext hderiv_gi]
      -- Use chain rule: g ∘ f has deriv (fderiv g x₀') eᵢ at 0
      -- where g = fun y => fderiv ... y eᵢ, f = fun t => x₀' + t • eᵢ
      have hfda : HasFDerivAt (fun y => fderiv ℝ (periodicLift φ) y eᵢ)
          (fderiv ℝ (fun y => fderiv ℝ (periodicLift φ) y eᵢ) x₀') (x₀' + (0 : ℝ) • eᵢ) := by
        simp only [zero_smul, add_zero]; exact hdiff.hasFDerivAt
      exact (hfda.comp_hasDerivAt 0 (hpath_hd 0)).deriv
    rw [← hconnect]; exact h1d
  · -- Case: hᵢ not differentiable at x₀'. fderiv = 0 ≤ 0.
    simp [fderiv_zero_of_not_differentiableAt hdiff]

-- ============================================================================
-- Flatness axioms
-- ============================================================================

/-- hKillingToHarmonic: Killing vector field components are harmonic on flat T³. -/
-- Helper used by both Killing and curl/div proofs:
-- derive ContDiff ℝ 2 from C¹ + C¹ of each partial
private lemma contDiff2_from_partials {g : (Fin 3 → ℝ) → ℝ}
    (hg1 : ContDiff ℝ 1 g)
    (hg_parts : ∀ i : Fin 3, ContDiff ℝ 1 (fun y => fderiv ℝ g y (Pi.single i 1))) :
    ContDiff ℝ 2 g := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_fderiv]
  refine ⟨hg1.differentiable one_ne_zero, fun h => by simp at h, ?_⟩
  rw [contDiff_clm_apply_iff]
  intro v
  have heq : (fun y => fderiv ℝ g y v) =
      fun y => ∑ i : Fin 3, v i * fderiv ℝ g y (Pi.single i 1) := by
    ext y
    set L := fderiv ℝ g y with hL
    have hv : v = ∑ i : Fin 3, v i • (Pi.single i (1 : ℝ) : Fin 3 → ℝ) := by
      ext m; simp [Pi.single_apply, mul_ite]
    -- conv_lhs rewrites only the argument of L, not the v inside the sum on the RHS
    calc L v = L (∑ i : Fin 3, v i • (Pi.single i (1 : ℝ) : Fin 3 → ℝ)) := by
            conv_lhs => rw [hv]
      _ = ∑ i : Fin 3, v i * L (Pi.single i (1 : ℝ)) := by
          simp [map_sum, map_smul, smul_eq_mul]
  rw [heq]
  exact ContDiff.sum (fun i _ => (hg_parts i).const_smul (v i))

theorem torus_hKillingToHarmonic (b : Torus3 → Fin 3 → ℝ)
    (hb_C1 : ∀ j, ContDiff ℝ 1 (periodicLift (fun z => b z j)))
    (hb_C2 : ∀ j i, ContDiff ℝ 1 (periodicLift (fun x => torusGradX (fun y => b y j) x i)))
    (hKilling : ∀ x i j, torusGradX (fun y => b y j) x i +
                          torusGradX (fun y => b y i) x j = 0) :
    ∀ j : Fin 3, ∀ x, torusDivX (torusGradX (fun y => b y j)) x = 0 := by
  -- Convert hb_C2 to ℝⁿ form: each partial ∂b_k/∂x_i is C¹
  have hC2_comp : ∀ k i : Fin 3, ContDiff ℝ 1
      (fun y => fderiv ℝ (periodicLift (fun z => b z k)) y (Pi.single i 1)) := by
    intro k i
    have h := hb_C2 k i
    rwa [show periodicLift (fun x => torusGradX (fun y => b y k) x i) =
        fun y => fderiv ℝ (periodicLift (fun z => b z k)) y (Pi.single i 1) from
        funext (periodicLift_torusGradX (fun z => b z k) i)] at h
  -- Derive ContDiff ℝ 2 for each component
  have hC2_all : ∀ k : Fin 3, ContDiff ℝ 2 (periodicLift (fun z => b z k)) :=
    fun k => contDiff2_from_partials (hb_C1 k) (hC2_comp k)
  -- Killing condition in ℝⁿ form
  have hKilling_rn : ∀ (y : Fin 3 → ℝ) (i k : Fin 3),
      fderiv ℝ (periodicLift (fun z => b z k)) y (Pi.single i 1) +
      fderiv ℝ (periodicLift (fun z => b z i)) y (Pi.single k 1) = 0 := by
    intro y i k
    rw [← periodicLift_torusGradX (fun w => b w k) i y,
        ← periodicLift_torusGradX (fun w => b w i) k y]
    simp only [periodicLift, Function.comp_apply]
    exact hKilling (torusMk y) i k
  -- Main proof: for each j and x, show div(grad(b_j))(x) = 0
  intro jj x
  simp only [torusDivX]
  simp_rw [show ∀ i : Fin 3, (fun y => periodicLift (fun z => torusGradX (fun w => b w jj) z i) y) =
      (fun y => fderiv ℝ (periodicLift (fun z => b z jj)) y (Pi.single i 1)) from
      fun i => funext (periodicLift_torusGradX (fun z => b z jj) i)]
  exact killing_harmonic_rn'
    (fun y k => periodicLift (fun z => b z k) y)
    hC2_all hKilling_rn jj (torusMk_surjective x).choose

/-- hCurlZeroDivZeroHarmonic: irrotational + solenoidal → harmonic on flat T³. -/
theorem torus_hCurlZeroDivZeroHarmonic (F : Torus3 → Fin 3 → ℝ)
    (hF_C1 : ∀ i, ContDiff ℝ 1 (periodicLift (fun z => F z i)))
    (hF_C2 : ∀ i j, ContDiff ℝ 1 (periodicLift (fun x => torusGradX (fun y => F y i) x j)))
    (hcurl : ∀ x, torusCurlX F x = 0) (hdiv : ∀ x, torusDivX F x = 0) :
    ∀ i, ∀ x, torusDivX (torusGradX (fun y => F y i)) x = 0 := by
  -- Convert hF_C2 to ℝⁿ form
  have hC2_comp : ∀ k j : Fin 3, ContDiff ℝ 1
      (fun y => fderiv ℝ (periodicLift (fun z => F z k)) y (Pi.single j 1)) := by
    intro k j
    have h := hF_C2 k j
    rwa [show periodicLift (fun x => torusGradX (fun y => F y k) x j) =
        fun y => fderiv ℝ (periodicLift (fun z => F z k)) y (Pi.single j 1) from
        funext (periodicLift_torusGradX (fun z => F z k) j)] at h
  -- ContDiff ℝ 2 for each component
  have hC2_all : ∀ k : Fin 3, ContDiff ℝ 2 (periodicLift (fun z => F z k)) :=
    fun k => contDiff2_from_partials (hF_C1 k) (hC2_comp k)
  -- Symmetric Jacobian from curl = 0.
  -- Key insight: torusCurlX F x = ![torusGradX (F·2) x 1 - ..., ..., ...] by rfl
  -- (both use the same canonical preimage x₀ = (torusMk_surjective x).choose,
  --  and fun w => periodicLift f w = periodicLift f by eta reduction in Lean 4)
  have hjac_sym : ∀ (y : Fin 3 → ℝ) (i j : Fin 3),
      fderiv ℝ (periodicLift (fun z => F z j)) y (Pi.single i 1) =
      fderiv ℝ (periodicLift (fun z => F z i)) y (Pi.single j 1) := by
    intro y i j
    rw [← periodicLift_torusGradX (fun z => F z j) i y,
        ← periodicLift_torusGradX (fun z => F z i) j y]
    simp only [periodicLift, Function.comp_apply]
    -- Goal: torusGradX (F·j) (torusMk y) i = torusGradX (F·i) (torusMk y) j
    have hcurl_y := hcurl (torusMk y)
    -- Express torusCurlX directly in terms of torusGradX (by definitional equality / eta)
    have hcurl_expand : torusCurlX F (torusMk y) =
        ![torusGradX (fun w => F w 2) (torusMk y) 1 - torusGradX (fun w => F w 1) (torusMk y) 2,
          torusGradX (fun w => F w 0) (torusMk y) 2 - torusGradX (fun w => F w 2) (torusMk y) 0,
          torusGradX (fun w => F w 1) (torusMk y) 0 -
            torusGradX (fun w => F w 0) (torusMk y) 1] := rfl
    rw [hcurl_expand] at hcurl_y
    -- Extract the three symmetry conditions
    have h0 : torusGradX (fun w => F w 2) (torusMk y) 1 =
        torusGradX (fun w => F w 1) (torusMk y) 2 := by
      have := congr_fun hcurl_y 0
      simp at this
      linarith
    have h1 : torusGradX (fun w => F w 0) (torusMk y) 2 =
        torusGradX (fun w => F w 2) (torusMk y) 0 := by
      have := congr_fun hcurl_y 1
      simp at this
      linarith
    have h2 : torusGradX (fun w => F w 1) (torusMk y) 0 =
        torusGradX (fun w => F w 0) (torusMk y) 1 := by
      have := congr_fun hcurl_y 2
      simp at this
      linarith
    fin_cases i <;> fin_cases j <;> simp_all
  -- Divergence-free in ℝⁿ form
  -- torusDivX F (torusMk y) = 0 gives the sum at x₀ = (torusMk_surjective (torusMk y)).choose.
  -- Transfer to y via periodicLift_fderiv_eq (both x₀ and y are preimages of torusMk y).
  have hdiv_rn : ∀ (y : Fin 3 → ℝ),
      ∑ i : Fin 3, fderiv ℝ (periodicLift (fun z => F z i)) y (Pi.single i 1) = 0 := by
    intro y
    have key := hdiv (torusMk y)
    simp only [torusDivX] at key
    -- key uses x₀ = (torusMk_surjective (torusMk y)).choose; normalize eta form
    simp only [show ∀ i : Fin 3, (fun w => periodicLift (fun z => F z i) w) =
        periodicLift (fun z => F z i) from fun _ => rfl] at key
    -- key : ∑ i, fderiv ℝ (periodicLift (F·i)) x₀ (Pi.single i 1) = 0
    -- Convert to sum at y using periodicLift_fderiv_eq
    calc ∑ i : Fin 3, fderiv ℝ (periodicLift (fun z => F z i)) y (Pi.single i 1)
        = ∑ i : Fin 3, fderiv ℝ (periodicLift (fun z => F z i))
            ((torusMk_surjective (torusMk y)).choose) (Pi.single i 1) := by
          apply Finset.sum_congr rfl; intro i _
          exact congrFun (congrArg DFunLike.coe
            (periodicLift_fderiv_eq (fun z => F z i) y _
            ((torusMk_surjective (torusMk y)).choose_spec.symm))) (Pi.single i 1)
      _ = 0 := key
  -- Main proof
  intro ii x
  simp only [torusDivX]
  simp_rw [show ∀ i : Fin 3, (fun y => periodicLift (fun z => torusGradX (fun w => F w ii) z i) y) =
      (fun y => fderiv ℝ (periodicLift (fun z => F z ii)) y (Pi.single i 1)) from
      fun i => funext (periodicLift_torusGradX (fun z => F z ii) i)]
  exact curl_div_harmonic_rn'
    (fun y k => periodicLift (fun z => F z k) y)
    hC2_all hjac_sym hdiv_rn ii (torusMk_surjective x).choose

-- ============================================================================
-- The FlatTorus3 instance (all fields proved, 0 sorry's)
-- ============================================================================

instance : VML.FlatTorus3 Torus3 where
  toMeasureSpace := inferInstance
  instCompact := inferInstance
  instNonempty := ⟨fun _ => 0⟩
  instFirstCountable := inferInstance
  gradX := torusGradX
  divX := torusDivX
  curlX := torusCurlX
  hDivLinear := by
    intro α G x; simp only [torusDivX]
    simp only [show ∀ i, periodicLift (fun z => (α • G z) i) =
          fun y => α * periodicLift (fun z => G z i) y from
        fun i => by ext y; simp [periodicLift, Pi.smul_apply, smul_eq_mul]]
    simp [fderiv_const_mul_always, Finset.mul_sum]
  hGradConst := torus_hGradConst
  hSpatialPos := fun g hcont hpos => torus_hSpatialPos g hpos hcont
  hSpatialNonnegZero := fun g hcont hnn hint => torus_hSpatialNonnegZero g hnn hint hcont
  IsSpatiallySmooth := fun n f => ContDiff ℝ n (periodicLift f)
  hDiff_of_le := fun {n m} f hle hf => hf.of_le (by exact_mod_cast hle)
  hDiff_const := fun n c => by
    show ContDiff ℝ n (periodicLift (fun _ => c))
    have : periodicLift (fun _ : Torus3 => c) = fun _ => c := by ext y; simp [periodicLift]
    rw [this]; exact contDiff_const
  hDiff_add := fun n f g hf hg => by
    show ContDiff ℝ n (periodicLift (fun x => f x + g x))
    have : periodicLift (fun x => f x + g x) = fun y => periodicLift f y + periodicLift g y := by
      ext y; simp [periodicLift]
    rw [this]; exact hf.add hg
  hDiff_smul := fun n c f hf => by
    show ContDiff ℝ n (periodicLift (fun x => c * f x))
    have : periodicLift (fun x => c * f x) = fun y => c * periodicLift f y := by
      ext y; simp [periodicLift]
    rw [this]; exact hf.const_smul c
  hDiff_log := fun n f hf hpos => by
    show ContDiff ℝ n (periodicLift (Real.log ∘ f))
    have hlift : periodicLift (Real.log ∘ f) = Real.log ∘ periodicLift f := rfl
    rw [hlift]
    exact hf.log (fun y => ne_of_gt (hpos (torusMk y)))
  hDiff_continuous := fun n f hf => by
    rw [isOpenQuotientMap_torusMk.isQuotientMap.continuous_iff]
    exact hf.continuous
  hDiff_grad := fun n f i hf => by
    show ContDiff ℝ n (periodicLift (fun x => torusGradX f x i))
    have heq : periodicLift (fun x => torusGradX f x i) =
        fun y => fderiv ℝ (periodicLift f) y (Pi.single i 1) :=
      funext (fun y => periodicLift_torusGradX f i y)
    rw [heq]
    exact (hf.fderiv_right le_rfl).clm_apply contDiff_const
  hCurlIntZero := fun F u hF => torus_hCurlIntZero F u (fun j => (hF j).of_le (by decide))
  hHarmonic_const := fun φ hd => torus_hHarmonic_const φ hd
  hLaplacianMaxNonpos := fun φ x₀ hd => torus_hLaplacianMaxNonpos φ x₀ (hd.of_le (by decide))
  hGradAdd := fun f g hf hg => torus_hGradAdd' f g (hf.of_le (by decide)) (hg.of_le (by decide))
  hGradScalarMul := by
    intro c f x
    ext i
    simp only [torusGradX, Pi.smul_apply, smul_eq_mul]
    show fderiv ℝ (periodicLift (fun y => c * f y)) _ (Pi.single i 1) = _
    simp only [show periodicLift (fun y => c * f y) = fun y => c * periodicLift f y
      from by ext y; simp [periodicLift]]
    rw [fderiv_const_mul_always]; rfl
  hGradChainExp := by
    intro φ _hφ x i; simp only [torusGradX]
    show fderiv ℝ (periodicLift (fun y => Real.exp (φ y))) _ (Pi.single i 1) = _
    have hlift : periodicLift (fun y => Real.exp (φ y)) = fun y => Real.exp (periodicLift φ y) :=
      by ext y; simp [periodicLift]
    rw [hlift, fderiv_exp_comp_always, _root_.smul_apply, smul_eq_mul]
    have hx₀ := (torusMk_surjective x).choose_spec
    change Real.exp (periodicLift φ _) * _ = Real.exp (φ x) * _
    simp [periodicLift, hx₀]
  hKillingToHarmonic := fun b hb_C1 hb_C2 hKilling =>
    torus_hKillingToHarmonic b (fun j => (hb_C1 j).of_le (by decide))
      (fun j i => (hb_C2 j i).of_le (by decide)) hKilling
  hCurlZeroDivZeroHarmonic := fun F hF_C1 hF_C2 hcurl hdiv =>
    torus_hCurlZeroDivZeroHarmonic F (fun i => (hF_C1 i).of_le (by decide))
      (fun i j => (hF_C2 i j).of_le (by decide)) hcurl hdiv
  hIBP_spatial := fun φ ψ i hφ hψ =>
    torus_hIBP_spatial φ ψ i
      (hφ.of_le (by decide)) (hψ.of_le (by decide))
  hSpatialVelocityFubini := by
    intro F hF_joint
    exact integral_integral_swap hF_joint
  hSpatialAdd := fun g₁ g₂ h1 h2 => integral_add h1 h2
  hGradIntegrable := by
    intro g hg i
    have h_cont : Continuous (fun x : Torus3 => torusGradX g x i) := by
      have hH_cont : Continuous
          (fun y : Fin 3 → ℝ => fderiv ℝ (periodicLift g) y (Pi.single i 1)) :=
        (hg.continuous_fderiv (by decide)).clm_apply continuous_const
      have heq : (fun x : Torus3 => torusGradX g x i) ∘ torusMk =
          fun y => fderiv ℝ (periodicLift g) y (Pi.single i 1) :=
        funext (fun y => periodicLift_torusGradX g i y)
      rw [isOpenQuotientMap_torusMk.isQuotientMap.continuous_iff, heq]
      exact hH_cont
    rw [← integrableOn_univ]
    exact h_cont.continuousOn.integrableOn_compact isCompact_univ

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-
## Status of the FlatTorus3 instance on Fin 3 → AddCircle 1

**0 errors, 0 sorry's**

### Instance fields:
- All 21 fields proved (hDiff_velocityIntegral removed from FlatTorus3 — see below)
- hGradConst, hGradAdd, hGradScalarMul, hGradChainExp: proved
- hDivLinear: case analysis on differentiability
- hSpatialPos, hSpatialNonnegZero: with Continuous hypothesis
- hSpatialVelocityFubini: with joint integrability
- hSpatialAdd: with integrability hypotheses, via integral_add
- hGradIntegrable: proved via IsOpenQuotientMap.piMap
- IsSpatiallySmooth ⊤ := ContDiff ℝ ⊤ ∘ periodicLift (smooth)
- hDiff_const ⊤, hDiff_add ⊤, hDiff_smul ⊤, hDiff_log ⊤,
  hDiff_grad ⊤: closure properties, all proved
- hCurlIntZero: forwarded to torus_hCurlIntZero (proved)
- hHarmonic_const: forwarded to torus_hHarmonic_const (proved, energy method)
- hIBP_spatial: forwarded to torus_hIBP_spatial (proved)
- hLaplacianMaxNonpos: 1D second derivative test + chain rule (proved)
- hKillingToHarmonic, hCurlZeroDivZeroHarmonic: Clairaut + algebraic argument (proved)

### Proved helper theorems (11+):
- torus_hIBP_spatial: core torus IBP (1D FTC + Fubini + periodicity)
- torus_hCurlIntZero: integral of curl = 0 (from IBP with φ=1)
- torus_hHarmonic_const: harmonic → constant on torus (energy method via IBP)
- torus_hGradConst, torus_hGradAdd', torus_hSpatialPos, torus_hSpatialNonnegZero
- torus_hSpatialVelocityFubini, torus_hLaplacianMaxNonpos
- torus_hKillingToHarmonic, torus_hCurlZeroDivZeroHarmonic
-/

end
