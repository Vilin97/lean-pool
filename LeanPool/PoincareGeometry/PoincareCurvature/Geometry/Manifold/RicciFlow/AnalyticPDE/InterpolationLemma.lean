/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Interpolation Lemma -/

@[expose] public noncomputable section

open Metric Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Derivative of `t ↦ t • v` is `v`. -/
theorem hasDerivAt_smul_const_lemma (v : E) (s : ℝ) :
    HasDerivAt (fun t : ℝ => t • v) v s := by
  have h := HasDerivAt.smul_const (hasDerivAt_id s) v
  simpa using h

/-- Derivative of affine curve `t ↦ x + t • v` is `v`. -/
theorem hasDerivAt_affine_lemma (x v : E) (s : ℝ) :
    HasDerivAt (fun t : ℝ => x + t • v) v s := by
  have h1 := hasDerivAt_smul_const_lemma v s
  have h2 : HasDerivAt (fun _ : ℝ => x) 0 s := hasDerivAt_const s x
  have h := h2.add h1
  have heq : (fun _ : ℝ => x) + (fun t : ℝ => t • v) = (fun t : ℝ => x + t • v) := rfl
  rw [heq] at h
  simpa using h

/-- From C², the Fréchet derivative is C¹, hence has a Fréchet derivative. -/
theorem contDiffAt_two_hasFDerivAt_fderiv {f : E → F} {y : E}
    (h : ContDiffAt ℝ 2 f y) :
    HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) y) y := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) y := h.fderiv_right (by norm_num)
  have hdiff : DifferentiableAt ℝ (fderiv ℝ f) y := h1.differentiableAt (by norm_num)
  exact hdiff.hasFDerivAt

/-- Second derivative bound applied twice to a unit vector. -/
theorem second_deriv_bound {f : E → F} {y v : E} {M₂ : ℝ}
    (h2 : ‖fderiv ℝ (fun z => fderiv ℝ f z) y‖ ≤ M₂)
    (hvv : ‖v‖ = 1) :
    ‖((fderiv ℝ (fderiv ℝ f) y) v) v‖ ≤ M₂ := by
  have heq : fderiv ℝ (fun z => fderiv ℝ f z) y = fderiv ℝ (fderiv ℝ f) y := rfl
  rw [heq] at h2
  calc ‖((fderiv ℝ (fderiv ℝ f) y) v) v‖
      ≤ ‖(fderiv ℝ (fderiv ℝ f) y) v‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖fderiv ℝ (fderiv ℝ f) y‖ * ‖v‖) * ‖v‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ (fderiv ℝ f) y‖ := by rw [hvv, mul_one, mul_one]
    _ ≤ M₂ := h2

/-- Derivative of `s ↦ (fderiv ℝ f (x + s • v)) v` is `((D²f (x+s•v)) v) v`. -/
theorem G_hasDerivAt {f : E → F} {x v : E} {s : ℝ}
    (hDf : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (x + s • v)) (x + s • v)) :
    HasDerivAt (fun t : ℝ => (fderiv ℝ f (x + t • v)) v)
      (((fderiv ℝ (fderiv ℝ f) (x + s • v)) v) v) s := by
  have hcurve : HasFDerivAt (fun t : ℝ => x + t • v)
      (ContinuousLinearMap.toSpanSingleton ℝ v) s :=
    (hasDerivAt_affine_lemma x v s).hasFDerivAt
  have hF := hDf.comp s hcurve
  have hu : HasFDerivAt (fun _ : ℝ => v) (0 : ℝ →L[ℝ] E) s := hasFDerivAt_const v s
  have h := hF.clm_apply hu
  simp only [ContinuousLinearMap.comp_zero, zero_add] at h
  have hDeriv := h.hasDerivAt
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply] at hDeriv
  have hB1 : (ContinuousLinearMap.toSpanSingleton ℝ v : ℝ →L[ℝ] E) 1 = v := by simp
  rw [hB1] at hDeriv
  exact hDeriv

/-- MVT bound: `‖G(s) - G(0)‖ ≤ M₂ * s` where `G(t) = (fderiv ℝ f (x+t•v)) v`. -/
theorem G_mvt_bound {f : E → F} {x₀ x v : E} {R h M₂ : ℝ}
    (hf : ContDiffOn ℝ 2 f (ball x₀ R))
    (h2 : ∀ y ∈ ball x₀ R, ‖fderiv ℝ (fun z => fderiv ℝ f z) y‖ ≤ M₂)
    (hmem : ∀ s ∈ Icc (0:ℝ) h, x + s • v ∈ ball x₀ R)
    (hvv : ‖v‖ = 1) :
    ∀ s ∈ Icc (0:ℝ) h,
      ‖(fderiv ℝ f (x + s • v)) v - (fderiv ℝ f x) v‖ ≤ M₂ * s := by
  set G : ℝ → F := fun t => (fderiv ℝ f (x + t • v)) v with hG_def
  set G' : ℝ → F := fun t => ((fderiv ℝ (fderiv ℝ f) (x + t • v)) v) v with hG'_def
  have hG_deriv : ∀ t ∈ Icc (0:ℝ) h, HasDerivWithinAt G (G' t) (Icc (0:ℝ) h) t := by
    intro t ht
    have hC2 : ContDiffAt ℝ 2 f (x + t • v) :=
      hf.contDiffAt (isOpen_ball.mem_nhds (hmem t ht))
    have hDf := contDiffAt_two_hasFDerivAt_fderiv hC2
    have hGAt := G_hasDerivAt hDf
    have h1 : (fun t_ : ℝ => (fderiv ℝ f (x + t_ • v)) v) = G := rfl
    have h2' : (((fderiv ℝ (fderiv ℝ f) (x + t • v)) v) v) = G' t := rfl
    rw [h1, h2'] at hGAt
    exact hGAt.hasDerivWithinAt
  have hG'_bound : ∀ t ∈ Ico (0:ℝ) h, ‖G' t‖ ≤ M₂ := by
    intro t ht
    have htIcc : t ∈ Icc (0:ℝ) h := Ico_subset_Icc_self ht
    have h2t := h2 (x + t • v) (hmem t htIcc)
    have heq : G' t = ((fderiv ℝ (fderiv ℝ f) (x + t • v)) v) v := rfl
    rw [heq]
    exact second_deriv_bound h2t hvv
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hG_deriv hG'_bound
  intro s hs
  have h := hmvt s hs
  have hG0 : G 0 = (fderiv ℝ f x) v := by simp [hG_def]
  have hGs : G s = (fderiv ℝ f (x + s • v)) v := rfl
  rw [hGs, hG0] at h
  simpa using h

/-- Interpolation inequality: C² control gives C¹ bound.

If `f` is C² on `ball x₀ R` with `‖f‖ ≤ M₀` and `‖D²f‖ ≤ M₂`,
then for `x` with `closedBall x δ ⊆ ball x₀ R` and `0 < h ≤ δ`:
  `‖fderiv ℝ f x‖ ≤ 2 * M₀ / h + h * M₂`.
-/
theorem norm_fderiv_le_of_C2_bound
    {f : E → F} {x₀ : E} {R : ℝ}
    (hf : ContDiffOn ℝ 2 f (ball x₀ R))
    {M₀ M₂ : ℝ}
    (h0 : ∀ y ∈ ball x₀ R, ‖f y‖ ≤ M₀)
    (h2 : ∀ y ∈ ball x₀ R, ‖fderiv ℝ (fun z => fderiv ℝ f z) y‖ ≤ M₂)
    {x : E} {δ h : ℝ} (hδ : 0 < δ) (hh : 0 < h) (hhδ : h ≤ δ)
    (hx : closedBall x δ ⊆ ball x₀ R) :
    ‖fderiv ℝ f x‖ ≤ 2 * M₀ / h + h * M₂ := by
  -- Nonnegativity of bounds
  have hx_mem : x ∈ ball x₀ R := hx (mem_closedBall_self hδ.le)
  have hM₀_nn : 0 ≤ M₀ := le_trans (norm_nonneg _) (h0 x hx_mem)
  -- M₂ bounds a norm, hence is nonnegative
  have hM₂_nn : 0 ≤ M₂ :=
    le_trans (norm_nonneg (fderiv ℝ (fun z => fderiv ℝ f z) x)) (h2 x hx_mem)
  have hRHS_nn : 0 ≤ 2 * M₀ / h + h * M₂ := by positivity
  -- Reduce to pointwise bound via operator norm characterization
  apply ContinuousLinearMap.opNorm_le_bound _ hRHS_nn
  intro u
  by_cases hu : u = 0
  · simp [hu]
  · have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
    -- Scale to unit vector v
    set v : E := (‖u‖⁻¹) • u with hv_def
    have hvv : ‖v‖ = 1 := by
      rw [hv_def, norm_smul]
      have h1 : ‖(‖u‖⁻¹ : ℝ)‖ = ‖u‖⁻¹ := by
        rw [Real.norm_of_nonneg (inv_nonneg.mpr hnu.le)]
      rw [h1]
      exact inv_mul_cancel₀ hnu.ne'
    -- u = ‖u‖ • v
    have huv : u = ‖u‖ • v := by
      rw [hv_def, smul_smul, mul_inv_cancel₀ hnu.ne', one_smul]
    -- It suffices to bound ‖(fderiv ℝ f x) v‖; the core estimate
    have key : ‖(fderiv ℝ f x) v‖ ≤ 2 * M₀ / h + h * M₂ := by
      -- Core estimate for unit vector v
      -- Define g(s) = f(x + s•v) for s ∈ [0,h]
      set g : ℝ → F := fun s => f (x + s • v) with hg_def
      -- The curve stays in the ball
      have hmem : ∀ s ∈ Icc (0:ℝ) h, x + s • v ∈ ball x₀ R := by
        intro s hs
        apply hx
        rw [mem_closedBall, dist_eq_norm]
        have e1 : (x + s • v) - x = s • v := by abel
        rw [e1, norm_smul, hvv, mul_one]
        rw [mem_Icc] at hs
        calc |s| = s := abs_of_nonneg hs.1
          _ ≤ h := hs.2
          _ ≤ δ := hhδ
      -- g is differentiable on [0,h]
      have hg_diff : DifferentiableOn ℝ g (Icc (0:ℝ) h) := by
        intro s hs
        have hC2 : ContDiffAt ℝ 2 f (x + s • v) :=
          hf.contDiffAt (isOpen_ball.mem_nhds (hmem s hs))
        have hdiff : DifferentiableAt ℝ f (x + s • v) :=
          hC2.differentiableAt (by norm_num)
        have hF : HasFDerivAt f (fderiv ℝ f (x + s • v)) (x + s • v) :=
          hdiff.hasFDerivAt
        have hc : HasDerivAt (fun t : ℝ => x + t • v) v s :=
          hasDerivAt_affine_lemma x v s
        -- The point (fun t => x + t•v) s is definitionally x + s•v
        have hF' : HasFDerivAt f (fderiv ℝ f ((fun t : ℝ => x + t • v) s))
            ((fun t : ℝ => x + t • v) s) := hF
        have hcomp := HasFDerivAt.comp_hasDerivAt (l := f)
          (l' := fderiv ℝ f ((fun t : ℝ => x + t • v) s))
          (f := fun t : ℝ => x + t • v) (f' := v) (x := s) hF' hc
        have heq : g = f ∘ (fun t : ℝ => x + t • v) := rfl
        rw [heq]
        exact hcomp.differentiableAt.differentiableWithinAt
      -- Bound on g: ‖g(s)‖ ≤ M₀
      have hg_bnd : ∀ s ∈ Icc (0:ℝ) h, ‖g s‖ ≤ M₀ :=
        fun s hs => h0 _ (hmem s hs)
      -- Define A = g'(0) = (fderiv ℝ f x) v
      set A : F := (fderiv ℝ f x) v with hA_def
      -- Define ψ(s) = g(s) - s • A
      set ψ : ℝ → F := fun s => g s - s • A with hψ_def
      -- ψ is differentiable on [0,h]
      have hψ_diff : DifferentiableOn ℝ ψ (Icc (0:ℝ) h) := by
        intro s hs
        have hg : DifferentiableWithinAt ℝ g (Icc (0:ℝ) h) s := hg_diff s hs
        have hsmul : DifferentiableWithinAt ℝ (fun t : ℝ => t • A) (Icc (0:ℝ) h) s := by
          apply DifferentiableWithinAt.smul_const
          exact differentiableWithinAt_id
        exact hg.sub hsmul
      -- Get the derivative of g with explicit value
      have hg_deriv : ∀ s ∈ Icc (0:ℝ) h,
          HasDerivAt g ((fderiv ℝ f (x + s • v)) v) s := by
        intro s hs
        have hC2 : ContDiffAt ℝ 2 f (x + s • v) :=
          hf.contDiffAt (isOpen_ball.mem_nhds (hmem s hs))
        have hdiff : DifferentiableAt ℝ f (x + s • v) :=
          hC2.differentiableAt (by norm_num)
        have hF : HasFDerivAt f (fderiv ℝ f (x + s • v)) (x + s • v) :=
          hdiff.hasFDerivAt
        have hc : HasDerivAt (fun t : ℝ => x + t • v) v s :=
          hasDerivAt_affine_lemma x v s
        have hF' : HasFDerivAt f (fderiv ℝ f ((fun t : ℝ => x + t • v) s))
            ((fun t : ℝ => x + t • v) s) := hF
        have hcomp := HasFDerivAt.comp_hasDerivAt (l := f)
          (l' := fderiv ℝ f ((fun t : ℝ => x + t • v) s))
          (f := fun t : ℝ => x + t • v) (f' := v) (x := s) hF' hc
        have heq : g = f ∘ (fun t : ℝ => x + t • v) := rfl
        rw [heq]
        simpa using hcomp
      -- MVT bound on G(s) = (fderiv ℝ f (x+s•v)) v
      have hG_bound := G_mvt_bound hf h2 hmem hvv
      -- ψ'(s) = g'(s) - A with explicit value
      have hψ_deriv : ∀ s ∈ Icc (0:ℝ) h,
          HasDerivWithinAt ψ (((fderiv ℝ f (x + s • v)) v) - A) (Icc (0:ℝ) h) s := by
        intro s hs
        have hg_s := hg_deriv s hs
        have hsmul : HasDerivAt (fun t : ℝ => t • A) A s := by
          have h := HasDerivAt.smul_const (hasDerivAt_id s) A
          simpa using h
        have hsub := hg_s.sub hsmul
        have heq : (g - fun t : ℝ => t • A) = ψ := rfl
        rw [heq] at hsub
        exact hsub.hasDerivWithinAt
      -- Uniform bound ‖ψ'(s)‖ ≤ M₂ * h
      have hψ'_bound : ∀ s ∈ Ico (0:ℝ) h, ‖((fderiv ℝ f (x + s • v)) v) - A‖ ≤ M₂ * h := by
        intro s hs
        have hsIcc : s ∈ Icc (0:ℝ) h := Ico_subset_Icc_self hs
        have hGb := hG_bound s hsIcc
        have hs_le : s ≤ h := (mem_Icc.mp hsIcc).2
        calc ‖((fderiv ℝ f (x + s • v)) v) - A‖
            = ‖(fderiv ℝ f (x + s • v)) v - (fderiv ℝ f x) v‖ := by rw [hA_def]
          _ ≤ M₂ * s := hGb
          _ ≤ M₂ * h := mul_le_mul_of_nonneg_left hs_le hM₂_nn
      -- MVT on ψ
      have hmvt_ψ := norm_image_sub_le_of_norm_deriv_le_segment' hψ_deriv hψ'_bound
      have hmem_h : h ∈ Icc (0:ℝ) h := by
        rw [mem_Icc]; exact ⟨hh.le, le_refl h⟩
      have hψ_bound := hmvt_ψ h hmem_h
      have hψ0 : ψ 0 = g 0 := by simp [hψ_def]
      have hψh : ψ h = g h - h • A := rfl
      have hg0 : g 0 = f x := by simp [hg_def]
      rw [hψ0, hg0, hψh] at hψ_bound
      have hg_h_bnd : ‖g h‖ ≤ M₀ := hg_bnd h hmem_h
      have hg_0_bnd : ‖f x‖ ≤ M₀ := by
        have hmem0 : (0:ℝ) ∈ Icc (0:ℝ) h := by rw [mem_Icc]; exact ⟨le_refl 0, hh.le⟩
        have h := hg_bnd 0 hmem0
        simpa [hg_def] using h
      -- h • A = (g h - f x) - ((g h - h • A) - f x)
      have key_eq : h • A = (g h - f x) - ((g h - h • A) - f x) := by abel
      have h_norm : ‖h • A‖ ≤ 2 * M₀ + M₂ * h * h := by
        rw [key_eq]
        calc ‖(g h - f x) - ((g h - h • A) - f x)‖
            ≤ ‖g h - f x‖ + ‖(g h - h • A) - f x‖ := norm_sub_le _ _
          _ ≤ 2 * M₀ + M₂ * h * h := by
              have h1 : ‖g h - f x‖ ≤ 2 * M₀ := by
                calc ‖g h - f x‖ ≤ ‖g h‖ + ‖f x‖ := norm_sub_le _ _
                  _ ≤ M₀ + M₀ := add_le_add hg_h_bnd hg_0_bnd
                  _ = 2 * M₀ := by ring
              have h2'' : ‖(g h - h • A) - f x‖ ≤ M₂ * h * h := by
                have := hψ_bound
                simpa using this
              linarith
      have h_hA : ‖h • A‖ = h * ‖A‖ := by
        rw [norm_smul, Real.norm_of_nonneg hh.le]
      rw [h_hA] at h_norm
      -- Divide by h > 0
      have heq : (2:ℝ) * M₀ / h + h * M₂ = (2 * M₀ + M₂ * h * h) / h := by
        field_simp
      have hA_le : ‖A‖ ≤ 2 * M₀ / h + h * M₂ := by
        rw [heq, le_div_iff₀ hh]
        calc ‖A‖ * h = h * ‖A‖ := mul_comm _ _
          _ ≤ 2 * M₀ + M₂ * h * h := h_norm
      rw [hA_def] at hA_le
      exact hA_le
    -- Derive the bound for u from the bound for v
    have hsc : (fderiv ℝ f x) u = ‖u‖ • ((fderiv ℝ f x) v) := by
      have h1 : (fderiv ℝ f x) u = (fderiv ℝ f x) (‖u‖ • v) := congrArg _ huv
      rw [h1, map_smul]
    calc ‖(fderiv ℝ f x) u‖ = ‖‖u‖ • ((fderiv ℝ f x) v)‖ := by rw [hsc]
      _ = ‖u‖ * ‖(fderiv ℝ f x) v‖ := by
          rw [norm_smul, Real.norm_of_nonneg hnu.le]
      _ ≤ ‖u‖ * (2 * M₀ / h + h * M₂) :=
          mul_le_mul_of_nonneg_left key hnu.le
      _ = (2 * M₀ / h + h * M₂) * ‖u‖ := mul_comm _ _
