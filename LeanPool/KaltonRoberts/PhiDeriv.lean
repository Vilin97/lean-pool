/-
Copyright (c) 2026 Ho Boon Suan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ho Boon Suan
-/

/-
# Derivative computations for the Phi function
-/
import LeanPool.KaltonRoberts.Defs

/-!
# Derivative computations for the Phi function

First and second derivative computations for the entropy expressions defining
the Phi functions.
-/

namespace KaltonRoberts

open Real

/-! ## First derivatives of hEntropy components -/

theorem hasDerivAt_binEntropy (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun x => -x * Real.log x - (1 - x) * Real.log (1 - x))
      (Real.log (1 - x) - Real.log x) x := by
  convert
    HasDerivAt.sub
      (HasDerivAt.mul (hasDerivAt_neg x) (Real.hasDerivAt_log hx.ne'))
      (HasDerivAt.mul (hasDerivAt_id x |> HasDerivAt.const_sub 1)
        (HasDerivAt.log (hasDerivAt_id x |> HasDerivAt.const_sub 1)
          (by linarith : (1 - x) ≠ 0))) using 1
  · rfl
  · rfl
  · ext y
    simp [Pi.mul_apply, Pi.sub_apply, id_eq]
  · simp [id_eq]
    field_simp [hx.ne', sub_ne_zero.mpr hx1.ne']
    ring

theorem hasDerivAt_h_entropy_second (θ x : ℝ) (hx : 0 < x) (hxθ : x < θ) :
    HasDerivAt (fun x => θ * Real.log θ - x * Real.log x - (θ - x) * Real.log (θ - x))
      (Real.log (θ - x) - Real.log x) x := by
  convert
    HasDerivAt.sub
      (HasDerivAt.sub (hasDerivAt_const x (θ * Real.log θ))
        (HasDerivAt.mul (hasDerivAt_id x) (Real.hasDerivAt_log hx.ne')))
      (HasDerivAt.mul (hasDerivAt_id x |> HasDerivAt.const_sub θ)
        (HasDerivAt.log (hasDerivAt_id x |> HasDerivAt.const_sub θ)
          (by linarith : (θ - x) ≠ 0))) using 1
  · rfl
  · rfl
  · ext y
    simp [Pi.mul_apply, Pi.sub_apply, id_eq]
  · simp [id_eq]
    field_simp [hx.ne', sub_ne_zero.mpr hxθ.ne']
    ring

theorem hasDerivAt_neg_entropy_scaled (r x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun x => r * x * Real.log x + r * (1 - x) * Real.log (1 - x))
      (r * (Real.log x - Real.log (1 - x))) x := by
  convert
    HasDerivAt.add
      (HasDerivAt.mul (HasDerivAt.mul (hasDerivAt_const x r) (hasDerivAt_id x))
        (Real.hasDerivAt_log hx.ne'))
      (HasDerivAt.mul
        (HasDerivAt.mul (hasDerivAt_const x r) (hasDerivAt_id x |> HasDerivAt.const_sub 1))
        (HasDerivAt.log (hasDerivAt_id x |> HasDerivAt.const_sub 1)
          (by linarith : (1 - x) ≠ 0))) using 1
  · rfl
  · rfl
  · ext y
    simp [Pi.mul_apply, Pi.add_apply, id_eq]
  · simp [id_eq]
    field_simp [hx.ne', sub_ne_zero.mpr hx1.ne']
    ring

/-! ## Second derivatives -/

theorem hasDerivAt_binEntropy_deriv (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun x => Real.log (1 - x) - Real.log x) (-1/(1-x) - 1/x) x := by
  convert
    HasDerivAt.sub
      (HasDerivAt.log (hasDerivAt_id x |> HasDerivAt.const_sub 1)
        (by linarith : (1 - x) ≠ 0))
      (Real.hasDerivAt_log hx.ne') using 1
  · rfl
  · rfl
  · ext y
    rfl
  · simp [id_eq, one_div, sub_eq_add_neg]

theorem hasDerivAt_h_entropy_second_deriv (θ x : ℝ) (hx : 0 < x) (hxθ : x < θ) :
    HasDerivAt (fun x => Real.log (θ - x) - Real.log x) (-1/(θ-x) - 1/x) x := by
  convert
    HasDerivAt.sub
      (HasDerivAt.log (hasDerivAt_id x |> HasDerivAt.const_sub θ)
        (by linarith : (θ - x) ≠ 0))
      (Real.hasDerivAt_log hx.ne') using 1
  · rfl
  · rfl
  · ext y
    rfl
  · simp [id_eq, one_div, sub_eq_add_neg]

theorem hasDerivAt_neg_entropy_scaled_deriv (r x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun x => r * (Real.log x - Real.log (1 - x))) (r * (1/x + 1/(1-x))) x := by
  convert
    HasDerivAt.const_mul r
      (HasDerivAt.sub (Real.hasDerivAt_log hx.ne')
        (HasDerivAt.log (hasDerivAt_id' x |> HasDerivAt.const_sub 1) (by linarith))) using 1
  · rfl
  · rfl
  · simp_all
  · ring_nf

/-! ## Derivative of Phi -/

/-
The first derivative of Phi at a point `x` in `(0, θ)` with `θ < 1`.
-/
theorem hasDerivAt_Phi (r θ x : ℝ) (hx : 0 < x) (hxθ : x < θ) (hx1 : x < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr : 0 < r) :
    HasDerivAt (fun x => Phi r θ x)
      ((Real.log (1 - x) - Real.log x) + (Real.log (θ - x) - Real.log x)
       + (r / θ * Real.log (r / θ) - r * Real.log r - (r / θ - r) * Real.log (r / θ - r))
       + r * (Real.log x - Real.log (1 - x))) x := by
  unfold Phi;
  have h_def : ∀ᶠ y in nhds x, hEntropy (r * y / θ) (r * y) = y * (hEntropy (r / θ) r) := by
    filter_upwards [ lt_mem_nhds hx ] with y hy;
    unfold hEntropy;
    field_simp;
    rw [ Real.log_div, Real.log_div, Real.log_div, Real.log_mul, Real.log_mul ] <;> try nlinarith;
    · rw [ Real.log_div, Real.log_mul, Real.log_mul ] <;> ring_nf <;> nlinarith;
    · exact mul_ne_zero ( mul_ne_zero hr.ne' hy.ne' ) ( by linarith );
  have h_def2 :
      ∀ᶠ y in nhds x,
        -hEntropy r (r * y) = r * y * Real.log y +
          r * (1 - y) * Real.log (1 - y) := by
    filter_upwards [ Ioo_mem_nhds hx hx1 ] with y hy;
    unfold hEntropy; ring_nf;
    rw [show r - r * y = r * (1 - y) by ring,
      Real.log_mul (by linarith) (by linarith [hy.1, hy.2]),
      Real.log_mul (by linarith) (by linarith [hy.1, hy.2])];
    ring;
  have h_def3 :
      ∀ᶠ y in nhds x,
        hEntropy 1 y = -y * Real.log y - (1 - y) * Real.log (1 - y) := by
    filter_upwards [ Ioo_mem_nhds hx hx1 ] with y hy using by unfold hEntropy; norm_num;
  have h_def4 :
      ∀ᶠ y in nhds x,
        hEntropy θ y =
          θ * Real.log θ - y * Real.log y - (θ - y) * Real.log (θ - y) := by
    exact Filter.Eventually.of_forall fun y => rfl;
  have h_def5 :
      ∀ᶠ y in nhds x,
        hEntropy (r * y / θ) (r * y) - hEntropy r (r * y) =
          y * hEntropy (r / θ) r + r * y * Real.log y +
            r * (1 - y) * Real.log (1 - y) := by
    filter_upwards [ h_def, h_def2 ] with y hy₁ hy₂ using by linarith;
  have h_def6 :
      HasDerivAt
        (fun y =>
          -y * Real.log y - (1 - y) * Real.log (1 - y) + θ * Real.log θ -
            y * Real.log y - (θ - y) * Real.log (θ - y) +
              y * hEntropy (r / θ) r + r * y * Real.log y +
                r * (1 - y) * Real.log (1 - y))
        (log (1 - x) - log x + (log (θ - x) - log x) +
          (r / θ * log (r / θ) - r * log r - (r / θ - r) * log (r / θ - r)) +
            r * (log x - log (1 - x)))
        x := by
    convert
      HasDerivAt.add
        (HasDerivAt.add
          (HasDerivAt.add
            (HasDerivAt.add
              (HasDerivAt.add
                (HasDerivAt.add
                  (HasDerivAt.add (hasDerivAt_binEntropy x hx hx1) (hasDerivAt_const x 0))
                  (hasDerivAt_h_entropy_second θ x hx hxθ))
                (hasDerivAt_id' x |> HasDerivAt.mul_const <| hEntropy (r / θ) r))
              (hasDerivAt_neg_entropy_scaled r x hx hx1))
            (hasDerivAt_const x 0))
          (hasDerivAt_const x 0))
        (hasDerivAt_const x 0) using 1
    · rfl
    · rfl
    · ext y
      simp [Pi.add_apply]
      ring
    · unfold hEntropy
      ring
  apply h_def6.congr_of_eventuallyEq
  filter_upwards [ h_def, h_def2, h_def3, h_def4, h_def5 ] with y hy1 hy2 hy3 hy4 hy5 using by
    linarith;

/-- The second derivative of Phi equals `Phi'' r θ x`. -/
theorem hasDerivAt_Phi_second (r θ x : ℝ) (hx : 0 < x) (hxθ : x < θ) (hx1 : x < 1)
    (_hθ0 : 0 < θ) (_hr : 2 < r) :
    HasDerivAt (fun x =>
      (Real.log (1 - x) - Real.log x) + (Real.log (θ - x) - Real.log x)
      + (r / θ * Real.log (r / θ) - r * Real.log r -
        (r / θ - r) * Real.log (r / θ - r))
      + r * (Real.log x - Real.log (1 - x)))
      (Phi'' r θ x) x := by
  convert
    HasDerivAt.add
      (HasDerivAt.add
        (HasDerivAt.add (hasDerivAt_binEntropy_deriv x hx hx1)
          (hasDerivAt_h_entropy_second_deriv θ x hx hxθ))
        (hasDerivAt_const x
          (r / θ * Real.log (r / θ) - r * Real.log r -
            (r / θ - r) * Real.log (r / θ - r))))
      (hasDerivAt_neg_entropy_scaled_deriv r x hx hx1) using 1
  · rfl
  · rfl
  · ext y
    simp [Pi.add_apply]
  · unfold Phi''
    field_simp [hx.ne', sub_ne_zero.mpr hx1.ne', sub_ne_zero.mpr hxθ.ne']
    ring

/-! ## Generic ConvexOn for Phi -/

/-
ConvexOn for Phi on an interval [δ, α], given an explicit hypothesis
that the second-derivative formula `Phi'' r θ x` is nonneg on `[δ, α]`.
-/
theorem convexOn_Phi_of_Phi''_nonneg {r θ δ α : ℝ}
    (hδ : 0 < δ) (hαθ : α < θ) (hθ1 : θ < 1) (hr : 2 < r)
    (hθ0 : 0 < θ) (hδα : δ ≤ α)
    (hPhi'' : ∀ x : ℝ, δ ≤ x → x ≤ α → 0 ≤ Phi'' r θ x) :
    ConvexOn ℝ (Set.Icc δ α) (fun x => Phi r θ x) := by
  apply_rules [ convexOn_of_deriv2_nonneg ] <;> try exact convex_Icc δ α;
  · apply ContinuousOn.sub
    · apply ContinuousOn.add
      · apply ContinuousOn.add
        · apply ContinuousOn.sub
          · exact ContinuousOn.sub continuousOn_const
              (ContinuousOn.mul continuousOn_id
                (Real.continuousOn_log.mono (by
                  simp_all)))
          · exact ContinuousOn.mul (continuousOn_const.sub continuousOn_id)
              (ContinuousOn.log (continuousOn_const.sub continuousOn_id) fun x hx => by
                linarith [hx.1, hx.2])
        · apply ContinuousOn.sub
          · exact ContinuousOn.sub continuousOn_const
              (ContinuousOn.mul continuousOn_id
                (Real.continuousOn_log.mono (by
                  simp_all)))
          · exact ContinuousOn.mul (continuousOn_const.sub continuousOn_id)
              (ContinuousOn.log (continuousOn_const.sub continuousOn_id) fun x hx => by
                linarith [hx.1, hx.2])
      · apply ContinuousOn.sub
        · exact ContinuousOn.sub
            (ContinuousOn.mul
              (ContinuousOn.div_const (continuousOn_const.mul continuousOn_id) _)
              (ContinuousOn.log
                (ContinuousOn.div_const (continuousOn_const.mul continuousOn_id) _)
                fun x hx => by nlinarith [hx.1, hx.2, mul_div_cancel₀ (r * x) hθ0.ne']))
            (ContinuousOn.mul (continuousOn_const.mul continuousOn_id)
              (ContinuousOn.log (continuousOn_const.mul continuousOn_id) fun x hx => by
                nlinarith [hx.1, hx.2]))
        · apply ContinuousOn.mul
          · exact ContinuousOn.sub
              (ContinuousOn.div_const (continuousOn_const.mul continuousOn_id) _)
              (continuousOn_const.mul continuousOn_id)
          · apply ContinuousOn.log
            · exact ContinuousOn.sub
                (ContinuousOn.div_const (continuousOn_const.mul continuousOn_id) _)
                (continuousOn_const.mul continuousOn_id)
            · exact fun x hx => by
                nlinarith [hx.1, hx.2, mul_div_cancel₀ (r * x) hθ0.ne',
                  mul_pos (by linarith : 0 < r) (by linarith [hx.1] : 0 < x)]
    · apply ContinuousOn.sub
      · exact ContinuousOn.sub continuousOn_const <|
          ContinuousOn.mul (continuousOn_const.mul continuousOn_id) <|
            ContinuousOn.log (continuousOn_const.mul continuousOn_id) fun x hx => by
              nlinarith [hx.1]
      · exact ContinuousOn.mul
          (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
          (ContinuousOn.log
            (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
            fun x hx => by nlinarith [hx.1, hx.2])
  · norm_num +zetaDelta at *;
    intro x hx
    exact (hasDerivAt_Phi r θ x (by linarith [hx.1]) (by linarith [hx.2])
      (by linarith [hx.2]) (by linarith [hx.1]) (by linarith [hx.2])
      (by linarith [hx.1, hx.2])) |>.differentiableAt |>.differentiableWithinAt;
  · simp +zetaDelta only [interior_Icc] at *;
    -- By definition of $Phi$, its derivative is the expression in `hasDerivAt_Phi`.
    have h_deriv : ∀ x ∈ Set.Ioo δ α, deriv (fun x => Phi r θ x) x =
        (Real.log (1 - x) - Real.log x) + (Real.log (θ - x) - Real.log x) +
          (r / θ * Real.log (r / θ) - r * Real.log r -
            (r / θ - r) * Real.log (r / θ - r)) +
            r * (Real.log x - Real.log (1 - x)) := by
      intro x hx
      exact HasDerivAt.deriv (hasDerivAt_Phi r θ x (by linarith [hx.1])
        (by linarith [hx.2]) (by linarith [hx.2]) (by linarith [hx.1])
        (by linarith [hx.2]) (by linarith [hx.1, hx.2]));
    exact DifferentiableOn.congr (fun x hx =>
      DifferentiableAt.differentiableWithinAt <| by
        exact DifferentiableAt.add
          (DifferentiableAt.add
            (DifferentiableAt.add
              (DifferentiableAt.sub
                (DifferentiableAt.log (differentiableAt_id.const_sub _) <| by
                  linarith [hx.1, hx.2])
                (DifferentiableAt.log differentiableAt_id <| by linarith [hx.1, hx.2]))
              (DifferentiableAt.sub
                (DifferentiableAt.log (differentiableAt_id.const_sub _) <| by
                  linarith [hx.1, hx.2])
                (DifferentiableAt.log differentiableAt_id <| by linarith [hx.1, hx.2])))
            (differentiableAt_const _))
          (DifferentiableAt.mul (differentiableAt_const _)
            (DifferentiableAt.sub
              (DifferentiableAt.log differentiableAt_id <| by linarith [hx.1, hx.2])
              (DifferentiableAt.log (differentiableAt_id.const_sub _) <| by
                linarith [hx.1, hx.2])))) h_deriv;
  · simp +zetaDelta only [interior_Icc, Set.mem_Ioo, Function.iterate_succ,
        Function.comp_apply, and_imp] at *;
    intro x hx₁ hx₂;
    convert hPhi'' x hx₁.le hx₂.le using 1;
    convert HasDerivAt.deriv
      (hasDerivAt_Phi_second r θ x (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith)) using 1;
    exact Filter.EventuallyEq.deriv_eq (by
      filter_upwards [Ioo_mem_nhds hx₁ hx₂] with y hy using
        HasDerivAt.deriv (hasDerivAt_Phi r θ y (by linarith [hy.1])
          (by linarith [hy.2]) (by linarith [hy.2]) (by linarith [hy.1])
          (by linarith [hy.2]) (by linarith [hy.1])))

end KaltonRoberts
