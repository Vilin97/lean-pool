/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.Basic.Core.JetsAndFTC

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Core Aleksandrov Jet Infrastructure (SegmentTaylor)

Part of the core Aleksandrov jet infrastructure development. Split from
`Core.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open scoped ContDiff MatrixOrder Topology
open scoped ENNReal
open scoped intervalIntegral

open ContinuousLinearMap MeasureTheory

namespace ViscositySolns

variable {n : Nat}

/--
Segment-integration form of the a.e. FTC estimate.

If the line segment from `x0` to each nearby `z` is absolutely continuous,
has the supplied derivative field a.e. on `[0, 1]`, and that derivative is
uniformly bounded by `c * ‖z - x0‖²`, then the increment is
`o(‖z - x0‖²)`.
-/
theorem frechet_sub_const_isLittleO_sq_of_line_hasDerivAt_bound
    {F : Point n -> Real} {x0 : Point n}
    {g : Point n -> Point n →L[Real] Real}
    (hAC :
      ∀ᶠ z in 𝓝 x0,
        AbsolutelyContinuousOnInterval
          (fun t : Real => F (x0 + t • (z - x0))) 0 1)
    (hderiv :
      ∀ᶠ z in 𝓝 x0,
        ∀ᵐ t ∂(volume : Measure Real),
          t ∈ Set.uIcc (0 : Real) 1 ->
            HasDerivAt
              (fun s : Real => F (x0 + s • (z - x0)))
              (g (x0 + t • (z - x0)) (z - x0)) t)
    (hbound :
      ∀ c > 0, ∀ᶠ z in 𝓝 x0,
        ∀ t ∈ Set.uIoc (0 : Real) 1,
          ‖g (x0 + t • (z - x0)) (z - x0)‖ ≤ c * ‖z - x0‖ ^ 2) :
    (fun z : Point n => F z - F x0)
      =o[𝓝 x0] (fun z : Point n => ‖z - x0‖ ^ 2) := by
  refine Asymptotics.IsLittleO.of_bound ?_
  intro c hc
  filter_upwards [hAC, hderiv, hbound c hc] with z hACz hderivz hboundz
  let H : Real -> Real := fun t : Real => F (x0 + t • (z - x0))
  let G : Real -> Real := fun t : Real => g (x0 + t • (z - x0)) (z - x0)
  have hftc : (∫ t in (0 : Real)..1, G t) = H 1 - H 0 := by
    refine AbsolutelyContinuousOnInterval.integral_eq_sub_of_ae_hasDerivAt hACz ?_
    filter_upwards [hderivz] with t ht htmem
    exact ht htmem
  have hnormInt :
      ‖∫ t in (0 : Real)..1, G t‖ ≤ (c * ‖z - x0‖ ^ 2) * |1 - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : Real)) (b := 1) (C := c * ‖z - x0‖ ^ 2)
      (f := G) ?_
    intro t ht
    exact hboundz t ht
  calc
    ‖F z - F x0‖ = ‖H 1 - H 0‖ := by
      simp [H]
    _ = ‖∫ t in (0 : Real)..1, G t‖ := by
      rw [hftc]
    _ ≤ (c * ‖z - x0‖ ^ 2) * |1 - 0| := hnormInt
    _ = c * ‖(‖z - x0‖ ^ 2 : Real)‖ := by
      rw [sub_zero, abs_one, mul_one, Real.norm_of_nonneg (sq_nonneg ‖z - x0‖)]

/--
Line-restriction chain rule for Fréchet derivatives on `Point n`.

If `F` has Fréchet derivative `D` at `x + t • v`, then the one-dimensional
restriction `s ↦ F (x + s • v)` has derivative `D v` at `t`.
-/
theorem HasFDerivAt.hasDerivAt_line
    {F : Point n -> Real} {x v : Point n} {t : Real}
    {D : Point n →L[Real] Real}
    (hF : HasFDerivAt F D (x + t • v)) :
    HasDerivAt (fun s : Real => F (x + s • v)) (D v) t := by
  have hline : HasDerivAt (fun s : Real => x + s • v) v t := by
    simpa using ((hasDerivAt_id' t).smul_const v).const_add x
  exact hF.comp_hasDerivAt t hline

/--
Line-restriction derivative for the residual after subtracting a Fréchet
second-order Taylor model.

This is the differentiated form of the source proof's residual
`Ψ(δy) = φ(x + δy) -` quadratic model, restricted to a line
`δy = t • v`.
-/
theorem HasFDerivAt.hasDerivAt_frechetSecondOrderResidual_line
    {φ : Point n -> Real} {x0 v : Point n} {t : Real}
    {Dφ : Point n →L[Real] Real}
    {D2φ : Point n →L[Real] Point n →L[Real] Real}
    {Dφ_at : Point n -> Point n →L[Real] Real}
    (hD2sym : IsSymmetricBilinear D2φ)
    (hφ :
      HasFDerivAt φ (Dφ_at (x0 + t • v)) (x0 + t • v)) :
    HasDerivAt
      (fun s : Real =>
        φ (x0 + s • v) -
          frechetSecondOrderModel x0 (φ x0) Dφ D2φ (x0 + s • v))
      ((Dφ_at (x0 + t • v) -
        (Dφ + D2φ ((x0 + t • v) - x0))) v) t := by
  have hres :
      HasFDerivAt
        (fun y : Point n =>
          φ y - frechetSecondOrderModel x0 (φ x0) Dφ D2φ y)
        (Dφ_at (x0 + t • v) -
          (Dφ + D2φ ((x0 + t • v) - x0))) (x0 + t • v) := by
    have hwithin :
        HasFDerivWithinAt
          (fun y : Point n =>
            φ y - frechetSecondOrderModel x0 (φ x0) Dφ D2φ y)
          (Dφ_at (x0 + t • v) -
            (Dφ + D2φ ((x0 + t • v) - x0))) Set.univ
          (x0 + t • v) :=
      hasFDerivWithinAt_frechetSecondOrderResidual
        (C := Set.univ) (φ := φ) (x0 := x0) (x := x0 + t • v)
        (Dφ := Dφ) (D2φ := D2φ) (Dφ_at := Dφ_at)
        hD2sym hφ.hasFDerivWithinAt
    exact hwithin.hasFDerivAt_of_univ
  simpa using HasFDerivAt.hasDerivAt_line (x := x0) (v := v) (t := t) hres

/--
A.e. line-restriction derivative for the residual after subtracting a Fréchet
second-order Taylor model.

This is the form designed to feed the a.e. FTC lemmas above: differentiability
of `φ` at a.e. point on the line gives differentiability of the scalar residual
line restriction with the expected derivative-error field.
-/
theorem ae_hasDerivAt_frechetSecondOrderResidual_line
    {φ : Point n -> Real} {x0 v : Point n}
    {Dφ : Point n →L[Real] Real}
    {D2φ : Point n →L[Real] Point n →L[Real] Real}
    {Dφ_at : Point n -> Point n →L[Real] Real}
    (hD2sym : IsSymmetricBilinear D2φ)
    (hφ :
      ∀ᵐ t ∂(volume : Measure Real),
        HasFDerivAt φ (Dφ_at (x0 + t • v)) (x0 + t • v)) :
    ∀ᵐ t ∂(volume : Measure Real),
      HasDerivAt
        (fun s : Real =>
          φ (x0 + s • v) -
            frechetSecondOrderModel x0 (φ x0) Dφ D2φ (x0 + s • v))
        ((Dφ_at (x0 + t • v) -
          (Dφ + D2φ ((x0 + t • v) - x0))) v) t := by
  filter_upwards [hφ] with t ht
  exact HasFDerivAt.hasDerivAt_frechetSecondOrderResidual_line
    (x0 := x0) (v := v) (t := t)
    (Dφ := Dφ) (D2φ := D2φ) (Dφ_at := Dφ_at)
    hD2sym ht

/--
Quadratic line-restriction little-oh for the residual after subtracting a
Fréchet second-order Taylor model.

This combines the a.e. residual-line derivative calculation with the scalar
a.e. FTC estimate above. It is the linewise form of the source proof's final
claim that integrating the `o(t)` derivative error gives an `o(t²)` Taylor
residual.
-/
theorem frechetSecondOrderResidual_line_isLittleO_sq_of_ae_hasFDerivAt_isLittleO
    {φ : Point n -> Real} {x0 v : Point n}
    {Dφ : Point n →L[Real] Real}
    {D2φ : Point n →L[Real] Point n →L[Real] Real}
    {Dφ_at : Point n -> Point n →L[Real] Real}
    (hD2sym : IsSymmetricBilinear D2φ)
    (hAC :
      ∀ᶠ t in 𝓝 (0 : Real),
        AbsolutelyContinuousOnInterval
          (fun s : Real =>
            φ (x0 + s • v) -
              frechetSecondOrderModel x0 (φ x0) Dφ D2φ (x0 + s • v))
          0 t)
    (hφ :
      ∀ᵐ t ∂(volume : Measure Real),
        HasFDerivAt φ (Dφ_at (x0 + t • v)) (x0 + t • v))
    (hg :
      (fun t : Real =>
        ((Dφ_at (x0 + t • v) -
          (Dφ + D2φ ((x0 + t • v) - x0))) v))
        =o[𝓝 (0 : Real)] (fun t : Real => t)) :
    (fun t : Real =>
      φ (x0 + t • v) -
        frechetSecondOrderModel x0 (φ x0) Dφ D2φ (x0 + t • v))
      =o[𝓝 (0 : Real)] (fun t : Real => t ^ 2) := by
  let F : Real -> Real :=
    fun s : Real =>
      φ (x0 + s • v) -
        frechetSecondOrderModel x0 (φ x0) Dφ D2φ (x0 + s • v)
  let g : Real -> Real :=
    fun t : Real =>
      ((Dφ_at (x0 + t • v) -
        (Dφ + D2φ ((x0 + t • v) - x0))) v)
  have hderiv : ∀ᵐ t ∂(volume : Measure Real), HasDerivAt F (g t) t := by
    simpa [F, g] using
      ae_hasDerivAt_frechetSecondOrderResidual_line
        (x0 := x0) (v := v) (Dφ := Dφ) (D2φ := D2φ)
        (Dφ_at := Dφ_at) hD2sym hφ
  have hline : (fun t : Real => F t - F 0)
      =o[𝓝 (0 : Real)] (fun t : Real => t ^ 2) := by
    exact
      absolutelyContinuous_sub_const_isLittleO_sq_of_ae_hasDerivAt_isLittleO
        (F := F) (g := g) (by simpa [F] using hAC) hderiv
        (by simpa [g] using hg)
  have hF0 : F 0 = 0 := by
    simp [F, frechetSecondOrderModel]
  simpa [F, hF0] using hline

/--
Linewise little-oh for the derivative error of a Fréchet derivative map.

If `Dφ_at` has derivative `D2φ` at `x0` and agrees with the base derivative
`Dφ` at `x0`, then evaluating the derivative residual on a fixed direction
along the line `x0 + t • v` is `o(t)`.
-/
theorem derivativeResidual_line_isLittleO_of_hasFDerivAt
    {x0 v : Point n}
    {Dφ : Point n →L[Real] Real}
    {D2φ : Point n →L[Real] Point n →L[Real] Real}
    {Dφ_at : Point n -> Point n →L[Real] Real}
    (hDφ0 : Dφ_at x0 = Dφ)
    (hDφ_deriv : HasFDerivAt Dφ_at D2φ x0) :
    (fun t : Real =>
      ((Dφ_at (x0 + t • v) -
        (Dφ + D2φ ((x0 + t • v) - x0))) v))
      =o[𝓝 (0 : Real)] (fun t : Real => t) := by
  have hres :
      (fun x : Point n => Dφ_at x - (Dφ + D2φ (x - x0)))
        =o[𝓝 x0] (fun x : Point n => ‖x - x0‖) := by
    simpa [nhdsWithin_univ] using
      frechetDerivativeResidual_isLittleO_of_hasFDerivWithinAt
        (C := Set.univ) (x0 := x0) (Dφ := Dφ)
        (D2φ := D2φ) (Dφ_at := Dφ_at)
        hDφ0 hDφ_deriv.hasFDerivWithinAt
  have hline_tendsto :
      Filter.Tendsto (fun t : Real => x0 + t • v)
        (𝓝 (0 : Real)) (𝓝 x0) := by
    have hline_deriv : HasDerivAt (fun t : Real => x0 + t • v) v
        (0 : Real) := by
      simpa using ((hasDerivAt_id' (0 : Real)).smul_const v).const_add x0
    simpa using hline_deriv.continuousAt.tendsto
  have hline :
      (fun t : Real =>
        Dφ_at (x0 + t • v) -
          (Dφ + D2φ ((x0 + t • v) - x0)))
        =o[𝓝 (0 : Real)]
          (fun t : Real => ‖(x0 + t • v) - x0‖) :=
    hres.comp_tendsto hline_tendsto
  have heval :
      (fun t : Real =>
        ((Dφ_at (x0 + t • v) -
          (Dφ + D2φ ((x0 + t • v) - x0))) v))
        =O[𝓝 (0 : Real)]
          (fun t : Real =>
            Dφ_at (x0 + t • v) -
              (Dφ + D2φ ((x0 + t • v) - x0))) := by
    refine Asymptotics.IsBigO.of_bound ‖v‖ ?_
    filter_upwards with t
    have h :=
      ContinuousLinearMap.le_opNorm
        (Dφ_at (x0 + t • v) -
          (Dφ + D2φ ((x0 + t • v) - x0))) v
    simpa [mul_comm] using h
  have hscalar :
      (fun t : Real =>
        ((Dφ_at (x0 + t • v) -
          (Dφ + D2φ ((x0 + t • v) - x0))) v))
        =o[𝓝 (0 : Real)]
          (fun t : Real => ‖(x0 + t • v) - x0‖) :=
    heval.trans_isLittleO hline
  have hdist :
      (fun t : Real => ‖(x0 + t • v) - x0‖)
        =O[𝓝 (0 : Real)] (fun t : Real => t) := by
    refine Asymptotics.IsBigO.of_bound ‖v‖ ?_
    filter_upwards with t
    have hsub : (x0 + t • v) - x0 = t • v := by
      simp
    rw [hsub, norm_smul]
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg t) (norm_nonneg v))]
    ring_nf
    exact le_rfl
  exact hscalar.trans_isBigO hdist

/--
Uniform segment bound for the derivative error produced by differentiability
of the derivative map at the base point.

This is the multivariate counterpart of
`derivativeResidual_line_isLittleO_of_hasFDerivAt`: along every sufficiently
short segment from `x0` to `z`, the derivative residual evaluated on the
segment direction is bounded by `c * ‖z - x0‖²`.
-/
theorem derivativeResidual_segment_bound_of_hasFDerivAt
    {x0 : Point n}
    {Dφ : Point n →L[Real] Real}
    {D2φ : Point n →L[Real] Point n →L[Real] Real}
    {Dφ_at : Point n -> Point n →L[Real] Real}
    (hDφ0 : Dφ_at x0 = Dφ)
    (hDφ_deriv : HasFDerivAt Dφ_at D2φ x0) :
    ∀ c > 0, ∀ᶠ z in 𝓝 x0,
      ∀ t ∈ Set.uIoc (0 : Real) 1,
        ‖((Dφ_at (x0 + t • (z - x0)) -
          (Dφ + D2φ ((x0 + t • (z - x0)) - x0))) (z - x0))‖
          ≤ c * ‖z - x0‖ ^ 2 := by
  intro c hc
  have hres :
      (fun x : Point n => Dφ_at x - (Dφ + D2φ (x - x0)))
        =o[𝓝 x0] (fun x : Point n => ‖x - x0‖) := by
    simpa [nhdsWithin_univ] using
      frechetDerivativeResidual_isLittleO_of_hasFDerivWithinAt
        (C := Set.univ) (x0 := x0) (Dφ := Dφ)
        (D2φ := D2φ) (Dφ_at := Dφ_at)
        hDφ0 hDφ_deriv.hasFDerivWithinAt
  have hsmall :
      ∀ᶠ x in 𝓝 x0,
        ‖Dφ_at x - (Dφ + D2φ (x - x0))‖ ≤ c * ‖(‖x - x0‖ : Real)‖ :=
    hres.bound hc
  rcases Metric.nhds_basis_closedBall.eventually_iff.mp hsmall with
    ⟨δ, hδ, hδbound⟩
  filter_upwards [Metric.closedBall_mem_nhds x0 hδ] with z hz t ht
  have ht01 : 0 ≤ t ∧ t ≤ 1 := by
    rcases Set.mem_uIoc.mp ht with h | h
    · exact ⟨h.1.le, h.2⟩
    · linarith
  have hseg_sub :
      (x0 + t • (z - x0)) - x0 = t • (z - x0) := by
    simp
  have hseg_norm_le : ‖(x0 + t • (z - x0)) - x0‖ ≤ ‖z - x0‖ := by
    rw [hseg_sub, norm_smul]
    have ht_norm : ‖t‖ ≤ (1 : Real) := by
      rw [Real.norm_of_nonneg ht01.1]
      exact ht01.2
    calc
      ‖t‖ * ‖z - x0‖ ≤ 1 * ‖z - x0‖ :=
        mul_le_mul_of_nonneg_right ht_norm (norm_nonneg _)
      _ = ‖z - x0‖ := by simp
  have hseg_mem : x0 + t • (z - x0) ∈ Metric.closedBall x0 δ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hzδ : ‖z - x0‖ ≤ δ := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    exact hseg_norm_le.trans hzδ
  have hop :
      ‖Dφ_at (x0 + t • (z - x0)) -
          (Dφ + D2φ ((x0 + t • (z - x0)) - x0))‖
        ≤ c * ‖(‖(x0 + t • (z - x0)) - x0‖ : Real)‖ :=
    hδbound hseg_mem
  have heval :=
    ContinuousLinearMap.le_opNorm
      (Dφ_at (x0 + t • (z - x0)) -
        (Dφ + D2φ ((x0 + t • (z - x0)) - x0))) (z - x0)
  calc
    ‖((Dφ_at (x0 + t • (z - x0)) -
      (Dφ + D2φ ((x0 + t • (z - x0)) - x0))) (z - x0))‖
        ≤ ‖Dφ_at (x0 + t • (z - x0)) -
            (Dφ + D2φ ((x0 + t • (z - x0)) - x0))‖ * ‖z - x0‖ := by
          simpa [mul_comm] using heval
    _ ≤ (c * ‖(‖(x0 + t • (z - x0)) - x0‖ : Real)‖) * ‖z - x0‖ :=
        mul_le_mul_of_nonneg_right hop (norm_nonneg _)
    _ ≤ (c * ‖z - x0‖) * ‖z - x0‖ := by
        have hseg_norm :
            ‖(‖(x0 + t • (z - x0)) - x0‖ : Real)‖
              ≤ ‖z - x0‖ := by
          rwa [Real.norm_of_nonneg (norm_nonneg _)]
        exact
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hseg_norm hc.le) (norm_nonneg _)
    _ = c * ‖z - x0‖ ^ 2 := by ring

/--
Fréchet quadratic Taylor little-oh from the source proof's segment-integration
data.

This is the multivariate endpoint of the a.e. FTC step: absolute continuity
of the Taylor residual on nearby segments, a.e. differentiability of `φ` along
those segments, and differentiability of the derivative map at `x0` imply the
full Fréchet remainder `o(‖z - x0‖²)`.
-/
theorem frechetSecondOrderResidual_isLittleO_sq_of_line_ae_hasFDerivAt_hasFDerivAt
    {φ : Point n -> Real} {x0 : Point n}
    {Dφ : Point n →L[Real] Real}
    {D2φ : Point n →L[Real] Point n →L[Real] Real}
    {Dφ_at : Point n -> Point n →L[Real] Real}
    (hD2sym : IsSymmetricBilinear D2φ)
    (hAC :
      ∀ᶠ z in 𝓝 x0,
        AbsolutelyContinuousOnInterval
          (fun t : Real =>
            φ (x0 + t • (z - x0)) -
              frechetSecondOrderModel x0 (φ x0) Dφ D2φ
                (x0 + t • (z - x0)))
          0 1)
    (hφ :
      ∀ᶠ z in 𝓝 x0,
        ∀ᵐ t ∂(volume : Measure Real),
          t ∈ Set.uIcc (0 : Real) 1 ->
            HasFDerivAt φ
              (Dφ_at (x0 + t • (z - x0)))
              (x0 + t • (z - x0)))
    (hDφ0 : Dφ_at x0 = Dφ)
    (hDφ_deriv : HasFDerivAt Dφ_at D2φ x0) :
    Asymptotics.IsLittleO (𝓝 x0)
      (fun z : Point n =>
        φ z - frechetSecondOrderModel x0 (φ x0) Dφ D2φ z)
      (fun z : Point n => ‖z - x0‖ ^ 2) := by
  let F : Point n -> Real :=
    fun z : Point n =>
      φ z - frechetSecondOrderModel x0 (φ x0) Dφ D2φ z
  let g : Point n -> Point n →L[Real] Real :=
    fun z : Point n => Dφ_at z - (Dφ + D2φ (z - x0))
  have hderiv :
      ∀ᶠ z in 𝓝 x0,
        ∀ᵐ t ∂(volume : Measure Real),
          t ∈ Set.uIcc (0 : Real) 1 ->
            HasDerivAt
              (fun s : Real => F (x0 + s • (z - x0)))
              (g (x0 + t • (z - x0)) (z - x0)) t := by
    filter_upwards [hφ] with z hz
    filter_upwards [hz] with t ht htmem
    exact
      HasFDerivAt.hasDerivAt_frechetSecondOrderResidual_line
        (x0 := x0) (v := z - x0) (t := t)
        (Dφ := Dφ) (D2φ := D2φ) (Dφ_at := Dφ_at)
        hD2sym (ht htmem)
  have hbound :
      ∀ c > 0, ∀ᶠ z in 𝓝 x0,
        ∀ t ∈ Set.uIoc (0 : Real) 1,
          ‖g (x0 + t • (z - x0)) (z - x0)‖ ≤ c * ‖z - x0‖ ^ 2 := by
    simpa [g] using
      derivativeResidual_segment_bound_of_hasFDerivAt
        (x0 := x0) (Dφ := Dφ) (D2φ := D2φ)
        (Dφ_at := Dφ_at) hDφ0 hDφ_deriv
  have hmain :
      (fun z : Point n => F z - F x0)
        =o[𝓝 x0] (fun z : Point n => ‖z - x0‖ ^ 2) :=
    frechet_sub_const_isLittleO_sq_of_line_hasDerivAt_bound
      (F := F) (g := g)
      (by simpa [F] using hAC) hderiv hbound
  have hF0 : F x0 = 0 := by
    simp [F, frechetSecondOrderModel]
  simpa [F, hF0] using hmain

/--
Linewise quadratic Taylor little-oh from a.e. differentiability of the function
along the line and differentiability of its derivative map at the base point.

This is the direct source-proof package: the derivative residual is `o(t)` by
Fréchet differentiability of `Dφ_at` at `x0`, and the a.e. FTC estimate
integrates that derivative error to an `o(t²)` residual.
-/
theorem frechetSecondOrderResidual_line_isLittleO_sq_of_ae_hasFDerivAt_hasFDerivAt
    {φ : Point n -> Real} {x0 v : Point n}
    {Dφ : Point n →L[Real] Real}
    {D2φ : Point n →L[Real] Point n →L[Real] Real}
    {Dφ_at : Point n -> Point n →L[Real] Real}
    (hD2sym : IsSymmetricBilinear D2φ)
    (hAC :
      ∀ᶠ t in 𝓝 (0 : Real),
        AbsolutelyContinuousOnInterval
          (fun s : Real =>
            φ (x0 + s • v) -
              frechetSecondOrderModel x0 (φ x0) Dφ D2φ (x0 + s • v))
          0 t)
    (hφ :
      ∀ᵐ t ∂(volume : Measure Real),
        HasFDerivAt φ (Dφ_at (x0 + t • v)) (x0 + t • v))
    (hDφ0 : Dφ_at x0 = Dφ)
    (hDφ_deriv : HasFDerivAt Dφ_at D2φ x0) :
    (fun t : Real =>
      φ (x0 + t • v) -
        frechetSecondOrderModel x0 (φ x0) Dφ D2φ (x0 + t • v))
      =o[𝓝 (0 : Real)] (fun t : Real => t ^ 2) :=
  frechetSecondOrderResidual_line_isLittleO_sq_of_ae_hasFDerivAt_isLittleO
    hD2sym hAC hφ
    (derivativeResidual_line_isLittleO_of_hasFDerivAt hDφ0 hDφ_deriv)

/--
A.e. form of `HasFDerivAt.hasDerivAt_line`.
-/
theorem ae_hasDerivAt_line_of_ae_hasFDerivAt_line
    {F : Point n -> Real} {x v : Point n}
    {D : Real -> Point n →L[Real] Real}
    (hF : ∀ᵐ t ∂volume, HasFDerivAt F (D t) (x + t • v)) :
    ∀ᵐ t ∂volume,
      HasDerivAt (fun s : Real => F (x + s • v)) (D t v) t := by
  filter_upwards [hF] with t ht
  exact HasFDerivAt.hasDerivAt_line ht

/--
If a scalar function has a derivative field everywhere and that derivative
field is differentiable at a point, then the resulting second derivative is
symmetric.

This packages the Schwarz/Clairaut symmetry theorem in the finite-coordinate
form used by the Mignot residual calculation.
-/
theorem IsSymmetricBilinear.of_hasFDerivAt_derivative_map
    {f : Point n -> Real} {x : Point n}
    {Df : Point n -> Point n →L[Real] Real}
    {D2f : Point n →L[Real] Point n →L[Real] Real}
    (hf : ∀ z : Point n, HasFDerivAt f (Df z) z)
    (hDf : HasFDerivAt Df D2f x) :
    IsSymmetricBilinear D2f := by
  intro v w
  have hsym :=
    Convex.second_derivative_within_at_symmetric
      (s := Set.univ) (f := f) (f' := Df) (f'' := D2f)
      convex_univ (show (interior (Set.univ : Set (Point n))).Nonempty by
        exact ⟨0, by simp⟩)
      (by
        intro z _hz
        exact hf z)
      (by simp : x ∈ (Set.univ : Set (Point n)))
      (by simpa using hDf)
      v w
  simpa using hsym

/--
If a scalar function has a derivative field in a neighborhood of a point and
that derivative field is differentiable at the point, then the resulting
second derivative is symmetric.
-/
theorem IsSymmetricBilinear.of_hasFDerivAt_derivative_map_eventually
    {f : Point n -> Real} {x : Point n}
    {Df : Point n -> Point n →L[Real] Real}
    {D2f : Point n →L[Real] Point n →L[Real] Real}
    (hf : ∀ᶠ z in 𝓝 x, HasFDerivAt f (Df z) z)
    (hDf : HasFDerivAt Df D2f x) :
    IsSymmetricBilinear D2f := by
  intro v w
  have hsym :=
    second_derivative_symmetric_of_eventually
      (𝕜 := Real) (f := f) (f' := Df) (f'' := D2f)
      hf hDf v w
  simpa using hsym

/--
A continuous linear map is self-adjoint for the coordinate dot product.

This is the finite-coordinate formulation of the symmetry property needed for
the Mignot residual Hessian.
-/
def DotProductSelfAdjoint (A : Point n →L[Real] Point n) : Prop :=
  ∀ v w : Point n, dotProduct (A v) w = dotProduct (A w) v

/--
The identity map is self-adjoint for the coordinate dot product.
-/
theorem dotProductSelfAdjoint_id :
    DotProductSelfAdjoint (ContinuousLinearMap.id Real (Point n)) := by
  intro v w
  simp [dotProduct_comm]

/--
Self-adjointness for the coordinate dot product is preserved by subtraction.
-/
theorem DotProductSelfAdjoint.sub
    {A B : Point n →L[Real] Point n}
    (hA : DotProductSelfAdjoint A) (hB : DotProductSelfAdjoint B) :
    DotProductSelfAdjoint (A - B) := by
  intro v w
  simp only [sub_apply, sub_dotProduct]
  rw [hA v w, hB v w]

/--
The inverse of a coordinate-dot-product self-adjoint linear equivalence is
self-adjoint.
-/
theorem ContinuousLinearEquiv.dotProductSelfAdjoint_symm
    (Jlin : Point n ≃L[Real] Point n)
    (hJ : DotProductSelfAdjoint Jlin.toContinuousLinearMap) :
    DotProductSelfAdjoint Jlin.symm.toContinuousLinearMap := by
  intro v w
  have h := hJ (Jlin.symm v) (Jlin.symm w)
  simpa [dotProduct_comm] using h.symm

/--
If a linear map is self-adjoint for the coordinate dot product, then the
bilinear form represented by `gradientLinearMapCLM ∘ A` is symmetric.
-/
theorem DotProductSelfAdjoint.isSymmetricBilinear_gradientLinearMapCLM_comp
    {A : Point n →L[Real] Point n}
    (hA : DotProductSelfAdjoint A) :
    IsSymmetricBilinear (gradientLinearMapCLM.comp A) := by
  intro v w
  simpa [gradientLinearMapCLM_apply, gradientLinearMap_apply] using hA v w

/--
The residual Hessian candidate `gradientLinearMapCLM ∘ (A - I)` is symmetric
whenever `A` is self-adjoint for the coordinate dot product.
-/
theorem DotProductSelfAdjoint.isSymmetricBilinear_gradientLinearMapCLM_comp_sub_id
    {A : Point n →L[Real] Point n}
    (hA : DotProductSelfAdjoint A) :
    IsSymmetricBilinear
      (gradientLinearMapCLM.comp
        (A - ContinuousLinearMap.id Real (Point n))) :=
  (hA.sub dotProductSelfAdjoint_id).isSymmetricBilinear_gradientLinearMapCLM_comp

end ViscositySolns
