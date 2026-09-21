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

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Existence
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Mixed Time Space -/

open scoped Topology

namespace PoincareCurvature
theorem hasDerivAt_fderiv_space_of_joint_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E → ℝ) (Fdot : E → ℝ)
    (hF : ContDiff ℝ 2 (fun p : ℝ × E => F p.1 p.2))
    (hFdot : ∀ y : E, HasDerivAt (fun τ : ℝ => F τ y) (Fdot y) t)
    (v : E) :
    HasDerivAt
      (fun τ : ℝ => fderiv ℝ (fun y : E => F τ y) 0 v)
      (fderiv ℝ Fdot 0 v) t := by
  let full : (ℝ × E) → ℝ := fun p => F p.1 p.2
  have hfull : ContDiff ℝ 2 full := by
    simpa [full] using hF
  have hDf : ContDiffAt ℝ 1 (fderiv ℝ full) (t, 0) :=
    hfull.contDiffAt (x := (t, 0)) |>.fderiv_right (m := 1) (by norm_num)
  have hDff : HasFDerivAt (fderiv ℝ full)
      (fderiv ℝ (fderiv ℝ full) (t, 0)) (t, 0) :=
    (hDf.differentiableAt one_ne_zero).hasFDerivAt
  let inlMap : ℝ →L[ℝ] (ℝ × E) := ContinuousLinearMap.inl ℝ ℝ E
  let inrMap : E →L[ℝ] (ℝ × E) := ContinuousLinearMap.inr ℝ ℝ E
  let inl : ℝ × E := (1, (0 : E))
  have hS0 :=
    hDff.clm_apply
      (hasFDerivAt_const (inl : ℝ × E) (t, 0) :
        HasFDerivAt (fun _ : ℝ × E => inl)
          (0 : (ℝ × E) →L[ℝ] (ℝ × E)) (t, 0))
  have hS : HasFDerivAt
      (fun p : ℝ × E => (fderiv ℝ full p) inl)
      ((fderiv ℝ full (t, 0)).comp (0 : (ℝ × E) →L[ℝ] (ℝ × E)) +
        (fderiv ℝ (fderiv ℝ full) (t, 0)).flip inl)
      (t, 0) := by
    simpa only using hS0
  have hPderiv : HasFDerivAt
      (fun y : E => (fderiv ℝ full (t, y)) inl)
      (((fderiv ℝ full (t, 0)).comp (0 : (ℝ × E) →L[ℝ] (ℝ × E)) +
        (fderiv ℝ (fderiv ℝ full) (t, 0)).flip inl).comp inrMap)
      0 := by
    simpa [inl, Function.comp_def] using
      HasFDerivAt.comp (0 : E) hS
        (hasFDerivAt_prodMk_right (𝕜 := ℝ) t (0 : E))
  have hP_eq_full : ∀ y : E,
      fderiv ℝ (fun τ : ℝ => F τ y) t 1 =
        (fderiv ℝ full (t, y)) inl := by
    intro y
    have htime := (hfull.contDiffAt (x := (t, y))).differentiableAt
      (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    have hcomp := HasFDerivAt.comp (t : ℝ) htime.hasFDerivAt
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) t y)
    have hfd := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hcomp.fderiv
    simpa [full, inl, inlMap, Function.comp_def] using hfd
  let P : E → ℝ := fun y => fderiv ℝ (fun τ : ℝ => F τ y) t 1
  have hP_eq : P = Fdot := by
    funext y
    have hy := (hFdot y).hasFDerivAt.fderiv
    have hy' := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hy
    simpa [P] using hy'
  have hPderiv' := hPderiv.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun y => by
      simpa [P] using hP_eq_full y))
  have hFdotDeriv := hPderiv'.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun y => by
      simpa [P] using congrFun hP_eq.symm y))
  have hQ : HasFDerivAt
      (fun p : ℝ × E => (fderiv ℝ full p) (0, v))
      ((fderiv ℝ full (t, 0)).comp (0 : (ℝ × E) →L[ℝ] (ℝ × E)) +
        (fderiv ℝ (fderiv ℝ full) (t, 0)).flip (0, v))
      (t, 0) :=
    hDff.clm_apply
      (hasFDerivAt_const (0, v) (t, 0) :
        HasFDerivAt (fun _ : ℝ × E => (0, v))
          (0 : (ℝ × E) →L[ℝ] (ℝ × E)) (t, 0))
  have hQtime0 := HasFDerivAt.comp (t : ℝ) hQ
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) t (0 : E))
  have hQtime := hQtime0.hasDerivAt
  have hsymm := (hfull.contDiffAt (x := (t, 0))).isSymmSndFDerivAt (by norm_num)
  have hswap :
      (fderiv ℝ (fderiv ℝ full) (t, 0)) inl (0, v) =
        (fderiv ℝ (fderiv ℝ full) (t, 0)) (0, v) inl := by
    exact hsymm.eq inl (0, v)
  have hQtime'₀ : HasDerivAt
      (fun τ : ℝ => (fderiv ℝ full (τ, 0)) (0, v)) _ t :=
    hQtime.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun τ => by
        simp only [Function.comp_apply]))
  have hQtime' : HasDerivAt
      (fun τ : ℝ => (fderiv ℝ full (τ, 0)) (0, v))
      (fderiv ℝ (fderiv ℝ full) (t, 0) inl (0, v))
      t := by
    exact hQtime'₀.congr_deriv (by
      simpa [inl] using hswap)
  have hslice : ∀ τ : ℝ,
      fderiv ℝ (fun y : E => F τ y) 0 v =
        (fderiv ℝ full (τ, 0)) (0, v) := by
    intro τ
    have htime := (hfull.contDiffAt (x := (τ, 0))).differentiableAt
      (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    have hcomp := HasFDerivAt.comp (0 : E) htime.hasFDerivAt
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) τ (0 : E))
    have hfd := congrArg (fun L : E →L[ℝ] ℝ => L v) hcomp.fderiv
    simpa [full, Function.comp_def] using hfd
  have htarget := hQtime'.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun τ => hslice τ))
  have hderiv_eq :
      fderiv ℝ (fderiv ℝ full) (t, 0) (0, v) inl =
          fderiv ℝ Fdot 0 v := by
    calc
      fderiv ℝ (fderiv ℝ full) (t, 0) (0, v) inl =
          (((fderiv ℝ full (t, 0)).comp (0 : (ℝ × E) →L[ℝ] (ℝ × E)) +
                (fderiv ℝ (fderiv ℝ full) (t, 0)).flip inl).comp inrMap) v := by
              simp [inl, inrMap, ContinuousLinearMap.add_apply,
                ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
                zero_add, ContinuousLinearMap.flip_apply]
      _ = fderiv ℝ Fdot 0 v := by
        rw [← congrArg (fun L : E →L[ℝ] ℝ => L v) hFdotDeriv.fderiv]
  exact htarget.congr_deriv (hswap.trans hderiv_eq)

/- The mixed time--space derivative theorem at an arbitrary spatial base point.

The derivative is obtained from the genuine joint C² field on
ℝ × E; the time derivative of the spatial differential is therefore the
spatial differential of the time derivative.  Keeping the base point
explicit is important for manifold applications, where the point at which
a connection or curvature component is read out is not a distinguished
origin of the model space. -/
theorem hasDerivAt_fderiv_space_of_joint_contDiff_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E → ℝ) (Fdot : E → ℝ)
    (hF : ContDiff ℝ 2 (fun p : ℝ × E => F p.1 p.2))
    (hFdot : ∀ y : E, HasDerivAt (fun τ : ℝ => F τ y) (Fdot y) t)
    (x v : E) :
    HasDerivAt
      (fun τ => fderiv ℝ (fun y => F τ y) x v)
      (fderiv ℝ Fdot x v) t := by
  let full : (ℝ × E) → ℝ := fun p => F p.1 p.2
  have hfull : ContDiff ℝ 2 full := by
    simpa [full] using hF
  have hDf : ContDiffAt ℝ 1 (fderiv ℝ full) (t, x) :=
    hfull.contDiffAt (x := (t, x)) |>.fderiv_right (m := 1) (by norm_num)
  have hDff : HasFDerivAt (fderiv ℝ full)
      (fderiv ℝ (fderiv ℝ full) (t, x)) (t, x) :=
    (hDf.differentiableAt one_ne_zero).hasFDerivAt
  let inrMap : E →L[ℝ] (ℝ × E) := ContinuousLinearMap.inr ℝ ℝ E
  let inl : ℝ × E := (1, (0 : E))
  have hS0 :=
    hDff.clm_apply
      (hasFDerivAt_const (inl : ℝ × E) (t, x) :
        HasFDerivAt (fun _ : ℝ × E => inl)
          (0 : (ℝ × E) →L[ℝ] (ℝ × E)) (t, x))
  have hS : HasFDerivAt
      (fun p : ℝ × E => (fderiv ℝ full p) inl)
      ((fderiv ℝ full (t, x)).comp (0 : (ℝ × E) →L[ℝ] (ℝ × E)) +
        (fderiv ℝ (fderiv ℝ full) (t, x)).flip inl)
      (t, x) := by
    simpa only using hS0
  have hPderiv : HasFDerivAt
      (fun y : E => (fderiv ℝ full (t, y)) inl)
      (((fderiv ℝ full (t, x)).comp (0 : (ℝ × E) →L[ℝ] (ℝ × E)) +
        (fderiv ℝ (fderiv ℝ full) (t, x)).flip inl).comp inrMap)
      x := by
    simpa [inl, Function.comp_def] using
      HasFDerivAt.comp x hS
        (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
  have hP_eq_full : ∀ y : E,
      fderiv ℝ (fun τ : ℝ => F τ y) t 1 =
        (fderiv ℝ full (t, y)) inl := by
    intro y
    have htime := (hfull.contDiffAt (x := (t, y))).differentiableAt
      (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    have hcomp := HasFDerivAt.comp (t : ℝ) htime.hasFDerivAt
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) t y)
    have hfd := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hcomp.fderiv
    simpa [full, inl, Function.comp_def] using hfd
  let P : E → ℝ := fun y => fderiv ℝ (fun τ : ℝ => F τ y) t 1
  have hP_eq : P = Fdot := by
    funext y
    have hy := (hFdot y).hasFDerivAt.fderiv
    have hy' := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hy
    simpa [P] using hy'
  have hPderiv' := hPderiv.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun y => by
      simpa [P] using hP_eq_full y))
  have hFdotDeriv := hPderiv'.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun y => by
      simpa [P] using congrFun hP_eq.symm y))
  have hQ : HasFDerivAt
      (fun p : ℝ × E => (fderiv ℝ full p) (0, v))
      ((fderiv ℝ full (t, x)).comp (0 : (ℝ × E) →L[ℝ] (ℝ × E)) +
        (fderiv ℝ (fderiv ℝ full) (t, x)).flip (0, v))
      (t, x) :=
    hDff.clm_apply
      (hasFDerivAt_const (0, v) (t, x) :
        HasFDerivAt (fun _ : ℝ × E => (0, v))
          (0 : (ℝ × E) →L[ℝ] (ℝ × E)) (t, x))
  have hQtime0 := HasFDerivAt.comp (t : ℝ) hQ
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) t x)
  have hQtime := hQtime0.hasDerivAt
  have hsymm := (hfull.contDiffAt (x := (t, x))).isSymmSndFDerivAt (by norm_num)
  have hswap :
      (fderiv ℝ (fderiv ℝ full) (t, x)) inl (0, v) =
        (fderiv ℝ (fderiv ℝ full) (t, x)) (0, v) inl := by
    exact hsymm.eq inl (0, v)
  have hQtime'₀ : HasDerivAt
      (fun τ : ℝ => (fderiv ℝ full (τ, x)) (0, v)) _ t :=
    hQtime.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun τ => by
        simp only [Function.comp_apply]))
  have hQtime' : HasDerivAt
      (fun τ : ℝ => (fderiv ℝ full (τ, x)) (0, v))
      (fderiv ℝ (fderiv ℝ full) (t, x) inl (0, v))
      t := by
    exact hQtime'₀.congr_deriv (by
      simpa [inl] using hswap)
  have hslice : ∀ τ : ℝ,
      fderiv ℝ (fun y : E => F τ y) x v =
        (fderiv ℝ full (τ, x)) (0, v) := by
    intro τ
    have htime := (hfull.contDiffAt (x := (τ, x))).differentiableAt
      (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    have hcomp := HasFDerivAt.comp x htime.hasFDerivAt
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) τ x)
    have hfd := congrArg (fun L : E →L[ℝ] ℝ => L v) hcomp.fderiv
    simpa [full, Function.comp_def] using hfd
  have htarget := hQtime'.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun τ => hslice τ))
  have hderiv_eq :
      fderiv ℝ (fderiv ℝ full) (t, x) (0, v) inl =
          fderiv ℝ Fdot x v := by
    calc
      fderiv ℝ (fderiv ℝ full) (t, x) (0, v) inl =
          (((fderiv ℝ full (t, x)).comp (0 : (ℝ × E) →L[ℝ] (ℝ × E)) +
                (fderiv ℝ (fderiv ℝ full) (t, x)).flip inl).comp inrMap) v := by
              simp [inl, inrMap, ContinuousLinearMap.add_apply,
                ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
                zero_add, ContinuousLinearMap.flip_apply]
      _ = fderiv ℝ Fdot x v := by
        rw [← congrArg (fun L : E →L[ℝ] ℝ => L v) hFdotDeriv.fderiv]
  exact htarget.congr_deriv (hswap.trans hderiv_eq)

/-! A local version is useful for manifold charts: a `C²` field only needs to be
known near the spacetime point at which the mixed derivative is taken. -/
theorem hasDerivAt_fderiv_space_of_joint_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E → ℝ) (Fdot : E → ℝ)
    {t : ℝ} {x : E}
    (hF : ContDiffAt ℝ 2 (fun p : ℝ × E => F p.1 p.2) (t, x))
    (hFdot : ∀ y : E, HasDerivAt (fun τ : ℝ => F τ y) (Fdot y) t)
    (v : E) :
    HasDerivAt
      (fun τ => fderiv ℝ (fun y : E => F τ y) x v)
      (fderiv ℝ Fdot x v) t := by
  let full : (ℝ × E) → ℝ := fun p => F p.1 p.2
  have hfull : ContDiffAt ℝ 2 full (t, x) := by
    simpa [full] using hF
  have hDf : ContDiffAt ℝ 1 (fderiv ℝ full) (t, x) :=
    hfull.fderiv_right (m := 1) (by norm_num)
  have hDff : HasFDerivAt (fderiv ℝ full)
      (fderiv ℝ (fderiv ℝ full) (t, x)) (t, x) :=
    (hDf.differentiableAt one_ne_zero).hasFDerivAt
  let inrMap : E →L[ℝ] (ℝ × E) := ContinuousLinearMap.inr ℝ ℝ E
  let inl : ℝ × E := (1, (0 : E))
  have hS0 :=
    hDff.clm_apply
      (hasFDerivAt_const (inl : ℝ × E) (t, x) :
        HasFDerivAt (fun _ : ℝ × E => inl)
          (0 : (ℝ × E) →L[ℝ] (ℝ × E)) (t, x))
  have hS : HasFDerivAt
      (fun p : ℝ × E => (fderiv ℝ full p) inl)
      ((fderiv ℝ full (t, x)).comp (0 : (ℝ × E) →L[ℝ] (ℝ × E)) +
        (fderiv ℝ (fderiv ℝ full) (t, x)).flip inl)
      (t, x) := by
    simpa only using hS0
  have hPderiv : HasFDerivAt
      (fun y : E => (fderiv ℝ full (t, y)) inl)
      (((fderiv ℝ full (t, x)).comp (0 : (ℝ × E) →L[ℝ] (ℝ × E)) +
        (fderiv ℝ (fderiv ℝ full) (t, x)).flip inl).comp inrMap)
      x := by
    simpa [inl, Function.comp_def] using
      HasFDerivAt.comp x hS
        (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
  have hfullOn : ∃ u ∈ 𝓝 (t, x), ContDiffOn ℝ 2 full u :=
    hfull.contDiffOn (m := (2 : WithTop ℕ∞)) (le_refl _) (by norm_num)
  rcases hfullOn with ⟨u, hu, hU⟩
  rcases mem_nhds_iff.mp hu with ⟨w, hwU, hwopen, hwtx⟩
  have htimeAt : ∀ᶠ y : E in 𝓝 x,
      HasFDerivAt full (fderiv ℝ full (t, y)) (t, y) := by
    have hpair : ContinuousAt (fun y : E => (t, y)) x :=
      continuousAt_const.prodMk continuousAt_id
    have hyW : {y : E | (t, y) ∈ w} ∈ 𝓝 x :=
      hpair.preimage_mem_nhds (hwopen.mem_nhds hwtx)
    filter_upwards [hyW] with y hy
    have huy : u ∈ 𝓝 (t, y) :=
      Filter.mem_of_superset (hwopen.mem_nhds hy) hwU
    exact ((hU (t, y) (hwU hy)).contDiffAt huy).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hP_eq_full : ∀ᶠ y : E in 𝓝 x,
      fderiv ℝ (fun τ : ℝ => F τ y) t 1 =
        (fderiv ℝ full (t, y)) inl := by
    filter_upwards [htimeAt] with y hy
    have hcomp := HasFDerivAt.comp t hy
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) t y)
    have hfd := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hcomp.fderiv
    simpa [full, inl, Function.comp_def] using hfd
  let P : E → ℝ := fun y => fderiv ℝ (fun τ : ℝ => F τ y) t 1
  have hP_eq : ∀ᶠ y : E in 𝓝 x, P y = Fdot y := by
    filter_upwards [hP_eq_full] with y hy
    have hfd := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1)
      (hFdot y).hasFDerivAt.fderiv
    simpa [P] using hfd
  have hPderiv' := hPderiv.congr_of_eventuallyEq
    (hP_eq_full.mono (fun y hy => by simpa [P] using hy))
  have hFdotDeriv := hPderiv'.congr_of_eventuallyEq
    (hP_eq.mono (fun y hy => hy.symm))
  have hQ : HasFDerivAt
      (fun p : ℝ × E => (fderiv ℝ full p) (0, v))
      ((fderiv ℝ full (t, x)).comp (0 : (ℝ × E) →L[ℝ] (ℝ × E)) +
        (fderiv ℝ (fderiv ℝ full) (t, x)).flip (0, v))
      (t, x) :=
    hDff.clm_apply
      (hasFDerivAt_const (0, v) (t, x) :
        HasFDerivAt (fun _ : ℝ × E => (0, v))
          (0 : (ℝ × E) →L[ℝ] (ℝ × E)) (t, x))
  have hQtime0 := HasFDerivAt.comp t hQ
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) t x)
  have hQtime := hQtime0.hasDerivAt
  have hsymm := hfull.isSymmSndFDerivAt (by norm_num)
  have hswap :
      (fderiv ℝ (fderiv ℝ full) (t, x)) inl (0, v) =
        (fderiv ℝ (fderiv ℝ full) (t, x)) (0, v) inl := by
    exact hsymm.eq inl (0, v)
  have hQtime'₀ : HasDerivAt
      (fun τ : ℝ => (fderiv ℝ full (τ, x)) (0, v)) _ t :=
    hQtime.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun τ => by
        simp only [Function.comp_apply]))
  have hQtime' : HasDerivAt
      (fun τ : ℝ => (fderiv ℝ full (τ, x)) (0, v))
      (fderiv ℝ (fderiv ℝ full) (t, x) inl (0, v)) t := by
    exact hQtime'₀.congr_deriv (by
      simpa [inl] using hswap)
  have htimeAt' : ∀ᶠ τ : ℝ in 𝓝 t,
      HasFDerivAt full (fderiv ℝ full (τ, x)) (τ, x) := by
    have hpair : ContinuousAt (fun τ : ℝ => (τ, x)) t :=
      continuousAt_id.prodMk continuousAt_const
    have htW : {τ : ℝ | (τ, x) ∈ w} ∈ 𝓝 t :=
      hpair.preimage_mem_nhds (hwopen.mem_nhds hwtx)
    filter_upwards [htW] with τ hτ
    have huτ : u ∈ 𝓝 (τ, x) :=
      Filter.mem_of_superset (hwopen.mem_nhds hτ) hwU
    exact ((hU (τ, x) (hwU hτ)).contDiffAt huτ).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hslice : ∀ᶠ τ : ℝ in 𝓝 t,
      fderiv ℝ (fun y : E => F τ y) x v =
        (fderiv ℝ full (τ, x)) (0, v) := by
    filter_upwards [htimeAt'] with τ hτ
    have hcomp := HasFDerivAt.comp x hτ
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) τ x)
    have hfd := congrArg (fun L : E →L[ℝ] ℝ => L v) hcomp.fderiv
    simpa [full, Function.comp_def] using hfd
  have htarget := hQtime'.congr_of_eventuallyEq hslice
  have hderiv_eq :
      fderiv ℝ (fderiv ℝ full) (t, x) (0, v) inl =
          fderiv ℝ Fdot x v := by
    calc
      fderiv ℝ (fderiv ℝ full) (t, x) (0, v) inl =
          (((fderiv ℝ full (t, x)).comp (0 : (ℝ × E) →L[ℝ] (ℝ × E)) +
                (fderiv ℝ (fderiv ℝ full) (t, x)).flip inl).comp inrMap) v := by
              simp [inl, inrMap, ContinuousLinearMap.add_apply,
                ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
                zero_add, ContinuousLinearMap.flip_apply]
      _ = fderiv ℝ Fdot x v := by
        rw [← congrArg (fun L : E →L[ℝ] ℝ => L v) hFdotDeriv.fderiv]
  exact htarget.congr_deriv (hswap.trans hderiv_eq)

end PoincareCurvature
