/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.VectorField
public import LeanPool.PoincareGeometry.PoincareCurvature.Analysis.MixedTimeSpace

/-!
# Mixed time--space regularity for Lie brackets

This file proves the Euclidean, vector-valued mixed derivative bridge needed for the
Hamilton--Ivey moving-section Koszul formula.  The scalar theorem
`PoincareCurvature.hasDerivAt_fderiv_space_of_joint_contDiffAt` is the underlying local mixed
partial result; the vector-valued version below follows the same chart-level argument, using
symmetry of the second Fréchet derivative.

The manifold chart transport from a jointly `C²` totalized tangent section to these Euclidean
lemmas is intentionally kept separate, so that no derivative of a manifold Lie bracket is
postulated here.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace PoincareCurvature
/-- Vector-valued mixed partials: a jointly `C²` map `(τ,y) ↦ F τ y` has time derivative of
its spatial differential equal to the spatial differential of its pointwise time derivative.

This is the vector-codomain counterpart of
`hasDerivAt_fderiv_space_of_joint_contDiffAt`, proved by the same local Fréchet-derivative and
symmetric-Hessian argument. -/
theorem hasDerivAt_fderiv_space_vector_of_joint_contDiffAt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (G : ℝ → E → F) (Gdot : E → F)
    {t : ℝ} {x : E}
    (hG : ContDiffAt ℝ 2 (fun p : ℝ × E => G p.1 p.2) (t, x))
    (hGdot : ∀ y : E, HasDerivAt (fun τ : ℝ => G τ y) (Gdot y) t)
    (v : E) :
    HasDerivAt
      (fun τ => fderiv ℝ (fun y => G τ y) x v)
      (fderiv ℝ Gdot x v) t := by
  let full : (ℝ × E) → F := fun p => G p.1 p.2
  have hfull : ContDiffAt ℝ 2 full (t, x) := by
    simpa [full] using hG
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
      fderiv ℝ (fun τ : ℝ => G τ y) t 1 = (fderiv ℝ full (t, y)) inl := by
    filter_upwards [htimeAt] with y hy
    have hcomp := HasFDerivAt.comp t hy
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) t y)
    have hfd := congrArg (fun L : ℝ →L[ℝ] F => L 1) hcomp.fderiv
    simpa [full, inl, Function.comp_def] using hfd
  let P : E → F := fun y => fderiv ℝ (fun τ : ℝ => G τ y) t 1
  have hP_eq : ∀ᶠ y : E in 𝓝 x, P y = Gdot y := by
    filter_upwards [hP_eq_full] with y hy
    have hfd := congrArg (fun L : ℝ →L[ℝ] F => L 1)
      (hGdot y).hasFDerivAt.fderiv
    simpa [P] using hfd
  have hPderiv' := hPderiv.congr_of_eventuallyEq
    (hP_eq_full.mono (fun y hy => by simpa [P] using hy))
  have hGdotDeriv := hPderiv'.congr_of_eventuallyEq
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
        (fderiv ℝ (fderiv ℝ full) (t, x)) (0, v) inl :=
    hsymm.eq inl (0, v)
  have hQtime'₀ : HasDerivAt
      (fun τ : ℝ => (fderiv ℝ full (τ, x)) (0, v)) _ t :=
    hQtime.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun τ => by simp only [Function.comp_apply]))
  have hQtime' : HasDerivAt
      (fun τ : ℝ => (fderiv ℝ full (τ, x)) (0, v))
      (fderiv ℝ (fderiv ℝ full) (t, x) inl (0, v)) t := by
    exact hQtime'₀.congr_deriv (by simpa [inl] using hswap)
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
      fderiv ℝ (fun y : E => G τ y) x v = (fderiv ℝ full (τ, x)) (0, v) := by
    filter_upwards [htimeAt'] with τ hτ
    have hcomp := HasFDerivAt.comp x hτ
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) τ x)
    have hfd := congrArg (fun L : E →L[ℝ] F => L v) hcomp.fderiv
    simpa [full, Function.comp_def] using hfd
  have htarget := hQtime'.congr_of_eventuallyEq hslice
  have hderiv_eq :
      fderiv ℝ (fderiv ℝ full) (t, x) (0, v) inl = fderiv ℝ Gdot x v := by
    calc
      fderiv ℝ (fderiv ℝ full) (t, x) (0, v) inl =
          (((fderiv ℝ full (t, x)).comp (0 : (ℝ × E) →L[ℝ] (ℝ × E)) +
                (fderiv ℝ (fderiv ℝ full) (t, x)).flip inl).comp inrMap) v := by
              simp [inl, inrMap, ContinuousLinearMap.add_apply,
                ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
                zero_add, ContinuousLinearMap.flip_apply]
      _ = fderiv ℝ Gdot x v := by
        rw [← congrArg (fun L : E →L[ℝ] F => L v) hGdotDeriv.fderiv]
  exact htarget.congr_deriv (hswap.trans hderiv_eq)
/-- Time derivative of a Euclidean Lie bracket when the left field is jointly `C²` in time and
space. -/
theorem hasDerivAt_lieBracket_left_of_joint_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (U : ℝ → E → E) (Udot V : E → E)
    {t : ℝ} {x : E}
    (hU : ContDiffAt ℝ 2 (fun p : ℝ × E => U p.1 p.2) (t, x))
    (hUtime : ∀ y : E, HasDerivAt (fun τ : ℝ => U τ y) (Udot y) t)
    (hV : ContDiffAt ℝ 1 V x) :
    HasDerivAt
      (fun τ => VectorField.lieBracket ℝ (U τ) V x)
      (VectorField.lieBracket ℝ Udot V x) t := by
  have hUvalue := hUtime x
  let L : E →L[ℝ] E := fderiv ℝ V x
  have hLconst : HasDerivAt (fun _ : ℝ => L) (0 : E →L[ℝ] E) t :=
    hasDerivAt_const t L
  have hfirst := hLconst.clm_apply hUvalue
  have hfirst' : HasDerivAt
      (fun τ => fderiv ℝ V x (U τ x))
      (fderiv ℝ V x (Udot x)) t := by
    simpa [L] using hfirst
  have hsecond :=
    hasDerivAt_fderiv_space_vector_of_joint_contDiffAt U Udot hU hUtime (V x)
  change HasDerivAt
    (fun τ => fderiv ℝ V x (U τ x) -
      fderiv ℝ (fun y => U τ y) x (V x))
    (fderiv ℝ V x (Udot x) - fderiv ℝ Udot x (V x)) t
  exact hfirst'.sub hsecond
/-- Time derivative of a Euclidean Lie bracket when the right field is jointly `C²` in time and
space. -/
theorem hasDerivAt_lieBracket_right_of_joint_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (U : ℝ → E → E) (Udot V : E → E)
    {t : ℝ} {x : E}
    (hU : ContDiffAt ℝ 2 (fun p : ℝ × E => U p.1 p.2) (t, x))
    (hUtime : ∀ y : E, HasDerivAt (fun τ : ℝ => U τ y) (Udot y) t)
    (hV : ContDiffAt ℝ 1 V x) :
    HasDerivAt
      (fun τ => VectorField.lieBracket ℝ V (U τ) x)
      (VectorField.lieBracket ℝ V Udot x) t := by
  have hUvalue := hUtime x
  let L : E →L[ℝ] E := fderiv ℝ V x
  have hLconst : HasDerivAt (fun _ : ℝ => L) (0 : E →L[ℝ] E) t :=
    hasDerivAt_const t L
  have hsecond := hLconst.clm_apply hUvalue
  have hsecond' : HasDerivAt
      (fun τ => fderiv ℝ V x (U τ x))
      (fderiv ℝ V x (Udot x)) t := by
    simpa [L] using hsecond
  have hfirst :=
    hasDerivAt_fderiv_space_vector_of_joint_contDiffAt U Udot hU hUtime (V x)
  change HasDerivAt
    (fun τ => fderiv ℝ (fun y => U τ y) x (V x) -
      fderiv ℝ V x (U τ x))
    (fderiv ℝ Udot x (V x) - fderiv ℝ V x (Udot x)) t
  exact hfirst.sub hsecond'

end PoincareCurvature
