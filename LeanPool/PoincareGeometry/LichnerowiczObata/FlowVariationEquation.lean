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

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # The variational equation derived from a smooth flow equation -/

@[expose] public noncomputable section
open Filter
open scoped Topology ContDiff

namespace LichnerowiczObata

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Commuting second derivatives differentiates a prescribed flow
right-hand side even when it depends on the initial parameter. -/
theorem fderiv_variation_equation_rhs {φ rhs : E → F} {x : E}
    (hφ : ContDiffAt ℝ 2 φ x) (a b : E)
    (hode : (fun y => fderiv ℝ φ y b) =ᶠ[𝓝 x] rhs) :
    fderiv ℝ (fun y => fderiv ℝ φ y a) x b = fderiv ℝ rhs x a := by
  have hD : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have he (c d : E) : fderiv ℝ (fun y => fderiv ℝ φ y c) x d =
      fderiv ℝ (fderiv ℝ φ) x d c := by
    rw [fderiv_clm_apply hD (differentiableAt_const c)]
    simp
  rw [he a b, hφ.isSymmSndFDerivAt (by norm_num) b a, ← he b a, hode.fderiv_eq]

/-- Differentiating the actual flow equation and commuting second
derivatives yields the linearized equation for spatial variations. -/
theorem fderiv_variation_equation {φ : E → F} {v : F → F} {x : E}
    (hφ : ContDiffAt ℝ 2 φ x) (hv : DifferentiableAt ℝ v (φ x)) (a b : E)
    (hode : (fun y => fderiv ℝ φ y b) =ᶠ[𝓝 x] (v ∘ φ)) :
    fderiv ℝ (fun y => fderiv ℝ φ y a) x b =
      fderiv ℝ v (φ x) (fderiv ℝ φ x a) := by
  rw [fderiv_variation_equation_rhs hφ a b hode,
    fderiv_comp x hv (hφ.differentiableAt (by norm_num))]
  rfl

/-- A smooth family of actual ODE solutions satisfies the variational ODE
in each initial-point direction. The linearized equation is a conclusion. -/
theorem hasDerivAt_flow_variation {φ : E × ℝ → F} {v : F → F}
    {U : Set (E × ℝ)} (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U)
    (hode : ∀ y ∈ U, HasDerivAt (fun t => φ (y.1, t)) (v (φ y)) y.2)
    {x : E} {t : ℝ} (hx : (x, t) ∈ U) (hv : DifferentiableAt ℝ v (φ (x, t))) (u : E) :
    HasDerivAt (fun s => fderiv ℝ φ (x, s) (u, 0))
      (fderiv ℝ v (φ (x, t)) (fderiv ℝ φ (x, t) (u, 0))) t := by
  have hs : ContDiffAt ℝ 2 φ (x, t) := (hφ _ hx).contDiffAt (hU.mem_nhds hx)
  have he : (fun y => fderiv ℝ φ y (0, 1)) =ᶠ[𝓝 (x, t)] (v ∘ φ) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hd := ((hφ y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
    have hp := hd.hasFDerivAt.comp_hasDerivAt y.2
      ((hasDerivAt_const y.2 y.1).prodMk (hasDerivAt_id y.2))
    exact hp.unique (hode y hy)
  have hD : DifferentiableAt ℝ (fderiv ℝ φ) (x, t) :=
    (hs.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hd := (hD.clm_apply (differentiableAt_const (u, (0 : ℝ)))).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
  have hlin := fderiv_variation_equation hs hv (u, (0 : ℝ)) (0, (1 : ℝ)) he
  simpa only [Function.comp_def, hlin] using hd

/-- The initial-value identity determines every spatial derivative at time zero. -/
theorem fderiv_flow_initial_apply {φ : E × ℝ → E} {x : E}
    (hφ : DifferentiableAt ℝ φ (x, 0))
    (hinit : (fun y => φ (y, 0)) =ᶠ[𝓝 x] id) (u : E) :
    fderiv ℝ φ (x, 0) (u, 0) = u := by
  have hi : HasFDerivAt (fun y : E => (y, (0 : ℝ)))
      ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ)) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const (0 : ℝ) x)
  have hd := hφ.hasFDerivAt.comp x hi
  have he := hinit.fderiv_eq (𝕜 := ℝ)
  have hd' : HasFDerivAt (fun y => φ (y, 0))
      ((fderiv ℝ φ (x, 0)).comp ((ContinuousLinearMap.id ℝ E).prod 0)) x := hd
  rw [hd'.fderiv] at he
  simpa using congrArg (fun L : E →L[ℝ] E => L u) he

/-- Restriction to initial velocities and projection to positions turns the
flat flow derivative into a scalar multiple of the identity. -/
theorem hasFDerivAt_position_endpoint {α : (E × E) × ℝ → E × E} {z : E} {t : ℝ}
    (hα : DifferentiableAt ℝ α ((z, 0), t))
    (hlin : ∀ v : E, fderiv ℝ α ((z, 0), t) ((0, v), 0) = (t • v, v)) :
    HasFDerivAt (fun v => (α ((z, v), t)).1)
      (t • ContinuousLinearMap.id ℝ E) 0 := by
  let L : E →L[ℝ] (E × E) × ℝ :=
    ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)).prod 0
  have hi : HasFDerivAt (fun v : E => ((z, v), t)) L 0 :=
    ((hasFDerivAt_const z 0).prodMk (hasFDerivAt_id 0)).prodMk
      (hasFDerivAt_const t 0)
  have hd : HasFDerivAt (fun v => α ((z, v), t))
      ((fderiv ℝ α ((z, 0), t)).comp L) 0 := hα.hasFDerivAt.comp 0 hi
  have hp : HasFDerivAt (fun v => (α ((z, v), t)).1)
      ((ContinuousLinearMap.fst ℝ E E).comp ((fderiv ℝ α ((z, 0), t)).comp L)) 0 :=
    (hasFDerivAt_fst (p := α ((z, 0), t))).comp 0 hd
  convert hp using 1
  ext v
  simpa [L] using (congrArg Prod.fst (hlin v)).symm

/-- A parameter-dependent flow equation yields the spatial variational
equation by differentiating its actual right-hand side. -/
theorem hasDerivAt_flow_variation_rhs {φ rhs : E × ℝ → F}
    {U : Set (E × ℝ)} (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U)
    (hode : ∀ y ∈ U, HasDerivAt (fun t => φ (y.1, t)) (rhs y) y.2)
    {x : E} {t : ℝ} (hx : (x, t) ∈ U) (u : E) :
    HasDerivAt (fun s => fderiv ℝ φ (x, s) (u, 0))
      (fderiv ℝ rhs (x, t) (u, 0)) t := by
  have hs : ContDiffAt ℝ 2 φ (x, t) := hφ.contDiffAt (hU.mem_nhds hx)
  have he : (fun y => fderiv ℝ φ y (0, 1)) =ᶠ[𝓝 (x, t)] rhs := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hd := (hφ.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
    have hp := hd.hasFDerivAt.comp_hasDerivAt y.2
      ((hasDerivAt_const y.2 y.1).prodMk (hasDerivAt_id y.2))
    exact hp.unique (hode y hy)
  have hD : DifferentiableAt ℝ (fderiv ℝ φ) (x, t) :=
    (hs.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hd := (hD.clm_apply (differentiableAt_const (u, (0 : ℝ)))).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
  have hlin := fderiv_variation_equation_rhs hs (u, (0 : ℝ)) (0, (1 : ℝ)) he
  simpa only [Function.comp_def, hlin] using hd

/-- Initial-parameter-dependent speed contributes an explicit longitudinal
term to the spatial variation equation. -/
theorem hasDerivAt_scaled_flow_variation
    {φ : E × ℝ → F} {v : F → F} {σ : E → ℝ}
    {U : Set (E × ℝ)} (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U)
    (hode : ∀ y ∈ U, HasDerivAt (fun t => φ (y.1, t)) (σ y.1 • v (φ y)) y.2)
    {x : E} {t : ℝ} (hx : (x, t) ∈ U)
    (hσ : DifferentiableAt ℝ σ x) (hv : DifferentiableAt ℝ v (φ (x, t))) (u : E) :
    HasDerivAt (fun s => fderiv ℝ φ (x, s) (u, 0))
      (σ x • fderiv ℝ v (φ (x, t)) (fderiv ℝ φ (x, t) (u, 0)) +
        fderiv ℝ σ x u • v (φ (x, t))) t := by
  have hφd := (hφ.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hσc : HasFDerivAt (fun q : E × ℝ => σ q.1)
      ((fderiv ℝ σ x).comp (ContinuousLinearMap.fst ℝ E ℝ)) (x, t) :=
    hσ.hasFDerivAt.comp (x, t) (hasFDerivAt_fst (p := (x, t)))
  have hvc : HasFDerivAt (fun q => v (φ q))
      ((fderiv ℝ v (φ (x, t))).comp (fderiv ℝ φ (x, t))) (x, t) :=
    hv.hasFDerivAt.comp (x, t) hφd.hasFDerivAt
  have hprod : HasFDerivAt (fun q : E × ℝ => σ q.1 • v (φ q))
      (σ x • ((fderiv ℝ v (φ (x, t))).comp (fderiv ℝ φ (x, t))) +
        ((fderiv ℝ σ x).comp (ContinuousLinearMap.fst ℝ E ℝ)).smulRight (v (φ (x, t))))
      (x, t) := hσc.smul hvc
  have hd := hasDerivAt_flow_variation_rhs hU hφ hode hx u
  rw [hprod.fderiv] at hd
  simpa using hd

end LichnerowiczObata
