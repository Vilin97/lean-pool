/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowIsFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.FlowDefs.FlowInv
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.LimitFieldBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.ExplicitBarNorm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.LimitFieldRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.Scalars
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.TimeScaleBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.Liouville
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SpatialRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.InverseC1
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.CorrectorBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.LocalFinite
public import Mathlib.Analysis.Calculus.MeanValue

/-! Time regularity ingredients for the limit stream.

The flow/material estimates of §2 are carried as explicit source-form data;
the recursion estimate differentiates the finite-overlap stream update and
then applies the mean-value theorem in time.
-/

@[expose] public section

open MeasureTheory Homogenization Filter Topology
open scoped ContDiff

noncomputable section

namespace AVenhance

/-- The canonical smooth periodic flow associated with one member of a stream
sequence. -/
noncomputable def constructionFlow {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ) (m : ℕ) :
    ℝ → Vec 2 → ℝ → Vec 2 := by
  let hφ := streamSeq_isAdmissible hseq m
  exact flow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz

/-- The inverse-flow map for `constructionFlow`, with arguments ordered as in
the `flowInv`. -/
noncomputable def constructionFlowInv {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ) (m : ℕ) :
    ℝ → Vec 2 → ℝ → Vec 2 := by
  let hφ := streamSeq_isAdmissible hseq m
  exact flowInv (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz

/-- The spatial Jacobian of the `m`th flow at offset `t` from start time `s`. -/
noncomputable def constructionFlowJacobian {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ) (m : ℕ)
    (t s : ℝ) (x : Vec 2) : Vec 2 →L[ℝ] Vec 2 :=
  fderiv ℝ (fun y : Vec 2 => constructionFlow hseq m (s + t) y s) x

/-- The spatial Jacobian of the inverse flow at offset `t` from start time `s`. -/
noncomputable def constructionFlowInvJacobian {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ) (m : ℕ)
    (t s : ℝ) (x : Vec 2) : Vec 2 →L[ℝ] Vec 2 :=
  fderiv ℝ (fun y : Vec 2 => constructionFlowInv hseq m (s + t) y s) x

/-- The forward spatial Jacobian pulled back by its inverse, as in
`c.material.DX.Xinv` and `c.flowreg` display 2. -/
noncomputable def constructionComposedFlowJacobian {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ) (m : ℕ)
    (s r : ℝ) (x : Vec 2) : Vec 2 →L[ℝ] Vec 2 :=
  constructionFlowJacobian hseq m r s
    (constructionFlowInv hseq m (s + r) x s)

/-- Componentwise version of the source spatial seminorm for a matrix field.
Each entry is measured by the scalar `barNorm`. -/
def flowJacobianBarNorm (n : ℕ) (R : ℝ)
    (J : Vec 2 → Vec 2 →L[ℝ] Vec 2) : ENNReal :=
  ⨆ i : Fin 2, ⨆ j : Fin 2,
    barNorm n R (fun x : Vec 2 => J x (basisVec j) i)

/-- One material derivative along a time-dependent vector field, matching
`D_{t,m} = ∂ₜ + b_m·∇` in the source. -/
def constructionMaterialDerivative (b : ℝ → Vec 2 → Vec 2)
    (F : ℝ → Vec 2 → ℝ) : ℝ → Vec 2 → ℝ :=
  fun t x => deriv (fun r : ℝ => F r x) t + fderiv ℝ (F t) x (b t x)

/-- Iterates of the source material derivative. -/
def constructionMaterialIterate (b : ℝ → Vec 2 → Vec 2) :
    ℕ → (ℝ → Vec 2 → ℝ) → ℝ → Vec 2 → ℝ
  | 0, F => F
  | n + 1, F => constructionMaterialDerivative b (constructionMaterialIterate b n F)

/-- Explicit source-form flow and material bounds used in the differentiated
stream recursion. The seminorm fields transcribe e.Xm.regbounds and all four
displays of c.flowreg componentwise; `material_jacobian` transcribes
c.material.DX.Xinv. The final field records e.PDE.backwards for the inverse
flow. -/
structure FlowBoundsData {β : ℝ} (I : Ingredients β)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hseq : IsStreamSeq I Φ) (Cmat : ℝ) : Prop where
  /-- The source constant in c.material.DX.Xinv is at least one. -/
  material_constant_ge_one : 1 ≤ Cmat
  /-- e.Xm.regbounds, componentwise for every derivative order n. -/
  inverse_regbounds : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n : ℕ,
      flowJacobianBarNorm n (2 ^ 11 * (epsilon β I.Λ m)⁻¹)
        (fun x => constructionFlowInvJacobian hseq m t s x -
          ContinuousLinearMap.id ℝ (Vec 2))
        ≤ ENNReal.ofReal (2 ^ 23 * |t| * a β I.Λ m)
  /-- c.flowreg display e.Xm.bound.1. -/
  flow_close : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ x : Vec 2,
      ‖constructionFlowJacobian hseq m t s x -
        ContinuousLinearMap.id ℝ (Vec 2)‖ ≤
        2 ^ 23 * |t| * a β I.Λ m ∧
      2 ^ 23 * |t| * a β I.Λ m ≤ 1 / 4
  /-- c.flowreg display e.Xm.bound.2. -/
  flow_jacobian_composed : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n : ℕ,
      flowJacobianBarNorm n (2 ^ 10 * (epsilon β I.Λ m)⁻¹)
        (fun x => constructionComposedFlowJacobian hseq m s t x -
          ContinuousLinearMap.id ℝ (Vec 2))
        ≤ ENNReal.ofReal 40
  /-- Smooth spatial representative used to evaluate the essential-supremum
  seminorm bounds pointwise. This is qualitative flow regularity from §2. -/
  composed_jacobian_smooth : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ →
      ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 =>
        constructionComposedFlowJacobian hseq m s t x)
  /-- c.flowreg display e.Xm.bound.3. -/
  flow_jacobian : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n : ℕ, 1 ≤ n →
      flowJacobianBarNorm n (2 ^ 14 * (epsilon β I.Λ m)⁻¹)
        (constructionFlowJacobian hseq m t s) ≤ ENNReal.ofReal 12
  /-- Corrected c.flowreg derivative bound. The printed radius coefficient
  `2^13` fails at order seven (checked against the source); `Scalars.flow_derivative_bound`
  proves the corresponding conversion with `2^14`. -/
  flow_higher_derivative : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n : ℕ, 1 ≤ n →
      ∀ x : Vec 2, ∀ J : Fin n → Fin 2,
      ‖iteratedFDeriv ℝ n (fun y : Vec 2 =>
        constructionFlow hseq m (s + t) y s) x (fun k => basisVec (J k))‖ ≤
          2 * n.factorial * (2 ^ 14 * (epsilon β I.Λ m)⁻¹) ^ (n - 1)
  /-- c.material.DX.Xinv, in its pointwise derivative form. -/
  material_jacobian : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ n ell : ℕ,
      n + ell ≤ Nstar β → ∀ i j : Fin 2, ∀ x : Vec 2,
        ∀ J : Fin n → Fin 2,
        ‖iteratedFDeriv ℝ n
          (fun y => constructionMaterialIterate
            (fun r z => streamVel (Φ m) (s + r) z) ell
            (fun r z => constructionComposedFlowJacobian hseq m s r z
              (basisVec j) i) t y)
          x (fun k => basisVec (J k))‖ ≤
          Cmat * (epsilon β I.Λ m)⁻¹ ^ n *
            (epsilon β I.Λ m ^ (β - 2)) ^ ell
  /-- Classical differentiability in target time of the entries appearing in
  c.material.DX.Xinv; this is the regularity implicit in that display's
  partial-time derivatives. -/
  material_jacobian_time_diff : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ,
    |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ → ∀ i j : Fin 2, ∀ x : Vec 2,
      DifferentiableAt ℝ
        (fun r => constructionComposedFlowJacobian hseq m s r x (basisVec j) i) t
  /-- Classical target-time differentiability of the spatial inverse-flow
  Jacobian. This is the mixed regularity needed when differentiating the
  inverse transport equation in space. -/
  inverse_jacobian_time_diff : ∀ m : ℕ, 1 ≤ m → ∀ s t : ℝ, ∀ x : Vec 2,
      DifferentiableAt ℝ
        (fun r => constructionFlowInvJacobian hseq m r s x) t
  /-- e.PDE.backwards for each stream flow. -/
  inverse_transport : ∀ m : ℕ, 1 ≤ m → ∀ t s : ℝ, ∀ x : Vec 2,
    HasDerivAt (fun r : ℝ => constructionFlowInv hseq m r x s)
      (-(constructionFlowInvJacobian hseq m (t - s) s x)
        (streamVel (Φ m) t x)) t

/-- Differentiate a transported spatial profile derivative when both the
inverse trajectory and its spatial Jacobian have target-time derivatives. -/
theorem hasDerivAt_profile_spatialDerivative
    {t : ℝ} {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {Y : ℝ → Vec 2} {DY : ℝ → Vec 2 →L[ℝ] Vec 2}
    {Ydot : Vec 2} {DYdot : Vec 2 →L[ℝ] Vec 2}
    (hY : HasDerivAt Y Ydot t)
    (hDY : ∀ v : Vec 2, HasDerivAt (fun r => DY r v) (DYdot v) t)
    (v : Vec 2) :
    HasDerivAt (fun r => fderiv ℝ ψ (Y r) (DY r v))
      (fderiv ℝ (fderiv ℝ ψ) (Y t) Ydot (DY t v) +
        fderiv ℝ ψ (Y t) (DYdot v)) t := by
  have hA : HasDerivAt (fun r => fderiv ℝ ψ (Y r))
      (fderiv ℝ (fderiv ℝ ψ) (Y t) Ydot) t := by
    have houter := hψ.fderiv_right (m := 1) (by simp)
    have houter' := (houter.differentiable (by simp) (Y t)).hasFDerivAt
    have hcomp := houter'.comp_hasDerivAt t hY
    simpa only [Function.comp_def] using hcomp
  have hV : HasDerivAt (fun r => DY r v) (DYdot v) t := hDY v
  simpa only [Function.comp_apply] using hA.clm_apply hV

/-- Product rule for the time-dependent cutoff multiplying a transported
spatial profile derivative. -/
theorem hasDerivAt_cutoff_mul_profile_spatialDerivative
    {t : ℝ} {c : ℝ → ℝ} {c' : ℝ} (hc : HasDerivAt c c' t)
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {Y : ℝ → Vec 2} {DY : ℝ → Vec 2 →L[ℝ] Vec 2}
    {Ydot : Vec 2} {DYdot : Vec 2 →L[ℝ] Vec 2}
    (hY : HasDerivAt Y Ydot t)
    (hDY : ∀ v : Vec 2, HasDerivAt (fun r => DY r v) (DYdot v) t)
    (v : Vec 2) :
    HasDerivAt (fun r => c r * fderiv ℝ ψ (Y r) (DY r v))
      (c' * fderiv ℝ ψ (Y t) (DY t v) + c t *
        (fderiv ℝ (fderiv ℝ ψ) (Y t) Ydot (DY t v) +
          fderiv ℝ ψ (Y t) (DYdot v))) t := by
  exact hc.mul (hasDerivAt_profile_spatialDerivative hψ hY hDY v)

/-- The normed-vector mean-value estimate used to turn the differentiated
recursion into a time-increment bound. -/
theorem norm_sub_le_of_uniform_deriv_le {f : ℝ → Vec 2} {B : ℝ}
    (hf : ∀ t : ℝ, DifferentiableAt ℝ f t)
    (hderiv : ∀ t : ℝ, ‖deriv f t‖ ≤ B) (s t : ℝ) :
    ‖f s - f t‖ ≤ B * |s - t| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (f := f) (x := s) (y := t)
    (fun r _ => hf r)
    (fun r _ => hderiv r)
    convex_univ (Set.mem_univ s) (Set.mem_univ t)
  simpa [Real.norm_eq_abs, norm_sub_rev] using h

theorem continuous_norm_le_of_ae_le {f : Vec 2 → ℝ} {B : ℝ}
    (hf : Continuous f) (hB : 0 ≤ B)
    (h : ∀ᵐ x ∂(volume : Measure (Vec 2)), ‖f x‖ₑ ≤ ENNReal.ofReal B) :
    ∀ x, ‖f x‖ ≤ B := by
  intro x
  by_contra hx
  have hx' : B < ‖f x‖ := lt_of_not_ge hx
  let U : Set (Vec 2) := {y | B < ‖f y‖}
  have hUopen : IsOpen U := isOpen_lt continuous_const (Continuous.norm hf)
  have hUnonempty : U.Nonempty := ⟨x, hx'⟩
  have hUpos : 0 < volume U := hUopen.measure_pos volume hUnonempty
  have hnotU : ∀ᵐ y ∂(volume : Measure (Vec 2)), y ∉ U := by
    filter_upwards [h] with y hy
    intro hyU
    have hle : ENNReal.ofReal ‖f y‖ ≤ ENNReal.ofReal B := by
      simpa [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs] using hy
    have hle' : ‖f y‖ ≤ B := (ENNReal.ofReal_le_ofReal_iff hB).mp hle
    exact (not_lt_of_ge hle') hyU
  have hUzero : volume U = 0 := by simpa [ae_iff] using hnotU
  exact (ne_of_gt hUpos) hUzero

theorem barNorm_iterated_pointwise {n : ℕ} {R B : ℝ} {f : Vec 2 → ℝ}
    (i : Fin n → Fin 2)
    (hf : Continuous (fun x => iteratedFDeriv ℝ n f x (fun j => basisVec (i j))))
    (hR : 0 < R) (hB : 0 ≤ B)
    (h : barNorm n R f ≤ ENNReal.ofReal B) :
    ∀ x, ‖iteratedFDeriv ℝ n f x (fun j => basisVec (i j))‖ ≤
      B / (((n + 1 : ℝ) ^ 2 / (n.factorial : ℝ)) * R⁻¹ ^ n) := by
  let g : Vec 2 → ℝ := fun x => iteratedFDeriv ℝ n f x (fun j => basisVec (i j))
  let c : ℝ := (n + 1 : ℝ) ^ 2 / (n.factorial : ℝ)
  let r : ℝ := c * R⁻¹ ^ n
  let W : ENNReal := ENNReal.ofReal c * (ENNReal.ofReal R)⁻¹ ^ n
  have hc : 0 < c := by dsimp [c]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hW : W = ENNReal.ofReal r := by
    dsimp [W, r, c]
    rw [← ENNReal.ofReal_inv_of_pos hR, ← ENNReal.ofReal_pow (by positivity)]
    rw [← ENNReal.ofReal_mul (by positivity)]
  have hWpos : 0 < W := by rw [hW]; exact ENNReal.ofReal_pos.mpr hr
  have hcoord : eLpNorm g ⊤ volume ≤
      (⨆ j : Fin n → Fin 2,
        eLpNorm (fun x => iteratedFDeriv ℝ n f x (fun k => basisVec (j k))) ⊤ volume) :=
    le_iSup_of_le i le_rfl
  have hmul : W * eLpNorm g ⊤ volume ≤ ENNReal.ofReal B := by
    calc
      W * eLpNorm g ⊤ volume ≤ W *
          (⨆ j : Fin n → Fin 2,
            eLpNorm (fun x => iteratedFDeriv ℝ n f x (fun k => basisVec (j k))) ⊤ volume) :=
        mul_le_mul_of_nonneg_left hcoord (by positivity)
      _ = barNorm n R f := by simp [W, barNorm, c, mul_assoc]
      _ ≤ ENNReal.ofReal B := h
  have hWne : W ≠ 0 := ne_of_gt hWpos
  have hprodtop : W * eLpNorm g ⊤ volume ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hmul ENNReal.ofReal_lt_top)
  have hDtop : eLpNorm g ⊤ volume ≠ ⊤ := by
    intro htop
    apply hprodtop
    exact (ENNReal.mul_eq_top).2 (Or.inl ⟨hWne, htop⟩)
  have hDreal : r * (eLpNorm g ⊤ volume).toReal ≤ B := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmul
    rw [ENNReal.toReal_mul, hW, ENNReal.toReal_ofReal hr.le,
      ENNReal.toReal_ofReal hB] at ht
    exact ht
  have hD' : eLpNorm g ⊤ volume ≤ ENNReal.ofReal (B / r) := by
    apply (ENNReal.toReal_le_toReal hDtop ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (div_nonneg hB hr.le)]
    exact (le_div_iff₀ hr).2 (by simpa [mul_comm] using hDreal)
  have hess : eLpNormEssSup g volume ≤ ENNReal.ofReal (B / r) := by
    rw [← eLpNorm_exponent_top hf.aestronglyMeasurable]
    exact hD'
  have hae : ∀ᵐ x ∂(volume : Measure (Vec 2)),
      ‖g x‖ₑ ≤ ENNReal.ofReal (B / r) :=
    (ae_le_eLpNormEssSup (f := g) (μ := volume)).mono fun x hx => hx.trans hess
  have hBr : 0 ≤ B / r := div_nonneg hB hr.le
  have hpoint := continuous_norm_le_of_ae_le hf hBr hae
  intro x
  simpa [g, c, r] using hpoint x

theorem continuous_iteratedCoordinate {n : ℕ} {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin n → Fin 2) :
    Continuous (fun x => iteratedFDeriv ℝ n f x (fun j => basisVec (i j))) := by
  have hT : Continuous (fun x => iteratedFDeriv ℝ n f x) :=
    continuous_iff_continuousAt.mpr fun x =>
      (hf.contDiffAt).continuousAt_iteratedFDeriv (by simp)
  fun_prop

theorem composed_jacobian_spatial_partial_bound {β Cmat : ℝ}
    {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} (hflow : FlowBoundsData I Φ hseq Cmat)
    {m : ℕ} (hm : 1 ≤ m) (s t : ℝ)
    (ht : |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹)
    (i j k : Fin 2) (x : Vec 2) :
    ‖fderiv ℝ (fun y : Vec 2 =>
        constructionComposedFlowJacobian hseq m s t y (basisVec j) i)
        x (basisVec k)‖ ≤ 2 ^ 14 * (epsilon β I.Λ m)⁻¹ := by
  let G : Vec 2 → Vec 2 →L[ℝ] Vec 2 :=
    constructionComposedFlowJacobian hseq m s t
  let f : Vec 2 → ℝ := fun y =>
    (G y - ContinuousLinearMap.id ℝ (Vec 2)) (basisVec j) i
  have hGsm := hflow.composed_jacobian_smooth m hm s t ht
  have hv : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => G y (basisVec j)) := by
    exact hGsm.clm_apply contDiff_const
  have hconst : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : Vec 2 => ContinuousLinearMap.id ℝ (Vec 2) (basisVec j)) :=
    contDiff_const
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := by
    dsimp [f]
    exact (contDiff_apply ℝ ℝ i).comp (hv.sub hconst)
  have hcont : Continuous
      (fun y => iteratedFDeriv ℝ 1 f y (fun _ => basisVec k)) :=
    continuous_iteratedCoordinate hf (fun _ => k)
  have hbar := hflow.flow_jacobian_composed m hm s t ht 1
  have heps : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hR : 0 < 2 ^ 10 * (epsilon β I.Λ m)⁻¹ := by positivity
  have hentrybar : barNorm 1 (2 ^ 10 * (epsilon β I.Λ m)⁻¹) f ≤
      ENNReal.ofReal 40 := by
    have h := (le_iSup_of_le i (le_iSup_of_le j le_rfl)).trans hbar
    simpa [f, G] using h
  have hpoint := barNorm_iterated_pointwise (fun _ : Fin 1 => k) hcont
    hR (by norm_num : (0 : ℝ) ≤ 40) hentrybar x
  let g : Vec 2 → ℝ := fun y => G y (basisVec j) i
  let c : Vec 2 → ℝ := fun _ =>
    (ContinuousLinearMap.id ℝ (Vec 2)) (basisVec j) i
  have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
    (contDiff_apply ℝ ℝ i).comp hv
  have hdiffg : DifferentiableAt ℝ g x := hg.differentiable (by simp) x
  have hdiffc : DifferentiableAt ℝ c x := differentiableAt_const _
  have hsub : fderiv ℝ f x = fderiv ℝ g x - fderiv ℝ c x := by
    dsimp [f, g, c]
    exact fderiv_sub hdiffg hdiffc
  have hcderiv : fderiv ℝ c x = 0 := by simp [c, fderiv_const_apply]
  have hderiv : fderiv ℝ
      (fun y : Vec 2 => G y (basisVec j) i) x (basisVec k) =
      iteratedFDeriv ℝ 1 f x (fun _ => basisVec k) := by
    have hcoord := congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (basisVec k)) hsub
    rw [hcderiv] at hcoord
    simpa [g, iteratedFDeriv_one_apply] using hcoord.symm
  have hbase : ‖fderiv ℝ f x (basisVec k)‖ ≤
      40 / (4 * (2 ^ 10 * (epsilon β I.Λ m)⁻¹)⁻¹) := by
    calc
      ‖fderiv ℝ f x (basisVec k)‖ ≤
          40 / (((1 + 1 : ℝ) ^ 2 / (Nat.factorial 1 : ℝ)) *
            (2 ^ 10 * (epsilon β I.Λ m)⁻¹)⁻¹) := by
              simpa [iteratedFDeriv_one_apply] using hpoint
      _ = 40 / (4 * (2 ^ 10 * (epsilon β I.Λ m)⁻¹)⁻¹) := by norm_num
  have hrough : 40 / (4 * (2 ^ 10 * (epsilon β I.Λ m)⁻¹)⁻¹) ≤
      2 ^ 14 * (epsilon β I.Λ m)⁻¹ := by
    have : 40 / (4 * (2 ^ 10 * (epsilon β I.Λ m)⁻¹)⁻¹) =
        2 ^ 10 * 10 * (epsilon β I.Λ m)⁻¹ := by
      field_simp [ne_of_gt heps]
      norm_num
    rw [this]
    have hinv : 0 ≤ (epsilon β I.Λ m)⁻¹ := inv_nonneg.mpr heps.le
    norm_num at hinv ⊢
    nlinarith [hinv]
  rw [hderiv]
  simpa [iteratedFDeriv_one_apply] using hbase.trans hrough

/-- The exponent in the source comparison of the fast spatial and slow time
scales is positive. -/
theorem q_minus_time_exponent_pos {β : ℝ}
    (hβ : 1 < β) (hβ' : β < 4 / 3) :
    0 < q β - (2 - β + 4 * delta β) := by
  have hq := Infra.Ingredients.one_lt_q hβ hβ'
  have hd := Infra.Ingredients.delta_eq_q_fraction hβ hβ'
  have hβq : β = 4 * q β / (4 * q β - 1) := by
    have hqval := Infra.Ingredients.q_eq_beta_div_four_sub_one hβ
    have hmul : q β * (4 * (β - 1)) = β := by
      rw [hqval]
      field_simp [ne_of_gt (sub_pos.mpr hβ)]
    have hden : 4 * q β - 1 ≠ 0 := by linarith
    have hnum : β * (4 * q β - 1) = 4 * q β := by nlinarith [hmul]
    calc
      β = (4 * q β) / (4 * q β - 1) := by
        field_simp [hden]
        exact hnum
      _ = 4 * q β / (4 * q β - 1) := rfl
  have h2 : 2 - β = 2 - 4 * q β / (4 * q β - 1) :=
    congrArg (fun z : ℝ => 2 - z) hβq
  have hden₁ : 0 < 4 * q β - 1 := by linarith
  have hden₂ : 0 < q β + 1 := by linarith
  have hden₁' : -1 + q β * 4 ≠ 0 := by linarith
  have hnum : 0 < 4 * q β ^ 3 - 2 * q β ^ 2 - q β + 1 := by
    let r := q β - 1
    have hr : 0 < r := by dsimp [r]; linarith
    have heq : 4 * q β ^ 3 - 2 * q β ^ 2 - q β + 1 =
        2 + 7 * r + 10 * r ^ 2 + 4 * r ^ 3 := by
      dsimp [r]
      ring
    rw [heq]
    positivity
  have hform : q β - (2 - 4 * q β / (4 * q β - 1) +
      4 * ((q β - 1) ^ 2 / (4 * (q β + 1) * (4 * q β - 1)))) =
      (4 * q β ^ 3 - 2 * q β ^ 2 - q β + 1) /
        ((q β + 1) * (4 * q β - 1)) := by
    apply (eq_div_iff (ne_of_gt (mul_pos hden₂ hden₁))).2
    simp only [div_eq_mul_inv]
    field_simp [hden₁', ne_of_gt hden₂,
      ne_of_gt (show (0 : ℝ) < 4 by norm_num)]
    have hinv : (-1 + q β * 4) * (-1 + q β * 4)⁻¹ = 1 := by
      field_simp [hden₁']
    linear_combination -(1 - 6 * q β - 3 * q β ^ 2) * hinv
  have heq : q β - (2 - β + 4 * delta β) =
      (4 * q β ^ 3 - 2 * q β ^ 2 - q β + 1) /
        ((q β + 1) * (4 * q β - 1)) := by
    calc
      q β - (2 - β + 4 * delta β) =
          q β - (2 - β + 4 *
            ((q β - 1) ^ 2 / (4 * (q β + 1) * (4 * q β - 1)))) := by rw [hd]
      _ = q β - (2 - 4 * q β / (4 * q β - 1) + 4 *
            ((q β - 1) ^ 2 / (4 * (q β + 1) * (4 * q β - 1)))) := by rw [h2]
      _ = _ := hform
  rw [heq]
  exact div_pos hnum (mul_pos hden₂ hden₁)

theorem epsilon_div_tau_le_constant {β : ℝ} {I : Ingredients β}
    (m : ℕ) (hm : 1 ≤ m) :
    epsilon β I.Λ m / tau β I.Λ m ≤
      2 ^ 33 * (1 + Infra.Ingredients.supergeoConstant β) := by
  have he : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have he1 : epsilon β I.Λ (m - 1) ≤ 1 :=
    Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hq := q_minus_time_exponent_pos I.one_lt_beta I.beta_lt
  let E := 2 - β + 4 * delta β
  have hpow : epsilon β I.Λ (m - 1) ^ q β ≤
      epsilon β I.Λ (m - 1) ^ E :=
    Real.rpow_le_rpow_of_exponent_ge he he1 (by dsimp [E]; linarith)
  have hS : 0 ≤ Infra.Ingredients.supergeoConstant β := by
    have hq : 0 < q β := lt_trans zero_lt_one
      (Infra.Ingredients.one_lt_q I.one_lt_beta I.beta_lt)
    dsimp [Infra.Ingredients.supergeoConstant]
    positivity
  have hfactor : 1 + Infra.Ingredients.supergeoConstant β *
      epsilon β I.Λ (m - 1) ≤ 1 + Infra.Ingredients.supergeoConstant β := by
    nlinarith [mul_nonneg hS (sub_nonneg.mpr he1)]
  have heUpper : epsilon β I.Λ m ≤
      (1 + Infra.Ingredients.supergeoConstant β) *
        epsilon β I.Λ (m - 1) ^ E := by
    by_cases hmone : m = 1
    · subst m
      have hε := Infra.Construction.epsilon_le_one
        I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := 1)
      simpa [epsilon] using (show epsilon β I.Λ 1 ≤
        (1 + Infra.Ingredients.supergeoConstant β) * 1 by
          nlinarith [hε, hS])
    · have hm' : 1 ≤ m - 1 := by omega
      have hsuper := Infra.Ingredients.epsilon_supergeo
        I.one_lt_beta I.beta_lt I.two_pow_seven_le hm'
      have hstep : epsilon β I.Λ m ≤
          (1 + Infra.Ingredients.supergeoConstant β *
            epsilon β I.Λ (m - 1)) * epsilon β I.Λ (m - 1) ^ q β := by
        simpa [Nat.sub_add_cancel hm] using hsuper.2
      calc
        epsilon β I.Λ m ≤
            (1 + Infra.Ingredients.supergeoConstant β *
              epsilon β I.Λ (m - 1)) * epsilon β I.Λ (m - 1) ^ q β := hstep
        _ ≤ (1 + Infra.Ingredients.supergeoConstant β) *
            epsilon β I.Λ (m - 1) ^ q β :=
          mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg he.le _)
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  have htau := (Infra.Ingredients.tau_bounds
    I.one_lt_beta I.beta_lt I.two_pow_seven_le hm).1
  have hτ : 0 < tau β I.Λ m :=
    Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  apply (div_le_iff₀ hτ).2
  calc
    epsilon β I.Λ m ≤
        (1 + Infra.Ingredients.supergeoConstant β) *
          epsilon β I.Λ (m - 1) ^ E := heUpper
    _ = (2 : ℝ) ^ 33 * (1 + Infra.Ingredients.supergeoConstant β) *
          ((2 : ℝ) ^ (-33 : ℤ) * epsilon β I.Λ (m - 1) ^ E) := by ring_nf
    _ ≤ 2 ^ 33 * (1 + Infra.Ingredients.supergeoConstant β) *
          tau β I.Λ m := by
          exact mul_le_mul_of_nonneg_left htau
            (mul_nonneg (by positivity) (by linarith [hS]))

theorem tau_le_tauP {β : ℝ} {I : Ingredients β}
    (m : ℕ) (hm : 1 ≤ m) : tau β I.Λ m ≤ tauP β I.Λ m := by
  have hτ : 0 < tau β I.Λ m :=
    Infra.Ingredients.tau_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hfactor : 1 ≤ Infra.Ingredients.tauCellFactor β I.Λ m := by
    have hceil : 0 ≤
        (⌈epsilon β I.Λ (m - 1) ^ (-delta β)⌉₊ : ℕ) := Nat.cast_nonneg _
    unfold Infra.Ingredients.tauCellFactor
    nlinarith
  rw [Infra.Ingredients.tauP_eq_cellFactor_mul_tau hm]
  calc
    tau β I.Λ m = 1 * tau β I.Λ m := by ring
    _ ≤ Infra.Ingredients.tauCellFactor β I.Λ m * tau β I.Λ m :=
      mul_le_mul_of_nonneg_right hfactor hτ.le

/-- Rotate a spatial differential to form the velocity of a time increment. -/
def timeIncrementRotate (L : Vec 2 →L[ℝ] ℝ) : Vec 2 :=
  fun i => if i = 0 then -L (basisVec 1) else L (basisVec 0)

theorem timeIncrementRotate_zero :
    timeIncrementRotate (0 : Vec 2 →L[ℝ] ℝ) = 0 := by
  ext i
  fin_cases i <;> simp [timeIncrementRotate]

theorem timeIncrement_vec_decomp (v : Vec 2) :
    v = v 0 • basisVec 0 + v 1 • basisVec 1 := by
  ext i
  fin_cases i <;> simp [basisVec]

theorem timeIncrement_vec_norm_le_coords (v : Vec 2) :
    ‖v‖ ≤ |v 0| + |v 1| := by
  have h0 : ‖basisVec (0 : Fin 2)‖ = 1 := by
    simp [basisVec, Pi.norm_single]
  have h1 : ‖basisVec (1 : Fin 2)‖ = 1 := by
    simp [basisVec, Pi.norm_single]
  have hdecomp := timeIncrement_vec_decomp v
  calc
    ‖v‖ = ‖v 0 • basisVec 0 + v 1 • basisVec 1‖ := congrArg norm hdecomp
    _ ≤
        ‖v 0 • basisVec 0‖ + ‖v 1 • basisVec 1‖ := norm_add_le _ _
    _ = |v 0| + |v 1| := by
      rw [norm_smul, h0, norm_smul, h1]
      simp [Real.norm_eq_abs]

theorem streamVel_eq_timeIncrementRotate
    (φ : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    streamVel φ t x = timeIncrementRotate (fderiv ℝ (φ t) x) := by
  ext i
  fin_cases i <;>
    simp [streamVel, timeIncrementRotate, spaceGrad, sigmaMat, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

theorem timeIncrementRotate_norm_le (L : Vec 2 →L[ℝ] ℝ) :
    ‖timeIncrementRotate L‖ ≤ 2 * ‖L‖ := by
  have h0 := L.le_opNorm (basisVec 1)
  have h1 := L.le_opNorm (basisVec 0)
  have hb0 : ‖basisVec (0 : Fin 2)‖ = 1 := by simp [basisVec, Pi.norm_single]
  have hb1 : ‖basisVec (1 : Fin 2)‖ = 1 := by simp [basisVec, Pi.norm_single]
  calc
    ‖timeIncrementRotate L‖ ≤
        |timeIncrementRotate L 0| + |timeIncrementRotate L 1| :=
          timeIncrement_vec_norm_le_coords _
    _ ≤ ‖L‖ + ‖L‖ := by
      have h0' : ‖L (basisVec 1)‖ ≤ ‖L‖ := by simpa [hb1] using h0
      have h1' : ‖L (basisVec 0)‖ ≤ ‖L‖ := by simpa [hb0] using h1
      simpa [timeIncrementRotate] using add_le_add h0' h1'
    _ = 2 * ‖L‖ := by ring

theorem timeIncrement_clm_norm_le_two_basis
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : Vec 2 →L[ℝ] F} {B : ℝ} (hB : 0 ≤ B)
    (h0 : ‖L (basisVec 0)‖ ≤ B) (h1 : ‖L (basisVec 1)‖ ≤ B) :
    ‖L‖ ≤ 2 * B := by
  apply L.opNorm_le_bound (by positivity)
  intro v
  have hv : v = v 0 • basisVec 0 + v 1 • basisVec 1 := by
    ext i
    fin_cases i <;> simp [basisVec]
  have hmap : L v = v 0 • L (basisVec 0) + v 1 • L (basisVec 1) := by
    calc
      L v = L (v 0 • basisVec 0 + v 1 • basisVec 1) := congrArg L hv
      _ = v 0 • L (basisVec 0) + v 1 • L (basisVec 1) := by simp
  calc
    ‖L v‖ = ‖v 0 • L (basisVec 0) + v 1 • L (basisVec 1)‖ := by rw [hmap]
    _ ≤
        ‖v 0 • L (basisVec 0)‖ + ‖v 1 • L (basisVec 1)‖ := norm_add_le _ _
    _ ≤ |v 0| * B + |v 1| * B := by
      rw [norm_smul, Real.norm_eq_abs, norm_smul, Real.norm_eq_abs]
      exact add_le_add (mul_le_mul_of_nonneg_left h0 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
    _ ≤ (‖v‖ + ‖v‖) * B := by
      have hv0 : |v 0| ≤ ‖v‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm v (0 : Fin 2)
      have hv1 : |v 1| ≤ ‖v‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm v (1 : Fin 2)
      nlinarith [mul_le_mul_of_nonneg_right hv0 hB,
        mul_le_mul_of_nonneg_right hv1 hB]
    _ = 2 * B * ‖v‖ := by ring

theorem timeIncrementSlice_contDiff {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ)
    (m : ℕ) (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (Φ m t) := by
  have hφ := (streamSeq_isAdmissible hseq m).1
  exact hφ.comp (contDiff_const.prodMk contDiff_id)

theorem stream_member_velocity_bound {β C : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ)
    (hreg : StreamRegularityBounds C I Φ) (m : ℕ) (t : ℝ) (x : Vec 2) :
    ‖streamVel (Φ m) t x‖ ≤ 2 * (|C| + 1) ^ 2 := by
  by_cases hm : 1 ≤ m
  · by_cases hC : 0 < C
    · let e := epsilon β I.Λ m
      let R := C * e⁻¹
      have he : 0 < e := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
        I.two_pow_seven_le
      have hR : 0 < R := by dsimp [R, e]; positivity
      have hB : 0 ≤ C * e := by positivity
      have hf := timeIncrementSlice_contDiff hseq m t
      have hbar : barNorm 1 R (Φ m t) ≤ ENNReal.ofReal (C * e) := by
        simpa [R, e] using (hreg m hm t).2.2 1 (by omega)
      have h0 := barNorm_iterated_pointwise (f := Φ m t)
        (fun _ : Fin 1 => (0 : Fin 2))
        (continuous_iteratedCoordinate hf (fun _ => (0 : Fin 2))) hR hB hbar x
      have h1 := barNorm_iterated_pointwise (f := Φ m t)
        (fun _ : Fin 1 => (1 : Fin 2))
        (continuous_iteratedCoordinate hf (fun _ => (1 : Fin 2))) hR hB hbar x
      have hcoord0 : ‖fderiv ℝ (Φ m t) x (basisVec 0)‖ ≤
          (C * e) / (4 * R⁻¹) := by
        norm_num [iteratedFDeriv_one_apply, Nat.factorial] at h0 ⊢
        exact h0
      have hcoord1 : ‖fderiv ℝ (Φ m t) x (basisVec 1)‖ ≤
          (C * e) / (4 * R⁻¹) := by
        norm_num [iteratedFDeriv_one_apply, Nat.factorial] at h1 ⊢
        exact h1
      have hscale : (C * e) / (4 * R⁻¹) = C ^ 2 / 4 := by
        dsimp [R, e]
        field_simp [ne_of_gt hC, he.ne']
        ring_nf
        simpa [mul_comm] using mul_inv_cancel₀ he.ne'
      have hcoord0' : ‖fderiv ℝ (Φ m t) x (basisVec 0)‖ ≤ C ^ 2 / 4 :=
        calc
          _ ≤ (C * e) / (4 * R⁻¹) := hcoord0
          _ = C ^ 2 / 4 := hscale
      have hcoord1' : ‖fderiv ℝ (Φ m t) x (basisVec 1)‖ ≤ C ^ 2 / 4 :=
        calc
          _ ≤ (C * e) / (4 * R⁻¹) := hcoord1
          _ = C ^ 2 / 4 := hscale
      have hderiv : ‖fderiv ℝ (Φ m t) x‖ ≤ C ^ 2 / 2 := by
        have hh := timeIncrement_clm_norm_le_two_basis (by positivity)
          hcoord0' hcoord1'
        nlinarith
      calc
        ‖streamVel (Φ m) t x‖ ≤ 2 * ‖fderiv ℝ (Φ m t) x‖ := by
          rw [streamVel_eq_timeIncrementRotate]
          exact timeIncrementRotate_norm_le _
        _ ≤ C ^ 2 := by nlinarith [hderiv]
        _ ≤ 2 * (|C| + 1) ^ 2 := by
          rw [abs_of_pos hC]
          nlinarith [sq_nonneg C]
    · have hCnonpos : C ≤ 0 := le_of_not_gt hC
      have hbar : barNorm 0 (C * (epsilon β I.Λ m)⁻¹) (Φ m t) ≤ 0 := by
        have h := (hreg m hm t).2.2 0 (by norm_num)
        simpa [Real.rpow_zero, ENNReal.ofReal_eq_zero.mpr hCnonpos] using h
      have hzero : barNorm 0 (C * (epsilon β I.Λ m)⁻¹) (Φ m t) = 0 :=
        le_antisymm hbar bot_le
      have hfun : Φ m t = 0 := by
        funext y
        have hpt := barNorm_zero_pointwise
          (timeIncrementSlice_contDiff hseq m t).continuous (by norm_num)
          (by simp [hzero] : barNorm 0 (C * (epsilon β I.Λ m)⁻¹) (Φ m t) ≤
            ENNReal.ofReal (0 : ℝ)) y
        exact norm_eq_zero.mp (le_antisymm (by simpa using hpt) (norm_nonneg _))
      have hderiv : fderiv ℝ (Φ m t) x = 0 := by
        rw [hfun]
        simp
      rw [streamVel_eq_timeIncrementRotate, hderiv, timeIncrementRotate_zero]
      simpa using (show (0 : ℝ) ≤ 2 * (|C| + 1) ^ 2 by positivity)
  · have hm0 : m = 0 := by omega
    subst m
    rw [streamVel_eq_timeIncrementRotate]
    have hfun : Φ 0 t = 0 := by
      funext y
      exact congrArg (fun f => f t y) hseq.1
    rw [hfun]
    have hderiv : fderiv ℝ (0 : Vec 2 → ℝ) x = 0 := by simp
    rw [hderiv, timeIncrementRotate_zero]
    simpa using (show (0 : ℝ) ≤ 2 * (|C| + 1) ^ 2 by positivity)

theorem psi_timeIncrement_contDiff {β : ℝ} {I : Ingredients β}
    (m : ℕ) (k : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (psi β I.Λ m k) := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x : Vec 2 => a β I.Λ m * epsilon β I.Λ m ^ 2 *
      psi0 k ((epsilon β I.Λ m)⁻¹ • x))
  have hcoord (j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec 2 => Real.sin (2 * Real.pi * ((epsilon β I.Λ m)⁻¹ • x) j)) := by
    fun_prop
  have hconst : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : Vec 2 => a β I.Λ m * epsilon β I.Λ m ^ 2) := contDiff_const
  by_cases h1 : k % 4 = 1
  · simpa [psi0, h1] using hconst.mul (hcoord 0)
  · by_cases h3 : k % 4 = 3
    · simpa [psi0, h1, h3] using hconst.mul (hcoord 1)
    · simp only [psi0, h1, ↓reduceIte, h3, mul_zero]
      exact contDiff_const

theorem psi_first_partial_timeIncrement_le {β : ℝ} {I : Ingredients β}
    (m : ℕ) (k : ℤ) (i : Fin 2) (x : Vec 2) :
    ‖fderiv ℝ (psi β I.Λ m k) x (basisVec i)‖ ≤
      10 * a β I.Λ m * epsilon β I.Λ m := by
  let e := epsilon β I.Λ m
  let R := 8 * e⁻¹
  have he : 0 < e := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le
  have hR : 0 < R := by dsimp [R, e]; positivity
  have hωR : 2 * Real.pi / e ≤ R := by
    apply (div_le_iff₀ he).2
    dsimp [R]
    field_simp [he.ne']
    nlinarith [Real.pi_lt_four]
  have ha : 0 < a β I.Λ m :=
    Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hA : 0 ≤ 5 * a β I.Λ m * e ^ 2 := by positivity
  have hψ := psi_timeIncrement_contDiff (β := β) (I := I) m k
  have hbar := Infra.Construction.psi_barNorm_le I m k 1 hωR
  have hpoint := barNorm_iterated_pointwise (f := psi β I.Λ m k)
    (fun _ : Fin 1 => i)
    (continuous_iteratedCoordinate hψ (fun _ => i)) hR hA hbar x
  have hraw : ‖fderiv ℝ (psi β I.Λ m k) x (basisVec i)‖ ≤
      (5 * a β I.Λ m * e ^ 2) / (4 * R⁻¹) := by
    norm_num [iteratedFDeriv_one_apply, Nat.factorial] at hpoint ⊢
    exact hpoint
  have hscale : (5 * a β I.Λ m * e ^ 2) / (4 * R⁻¹) =
      10 * a β I.Λ m * e := by
    dsimp [R]
    field_simp [he.ne']
    ring_nf
  calc
    ‖fderiv ℝ (psi β I.Λ m k) x (basisVec i)‖ ≤
        (5 * a β I.Λ m * e ^ 2) / (4 * R⁻¹) := hraw
    _ = 10 * a β I.Λ m * epsilon β I.Λ m := by simpa [e] using hscale

theorem psi_second_partial_timeIncrement_le {β : ℝ} {I : Ingredients β}
    (m : ℕ) (k : ℤ) (J : Fin 2 → Fin 2) (x : Vec 2) :
    ‖iteratedFDeriv ℝ 2 (psi β I.Λ m k) x (fun j => basisVec (J j))‖ ≤
      72 * a β I.Λ m := by
  let e := epsilon β I.Λ m
  let R := 8 * e⁻¹
  have he : 0 < e := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le
  have hR : 0 < R := by dsimp [R, e]; positivity
  have hωR : 2 * Real.pi / e ≤ R := by
    apply (div_le_iff₀ he).2
    dsimp [R]
    field_simp [he.ne']
    nlinarith [Real.pi_lt_four]
  have ha : 0 < a β I.Λ m :=
    Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hA : 0 ≤ 5 * a β I.Λ m * e ^ 2 := by positivity
  have hψ := psi_timeIncrement_contDiff (β := β) (I := I) m k
  have hbar := Infra.Construction.psi_barNorm_le I m k 2 hωR
  have hpoint := barNorm_iterated_pointwise (f := psi β I.Λ m k) J
    (continuous_iteratedCoordinate hψ J) hR hA hbar x
  have hraw : ‖iteratedFDeriv ℝ 2 (psi β I.Λ m k) x
      (fun j => basisVec (J j))‖ ≤
      (5 * a β I.Λ m * e ^ 2) /
        (((2 + 1 : ℝ) ^ 2 / (Nat.factorial 2 : ℝ)) * R⁻¹ ^ 2) := by
    simpa [Nat.factorial] using hpoint
  have hscale :
      (5 * a β I.Λ m * e ^ 2) /
        (((2 + 1 : ℝ) ^ 2 / (Nat.factorial 2 : ℝ)) * R⁻¹ ^ 2) =
      (640 / 9) * a β I.Λ m := by
    dsimp [R]
    field_simp [he.ne']
    ring_nf
  calc
    ‖iteratedFDeriv ℝ 2 (psi β I.Λ m k) x
        (fun j => basisVec (J j))‖ ≤
        (5 * a β I.Λ m * e ^ 2) /
          (((2 + 1 : ℝ) ^ 2 / (Nat.factorial 2 : ℝ)) * R⁻¹ ^ 2) := hraw
    _ = (640 / 9) * a β I.Λ m := hscale
    _ ≤ 72 * a β I.Λ m := by nlinarith [ha]

theorem psi_hessian_apply_timeIncrement_le {β : ℝ} {I : Ingredients β}
    (m : ℕ) (k : ℤ) (y u v : Vec 2) :
    |fderiv ℝ (fderiv ℝ (psi β I.Λ m k)) y u v| ≤
      4 * (72 * a β I.Λ m) * ‖u‖ * ‖v‖ := by
  let H := fderiv ℝ (fderiv ℝ (psi β I.Λ m k)) y
  have hB : 0 ≤ 72 * a β I.Λ m := by
    have ha := Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m)
    positivity
  have hentry (i j : Fin 2) : ‖H (basisVec i) (basisVec j)‖ ≤
      72 * a β I.Λ m := by
    have h := psi_second_partial_timeIncrement_le (β := β) (I := I) m k
      (fun n => if n = 0 then i else j) y
    simpa [H, iteratedFDeriv_two_apply] using h
  have hrow (i : Fin 2) : ‖H (basisVec i)‖ ≤ 2 * (72 * a β I.Λ m) :=
    timeIncrement_clm_norm_le_two_basis hB (hentry i 0) (hentry i 1)
  have hH : ‖H‖ ≤ 4 * (72 * a β I.Λ m) := by
    calc
      ‖H‖ ≤ 2 * (2 * (72 * a β I.Λ m)) :=
        timeIncrement_clm_norm_le_two_basis (mul_nonneg (by norm_num) hB)
          (hrow 0) (hrow 1)
      _ = 4 * (72 * a β I.Λ m) := by ring
  have hEval : ‖H u v‖ ≤ ‖H u‖ * ‖v‖ := (H u).le_opNorm v
  have hFirst : ‖H u‖ ≤ ‖H‖ * ‖u‖ := H.le_opNorm u
  have hAbs : |H u v| = ‖H u v‖ := by rw [Real.norm_eq_abs]
  rw [hAbs]
  calc
    ‖H u v‖ ≤ ‖H u‖ * ‖v‖ := hEval
    _ ≤ (‖H‖ * ‖u‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right hFirst (norm_nonneg _)
    _ ≤ (4 * (72 * a β I.Λ m) * ‖u‖) * ‖v‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hH (norm_nonneg _)) (norm_nonneg _)
    _ = 4 * (72 * a β I.Λ m) * ‖u‖ * ‖v‖ := by ring

theorem composed_flow_jacobian_entry_time_deriv_bound
    {β C Cmat : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} (hflow : FlowBoundsData I Φ hseq Cmat)
    (hreg : StreamRegularityBounds C I Φ)
    {m : ℕ} (hm : 1 ≤ m) (s t : ℝ)
    (ht : |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹)
    (i j : Fin 2) (x : Vec 2) :
    |deriv (fun r => constructionComposedFlowJacobian hseq m s r x
        (basisVec j) i) t| ≤
      Cmat * (epsilon β I.Λ m) ^ (β - 2) +
        2 ^ 15 * (epsilon β I.Λ m)⁻¹ * (2 * (|C| + 1) ^ 2) := by
  let b : ℝ → Vec 2 → Vec 2 := fun r z => streamVel (Φ m) (s + r) z
  let F : ℝ → Vec 2 → ℝ := fun r z =>
    constructionComposedFlowJacobian hseq m s r z (basisVec j) i
  have hdiff : DifferentiableAt ℝ (fun r => F r x) t := by
    exact hflow.material_jacobian_time_diff m hm s t ht i j x
  have hpartial (k : Fin 2) :
      ‖fderiv ℝ (F t) x (basisVec k)‖ ≤
        2 ^ 14 * (epsilon β I.Λ m)⁻¹ := by
    simpa [F] using composed_jacobian_spatial_partial_bound hflow hm s t ht i j k x
  have he : 0 < epsilon β I.Λ m :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hpartialNorm : ‖fderiv ℝ (F t) x‖ ≤
      2 * (2 ^ 14 * (epsilon β I.Λ m)⁻¹) :=
    timeIncrement_clm_norm_le_two_basis
      (mul_nonneg (by positivity) (inv_nonneg.mpr he.le))
      (by simpa [F] using hpartial 0) (by simpa [F] using hpartial 1)
  have hpartialNorm' : ‖fderiv ℝ (F t) x‖ ≤
      2 ^ 14 * (epsilon β I.Λ m)⁻¹ * 2 := by
    calc
      _ ≤ 2 * (2 ^ 14 * (epsilon β I.Λ m)⁻¹) := hpartialNorm
      _ = 2 ^ 14 * (epsilon β I.Λ m)⁻¹ * 2 := by ring
  have hmat0 := hflow.material_jacobian m hm s t ht 0 1 (by
      exact Nat.le_trans (by norm_num : 1 ≤ 256)
        (Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt))
    i j x (fun z : Fin 0 => Fin.elim0 z)
  have hmat' : ‖constructionMaterialDerivative b F t x‖ ≤
      Cmat * (epsilon β I.Λ m) ^ (β - 2) := by
    simpa [b, F, constructionMaterialIterate,
      constructionMaterialDerivative, iteratedFDeriv_zero_apply,
      Real.rpow_one] using hmat0
  have hmat : |constructionMaterialDerivative b F t x| ≤
      Cmat * (epsilon β I.Λ m) ^ (β - 2) := by
    simpa [Real.norm_eq_abs] using hmat'
  have hvel := stream_member_velocity_bound hseq hreg m (s + t) x
  have htransportTerm :
      |fderiv ℝ (F t) x (b t x)| ≤
        (2 ^ 14 * (epsilon β I.Λ m)⁻¹ * 2) *
          (2 * (|C| + 1) ^ 2) := by
    calc
      |fderiv ℝ (F t) x (b t x)| =
          ‖fderiv ℝ (F t) x (b t x)‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖fderiv ℝ (F t) x‖ * ‖b t x‖ :=
        (fderiv ℝ (F t) x).le_opNorm _
      _ ≤ (2 ^ 14 * (epsilon β I.Λ m)⁻¹ * 2) *
          (2 * (|C| + 1) ^ 2) := by
        exact mul_le_mul hpartialNorm' hvel (norm_nonneg _) (by positivity)
  have hmaterialEq : constructionMaterialDerivative b F t x =
      deriv (fun r => F r x) t + fderiv ℝ (F t) x (b t x) := rfl
  calc
    |deriv (fun r => F r x) t| =
        |constructionMaterialDerivative b F t x -
          fderiv ℝ (F t) x (b t x)| := by rw [hmaterialEq]; ring_nf
    _ ≤ |constructionMaterialDerivative b F t x| +
        |fderiv ℝ (F t) x (b t x)| := abs_sub _ _
    _ ≤ Cmat * (epsilon β I.Λ m) ^ (β - 2) +
        (2 ^ 14 * (epsilon β I.Λ m)⁻¹ * 2) *
          (2 * (|C| + 1) ^ 2) := add_le_add hmat htransportTerm
    _ = Cmat * (epsilon β I.Λ m) ^ (β - 2) +
        2 ^ 15 * (epsilon β I.Λ m)⁻¹ * (2 * (|C| + 1) ^ 2) := by ring

theorem inverse_column_time_derivative_bound
    {K : ℝ} (t : ℝ)
    (G D : ℝ → Vec 2 →L[ℝ] Vec 2)
    (gdot ddot : Fin 2 → Vec 2)
    (hK : 0 ≤ K)
    (hGclose : ‖G t - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1 / 4)
    (hDnorm : ‖D t‖ ≤ 2)
    (hcomp : ∀ r, (G r).comp (D r) = ContinuousLinearMap.id ℝ (Vec 2))
    (hGdiff : ∀ j, HasDerivAt (fun r => G r (basisVec j)) (gdot j) t)
    (hDdiff : ∀ j, HasDerivAt (fun r => D r (basisVec j)) (ddot j) t)
    (hGdot : ∀ j, ‖gdot j‖ ≤ K) (j : Fin 2) :
    ‖ddot j‖ ≤ 8 * K := by
  let g0 : ℝ → Vec 2 := fun r => G r (basisVec 0)
  let g1 : ℝ → Vec 2 := fun r => G r (basisVec 1)
  let d : ℝ → Vec 2 := fun r => D r (basisVec j)
  let c0 : ℝ → ℝ := fun r => d r 0
  let c1 : ℝ → ℝ := fun r => d r 1
  let H : ℝ → Vec 2 := fun r => c0 r • g0 r + c1 r • g1 r
  have hg0 := hGdiff 0
  have hg1 := hGdiff 1
  have hd := hDdiff j
  have hc0 : HasDerivAt c0 (ddot j 0) t := (hasDerivAt_pi.mp hd) 0
  have hc1 : HasDerivAt c1 (ddot j 1) t := (hasDerivAt_pi.mp hd) 1
  have hH : HasDerivAt H
      (c0 t • gdot 0 + ddot j 0 • g0 t +
        (c1 t • gdot 1 + ddot j 1 • g1 t)) t := by
    have h0 := hc0.smul hg0
    have h1 := hc1.smul hg1
    dsimp [H, g0, g1]
    exact h0.add h1
  have hrep (r : ℝ) : H r = G r (D r (basisVec j)) := by
    dsimp [H, c0, c1, d, g0, g1]
    rw [timeIncrement_vec_decomp (D r (basisVec j))]
    simp
  have hval (r : ℝ) : H r = basisVec j := by
    rw [hrep r]
    have hh := congrArg (fun L : Vec 2 →L[ℝ] Vec 2 => L (basisVec j)) (hcomp r)
    simpa using hh
  have hHconst := hH.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => (hval r).symm)
  have hzero :
      c0 t • gdot 0 + ddot j 0 • g0 t +
        (c1 t • gdot 1 + ddot j 1 • g1 t) = 0 := by
    have hz := hHconst.deriv
    simpa using hz.symm
  have hGrep : G t (ddot j) =
      ddot j 0 • G t (basisVec 0) + ddot j 1 • G t (basisVec 1) := by
    rw [timeIncrement_vec_decomp (ddot j)]
    simp
  have hsum : G t (ddot j) +
      (D t (basisVec j) 0 • gdot 0 + D t (basisVec j) 1 • gdot 1) = 0 := by
    simpa [c0, c1, d, g0, g1, hGrep,
      add_assoc, add_comm, add_left_comm] using hzero
  have hGd : G t (ddot j) =
      -(D t (basisVec j) 0 • gdot 0 + D t (basisVec j) 1 • gdot 1) :=
    eq_neg_iff_add_eq_zero.mpr hsum
  have hdcol : ‖D t (basisVec j)‖ ≤ 2 := by
    have hbasis : ‖basisVec j‖ = 1 := by
      fin_cases j <;> simp [basisVec, Pi.norm_single]
    calc
      ‖D t (basisVec j)‖ ≤ ‖D t‖ * ‖basisVec j‖ := (D t).le_opNorm _
      _ = ‖D t‖ := by rw [hbasis, mul_one]
      _ ≤ 2 := hDnorm
  have hc0bound : |D t (basisVec j) 0| ≤ 2 := by
    have h := norm_le_pi_norm (D t (basisVec j)) (0 : Fin 2)
    have h' : |D t (basisVec j) 0| ≤ ‖D t (basisVec j)‖ := by
      simpa [Real.norm_eq_abs] using h
    exact h'.trans hdcol
  have hc1bound : |D t (basisVec j) 1| ≤ 2 := by
    have h := norm_le_pi_norm (D t (basisVec j)) (1 : Fin 2)
    have h' : |D t (basisVec j) 1| ≤ ‖D t (basisVec j)‖ := by
      simpa [Real.norm_eq_abs] using h
    exact h'.trans hdcol
  have hprod :
      ‖D t (basisVec j) 0 • gdot 0 + D t (basisVec j) 1 • gdot 1‖ ≤ 4 * K := by
    calc
      _ ≤ ‖D t (basisVec j) 0 • gdot 0‖ +
          ‖D t (basisVec j) 1 • gdot 1‖ := norm_add_le _ _
      _ = |D t (basisVec j) 0| * ‖gdot 0‖ +
          |D t (basisVec j) 1| * ‖gdot 1‖ := by
        rw [norm_smul, Real.norm_eq_abs, norm_smul, Real.norm_eq_abs]
      _ ≤ 2 * K + 2 * K := by
        exact add_le_add
          (mul_le_mul_of_nonneg hc0bound (hGdot 0) (abs_nonneg _) hK)
          (mul_le_mul_of_nonneg hc1bound (hGdot 1) (abs_nonneg _) hK)
      _ = 4 * K := by ring
  have hlin : ddot j =
      (ContinuousLinearMap.id ℝ (Vec 2) - G t) (ddot j) + G t (ddot j) := by
    ext i
    simp
  have hsubnorm :
      ‖ContinuousLinearMap.id ℝ (Vec 2) - G t‖ =
        ‖G t - ContinuousLinearMap.id ℝ (Vec 2)‖ := by
    rw [show ContinuousLinearMap.id ℝ (Vec 2) - G t =
        -(G t - ContinuousLinearMap.id ℝ (Vec 2)) by abel, norm_neg]
  have hlower : ‖ddot j‖ ≤ (1 / 4) * ‖ddot j‖ + ‖G t (ddot j)‖ := by
    calc
      ‖ddot j‖ =
          ‖(ContinuousLinearMap.id ℝ (Vec 2) - G t) (ddot j) + G t (ddot j)‖ := by
            rw [← hlin]
      _ ≤ ‖(ContinuousLinearMap.id ℝ (Vec 2) - G t) (ddot j)‖ +
          ‖G t (ddot j)‖ := norm_add_le _ _
      _ ≤ ‖ContinuousLinearMap.id ℝ (Vec 2) - G t‖ * ‖ddot j‖ +
          ‖G t (ddot j)‖ := by
        exact add_le_add ((ContinuousLinearMap.id ℝ (Vec 2) - G t).le_opNorm _)
          le_rfl
      _ ≤ (1 / 4) * ‖ddot j‖ + ‖G t (ddot j)‖ := by
        gcongr
        rw [hsubnorm]
        exact hGclose
  have hGnorm : ‖G t (ddot j)‖ ≤ 4 * K := by
    rw [hGd, norm_neg]
    exact hprod
  nlinarith [hlower, hGnorm, hK]

theorem constructionFlowInvJacobian_entry_continuous
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (m : ℕ) (s t : ℝ) (i j : Fin 2) :
    Continuous (fun x =>
      constructionFlowInvJacobian hseq m t s x (basisVec j) i) := by
  let hφ := streamSeq_isAdmissible hseq m
  let b : ℝ → Vec 2 → Vec 2 := streamVel (Φ m)
  have hb : Infra.Flow.SmoothPeriodicField b :=
    Infra.Construction.smoothPeriodic_streamVel hφ
  have hL := hφ.vel_lipschitz
  have hX : IsFlow b (constructionFlow hseq m) := by
    dsimp [b, constructionFlow]
    exact flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  have hY : ContDiff ℝ 1
      (fun x => constructionFlowInv hseq m (s + t) x s) := by
    simpa [constructionFlowInv, constructionFlow, flowInv, b] using
      Infra.Flow.flow_spatial_contDiff_one hb hX (s + t) s
  have hderiv := hY.continuous_fderiv (by norm_num)
  have hcol : Continuous (fun x =>
      fderiv ℝ (fun y => constructionFlowInv hseq m (s + t) y s) x
        (basisVec j)) := by
    exact hderiv.clm_apply continuous_const
  have hentry : Continuous (fun x =>
      fderiv ℝ (fun y => constructionFlowInv hseq m (s + t) y s) x
        (basisVec j) i) := by fun_prop
  simpa [constructionFlowInvJacobian] using hentry

theorem inverse_flowJacobian_column_bound
    {β Cmat : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} (hflow : FlowBoundsData I Φ hseq Cmat)
    (m : ℕ) (hm : 1 ≤ m) (s t : ℝ)
    (ht : |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹) (x : Vec 2) :
    ‖constructionFlowInvJacobian hseq m t s x‖ ≤ 2 := by
  let e := epsilon β I.Λ m
  let R := 2 ^ 11 * e⁻¹
  let B := 2 ^ 23 * |t| * a β I.Λ m
  let f (jj i : Fin 2) : Vec 2 → ℝ := fun y =>
    (constructionFlowInvJacobian hseq m t s y -
      ContinuousLinearMap.id ℝ (Vec 2)) (basisVec jj) i
  have he : 0 < e := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le
  have hR : 0 < R := by dsimp [R, e]; positivity
  have ha : 0 < a β I.Λ m :=
    Infra.Cutoff.a_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hB : 0 ≤ B := by positivity
  have hbar := hflow.inverse_regbounds m hm s t ht 0
  have hcomponent (jj i : Fin 2) :
      barNorm 0 R (f jj i) ≤ ENNReal.ofReal B := by
    have h := (le_iSup_of_le i (le_iSup_of_le jj le_rfl)).trans hbar
    simpa [f, R, e, B] using h
  have hentry (jj i : Fin 2) : ‖f jj i x‖ ≤ B := by
    have hcontD := constructionFlowInvJacobian_entry_continuous hseq m s t i jj
    have hcont : Continuous (f jj i) := by
      change Continuous (fun y =>
        constructionFlowInvJacobian hseq m t s y (basisVec jj) i -
          (ContinuousLinearMap.id ℝ (Vec 2)) (basisVec jj) i)
      exact hcontD.sub continuous_const
    have hpoint := barNorm_iterated_pointwise (n := 0) (f := f jj i)
      (fun z : Fin 0 => Fin.elim0 z)
      (by simpa [iteratedFDeriv_zero_apply] using hcont) hR hB (hcomponent jj i) x
    simpa using hpoint
  have hcol (jj : Fin 2) :
      ‖(constructionFlowInvJacobian hseq m t s x -
        ContinuousLinearMap.id ℝ (Vec 2)) (basisVec jj)‖ ≤ 2 * B := by
    calc
      _ ≤ |((constructionFlowInvJacobian hseq m t s x -
          ContinuousLinearMap.id ℝ (Vec 2)) (basisVec jj)) 0| +
          |((constructionFlowInvJacobian hseq m t s x -
          ContinuousLinearMap.id ℝ (Vec 2)) (basisVec jj)) 1| :=
            timeIncrement_vec_norm_le_coords _
      _ ≤ B + B := add_le_add (by simpa [f] using hentry jj 0)
          (by simpa [f] using hentry jj 1)
      _ = 2 * B := by ring
  have hdiffNorm : ‖constructionFlowInvJacobian hseq m t s x -
      ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 4 * B := by
    calc
      _ ≤ 2 * (2 * B) := timeIncrement_clm_norm_le_two_basis
        (L := constructionFlowInvJacobian hseq m t s x -
          ContinuousLinearMap.id ℝ (Vec 2)) (B := 2 * B)
        (mul_nonneg (by norm_num) hB) (hcol 0) (hcol 1)
      _ = 4 * B := by ring
  have hBsmall : B ≤ 1 / 4 := by
    dsimp [B]
    calc
      2 ^ 23 * |t| * a β I.Λ m ≤
          2 ^ 23 * (2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹) * a β I.Λ m := by
            calc
              2 ^ 23 * |t| * a β I.Λ m =
                  2 ^ 23 * (|t| * a β I.Λ m) := by ring
              _ ≤ 2 ^ 23 *
                  (2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹ * a β I.Λ m) := by
                    exact mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_right ht (le_of_lt ha))
                      (by positivity)
              _ = 2 ^ 23 *
                  (2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹) * a β I.Λ m := by ring
      _ = 1 / 4 := by field_simp [ha.ne']; norm_num
  calc
    ‖constructionFlowInvJacobian hseq m t s x‖ ≤
        ‖constructionFlowInvJacobian hseq m t s x -
          ContinuousLinearMap.id ℝ (Vec 2)‖ + 1 := by
            have hdecomp : constructionFlowInvJacobian hseq m t s x =
                (constructionFlowInvJacobian hseq m t s x -
                  ContinuousLinearMap.id ℝ (Vec 2)) +
                  ContinuousLinearMap.id ℝ (Vec 2) := by abel
            rw [hdecomp]
            calc
              ‖(constructionFlowInvJacobian hseq m t s x -
                ContinuousLinearMap.id ℝ (Vec 2)) +
                ContinuousLinearMap.id ℝ (Vec 2)‖ ≤
                  ‖constructionFlowInvJacobian hseq m t s x -
                    ContinuousLinearMap.id ℝ (Vec 2)‖ +
                    ‖ContinuousLinearMap.id ℝ (Vec 2)‖ := norm_add_le _ _
              _ = _ := by simp
    _ ≤ 4 * B + 1 := add_le_add hdiffNorm le_rfl
    _ ≤ 2 := by linarith

theorem inverseFlowJacobian_column_time_deriv_bound
    {β C Cmat : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {hseq : IsStreamSeq I Φ} (hflow : FlowBoundsData I Φ hseq Cmat)
    (hreg : StreamRegularityBounds C I Φ) {m : ℕ} (hm : 1 ≤ m)
    (s t : ℝ) (ht : |t| ≤ 2 ^ (-25 : ℤ) * (a β I.Λ m)⁻¹)
    (x : Vec 2) (j : Fin 2) :
    ‖deriv (fun r => constructionFlowInvJacobian hseq m r s x
        (basisVec j)) t‖ ≤
      16 * (Cmat * (epsilon β I.Λ m) ^ (β - 2) +
        2 ^ 15 * (epsilon β I.Λ m)⁻¹ * (2 * (|C| + 1) ^ 2)) := by
  let G : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => constructionComposedFlowJacobian hseq m s r x
  let D : ℝ → Vec 2 →L[ℝ] Vec 2 :=
    fun r => constructionFlowInvJacobian hseq m r s x
  let gdot (jj : Fin 2) : Vec 2 := fun ii =>
    deriv (fun r => G r (basisVec jj) ii) t
  let ddot (jj : Fin 2) : Vec 2 := fun ii =>
    (deriv D t) (basisVec jj) ii
  let K : ℝ := Cmat * (epsilon β I.Λ m) ^ (β - 2) +
    2 ^ 15 * (epsilon β I.Λ m)⁻¹ * (2 * (|C| + 1) ^ 2)
  have hK : 0 ≤ K := by
    have hCmat : 0 < Cmat := lt_of_lt_of_le (by norm_num) hflow.material_constant_ge_one
    have he : 0 < epsilon β I.Λ m :=
      Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
    have hpow : 0 < (epsilon β I.Λ m) ^ (β - 2) :=
      Real.rpow_pos_of_pos he _
    dsimp [K]
    positivity
  have hGdiff (jj : Fin 2) :
      HasDerivAt (fun r => G r (basisVec jj)) (gdot jj) t := by
    apply hasDerivAt_pi.mpr
    intro ii
    have hd := hflow.material_jacobian_time_diff m hm s t ht ii jj x
    exact hd.hasDerivAt
  have hDhas : HasDerivAt D (deriv D t) t :=
    (hflow.inverse_jacobian_time_diff m hm s t x).hasDerivAt
  have hDdiff (jj : Fin 2) :
      HasDerivAt (fun r => D r (basisVec jj)) (ddot jj) t := by
    have hcol := hDhas.clm_apply (hasDerivAt_const t (basisVec jj))
    simpa [D, ddot] using hcol
  have hGdot (jj : Fin 2) : ‖gdot jj‖ ≤ 2 * K := by
    have h0 := composed_flow_jacobian_entry_time_deriv_bound
      hflow hreg hm s t ht 0 jj x
    have h1 := composed_flow_jacobian_entry_time_deriv_bound
      hflow hreg hm s t ht 1 jj x
    have hcoords : |gdot jj 0| ≤ K ∧ |gdot jj 1| ≤ K := by
      constructor <;> simpa [gdot, G, K, Real.norm_eq_abs] using (by assumption : _)
    calc
      ‖gdot jj‖ ≤ |gdot jj 0| + |gdot jj 1| := timeIncrement_vec_norm_le_coords _
      _ ≤ K + K := add_le_add hcoords.1 hcoords.2
      _ = 2 * K := by ring
  have hb : Infra.Flow.SmoothPeriodicField (streamVel (Φ m)) :=
    Infra.Construction.smoothPeriodic_streamVel (streamSeq_isAdmissible hseq m)
  have hφ := streamSeq_isAdmissible hseq m
  have hX : IsFlow (streamVel (Φ m)) (constructionFlow hseq m) := by
    dsimp [constructionFlow]
    exact flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  have hcomp (r : ℝ) : (G r).comp (D r) =
      ContinuousLinearMap.id ℝ (Vec 2) := by
    let F : Vec 2 → Vec 2 := fun y => constructionFlow hseq m (s + r) y s
    let H : Vec 2 → Vec 2 := fun y => constructionFlowInv hseq m (s + r) y s
    obtain ⟨_, _, _, hinv⟩ :=
      Infra.Flow.flow_fixed_time_maps_are_C1_inverses hb hX s (s + r)
    have hmap (y : Vec 2) : F (H y) = y := by
      simpa [F, H, constructionFlow, constructionFlowInv, flowInv] using hinv y
    have hF : HasFDerivAt F (fderiv ℝ F (H x)) (H x) := by
      exact (Infra.Flow.flow_spatial_contDiff_one hb hX s (s + r)
        |>.differentiable (by norm_num) (H x)).hasFDerivAt
    have hH : HasFDerivAt H (fderiv ℝ H x) x := by
      exact (Infra.Flow.flow_spatial_contDiff_one hb hX (s + r) s
        |>.differentiable (by norm_num) x).hasFDerivAt
    have hchain := HasFDerivAt.comp x hF hH
    have hid := hchain.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => (hmap y).symm)
    have hderiv := hid.unique (hasFDerivAt_id x)
    simpa [G, D, F, H, constructionComposedFlowJacobian,
      constructionFlowJacobian, constructionFlowInvJacobian] using hderiv
  have hclose : ‖G t - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1 / 4 := by
    have hcl := hflow.flow_close m hm s t ht
      (constructionFlowInv hseq m (s + t) x s)
    simpa [G, constructionComposedFlowJacobian] using hcl.1.trans hcl.2
  have hDnorm : ‖D t‖ ≤ 2 := by
    simpa [D] using inverse_flowJacobian_column_bound hflow m hm s t ht x
  have hgdot_nonneg : 0 ≤ 2 * K := by positivity
  have hddot := inverse_column_time_derivative_bound t G D gdot ddot
    hgdot_nonneg hclose hDnorm hcomp hGdiff hDdiff hGdot j
  have hresult : ‖ddot j‖ ≤ 16 * K := by
    calc
      ‖ddot j‖ ≤ 8 * (2 * K) := hddot
      _ = 16 * K := by ring
  have hcolEq : ddot j = deriv (fun r => D r (basisVec j)) t :=
    (hDdiff j).deriv.symm
  rw [hcolEq] at hresult
  simpa [D] using hresult

end AVenhance
