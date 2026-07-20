/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.MorseBott.TubularProjection.Defs
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Tubular Neighborhood Projection -- IFT-Based C¹ Regularity

IFT-based proof that the nearest-point projection is C¹ at every point of
the submanifold S.
-/

open Filter Topology Metric NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace PLAcceleratedNesterovLean


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private lemma isInvertible_of_bijective_finiteDimensional
    {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    (L : A →L[ℝ] B) (hL : Function.Bijective L) :
    L.IsInvertible := by
  refine ⟨(LinearEquiv.ofBijective L.toLinearMap ?_).toContinuousLinearEquiv, ?_⟩
  · exact hL
  · ext x
    rfl

-- ════════════════════════════════════════════════════════════════════════════
-- § IFT-based local C¹ regularity of the tubular projection
-- ════════════════════════════════════════════════════════════════════════════

/-! ### Analysis of `fderiv ℝ π x` for `x ∉ S`

At `m ∈ S`, `fderiv ℝ π m = V_m.starProjection` (Property 9). But for
`x ∈ U \ S`, the derivative is **not** simply the orthogonal projection
onto the tangent space at `π(x)`. In chart coordinates at `m = π(x)`:

  `π(y) = m + v*(y − m) + φ(v*(y − m))`

where `v* : E → V` is the IFT solution to the first-order optimality
equation `F(r, v) = 0`. The derivative is:

  `fderiv ℝ π x = (ι_V + ι_{V⊥} ∘ Dφ(v₀)) ∘ Dv*(r₀)`

where `v₀ = v*(x − m)`, `r₀ = x − m`, and `Dv*` is given by the
implicit derivative formula `Dv* = −(∂F/∂v)⁻¹ ∘ (∂F/∂r)`.

At `v₀ = 0` (i.e., `x = m ∈ S`), `Dφ(0) = 0` and `Dv*(0) = proj_V`,
recovering `fderiv ℝ π m = V.starProjection`.

At `v₀ ≠ 0`, `Dφ(v₀) ≠ 0`, and the derivative depends on second-order
geometry (D²φ) of the submanifold. Continuity of `x ↦ fderiv ℝ π x`
follows from the IFT giving C¹ regularity of `v*`.

**Why the IFT is essential:** To determine `fderiv ℝ π x` at `x ∉ S`,
one must solve the optimality equation (which IS the IFT). Composing
`x ↦ π(x) ↦ V_{π(x)} ↦ V_{π(x)}.starProjection` only gives the
derivative on `S`; the IFT extends it to all of `U`. -/

/-- The optimality equation `F` is C¹ when `φ` is C².
This follows because `F` involves `φ`, `fderiv ℝ φ`, and the
continuous linear maps `V.orthogonalProjectionOnto`, `V⊥.orthogonalProjectionOnto`,
and the adjoint operation. Since `φ` is C², `fderiv ℝ φ` is C¹,
and the adjoint is a continuous linear operation. -/
private lemma contDiff_adjoint
    {n : WithTop ℕ∞}
    {F₁ F₂ : Type*}
    [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    [NormedAddCommGroup F₂] [InnerProductSpace ℝ F₂] [FiniteDimensional ℝ F₂] :
    ContDiff ℝ n
      (ContinuousLinearMap.adjoint : (F₁ →L[ℝ] F₂) → (F₂ →L[ℝ] F₁)) :=
  IsBoundedLinearMap.contDiff {
    map_add := fun A B => by
      simp_all
    map_smul := fun c A => by
      simp_all
    bound := ⟨1, one_pos, fun A => by
      simp_all⟩
  }

lemma optimalityEqn_contDiff
    {V : Submodule ℝ E} {φ : V → V.orthogonal}
    (hφ : ContDiff ℝ 2 φ) (m : E) :
    ContDiff ℝ 1 (optimalityEqn φ m) := by
  unfold optimalityEqn
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  -- The residual r - v - φ(v) is C¹ as a function of (r, v)
  have hres : ContDiff ℝ 1 fun p : E × V =>
      p.1 - (V.subtypeL p.2 : E) - (V.orthogonal.subtypeL (φ p.2) : E) :=
    (contDiff_fst.sub (V.subtypeL.contDiff.comp contDiff_snd)).sub
      (V.orthogonal.subtypeL.contDiff.comp (hφ1.comp contDiff_snd))
  -- fderiv ℝ φ is C¹ (since φ is C²)
  have hDφ : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_cast)
  -- The adjoint of (fderiv ℝ φ v) is C¹ in v
  have hDφ_adj : ContDiff ℝ 1 fun v : V =>
      (ContinuousLinearMap.adjoint (fderiv ℝ φ v) : V.orthogonal →L[ℝ] V) :=
    contDiff_adjoint.comp hDφ
  -- Sum: projV(res) + (Dφ(v))†(projW(res))
  exact ((V.orthogonalProjectionOnto : E →L[ℝ] V).contDiff.comp hres).add
    ((hDφ_adj.comp contDiff_snd).clm_apply
      ((V.orthogonal.orthogonalProjectionOnto : E →L[ℝ] V.orthogonal).contDiff.comp hres))

/-- At the base point `(0, 0)`, `∂F/∂v = −Id_V`.

More precisely: `F(r, v) = T_v*(r − v − φ(v))` and at `v = 0`:
  - `T_0 = ι_V` (since `Dφ(0) = 0`), so `T_0* = V.orthogonalProjectionOnto`
  - `∂/∂v [r − v − φ(v)]|_{v=0} = −Id − Dφ(0) = −Id`
  - `∂F/∂v|_{(r,0)} = T_0*(−Id) + [D_v T_v*]·(r − 0 − 0) = −Id_V + ...`

The second term involves `D²φ(0)` contracted with the normal
component of `r`. At `r = 0`, it vanishes, giving `∂F/∂v = −Id_V`.

At general `(r₀, v₀)`:
  `∂F/∂v = −(Id_V + Dφ(v₀)* ∘ Dφ(v₀)) + [D²φ-dependent terms]`

The operator `Id_V + Dφ(v₀)* ∘ Dφ(v₀)` is always positive definite
(≥ Id_V). The D²φ terms are bounded by `‖D²φ‖ · ‖normal distance‖`.
Within the tube (radius < reach), this perturbation is small enough
that `∂F/∂v` remains invertible. -/
lemma optimalityEqn_partial_v_eq_neg_id
    {V : Submodule ℝ E} {φ : V → V.orthogonal}
    (hφC2 : ContDiff ℝ 2 φ) (hφ0 : φ 0 = 0) (hDφ0 : fderiv ℝ φ 0 = 0)
    (m : E) :
    (fderiv ℝ (optimalityEqn φ m) (0, (0 : V))).comp
      (ContinuousLinearMap.inr ℝ E V) =
    -ContinuousLinearMap.id ℝ V := by
  set F' := fderiv ℝ (optimalityEqn φ m) (0, (0 : V))
  have hF_diff : DifferentiableAt ℝ (optimalityEqn φ m) (0, (0 : V)) :=
    (optimalityEqn_contDiff hφC2 m).differentiable one_ne_zero |>.differentiableAt
  have hchain : HasFDerivAt (fun v : V => optimalityEqn φ m ((0 : E), v))
      (F'.comp (ContinuousLinearMap.inr ℝ E V)) 0 :=
    hF_diff.hasFDerivAt.comp (0 : V) (ContinuousLinearMap.inr ℝ E V).hasFDerivAt
  set ιV := V.subtypeL
  set ιW := V.orthogonal.subtypeL
  have hφ_hfd : HasFDerivAt φ (0 : V →L[ℝ] V.orthogonal) 0 := by
    rw [← hDφ0]; exact (hφC2.differentiable two_ne_zero).differentiableAt.hasFDerivAt
  have h_φE : HasFDerivAt (fun v : V => (φ v : E)) (0 : V →L[ℝ] E) 0 := by
    have := ιW.hasFDerivAt.comp (0 : V) hφ_hfd
    rwa [ContinuousLinearMap.comp_zero] at this
  have hres : HasFDerivAt (fun v : V => (0 : E) - (v : E) - (φ v : E)) (-ιV) 0 := by
    have h_vE : HasFDerivAt (fun v : V => (v : E) + (φ v : E)) (ιV : V →L[ℝ] E) 0 := by
      have hιV_hfd : HasFDerivAt (fun v : V => (v : E)) (ιV : V →L[ℝ] E) 0 := by
        simpa [ιV] using ιV.hasFDerivAt
      convert hιV_hfd.add h_φE using 1
      · rfl
      · rfl
      · rfl
      · funext v
        rfl
      · simp_all
    exact h_vE.neg.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => by
      change (0 : E) - (v : E) - (φ v : E) = -((v : E) + (φ v : E)); abel)
  have hterm1 : HasFDerivAt
      (fun v : V => V.orthogonalProjectionOnto ((0 : E) - (v : E) - (φ v : E)))
      (-ContinuousLinearMap.id ℝ V) 0 := by
    have h := (V.orthogonalProjectionOnto : E →L[ℝ] V).hasFDerivAt.comp (0 : V) hres
    have h_comp_eq : (V.orthogonalProjectionOnto : E →L[ℝ] V).comp (-ιV) =
        -ContinuousLinearMap.id ℝ V := by
      ext v
      apply congrArg (Subtype.val (p := (· ∈ V)))
      simp only [ContinuousLinearMap.comp_apply, neg_apply,
        ContinuousLinearMap.id_apply, map_neg]
      congr 1
      exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self v
    rwa [h_comp_eq] at h
  have hDφ_diff : Differentiable ℝ (fderiv ℝ φ) :=
    (by
      have : ContDiff ℝ 1 (fderiv ℝ φ) := hφC2.fderiv_right (by norm_num)
      exact this.differentiable one_ne_zero)
  have hterm2 : HasFDerivAt
      (fun v : V =>
        ((ContinuousLinearMap.adjoint (fderiv ℝ φ v) : V.orthogonal →L[ℝ] V)
          ((V.orthogonal.orthogonalProjectionOnto : E →L[ℝ] V.orthogonal)
            ((0 : E) - (v : E) - (φ v : E)))))
      (0 : V →L[ℝ] V) 0 := by
    have hA : DifferentiableAt ℝ
        (fun v : V => (ContinuousLinearMap.adjoint (fderiv ℝ φ v) :
          V.orthogonal →L[ℝ] V)) 0 :=
      ((contDiff_adjoint (n := 1)).differentiable one_ne_zero |>.comp
        hDφ_diff).differentiableAt
    have hb : HasFDerivAt
        (fun v : V => (V.orthogonal.orthogonalProjectionOnto : E →L[ℝ] V.orthogonal)
          ((0 : E) - (v : E) - (φ v : E)))
        ((V.orthogonal.orthogonalProjectionOnto : E →L[ℝ] V.orthogonal).comp (-ιV)) 0 :=
      (V.orthogonal.orthogonalProjectionOnto : E →L[ℝ] V.orthogonal).hasFDerivAt.comp
        (0 : V) hres
    have hA0 : (ContinuousLinearMap.adjoint (fderiv ℝ φ (0 : V)) :
        V.orthogonal →L[ℝ] V) = 0 := by
      rw [hDφ0]; simp only [map_zero]
    have hb0 : (V.orthogonal.orthogonalProjectionOnto : E →L[ℝ] V.orthogonal)
        ((0 : E) - ((0 : V) : E) - (φ (0 : V) : E)) = 0 := by
      simp only [ZeroMemClass.coe_zero, sub_self, hφ0, map_zero]
    have hprod := hA.hasFDerivAt.clm_apply hb
    simp_all
  have hcombined := hterm1.add hterm2
  simp only [add_zero] at hcombined
  have hdirect : HasFDerivAt (fun v : V => optimalityEqn φ m ((0 : E), v))
      (-ContinuousLinearMap.id ℝ V) 0 := by
    refine hcombined.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => ?_)
    simp only [optimalityEqn, Pi.add_apply]
  exact hchain.unique hdirect

lemma optimalityEqn_partial_v_bijective
    {V : Submodule ℝ E} {φ : V → V.orthogonal}
    (hφC2 : ContDiff ℝ 2 φ) (hφ0 : φ 0 = 0) (hDφ0 : fderiv ℝ φ 0 = 0)
    (m : E) :
    let F' := fderiv ℝ (optimalityEqn φ m) (0, (0 : V))
    Function.Bijective (F'.comp (ContinuousLinearMap.inr ℝ E V)) := by
  intro F'
  rw [optimalityEqn_partial_v_eq_neg_id hφC2 hφ0 hDφ0 m]
  exact ⟨fun a b h => by simpa using h,
    fun y => ⟨-y, by
      simp only [neg_apply,
        ContinuousLinearMap.coe_id', id_eq, neg_neg]⟩⟩


/-- If v' locally minimizes g(v) = ‖r - v↑ - (φ v)↑‖², then F(r, v') = 0. -/
lemma localMin_sq_dist_implies_optimalityEqn
    {V : Submodule ℝ E} {φ : V → V.orthogonal}
    (hφC2 : ContDiff ℝ 2 φ) (m : E) {r : E} {v' : V}
    (h_min : IsLocalMin (fun v : V => ‖r - (v : E) - (φ v : E)‖ ^ 2) v') :
    optimalityEqn φ m (r, v') = 0 := by
  set g : V → ℝ := fun v => ‖r - (v : E) - (φ v : E)‖ ^ 2
  set res : V → E := fun v => r - (v : E) - (φ v : E)
  set ιV := V.subtypeL
  set ιW := V.orthogonal.subtypeL
  set Dφ := fderiv ℝ φ v'
  have hφ_diff : Differentiable ℝ φ := hφC2.differentiable two_ne_zero
  set res' : V →L[ℝ] E := -(ιV + ιW.comp Dφ)
  have hres_fda : HasFDerivAt res res' v' := by
    have h1 : HasFDerivAt (fun v : V => (v : E)) ιV v' := ιV.hasFDerivAt
    have h2 : HasFDerivAt (fun v : V => (φ v : E)) (ιW.comp Dφ) v' :=
      ιW.hasFDerivAt.comp v' (hφ_diff.differentiableAt.hasFDerivAt)
    have h3 := ((hasFDerivAt_const r v').sub h1).sub h2
    have : (0 : V →L[ℝ] E) - ιV - ιW.comp Dφ = res' :=
      ContinuousLinearMap.ext fun w => by
        simp only [zero_sub,
          FunLike.coe_sub,
          ContinuousLinearMap.coe_comp,
          Pi.sub_apply,
          neg_apply,
          Function.comp_apply, neg_add_rev,
          add_apply, res']
        abel
    rwa [this] at h3
  have hg_fda : HasFDerivAt g (2 • (innerSL ℝ (res v')).comp res') v' :=
    hres_fda.norm_sq
  have h_fderiv_zero : fderiv ℝ g v' = 0 := h_min.fderiv_eq_zero
  have h_deriv_eq : (2 • (innerSL ℝ (res v')).comp res') = (0 : V →L[ℝ] ℝ) := by
    rw [← h_fderiv_zero]; exact hg_fda.fderiv.symm
  have h_res_inner : ∀ w : V, @inner ℝ E _ (res v') (res' w) = 0 := by
    intro w
    have hw := ContinuousLinearMap.ext_iff.mp h_deriv_eq w
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
               zero_apply, innerSL_apply_apply] at hw
    rw [two_smul] at hw; linarith
  have h_sum_zero : ∀ w : V,
      @inner ℝ E _ (res v') (w : E) +
      @inner ℝ E _ (res v') ((Dφ w : V.orthogonal) : E) = 0 := by
    intro w
    have := h_res_inner w
    simp only [res', neg_apply, add_apply,
               ContinuousLinearMap.comp_apply] at this
    rw [inner_neg_right, neg_eq_zero, inner_add_right] at this
    exact this
  set F := optimalityEqn φ m (r, v')
  suffices h_F_inner : ∀ w : V, @inner ℝ V _ F w = 0 by
    have := h_F_inner F; rwa [inner_self_eq_zero] at this
  intro w
  change @inner ℝ V _ (V.orthogonalProjectionOnto (res v') +
    Dφ.adjoint (V.orthogonal.orthogonalProjectionOnto (res v'))) w = 0
  rw [inner_add_left]
  have hterm1 : @inner ℝ V _ (V.orthogonalProjectionOnto (res v')) w =
      @inner ℝ E _ (res v') (w : E) :=
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right w (res v')
  have hterm2 : @inner ℝ V _
      (Dφ.adjoint (V.orthogonal.orthogonalProjectionOnto (res v'))) w =
      @inner ℝ E _ (res v') ((Dφ w : V.orthogonal) : E) := by
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (Dφ w) (res v')
  rw [hterm1, hterm2]; exact h_sum_zero w




omit [FiniteDimensional ℝ E] in
/-- `v = 0` is a local minimizer of `‖(x − m) − v − φ(v)‖²` when `π(x) = m`.
    This is because `π(x) = m` is the nearest point in `S` to `x`, and
    for `v` near `0`, the point `m + v + φ(v)` lies on `S` (by the chart),
    so `dist(x, m) ≤ dist(x, m + v + φ(v))`. -/
private lemma nearest_point_isLocalMin {S U : Set E}
    (hTN : IsTubularNeighborhoodOfSubmanifold S U) (hne : S.Nonempty)
    {V : Submodule ℝ E} {φ : V → V.orthogonal}
    (hφC2 : ContDiff ℝ 2 φ) (hφ0 : φ 0 = 0)
    {m : E} {δ : ℝ} (hδ : 0 < δ)
    (hchart : ∀ y ∈ Metric.ball m δ,
      y ∈ S ↔ ∃ v : V, y = m + (v : E) + (φ v : E))
    (x : E) (hx : x ∈ U)
    (hπx : tubularProj hTN hne x = m) :
    IsLocalMin (fun v : V => ‖(x - m) - (v : E) - (φ v : E)‖ ^ 2) 0 := by
  -- The map v ↦ m + v + φ(v) is continuous
  have hcont_pt : Continuous (fun v : V => m + (v : E) + (φ v : E)) :=
    (continuous_const.add V.subtypeL.continuous).add
      (V.orthogonal.subtypeL.continuous.comp hφC2.continuous)
  -- Its preimage of B(m, δ) is a neighborhood of 0
  have h_pre : (fun v : V => m + (v : E) + (φ v : E)) ⁻¹' Metric.ball m δ ∈ 𝓝 (0 : V) :=
    hcont_pt.continuousAt.preimage_mem_nhds (by
      simp only [hφ0, ZeroMemClass.coe_zero, add_zero]
      exact Metric.ball_mem_nhds m hδ)
  rw [IsLocalMin]
  filter_upwards [h_pre] with v hv
  -- m + v + φ(v) ∈ B(m, δ), hence ∈ S by chart
  have hv_S : m + (v : E) + (φ v : E) ∈ S := (hchart _ hv).mpr ⟨v, rfl⟩
  -- Nearest-point optimality: dist(x, m) ≤ dist(x, m + v + φ(v))
  have h_dist_eq : dist x m = Metric.infDist x S := by
    have h := (tubularProj_mem hTN hne x hx).2
    rwa [hπx] at h
  have h_opt : dist x m ≤ dist x (m + (v : E) + (φ v : E)) :=
    h_dist_eq ▸ Metric.infDist_le_dist_of_mem hv_S
  -- Convert to norm inequality
  simp only [ZeroMemClass.coe_zero, sub_zero, hφ0]
  have h1 : ‖x - m‖ ≤ ‖x - m - (v : E) - (φ v : E)‖ := by
    rw [dist_eq_norm] at h_opt
    calc ‖x - m‖ ≤ dist x (m + (v : E) + (φ v : E)) := h_opt
      _ = ‖x - (m + (v : E) + (φ v : E))‖ := dist_eq_norm _ _
      _ = ‖x - m - (v : E) - (φ v : E)‖ := by congr 1; abel
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

/-- For `y ∈ U` with `π(y)` in the chart at `m`, the V-component of
    `π(y) − m` is a local minimizer of the squared distance function. -/
private lemma chart_point_isLocalMin {S U : Set E}
    (hTN : IsTubularNeighborhoodOfSubmanifold S U) (hne : S.Nonempty)
    {V : Submodule ℝ E} {φ : V → V.orthogonal}
    (hφC2 : ContDiff ℝ 2 φ)
    {m : E} {δ : ℝ} (_hδ : 0 < δ)
    (hchart : ∀ z ∈ Metric.ball m δ,
      z ∈ S ↔ ∃ v : V, z = m + (v : E) + (φ v : E))
    (y : E) (hy : y ∈ U) (hπ_ball : tubularProj hTN hne y ∈ Metric.ball m δ) :
    let v' := V.orthogonalProjectionOnto (tubularProj hTN hne y - m)
    IsLocalMin (fun v : V => ‖(y - m) - (v : E) - (φ v : E)‖ ^ 2) v' := by
  intro v'
  -- π(y) ∈ S ∩ B(m, δ), so by chart: π(y) = m + v_0 + φ(v_0) for some v_0
  set πy := tubularProj hTN hne y with hπy_def
  have hπ_S := (tubularProj_mem hTN hne y hy).1
  obtain ⟨v_0, hv0_eq⟩ := (hchart πy hπ_ball).mp hπ_S
  -- v_0 = V.orthogonalProjectionOnto(π(y) - m) = v'
  have hv0_eq_v' : v_0 = v' := by
    have hπ_sub : πy - m = (v_0 : E) + (φ v_0 : E) := by rw [hv0_eq]; abel
    change v_0 = V.orthogonalProjectionOnto (πy - m)
    simp_all
  -- The map v ↦ m + v + φ(v) is continuous
  have hcont_pt : Continuous (fun v : V => m + (v : E) + (φ v : E)) :=
    (continuous_const.add V.subtypeL.continuous).add
      (V.orthogonal.subtypeL.continuous.comp hφC2.continuous)
  -- Preimage of B(m, δ) is a neighborhood of v' (since m + v' + φ(v') = π(y) ∈ B(m, δ))
  have h_pre : (fun v : V => m + (v : E) + (φ v : E)) ⁻¹' Metric.ball m δ ∈ 𝓝 v' := by
    apply hcont_pt.continuousAt.preimage_mem_nhds
    -- Goal: ball m δ ∈ 𝓝 (m + v' + φ(v'))
    -- Since m + v' + φ(v') = m + v_0 + φ(v_0) = π(y) ∈ B(m, δ)
    rw [show m + (v' : E) + (φ v' : E) = πy from by rw [← hv0_eq_v', hv0_eq]]
    exact isOpen_ball.mem_nhds hπ_ball
  rw [IsLocalMin]
  filter_upwards [h_pre] with v hv_ball
  -- m + v + φ(v) ∈ S (by chart)
  have hv_S : m + (v : E) + (φ v : E) ∈ S := (hchart _ hv_ball).mpr ⟨v, rfl⟩
  -- Nearest-point optimality: dist(y, π(y)) ≤ dist(y, m + v + φ(v))
  have h_opt : dist y πy ≤ dist y (m + (v : E) + (φ v : E)) :=
    (tubularProj_mem hTN hne y hy).2 ▸ Metric.infDist_le_dist_of_mem hv_S
  -- ‖(y-m) - v'↑ - (φ v')↑‖ = dist(y, π(y))
  have h_eq : ‖(y - m) - (v' : E) - (φ v' : E)‖ = dist y πy := by
    rw [dist_eq_norm]; congr 1; rw [← hv0_eq_v', hv0_eq]; abel
  -- ‖(y-m) - v↑ - (φ v)↑‖ = dist(y, m + v + φ(v))
  have h_eq2 : ‖(y - m) - (v : E) - (φ v : E)‖ = dist y (m + (v : E) + (φ v : E)) := by
    rw [dist_eq_norm]; congr 1; abel
  calc ‖(y - m) - (v' : E) - (φ v' : E)‖ ^ 2 = dist y πy ^ 2 := by rw [h_eq]
    _ ≤ dist y (m + (v : E) + (φ v : E)) ^ 2 := pow_le_pow_left₀ dist_nonneg h_opt 2
    _ = ‖(y - m) - (v : E) - (φ v : E)‖ ^ 2 := by rw [h_eq2]

/-- For each `m ∈ S`, the nearest-point projection `π` is C¹ at `m`.

    **Proof strategy** (Foote 1984, adapted):
    Apply the IFT at `(0, 0)` where `∂F/∂v = −Id` is bijective by
    `optimalityEqn_partial_v_bijective`. Get a C¹ implicit function `v*`
    near `0`. Use continuity of `π` and IFT uniqueness to show `π = χ`
    near `m`, where `χ(y) = m + v*(y−m) + φ(v*(y−m))` is C¹. -/
lemma tubularProj_contDiffAt_S {S U : Set E}
    (hTN : IsTubularNeighborhoodOfSubmanifold S U) (hne : S.Nonempty)
    (m : E) (hm : m ∈ S) :
    ContDiffAt ℝ 1 (tubularProj hTN hne) m := by
  set π := tubularProj hTN hne with hπ_def
  have hm_U : m ∈ U := hTN.subset hm
  obtain ⟨V, φ, δ, hδ, hφC2, hφ0, hDφ0, hchart⟩ := hTN.submanifold_chart m hm
  have hU_open := U_isOpen hTN
  -- ── Step 1: F is globally C¹ ──
  have hF_C1 : ContDiff ℝ 1 (optimalityEqn φ m) := optimalityEqn_contDiff hφC2 m
  -- ── Step 2: F(0, 0) = 0 ──
  have hF_zero : optimalityEqn φ m (0, (0 : V)) = 0 := by
    simp only [optimalityEqn, hφ0, ZeroMemClass.coe_zero, sub_zero, map_zero, add_zero]
  -- ── Step 3: Build IFT instance at (0, 0) ──
  set F'_0 := fderiv ℝ (optimalityEqn φ m) (0, (0 : V))
  have hF_fda : HasFDerivAt (optimalityEqn φ m) F'_0 (0, (0 : V)) :=
    (hF_C1.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hF_bij : Function.Bijective (F'_0.comp (ContinuousLinearMap.inr ℝ E V)) :=
    optimalityEqn_partial_v_bijective hφC2 hφ0 hDφ0 m
  have hF_cda : ContDiffAt ℝ 1 (optimalityEqn φ m) (0, (0 : V)) := hF_C1.contDiffAt
  have hF_right_inv : (F'_0.comp (ContinuousLinearMap.inr ℝ E V)).IsInvertible :=
    isInvertible_of_bijective_finiteDimensional
      (F'_0.comp (ContinuousLinearMap.inr ℝ E V)) hF_bij
  have hF_partial_inv :
      (fderiv ℝ (optimalityEqn φ m) (0, (0 : V)) ∘L
        ContinuousLinearMap.inr ℝ E V).IsInvertible := by
    rw [hF_fda.fderiv]
    exact hF_right_inv
  -- ── Step 4: IFT gives C¹ implicit function ──
  set v_impl := hF_cda.implicitFunction one_ne_zero hF_partial_inv with hv_impl_def
  set v_star : E → V := fun y => v_impl (y - m) with hv_def
  have hv_star_cd : ContDiffAt ℝ 1 v_star m := by
    change ContDiffAt ℝ 1 (v_impl ∘ (· - m)) m
    have hcd : ContDiffAt ℝ 1 v_impl (m - m) := by
      rw [sub_self, hv_impl_def]
      exact hF_cda.contDiffAt_implicitFunction one_ne_zero hF_partial_inv
    exact hcd.comp (f := fun x => x - m) m (contDiffAt_id.sub contDiffAt_const)
  -- ── Step 5: Chart projection χ is C¹ at m ──
  have hφ1 : ContDiff ℝ 1 φ := hφC2.of_le (by norm_num)
  set χ : E → E := fun y => m + (v_star y : E) + (φ (v_star y) : E) with hχ_def
  have hχ_cd : ContDiffAt ℝ 1 χ m := by
    have hv_E := V.subtypeL.contDiff.contDiffAt.comp m hv_star_cd
    have hφv_E := V.orthogonal.subtypeL.contDiff.contDiffAt.comp m
        (hφ1.contDiffAt.comp m hv_star_cd)
    exact (contDiffAt_const.add hv_E).add hφv_E
  -- ── Step 6: Show π =ᶠ[𝓝 m] χ using IFT uniqueness + continuity ──
  -- π(m) = m since m ∈ S
  have hπ_m : π m = m := tubularProj_fixes_S hTN hne m hm
  -- Continuity of π at m
  have hπ_cont_at : ContinuousAt π m :=
    tubularProj_continuousAt_of_mem hTN hne hm
  -- For y near m: π(y) ∈ B(m, δ) (since π continuous, π(m) = m ∈ B(m, δ))
  have hπ_near_m : ∀ᶠ y in 𝓝 m, π y ∈ Metric.ball m δ := by
    have h1 := hπ_cont_at (Metric.ball_mem_nhds (π m) hδ)
    rwa [hπ_m] at h1
  -- The map y ↦ (y − m, V.orthogonalProjectionOnto(π(y) − m)) tends to (0, 0)
  have h_tend_pair : Tendsto (fun y => (y - m, V.orthogonalProjectionOnto (π y - m)))
      (𝓝 m) (𝓝 (0, (0 : V))) := by
    apply Filter.Tendsto.prodMk_nhds
    · rw [show (0 : E) = m - m from (sub_self m).symm]
      exact tendsto_id.sub tendsto_const_nhds
    · have h_sub_tend : Tendsto (fun y => π y - m) (𝓝 m) (𝓝 (0 : E)) := by
        rw [show (0 : E) = π m - m from by rw [hπ_m]; exact (sub_self m).symm]
        exact hπ_cont_at.sub tendsto_const_nhds
      rw [show (0 : V) = (V.orthogonalProjectionOnto : E →L[ℝ] V) 0 from (map_zero _).symm]
      exact ((V.orthogonalProjectionOnto : E →L[ℝ] V).continuous.tendsto 0).comp h_sub_tend
  -- IFT uniqueness: ∀ᶠ (r,v) near (0, 0), F(r,v) = F(0,0) → impl(r) = v
  have h_ift_uniq :
      ∀ᶠ p in 𝓝 (0, (0 : V)),
        optimalityEqn φ m p = optimalityEqn φ m (0, (0 : V)) ↔ v_impl p.1 = p.2 := by
    rw [hv_impl_def]
    exact hF_cda.eventually_apply_eq_iff_implicitFunction one_ne_zero hF_partial_inv
  -- Pull back through h_tend_pair
  have h_uniq_pulled := h_tend_pair.eventually h_ift_uniq
  -- For y near m with y ∈ U, π(y) in chart: F(y−m, w_y) = 0
  have h_opt_near : ∀ᶠ y in 𝓝 m, y ∈ U → π y ∈ Metric.ball m δ →
      optimalityEqn φ m (y - m, V.orthogonalProjectionOnto (π y - m)) = 0 := by
    exact Eventually.of_forall fun y hy_U hπ_ball =>
      localMin_sq_dist_implies_optimalityEqn hφC2 m
        (chart_point_isLocalMin hTN hne hφC2 hδ hchart y hy_U hπ_ball)
  -- For y near m with y ∈ U, π(y) in chart: π(y) = m + w_y + φ(w_y)
  have h_chart_repr : ∀ᶠ y in 𝓝 m, y ∈ U → π y ∈ Metric.ball m δ →
      π y = m + (V.orthogonalProjectionOnto (π y - m) : E) +
        (φ (V.orthogonalProjectionOnto (π y - m)) : E) := by
    apply Eventually.of_forall
    intro y hy_U hπ_ball
    have hπ_S := (tubularProj_mem hTN hne y hy_U).1
    obtain ⟨v_0, hv0_eq⟩ := (hchart (π y) hπ_ball).mp hπ_S
    have hv0_eq_w : v_0 = V.orthogonalProjectionOnto (π y - m) := by
      have hπ_sub : π y - m = (v_0 : E) + (φ v_0 : E) := by rw [hv0_eq]; abel
      simp_all
    rw [← hv0_eq_w]; exact hv0_eq
  -- Combine: π = χ near m
  have hπ_eq_χ : π =ᶠ[𝓝 m] χ := by
    filter_upwards [hU_open.mem_nhds hm_U, hπ_near_m, h_uniq_pulled,
        h_opt_near, h_chart_repr] with y hy_U hπ_ball h_uniq h_opt h_repr
    set w_y := V.orthogonalProjectionOnto (π y - m) with hw_def
    have h_solve : optimalityEqn φ m (y - m, w_y) = 0 := h_opt hy_U hπ_ball
    have h_eq_base : optimalityEqn φ m (y - m, w_y) =
        optimalityEqn φ m (0, (0 : V)) := by rw [h_solve, hF_zero]
    have h_impl_eq : v_impl (y - m) = w_y := by
      simpa [Prod.fst, Prod.snd] using h_uniq.mp h_eq_base
    have hπ_chart := h_repr hy_U hπ_ball
    change π y = m + (v_star y : E) + (φ (v_star y) : E)
    change π y = m + (v_impl (y - m) : E) + (φ (v_impl (y - m)) : E)
    rw [h_impl_eq]; exact hπ_chart
  -- ── Step 7: Transfer C¹ from χ to π ──
  exact hχ_cd.congr_of_eventuallyEq hπ_eq_χ


end PLAcceleratedNesterovLean
