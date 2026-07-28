/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import LeanPool.CompactSpectral.Topology.WeakHilbertCompact

/-!
# Rayleigh quotient for compact self-adjoint operators

Mathlib’s file `Mathlib.Analysis.InnerProductSpace.Rayleigh` contains the core calculus lemma:
if the quadratic form `x ↦ re ⟪T x, x⟫` attains its maximum/minimum on a sphere, then the
extremiser is an eigenvector and the corresponding eigenvalue is the global `iSup`/`iInf` of the
Rayleigh quotient.

This file supplies the (slightly more elaborate) compact-operator corollary suggested as a TODO in
Mathlib:

*If `T` is compact and self-adjoint on a (real or complex) Hilbert space, then `T` has a nonzero
eigenvector with eigenvalue either `⨆ x, rayleighQuotient T x` or `⨅ x, rayleighQuotient T x`.*

The key technical step is to work on the unit **weak** closed ball, which is compact by
Banach–Alaoglu + Riesz (`CompactSelfAdjoint.Topology.WeakHilbertCompact`), and show that for a
compact operator the quadratic form is continuous on that weakly compact set.
## Main results
- `CompactSelfAdjoint.continuousOn_weakClosedBall_reApplyInnerSelf_of_isCompactOperator`
- `CompactSelfAdjoint.exists_hasEigenvector_iSup_or_iInf_of_isCompactOperator`
-/
namespace CompactSelfAdjoint

open CompactSpectral
open Set Filter Topology
open scoped Topology
open Metric

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The inclusion `E → WeakDual 𝕜 E` obtained by composing the weak-topology inclusion
`E → WeakSpace 𝕜 E` with the Riesz map into the dual. This is a convenient bridge for uniqueness
arguments that need a Hausdorff target (since `WeakDual 𝕜 E` is `T2`). -/
noncomputable def strongToWeakDual : E → WeakDual 𝕜 E :=
  fun x => weakToWeakDual (𝕜 := 𝕜) (E := E) (toWeakSpaceCLM 𝕜 E x)

private lemma eq_of_mapClusterPt_of_tendsto {X : Type*} [TopologicalSpace X] [T2Space X]
    {α : Type*} {l : Filter α} {f : α → X} {y z : X}
    (hy : Tendsto f l (𝓝 y)) (hz : MapClusterPt z l f) : z = y := by
  classical
  by_contra hzy
  have hdisj : Disjoint (𝓝 z) (𝓝 y) := (disjoint_nhds_nhds.2 hzy)
  have hbot : (𝓝 z ⊓ 𝓝 y : Filter X) = ⊥ := by
    simpa [disjoint_iff] using hdisj
  have hmap : (Filter.map f l : Filter X) ≤ 𝓝 y := hy
  have hle : (𝓝 z ⊓ Filter.map f l : Filter X) ≤ (𝓝 z ⊓ 𝓝 y : Filter X) :=
    inf_le_inf_left _ hmap
  have : (𝓝 z ⊓ Filter.map f l : Filter X) = ⊥ := by
    simp_all
  exact (hz.clusterPt.neBot.ne this)
/-- If `T` is compact, then it sends weak convergence on a weakly-closed ball
to norm convergence. -/
lemma tendsto_apply_of_isCompactOperator (T : E →L[𝕜] E) (hTc : IsCompactOperator (T : E → E))
    {α : Type*} {l : Filter α}
    {x : α → WeakSpace 𝕜 E} {x0 : WeakSpace 𝕜 E} {r : ℝ}
    (hx : ∀ᶠ a in l, x a ∈ weakClosedBall (𝕜 := 𝕜) (E := E) r)
    (hweak : Tendsto x l (𝓝 x0)) :
    Tendsto (fun a => T (x a : E)) l (𝓝 (T (x0 : E))) := by
  classical
  let K : Set E := closure (T '' closedBall (α := E) (0 : E) r)
  have hK : IsCompact K := by
    simpa [K] using
      (IsCompactOperator.isCompact_closure_image_closedBall (𝕜₁ := 𝕜) (𝕜₂ := 𝕜)
        (σ₁₂ := RingHom.id 𝕜) (M₁ := E) (M₂ := E) (f := (T : E →ₛₗ[RingHom.id 𝕜] E)) hTc r)
  have hmem : ∀ᶠ a in l, T (x a : E) ∈ K := by
    filter_upwards [hx] with a ha
    have ha' : (x a : E) ∈ closedBall (α := E) (0 : E) r := ha
    exact subset_closure ⟨(x a : E), ha', rfl⟩
  have hcont_stw : Continuous (strongToWeakDual (𝕜 := 𝕜) (E := E)) := by
    have h1 : Continuous (toWeakSpaceCLM 𝕜 E : E → WeakSpace 𝕜 E) :=
      (toWeakSpaceCLM 𝕜 E).continuous
    have h2 : Continuous (weakToWeakDual (𝕜 := 𝕜) (E := E)) :=
      continuous_weakToWeakDual (𝕜 := 𝕜) (E := E)
    exact h2.comp h1
  have hinj : Function.Injective (strongToWeakDual (𝕜 := 𝕜) (E := E)) := by
    intro a b hab
    -- strongToWeakDual is the composition: toDual then toWeakDual, both injective
    unfold strongToWeakDual at hab
    -- hab : weakToWeakDual (toWeakSpaceCLM 𝕜 E a) = weakToWeakDual (toWeakSpaceCLM 𝕜 E b)
    -- weakToWeakDual x = StrongDual.toWeakDual (toDual x), so this gives
    -- StrongDual.toWeakDual (toDual a) = StrongDual.toWeakDual (toDual b)
    simp only [weakToWeakDual, toWeakSpaceCLM, toWeakSpace] at hab
    have h1 := (StrongDual.toWeakDual_inj (𝕜 := 𝕜) (E := E) _ _).mp hab
    exact (InnerProductSpace.toDual 𝕜 E).injective h1
  have huniq :
      ∀ z ∈ K, MapClusterPt z l (fun a => T (x a : E)) → z = T (x0 : E) := by
    intro z hzK hz
    have hz' :
        MapClusterPt (strongToWeakDual (𝕜 := 𝕜) (E := E) z) l
          (fun a => strongToWeakDual (𝕜 := 𝕜) (E := E) (T (x a : E))) := by
      exact hz.continuousAt_comp (hcont_stw.continuousAt)
    have hweakT :
        Tendsto (fun a => (WeakSpace.map T (x a) : WeakSpace 𝕜 E)) l (𝓝 (WeakSpace.map T x0)) :=
      (WeakSpace.map T).continuous.tendsto _ |>.comp hweak
    have hweakDual :
        Tendsto
          (fun a => weakToWeakDual (𝕜 := 𝕜) (E := E) (WeakSpace.map T (x a))) l
          (𝓝 (weakToWeakDual (𝕜 := 𝕜) (E := E) (WeakSpace.map T x0))) :=
      (continuous_weakToWeakDual (𝕜 := 𝕜) (E := E)).tendsto _ |>.comp hweakT
    have htendsto :
        Tendsto
          (fun a => strongToWeakDual (𝕜 := 𝕜) (E := E) (T (x a : E))) l
          (𝓝 (strongToWeakDual (𝕜 := 𝕜) (E := E) (T (x0 : E)))) := by
      exact hweakDual
    have :
        strongToWeakDual (𝕜 := 𝕜) (E := E) z =
          strongToWeakDual (𝕜 := 𝕜) (E := E) (T (x0 : E)) :=
      eq_of_mapClusterPt_of_tendsto (X := WeakDual 𝕜 E) htendsto hz'
    exact hinj this
  exact IsCompact.tendsto_nhds_of_unique_mapClusterPt (s := K) hK hmem huniq
/-- For a compact operator `T`, the quadratic form `x ↦ re ⟪T x, x⟫` is continuous on weakly-compact
closed balls (i.e. `weakClosedBall`). -/
lemma continuousOn_weakClosedBall_reApplyInnerSelf_of_isCompactOperator
    (T : E →L[𝕜] E) (hTc : IsCompactOperator (T : E → E)) (r : ℝ) :
    ContinuousOn (fun x : WeakSpace 𝕜 E => T.reApplyInnerSelf (x : E))
      (weakClosedBall (𝕜 := 𝕜) (E := E) r) := by
  classical
  intro x hx
  let l : Filter (WeakSpace 𝕜 E) := 𝓝[weakClosedBall (𝕜 := 𝕜) (E := E) r] x
  have hx_ball : ∀ᶠ y in l, y ∈ weakClosedBall (𝕜 := 𝕜) (E := E) r := by
    have : weakClosedBall (𝕜 := 𝕜) (E := E) r ∈ l := by
      have :
          weakClosedBall (𝕜 := 𝕜) (E := E) r ∈
            (𝓟 (weakClosedBall (𝕜 := 𝕜) (E := E) r) : Filter (WeakSpace 𝕜 E)) := by
        simp
      simpa [l, nhdsWithin] using (Filter.mem_inf_of_right this)
    simpa [Filter.eventually_iff] using this
  have hid : Tendsto (fun y : WeakSpace 𝕜 E => y) l (𝓝 x) := by
    simp [Filter.Tendsto, l, nhdsWithin]
  have hTt : Tendsto (fun y : WeakSpace 𝕜 E => T (y : E)) l (𝓝 (T (x : E))) := by
    simpa [l] using
      tendsto_apply_of_isCompactOperator (𝕜 := 𝕜) (E := E) T hTc (r := r) hx_ball hid
  have hinner :
      Tendsto (fun y : WeakSpace 𝕜 E => inner 𝕜 (T (y : E)) (y : E)) l
        (𝓝 (inner 𝕜 (T (x : E)) (x : E))) := by
    have hdiff :
        Tendsto (fun y : WeakSpace 𝕜 E =>
            ‖T (y : E) - T (x : E)‖) l (𝓝 (0 : ℝ)) := by
      have h := (hTt.sub (tendsto_const_nhds (x := T (x : E)))).norm
      simpa using h
    have hnorm_inner :
        Tendsto
          (fun y : WeakSpace 𝕜 E =>
            ‖inner 𝕜 (T (y : E) - T (x : E)) (y : E)‖)
          l (𝓝 (0 : ℝ)) := by
      have hrhs :
          Tendsto (fun y : WeakSpace 𝕜 E =>
              ‖T (y : E) - T (x : E)‖ * r) l (𝓝 (0 : ℝ)) := by
        simpa [zero_mul] using (hdiff.mul tendsto_const_nhds)
      refine
        tendsto_of_tendsto_of_tendsto_of_le_of_le'
          (g := fun _ => (0 : ℝ))
          (h := fun y => ‖T (y : E) - T (x : E)‖ * r)
          tendsto_const_nhds hrhs ?_ ?_
      · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
      · filter_upwards [hx_ball] with y hy
        have hy' : ‖(y : E)‖ ≤ r := by
          let ye : E := y
          have hye : ye ∈ closedBall (α := E) (0 : E) r := hy
          exact (mem_closedBall_zero_iff (a := ye) (r := r)).1 hye
        have hle :
            ‖inner 𝕜 (T (y : E) - T (x : E)) (y : E)‖ ≤
              ‖T (y : E) - T (x : E)‖ * r := by
          have hle' :
              ‖inner 𝕜 (T (y : E) - T (x : E)) (y : E)‖ ≤
                ‖T (y : E) - T (x : E)‖ * ‖(y : E)‖ :=
            norm_inner_le_norm _ _
          exact le_trans hle' (by exact mul_le_mul_of_nonneg_left hy' (norm_nonneg _))
        exact hle
    have h1 :
        Tendsto
          (fun y : WeakSpace 𝕜 E =>
            inner 𝕜 (T (y : E) - T (x : E)) (y : E))
          l (𝓝 (0 : 𝕜)) :=
      (tendsto_zero_iff_norm_tendsto_zero).2 hnorm_inner
    have h2 :
        Tendsto (fun y : WeakSpace 𝕜 E => inner 𝕜 (T (x : E)) (y : E)) l
          (𝓝 (inner 𝕜 (T (x : E)) (x : E))) := by
      have hcont :
          Continuous fun y : WeakSpace 𝕜 E =>
            ((InnerProductSpace.toDual 𝕜 E) (T (x : E))) (y : E) := by
        have h := WeakBilin.eval_continuous (B := (topDualPairing 𝕜 E).flip)
          (y := (InnerProductSpace.toDual 𝕜 E) (T (x : E)))
        exact h
      have :
          Tendsto
            (fun y : WeakSpace 𝕜 E =>
              ((InnerProductSpace.toDual 𝕜 E) (T (x : E))) (y : E))
            l
            (𝓝 (((InnerProductSpace.toDual 𝕜 E) (T (x : E))) (x : E))) :=
        (hcont.tendsto x).comp hid
      exact this
    have hadd :
        Tendsto
          (fun y : WeakSpace 𝕜 E =>
            inner 𝕜 (T (y : E) - T (x : E)) (y : E) +
              inner 𝕜 (T (x : E)) (y : E))
          l (𝓝 (0 + inner 𝕜 (T (x : E)) (x : E))) :=
      h1.add h2
    have hsplit :
        (fun y : WeakSpace 𝕜 E => inner 𝕜 (T (y : E)) (y : E)) =
          fun y =>
            inner 𝕜 (T (y : E) - T (x : E)) (y : E) +
              inner 𝕜 (T (x : E)) (y : E) := by
      funext y
      have h : T (y : E) = (T (y : E) - T (x : E)) + T (x : E) := by
        abel
      rw [h]
      simpa using
        (inner_add_left (𝕜 := 𝕜)
          (x := (T (y : E) - T (x : E)))
          (y := T (x : E))
          (z := (y : E)))
    rw [hsplit]
    have := hadd
    rwa [zero_add] at this
  have hre :
      Tendsto
        (fun y : WeakSpace 𝕜 E =>
          RCLike.re (inner 𝕜 (T (y : E)) (y : E)))
        l (𝓝 (RCLike.re (inner 𝕜 (T (x : E)) (x : E)))) :=
    (RCLike.continuous_re.tendsto _).comp hinner
  exact hre
omit [CompleteSpace E] in
/-- An extremum of a positive-2-homogeneous function on the unit weak closed ball must lie on the
unit sphere, provided the extremal value has a definite sign (encoded via a sign `σ`).

This unifies the min/max cases in the spectral theorem: use `σ = -1` for the minimum and `σ = 1`
for the maximum. -/
private lemma extremizer_mem_unit_sphere
    {f : WeakSpace 𝕜 E → ℝ}
    (hf_scale : ∀ (c : 𝕜) (y : WeakSpace 𝕜 E), f (c • y) = ‖c‖ ^ 2 * f y)
    {x : WeakSpace 𝕜 E} (hx_mem : x ∈ weakClosedBall (𝕜 := 𝕜) (E := E) 1)
    {σ : ℝ} (hσ : 0 < σ * f x)
    (hx_extr : ∀ y ∈ weakClosedBall (𝕜 := 𝕜) (E := E) 1, σ * f y ≤ σ * f x) :
    ‖(x : E)‖ = 1 := by
  have hx_norm_le : ‖(x : E)‖ ≤ 1 := by
    let xe : E := x
    have hxe : xe ∈ closedBall (α := E) (0 : E) 1 := hx_mem
    exact (mem_closedBall_zero_iff (a := xe) (r := 1)).1 hxe
  rcases hx_norm_le.eq_or_lt with heq | hlt
  · exact heq
  exfalso
  -- `f 0 = 0` from 2-homogeneity: f (0 • x) = ‖0‖² · f x = 0.
  have hf0 : f 0 = 0 := by simpa [norm_zero, zero_smul, zero_mul] using hf_scale (0 : 𝕜) x
  have hx_ne0 : (x : E) ≠ 0 := by
    intro h
    simp_all
  have hx_pos : 0 < ‖(x : E)‖ := by
    let xe : E := x
    have : xe ≠ 0 := hx_ne0
    exact norm_pos_iff.mpr this
  -- Scale `x` to the unit sphere; the scaled point still lies in `weakClosedBall 1`.
  let c : 𝕜 := ((‖(x : E)‖⁻¹ : ℝ) : 𝕜)
  have hcnorm : ‖c‖ = ‖(x : E)‖⁻¹ := by
    let xe : E := x
    change ‖((‖xe‖⁻¹ : ℝ) : 𝕜)‖ = ‖xe‖⁻¹
    simp
  have hc2_gt : 1 < ‖c‖ ^ 2 := by
    nlinarith [show 1 < ‖c‖ from hcnorm ▸ (one_lt_inv₀ hx_pos).mpr hlt]
  have hz_mem : c • x ∈ weakClosedBall (𝕜 := 𝕜) (E := E) 1 := by
    -- weakClosedBall = Metric.closedBall (α := E) 0 1, and c • x : WeakSpace 𝕜 E := E
    let xe : E := x
    have h : ‖c • xe‖ = 1 := by
      rw [norm_smul]
      have : ‖c‖ = ‖xe‖⁻¹ := by
        change ‖((‖xe‖⁻¹ : ℝ) : 𝕜)‖ = ‖xe‖⁻¹
        simp
      rw [this, inv_mul_cancel₀ (ne_of_gt (norm_pos_iff.mpr hx_ne0))]
    exact (mem_closedBall_zero_iff (a := c • xe) (r := 1)).2 (le_of_eq h)
  -- The scaled value satisfies σ · f(c•x) > σ · f(x), contradicting extremality.
  have hgt : σ * f x < σ * f (c • x) := by
    rw [hf_scale]
    nlinarith [mul_pos (show (0 : ℝ) < ‖c‖ ^ 2 - 1 by linarith) hσ]
  linarith [hx_extr (c • x) hz_mem]

section

variable [Nontrivial E]

omit [Nontrivial E] in
/-- If a self-adjoint operator is nonzero, then its quadratic form `x ↦ re ⟪T x, x⟫` is not
identically zero. -/
lemma exists_reApplyInnerSelf_ne_zero_of_isSelfAdjoint
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (h0 : T ≠ 0) : ∃ x : E, T.reApplyInnerSelf x ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hSym : (T : E →ₗ[𝕜] E).IsSymmetric := IsSelfAdjoint.isSymmetric hT
  have hinner0 : ∀ x : E, inner 𝕜 (T x) x = 0 := by
    intro x
    have hRe : (T.reApplyInnerSelf x : 𝕜) = inner 𝕜 (T x) x := by
      simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using
        (LinearMap.IsSymmetric.coe_re_inner_apply_self (T := (T : E →ₗ[𝕜] E)) hSym x)
    simp_all
  have hinner : ∀ x y : E, inner 𝕜 ((T : E →ₗ[𝕜] E) x) y = 0 := by
    intro x y
    have hpol :=
      LinearMap.IsSymmetric.inner_map_polarization (𝕜 := 𝕜) (E := E) (T := (T : E →ₗ[𝕜] E)) hSym x y
    have hxy : inner 𝕜 ((T : E →ₗ[𝕜] E) (x + y)) (x + y) = 0 := by
      simpa using hinner0 (x + y)
    have hxmy : inner 𝕜 ((T : E →ₗ[𝕜] E) (x - y)) (x - y) = 0 := by
      simpa using hinner0 (x - y)
    have hxIy :
        inner 𝕜 ((T : E →ₗ[𝕜] E) (x + (RCLike.I : 𝕜) • y)) (x + (RCLike.I : 𝕜) • y) = 0 := by
      simpa using hinner0 (x + (RCLike.I : 𝕜) • y)
    have hxmIy :
        inner 𝕜 ((T : E →ₗ[𝕜] E) (x - (RCLike.I : 𝕜) • y)) (x - (RCLike.I : 𝕜) • y) = 0 := by
      simpa using hinner0 (x - (RCLike.I : 𝕜) • y)
    simp_all
  have hTzero : T = 0 := by
    ext x
    have : ∀ v : E, inner 𝕜 v (T x) = 0 := by
      simp_all
    apply ext_inner_left 𝕜
    simp_all
  exact h0 hTzero
/-- Compact self-adjoint operators attain an extremum of the Rayleigh quotient, yielding a nonzero
eigenvector for either the global supremum or the global infimum. -/
theorem exists_hasEigenvector_iSup_or_iInf_of_isCompactOperator
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (hTc : IsCompactOperator (T : E → E)) :
    (∃ x : E,
        Module.End.HasEigenvector (T : E →ₗ[𝕜] E)
          (↑(⨆ x : { x : E // x ≠ 0 }, T.rayleighQuotient x)) x) ∨
      (∃ x : E,
        Module.End.HasEigenvector (T : E →ₗ[𝕜] E)
          (↑(⨅ x : { x : E // x ≠ 0 }, T.rayleighQuotient x)) x) := by
  classical
  by_cases hT0 : T = 0
  · -- Any nonzero vector is an eigenvector with eigenvalue `0 = iSup`.
    have hsup : (⨆ x : { x : E // x ≠ 0 }, (0 : E →L[𝕜] E).rayleighQuotient x) = (0 : ℝ) := by
      simp_all
    obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne (0 : E)
    left
    subst hT0
    refine ⟨x, ?_⟩
    have : Module.End.HasEigenvector (0 : E →ₗ[𝕜] E) (0 : 𝕜) x := by
      refine ⟨?_, hx⟩
      simp_all
    simpa [hsup] using this
  -- Work on the unit weak closed ball, which is weakly compact in a Hilbert space.
  let s : Set (WeakSpace 𝕜 E) := weakClosedBall (𝕜 := 𝕜) (E := E) (1 : ℝ)
  let f : WeakSpace 𝕜 E → ℝ := fun x => T.reApplyInnerSelf (x : E)
  have hs_compact : IsCompact s := isCompact_weakClosedBall (𝕜 := 𝕜) (E := E) (1 : ℝ)
  have hs_nonempty : s.Nonempty := by
    refine ⟨(0 : WeakSpace 𝕜 E), ?_⟩
    change (0 : E) ∈ closedBall (α := E) (0 : E) (1 : ℝ)
    exact Metric.mem_closedBall_self zero_le_one
  have hf_cont : ContinuousOn f s :=
    continuousOn_weakClosedBall_reApplyInnerSelf_of_isCompactOperator
      (𝕜 := 𝕜) (E := E) T hTc (1 : ℝ)
  rcases hs_compact.exists_isMaxOn hs_nonempty hf_cont with ⟨xMax, hxMax_mem, hxMax⟩
  rcases hs_compact.exists_isMinOn hs_nonempty hf_cont with ⟨xMin, hxMin_mem, hxMin⟩
  -- Produce a point on the unit ball where the quadratic form is nonzero.
  rcases exists_reApplyInnerSelf_ne_zero_of_isSelfAdjoint (𝕜 := 𝕜) (E := E) T hT hT0 with ⟨x, hx⟩
  have hx0 : x ≠ 0 := by
    intro hx'
    subst hx'
    exact hx (by simp [ContinuousLinearMap.reApplyInnerSelf_apply])
  let c : 𝕜 := (((‖x‖)⁻¹ : ℝ) : 𝕜)
  let y : E := c • x
  let yw : WeakSpace 𝕜 E := (y : WeakSpace 𝕜 E)
  have hc : c ≠ 0 := by
    simp [c, hx0]
  have hy_norm : ‖y‖ = (1 : ℝ) := by
    simp [y, c, norm_smul, hx0]
  have hyw_mem : yw ∈ s := by
    change y ∈ closedBall (α := E) (0 : E) (1 : ℝ)
    simp_all
  have hyw_eval : f yw = ‖c‖ ^ 2 * T.reApplyInnerSelf x := by
    simp [f, yw, y, c, ContinuousLinearMap.reApplyInnerSelf_smul]
  have hc2_pos : 0 < (‖c‖ ^ 2 : ℝ) := by
    simp_all
  have hyw_ne : f yw ≠ 0 := by
    -- `f yw` is a nonzero scalar multiple of `T.reApplyInnerSelf x`.
    simp_all
  have hyw_sign : f yw < 0 ∨ 0 < f yw := lt_or_gt_of_ne hyw_ne
  cases hyw_sign with
  | inl hyw_neg =>
      -- Use the minimiser: strictly negative, so on the unit sphere, giving an eigenvector.
      have hxMin_neg : f xMin < 0 := by
        have hxMin_le : f xMin ≤ f yw := (isMinOn_iff.1 hxMin) yw hyw_mem
        exact lt_of_le_of_lt hxMin_le hyw_neg
      have hxMin_norm_eq : ‖(xMin : E)‖ = (1 : ℝ) :=
        extremizer_mem_unit_sphere (f := f)
          (fun c y => by
            change T.reApplyInnerSelf (c • (y : E)) = ‖c‖ ^ 2 * T.reApplyInnerSelf (y : E)
            exact ContinuousLinearMap.reApplyInnerSelf_smul T (y : E) (c := c))
          hxMin_mem (σ := -1) (by linarith)
          (fun y hy => by linarith [(isMinOn_iff.1 hxMin) y hy])
      have hxMin_ne0 : (xMin : E) ≠ 0 := by
        intro hx0'
        -- hxMin_norm_eq : ‖(xMin : E)‖ = 1, but xMin = 0, so ‖0‖ = 1, contradiction
        let xme : E := xMin
        have hxme0 : xme = 0 := hx0'
        have hxme_norm : ‖xme‖ = 1 := hxMin_norm_eq
        simp_all
      have hmin_sphere : IsMinOn T.reApplyInnerSelf
          (sphere (0 : E) (1 : ℝ)) (xMin : E) := by
        refine (isMinOn_iff.2 ?_)
        intro y hy
        have hy' : (y : WeakSpace 𝕜 E) ∈ s := by
          change y ∈ closedBall (α := E) (0 : E) (1 : ℝ)
          exact sphere_subset_closedBall hy
        have := (isMinOn_iff.1 hxMin) (y : WeakSpace 𝕜 E) hy'
        simpa [f] using this
      right
      refine ⟨(xMin : E), ?_⟩
      have hmin_sphere' :
          IsMinOn T.reApplyInnerSelf (sphere (0 : E) ‖(xMin : E)‖) (xMin : E) := by
        simpa [hxMin_norm_eq] using hmin_sphere
      exact IsSelfAdjoint.hasEigenvector_of_isMinOn (T := T) hT hxMin_ne0 hmin_sphere'
  | inr hyw_pos =>
      -- Use the maximiser: strictly positive, so on the unit sphere, giving an eigenvector.
      have hxMax_pos : 0 < f xMax := by
        have hxMax_ge : f yw ≤ f xMax := (isMaxOn_iff.1 hxMax) yw hyw_mem
        exact lt_of_lt_of_le hyw_pos hxMax_ge
      have hxMax_norm_eq : ‖(xMax : E)‖ = (1 : ℝ) :=
        extremizer_mem_unit_sphere (f := f)
          (fun c y => by
            change T.reApplyInnerSelf (c • (y : E)) = ‖c‖ ^ 2 * T.reApplyInnerSelf (y : E)
            exact ContinuousLinearMap.reApplyInnerSelf_smul T (y : E) (c := c))
          hxMax_mem (σ := 1) (by linarith)
          (fun y hy => by linarith [(isMaxOn_iff.1 hxMax) y hy])
      have hxMax_ne0 : (xMax : E) ≠ 0 := by
        intro hx0'
        let xme : E := xMax
        have hxme0 : xme = 0 := hx0'
        have hxme_norm : ‖xme‖ = 1 := hxMax_norm_eq
        simp_all
      have hmax_sphere : IsMaxOn T.reApplyInnerSelf
          (sphere (0 : E) (1 : ℝ)) (xMax : E) := by
        refine (isMaxOn_iff.2 ?_)
        intro y hy
        have hy' : (y : WeakSpace 𝕜 E) ∈ s := by
          change y ∈ closedBall (α := E) (0 : E) (1 : ℝ)
          exact sphere_subset_closedBall hy
        have := (isMaxOn_iff.1 hxMax) (y : WeakSpace 𝕜 E) hy'
        simpa [f] using this
      left
      refine ⟨(xMax : E), ?_⟩
      have hmax_sphere' :
          IsMaxOn T.reApplyInnerSelf (sphere (0 : E) ‖(xMax : E)‖) (xMax : E) := by
        simpa [hxMax_norm_eq] using hmax_sphere
      exact IsSelfAdjoint.hasEigenvector_of_isMaxOn (T := T) hT hxMax_ne0 hmax_sphere'
end
end CompactSelfAdjoint
