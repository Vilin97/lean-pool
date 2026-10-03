/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Kernel
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ZeroExtensionGraph
public import Mathlib.Analysis.Convex.Topology

/-!
# Inward mollification on bounded convex domains

This file records the geometric version of global mollification used for
zero-boundary Sobolev approximation.  The convolution is evaluated after an
outward affine dilation.  Consequently, its support is a compact set strictly
inside the original bounded open convex domain.
-/

@[expose] public section

namespace Homogenization

open Function Set MeasureTheory Topology
open scoped Pointwise Convolution

noncomputable section

/-- Mollify a global field at scale `ε * r` and pull the result back by the
outward affine map based at `x0`. -/
noncomputable def inwardMollification {d : ℕ} (ρ g : Vec d → ℝ)
    (x0 : Vec d) (r ε : ℝ) : Vec d → ℝ :=
  fun x =>
    (scaledConvexApproxKernel ρ (ε * r) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      volume] g) ((1 + ε) • x - ε • x0)

@[simp] theorem inwardMollification_apply {d : ℕ} (ρ g : Vec d → ℝ)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    inwardMollification ρ g x0 r ε x =
      (scaledConvexApproxKernel ρ (ε * r) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        volume] g) ((1 + ε) • x - ε • x0) :=
  rfl

private def inwardMollificationSupportSet {d : ℕ} (U : Set (Vec d))
    (x0 : Vec d) (r ε : ℝ) : Set (Vec d) :=
  (fun y : Vec d => (1 + ε)⁻¹ • y + (ε * (1 + ε)⁻¹) • x0) ''
    (Metric.closedBall (0 : Vec d) (ε * r) + closure U)

private theorem inwardMollification_affine_eq {d : ℕ} (x x0 : Vec d) {ε : ℝ}
    (hε : 0 < ε) :
    x = (1 + ε)⁻¹ • ((1 + ε) • x - ε • x0) +
      (ε * (1 + ε)⁻¹) • x0 := by
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, smul_eq_mul, Pi.smul_apply]
  field_simp [hε.ne']
  ring

private theorem inwardMollification_supportSet_compact {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (x0 : Vec d) (r ε : ℝ) :
    IsCompact (inwardMollificationSupportSet U x0 r ε) := by
  apply IsCompact.image
  · exact (isCompact_closedBall (0 : Vec d) (ε * r)).add
      hU.isBoundedDomain.isBounded.isCompact_closure
  · exact
      ((continuous_const : Continuous fun _ : Vec d => (1 + ε)⁻¹).smul continuous_id).add
        (continuous_const : Continuous fun _ : Vec d => (ε * (1 + ε)⁻¹) • x0)

private theorem scaledBall_translate_mem {d : ℕ} {x0 t : Vec d} {r ε : ℝ}
    (hε : 0 < ε) (ht : t ∈ Metric.closedBall (0 : Vec d) (ε * r)) :
    x0 + ε⁻¹ • t ∈ Metric.closedBall x0 r := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have ht_norm : ‖t‖ ≤ ε * r := by
    rw [Metric.mem_closedBall, dist_zero_right] at ht
    exact ht
  have hε_inv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.le
  calc
    ‖x0 + ε⁻¹ • t - x0‖ = ‖ε⁻¹ • t‖ := by abel_nf
    _ = |ε⁻¹| * ‖t‖ := norm_smul _ _
    _ = ε⁻¹ * ‖t‖ := by rw [abs_of_nonneg hε_inv_nonneg]
    _ ≤ ε⁻¹ * (ε * r) := mul_le_mul_of_nonneg_left ht_norm hε_inv_nonneg
    _ = r := by field_simp [hε.ne']

private theorem inwardMollification_supportSet_subset {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hε : 0 < ε) :
    inwardMollificationSupportSet U x0 r ε ⊆ U := by
  rintro x ⟨y, hy, rfl⟩
  rcases hy with ⟨t, ht, z, hz, rfl⟩
  have hw : x0 + ε⁻¹ • t ∈ U :=
    hball (scaledBall_translate_mem hε ht)
  have hz' : z ∈ closure U := hz
  have hinterior : z ∈ closure U := hz'
  have hw_interior : x0 + ε⁻¹ • t ∈ interior U := by
    rwa [hU.isOpen.interior_eq]
  have ha_nonneg : 0 ≤ (1 + ε)⁻¹ := by positivity
  have hb_pos : 0 < ε * (1 + ε)⁻¹ := by positivity
  have hab : (1 + ε)⁻¹ + ε * (1 + ε)⁻¹ = 1 := by
    field_simp [hε.ne']
  have hcombo := hU.convex.combo_closure_interior_mem_interior hinterior hw_interior
    ha_nonneg hb_pos hab
  have hrewrite :
      (1 + ε)⁻¹ • (t + z) + (ε * (1 + ε)⁻¹) • x0 =
        (1 + ε)⁻¹ • z + (ε * (1 + ε)⁻¹) • (x0 + ε⁻¹ • t) := by
    ext i
    simp only [Pi.add_apply, smul_eq_mul, Pi.smul_apply]
    field_simp [hε.ne']
    ring
  change (1 + ε)⁻¹ • (t + z) + (ε * (1 + ε)⁻¹) • x0 ∈ U
  rw [hrewrite]
  rwa [hU.isOpen.interior_eq] at hcombo

/-- A compactly supported smooth kernel convolved with a locally integrable
field is smooth after the inward affine pullback. -/
theorem contDiff_inwardMollification {d : ℕ} {ρ g : Vec d → ℝ}
    (hρ : IsConvexApproxKernel ρ) (hg : LocallyIntegrable g volume)
    {x0 : Vec d} {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (inwardMollification ρ g x0 r ε) := by
  have hscale : 0 < ε * r := mul_pos hε hr
  have hconv :
      ContDiff ℝ (⊤ : ℕ∞)
        (scaledConvexApproxKernel ρ (ε * r) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          volume] g) :=
    HasCompactSupport.contDiff_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
      (hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport hscale)
      (contDiff_scaledConvexApproxKernel hρ (ε * r)) hg
  have haff : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec d => (1 + ε) • x - ε • x0) := by
    simpa using (contDiff_const.smul contDiff_id).sub contDiff_const
  simpa [inwardMollification] using! hconv.comp haff

/-- The topological support of inward mollification lies strictly in the
domain, provided the input field is supported in the domain closure. -/
theorem tsupport_inwardMollification_subset {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {ρ g : Vec d → ℝ}
    (hρ : IsConvexApproxKernel ρ) (hg_support : tsupport g ⊆ closure U)
    {x0 : Vec d} {r ε : ℝ} (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε : 0 < ε) :
    tsupport (inwardMollification ρ g x0 r ε) ⊆ U := by
  let k : Vec d → ℝ := scaledConvexApproxKernel ρ (ε * r)
  let h : Vec d → ℝ := k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g
  let K := inwardMollificationSupportSet U x0 r ε
  have hscale : 0 < ε * r := mul_pos hε hr
  have hk_support : support k ⊆ Metric.closedBall (0 : Vec d) (ε * r) := by
    intro t ht
    have hρ_ne : ρ ((ε * r)⁻¹ • t) ≠ 0 := by
      intro hzero
      apply ht
      simp only [k, scaledConvexApproxKernel, hzero, mul_zero]
    have hρ_ball : (ε * r)⁻¹ • t ∈ Metric.closedBall (0 : Vec d) 1 :=
      hρ.support_subset_closedBall (subset_tsupport ρ hρ_ne)
    rw [Metric.mem_closedBall, dist_zero_right] at hρ_ball ⊢
    calc
      ‖t‖ = (ε * r) * ((ε * r)⁻¹ * ‖t‖) := by
        field_simp [hscale.ne']
      _ = (ε * r) * ‖(ε * r)⁻¹ • t‖ := by
        rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hscale]
      _ ≤ (ε * r) * 1 := mul_le_mul_of_nonneg_left hρ_ball hscale.le
      _ = ε * r := mul_one _
  have hg_raw_support : support g ⊆ closure U :=
    (subset_tsupport g).trans hg_support
  have hh_support : support h ⊆ Metric.closedBall (0 : Vec d) (ε * r) + closure U := by
    exact (support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ)).trans
      (add_subset_add hk_support hg_raw_support)
  have hK_compact : IsCompact K := inwardMollification_supportSet_compact hU x0 r ε
  have hraw : support (inwardMollification ρ g x0 r ε) ⊆ K := by
    intro x hx
    refine ⟨(1 + ε) • x - ε • x0, ?_, ?_⟩
    · apply hh_support
      change h ((1 + ε) • x - ε • x0) ≠ 0
      simpa only [inwardMollification, h, k] using! hx
    · exact (inwardMollification_affine_eq x x0 hε).symm
  have htsupportK : tsupport (inwardMollification ρ g x0 r ε) ⊆ K :=
    closure_minimal hraw hK_compact.isClosed
  exact htsupportK.trans (inwardMollification_supportSet_subset hU hball hε)

/-- Inward mollification has compact support under the bounded-domain support
condition. -/
theorem hasCompactSupport_inwardMollification {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {ρ g : Vec d → ℝ}
    (hρ : IsConvexApproxKernel ρ) (hg_support : tsupport g ⊆ closure U)
    {x0 : Vec d} {r ε : ℝ} (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε : 0 < ε) :
    HasCompactSupport (inwardMollification ρ g x0 r ε) := by
  exact hU.isBoundedDomain.isBounded.isCompact_closure.of_isClosed_subset
    (isClosed_tsupport _)
    ((tsupport_inwardMollification_subset hU hρ hg_support hball hr hε).trans subset_closure)

namespace H10Function

/-- The literal zero extension of an `H¹₀` function is supported in the
closure of its domain. -/
theorem tsupport_zeroExtension_subset_closure {d : ℕ} {U : Set (Vec d)}
    (u : H10Function U) :
    tsupport u.zeroExtension ⊆ closure U := by
  apply closure_mono
  intro x hx
  by_contra hxU
  exact hx (u.zeroExtension_apply_of_not_mem hxU)

/-- The inward mollification of the global zero extension of an `H¹₀`
function is globally smooth, compactly supported, and has topological support
strictly inside the original bounded open convex domain. -/
theorem inwardMollification_unit_properties {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H10Function U)
    {x0 : Vec d} {r ε : ℝ} (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞)
        (inwardMollification (unitConvexApproxKernel (d := d)) u.zeroExtension x0 r ε) ∧
      HasCompactSupport
        (inwardMollification (unitConvexApproxKernel (d := d)) u.zeroExtension x0 r ε) ∧
      tsupport
        (inwardMollification (unitConvexApproxKernel (d := d)) u.zeroExtension x0 r ε) ⊆ U := by
  have hρ : IsConvexApproxKernel (unitConvexApproxKernel (d := d)) :=
    isConvexApproxKernel_unitConvexApproxKernel
  have hu_mem : MemLp u.zeroExtension 2 volume :=
    u.memLp_zeroExtension hU.isOpen.measurableSet u.toH1Function.memL2
  have hu_local : LocallyIntegrable u.zeroExtension volume :=
    hu_mem.locallyIntegrable (by norm_num)
  have hu_support : tsupport u.zeroExtension ⊆ closure U :=
    u.tsupport_zeroExtension_subset_closure
  refine ⟨contDiff_inwardMollification hρ hu_local hr hε,
    hasCompactSupport_inwardMollification hU hρ hu_support hball hr hε,
    tsupport_inwardMollification_subset hU hρ hu_support hball hr hε⟩

end H10Function

end

end Homogenization
