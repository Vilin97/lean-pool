/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.ScalarEvolution
public import LeanPool.PoincareGeometry.PoincareCurvature.Analysis.RiccatiBarrier

/-!
# Compact scalar parabolic Riccati barrier

This file proves the spacetime maximum-principle step used in the scalar
curvature lower bound.  On a compact boundaryless manifold, an intrinsic
supersolution

`partial_t f >= Delta f + (2 / n) f^2`

with initial lower bound `f(0) >= -n C` satisfies the sharp barrier

`f(t) >= -n C / (1 + 2 C t)`.

The proof minimizes the rescaled quantity
`(1 + 2 C t) f + n C` on a compact spacetime slab.  At a hypothetical
negative minimum, the intrinsic Laplace--Beltrami operator is nonnegative
and the backward time derivative is nonpositive, while the reaction term
forces that derivative to be strictly positive.
-/

@[expose] public noncomputable section

open Bundle Filter Set Topology
open scoped Manifold ContDiff

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [CompactSpace M] [Nonempty M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)

/-- Sharp compact-manifold Riccati barrier for an intrinsic scalar parabolic
supersolution. -/
theorem parabolicRiccatiLowerBarrier
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (f ft : ℝ → M → ℝ) {n C T : ℝ}
    (hn : 0 < n) (hC : 0 ≤ C)
    (hcont : ContinuousOn (fun p : ℝ × M => f p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (htime : ∀ t ∈ Icc 0 T, ∀ x : M,
      HasDerivAt (fun s => f s x) (ft t x) t)
    (hfNear : ∀ t ∈ Icc 0 T, ∀ x : M,
      ∀ᶠ y in nhds x, MDiffAt (f t) y)
    (hdf : ∀ t ∈ Icc 0 T, ∀ x : M,
      MDiffAt
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
          (CovariantDerivative.scalarDifferential (I := I) (f t) y)) x)
    (hpde : ∀ t ∈ Icc 0 T, ∀ x : M,
      g.scalarLaplacian cov f t x + (2 / n) * (f t x) ^ 2 ≤ ft t x)
    (hinitial : ∀ x : M, -n * C ≤ f 0 x) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      -n * C / (1 + 2 * C * t) ≤ f t x := by
  let F : ℝ × M → ℝ := fun p =>
    (1 + 2 * C * p.1) * f p.1 p.2 + n * C
  have hFcont : ContinuousOn F (Icc 0 T ×ˢ (Set.univ : Set M)) := by
    have hcoeff : Continuous (fun p : ℝ × M => 1 + 2 * C * p.1) := by
      fun_prop
    exact (hcoeff.continuousOn.mul hcont).add continuousOn_const
  intro b hb x
  have hdenb : 0 < 1 + 2 * C * b := by
    nlinarith [mul_nonneg hC hb.1]
  rw [div_le_iff₀ hdenb]
  by_contra hbarrier
  have hFbx : F (b, x) < 0 := by
    dsimp [F]
    linarith
  let slab : Set (ℝ × M) := Icc 0 b ×ˢ (Set.univ : Set M)
  have hslabCompact : IsCompact slab :=
    isCompact_Icc.prod isCompact_univ
  have hslabNonempty : slab.Nonempty :=
    ⟨(0, Classical.choice inferInstance), ⟨⟨le_rfl, hb.1⟩, Set.mem_univ _⟩⟩
  have hslabSub : slab ⊆ Icc 0 T ×ˢ (Set.univ : Set M) := by
    intro p hp
    exact ⟨⟨hp.1.1, hp.1.2.trans hb.2⟩, Set.mem_univ _⟩
  obtain ⟨p, hp, hpmin⟩ :=
    hslabCompact.exists_isMinOn hslabNonempty (hFcont.mono hslabSub)
  have hpneg : F p < 0 :=
    (hpmin ⟨⟨hb.1, le_rfl⟩, Set.mem_univ x⟩).trans_lt hFbx
  have hptimePos : 0 < p.1 := by
    have hptimeNonneg : 0 ≤ p.1 := hp.1.1
    have hne : p.1 ≠ 0 := by
      intro hpeq
      have hinit := hinitial p.2
      change (1 + 2 * C * p.1) * f p.1 p.2 + n * C < 0 at hpneg
      rw [hpeq] at hpneg
      norm_num at hpneg
      linarith
    exact lt_of_le_of_ne hptimeNonneg (Ne.symm hne)
  have hdenp : 0 < 1 + 2 * C * p.1 := by
    nlinarith [mul_nonneg hC hp.1.1]
  have hfpneg : f p.1 p.2 < 0 := by
    have hnC : 0 ≤ n * C := mul_nonneg hn.le hC
    dsimp [F] at hpneg
    by_contra hnonneg
    have hfnonneg : 0 ≤ f p.1 p.2 := le_of_not_gt hnonneg
    nlinarith [mul_nonneg hdenp.le hfnonneg]
  have hspatialMinOn : IsMinOn (f p.1) Set.univ p.2 := by
    intro y hy
    have hFy := hpmin
      (show (p.1, y) ∈ slab from ⟨hp.1, Set.mem_univ y⟩)
    dsimp [F] at hFy
    have hscaled :
        (1 + 2 * C * p.1) * f p.1 p.2 ≤
          (1 + 2 * C * p.1) * f p.1 y := by
      linarith
    exact (mul_le_mul_iff_of_pos_left hdenp).mp hscaled
  have hlap : 0 ≤ g.scalarLaplacian cov f p.1 p.2 :=
    g.scalarLaplacian_nonneg_of_isLocalMin cov f p.1
      (hspatialMinOn.isLocalMin univ_mem)
      (hfNear p.1 ⟨hp.1.1, hp.1.2.trans hb.2⟩ p.2)
      (hdf p.1 ⟨hp.1.1, hp.1.2.trans hb.2⟩ p.2)
  let z : ℝ → ℝ := fun t => F (t, p.2)
  let z' : ℝ :=
    2 * C * f p.1 p.2 + (1 + 2 * C * p.1) * ft p.1 p.2
  have hzderiv : HasDerivAt z z' p.1 := by
    have hlinear : HasDerivAt (fun t : ℝ => 1 + 2 * C * t) (2 * C) p.1 := by
      convert! (hasDerivAt_const p.1 (1 : ℝ)).add
        ((hasDerivAt_id p.1).const_mul (2 * C)) using 1
      ring
    have hfderiv := htime p.1 ⟨hp.1.1, hp.1.2.trans hb.2⟩ p.2
    dsimp [z, F, z']
    convert! (hlinear.mul hfderiv).add_const (n * C) using 1
  have htimeMin : IsLocalMinOn z (Icc 0 b) p.1 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hpmin (show (t, p.2) ∈ slab from ⟨ht, Set.mem_univ p.2⟩)
  have hzeroMem : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.1⟩
  have htangent : (0 : ℝ) - p.1 ∈ posTangentConeAt (Icc 0 b) p.1 :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc (0 : ℝ) b).segment_subset hp.1 hzeroMem)
  have hznonpos := htimeMin.hasFDerivWithinAt_nonneg
    hzderiv.hasFDerivAt.hasFDerivWithinAt htangent
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hznonpos
  have hzle : z' ≤ 0 := by
    dsimp [z'] at ⊢
    nlinarith
  have hpde' := hpde p.1 ⟨hp.1.1, hp.1.2.trans hb.2⟩ p.2
  have hreaction : 0 <
      2 * C * f p.1 p.2 +
        (1 + 2 * C * p.1) * ((2 / n) * (f p.1 p.2) ^ 2) := by
    have hfactor :
        2 * C * f p.1 p.2 +
            (1 + 2 * C * p.1) * ((2 / n) * (f p.1 p.2) ^ 2) =
          (2 / n) * f p.1 p.2 * F p := by
      dsimp [F]
      field_simp [hn.ne']
      ring
    rw [hfactor]
    exact mul_pos_of_neg_of_neg
      (mul_neg_of_pos_of_neg (div_pos (by norm_num) hn) hfpneg) hpneg
  have hscaledPDE :
      (1 + 2 * C * p.1) *
          (g.scalarLaplacian cov f p.1 p.2 +
            (2 / n) * (f p.1 p.2) ^ 2) ≤
        (1 + 2 * C * p.1) * ft p.1 p.2 :=
    mul_le_mul_of_nonneg_left hpde' hdenp.le
  have hzpos : 0 < z' := by
    dsimp [z']
    nlinarith [mul_nonneg hdenp.le hlap]
  linarith

end CovariantDerivative.TimeDependentRiemannianMetric
