/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.Compactness
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.Bases

/-!
# Weak path compactness for Galerkin approximations

The pointwise Hilbert-space extraction in `Compactness` does not by itself produce one
subsequence converging at every time. This file packages the path-space step: a uniformly bounded,
weakly equicontinuous sequence of continuous Hilbert-valued paths has a subsequence converging
pointwise weakly on the whole compact time interval. A common initial trace and the uniform norm
bound pass to that limit.

For a Galerkin sequence, the equation is responsible for the weak equicontinuity premise. The
constructor for that modulus is kept separate from this compactness theorem.
-/

@[expose] public section

noncomputable section

open Filter Topology
open scoped RealInnerProductSpace

open TopologicalSpace

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- Closed unit time interval for the Galerkin path compactness argument. -/
abbrev PathCompactness.TimeInterval := Set.Icc (0 : ℝ) 1

section WeakUniformity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [TopologicalSpace.SeparableSpace E]

local instance weakDualTopologicalAddGroup : IsTopologicalAddGroup (WeakDual ℝ E) :=
  (WeakDual.withSeminorms ℝ E).isTopologicalAddGroup

/-- Translation-invariant uniform structure on the weak dual. -/
local instance weakDualUniformSpace : UniformSpace (WeakDual ℝ E) :=
  IsTopologicalAddGroup.rightUniformSpace (WeakDual ℝ E)

local instance weakDualUniformAddGroup : IsUniformAddGroup (WeakDual ℝ E) :=
  isUniformAddGroup_of_addCommGroup

/-- The Hilbert Riesz map, viewed with the weak-dual topology. -/
def hilbertToWeakDual (x : E) : WeakDual ℝ E :=
  StrongDual.toWeakDual (InnerProductSpace.toDualMap ℝ E x)

omit [CompleteSpace E] [TopologicalSpace.SeparableSpace E] in
@[simp]
theorem hilbertToWeakDual_apply (x v : E) : hilbertToWeakDual x v = inner ℝ x v := by
  simp [hilbertToWeakDual, InnerProductSpace.toDualMap_apply_apply,
    StrongDual.toWeakDual_apply]

omit [CompleteSpace E] [TopologicalSpace.SeparableSpace E] in
theorem PathCompactness.exists_finite_test_modulus
    {uSeq : ℕ → PathCompactness.TimeInterval → E}
    (hmod : ∀ v : E, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n t s,
        |inner ℝ (uSeq n t) v - inner ℝ (uSeq n s) v| ≤ C * Real.sqrt (dist t s))
    (s : Finset E) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t₀ t n, dist t t₀ < δ →
      (s.sup (WeakDual.seminormFamily ℝ E))
        (hilbertToWeakDual (uSeq n t) - hilbertToWeakDual (uSeq n t₀)) < ε := by
  classical
  let L : E → ℝ := fun v => Classical.choose (hmod v)
  have hL_nonneg (v : E) : 0 ≤ L v := (Classical.choose_spec (hmod v)).1
  have hL_mod (v : E) : ∀ n t s,
      |inner ℝ (uSeq n t) v - inner ℝ (uSeq n s) v| ≤
        L v * Real.sqrt (dist t s) :=
    (Classical.choose_spec (hmod v)).2
  let R : ℝ := ∑ v ∈ s, L v
  have hR : 0 ≤ R := Finset.sum_nonneg fun v hv => hL_nonneg v
  have hL_le (v : E) (hv : v ∈ s) : L v ≤ R :=
    Finset.single_le_sum (fun w hw => hL_nonneg w) hv
  let δ : ℝ := (ε / (R + 1)) ^ 2
  have hδ : 0 < δ := by
    dsimp [δ]
    exact sq_pos_of_pos (div_pos hε (by linarith))
  have hRδ : R * Real.sqrt δ < ε := by
    have hq : 0 ≤ ε / (R + 1) := by positivity
    have hsqrt : Real.sqrt δ = ε / (R + 1) := by
      simp [δ, Real.sqrt_sq_eq_abs, abs_of_nonneg hq]
    have hratio : R / (R + 1) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    calc
      R * Real.sqrt δ = ε * (R / (R + 1)) := by rw [hsqrt]; ring
      _ < ε * 1 := mul_lt_mul_of_pos_left hratio hε
      _ = ε := by ring
  refine ⟨δ, hδ, ?_⟩
  intro t₀ t n hdist
  have hsup :
      (s.sup (WeakDual.seminormFamily ℝ E))
        (hilbertToWeakDual (uSeq n t) - hilbertToWeakDual (uSeq n t₀)) < ε := by
    apply Seminorm.finset_sup_apply_lt hε
    intro v hv
    change ‖(hilbertToWeakDual (uSeq n t) -
      hilbertToWeakDual (uSeq n t₀)) v‖ < ε
    have hpair :
        |inner ℝ (uSeq n t) v - inner ℝ (uSeq n t₀) v| ≤
          L v * Real.sqrt (dist t t₀) :=
      hL_mod v n t t₀
    have hlt : L v * Real.sqrt (dist t t₀) < ε := by
      calc
        L v * Real.sqrt (dist t t₀) ≤ R * Real.sqrt (dist t t₀) :=
          mul_le_mul_of_nonneg_right (hL_le v hv) (Real.sqrt_nonneg _)
        _ ≤ R * Real.sqrt δ := mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (le_of_lt hdist)) hR
        _ < ε := hRδ
    calc
      ‖(hilbertToWeakDual (uSeq n t) -
          hilbertToWeakDual (uSeq n t₀)) v‖ =
        |(hilbertToWeakDual (uSeq n t) -
          hilbertToWeakDual (uSeq n t₀)) v| := Real.norm_eq_abs _
      _ = |inner ℝ (uSeq n t) v - inner ℝ (uSeq n t₀) v| := by
        change |hilbertToWeakDual (uSeq n t) v -
          hilbertToWeakDual (uSeq n t₀) v| = _
        rw [hilbertToWeakDual_apply, hilbertToWeakDual_apply]
      _ < ε := hpair.trans_lt hlt
  exact hsup

omit [CompleteSpace E] [TopologicalSpace.SeparableSpace E] in
theorem PathCompactness.exists_weakDual_neighborhood_modulus
    {uSeq : ℕ → PathCompactness.TimeInterval → E}
    (hmod : ∀ v : E, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n t s,
        |inner ℝ (uSeq n t) v - inner ℝ (uSeq n s) v| ≤ C * Real.sqrt (dist t s))
    {V : Set (WeakDual ℝ E)} (hV : V ∈ 𝓝 (0 : WeakDual ℝ E)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t₀ t n, dist t t₀ < δ →
      hilbertToWeakDual (uSeq n t) - hilbertToWeakDual (uSeq n t₀) ∈ V := by
  obtain ⟨⟨s, ε⟩, hε, hballSub⟩ :=
    ((WeakDual.withSeminorms ℝ E).hasBasis_zero_ball).mem_iff.mp hV
  obtain ⟨δ, hδ, hfinite⟩ := PathCompactness.exists_finite_test_modulus hmod s hε
  refine ⟨δ, hδ, ?_⟩
  intro t₀ t n hdist
  have hball : hilbertToWeakDual (uSeq n t) - hilbertToWeakDual (uSeq n t₀) ∈
      (s.sup (WeakDual.seminormFamily ℝ E)).ball 0 ε := by
    simpa only [Seminorm.mem_ball, sub_zero] using hfinite t₀ t n hdist
  exact hballSub hball

omit [CompleteSpace E] [TopologicalSpace.SeparableSpace E] in
theorem PathCompactness.exists_finite_dense_test_modulus
    {uSeq : ℕ → PathCompactness.TimeInterval → E} {S : Set E} {M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ n t, ‖uSeq n t‖ ≤ M)
    (happrox : ∀ v : E, ∀ ε : ℝ, 0 < ε → ∃ w ∈ S, dist v w < ε)
    (hmod : ∀ w ∈ S, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n t s,
        |inner ℝ (uSeq n t) w - inner ℝ (uSeq n s) w| ≤ C * Real.sqrt (dist t s))
    (s : Finset E) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t₀ t n, dist t t₀ < δ →
      (s.sup (WeakDual.seminormFamily ℝ E))
        (hilbertToWeakDual (uSeq n t) - hilbertToWeakDual (uSeq n t₀)) < ε := by
  classical
  let ρ : ℝ := ε / (4 * (M + 1))
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact div_pos hε (by positivity)
  have hρerr : 2 * M * ρ < ε / 2 := by
    dsimp [ρ]
    have hfrac : M / (M + 1) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    calc
      2 * M * (ε / (4 * (M + 1))) = (ε / 2) * (M / (M + 1)) := by
        field_simp
        ring
      _ < (ε / 2) * 1 := mul_lt_mul_of_pos_left hfrac (by linarith)
      _ = ε / 2 := by ring
  let w : E → E := fun v => Classical.choose (happrox v ρ hρ)
  have hw_mem (v : E) : w v ∈ S := (Classical.choose_spec (happrox v ρ hρ)).1
  have hw_dist (v : E) : dist v (w v) < ρ := (Classical.choose_spec (happrox v ρ hρ)).2
  let L : E → ℝ := fun v => Classical.choose (hmod (w v) (hw_mem v))
  have hL_nonneg (v : E) : 0 ≤ L v :=
    (Classical.choose_spec (hmod (w v) (hw_mem v))).1
  have hL_mod (v : E) : ∀ n t s,
      |inner ℝ (uSeq n t) (w v) - inner ℝ (uSeq n s) (w v)| ≤
        L v * Real.sqrt (dist t s) :=
    (Classical.choose_spec (hmod (w v) (hw_mem v))).2
  let R : ℝ := ∑ v ∈ s, L v
  have hR : 0 ≤ R := Finset.sum_nonneg fun v hv => hL_nonneg v
  have hL_le (v : E) (hv : v ∈ s) : L v ≤ R :=
    Finset.single_le_sum (fun z hz => hL_nonneg z) hv
  let δ : ℝ := ((ε / 2) / (R + 1)) ^ 2
  have hδ : 0 < δ := by
    dsimp [δ]
    exact sq_pos_of_pos (div_pos (by linarith) (by linarith))
  have hRδ : R * Real.sqrt δ < ε / 2 := by
    have hq : 0 ≤ (ε / 2) / (R + 1) := by positivity
    have hsqrt : Real.sqrt δ = (ε / 2) / (R + 1) := by
      simp [δ, Real.sqrt_sq_eq_abs, abs_of_nonneg hq]
    have hratio : R / (R + 1) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    calc
      R * Real.sqrt δ = (ε / 2) * (R / (R + 1)) := by rw [hsqrt]; ring
      _ < (ε / 2) * 1 := mul_lt_mul_of_pos_left hratio (by linarith)
      _ = ε / 2 := by ring
  refine ⟨δ, hδ, ?_⟩
  intro t₀ t n hdist
  have hsup :
      (s.sup (WeakDual.seminormFamily ℝ E))
        (hilbertToWeakDual (uSeq n t) - hilbertToWeakDual (uSeq n t₀)) < ε := by
    apply Seminorm.finset_sup_apply_lt hε
    intro v hv
    change ‖(hilbertToWeakDual (uSeq n t) -
      hilbertToWeakDual (uSeq n t₀)) v‖ < ε
    rw [Real.norm_eq_abs]
    have hsplit :
        inner ℝ (uSeq n t) v - inner ℝ (uSeq n t₀) v =
          (inner ℝ (uSeq n t) (w v) - inner ℝ (uSeq n t₀) (w v)) +
            (inner ℝ (uSeq n t) (v - w v) - inner ℝ (uSeq n t₀) (v - w v)) := by
      rw [← inner_sub_left, ← inner_sub_left, ← inner_sub_left]
      rw [← inner_add_right]
      congr 1
      abel
    have hpairApprox :
        |inner ℝ (uSeq n t) (v - w v) - inner ℝ (uSeq n t₀) (v - w v)| ≤
          2 * M * ρ := by
      calc
        _ ≤ |inner ℝ (uSeq n t) (v - w v)| +
            |inner ℝ (uSeq n t₀) (v - w v)| := abs_sub _ _
        _ ≤ (‖uSeq n t‖ + ‖uSeq n t₀‖) * ‖v - w v‖ := by
          have ht := abs_real_inner_le_norm (uSeq n t) (v - w v)
          have hs := abs_real_inner_le_norm (uSeq n t₀) (v - w v)
          nlinarith [ht, hs]
        _ ≤ (M + M) * ρ := by
          calc
            (‖uSeq n t‖ + ‖uSeq n t₀‖) * ‖v - w v‖ ≤
                (M + M) * ‖v - w v‖ :=
              mul_le_mul_of_nonneg_right
                (add_le_add (hbound n t) (hbound n t₀)) (norm_nonneg _)
            _ ≤ (M + M) * ρ :=
              mul_le_mul_of_nonneg_left
                (by rw [← dist_eq_norm]; exact (hw_dist v).le) (by positivity)
        _ = 2 * M * ρ := by ring
    have hpairMain :
        |inner ℝ (uSeq n t) (w v) - inner ℝ (uSeq n t₀) (w v)| < ε / 2 := by
      have hlt : L v * Real.sqrt (dist t t₀) < ε / 2 := by
        calc
          L v * Real.sqrt (dist t t₀) ≤ R * Real.sqrt (dist t t₀) :=
            mul_le_mul_of_nonneg_right (hL_le v hv) (Real.sqrt_nonneg _)
          _ ≤ R * Real.sqrt δ := mul_le_mul_of_nonneg_left
            (Real.sqrt_le_sqrt (le_of_lt hdist)) hR
          _ < ε / 2 := hRδ
      exact (hL_mod v n t t₀).trans_lt hlt
    have hsum := abs_add_le
      (inner ℝ (uSeq n t) (w v) - inner ℝ (uSeq n t₀) (w v))
      (inner ℝ (uSeq n t) (v - w v) - inner ℝ (uSeq n t₀) (v - w v))
    calc
      |inner ℝ (uSeq n t) v - inner ℝ (uSeq n t₀) v| ≤
          |inner ℝ (uSeq n t) (w v) - inner ℝ (uSeq n t₀) (w v)| +
            |inner ℝ (uSeq n t) (v - w v) - inner ℝ (uSeq n t₀) (v - w v)| := by
        rw [hsplit]
        exact hsum
      _ < ε / 2 + ε / 2 := add_lt_add hpairMain (hpairApprox.trans_lt hρerr)
      _ = ε := by ring
  exact hsup

omit [CompleteSpace E] [TopologicalSpace.SeparableSpace E] in
theorem PathCompactness.exists_weakDual_neighborhood_modulus_of_dense_tests
    {uSeq : ℕ → PathCompactness.TimeInterval → E} {S : Set E} {M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ n t, ‖uSeq n t‖ ≤ M)
    (happrox : ∀ v : E, ∀ ε : ℝ, 0 < ε → ∃ w ∈ S, dist v w < ε)
    (hmod : ∀ w ∈ S, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n t s,
        |inner ℝ (uSeq n t) w - inner ℝ (uSeq n s) w| ≤ C * Real.sqrt (dist t s))
    {V : Set (WeakDual ℝ E)} (hV : V ∈ 𝓝 (0 : WeakDual ℝ E)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t₀ t n, dist t t₀ < δ →
      hilbertToWeakDual (uSeq n t) - hilbertToWeakDual (uSeq n t₀) ∈ V := by
  obtain ⟨⟨s, ε⟩, hε, hballSub⟩ :=
    ((WeakDual.withSeminorms ℝ E).hasBasis_zero_ball).mem_iff.mp hV
  obtain ⟨δ, hδ, hfinite⟩ :=
    PathCompactness.exists_finite_dense_test_modulus hM hbound happrox hmod s hε
  refine ⟨δ, hδ, ?_⟩
  intro t₀ t n hdist
  have hball : hilbertToWeakDual (uSeq n t) - hilbertToWeakDual (uSeq n t₀) ∈
      (s.sup (WeakDual.seminormFamily ℝ E)).ball 0 ε := by
    simpa only [Seminorm.mem_ball, sub_zero] using hfinite t₀ t n hdist
  exact hballSub hball

omit [CompleteSpace E] [TopologicalSpace.SeparableSpace E] in
/-- Dense-test scalar moduli plus a uniform Hilbert bound imply weak-dual equicontinuity. -/
theorem weakDual_equicontinuous_of_dense_pairing_moduli
    {uSeq : ℕ → PathCompactness.TimeInterval → E} {S : Set E} {M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ n t, ‖uSeq n t‖ ≤ M)
    (happrox : ∀ v : E, ∀ ε : ℝ, 0 < ε → ∃ w ∈ S, dist v w < ε)
    (hmod : ∀ w ∈ S, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n t s,
        |inner ℝ (uSeq n t) w - inner ℝ (uSeq n s) w| ≤ C * Real.sqrt (dist t s)) :
    Equicontinuous
      (fun n t => StrongDual.toWeakDual
        (InnerProductSpace.toDualMap ℝ E (uSeq n t))) := by
  classical
  let toWeak (x : E) : WeakDual ℝ E := hilbertToWeakDual x
  intro t₀ U hU
  have hU' : U ∈ Filter.comap
      (fun p : WeakDual ℝ E × WeakDual ℝ E => p.2 - p.1)
      (𝓝 (0 : WeakDual ℝ E)) := by
    rw [← uniformity_eq_comap_nhds_zero]
    exact hU
  obtain ⟨V, hV, hpre⟩ := Filter.mem_comap.mp hU'
  obtain ⟨δ, hδ, hclose⟩ := PathCompactness.exists_weakDual_neighborhood_modulus_of_dense_tests
    hM hbound happrox hmod hV
  refine Filter.Eventually.mono (Metric.ball_mem_nhds t₀ hδ) ?_
  intro t ht n
  have hdist : dist t t₀ < δ := by
    have h := Metric.mem_ball.mp ht
    simpa [dist_comm] using h
  have hclose' := hclose t₀ t n hdist
  have hpairV :
      (fun p : WeakDual ℝ E × WeakDual ℝ E => p.2 - p.1)
          (toWeak (uSeq n t₀), toWeak (uSeq n t)) ∈ V := by
    simpa [toWeak] using hclose'
  exact hpre hpairV

/-- Simultaneous pointwise weak extraction for a uniformly bounded, weakly equicontinuous family
of continuous paths in a separable real Hilbert space. -/
theorem exists_subseq_weakContinuousPath
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    {uSeq : ℕ → C(PathCompactness.TimeInterval, E)} {M : ℝ} {u₀ : E}
    (hbound : ∀ n t, ‖uSeq n t‖ ≤ M)
    (hinit : ∀ v, Tendsto
      (fun n => inner ℝ (uSeq n ⟨0, by norm_num, by norm_num⟩) v) atTop
        (𝓝 (inner ℝ u₀ v)))
    (hequicont : Equicontinuous
      (fun n t =>
        StrongDual.toWeakDual
          (InnerProductSpace.toDualMap ℝ E (uSeq n t)))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u : PathCompactness.TimeInterval → E,
      (∀ v, Continuous (fun t => inner ℝ (u t) v)) ∧
      (∀ t v, Tendsto (fun n => inner ℝ (uSeq (φ n) t) v) atTop
        (𝓝 (inner ℝ (u t) v))) ∧
      (∀ t, ‖u t‖ ≤ M) ∧ u ⟨0, by norm_num, by norm_num⟩ = u₀ := by
  let toWeak (x : E) : WeakDual ℝ E :=
    StrongDual.toWeakDual (InnerProductSpace.toDualMap ℝ E x)
  let pathSeq : ℕ → C(PathCompactness.TimeInterval, WeakDual ℝ E) := fun n =>
    ⟨fun t => toWeak (uSeq n t), (NormedSpace.Dual.toWeakDual_continuous.comp
      (InnerProductSpace.toDualMap ℝ E).continuous).comp (uSeq n).continuous⟩
  let ball : Set (WeakDual ℝ E) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) M
  have hball_compact : IsCompact ball := by
    simpa [ball] using WeakDual.isCompact_closedBall (0 : StrongDual ℝ E) M
  have hball_closed : IsClosed ball := by
    simpa [ball] using WeakDual.isClosed_closedBall (0 : StrongDual ℝ E) M
  let paths : Set C(PathCompactness.TimeInterval, WeakDual ℝ E) := Set.range pathSeq
  have hpaths_eqcont : ∀ K ∈ {K : Set PathCompactness.TimeInterval | IsCompact K},
      EquicontinuousOn
        (fun p : paths => (p.1 : PathCompactness.TimeInterval → WeakDual ℝ E)) K := by
    intro K hK
    let index : paths → ℕ := fun p => Classical.choose p.2
    have hindex (p : paths) : pathSeq (index p) = p.1 :=
      Classical.choose_spec p.2
    have hcomp := (hequicont.equicontinuousOn K).comp index
    have heq : (fun p : paths => (p.1 : PathCompactness.TimeInterval → WeakDual ℝ E)) =
        fun p => (pathSeq (index p) : PathCompactness.TimeInterval → WeakDual ℝ E) := by
      funext p
      exact congrArg (fun f : C(PathCompactness.TimeInterval, WeakDual ℝ E) =>
        (f : PathCompactness.TimeInterval → WeakDual ℝ E)) (hindex p).symm
    rw [heq]
    exact hcomp
  have hpaths_pointwise : ∀ K ∈ {K : Set PathCompactness.TimeInterval | IsCompact K},
      ∀ t ∈ K, ∃ Q : Set (WeakDual ℝ E), IsCompact Q ∧
        ∀ p ∈ paths, (p.1 : PathCompactness.TimeInterval → WeakDual ℝ E) t ∈ Q := by
    intro K hK t ht
    refine ⟨ball, hball_compact, ?_⟩
    rintro p ⟨n, hpn⟩
    have hval := congrArg (fun f : C(PathCompactness.TimeInterval, WeakDual ℝ E) => f t) hpn
    change p t ∈ ball
    rw [← hval]
    change toWeak (uSeq n t) ∈ ball
    change dist (WeakDual.toStrongDual (toWeak (uSeq n t))) 0 ≤ M
    simpa [toWeak, dist_eq_norm] using hbound n t
  have hpathEmbedding : Topology.IsClosedEmbedding
      (UniformOnFun.ofFun {K : Set PathCompactness.TimeInterval | IsCompact K} ∘
        (fun p : C(PathCompactness.TimeInterval, WeakDual ℝ E) => (p :
            PathCompactness.TimeInterval → WeakDual ℝ E))) := by
    have huniform : IsUniformEmbedding
        (UniformOnFun.ofFun {K : Set PathCompactness.TimeInterval | IsCompact K} ∘
          (fun p : C(PathCompactness.TimeInterval, WeakDual ℝ E) => (p :
              PathCompactness.TimeInterval → WeakDual ℝ E))) := by
      change IsUniformEmbedding
        (ContinuousMap.toUniformOnFunIsCompact :
          C(PathCompactness.TimeInterval, WeakDual ℝ E) →
            UniformOnFun PathCompactness.TimeInterval (WeakDual ℝ E)
              {K : Set PathCompactness.TimeInterval | IsCompact K})
      exact ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact
    have hrange : IsClosed (Set.range
        (UniformOnFun.ofFun {K : Set PathCompactness.TimeInterval | IsCompact K} ∘
          (fun p : C(PathCompactness.TimeInterval, WeakDual ℝ E) => (p :
              PathCompactness.TimeInterval → WeakDual ℝ E)))) := by
      convert UniformOnFun.isClosed_setOfPred_continuous
        (CompactlyCoherentSpace.isCoherentWith (X := PathCompactness.TimeInterval)) using 1
      ext f
      simp only [Set.mem_range]
      constructor
      · rintro ⟨p, rfl⟩
        exact p.continuous
      · intro hf
        refine ⟨⟨f, hf⟩, ?_⟩
        rfl
    exact ⟨huniform.isEmbedding, hrange⟩
  have hcompact : IsCompact (closure paths) :=
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (𝔖_compact := fun K hK => hK) hpathEmbedding hpaths_eqcont hpaths_pointwise
  let pathLimitSet : Set C(PathCompactness.TimeInterval, WeakDual ℝ E) := closure paths
  have hcompactSpace : CompactSpace (↥pathLimitSet) :=
    isCompact_iff_compactSpace.mp hcompact
  have hmetrizable : TopologicalSpace.MetrizableSpace (↥pathLimitSet) := by
    refine @Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating
      ℕ (↥pathLimitSet) (fun _ => ℝ) inferInstance inferInstance inferInstance
      hcompactSpace ?_ ?_ ?_
    · exact fun i p =>
        p.1 (denseSeq PathCompactness.TimeInterval (Nat.unpair i).1)
          (denseSeq E (Nat.unpair i).2)
    · intro i
      exact ((WeakDual.eval_continuous
        (denseSeq E (Nat.unpair i).2)).comp
          (continuous_eval_const
            (denseSeq PathCompactness.TimeInterval (Nat.unpair i).1))).comp
          continuous_subtype_val
    · classical
      intro p q hpq
      by_contra hsep
      push Not at hsep
      have htimes (i : ℕ) : p.1 (denseSeq PathCompactness.TimeInterval i) =
          q.1 (denseSeq PathCompactness.TimeInterval i) := by
        apply DFunLike.ext
        intro v
        have hall (j : ℕ) :
            p.1 (denseSeq PathCompactness.TimeInterval i) (denseSeq E j) =
              q.1 (denseSeq PathCompactness.TimeInterval i) (denseSeq E j) := by
          have hn := hsep (Nat.pair i j)
          simpa [Nat.unpair_pair] using hn
        have heq :
            (p.1 (denseSeq PathCompactness.TimeInterval i) :
              E →L[ℝ] ℝ) =
            (q.1 (denseSeq PathCompactness.TimeInterval i) :
              E →L[ℝ] ℝ) := by
          apply DFunLike.ext'_iff.mpr
          exact (map_continuous _).ext_on
            (denseRange_denseSeq E)
            (map_continuous _) (Set.eqOn_range.mpr (funext hall))
        exact congrFun (DFunLike.ext'_iff.mp heq) v
      have hpathsFun : (p.1 : PathCompactness.TimeInterval → WeakDual ℝ E) = q.1 := by
        apply Continuous.ext_on
          (denseRange_denseSeq PathCompactness.TimeInterval)
          p.1.continuous q.1.continuous
        exact Set.eqOn_range.mpr (funext htimes)
      apply hpq
      exact Subtype.ext (DFunLike.ext'_iff.mpr hpathsFun)
  have hseq_mem (n : ℕ) : pathSeq n ∈ pathLimitSet :=
    subset_closure ⟨n, rfl⟩
  have hfirst : FirstCountableTopology (↥pathLimitSet) := by
    exact @TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology
      (↥pathLimitSet) _ hmetrizable.toPseudoMetrizableSpace
  let xSeq : ℕ → ↥pathLimitSet := fun n => ⟨pathSeq n, hseq_mem n⟩
  let xSeq : ℕ → ↥pathLimitSet := fun n => ⟨pathSeq n, hseq_mem n⟩
  have hsubCompact : IsCompact (Set.univ : Set (↥pathLimitSet)) := isCompact_univ
  obtain ⟨p, hp, φ, hφ, hconv⟩ :=
    @IsCompact.tendsto_subseq (↥pathLimitSet) inferInstance hfirst Set.univ
      xSeq hsubCompact (fun _ => Set.mem_univ _)
  let weakPath : C(PathCompactness.TimeInterval, WeakDual ℝ E) := p.1
  have hconv' : Tendsto (fun n => (xSeq (φ n) : C(PathCompactness.TimeInterval, WeakDual ℝ E)))
      atTop (𝓝 (p : C(PathCompactness.TimeInterval, WeakDual ℝ E))) :=
    continuous_subtype_val.continuousAt.tendsto.comp hconv
  let u : PathCompactness.TimeInterval → E := fun t =>
    (InnerProductSpace.toDual ℝ E).symm
      (WeakDual.toStrongDual (weakPath t))
  have hpair (t : PathCompactness.TimeInterval) (v : E) :
      inner ℝ (u t) v = weakPath t v := by
    simp [u, InnerProductSpace.toDual_symm_apply]
  have hweak (t : PathCompactness.TimeInterval) (v : E) :
      Tendsto (fun n => inner ℝ (uSeq (φ n) t) v) atTop
        (𝓝 (inner ℝ (u t) v)) := by
    have heval : Continuous (fun q : C(PathCompactness.TimeInterval, WeakDual ℝ E) => q t v) :=
      (WeakDual.eval_continuous v).comp (continuous_eval_const t)
    have h := heval.continuousAt.tendsto.comp hconv'
    have h' : Tendsto (fun n => pathSeq (φ n) t v) atTop (𝓝 (weakPath t v)) := by
      simpa [xSeq, weakPath, Function.comp_def] using h
    have hseq : (fun n => inner ℝ (uSeq (φ n) t) v) =
        fun n => pathSeq (φ n) t v := by
      funext n
      simp [pathSeq, toWeak, InnerProductSpace.toDualMap_apply_apply,
        StrongDual.toWeakDual_apply]
    rw [hseq]
    simpa [hpair] using h'
  have hboundLimit : ∀ t, ‖u t‖ ≤ M := by
    intro t
    have hmem : weakPath t ∈ ball := by
      have hclosedEval : IsClosed {q : C(PathCompactness.TimeInterval, WeakDual ℝ E) | q t ∈ ball}
          :=
        hball_closed.preimage (continuous_eval_const t)
      have hpathsEval : paths ⊆ {q : C(PathCompactness.TimeInterval, WeakDual ℝ E) | q t ∈ ball}
          := by
        rintro q ⟨n, rfl⟩
        change toWeak (uSeq n t) ∈ ball
        change dist (WeakDual.toStrongDual (toWeak (uSeq n t))) 0 ≤ M
        simpa [toWeak, dist_eq_norm] using hbound n t
      have hpcl : p.1 ∈ closure paths := p.2
      exact closure_minimal hpathsEval hclosedEval hpcl
    have hnormDual : ‖WeakDual.toStrongDual (weakPath t)‖ ≤ M := by
      have := hmem
      change dist (WeakDual.toStrongDual (weakPath t)) 0 ≤ M at this
      simpa [dist_eq_norm] using this
    have hnorm : ‖u t‖ = ‖WeakDual.toStrongDual (weakPath t)‖ := by
      dsimp [u]
      exact (InnerProductSpace.toDual ℝ E).symm.norm_map _
    exact hnorm ▸ hnormDual
  have hcont : ∀ v, Continuous (fun t => inner ℝ (u t) v) := by
    intro v
    have h := (WeakDual.eval_continuous v).comp weakPath.continuous
    apply h.congr
    intro t
    exact (hpair t v).symm
  let t₀ : PathCompactness.TimeInterval := ⟨0, by norm_num, by norm_num⟩
  have htrace : u t₀ = u₀ :=
    pointwiseWeakLimit_preserves_weak_initial t₀
      (fun v => (hinit v).comp (StrictMono.tendsto_atTop hφ))
      (fun v => hweak t₀ v)
  exact ⟨φ, hφ, u, hcont, hweak, hboundLimit, htrace⟩

/-- The weak path and initial-trace extraction with scalar moduli only on a dense test family.
This is the compactness interface suited to Fourier Galerkin equations: the equation controls each
fixed trigonometric test, while the uniform `L²` bound extends the modulus to all tests. -/
theorem exists_subseq_weakContinuousPath_of_dense_pairing_moduli
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    {uSeq : ℕ → C(PathCompactness.TimeInterval, E)} {M : ℝ} {u₀ : E} {S : Set E}
    (hbound : ∀ n t, ‖uSeq n t‖ ≤ M)
    (hinit : ∀ v, Tendsto
      (fun n => inner ℝ (uSeq n ⟨0, by norm_num, by norm_num⟩) v) atTop
        (𝓝 (inner ℝ u₀ v)))
    (hM : 0 ≤ M)
    (happrox : ∀ v : E, ∀ ε : ℝ, 0 < ε → ∃ w ∈ S, dist v w < ε)
    (hmod : ∀ w ∈ S, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n t s,
        |inner ℝ (uSeq n t) w - inner ℝ (uSeq n s) w| ≤ C * Real.sqrt (dist t s)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u : PathCompactness.TimeInterval → E,
      (∀ v, Continuous (fun t => inner ℝ (u t) v)) ∧
      (∀ t v, Tendsto (fun n => inner ℝ (uSeq (φ n) t) v) atTop
        (𝓝 (inner ℝ (u t) v))) ∧
      (∀ t, ‖u t‖ ≤ M) ∧ u ⟨0, by norm_num, by norm_num⟩ = u₀ := by
  have hequicont := weakDual_equicontinuous_of_dense_pairing_moduli
    hM (fun n t => hbound n t) happrox hmod
  exact exists_subseq_weakContinuousPath hbound hinit hequicont

end WeakUniformity

end AVenhance.Infra.Parabolic.FourierGalerkin

end
