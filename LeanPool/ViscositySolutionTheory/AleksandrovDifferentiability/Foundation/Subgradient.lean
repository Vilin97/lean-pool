/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Convex subgradients

This file records the project-local subgradient predicate for real-valued convex functions on an
inner product space.
-/

@[expose] public section

namespace AleksandrovDifferentiability

open Asymptotics
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section ClosedConvexHull

/-- A uniform closed-ball estimate is preserved by convex combinations and by taking closure.

This is the elementary closed-convex-hull step used in the source proof when passing from limits
of gradients at differentiability points to arbitrary subgradients. The separate convex-analysis
density theorem should provide the hypothesis `p ∈ closure (convexHull ℝ s)`. -/
theorem norm_sub_le_of_mem_closure_convexHull_norm_sub_le
    {s : Set E} {a p : E} {R : ℝ}
    (hs : ∀ q ∈ s, ‖q - a‖ ≤ R) (hp : p ∈ closure (convexHull ℝ s)) :
    ‖p - a‖ ≤ R := by
  have hsball : s ⊆ Metric.closedBall a R := by
    intro q hq
    simpa [Metric.mem_closedBall, dist_eq_norm] using hs q hq
  have hconv : convexHull ℝ s ⊆ Metric.closedBall a R :=
    convexHull_min hsball (convex_closedBall a R)
  have hclosed : closure (convexHull ℝ s) ⊆ Metric.closedBall a R :=
    closure_minimal hconv Metric.isClosed_closedBall
  simpa [Metric.mem_closedBall, dist_eq_norm] using hclosed hp

/-- Image form of `norm_sub_le_of_mem_closure_convexHull_norm_sub_le`.

This is the form used in the subgradient-extension step: once a convex-analysis density theorem
places a subgradient in the closed convex hull of nearby gradient values, any uniform norm
estimate on those gradient values passes to the subgradient. -/
theorem norm_sub_le_of_mem_closure_convexHull_image_norm_sub_le
    {ι : Type*} {t : Set ι} {g : ι → E} {a p : E} {R : ℝ}
    (hg : ∀ q ∈ t, ‖g q - a‖ ≤ R)
    (hp : p ∈ closure (convexHull ℝ (g '' t))) :
    ‖p - a‖ ≤ R := by
  refine norm_sub_le_of_mem_closure_convexHull_norm_sub_le ?_ hp
  intro q hq
  rcases hq with ⟨y, hy, rfl⟩
  exact hg y hy

/-- Closed-convex-hull membership from all closed halfspace tests.

This is the separation-theorem half of the remaining finite-dimensional subgradient
cluster-density input. To prove that a subgradient lies in the closed convex hull of cluster
gradients, it is enough to show that every linear inequality true on the cluster gradients is
true for the subgradient. -/
theorem mem_closure_convexHull_of_forall_inner_le
    [CompleteSpace E] {s : Set E} {p : E}
    (hhalfspace : ∀ z : E, ∀ c : ℝ,
      (∀ q ∈ s, inner ℝ q z ≤ c) → inner ℝ p z ≤ c) :
    p ∈ closure (convexHull ℝ s) := by
  by_contra hp
  rcases geometric_hahn_banach_closed_point
      ((convex_convexHull ℝ s).closure) isClosed_closure hp with
    ⟨φ, c, hφ_on, hp_lt⟩
  let z : E := (InnerProductSpace.toDual ℝ E).symm φ
  have hs_le : ∀ q ∈ s, inner ℝ q z ≤ c := by
    intro q hq
    have hq_closure : q ∈ closure (convexHull ℝ s) :=
      subset_closure ((subset_convexHull (𝕜 := ℝ) s) hq)
    have hφq_lt : φ q < c := hφ_on q hq_closure
    have hφq_eq : φ q = inner ℝ q z := by
      have hdual : inner ℝ z q = φ q := by
        simp [z]
      rw [← hdual, real_inner_comm q z]
    simpa [hφq_eq] using hφq_lt.le
  have hp_le : inner ℝ p z ≤ c := hhalfspace z c hs_le
  have hp_gt : c < inner ℝ p z := by
    have hφp_eq : φ p = inner ℝ p z := by
      have hdual : inner ℝ z p = φ p := by
        simp [z]
      rw [← hdual, real_inner_comm p z]
    simpa [hφp_eq] using hp_lt
  exact hp_gt.not_ge hp_le

end ClosedConvexHull

/-- `p` is a subgradient of `u` at `x`, relative to the set `s`.

This is the supporting-hyperplane-from-below formulation used in the convex specialization of the
Aleksandrov proof.
-/
def SubgradientOn (s : Set E) (u : E → ℝ) (x p : E) : Prop :=
  x ∈ s ∧ ∀ y ∈ s, u x + inner ℝ p (y - x) ≤ u y

theorem SubgradientOn.mem {s : Set E} {u : E → ℝ} {x p : E}
    (hp : SubgradientOn s u x p) :
    x ∈ s :=
  hp.1

theorem SubgradientOn.supporting_inequality {s : Set E} {u : E → ℝ} {x p y : E}
    (hp : SubgradientOn s u x p) (hy : y ∈ s) :
    u x + inner ℝ p (y - x) ≤ u y :=
  hp.2 y hy

/-- The subgradients of `u` at a fixed point form a convex set. -/
theorem SubgradientOn.smul_add_smul
    {s : Set E} {u : E → ℝ} {x p₀ p₁ : E} {a b : ℝ}
    (hp₀ : SubgradientOn s u x p₀) (hp₁ : SubgradientOn s u x p₁)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    SubgradientOn s u x (a • p₀ + b • p₁) := by
  refine ⟨hp₀.mem, ?_⟩
  intro y hy
  have h₀ := hp₀.supporting_inequality hy
  have h₁ := hp₁.supporting_inequality hy
  have hcombo :=
    add_le_add (mul_le_mul_of_nonneg_left h₀ ha) (mul_le_mul_of_nonneg_left h₁ hb)
  calc
    u x + inner ℝ (a • p₀ + b • p₁) (y - x)
        = a * (u x + inner ℝ p₀ (y - x)) +
            b * (u x + inner ℝ p₁ (y - x)) := by
          rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
          have hb_eq : b = 1 - a := by linarith
          rw [hb_eq]
          ring
    _ ≤ a * u y + b * u y := hcombo
    _ = u y := by
      rw [← add_mul, hab, one_mul]

/-- Set-valued form of convexity of the subdifferential at a fixed point. -/
theorem convex_setOf_subgradientOn
    {s : Set E} {u : E → ℝ} {x : E} :
    Convex ℝ {p : E | SubgradientOn s u x p} := by
  intro p₀ hp₀ p₁ hp₁ a b ha hb hab
  exact hp₀.smul_add_smul hp₁ ha hb hab

/-- The subdifferential at a fixed point is closed.

If `x ∉ s`, the subdifferential is empty. If `x ∈ s`, it is the intersection over `y ∈ s` of
the closed half-spaces expressing the supporting inequalities. -/
theorem isClosed_setOf_subgradientOn
    {s : Set E} {u : E → ℝ} {x : E} :
    IsClosed {p : E | SubgradientOn s u x p} := by
  by_cases hx : x ∈ s
  · have hset :
        {p : E | SubgradientOn s u x p} =
          ⋂ y : E, ⋂ _hy : y ∈ s,
            {p : E | u x + inner ℝ p (y - x) ≤ u y} := by
      ext p
      simp [SubgradientOn, hx]
    rw [hset]
    refine isClosed_iInter fun y => isClosed_iInter fun hy => ?_
    exact isClosed_le (by fun_prop) continuous_const
  · have hset : {p : E | SubgradientOn s u x p} = ∅ := by
      ext p
      simp [SubgradientOn, hx]
    rw [hset]
    exact isClosed_empty

/-- Closed-graph form of the subgradient inequality along a convergent filter.

If base points `xs` converge to `x`, slopes `ps` converge to `p`, the function values
`u (xs i)` converge to `u x`, and eventually `ps i` is a subgradient at `xs i`, then `p` is a
subgradient at `x`. This is the local finite-valued version of the closedness of the
subdifferential graph used in Rockafellar 25.6. -/
theorem SubgradientOn.of_tendsto
    {ι : Type*} {l : Filter ι} [Filter.NeBot l] {s : Set E} {u : E → ℝ}
    {x p : E} {xs ps : ι → E}
    (hx : x ∈ s)
    (hxs : Filter.Tendsto xs l (𝓝 x))
    (hps : Filter.Tendsto ps l (𝓝 p))
    (hu : Filter.Tendsto (fun i => u (xs i)) l (𝓝 (u x)))
    (hsub : ∀ᶠ i in l, SubgradientOn s u (xs i) (ps i)) :
    SubgradientOn s u x p := by
  refine ⟨hx, ?_⟩
  intro z hz
  have hleft :
      Filter.Tendsto
        (fun i => u (xs i) + inner ℝ (ps i) (z - xs i)) l
        (𝓝 (u x + inner ℝ p (z - x))) := by
    exact hu.add (hps.inner (tendsto_const_nhds.sub hxs))
  have hright :
      Filter.Tendsto (fun _ : ι => u z) l (𝓝 (u z)) :=
    tendsto_const_nhds
  have hle :
      (fun i => u (xs i) + inner ℝ (ps i) (z - xs i)) ≤ᶠ[l]
        (fun _ : ι => u z) := by
    filter_upwards [hsub] with i hi
    exact hi.supporting_inequality hz
  exact le_of_tendsto_of_tendsto hleft hright hle

/-- Closed-graph form of the subgradient inequality when continuity of `u` at the limit point
supplies convergence of the function values. -/
theorem SubgradientOn.of_tendsto_of_continuousAt
    {ι : Type*} {l : Filter ι} [Filter.NeBot l] {s : Set E} {u : E → ℝ}
    {x p : E} {xs ps : ι → E}
    (hx : x ∈ s)
    (hxs : Filter.Tendsto xs l (𝓝 x))
    (hps : Filter.Tendsto ps l (𝓝 p))
    (hu : ContinuousAt u x)
    (hsub : ∀ᶠ i in l, SubgradientOn s u (xs i) (ps i)) :
    SubgradientOn s u x p :=
  SubgradientOn.of_tendsto hx hxs hps (hu.tendsto.comp hxs) hsub

/-- A bounded subdifferential is compact in a proper space.

For the finite-dimensional endpoint-attainment argument, `ProperSpace E` is supplied by
finite-dimensionality. The separate convex-analysis input is local boundedness of subgradients. -/
theorem isCompact_setOf_subgradientOn_of_isBounded
    [ProperSpace E] {s : Set E} {u : E → ℝ} {x : E}
    (hb : Bornology.IsBounded {p : E | SubgradientOn s u x p}) :
    IsCompact {p : E | SubgradientOn s u x p} :=
  Metric.isCompact_of_isClosed_isBounded isClosed_setOf_subgradientOn hb

/-- A bounded nonempty subdifferential has a maximizer for every directional pairing. -/
theorem exists_isMaxOn_inner_subgradientOn_of_isBounded
    [ProperSpace E] {s : Set E} {u : E → ℝ} {x : E} (z : E)
    (hne : {p : E | SubgradientOn s u x p}.Nonempty)
    (hb : Bornology.IsBounded {p : E | SubgradientOn s u x p}) :
    ∃ p : E, SubgradientOn s u x p ∧
      IsMaxOn (fun q : E => inner ℝ q z) {q : E | SubgradientOn s u x q} p := by
  have hK : IsCompact {p : E | SubgradientOn s u x p} :=
    isCompact_setOf_subgradientOn_of_isBounded (s := s) (u := u) (x := x) hb
  have hcont : ContinuousOn (fun q : E => inner ℝ q z) {q : E | SubgradientOn s u x q} :=
    (continuous_id.inner continuous_const).continuousOn
  rcases hK.exists_isMaxOn hne hcont with
    ⟨p, hp, hpmax⟩
  exact ⟨p, hp, hpmax⟩

/-- A bounded nonempty subdifferential has a minimizer for every directional pairing. -/
theorem exists_isMinOn_inner_subgradientOn_of_isBounded
    [ProperSpace E] {s : Set E} {u : E → ℝ} {x : E} (z : E)
    (hne : {p : E | SubgradientOn s u x p}.Nonempty)
    (hb : Bornology.IsBounded {p : E | SubgradientOn s u x p}) :
    ∃ p : E, SubgradientOn s u x p ∧
      IsMinOn (fun q : E => inner ℝ q z) {q : E | SubgradientOn s u x q} p := by
  have hK : IsCompact {p : E | SubgradientOn s u x p} :=
    isCompact_setOf_subgradientOn_of_isBounded (s := s) (u := u) (x := x) hb
  have hcont : ContinuousOn (fun q : E => inner ℝ q z) {q : E | SubgradientOn s u x q} :=
    (continuous_id.inner continuous_const).continuousOn
  rcases hK.exists_isMinOn hne hcont with
    ⟨p, hp, hpmin⟩
  exact ⟨p, hp, hpmin⟩

/-- First-order linearization of all nearby subgradients.

The two set parameters intentionally play different roles. In the source proof, subgradients are
taken relative to the larger convex domain `Q_3`, while the base point is approached through the
smaller working region `Q_{3/2}`. -/
def HasSubgradientLinearizationOnAt
    (domain approach : Set E) (u : E → ℝ) (x p₀ : E) (B : E →L[ℝ] E) : Prop :=
  ∀ ε > 0, ∀ᶠ y in 𝓝[approach] x,
    ∀ p : E, SubgradientOn domain u y p →
      ‖p - (p₀ + B (y - x))‖ ≤ ε * ‖y - x‖

namespace HasSubgradientLinearizationOnAt

/-- Extend subgradient linearization from a punctured approach set to the full approach set when
the base-point subgradients are all equal to the model slope. -/
theorem of_punctured_of_base
    {domain approach : Set E} {u : E → ℝ} {x p₀ : E} {B : E →L[ℝ] E}
    (hpunctured :
      HasSubgradientLinearizationOnAt domain (approach \ {x}) u x p₀ B)
    (hbase : ∀ p : E, SubgradientOn domain u x p → p = p₀) :
    HasSubgradientLinearizationOnAt domain approach u x p₀ B := by
  intro ε hε
  have hpunctured_ev := hpunctured ε hε
  rw [eventually_nhdsWithin_iff] at hpunctured_ev ⊢
  filter_upwards [hpunctured_ev] with y hy hyapproach p hp
  by_cases hyx : y = x
  · subst y
    have hp_eq : p = p₀ := hbase p hp
    subst p
    simp
  · exact hy ⟨hyapproach, by simpa using hyx⟩ p hp

/-- Cluster values of an auxiliary slope map `G` along the differentiability/approach set `D`.

In the source proof, `G` is the Fréchet gradient and `D` is the set of differentiability points.
Thus `GradientClusterSet D G y` is the set of all limits of gradients along points
`w ∈ D` with `w -> y`. -/
def GradientClusterSet (D : Set E) (G : E → E) (y : E) : Set E :=
  {q | MapClusterPt q (𝓝[D] y) G}

omit [InnerProductSpace ℝ E] in
/-- Enlarging the approach set enlarges the gradient cluster set. -/
theorem GradientClusterSet.mono
    {D₁ D₂ : Set E} {G : E → E} {y : E}
    (hD : D₁ ⊆ D₂) :
    GradientClusterSet D₁ G y ⊆ GradientClusterSet D₂ G y := by
  intro q hq
  exact MapClusterPt.mono hq (nhdsWithin_mono y hD)

/-- Closed-convex-hull membership of gradient cluster values is monotone in the approach set. -/
theorem GradientClusterSet.mem_closure_convexHull_mono
    {D₁ D₂ : Set E} {G : E → E} {y p : E}
    (hD : D₁ ⊆ D₂)
    (hp : p ∈ closure (convexHull ℝ (GradientClusterSet D₁ G y))) :
    p ∈ closure (convexHull ℝ (GradientClusterSet D₂ G y)) :=
  closure_mono (convexHull_mono (GradientClusterSet.mono hD)) hp

omit [InnerProductSpace ℝ E] in
/-- A point of the approach set contributes its own value as a cluster value.

This uses the non-punctured ambient filter `𝓝[D] y`: the point `y` itself belongs to every
neighborhood within `D`, so no continuity of `G` is required. -/
theorem GradientClusterSet.mem_of_mem
    {D : Set E} {G : E → E} {y : E} (hy : y ∈ D) :
    G y ∈ GradientClusterSet D G y := by
  rw [GradientClusterSet, Set.mem_ofPred_eq, mapClusterPt_def]
  have hmap : Filter.map G (pure y) ≤ Filter.map G (𝓝[D] y) :=
    Filter.map_mono (m := G) (pure_le_nhdsWithin hy)
  have hpure : ClusterPt (G y) (Filter.map G (pure y)) := by
    simpa using
      (ClusterPt.of_le_nhds (pure_le_nhds (G y)) :
        ClusterPt (G y) (pure (G y)))
  exact hpure.mono hmap

omit [InnerProductSpace ℝ E] in
/-- A genuine limit along the within-filter is, in particular, a cluster value.

This is the filter-level form of the exposed-point step in Rockafellar 25.6: once nearby
differentiability gradients are shown to converge to an exposed subgradient, that subgradient
belongs to the corresponding gradient cluster set. -/
theorem GradientClusterSet.mem_of_tendsto
    {D : Set E} {G : E → E} {y q : E}
    (hne : (𝓝[D] y).NeBot) (hG : Filter.Tendsto G (𝓝[D] y) (𝓝 q)) :
    q ∈ GradientClusterSet D G y := by
  rw [GradientClusterSet, Set.mem_ofPred_eq, mapClusterPt_def]
  exact ClusterPt.of_le_nhds hG

omit [InnerProductSpace ℝ E] in
/-- If `G` is eventually in every ball around `q` along the within-filter, then `q` is a cluster
value. -/
theorem GradientClusterSet.mem_of_eventually_mem_ball
    {D : Set E} {G : E → E} {y q : E}
    (hne : (𝓝[D] y).NeBot)
    (hball : ∀ ε > 0, ∀ᶠ w in 𝓝[D] y, G w ∈ Metric.ball q ε) :
    q ∈ GradientClusterSet D G y := by
  refine GradientClusterSet.mem_of_tendsto hne ?_
  rw [Metric.tendsto_nhds]
  intro ε hε
  exact hball ε hε

omit [InnerProductSpace ℝ E] in
/-- Norm-estimate version of `GradientClusterSet.mem_of_eventually_mem_ball`.

This is the final metric step in the exposed-point part of Rockafellar 25.6: once
outer semicontinuity forces nearby differentiability gradients to satisfy
`‖G w - q‖ < ε` for every `ε > 0`, the exposed subgradient `q` is a gradient cluster value. -/
theorem GradientClusterSet.mem_of_eventually_norm_sub_lt
    {D : Set E} {G : E → E} {y q : E}
    (hne : (𝓝[D] y).NeBot)
    (hnorm : ∀ ε > 0, ∀ᶠ w in 𝓝[D] y, ‖G w - q‖ < ε) :
    q ∈ GradientClusterSet D G y := by
  refine GradientClusterSet.mem_of_eventually_mem_ball hne ?_
  intro ε hε
  filter_upwards [hnorm ε hε] with w hw
  simpa [Metric.mem_ball, dist_eq_norm] using hw

/-- A point of the approach set belongs to the closed convex hull of the corresponding
cluster-value set through its own value. -/
theorem GradientClusterSet.mem_closure_convexHull_of_mem
    {D : Set E} {G : E → E} {y : E} (hy : y ∈ D) :
    G y ∈ closure (convexHull ℝ (GradientClusterSet D G y)) :=
  subset_closure
    ((subset_convexHull (𝕜 := ℝ) (GradientClusterSet D G y))
      (GradientClusterSet.mem_of_mem hy))

omit [InnerProductSpace ℝ E] in
/-- A cluster value along a parameterization whose image tends to `y` through `D` is an ambient
gradient cluster value at `y`. -/
theorem GradientClusterSet.mem_of_mapClusterPt
    {ι : Type*} {l : Filter ι} {D : Set E} {G : E → E} {y q : E} {φ : ι → E}
    (hφ : Filter.Tendsto φ l (𝓝[D] y)) (hq : MapClusterPt q l (fun a => G (φ a))) :
    q ∈ GradientClusterSet D G y :=
  hq.of_comp hφ

/-- Cluster values along an affine line, restricted to parameters whose images lie in `D`, are
ambient gradient cluster values. -/
theorem GradientClusterSet.mem_of_lineMapClusterPt
    {D : Set E} {G : E → E} {y z q : E}
    (hq : MapClusterPt q (𝓝[{t : ℝ | y + t • z ∈ D}] (0 : ℝ))
      (fun t : ℝ => G (y + t • z))) :
    q ∈ GradientClusterSet D G y := by
  refine GradientClusterSet.mem_of_mapClusterPt ?_ hq
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcont : ContinuousAt (fun t : ℝ => y + t • z) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  · exact eventually_mem_nhdsWithin

/-- Positive-line version of `GradientClusterSet.mem_of_lineMapClusterPt`. -/
theorem GradientClusterSet.mem_of_posLineMapClusterPt
    {D : Set E} {G : E → E} {y z q : E}
    (hq : MapClusterPt q (𝓝[{t : ℝ | 0 < t ∧ y + t • z ∈ D}] (0 : ℝ))
      (fun t : ℝ => G (y + t • z))) :
    q ∈ GradientClusterSet D G y := by
  refine GradientClusterSet.mem_of_mapClusterPt ?_ hq
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcont : ContinuousAt (fun t : ℝ => y + t • z) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [eventually_mem_nhdsWithin] with t ht
    exact ht.2

/-- Cluster-density from halfspace tests on the gradient cluster set.

This is the separation reduction for the remaining convex-analysis input: to prove a subgradient
belongs to the closed convex hull of the gradient cluster values, it suffices to prove every
linear upper bound valid for all cluster values is valid for that subgradient. -/
theorem mem_closure_convexHull_gradientClusterSet_of_forall_inner_le
    [CompleteSpace E] {D : Set E} {G : E → E} {y p : E}
    (hhalfspace : ∀ z : E, ∀ c : ℝ,
      (∀ q ∈ GradientClusterSet D G y, inner ℝ q z ≤ c) → inner ℝ p z ≤ c) :
    p ∈ closure (convexHull ℝ (GradientClusterSet D G y)) :=
  mem_closure_convexHull_of_forall_inner_le hhalfspace

/-- Eventual version of the halfspace-test reduction for the subgradient cluster-density
hypothesis used in the Aleksandrov proof. -/
theorem eventually_mem_closure_convexHull_gradientClusterSet_of_forall_inner_le
    [CompleteSpace E] {domain D approach : Set E} {u : E → ℝ} {G : E → E} {x : E}
    (hhalfspace : ∀ᶠ y in 𝓝[approach] x,
      ∀ p : E, SubgradientOn domain u y p →
        ∀ z : E, ∀ c : ℝ,
          (∀ q ∈ GradientClusterSet D G y, inner ℝ q z ≤ c) → inner ℝ p z ≤ c) :
    ∀ᶠ y in 𝓝[approach] x,
      ∀ p : E, SubgradientOn domain u y p →
        p ∈ closure (convexHull ℝ (GradientClusterSet D G y)) := by
  filter_upwards [hhalfspace] with y hy p hp
  exact mem_closure_convexHull_gradientClusterSet_of_forall_inner_le (hy p hp)

/-- Short alias for the halfspace-test form of the subgradient cluster-density hypothesis. -/
theorem clusterDensity_of_eventually_forall_inner_le
    [CompleteSpace E] {domain D approach : Set E} {u : E → ℝ} {G : E → E} {x : E}
    (hhalfspace : ∀ᶠ y in 𝓝[approach] x,
      ∀ p : E, SubgradientOn domain u y p →
        ∀ z : E, ∀ c : ℝ,
          (∀ q ∈ GradientClusterSet D G y, inner ℝ q z ≤ c) → inner ℝ p z ≤ c) :
    ∀ᶠ y in 𝓝[approach] x,
      ∀ p : E, SubgradientOn domain u y p →
        p ∈ closure (convexHull ℝ (GradientClusterSet D G y)) :=
  eventually_mem_closure_convexHull_gradientClusterSet_of_forall_inner_le hhalfspace

/-- A directional cluster value dominating `p` transfers cluster halfspace bounds to `p`. -/
theorem inner_le_of_exists_cluster_inner_ge
    {D : Set E} {G : E → E} {y p z : E} {c : ℝ}
    (hdom : ∃ q ∈ GradientClusterSet D G y, inner ℝ p z ≤ inner ℝ q z)
    (hbound : ∀ q ∈ GradientClusterSet D G y, inner ℝ q z ≤ c) :
    inner ℝ p z ≤ c := by
  rcases hdom with ⟨q, hq, hpq⟩
  exact hpq.trans (hbound q hq)

/-- Directional dominating cluster values imply the halfspace-test form of cluster density. -/
theorem clusterHalfspace_of_forall_exists_cluster_inner_ge
    {domain D : Set E} {u : E → ℝ} {G : E → E} {y : E}
    (hdom : ∀ p : E, SubgradientOn domain u y p →
      ∀ z : E, ∃ q ∈ GradientClusterSet D G y, inner ℝ p z ≤ inner ℝ q z) :
    ∀ p : E, SubgradientOn domain u y p →
      ∀ z : E, ∀ c : ℝ,
        (∀ q ∈ GradientClusterSet D G y, inner ℝ q z ≤ c) → inner ℝ p z ≤ c := by
  intro p hp z c hbound
  exact inner_le_of_exists_cluster_inner_ge (hdom p hp z) hbound

/-- Eventual version of
`HasSubgradientLinearizationOnAt.clusterHalfspace_of_forall_exists_cluster_inner_ge`. -/
theorem eventually_clusterHalfspace_of_eventually_directional_dominating_cluster
    {domain D approach : Set E} {u : E → ℝ} {G : E → E} {x : E}
    (hdom : ∀ᶠ y in 𝓝[approach] x,
      ∀ p : E, SubgradientOn domain u y p →
        ∀ z : E, ∃ q ∈ GradientClusterSet D G y, inner ℝ p z ≤ inner ℝ q z) :
    ∀ᶠ y in 𝓝[approach] x,
      ∀ p : E, SubgradientOn domain u y p →
        ∀ z : E, ∀ c : ℝ,
          (∀ q ∈ GradientClusterSet D G y, inner ℝ q z ≤ c) → inner ℝ p z ≤ c := by
  filter_upwards [hdom] with y hy
  exact clusterHalfspace_of_forall_exists_cluster_inner_ge hy

/-- Directional dominating cluster values imply the closed-convex-hull cluster-density
hypothesis used by the Aleksandrov proof. -/
theorem clusterDensity_of_eventually_directional_dominating_cluster
    [CompleteSpace E] {domain D approach : Set E} {u : E → ℝ} {G : E → E} {x : E}
    (hdom : ∀ᶠ y in 𝓝[approach] x,
      ∀ p : E, SubgradientOn domain u y p →
        ∀ z : E, ∃ q ∈ GradientClusterSet D G y, inner ℝ p z ≤ inner ℝ q z) :
    ∀ᶠ y in 𝓝[approach] x,
      ∀ p : E, SubgradientOn domain u y p →
        p ∈ closure (convexHull ℝ (GradientClusterSet D G y)) :=
  clusterDensity_of_eventually_forall_inner_le
    (eventually_clusterHalfspace_of_eventually_directional_dominating_cluster hdom)

/-- Eventual estimates for nearby gradient values pass to cluster gradient values.

This is the formal closed-set passage in the source proof: after proving an estimate for
`G w` for all `w` sufficiently close to `y` through `D`, the same estimate holds for every
cluster value `q = lim G w`. -/
theorem cluster_slope_estimates_of_eventually_gradient_estimates
    {D approach : Set E} {G : E → E} {x p₀ : E} {B : E →L[ℝ] E}
    (hgradient : ∀ ε > 0, ∀ᶠ y in 𝓝[approach] x,
      ∀ᶠ w in 𝓝[D] y,
        ‖G w - (p₀ + B (y - x))‖ ≤ ε * ‖y - x‖) :
    ∀ ε > 0, ∀ᶠ y in 𝓝[approach] x,
      ∀ q ∈ GradientClusterSet D G y,
        ‖q - (p₀ + B (y - x))‖ ≤ ε * ‖y - x‖ := by
  intro ε hε
  filter_upwards [hgradient ε hε] with y hy q hq
  let a : E := p₀ + B (y - x)
  let R : ℝ := ε * ‖y - x‖
  have hclosed : IsClosed (Metric.closedBall a R) := Metric.isClosed_closedBall
  have hmem : q ∈ Metric.closedBall a R := by
    refine hclosed.mem_of_mapClusterPt hq ?_
    filter_upwards [hy] with w hw
    simpa [a, R, Metric.mem_closedBall, dist_eq_norm] using hw
  simpa [a, R, Metric.mem_closedBall, dist_eq_norm] using hmem

/-- Closed-convex-hull transfer from cluster gradients to all nearby subgradients.

This is the source subgradient-extension argument after the finite-dimensional density theorem:
if every nearby subgradient belongs to the closed convex hull of the gradient cluster set, and
the cluster gradients satisfy the linearization estimate, then all nearby subgradients satisfy
the same estimate. -/
theorem of_gradient_clusterSet_of_eventually_mem_closure_convexHull
    {domain D approach : Set E} {u : E → ℝ} {G : E → E} {x p₀ : E}
    {B : E →L[ℝ] E}
    (hcluster : ∀ ε > 0, ∀ᶠ y in 𝓝[approach] x,
      ∀ q ∈ GradientClusterSet D G y,
        ‖q - (p₀ + B (y - x))‖ ≤ ε * ‖y - x‖)
    (hsubgradients : ∀ᶠ y in 𝓝[approach] x,
      ∀ p : E, SubgradientOn domain u y p →
        p ∈ closure (convexHull ℝ (GradientClusterSet D G y))) :
    HasSubgradientLinearizationOnAt domain approach u x p₀ B := by
  intro ε hε
  filter_upwards [hcluster ε hε, hsubgradients] with y hcluster_y hsubgradients_y p hp
  exact
    norm_sub_le_of_mem_closure_convexHull_norm_sub_le
      (a := p₀ + B (y - x)) (p := p) (R := ε * ‖y - x‖)
      hcluster_y (hsubgradients_y p hp)

/-- Source-shaped subgradient extension using cluster gradients.

This combines the closed-set passage to cluster gradient values with the closed-convex-hull
density input for subgradients. -/
theorem of_eventually_gradient_estimates_of_cluster_convexHull
    {domain D approach : Set E} {u : E → ℝ} {G : E → E} {x p₀ : E}
    {B : E →L[ℝ] E}
    (hgradient : ∀ ε > 0, ∀ᶠ y in 𝓝[approach] x,
      ∀ᶠ w in 𝓝[D] y,
        ‖G w - (p₀ + B (y - x))‖ ≤ ε * ‖y - x‖)
    (hsubgradients : ∀ᶠ y in 𝓝[approach] x,
      ∀ p : E, SubgradientOn domain u y p →
        p ∈ closure (convexHull ℝ (GradientClusterSet D G y))) :
    HasSubgradientLinearizationOnAt domain approach u x p₀ B :=
  of_gradient_clusterSet_of_eventually_mem_closure_convexHull
    (cluster_slope_estimates_of_eventually_gradient_estimates hgradient)
    hsubgradients

/-- Punctured source-shaped subgradient extension using cluster gradients, with the base point
handled separately by uniqueness of the subgradient at `x`. -/
theorem of_punctured_eventually_gradient_estimates_of_cluster_convexHull
    {domain D approach : Set E} {u : E → ℝ} {G : E → E} {x p₀ : E}
    {B : E →L[ℝ] E}
    (hgradient : ∀ ε > 0, ∀ᶠ y in 𝓝[approach \ {x}] x,
      ∀ᶠ w in 𝓝[D] y,
        ‖G w - (p₀ + B (y - x))‖ ≤ ε * ‖y - x‖)
    (hsubgradients : ∀ᶠ y in 𝓝[approach \ {x}] x,
      ∀ p : E, SubgradientOn domain u y p →
        p ∈ closure (convexHull ℝ (GradientClusterSet D G y)))
    (hbase : ∀ p : E, SubgradientOn domain u x p → p = p₀) :
    HasSubgradientLinearizationOnAt domain approach u x p₀ B :=
  of_punctured_of_base
    (of_eventually_gradient_estimates_of_cluster_convexHull
      (domain := domain) (D := D) (approach := approach \ {x})
      (u := u) (G := G) (x := x) (p₀ := p₀) (B := B)
      hgradient hsubgradients)
    hbase

/-- Convert a gradient little-o expansion at `x` into the moving-base estimates used by the
cluster-gradient subgradient extension.

For a nearby point `y ≠ x`, the estimate for `G w - p₀ - B (w - x)` is applied with
`w -> y` through `D`, while continuity of `B` controls the replacement of `B (w - x)` by
`B (y - x)`. -/
theorem eventually_gradient_estimates_of_isLittleO
    {D approach : Set E} {G : E → E} {x p₀ : E} {B : E →L[ℝ] E}
    (hgrad :
      (fun w : E => G w - p₀ - B (w - x)) =o[𝓝[D] x]
        fun w : E => ‖w - x‖) :
    ∀ ε > 0, ∀ᶠ y in 𝓝[approach \ {x}] x,
      ∀ᶠ w in 𝓝[D] y,
        ‖G w - (p₀ + B (y - x))‖ ≤ ε * ‖y - x‖ := by
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  have hgradEv :
      ∀ᶠ w in 𝓝[D] x,
        ‖G w - p₀ - B (w - x)‖ ≤ (ε / 4) * ‖w - x‖ := by
    simpa using hgrad.def hε4
  rw [eventually_nhdsWithin_iff] at hgradEv ⊢
  rcases mem_nhds_iff.mp hgradEv with ⟨U, hUsub, hUopen, hxU⟩
  filter_upwards [hUopen.mem_nhds hxU] with y hyU hyApproach
  have hyne : y ≠ x := by
    exact hyApproach.2
  have hynorm_pos : 0 < ‖y - x‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hyne)
  have hBsmall :
      ∀ᶠ w in 𝓝 y, ‖B (w - y)‖ < (ε / 2) * ‖y - x‖ := by
    have htarget_pos : 0 < (ε / 2) * ‖y - x‖ := by positivity
    have hcont :
        ContinuousAt (fun w : E => B (w - y)) y := by
      exact B.continuous.continuousAt.comp
        ((continuous_id.sub continuous_const).continuousAt)
    have htarget :
        {z : E | ‖z‖ < (ε / 2) * ‖y - x‖} ∈
          𝓝 ((fun w : E => B (w - y)) y) := by
      simpa [Metric.ball, dist_eq_norm] using
        (Metric.ball_mem_nhds (0 : E) htarget_pos)
    simpa using hcont.eventually htarget
  have hdist :
      ∀ᶠ w in 𝓝 y, ‖w - x‖ ≤ 2 * ‖y - x‖ := by
    have hball : Metric.ball y ‖y - x‖ ∈ 𝓝 y :=
      Metric.ball_mem_nhds y hynorm_pos
    filter_upwards [hball] with w hw
    have htri : ‖w - x‖ ≤ ‖w - y‖ + ‖y - x‖ := by
      simpa [sub_eq_add_neg, add_assoc] using norm_add_le (w - y) (y - x)
    have hwlt : ‖w - y‖ < ‖y - x‖ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    calc
      ‖w - x‖ ≤ ‖w - y‖ + ‖y - x‖ := htri
      _ ≤ ‖y - x‖ + ‖y - x‖ := by linarith
      _ = 2 * ‖y - x‖ := by ring
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hUopen.mem_nhds hyU, hBsmall, hdist] with w hwU hwB hwdist hwD
  have hgrad_w :
      ‖G w - p₀ - B (w - x)‖ ≤ (ε / 4) * ‖w - x‖ :=
    hUsub hwU hwD
  have hdecomp :
      G w - (p₀ + B (y - x)) =
        (G w - p₀ - B (w - x)) + B (w - y) := by
    have hwx : w - x = (w - y) + (y - x) := by
      abel
    rw [hwx, map_add]
    abel
  calc
    ‖G w - (p₀ + B (y - x))‖
        = ‖(G w - p₀ - B (w - x)) + B (w - y)‖ := by rw [hdecomp]
    _ ≤ ‖G w - p₀ - B (w - x)‖ + ‖B (w - y)‖ :=
        norm_add_le _ _
    _ ≤ (ε / 4) * ‖w - x‖ + (ε / 2) * ‖y - x‖ := by
        exact add_le_add hgrad_w (le_of_lt hwB)
    _ ≤ (ε / 4) * (2 * ‖y - x‖) + (ε / 2) * ‖y - x‖ := by
        exact add_le_add (mul_le_mul_of_nonneg_left hwdist (by positivity)) le_rfl
    _ = ε * ‖y - x‖ := by ring

/-- Closed-convex-hull transfer principle for subgradient linearization.

This isolates the elementary part of the source subgradient-extension lemma. If every nearby
subgradient lies in the closed convex hull of auxiliary slopes, and those auxiliary slopes satisfy
the desired first-order estimate, then every nearby subgradient satisfies the same estimate. The
remaining source input is the convex-analysis theorem producing the closed-convex-hull inclusion
from gradients at nearby differentiability points. -/
theorem of_eventually_mem_closure_convexHull_image
    {ι : Type*} {domain approach : Set E} {u : E → ℝ} {x p₀ : E}
    {B : E →L[ℝ] E} {t : E → Set ι} {g : E → ι → E}
    (hslopes : ∀ ε > 0, ∀ᶠ y in 𝓝[approach] x,
      ∀ q ∈ t y, ‖g y q - (p₀ + B (y - x))‖ ≤ ε * ‖y - x‖)
    (hsubgradients : ∀ᶠ y in 𝓝[approach] x,
      ∀ p : E, SubgradientOn domain u y p →
        p ∈ closure (convexHull ℝ ((g y) '' t y))) :
    HasSubgradientLinearizationOnAt domain approach u x p₀ B := by
  intro ε hε
  filter_upwards [hslopes ε hε, hsubgradients] with y hslopes_y hsubgradients_y p hp
  exact
    norm_sub_le_of_mem_closure_convexHull_image_norm_sub_le
      (a := p₀ + B (y - x)) (p := p) (R := ε * ‖y - x‖)
      hslopes_y (hsubgradients_y p hp)

/-- Convert a gradient expansion at the base point into the moving-base slope estimates needed by
the closed-convex-hull subgradient transfer.

The family `t y` should be read as the differentiability sample points approaching `y`. The
hypothesis `hwithin` says that, as `y -> x` through `approach`, all points of `t y` eventually lie
in every neighborhood of `x` inside `D`. The estimate `hBsmall` is the formal version of the
source proof's passage from `B (w - x)` to `B (y - x)` when `w -> y`. -/
theorem moving_slope_estimates_of_gradient_isLittleO
    {D approach : Set E} {G : E → E} {x p₀ : E} {B : E →L[ℝ] E}
    {t : E → Set E}
    (hgrad :
      (fun w : E => G w - p₀ - B (w - x)) =o[𝓝[D] x]
        fun w : E => ‖w - x‖)
    (hwithin : ∀ S ∈ 𝓝[D] x, ∀ᶠ y in 𝓝[approach] x, ∀ w ∈ t y, w ∈ S)
    (hdist : ∀ᶠ y in 𝓝[approach] x,
      ∀ w ∈ t y, ‖w - x‖ ≤ 2 * ‖y - x‖)
    (hBsmall : ∀ ε > 0, ∀ᶠ y in 𝓝[approach] x,
      ∀ w ∈ t y, ‖B (w - y)‖ ≤ (ε / 2) * ‖y - x‖) :
    ∀ ε > 0, ∀ᶠ y in 𝓝[approach] x,
      ∀ w ∈ t y, ‖G w - (p₀ + B (y - x))‖ ≤ ε * ‖y - x‖ := by
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  have hgradEv :
      ∀ᶠ w in 𝓝[D] x,
        ‖G w - p₀ - B (w - x)‖ ≤ (ε / 4) * ‖w - x‖ := by
    simpa using hgrad.def hε4
  have hgradY :
      ∀ᶠ y in 𝓝[approach] x,
        ∀ w ∈ t y, ‖G w - p₀ - B (w - x)‖ ≤ (ε / 4) * ‖w - x‖ :=
    hwithin _ hgradEv
  filter_upwards [hgradY, hdist, hBsmall ε hε] with y hygrad hydist hyB w hw
  have hdecomp :
      G w - (p₀ + B (y - x)) =
        (G w - p₀ - B (w - x)) + B (w - y) := by
    have hwx : w - x = (w - y) + (y - x) := by
      abel
    rw [hwx, map_add]
    abel
  calc
    ‖G w - (p₀ + B (y - x))‖
        = ‖(G w - p₀ - B (w - x)) + B (w - y)‖ := by rw [hdecomp]
    _ ≤ ‖G w - p₀ - B (w - x)‖ + ‖B (w - y)‖ :=
        norm_add_le _ _
    _ ≤ (ε / 4) * ‖w - x‖ + (ε / 2) * ‖y - x‖ :=
        add_le_add (hygrad w hw) (hyB w hw)
    _ ≤ (ε / 4) * (2 * ‖y - x‖) + (ε / 2) * ‖y - x‖ := by
        have hscale :
            (ε / 4) * ‖w - x‖ ≤ (ε / 4) * (2 * ‖y - x‖) :=
          mul_le_mul_of_nonneg_left (hydist w hw) (by positivity)
        exact add_le_add hscale (le_rfl)
    _ = ε * ‖y - x‖ := by ring

/-- Source-shaped subgradient extension from a gradient little-o expansion plus a closed-convex
hull density input.

This packages the proof of the source lemma up to the finite-dimensional density theorem: the
gradient expansion gives the moving-base estimates on nearby differentiability samples, and the
closed-convex-hull transfer then extends the estimate to every nearby subgradient. -/
theorem of_gradient_isLittleO_of_eventually_mem_closure_convexHull_image
    {domain D approach : Set E} {u : E → ℝ} {G : E → E} {x p₀ : E}
    {B : E →L[ℝ] E} {t : E → Set E}
    (hgrad :
      (fun w : E => G w - p₀ - B (w - x)) =o[𝓝[D] x]
        fun w : E => ‖w - x‖)
    (hwithin : ∀ S ∈ 𝓝[D] x, ∀ᶠ y in 𝓝[approach] x, ∀ w ∈ t y, w ∈ S)
    (hdist : ∀ᶠ y in 𝓝[approach] x,
      ∀ w ∈ t y, ‖w - x‖ ≤ 2 * ‖y - x‖)
    (hBsmall : ∀ ε > 0, ∀ᶠ y in 𝓝[approach] x,
      ∀ w ∈ t y, ‖B (w - y)‖ ≤ (ε / 2) * ‖y - x‖)
    (hsubgradients : ∀ᶠ y in 𝓝[approach] x,
      ∀ p : E, SubgradientOn domain u y p →
        p ∈ closure (convexHull ℝ (G '' t y))) :
    HasSubgradientLinearizationOnAt domain approach u x p₀ B :=
  of_eventually_mem_closure_convexHull_image
    (g := fun _y w => G w)
    (moving_slope_estimates_of_gradient_isLittleO hgrad hwithin hdist hBsmall)
    hsubgradients

/-- Evaluate a subgradient-linearization estimate along increment coordinates.

This is the form used in the final Taylor step: if small increments `z` keep `x + z` inside the
approach set, then the model estimate can be written with displacement `z` rather than
`(x + z) - x`. -/
theorem eventually_increment_estimates
    {domain approach : Set E} {u : E → ℝ} {x p₀ : E} {B : E →L[ℝ] E}
    (hlin : HasSubgradientLinearizationOnAt domain approach u x p₀ B)
    (happroach : ∀ᶠ z in 𝓝 (0 : E), x + z ∈ approach) :
    ∀ ε > 0, ∀ᶠ z in 𝓝 (0 : E),
      ∀ p : E, SubgradientOn domain u (x + z) p →
        ‖p - (p₀ + B z)‖ ≤ ε * ‖z‖ := by
  intro ε hε
  have hmap :
      Filter.Tendsto (fun z : E => x + z) (𝓝 (0 : E)) (𝓝[approach] x) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hc : ContinuousAt (fun z : E => x + z) 0 := by fun_prop
      simpa using hc.tendsto
    · exact happroach
  filter_upwards [hmap.eventually (hlin ε hε)] with z hz p hp
  simpa using hz p hp

/-- Uniform segment form of `eventually_increment_estimates`.

This matches the source proof's final integration step: after shrinking `z`, every point
`x + t • z`, `0 ≤ t ≤ 1`, lies in the approach set and in the neighborhood where the
subgradient-linearization estimate is valid. -/
theorem eventually_segment_estimates
    {domain approach : Set E} {u : E → ℝ} {x p₀ : E} {B : E →L[ℝ] E}
    (hlin : HasSubgradientLinearizationOnAt domain approach u x p₀ B)
    (hsegment : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → x + t • z ∈ approach) :
    ∀ ε > 0, ∀ᶠ z in 𝓝 (0 : E),
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        ∀ p : E, SubgradientOn domain u (x + t • z) p →
          ‖p - (p₀ + B (t • z))‖ ≤ ε * ‖t • z‖ := by
  intro ε hε
  have hlinEv :=
    (eventually_nhdsWithin_iff.mp (hlin ε hε) :
      ∀ᶠ y in 𝓝 x, y ∈ approach →
        ∀ p : E, SubgradientOn domain u y p →
          ‖p - (p₀ + B (y - x))‖ ≤ ε * ‖y - x‖)
  rcases Metric.mem_nhds_iff.mp hlinEv with ⟨δ, hδpos, hδsub⟩
  filter_upwards [Metric.ball_mem_nhds (0 : E) hδpos, hsegment] with
    z hzball hzsegment t ht p hp
  have ht_abs : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hz_norm_lt : ‖z‖ < δ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hzball
  have htz_norm_lt : ‖t • z‖ < δ := by
    calc
      ‖t • z‖ = |t| * ‖z‖ := norm_smul t z
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht_abs (norm_nonneg z)
      _ = ‖z‖ := by ring
      _ < δ := hz_norm_lt
  have hyball : x + t • z ∈ Metric.ball x δ := by
    simpa [Metric.mem_ball, dist_eq_norm] using htz_norm_lt
  have hestimate := hδsub hyball (hzsegment t ht) p hp
  simpa using hestimate

/-- Directional scalar consequence of the uniform segment estimate.

After pairing with the segment direction `z`, the vector estimate becomes the scalar estimate
used in the source integration argument:
`inner p z` is close to `inner p₀ z + t * inner z (B z)`, uniformly for `0 ≤ t ≤ 1`. -/
theorem eventually_segment_inner_estimates
    {domain approach : Set E} {u : E → ℝ} {x p₀ : E} {B : E →L[ℝ] E}
    (hlin : HasSubgradientLinearizationOnAt domain approach u x p₀ B)
    (hsegment : ∀ᶠ z in 𝓝 (0 : E),
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → x + t • z ∈ approach) :
    ∀ ε > 0, ∀ᶠ z in 𝓝 (0 : E),
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        ∀ p : E, SubgradientOn domain u (x + t • z) p →
          |inner ℝ p z - (inner ℝ p₀ z + t * inner ℝ z (B z))| ≤ ε * ‖z‖ ^ 2 := by
  intro ε hε
  filter_upwards [eventually_segment_estimates hlin hsegment ε hε] with z hz t ht p hp
  let r : E := p - (p₀ + B (t • z))
  have ht_abs : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have htz_norm : ‖t • z‖ ≤ ‖z‖ := by
    calc
      ‖t • z‖ = |t| * ‖z‖ := norm_smul t z
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht_abs (norm_nonneg z)
      _ = ‖z‖ := by ring
  have hmodel :
      inner ℝ (B (t • z)) z = t * inner ℝ z (B z) := by
    calc
      inner ℝ (B (t • z)) z = inner ℝ (t • B z) z := by rw [map_smul]
      _ = t * inner ℝ (B z) z := by simp [inner_smul_left]
      _ = t * inner ℝ z (B z) := by rw [real_inner_comm]
  have hscalar :
      inner ℝ p z - (inner ℝ p₀ z + t * inner ℝ z (B z)) = inner ℝ r z := by
    dsimp [r]
    rw [inner_sub_left, inner_add_left, hmodel]
  have hinner : |inner ℝ r z| ≤ ‖r‖ * ‖z‖ := by
    simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) r z
  have hnorm : ‖r‖ ≤ ε * ‖t • z‖ := by
    simpa [r] using hz t ht p hp
  calc
    |inner ℝ p z - (inner ℝ p₀ z + t * inner ℝ z (B z))|
        = |inner ℝ r z| := by rw [hscalar]
    _ ≤ ‖r‖ * ‖z‖ := hinner
    _ ≤ (ε * ‖t • z‖) * ‖z‖ :=
        mul_le_mul_of_nonneg_right hnorm (norm_nonneg z)
    _ ≤ (ε * ‖z‖) * ‖z‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htz_norm (le_of_lt hε)) (norm_nonneg z)
    _ = ε * ‖z‖ ^ 2 := by ring

end HasSubgradientLinearizationOnAt

section Gradient

variable [CompleteSpace E]

/-- A subgradient on a neighborhood of a differentiability point is the gradient.

This is the convex-analysis normalization used in the source proof: once `u` is differentiable
at `x`, every supporting slope at `x` is forced to be `∇u(x)`. -/
theorem SubgradientOn.eq_gradient_of_hasGradientAt {s : Set E} {u : E → ℝ} {x p q : E}
    (hp : SubgradientOn s u x p) (hs : s ∈ 𝓝 x) (hd : HasGradientAt u q x) :
    p = q := by
  let g : E → ℝ := fun y => u y - inner ℝ p y
  have hminOn : IsLocalMinOn g s x := by
    rw [IsLocalMinOn, IsMinFilter]
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hsupport := hp.supporting_inequality (y := y) hy
    dsimp [g]
    rw [← sub_nonneg]
    have hdiff : inner ℝ p (y - x) = inner ℝ p y - inner ℝ p x := by
      rw [inner_sub_right]
    linarith
  have hmin : IsLocalMin g x := hminOn.isLocalMin hs
  have hinner : HasFDerivAt (fun y : E => inner ℝ p y)
      (InnerProductSpace.toDual ℝ E p) x :=
    (InnerProductSpace.toDual ℝ E p).hasFDerivAt
  have hg : HasFDerivAt g
      (InnerProductSpace.toDual ℝ E q - InnerProductSpace.toDual ℝ E p) x := by
    change HasFDerivAt (u - fun y : E => inner ℝ p y)
      (InnerProductSpace.toDual ℝ E q - InnerProductSpace.toDual ℝ E p) x
    exact hd.hasFDerivAt.sub hinner
  have hzero :
      InnerProductSpace.toDual ℝ E q - InnerProductSpace.toDual ℝ E p = 0 :=
    hmin.hasFDerivAt_eq_zero hg
  have hdual_eq : InnerProductSpace.toDual ℝ E q = InnerProductSpace.toDual ℝ E p := by
    exact sub_eq_zero.mp hzero
  exact (InnerProductSpace.toDual ℝ E).injective hdual_eq.symm

/-- A subgradient on a neighborhood of a differentiability point is `gradient u x`. -/
theorem SubgradientOn.eq_gradient_of_differentiableAt {s : Set E} {u : E → ℝ} {x p : E}
    (hp : SubgradientOn s u x p) (hs : s ∈ 𝓝 x) (hd : DifferentiableAt ℝ u x) :
    p = gradient u x :=
  hp.eq_gradient_of_hasGradientAt hs hd.hasGradientAt

end Gradient

end AleksandrovDifferentiability
