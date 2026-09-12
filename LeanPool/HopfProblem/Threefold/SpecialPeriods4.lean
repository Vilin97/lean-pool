/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Uniformization.SpecialPeriods3
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Threefold.SpecialPeriods1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods3

/-!
# Hopf problem: threefold · special periods 4

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private abbrev SpecialPeriods.Threefold.Puncture :=
  Option Elliptic.Kind

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.puncturePoint :
    Puncture → SpecialPeriods.TriangleCompactifiedOrbitSpace
  | none => SpecialPeriods.triangleCuspPoint
  | some j => SpecialPeriods.Triangle.ellipticCompactifiedCenter j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.Threefold.puncturePoint_injective : Function.Injective puncturePoint := by
  intro i j h
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => exact (SpecialPeriods.Triangle.ellipticCompactifiedCenter_ne_cusp j h.symm).elim
  | some i =>
    cases j with
    | none => exact (SpecialPeriods.Triangle.ellipticCompactifiedCenter_ne_cusp i h).elim
    | some j =>
      congr 1
      cases i <;> cases j
      · rfl
      · exact (SpecialPeriods.triangleCompactifiedCenterOne_ne_centerTwo h).elim
      · exact (SpecialPeriods.triangleCompactifiedCenterOne_ne_centerTwo h.symm).elim
      · rfl

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.punctureChart :
    Puncture → OpenPartialHomeomorph SpecialPeriods.TriangleCompactifiedOrbitSpace ℂ
  | none => SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
  | some j => SpecialPeriods.Triangle.ellipticCompactifiedChart j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.punctureChartRadius : Puncture → ℝ
  | none => SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width
  | some _ => 1

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.punctureChartRadius_pos (i : Puncture) :
    0 < punctureChartRadius i := by
  cases i with
  | none => exact SpecialPeriods.Triangle.cuspRadius_pos SpecialPeriods.Triangle.width
  | some j => norm_num [punctureChartRadius]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.punctureChart_target (i : Puncture) :
    (punctureChart i).target = Metric.ball 0 (punctureChartRadius i) := by
  cases i with
  | none =>
    exact SpecialPeriods.Triangle.cuspFullChart_target SpecialPeriods.Triangle.width le_rfl
  | some j => exact SpecialPeriods.Triangle.ellipticCompactifiedChart_target j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.puncturePoint_mem_source (i : Puncture) :
    puncturePoint i ∈ (punctureChart i).source := by
  cases i with
  | none =>
    exact SpecialPeriods.Triangle.cuspPoint_mem_cuspNeighborhood SpecialPeriods.Triangle.width
  | some j => exact SpecialPeriods.Triangle.ellipticCompactifiedChart_center_mem_source j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.punctureChart_point (i : Puncture) :
    punctureChart i (puncturePoint i) = 0 := by
  cases i with
  | none =>
    exact SpecialPeriods.Triangle.cuspFullChart_cuspPoint SpecialPeriods.Triangle.width le_rfl
  | some j => exact SpecialPeriods.Triangle.ellipticCompactifiedChart_center j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.punctureChart_symm_zero (i : Puncture) :
    (punctureChart i).symm 0 = puncturePoint i := by
  rw [← punctureChart_point i]
  exact (punctureChart i).left_inv (puncturePoint_mem_source i)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.punctureChart_eq_zero_iff (i : Puncture)
    {x : SpecialPeriods.TriangleCompactifiedOrbitSpace} (hx : x ∈ (punctureChart i).source) :
    punctureChart i x = 0 ↔ x = puncturePoint i := by
  constructor
  · intro h
    apply (punctureChart i).injOn hx (puncturePoint_mem_source i)
    exact h.trans (punctureChart_point i).symm
  · rintro rfl
    exact punctureChart_point i

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.punctureChart_holomorphic (i : Puncture) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (punctureChart i) (punctureChart i).source := by
  cases i with
  | none => exact SpecialPeriods.triangleCompactified_cuspChart_holomorphic
  | some j => exact SpecialPeriods.Triangle.ellipticCompactifiedChart_holomorphic j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.punctureChart_symm_holomorphic (i : Puncture) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (punctureChart i).symm (punctureChart i).target := by
  cases i with
  | none => exact SpecialPeriods.triangleCompactified_cuspChart_symm_holomorphic
  | some j => exact SpecialPeriods.Triangle.ellipticCompactifiedChart_symm_holomorphic j

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.puncturePartial (i : Puncture) :
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace ℂ ω
    where
  toPartialEquiv := (punctureChart i).toPartialEquiv
  open_source := (punctureChart i).open_source
  open_target := (punctureChart i).open_target
  contMDiffOn_toFun := punctureChart_holomorphic i
  contMDiffOn_invFun := punctureChart_symm_holomorphic i

private theorem
    SpecialPeriods.Threefold.exists_pairwise_disjoint_opens {I X : Type*} [TopologicalSpace X]
    [Finite I] [T2Space X] (p : I → X) (hp : Function.Injective p)
    (U : I → TopologicalSpace.Opens X) (hU : ∀ i, p i ∈ U i) :
    ∃ V : I → TopologicalSpace.Opens X,
      (∀ i, p i ∈ V i) ∧
        (∀ i, V i ≤ U i) ∧ Pairwise (fun i j => Disjoint (V i : Set X) (V j : Set X)) := by
  obtain ⟨W, hW, hdisj⟩ := (Set.finite_range p).t2_separation
  refine
    ⟨fun i => ⟨W (p i) ∩ U i, (hW (p i)).2.inter (U i).isOpen⟩, fun i => ⟨(hW (p i)).1, hU i⟩,
      fun _ => Set.inter_subset_right, ?_⟩
  intro i j hij
  exact
    (hdisj (Set.mem_range_self i) (Set.mem_range_self j) (fun h => hij (hp h))).mono
      Set.inter_subset_left Set.inter_subset_left

private def SpecialPeriods.Threefold.coordinateDisc {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) (r : ℝ) : TopologicalSpace.Opens X :=
  ⟨e.source ∩ e ⁻¹' Metric.ball 0 r, e.isOpen_inter_preimage Metric.isOpen_ball⟩

@[simp]
private theorem SpecialPeriods.Threefold.mem_coordinateDisc {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) (r : ℝ) (x : X) :
    x ∈ coordinateDisc e r ↔ x ∈ e.source ∧ e x ∈ Metric.ball 0 r :=
  Iff.rfl

private theorem SpecialPeriods.Threefold.center_mem_coordinateDisc {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) {p : X} (hp : p ∈ e.source) (h0 : e p = 0) {r : ℝ}
    (hr : 0 < r) : p ∈ coordinateDisc e r := by exact ⟨hp, h0 ▸ Metric.mem_ball_self hr⟩

private theorem
    SpecialPeriods.Threefold.coordinateDisc_eq_symm_image {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) {r : ℝ} (hr : Metric.ball 0 r ⊆ e.target) :
    (coordinateDisc e r : Set X) = e.symm '' Metric.ball 0 r :=
  (e.symm_image_eq_source_inter_preimage hr).symm

private theorem
    SpecialPeriods.Threefold.exists_coordinateDisc_subset {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) {p : X} (hp : p ∈ e.source) (h0 : e p = 0)
    (U : TopologicalSpace.Opens X) (hU : p ∈ U) {R : ℝ} (hR : 0 < R) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ Metric.ball 0 r ⊆ e.target ∧ coordinateDisc e r ≤ U := by
  have hnhds : e.target ∩ e.symm ⁻¹' (U : Set X) ∈ 𝓝 (e p) :=
    Filter.inter_mem (e.open_target.mem_nhds (e.map_source hp))
      ((e.tendsto_symm hp).eventually (U.isOpen.mem_nhds hU))
  rw [h0] at hnhds
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let ρ := Min.min r (R / 2)
  have hρr : ρ ≤ r := min_le_left _ _
  have hρball : Metric.ball (0 : ℂ) ρ ⊆ e.target ∩ e.symm ⁻¹' (U : Set X) :=
    (Metric.ball_subset_ball hρr).trans hball
  refine
    ⟨ρ, lt_min hr (half_pos hR), (min_le_right _ _).trans_lt (half_lt_self hR),
      hρball.trans Set.inter_subset_left, ?_⟩
  intro x hx
  have hmem := (hρball hx.2).2
  change e.symm (e x) ∈ (U : Set X) at hmem
  rw [e.left_inv hx.1] at hmem
  exact hmem

private theorem SpecialPeriods.Threefold.exists_pairwise_disjoint_coordinateDiscs {I X : Type*}
    [TopologicalSpace X] [Finite I] [T2Space X] (p : I → X) (hp : Function.Injective p)
    (e : I → OpenPartialHomeomorph X ℂ) (hsource : ∀ i, p i ∈ (e i).source)
    (hzero : ∀ i, e i (p i) = 0) (U : I → TopologicalSpace.Opens X) (hU : ∀ i, p i ∈ U i)
    (R : I → ℝ) (hR : ∀ i, 0 < R i) :
    ∃ r : I → ℝ,
      (∀ i, 0 < r i ∧ r i < R i) ∧
        (∀ i, Metric.ball 0 (r i) ⊆ (e i).target) ∧
          (∀ i, coordinateDisc (e i) (r i) ≤ U i) ∧
            Pairwise
              (fun i j =>
                Disjoint (coordinateDisc (e i) (r i) : Set X)
                  (coordinateDisc (e j) (r j) : Set X)) := by
  obtain ⟨V, hpV, hVU, hVdisj⟩ := exists_pairwise_disjoint_opens p hp U hU
  have hdisc (i : I) :=
    exists_coordinateDisc_subset (e i) (hsource i) (hzero i) (V i) (hpV i) (hR i)
  choose r hr hrR htarget hsubset using hdisc
  refine ⟨r, fun i => ⟨hr i, hrR i⟩, htarget, fun i => (hsubset i).trans (hVU i), ?_⟩
  intro i j hij
  exact (hVdisj hij).mono (hsubset i) (hsubset j)

private theorem SpecialPeriods.ModularCoverTools.injective_of_covering_singleton_fibre {X B : Type*}
    [TopologicalSpace X] [TopologicalSpace B] [PathConnectedSpace B] {f : X → B}
    (hf : IsCoveringMap f) (b₀ : B) (h₀ : Subsingleton (f ⁻¹' { b₀ })) : Function.Injective f := by
  intro x y hxy
  let γ : Path.Homotopic.Quotient (f x) b₀ := .mk (PathConnectedSpace.somePath (f x) b₀)
  have he : (⟨x, rfl⟩ : f ⁻¹' {f x}) = ⟨y, hxy.symm⟩ := (hf.monodromy_bijective γ).1 (h₀.elim _ _)
  exact congrArg Subtype.val he

private theorem SpecialPeriods.ModularCoverTools.injective_of_open_dense {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] {f : X → Y} {D : Set Y}
    (hf : IsOpenMap f) (hD : Dense D) (hi : Set.InjOn f (f ⁻¹' D)) : Function.Injective f := by
  intro x y hxy
  by_contra hne
  obtain ⟨U, V, hU, hV, hx, hy, hUV⟩ := t2_separation hne
  have hnonempty : (f '' U ∩ f '' V).Nonempty := ⟨f x, ⟨x, hx, rfl⟩, y, hy, hxy.symm⟩
  obtain ⟨z, hzD, ⟨u, hu, huz⟩, ⟨v, hv, hvz⟩⟩ :=
    hD.exists_mem_open ((hf U hU).inter (hf V hV)) hnonempty
  have huv : u = v :=
    hi (by simpa only [Set.mem_preimage, huz] using hzD)
      (by simpa only [Set.mem_preimage, hvz] using hzD) (huz.trans hvz.symm)
  subst v
  exact hUV.le_bot ⟨hu, hv⟩

private theorem SpecialPeriods.ModularCoverTools.complex_compl_countable_pathConnected {S : Set ℂ}
    (hS : S.Countable) : PathConnectedSpace ↥(Sᶜ) :=
  isPathConnected_iff_pathConnectedSpace.mp
    (hS.isPathConnected_compl_of_one_lt_rank (by simp [Complex.rank_real_complex]))

private theorem SpecialPeriods.ModularCoverTools.complex_compl_pair_pathConnected (a b : ℂ) :
    PathConnectedSpace ↥(({ a, b } : Set ℂ)ᶜ) :=
  complex_compl_countable_pathConnected (Set.toFinite _).countable

private theorem SpecialPeriods.ModularCoverTools.complex_compl_countable_dense {S : Set ℂ}
    (hS : S.Countable) : Dense Sᶜ :=
  hS.dense_compl ℝ

private theorem SpecialPeriods.ModularCoverTools.complex_compl_pair_dense (a b : ℂ) :
    Dense (({ a, b } : Set ℂ)ᶜ) :=
  complex_compl_countable_dense (Set.toFinite _).countable

private def SpecialPeriods.TauEquivariance.intertwiningSubgroup {G X Y : Type*} [Group G]
    (α : G →* Equiv.Perm X) (β : G →* Equiv.Perm Y) (f : X → Y) : Subgroup G
    where
  carrier := {g | ∀ x, f (α g x) = β g (f x)}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro g h hg hh x
    simpa only [map_mul, Equiv.Perm.coe_mul, Function.comp_apply] using
      (hg (α h x)).trans (congrArg (β g) (hh x))
  inv_mem' := by
    intro g hg x
    apply (β g).injective
    have h := hg (α g⁻¹ x)
    simpa using h.symm

private theorem SpecialPeriods.GlobalTauNormalization.trace_neg_two_triples (p q r : ℤ)
    (hdet : -p ^ 2 - q * r = 1) (htr : p + q - r = -2) :
    (p = 0 ∧ q = -1 ∧ r = 1) ∨ (p = 1 ∧ q = -2 ∧ r = 1) ∨ (p = 1 ∧ q = -1 ∧ r = 2) := by
  have hq : q = r - p - 2 := by omega
  rw [hq] at hdet
  have hquad : p ^ 2 - p * r + r ^ 2 - 2 * r + 1 = 0 := by nlinarith only [hdet]
  have hp₀ : 0 ≤ p := by nlinarith only [hquad, sq_nonneg (2 * r - p - 2), sq_nonneg p]
  have hp_upper : 2 * p ≤ 3 := by
    nlinarith only [hquad, sq_nonneg (2 * r - p - 2), sq_nonneg (p - 1)]
  have hp₁ : p ≤ 1 := by omega
  have hr_lower : 4 ≤ 8 * r := by nlinarith only [hquad, sq_nonneg (2 * p - r), sq_nonneg r]
  have hr_upper : 10 * r ≤ 23 := by
    nlinarith only [hquad, sq_nonneg (2 * p - r), sq_nonneg (r - 3)]
  have hr₁ : 1 ≤ r := by omega
  have hr₂ : r ≤ 2 := by omega
  have hp_cases : p = 0 ∨ p = 1 := by omega
  have hr_cases : r = 1 ∨ r = 2 := by omega
  rcases hp_cases with rfl | rfl
  · rcases hr_cases with rfl | rfl
    · left
      omega
    · norm_num at hquad
  · rcases hr_cases with rfl | rfl
    · right
      left
      omega
    · right
      right
      omega

private def SpecialPeriods.TauCusp.simplePoleCoordinate (a : ℂ → ℂ) (t : ℂ) : ℂ :=
  1728 * t / a t

private def SpecialPeriods.TauCusp.simplePoleQ (a : ℂ → ℂ) (t : ℂ) : ℂ :=
  SpecialPeriods.modularCuspQ (simplePoleCoordinate a t)

private def SpecialPeriods.TauCusp.simplePoleUnit (a : ℂ → ℂ) (t : ℂ) : ℂ :=
  (1728 / a t) * SpecialPeriods.modularCuspUnit (simplePoleCoordinate a t)

@[simp]
private theorem SpecialPeriods.TauCusp.simplePoleCoordinate_zero (a : ℂ → ℂ) :
    simplePoleCoordinate a 0 = 0 := by simp [simplePoleCoordinate]

@[simp]
private theorem SpecialPeriods.TauCusp.simplePoleQ_zero (a : ℂ → ℂ) : simplePoleQ a 0 = 0 := by
  simp [simplePoleQ]

@[simp]
private theorem
    SpecialPeriods.TauCusp.simplePoleUnit_zero (a : ℂ → ℂ) : simplePoleUnit a 0 = 1 / a 0 := by
  simp [simplePoleUnit]
  ring

private theorem
    SpecialPeriods.TauCusp.simplePoleCoordinate_analyticAt {a : ℂ → ℂ} (ha : AnalyticAt ℂ a 0)
    (ha0 : a 0 ≠ 0) : AnalyticAt ℂ (simplePoleCoordinate a) 0 :=
  (analyticAt_const.mul analyticAt_id).div ha ha0

private theorem SpecialPeriods.TauCusp.simplePoleQ_analyticAt {a : ℂ → ℂ} (ha : AnalyticAt ℂ a 0)
    (ha0 : a 0 ≠ 0) : AnalyticAt ℂ (simplePoleQ a) 0 := by
  have hq : AnalyticAt ℂ SpecialPeriods.modularCuspQ (simplePoleCoordinate a 0) := by
    simpa only [simplePoleCoordinate_zero] using SpecialPeriods.modularCuspQ_analyticAt_zero
  exact hq.comp (simplePoleCoordinate_analyticAt ha ha0)

private theorem SpecialPeriods.TauCusp.simplePoleUnit_analyticAt {a : ℂ → ℂ} (ha : AnalyticAt ℂ a 0)
    (ha0 : a 0 ≠ 0) : AnalyticAt ℂ (simplePoleUnit a) 0 := by
  have hu : AnalyticAt ℂ SpecialPeriods.modularCuspUnit (simplePoleCoordinate a 0) := by
    simpa only [simplePoleCoordinate_zero] using SpecialPeriods.modularCuspUnit_analyticAt_zero
  exact (analyticAt_const.div ha ha0).mul (hu.comp (simplePoleCoordinate_analyticAt ha ha0))

private theorem SpecialPeriods.TauCusp.simplePoleQ_eq_mul_unit (a : ℂ → ℂ) (t : ℂ) :
    simplePoleQ a t = t * simplePoleUnit a t := by
  rw [simplePoleQ, SpecialPeriods.modularCuspQ_eq_mul_unit]
  simp only [simplePoleCoordinate, simplePoleUnit]
  ring

private theorem
    SpecialPeriods.TauCusp.simplePoleQ_eventually_j_eq {a : ℂ → ℂ} (ha : AnalyticAt ℂ a 0)
    (ha0 : a 0 ≠ 0) :
    ∀ᶠ t in 𝓝 (0 : ℂ), t ≠ 0 → SpecialPeriods.modularJInQ (simplePoleQ a t) = a t / t := by
  have hj :
    ∀ᶠ u in 𝓝 (0 : ℂ),
      u ≠ 0 → SpecialPeriods.modularJInQ (SpecialPeriods.modularCuspQ u) = 1728 / u :=
    eventually_nhdsWithin_iff.mp SpecialPeriods.modularCuspQ_eventually_j_eq
  have hc : Filter.Tendsto (simplePoleCoordinate a) (𝓝 0) (𝓝 0) := by
    simpa only [simplePoleCoordinate_zero] using
      (simplePoleCoordinate_analyticAt ha ha0).continuousAt.tendsto
  filter_upwards [hc.eventually hj, ha.continuousAt.eventually_ne ha0] with t hjt hat
  intro ht
  have hct : simplePoleCoordinate a t ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) ht) hat
  rw [simplePoleQ, hjt hct, simplePoleCoordinate]
  field_simp

private theorem
    SpecialPeriods.TauCusp.exists_simplePoleQ_coordinate {a : ℂ → ℂ} (ha : AnalyticAt ℂ a 0)
    (ha0 : a 0 ≠ 0) {R : ℝ} (hR : 0 < R) :
    ∃ r > 0,
      AnalyticOnNhd ℂ (simplePoleQ a) (Metric.ball 0 r) ∧
        AnalyticOnNhd ℂ (simplePoleUnit a) (Metric.ball 0 r) ∧
          ∀ t ∈ Metric.ball (0 : ℂ) r,
            a t ≠ 0 ∧
              simplePoleUnit a t ≠ 0 ∧
                ‖simplePoleQ a t‖ < R ∧
                  (t ≠ 0 → SpecialPeriods.modularJInQ (simplePoleQ a t) = a t / t) := by
  have hq := simplePoleQ_analyticAt ha ha0
  have hu := simplePoleUnit_analyticAt ha ha0
  have hu0 : simplePoleUnit a 0 ≠ 0 := by
    rw [simplePoleUnit_zero]
    exact one_div_ne_zero ha0
  have hn : ∀ᶠ t in 𝓝 (0 : ℂ), ‖simplePoleQ a t‖ < R := by
    have h :=
      hq.continuousAt.preimage_mem_nhds
        (show Metric.ball (0 : ℂ) R ∈ 𝓝 (simplePoleQ a 0)
          by
          rw [simplePoleQ_zero]
          exact Metric.ball_mem_nhds _ hR)
    filter_upwards [h] with t ht
    simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] using ht
  have hall :
    ∀ᶠ t in 𝓝 (0 : ℂ),
      AnalyticAt ℂ (simplePoleQ a) t ∧
        AnalyticAt ℂ (simplePoleUnit a) t ∧
          a t ≠ 0 ∧
            simplePoleUnit a t ≠ 0 ∧
              ‖simplePoleQ a t‖ < R ∧
                (t ≠ 0 → SpecialPeriods.modularJInQ (simplePoleQ a t) = a t / t) := by
    filter_upwards [hq.eventually_analyticAt, hu.eventually_analyticAt,
      ha.continuousAt.eventually_ne ha0, hu.continuousAt.eventually_ne hu0, hn,
      simplePoleQ_eventually_j_eq ha ha0] with t hqt hut hat hut0 hnt hjt
    exact ⟨hqt, hut, hat, hut0, hnt, hjt⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hall
  exact ⟨r, hr, fun t ht => (hball ht).1, fun t ht => (hball ht).2.1, fun t ht => (hball ht).2.2⟩

private theorem SpecialPeriods.TauCusp.mem_logBase_iff_im (r : ℝ) (hr : 0 < r) (s : ℂ) :
    s ∈ SpecialPeriods.CuspFamily.logBase r ↔ -Real.log r / (2 * Real.pi) < s.im :=
  CuspUniformization.mem_logDomain_iff_im r hr (s, 0)

private theorem SpecialPeriods.TauCusp.logBase_eq_halfSpace (r : ℝ) (hr : 0 < r) :
    (SpecialPeriods.CuspFamily.logBase r : Set ℂ) = {s | -Real.log r / (2 * Real.pi) < s.im} := by
  ext s
  exact mem_logBase_iff_im r hr s

private theorem SpecialPeriods.TauCusp.logBase_convex (r : ℝ) (hr : 0 < r) :
    Convex ℝ (SpecialPeriods.CuspFamily.logBase r : Set ℂ) := by
  rw [logBase_eq_halfSpace r hr]
  exact (convex_Ioi (-Real.log r / (2 * Real.pi))).linear_preimage Complex.imLm

private theorem SpecialPeriods.TauCusp.logBase_set_nonempty (r : ℝ) (hr : 0 < r) :
    (SpecialPeriods.CuspFamily.logBase r : Set ℂ).Nonempty := by
  obtain ⟨p, hp⟩ := CuspUniformization.logDomain_nonempty r hr
  exact ⟨p.1, hp⟩

private theorem SpecialPeriods.TauCusp.exponential_eq_qParam_one (s : ℂ) :
    CuspUniformization.exponential s = Function.Periodic.qParam 1 s := by
  simp only [CuspUniformization.exponential, Function.Periodic.qParam, Complex.ofReal_one,
    div_one]

private theorem SpecialPeriods.TauCusp.qParam_eq_exponential_div (w : ℝ) (s : ℂ) :
    Function.Periodic.qParam w s = CuspUniformization.exponential (s / w) := by
  simp only [CuspUniformization.exponential, Function.Periodic.qParam, mul_div_assoc]

private theorem SpecialPeriods.TauCusp.norm_exponential_lt_one_iff (s : ℂ) :
    ‖CuspUniformization.exponential s‖ < 1 ↔ 0 < s.im := by
  simpa only [SpecialPeriods.CuspFamily.mem_logBase, Real.log_one, neg_zero, zero_div] using
    mem_logBase_iff_im 1 zero_lt_one s

private theorem SpecialPeriods.TauCusp.upperHalfPlane_of_exponential_norm_lt_one {s : ℂ}
    (hs : ‖CuspUniformization.exponential s‖ < 1) : 0 < s.im :=
  (norm_exponential_lt_one_iff s).mp hs

public
theorem SpecialPeriods.TauCusp.exponential_norm_lt_one_of_upperHalfPlane {s : ℂ} (hs : 0 < s.im) :
    ‖CuspUniformization.exponential s‖ < 1 :=
  (norm_exponential_lt_one_iff s).mpr hs

private theorem SpecialPeriods.TauCusp.analytic_unit_normalized_logarithm {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) :
    ∃ r > 0,
      ∃ h : ℂ → ℂ,
        AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
          h 0 = CuspUniformization.logarithm (u 0) ∧
            ∀ t ∈ Metric.ball 0 r, CuspUniformization.exponential (h t) = u t := by
  let s := CuspUniformization.logarithm (u 0)
  let e := SpecialPeriods.CuspFamily.scalarExponentialChart s
  have hs : s ∈ e.source := SpecialPeriods.CuspFamily.scalarExponentialChart_mem_source s
  have he0 : e s = u 0 := CuspUniformization.exponential_logarithm hu0
  have huT : u 0 ∈ e.target := he0 ▸ e.map_source hs
  have hlocal : ∀ᶠ t in 𝓝 (0 : ℂ), AnalyticAt ℂ u t ∧ u t ∈ e.target :=
    hu.eventually_analyticAt.and (hu.continuousAt (e.open_target.mem_nhds huT))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hlocal
  refine ⟨r, hr, e.symm ∘ u, ?_, ?_, ?_⟩
  · intro t ht
    have hInv : ContDiffOn ℂ ω e.symm e.target :=
      SpecialPeriods.CuspFamily.scalarExponentialChart_symm_holomorphic s
    exact
      ((hInv (u t) (hball ht).2).contDiffAt (e.open_target.mem_nhds (hball ht).2)).analyticAt.comp
        (hball ht).1
  · change e.symm (u 0) = s
    rw [← he0]
    exact e.left_inv hs
  · intro t ht
    exact e.right_inv (hball ht).2

private theorem SpecialPeriods.TauCusp.modularJInQ_exponential {z : ℂ} (hz : 0 < z.im) :
    SpecialPeriods.modularJInQ (CuspUniformization.exponential z) =
      SpecialPeriods.modularJ (UpperHalfPlane.ofComplex z) := by
  simpa only [Function.Periodic.qParam, Complex.ofReal_one, div_one,
    CuspUniformization.exponential, UpperHalfPlane.ofComplex_apply_of_im_pos hz] using
    SpecialPeriods.modularJInQ_qParam (UpperHalfPlane.ofComplex z)

private def SpecialPeriods.TauCusp.correctedLogarithm (h : ℂ → ℂ) (s : ℂ) : ℂ :=
  s + h (CuspUniformization.exponential s)

private theorem SpecialPeriods.TauCusp.correctedLogarithm_exponential (h : ℂ → ℂ) (s : ℂ) :
    CuspUniformization.exponential (correctedLogarithm h s) =
      CuspUniformization.exponential s *
        CuspUniformization.exponential (h (CuspUniformization.exponential s)) :=
  CuspUniformization.exponential_add _ _

private theorem SpecialPeriods.TauCusp.correctedLogarithm_sub_int (h : ℂ → ℂ) (s : ℂ) (k : ℤ) :
    correctedLogarithm h (s - k) = correctedLogarithm h s - k := by
  simp only [correctedLogarithm, SpecialPeriods.CuspFamily.exponential_sub_int]
  abel

private theorem SpecialPeriods.TauCusp.correctedLogarithm_analyticAt {r : ℝ} {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r)) {s : ℂ}
    (hs : s ∈ SpecialPeriods.CuspFamily.logBase r) : AnalyticAt ℂ (correctedLogarithm h) s :=
  analyticAt_id.add
    ((hh (CuspUniformization.exponential s) hs).comp
      CuspUniformization.exponential_holomorphic.contDiffAt.analyticAt)

private theorem SpecialPeriods.TauCusp.exists_simplePole_logarithmic_lift {a : ℂ → ℂ}
    (ha : AnalyticAt ℂ a 0) (ha0 : a 0 ≠ 0) {R r₀ : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) :
    ∃ r > 0,
      r < r₀ ∧
        r < 1 ∧
          ∃ h : ℂ → ℂ,
            AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
              h 0 = CuspUniformization.logarithm (1 / a 0) ∧
                (∀ t ∈ Metric.ball 0 r,
                    CuspUniformization.exponential (h t) = simplePoleUnit a t) ∧
                  ∀ s ∈ SpecialPeriods.CuspFamily.logBase r,
                    CuspUniformization.exponential (correctedLogarithm h s) =
                        simplePoleQ a (CuspUniformization.exponential s) ∧
                      0 < (correctedLogarithm h s).im ∧
                        ‖CuspUniformization.exponential (correctedLogarithm h s)‖ < R ∧
                          SpecialPeriods.modularJ
                              (UpperHalfPlane.ofComplex (correctedLogarithm h s)) =
                            a (CuspUniformization.exponential s) /
                              CuspUniformization.exponential s := by
  obtain ⟨rq, hrq, _, _, hq⟩ := exists_simplePoleQ_coordinate ha ha0 (lt_min hR zero_lt_one)
  obtain ⟨rh, hrh, h, hh, hh0, he⟩ :=
    analytic_unit_normalized_logarithm (simplePoleUnit_analyticAt ha ha0)
      (by simpa using one_div_ne_zero ha0)
  obtain ⟨r, hr, hrr⟩ :=
    exists_between
      (show 0 < Min.min rq (Min.min rh (Min.min r₀ 1)) from
        lt_min hrq (lt_min hrh (lt_min hr₀ zero_lt_one)))
  have hparts : r < rq ∧ r < rh ∧ r < r₀ ∧ r < 1 := by simpa only [lt_min_iff] using hrr
  have hh' : AnalyticOnNhd ℂ h (Metric.ball 0 r) :=
    hh.mono (Metric.ball_subset_ball hparts.2.1.le)
  refine ⟨r, hr, hparts.2.2.1, hparts.2.2.2, h, hh', ?_, ?_, ?_⟩
  · simpa only [simplePoleUnit_zero] using hh0
  · intro t ht
    exact he t (Metric.ball_subset_ball hparts.2.1.le ht)
  · intro s hs
    have hst : CuspUniformization.exponential s ∈ Metric.ball (0 : ℂ) r := hs
    have hsq := hq (CuspUniformization.exponential s) (Metric.ball_subset_ball hparts.1.le hst)
    have hse := he (CuspUniformization.exponential s) (Metric.ball_subset_ball hparts.2.1.le hst)
    have hτq :
      CuspUniformization.exponential (correctedLogarithm h s) =
        simplePoleQ a (CuspUniformization.exponential s) := by
      rw [correctedLogarithm_exponential, hse, simplePoleQ_eq_mul_unit]
    have hτpos : 0 < (correctedLogarithm h s).im :=
      upperHalfPlane_of_exponential_norm_lt_one
        (by rw [hτq]; exact lt_of_lt_of_le hsq.2.2.1 (min_le_right R 1))
    refine ⟨hτq, hτpos, ?_, ?_⟩
    · rw [hτq]
      exact lt_of_lt_of_le hsq.2.2.1 (min_le_left R 1)
    · rw [← modularJInQ_exponential hτpos, hτq]
      exact hsq.2.2.2 (CuspUniformization.exponential_ne_zero s)

private def SpecialPeriods.TauCusp.correctedLogarithmWidth (w : ℝ) (h : ℂ → ℂ) (s : ℂ) : ℂ :=
  s / w + h (Function.Periodic.qParam w s)

private theorem
    SpecialPeriods.TauCusp.correctedLogarithmWidth_eq_correctedLogarithm (w : ℝ) (h : ℂ → ℂ)
    (s : ℂ) : correctedLogarithmWidth w h s = correctedLogarithm h (s / w) := by
  simp only [correctedLogarithmWidth, correctedLogarithm, qParam_eq_exponential_div]

private theorem
    SpecialPeriods.TauCusp.correctedLogarithmWidth_exponential (w : ℝ) (h : ℂ → ℂ) (s : ℂ) :
    CuspUniformization.exponential (correctedLogarithmWidth w h s) =
      Function.Periodic.qParam w s *
        CuspUniformization.exponential (h (Function.Periodic.qParam w s)) := by
  rw [correctedLogarithmWidth_eq_correctedLogarithm, correctedLogarithm_exponential, ←
    qParam_eq_exponential_div]

private theorem
    SpecialPeriods.TauCusp.correctedLogarithmWidth_analyticAt (w : ℝ) {r : ℝ} {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r)) {s : ℂ} (hs : ‖Function.Periodic.qParam w s‖ < r) :
    AnalyticAt ℂ (correctedLogarithmWidth w h) s := by
  have hs' : s / w ∈ SpecialPeriods.CuspFamily.logBase r := by
    rw [SpecialPeriods.CuspFamily.mem_logBase]
    simpa only [qParam_eq_exponential_div] using hs
  have hcomp :=
    (correctedLogarithm_analyticAt hh hs').comp (f := fun z : ℂ => z / (w : ℂ))
      (show AnalyticAt ℂ (fun z : ℂ => z / (w : ℂ)) s from analyticAt_id.div_const)
  have hfun : correctedLogarithmWidth w h = correctedLogarithm h ∘ (fun z : ℂ => z / (w : ℂ)) :=
    funext (correctedLogarithmWidth_eq_correctedLogarithm w h)
  rw [hfun]
  exact hcomp

private theorem
    SpecialPeriods.TauCusp.correctedLogarithmWidth_analyticOnNhd (w : ℝ) {r : ℝ} {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r)) :
    AnalyticOnNhd ℂ (correctedLogarithmWidth w h) {s : ℂ | ‖Function.Periodic.qParam w s‖ < r} :=
  fun _ hs => correctedLogarithmWidth_analyticAt w hh hs

private theorem SpecialPeriods.TauCusp.div_sub_int_mul_width (w : ℝ) (hw : w ≠ 0) (s : ℂ) (k : ℤ) :
    (s - (k : ℂ) * w) / w = s / w - k := by
  have hwC : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw
  rw [sub_div, mul_div_cancel_right₀ _ hwC]

private theorem
    SpecialPeriods.TauCusp.qParam_sub_int_mul_width (w : ℝ) (hw : w ≠ 0) (s : ℂ) (k : ℤ) :
    Function.Periodic.qParam w (s - (k : ℂ) * w) = Function.Periodic.qParam w s := by
  rw [qParam_eq_exponential_div, div_sub_int_mul_width w hw,
    SpecialPeriods.CuspFamily.exponential_sub_int, qParam_eq_exponential_div]

private theorem
    SpecialPeriods.TauCusp.correctedLogarithmWidth_sub_int_mul_width (w : ℝ) (hw : w ≠ 0)
    (h : ℂ → ℂ) (s : ℂ) (k : ℤ) :
    correctedLogarithmWidth w h (s - (k : ℂ) * w) = correctedLogarithmWidth w h s - k := by
  simp only [correctedLogarithmWidth_eq_correctedLogarithm, div_sub_int_mul_width w hw,
    correctedLogarithm_sub_int]

private theorem SpecialPeriods.TauCusp.exists_simplePole_logarithmic_lift_width (w : ℝ) (hw : 0 < w)
    {a : ℂ → ℂ} (ha : AnalyticAt ℂ a 0) (ha0 : a 0 ≠ 0) {R r₀ : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) :
    ∃ r > 0,
      r < r₀ ∧
        r < 1 ∧
          ∃ h : ℂ → ℂ,
            AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
              h 0 = CuspUniformization.logarithm (1 / a 0) ∧
                (∀ t ∈ Metric.ball 0 r,
                    CuspUniformization.exponential (h t) = simplePoleUnit a t) ∧
                  ∀ s ∈ {s : ℂ | ‖Function.Periodic.qParam w s‖ < r},
                    CuspUniformization.exponential (correctedLogarithmWidth w h s) =
                        simplePoleQ a (Function.Periodic.qParam w s) ∧
                      0 < (correctedLogarithmWidth w h s).im ∧
                        ‖CuspUniformization.exponential (correctedLogarithmWidth w h s)‖ < R ∧
                          SpecialPeriods.modularJ
                              (UpperHalfPlane.ofComplex (correctedLogarithmWidth w h s)) =
                            a (Function.Periodic.qParam w s) / Function.Periodic.qParam w s := by
  obtain ⟨r, hr, hrr₀, hr1, h, hh, hh0, he, hτ⟩ :=
    exists_simplePole_logarithmic_lift ha ha0 hR hr₀
  refine ⟨r, hr, hrr₀, hr1, h, hh, hh0, he, ?_⟩
  intro s hs
  have hwC : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
  obtain ⟨z, rfl⟩ := mul_right_surjective₀ hwC s
  have hz : z ∈ SpecialPeriods.CuspFamily.logBase r := by
    apply (SpecialPeriods.CuspFamily.mem_logBase r z).mpr
    simpa only [Set.mem_ofPred_eq, qParam_eq_exponential_div, mul_div_cancel_right₀ _ hwC] using
      hs
  simpa only [correctedLogarithmWidth_eq_correctedLogarithm, qParam_eq_exponential_div,
    mul_div_cancel_right₀ _ hwC] using hτ z hz

private theorem SpecialPeriods.TauCusp.upperHalfPlane_ambient_analyticAt {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ) {s : ℂ} (hs : 0 < s.im) :
    AnalyticAt ℂ (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ)) s := by
  have hc : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ)) s :=
    ((UpperHalfPlane.contMDiff_coe.comp hτ) (UpperHalfPlane.ofComplex s)).comp s
      (UpperHalfPlane.contMDiffAt_ofComplex hs)
  exact hc.contDiffAt.analyticAt

private theorem SpecialPeriods.TauCusp.widthLogBase_convex (w : ℝ) {r : ℝ} (hr : 0 < r) :
    Convex ℝ {s : ℂ | ‖Function.Periodic.qParam w s‖ < r} := by
  have hset :
    {s : ℂ | ‖Function.Periodic.qParam w s‖ < r} =
      (LinearMap.mulRight ℝ (w : ℂ)⁻¹) ⁻¹' (SpecialPeriods.CuspFamily.logBase r : Set ℂ) := by
    ext s
    change
      ‖Function.Periodic.qParam w s‖ < r ↔ s * (w : ℂ)⁻¹ ∈ SpecialPeriods.CuspFamily.logBase r
    rw [SpecialPeriods.CuspFamily.mem_logBase, qParam_eq_exponential_div, div_eq_mul_inv]
  rw [hset]
  exact (logBase_convex r hr).linear_preimage (LinearMap.mulRight ℝ (w : ℂ)⁻¹)

private theorem
    SpecialPeriods.TauCusp.upperHalfPlane_of_qParam_norm_lt_one (w : ℝ) (hw : 0 < w) {s : ℂ}
    (hs : ‖Function.Periodic.qParam w s‖ < 1) : 0 < s.im := by
  have hsd : 0 < (s / (w : ℂ)).im :=
    upperHalfPlane_of_exponential_norm_lt_one (by simpa only [qParam_eq_exponential_div] using hs)
  rw [Complex.div_ofReal_im] at hsd
  exact (div_pos_iff_of_pos_right hw).mp hsd

private theorem SpecialPeriods.TauCusp.eqOn_correctedLogarithmWidth_of_eventuallyEq (w : ℝ) {r : ℝ}
    (hr : 0 < r) {h τ : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r))
    (hτ : AnalyticOnNhd ℂ τ {s : ℂ | ‖Function.Periodic.qParam w s‖ < r}) {a : ℂ}
    (ha : ‖Function.Periodic.qParam w a‖ < r) (heq : τ =ᶠ[𝓝 a] correctedLogarithmWidth w h) :
    Set.EqOn τ (correctedLogarithmWidth w h) {s : ℂ | ‖Function.Periodic.qParam w s‖ < r} :=
  hτ.eqOn_of_preconnected_of_eventuallyEq (correctedLogarithmWidth_analyticOnNhd w hh)
    (widthLogBase_convex w hr).isPreconnected ha heq

private theorem SpecialPeriods.TauCusp.native_eqOn_correctedLogarithmWidth_of_eventuallyEq (w : ℝ)
    (hw : 0 < w) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r)) {τ : ℍ → ℍ} (hτ : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ)
    {a : ℂ} (ha : ‖Function.Periodic.qParam w a‖ < r)
    (heq :
      (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ)) =ᶠ[𝓝 a] correctedLogarithmWidth w h) :
    Set.EqOn (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ)) (correctedLogarithmWidth w h)
      {s : ℂ | ‖Function.Periodic.qParam w s‖ < r} := by
  apply eqOn_correctedLogarithmWidth_of_eventuallyEq w hr hh ?_ ha heq
  intro s hs
  exact
    upperHalfPlane_ambient_analyticAt hτ
      (upperHalfPlane_of_qParam_norm_lt_one w hw (lt_trans hs hr1))

private theorem SpecialPeriods.TauCusp.exists_native_source_cusp_point_mo1973_17243 (w : ℝ)
    (hw : 0 < w) {r : ℝ} (hr : 0 < r) : ∃ a : ℍ, ‖Function.Periodic.qParam w (a : ℂ)‖ < r := by
  obtain ⟨s, hs⟩ := logBase_set_nonempty (Min.min r 1) (lt_min hr zero_lt_one)
  have hsn : ‖CuspUniformization.exponential s‖ < Min.min r 1 :=
    (SpecialPeriods.CuspFamily.mem_logBase (Min.min r 1) s).mp hs
  have hspos : 0 < s.im :=
    upperHalfPlane_of_exponential_norm_lt_one (lt_of_lt_of_le hsn (min_le_right r 1))
  have hswpos : 0 < (s * (w : ℂ)).im := by
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, MulZeroClass.mul_zero,
      zero_add] using mul_pos hspos hw
  refine ⟨⟨s * w, hswpos⟩, ?_⟩
  have hwC : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
  simpa only [qParam_eq_exponential_div, mul_div_cancel_right₀ _ hwC] using
    lt_of_lt_of_le hsn (min_le_left r 1)

private theorem SpecialPeriods.TauCusp.sub_int_mul_width_im_pos_mo1973_17244 (w : ℝ) (k : ℤ)
    {s : ℂ} (hs : 0 < s.im) : 0 < (s - (k : ℂ) * w).im := by
  simpa only [Complex.sub_im, Complex.mul_im, Complex.intCast_im, Complex.ofReal_im,
    MulZeroClass.mul_zero, MulZeroClass.zero_mul, add_zero, sub_zero] using hs

private theorem
    SpecialPeriods.TauCusp.global_native_sub_int_mul_width_of_cuspFormula (w : ℝ) (hw : 0 < w)
    {r : ℝ} (hr : 0 < r) {h : ℂ → ℂ} {τ : ℍ → ℍ} (hτ : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ)
    (hcusp :
      ∀ z : ℍ,
        ‖Function.Periodic.qParam w (z : ℂ)‖ < r → (τ z : ℂ) = correctedLogarithmWidth w h z)
    (k : ℤ) (z : ℍ) :
    (τ (UpperHalfPlane.ofComplex ((z : ℂ) - (k : ℂ) * w)) : ℂ) = (τ z : ℂ) - k := by
  have hleft :
    AnalyticOnNhd ℂ (fun s : ℂ => (τ (UpperHalfPlane.ofComplex (s - (k : ℂ) * w)) : ℂ))
      UpperHalfPlane.upperHalfPlaneSet := by
    intro s hs
    have hshift : AnalyticAt ℂ (fun t : ℂ => t - (k : ℂ) * w) s :=
      analyticAt_id.sub analyticAt_const
    exact
      (upperHalfPlane_ambient_analyticAt hτ (sub_int_mul_width_im_pos_mo1973_17244 w k hs)).comp
        (f := fun t : ℂ => t - (k : ℂ) * w) (x := s) hshift
  have hright :
    AnalyticOnNhd ℂ (fun s : ℂ => (τ (UpperHalfPlane.ofComplex s) : ℂ) - k)
      UpperHalfPlane.upperHalfPlaneSet :=
    fun s hs => (upperHalfPlane_ambient_analyticAt hτ hs).sub analyticAt_const
  have hconnected : IsPreconnected UpperHalfPlane.upperHalfPlaneSet :=
    ((convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm).isPreconnected
  obtain ⟨a, ha⟩ := exists_native_source_cusp_point_mo1973_17243 w hw hr
  have hcuspAmbient {s : ℂ} (hs : 0 < s.im) (hsq : ‖Function.Periodic.qParam w s‖ < r) :
    (τ (UpperHalfPlane.ofComplex s) : ℂ) = correctedLogarithmWidth w h s := by
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hs] using hcusp ⟨s, hs⟩ hsq
  have hqOpen : IsOpen {s : ℂ | ‖Function.Periodic.qParam w s‖ < r} :=
    isOpen_lt (Function.Periodic.continuous_qParam (h := w)).norm continuous_const
  have heq :
    (fun s : ℂ => (τ (UpperHalfPlane.ofComplex (s - (k : ℂ) * w)) : ℂ)) =ᶠ[𝓝 (a : ℂ)]
      (fun s : ℂ => (τ (UpperHalfPlane.ofComplex s) : ℂ) - k) := by
    filter_upwards [hqOpen.mem_nhds ha,
      UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds a.im_pos] with s hsq hs
    have hskq : ‖Function.Periodic.qParam w (s - (k : ℂ) * w)‖ < r := by
      rw [qParam_sub_int_mul_width w hw.ne']
      exact hsq
    rw [hcuspAmbient (sub_int_mul_width_im_pos_mo1973_17244 w k hs) hskq, hcuspAmbient hs hsq,
      correctedLogarithmWidth_sub_int_mul_width w hw.ne']
  have hglobal := hleft.eqOn_of_preconnected_of_eventuallyEq hright hconnected a.im_pos heq
  have hz :
    (τ (UpperHalfPlane.ofComplex ((z : ℂ) - (k : ℂ) * w)) : ℂ) =
      (τ (UpperHalfPlane.ofComplex (z : ℂ)) : ℂ) - k :=
    hglobal z.im_pos
  simpa only [UpperHalfPlane.ofComplex_apply] using hz

private theorem SpecialPeriods.TauCusp.simplePole_factorization {F : ℂ → ℂ} (hF : MeromorphicAt F 0)
    (horder : meromorphicOrderAt F 0 = (-1 : ℤ)) :
    ∃ a : ℂ → ℂ,
      AnalyticAt ℂ a 0 ∧ a 0 ≠ 0 ∧ ∃ r > 0, ∀ t ∈ Metric.ball 0 r, t ≠ 0 → F t = a t / t := by
  obtain ⟨a, ha, ha0, heq⟩ := (meromorphicOrderAt_eq_int_iff hF).mp horder
  have heq' : ∀ᶠ t in 𝓝[≠] (0 : ℂ), F t = a t / t := by
    filter_upwards [heq] with t ht
    simpa [sub_zero, zpow_neg_one, smul_eq_mul, div_eq_mul_inv, mul_comm] using ht
  rw [eventually_nhdsWithin_iff] at heq'
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp heq'
  exact ⟨a, ha, ha0, r, hr, fun t ht hne => hball ht hne⟩

private theorem SpecialPeriods.TauCusp.simplePole_factorization_of_tendsto {F : ℂ → ℂ}
    (hF : MeromorphicAt F 0) (horder : meromorphicOrderAt F 0 = (-1 : ℤ)) {c : ℂ}
    (hc : Filter.Tendsto (fun t => t * F t) (𝓝[≠] 0) (𝓝 c)) :
    ∃ a : ℂ → ℂ,
      AnalyticAt ℂ a 0 ∧
        a 0 ≠ 0 ∧ a 0 = c ∧ ∃ r > 0, ∀ t ∈ Metric.ball 0 r, t ≠ 0 → F t = a t / t := by
  obtain ⟨a, ha, ha0, r, hr, hball⟩ := simplePole_factorization hF horder
  have heq : (fun t => t * F t) =ᶠ[𝓝[≠] (0 : ℂ)] a := by
    have hnear : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ∈ Metric.ball 0 r :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr)
    filter_upwards [hnear, self_mem_nhdsWithin] with t ht hne
    have ht0 : t ≠ 0 := hne
    rw [hball t ht ht0]
    field_simp [ht0]
  have hvalue : a 0 = c := tendsto_nhds_unique ha.continuousAt.continuousWithinAt (hc.congr' heq)
  exact ⟨a, ha, ha0, hvalue, r, hr, hball⟩

private theorem SpecialPeriods.TauCusp.exists_upperHalfPlane_qParam_small_mo1973_17412 (w : ℝ)
    (hw : 0 < w) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ∃ a : ℍ, ‖Function.Periodic.qParam w (a : ℂ)‖ < r := by
  obtain ⟨s, hs⟩ := logBase_set_nonempty r hr
  have hsNorm : ‖CuspUniformization.exponential s‖ < r :=
    (SpecialPeriods.CuspFamily.mem_logBase r s).mp hs
  have hsIm : 0 < s.im := upperHalfPlane_of_exponential_norm_lt_one (hsNorm.trans hr1)
  have hwsIm : 0 < ((w : ℂ) * s).im := by
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, MulZeroClass.zero_mul,
      add_zero] using mul_pos hw hsIm
  refine ⟨⟨(w : ℂ) * s, hwsIm⟩, ?_⟩
  change ‖Function.Periodic.qParam w ((w : ℂ) * s)‖ < r
  have hwC : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
  rw [qParam_eq_exponential_div, mul_div_cancel_left₀ s hwC]
  exact hsNorm

private theorem SpecialPeriods.TauCusp.isOpen_qParam_norm_lt_mo1973_17413 (w r : ℝ) :
    IsOpen {s : ℂ | ‖Function.Periodic.qParam w s‖ < r} :=
  isOpen_lt (Function.Periodic.continuous_qParam (h := w)).norm continuous_const

end Mathoverflow1973

end
