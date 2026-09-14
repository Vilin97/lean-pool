/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.PeriodFamily.Core6
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.Recognition.Smale1
import all LeanPool.HopfProblem.HomologyTheory.SphereHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology3
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz1
import all LeanPool.HopfProblem.Recognition.Smale2
import all LeanPool.HopfProblem.Recognition.Smale3
import all LeanPool.HopfProblem.Recognition.Smale4
import all LeanPool.HopfProblem.Recognition.Smale5
import all LeanPool.HopfProblem.Recognition.Degree1
import all LeanPool.HopfProblem.Recognition.Degree2
import all LeanPool.HopfProblem.Recognition.Smale6
import all LeanPool.HopfProblem.Recognition.Smale7
import all LeanPool.HopfProblem.Recognition.Smale8
import all LeanPool.HopfProblem.Recognition.Smale9
import all LeanPool.HopfProblem.PeriodFamily.Core6

/-!
# Hopf problem: recognition · smale 10

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

private theorem Degree.MorseRearrangement.native_cylinder_flow_coordinates {Z H N E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [TopologicalSpace H] {I : ModelWithCorners ℝ Z H}
    [TopologicalSpace N] [ChartedSpace H N] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (A : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞) (hsource : A.source = Set.univ)
    (F : Flow ℝ M) (ι : N → M) (hformula : ∀ u, A u = F u.2 (ι u.1)) {x : M} (hx : x ∈ A.target)
    (t : ℝ) : A.symm (F t x) = ((A.symm x).1, t + (A.symm x).2) := by
  have hright : A (A.symm x) = x := A.right_inv' hx
  have hexpr : F t x = A ((A.symm x).1, t + (A.symm x).2) := by
    calc
      F t x = F t (A (A.symm x)) := congrArg (F t) hright.symm
      _ = F (t + (A.symm x).2) (ι (A.symm x).1) := by rw [hformula, ← F.map_add]
      _ = A ((A.symm x).1, t + (A.symm x).2) := (hformula ((A.symm x).1, t + (A.symm x).2)).symm
  rw [hexpr]
  exact A.left_inv' (by rw [hsource]; trivial)

private theorem Degree.MorseRearrangement.nativeCylinderWeight_flow {Z H N E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [TopologicalSpace H] {I : ModelWithCorners ℝ Z H}
    [TopologicalSpace N] [ChartedSpace H N] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (A : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞) (hsource : A.source = Set.univ)
    (F : Flow ℝ M) (ι : N → M) (hformula : ∀ u, A u = F u.2 (ι u.1)) (θ : N → ℝ) {x : M}
    (hx : x ∈ A.target) (t : ℝ) : nativeCylinderWeight A θ (F t x) = nativeCylinderWeight A θ x :=
  by
  unfold nativeCylinderWeight
  rw [native_cylinder_flow_coordinates A hsource F ι hformula hx t]

private theorem Degree.MorseRearrangement.exists_native_cylinder_plateau_weight {Z H N E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace H]
    {I : ModelWithCorners ℝ Z H} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
    [T2Space N] [CompactSpace N] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (A : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞)
    (hsource : A.source = Set.univ) (F : Flow ℝ M) (ι : N → M)
    (hformula : ∀ u, A u = F u.2 (ι u.1)) {S₀ S₁ : Set N} (hS₀ : IsClosed S₀) (hS₁ : IsClosed S₁)
    (hdisj : Disjoint S₀ S₁) :
    ∃ w : M → ℝ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ w A.target ∧
        (∀ x, w x ∈ Set.Icc (0 : ℝ) 1) ∧
          (∀ x ∈ A.target, ∀ t, w (F t x) = w x) ∧
            (∀ x ∈ A.target, (A.symm x).1 ∈ S₀ → w =ᶠ[𝓝 x] fun _ => 0) ∧
              (∀ x ∈ A.target, (A.symm x).1 ∈ S₁ → w =ᶠ[𝓝 x] fun _ => 1) := by
  obtain ⟨θ, hθ₀, hθ₁, hθrange⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed I hS₀ hS₁ hdisj (n := ⊤)
  refine
    ⟨nativeCylinderWeight A θ, contMDiffOn_nativeCylinderWeight A θ.contMDiff,
      nativeCylinderWeight_mem_Icc A hθrange, fun x hx t =>
      nativeCylinderWeight_flow A hsource F ι hformula θ hx t, ?_, ?_⟩
  · intro x hx hlabel
    have hθpoint : ∀ᶠ y in 𝓝 (A.symm x).1, θ y = 0 := hθ₀.filter_mono (nhds_le_nhdsSet hlabel)
    have hc : ContinuousAt (fun y => (A.symm y).1) x :=
      (A.toOpenPartialHomeomorph.symm.continuousAt hx).fst
    exact hc.tendsto.eventually hθpoint
  · intro x hx hlabel
    have hθpoint : ∀ᶠ y in 𝓝 (A.symm x).1, θ y = 1 := hθ₁.filter_mono (nhds_le_nhdsSet hlabel)
    have hc : ContinuousAt (fun y => (A.symm y).1) x :=
      (A.toOpenPartialHomeomorph.symm.continuousAt hx).fst
    exact hc.tendsto.eventually hθpoint

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.eventually_nonzero_positive_coordinate_on_upper_level_basin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y)
    {a : ℝ} (ha : f p < a) :
    ∀ᶠ x in 𝓝 p, x ∈ Degree.FlowCancellation.levelBasin F f a → (c.splitChart x).2 ≠ 0 := by
  obtain ⟨r, hr, hbox, hfield⟩ := exists_native_morse_field_block c heq
  filter_upwards [morse_coordinate_neighborhood c hr hr] with x hx
  rintro ⟨t, ht⟩ hzero
  have hlim := native_morse_negative_plane_limit c hV F hF hr hbox hfield hx.1 hx.2.1 hzero
  have hheight : Filter.Tendsto (fun t => f (F t x)) Filter.atBot (𝓝 (f p)) :=
    hf.continuousAt.tendsto.comp hlim
  have hh := (hmono x).ge_of_tendsto hheight t
  rw [ht] at hh
  exact (not_le_of_gt ha) hh

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.eventually_nonzero_negative_coordinate_on_lower_level_basin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y)
    {a : ℝ} (ha : a < f p) :
    ∀ᶠ x in 𝓝 p, x ∈ Degree.FlowCancellation.levelBasin F f a → (c.splitChart x).1 ≠ 0 := by
  obtain ⟨r, hr, hbox, hfield⟩ := exists_native_morse_field_block c heq
  filter_upwards [morse_coordinate_neighborhood c hr hr] with x hx
  rintro ⟨t, ht⟩ hzero
  have hlim := native_morse_positive_plane_limit c hV F hF hr hbox hfield hx.1 hx.2.2 hzero
  have hheight : Filter.Tendsto (fun t => f (F t x)) Filter.atTop (𝓝 (f p)) :=
    hf.continuousAt.tendsto.comp hlim
  have hh := (hmono x).le_of_tendsto hheight t
  rw [ht] at hh
  exact (not_le_of_gt ha) hh

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.eventually_constant_basin_weight_of_belt_neighborhood {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) {r : ℝ} (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (hfield :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {a k : ℝ} (ha : f p < a) {w : M → ℝ}
    (hinv : ∀ x ∈ Degree.FlowCancellation.levelBasin F f a, ∀ t : ℝ, w (F t x) = w x) {U : Set M}
    (hU : IsOpen U)
    (hcore :
      ∀ v : Smale.PuncturedHandle.UnitSphere c.PositiveCoordinates,
        (c.beltCoreMap r hr hblock v : M) ∈ U)
    (hplateau : ∀ x ∈ U, f x = f p + r ^ 2 → w x = k) :
    ∀ᶠ x in 𝓝 p, x ∈ Degree.FlowCancellation.levelBasin F f a → w x = k := by
  have hcenter : c.splitChart.symm (0 : c.NegativeCoordinates × c.PositiveCoordinates) = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have heq :=
    hfield (0 : c.NegativeCoordinates × c.PositiveCoordinates)
      ⟨Metric.mem_closedBall_self (by positivity), Metric.mem_closedBall_self (by positivity)⟩
  rw [hcenter] at heq
  filter_upwards [eventually_nonzero_positive_coordinate_on_upper_level_basin c hf hV F hF hmono
      heq ha,
    eventually_backward_exit_in_belt_neighborhood c hV F hF hr hblock hfield hU hcore] with x hne
    hexit
  intro hx
  obtain ⟨T, -, hlevel, hU⟩ := hexit (hne hx)
  exact (hinv x hx T).symm.trans (hplateau _ hU hlevel)

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.eventually_constant_basin_weight_of_attaching_neighborhood {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : Continuous f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x))) {r : ℝ} (hr : 0 < r)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
        c.splitChart.target)
    (hfield :
      ∀
        z ∈
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
            Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
        ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y)
    {a k : ℝ} (ha : a < f p) {w : M → ℝ}
    (hinv : ∀ x ∈ Degree.FlowCancellation.levelBasin F f a, ∀ t : ℝ, w (F t x) = w x) {U : Set M}
    (hU : IsOpen U)
    (hcore :
      ∀ v : Smale.PuncturedHandle.UnitSphere c.NegativeCoordinates,
        (c.attachingCoreMap r hr hblock v : M) ∈ U)
    (hplateau : ∀ x ∈ U, f x = f p - r ^ 2 → w x = k) :
    ∀ᶠ x in 𝓝 p, x ∈ Degree.FlowCancellation.levelBasin F f a → w x = k := by
  have hcenter : c.splitChart.symm (0 : c.NegativeCoordinates × c.PositiveCoordinates) = p := by
    rw [← c.splitChart_center]
    exact c.splitChart.left_inv' c.splitChart_mem_source
  have heq :=
    hfield (0 : c.NegativeCoordinates × c.PositiveCoordinates)
      ⟨Metric.mem_closedBall_self (by positivity), Metric.mem_closedBall_self (by positivity)⟩
  rw [hcenter] at heq
  filter_upwards [eventually_nonzero_negative_coordinate_on_lower_level_basin c hf hV F hF hmono
      heq ha,
    eventually_forward_exit_in_attaching_neighborhood c hV F hF hr hblock hfield hU hcore] with x
    hne hexit
  intro hx
  obtain ⟨T, -, hlevel, hU⟩ := hexit (hne hx)
  exact (hinv x hx T).symm.trans (hplateau _ hU hlevel)

private theorem
    Degree.MorseRearrangement.height_side_of_not_levelBasin {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {a : ℝ} {x : X}
    (hx : x ∉ Degree.FlowCancellation.levelBasin F f a) (t : ℝ) : f (F t x) < a ↔ f x < a := by
  have hc : Continuous (fun s : ℝ => f (F s x)) :=
    hf.comp (F.continuous continuous_id continuous_const)
  have hside (s u : ℝ) (hs : f (F s x) < a) : f (F u x) < a := by
    by_contra hu
    obtain ⟨v, hv⟩ :=
      intermediate_value_univ s u hc
        (show a ∈ Set.Icc (f (F s x)) (f (F u x)) from ⟨hs.le, le_of_not_gt hu⟩)
    exact hx ⟨v, hv⟩
  constructor
  · intro ht
    simpa only [F.map_zero_apply] using hside t 0 ht
  · intro hx
    exact hside 0 t (by simpa only [F.map_zero_apply] using hx)

attribute [local instance 100] Classical.propDecidable in
private def
    Degree.MorseRearrangement.extendedBasinWeight {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    (f : X → ℝ) (a : ℝ) (w : X → ℝ) (x : X) : ℝ :=
  if x ∈ Degree.FlowCancellation.levelBasin F f a then w x else if f x < a then 1 else 0

private theorem Degree.MorseRearrangement.extendedBasinWeight_eq {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) (f : X → ℝ) (a : ℝ) (w : X → ℝ) {x : X}
    (hx : x ∈ Degree.FlowCancellation.levelBasin F f a) : extendedBasinWeight F f a w x = w x := by
  classical simp only [extendedBasinWeight, ite_eq_left hx]

private theorem Degree.MorseRearrangement.extendedBasinWeight_flow {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) (a : ℝ) (w : X → ℝ)
    (hinv : ∀ x ∈ Degree.FlowCancellation.levelBasin F f a, ∀ t : ℝ, w (F t x) = w x) (x : X)
    (t : ℝ) : extendedBasinWeight F f a w (F t x) = extendedBasinWeight F f a w x := by
  classical
  by_cases hx : x ∈ Degree.FlowCancellation.levelBasin F f a
  · rw [extendedBasinWeight_eq _ _ _ _
        ((Degree.FlowCancellation.levelBasin_flow_iff F f a t x).mpr hx),
      extendedBasinWeight_eq _ _ _ _ hx]
    exact hinv x hx t
  · have htx : F t x ∉ Degree.FlowCancellation.levelBasin F f a := fun h =>
      hx ((Degree.FlowCancellation.levelBasin_flow_iff F f a t x).mp h)
    simp only [extendedBasinWeight, ite_eq_right hx, ite_eq_right htx,
      height_side_of_not_levelBasin F hf hx t]

private theorem
    Degree.MorseRearrangement.extendedBasinWeight_mem_Icc {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) (f : X → ℝ) (a : ℝ) (w : X → ℝ)
    (hw : ∀ x ∈ Degree.FlowCancellation.levelBasin F f a, w x ∈ Set.Icc (0 : ℝ) 1) (x : X) :
    extendedBasinWeight F f a w x ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  by_cases hx : x ∈ Degree.FlowCancellation.levelBasin F f a
  · rw [extendedBasinWeight_eq _ _ _ _ hx]
    exact hw x hx
  · simp only [extendedBasinWeight, ite_eq_right hx]
    split_ifs <;> norm_num

private theorem
    Degree.MorseRearrangement.extendedBasinWeight_lower_germ {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} {a : ℝ} {w : X → ℝ} {p : X} (hf : ContinuousAt f p) (hp : f p < a)
    (hw : ∀ᶠ x in 𝓝 p, x ∈ Degree.FlowCancellation.levelBasin F f a → w x = 1) :
    extendedBasinWeight F f a w =ᶠ[𝓝 p] fun _ => 1 := by
  classical
  have hheight : ∀ᶠ x in 𝓝 p, f x < a := hf (eventually_lt_nhds hp)
  filter_upwards [hw, hheight] with x hx hfx
  by_cases hbasin : x ∈ Degree.FlowCancellation.levelBasin F f a
  · exact (extendedBasinWeight_eq _ _ _ _ hbasin).trans (hx hbasin)
  · simp only [extendedBasinWeight, ite_eq_right hbasin, ite_eq_left hfx]

private theorem
    Degree.MorseRearrangement.extendedBasinWeight_upper_germ {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} {a : ℝ} {w : X → ℝ} {p : X} (hf : ContinuousAt f p) (hp : a < f p)
    (hw : ∀ᶠ x in 𝓝 p, x ∈ Degree.FlowCancellation.levelBasin F f a → w x = 0) :
    extendedBasinWeight F f a w =ᶠ[𝓝 p] fun _ => 0 := by
  classical
  have hheight : ∀ᶠ x in 𝓝 p, a < f x := hf (eventually_gt_nhds hp)
  filter_upwards [hw, hheight] with x hx hfx
  by_cases hbasin : x ∈ Degree.FlowCancellation.levelBasin F f a
  · exact (extendedBasinWeight_eq _ _ _ _ hbasin).trans (hx hbasin)
  · simp only [extendedBasinWeight, ite_eq_right hbasin, ite_eq_right (not_lt_of_gt hfx)]

private theorem
    Degree.MorseRearrangement.constant_germ_of_endpoint_limit {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {w : X → ℝ} (hinv : ∀ x t, w (F t x) = w x) {p x : X} {k : ℝ} {l : Filter ℝ}
    [Filter.NeBot l] (hlim : Filter.Tendsto (fun t => F t x) l (𝓝 p))
    (hgerm : w =ᶠ[𝓝 p] fun _ => k) : w =ᶠ[𝓝 x] fun _ => k := by
  obtain ⟨t, ht⟩ := (hlim.eventually (eventually_eventually_nhds.mpr hgerm)).exists
  have hc : Continuous (fun y => F t y) := F.continuous continuous_const continuous_id
  filter_upwards [hc.continuousAt.tendsto.eventually ht] with y hy
  exact (hinv y t).symm.trans hy

private theorem
    Degree.MorseRearrangement.pair_band_basin_complement {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {S : Set X}
    (hinj : Set.InjOn f S) (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hstrict : ∀ x ∉ S, StrictAnti (fun t : ℝ => f (F t x))) {p q : X} {l a u : ℝ} (hla : l < a)
    (hau : a < u) (hp : f p < a) (hq : a < f q)
    (hpair : ∀ z ∈ S, f z ∈ Set.Icc l u → z = p ∨ z = q) {x : X} (hx : f x ∈ Set.Icc l u)
    (hnot : x ∉ Degree.FlowCancellation.levelBasin F f a) :
    (f x < a ∧ Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 p)) ∨
      (a < f x ∧ Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 q)) := by
  obtain ⟨r, hr, s, hs, hrlim, hslim, -⟩ :=
    Degree.FlowCancellation.exists_strict_descent_flow_endpoints F hf hinj hmono hstrict x
  have hrheight : Filter.Tendsto (fun t => f (F t x)) Filter.atBot (𝓝 (f r)) :=
    hf.continuousAt.tendsto.comp hrlim
  have hsheight : Filter.Tendsto (fun t => f (F t x)) Filter.atTop (𝓝 (f s)) :=
    hf.continuousAt.tendsto.comp hslim
  by_cases hxa : f x < a
  · have hrle : f r ≤ a :=
      isClosed_Iic.mem_of_tendsto hrheight
        (Filter.Eventually.of_forall
          (fun t => ((height_side_of_not_levelBasin F hf hnot t).mpr hxa).le))
    have hxr : f x ≤ f r := by
      simpa only [F.map_zero_apply] using (hmono x).ge_of_tendsto hrheight 0
    have hrp : r = p :=
      (hpair r hr ⟨hx.1.trans hxr, hrle.trans hau.le⟩).resolve_right
        (by
          intro heq
          rw [heq] at hrle
          exact (not_le_of_gt hq) hrle)
    exact Or.inl ⟨hxa, by simpa only [hrp] using hrlim⟩
  · have hneq : f x ≠ a := fun heq => hnot ⟨0, by simpa only [F.map_zero_apply] using heq⟩
    have hax : a < f x := lt_of_le_of_ne (le_of_not_gt hxa) (Ne.symm hneq)
    have hsge : a ≤ f s :=
      isClosed_Ici.mem_of_tendsto hsheight
        (Filter.Eventually.of_forall
          (fun t =>
            le_of_not_gt (fun ht => hxa ((height_side_of_not_levelBasin F hf hnot t).mp ht))))
    have hsx : f s ≤ f x := by
      simpa only [F.map_zero_apply] using (hmono x).le_of_tendsto hsheight 0
    have hsq : s = q :=
      (hpair s hs ⟨hla.le.trans hsge, hsx.trans hx.2⟩).resolve_left
        (by
          intro heq
          rw [heq] at hsge
          exact (not_le_of_gt hp) hsge)
    exact Or.inr ⟨hax, by simpa only [hsq] using hslim⟩

private theorem Degree.MorseRearrangement.contMDiffOn_extendedBasinWeight_pair_band {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] (F : Flow ℝ M) {f : M → ℝ}
    (hf : Continuous f) {S : Set M} (hinj : Set.InjOn f S)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hstrict : ∀ x ∉ S, StrictAnti (fun t : ℝ => f (F t x))) {p q : M} {l a u : ℝ} (hla : l < a)
    (hau : a < u) (hp : f p < a) (hq : a < f q)
    (hpair : ∀ z ∈ S, f z ∈ Set.Icc l u → z = p ∨ z = q)
    (hB : IsOpen (Degree.FlowCancellation.levelBasin F f a)) {w : M → ℝ}
    (hw : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ w (Degree.FlowCancellation.levelBasin F f a))
    (hstationary : ∀ x ∈ Degree.FlowCancellation.levelBasin F f a, ∀ t : ℝ, w (F t x) = w x)
    (hpw : ∀ᶠ x in 𝓝 p, x ∈ Degree.FlowCancellation.levelBasin F f a → w x = 1)
    (hqw : ∀ᶠ x in 𝓝 q, x ∈ Degree.FlowCancellation.levelBasin F f a → w x = 0) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (extendedBasinWeight F f a w) (f ⁻¹' Set.Icc l u) := by
  have hpgerm := extendedBasinWeight_lower_germ F hf.continuousAt hp hpw
  have hqgerm := extendedBasinWeight_upper_germ F hf.continuousAt hq hqw
  have hinvariant (x : M) (t : ℝ) := extendedBasinWeight_flow F hf a w hstationary x t
  intro x hx
  by_cases hxB : x ∈ Degree.FlowCancellation.levelBasin F f a
  · have heq : extendedBasinWeight F f a w =ᶠ[𝓝 x] w := by
      filter_upwards [hB.mem_nhds hxB] with y hy
      exact extendedBasinWeight_eq F f a w hy
    exact (((hw x hxB).contMDiffAt (hB.mem_nhds hxB)).congr_of_eventuallyEq heq).contMDiffWithinAt
  · rcases pair_band_basin_complement F hf hinj hmono hstrict hla hau hp hq hpair hx hxB with
      ⟨-, hlim⟩ | ⟨-, hlim⟩
    · have heq := constant_germ_of_endpoint_limit F hinvariant hlim hpgerm
      exact (contMDiffAt_const.congr_of_eventuallyEq heq).contMDiffWithinAt
    · have heq := constant_germ_of_endpoint_limit F hinvariant hlim hqgerm
      exact (contMDiffAt_const.congr_of_eventuallyEq heq).contMDiffWithinAt

attribute [local instance 100] Classical.propDecidable in
private theorem Degree.MorseRearrangement.exists_stationary_pair_weight {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f)) {p q : M}
    (cp : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (cq : Smale.ManifoldMorse.SignedMorseChart (E := E) f q) {rp rq l a u : ℝ} (hrp : 0 < rp)
    (hrq : 0 < rq) (hla : l < a) (hau : a < u)
    (hpair : ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, f z ∈ Set.Icc l u → z = p ∨ z = q)
    (hbp :
      Metric.closedBall (0 : cp.NegativeCoordinates) (2 * rp) ×ˢ
          Metric.closedBall (0 : cp.PositiveCoordinates) (2 * rp) ⊆
        cp.splitChart.target)
    (hbq :
      Metric.closedBall (0 : cq.NegativeCoordinates) (2 * rq) ×ˢ
          Metric.closedBall (0 : cq.PositiveCoordinates) (2 * rq) ⊆
        cq.splitChart.target)
    (hfp :
      ∀
        z ∈
          Metric.closedBall (0 : cp.NegativeCoordinates) (2 * rp) ×ˢ
            Metric.closedBall (0 : cp.PositiveCoordinates) (2 * rp),
        ∀ᶠ y in 𝓝 (cp.splitChart.symm z), V y = cp.descentField y)
    (hfq :
      ∀
        z ∈
          Metric.closedBall (0 : cq.NegativeCoordinates) (2 * rq) ×ˢ
            Metric.closedBall (0 : cq.PositiveCoordinates) (2 * rq),
        ∀ᶠ y in 𝓝 (cq.splitChart.symm z), V y = cq.descentField y)
    (hpa : f p + rp ^ 2 ≤ a) (haq : a ≤ f q - rq ^ 2)
    (hbandp : ∀ x, f x ∈ Set.Icc (f p + rp ^ 2) a → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hbandq : ∀ x, f x ∈ Set.Icc a (f q - rq ^ 2) → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hnoconnection :
      ∀ x,
        ¬(Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q) ∧
            Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))) :
    ∃ W : M → ℝ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ W (f ⁻¹' Set.Icc l u) ∧
        (∀ x, W x ∈ Set.Icc (0 : ℝ) 1) ∧
          (∀ x t, W (F t x) = W x) ∧ (W =ᶠ[𝓝 p] fun _ => 1) ∧ (W =ᶠ[𝓝 q] fun _ => 0) := by
  have hpa' : f p < a := by nlinarith [sq_pos_of_pos hrp]
  have haq' : a < f q := by nlinarith [sq_pos_of_pos hrq]
  have hreg : ∀ x, f x = a → x ∉ Smale.ManifoldMorse.criticalPoints E f := by
    intro x hx
    exact hbandp x (by rw [hx]; exact ⟨hpa, le_rfl⟩)
  have hboundp : ∀ x, f x = f p + rp ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0 := by
    intro x hx
    exact hdesc x (hbandp x (by rw [hx]; exact ⟨le_rfl, hpa⟩))
  have hboundq : ∀ x, f x = f q - rq ^ 2 → mvfderiv 𝓘(ℝ, E) f x (V x) < 0 := by
    intro x hx
    exact hdesc x (hbandq x (by rw [hx]; exact ⟨haq, le_rfl⟩))
  let L := { x : M // f x = a }
  let _ := Smale.RegularLevel.chartedSpace hf hreg
  let _ := Smale.RegularLevel.isManifold hf hreg
  let : CompactSpace L :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let S₀ : Set L := {x | Filter.Tendsto (fun t => F t (x : M)) Filter.atBot (𝓝 q)}
  let S₁ : Set L := {x | Filter.Tendsto (fun t => F t (x : M)) Filter.atTop (𝓝 p)}
  have hS₁ : IsCompact S₁ :=
    (Degree.FlowCancellation.isCompact_forward_section_iff_of_regular_band hf hV hdesc F hF hpa
          hbandp p).mpr
      (MorseCancel.isCompact_native_belt_basin cp hf hV F hF rp hrp hbp hfp hboundp)
  have hS₀ : IsCompact S₀ :=
    (Degree.FlowCancellation.isCompact_backward_section_iff_of_regular_band hf hV hdesc F hF haq
          hbandq q).mp
      (MorseCancel.isCompact_native_attaching_basin cq hf hV F hF rq hrq hbq hfq hboundq)
  have hdisj : Disjoint S₀ S₁ :=
    Set.disjoint_left.mpr (fun x hx₀ hx₁ => hnoconnection x ⟨hx₀, hx₁⟩)
  obtain ⟨z, hz⟩ := intermediate_value_univ p q hf.continuous ⟨hpa'.le, haq'.le⟩
  obtain ⟨A, hAsource, hAtarget, hAformula, -⟩ :=
    Degree.FlowCancellation.exists_native_level_flow_cylinder hf hreg hV F hF
      (fun x hx => hdesc x (hreg x hx)) (⟨z, hz⟩ : L)
  obtain ⟨w, hw, hwrange, hwinv, hw₀, hw₁⟩ :=
    exists_native_cylinder_plateau_weight A hAsource F Subtype.val hAformula hS₀.isClosed
      hS₁.isClosed hdisj
  have hmono := Smale.FlowConstruction.antitone_flow_height hf F hF hzero hdesc
  have hV₁ := hV.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  have hbasinp :=
    Degree.FlowCancellation.levelBasin_eq_of_regular_band hf hV hdesc F hF hpa hbandp
  have hbasinq :=
    Degree.FlowCancellation.levelBasin_eq_of_regular_band hf hV hdesc F hF haq hbandq
  have hcorep (v : Smale.PuncturedHandle.UnitSphere cp.PositiveCoordinates) :
    w =ᶠ[𝓝 (cp.beltCoreMap rp hrp hbp v : M)] fun _ => 1 := by
    let x : M := cp.beltCoreMap rp hrp hbp v
    have hx : x ∈ A.target := by
      rw [hAtarget, ← hbasinp]
      exact ⟨0, by simpa only [F.map_zero_apply] using (cp.beltCoreMap rp hrp hbp v).property⟩
    have hmap : F (A.symm x).2 ((A.symm x).1 : M) = x :=
      (hAformula (A.symm x)).symm.trans (A.right_inv' hx)
    apply hw₁ x hx
    have hh := MorseCancel.native_belt_core_forward_limit cp hV₁ F hF rp hrp hbp hfp v
    apply (MorseCancel.flow_time_atTop_limit_iff F (A.symm x).2 ((A.symm x).1 : M) p).mp
    rw [hmap]
    exact hh
  have hcoreq (v : Smale.PuncturedHandle.UnitSphere cq.NegativeCoordinates) :
    w =ᶠ[𝓝 (cq.attachingCoreMap rq hrq hbq v : M)] fun _ => 0 := by
    let x : M := cq.attachingCoreMap rq hrq hbq v
    have hx : x ∈ A.target := by
      rw [hAtarget, hbasinq]
      exact
        ⟨0, by simpa only [F.map_zero_apply] using (cq.attachingCoreMap rq hrq hbq v).property⟩
    have hmap : F (A.symm x).2 ((A.symm x).1 : M) = x :=
      (hAformula (A.symm x)).symm.trans (A.right_inv' hx)
    apply hw₀ x hx
    have hh := MorseCancel.native_attaching_core_backward_limit cq hV₁ F hF rq hrq hbq hfq v
    apply (MorseCancel.flow_time_atBot_limit_iff F (A.symm x).2 ((A.symm x).1 : M) q).mp
    rw [hmap]
    exact hh
  have hstationary : ∀ x ∈ Degree.FlowCancellation.levelBasin F f a, ∀ t, w (F t x) = w x := by
    simpa only [hAtarget] using hwinv
  have hpw : ∀ᶠ x in 𝓝 p, x ∈ Degree.FlowCancellation.levelBasin F f a → w x = 1 :=
    MorseCancel.eventually_constant_basin_weight_of_belt_neighborhood cp hf.continuous hV₁ F hF
      hmono hrp hbp hfp hpa' hstationary (U := interior {x | w x = 1}) isOpen_interior
      (fun v => mem_interior_iff_mem_nhds.mpr (hcorep v))
      (fun _ hx _ => interior_subset (s := {x : M | w x = 1}) hx)
  have hqw : ∀ᶠ x in 𝓝 q, x ∈ Degree.FlowCancellation.levelBasin F f a → w x = 0 :=
    MorseCancel.eventually_constant_basin_weight_of_attaching_neighborhood cq hf.continuous hV₁ F
      hF hmono hrq hbq hfq haq' hstationary (U := interior {x | w x = 0}) isOpen_interior
      (fun v => mem_interior_iff_mem_nhds.mpr (hcoreq v))
      (fun _ hx _ => interior_subset (s := {x : M | w x = 0}) hx)
  have hB : IsOpen (Degree.FlowCancellation.levelBasin F f a) := hAtarget ▸ A.open_target
  have hwB : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ w (Degree.FlowCancellation.levelBasin F f a) :=
    hAtarget ▸ hw
  refine
    ⟨extendedBasinWeight F f a w, ?_, extendedBasinWeight_mem_Icc F f a w (fun x _ => hwrange x),
      extendedBasinWeight_flow F hf.continuous a w hstationary,
      extendedBasinWeight_lower_germ F hf.continuous.continuousAt hpa' hpw,
      extendedBasinWeight_upper_germ F hf.continuous.continuousAt haq' hqw⟩
  exact
    contMDiffOn_extendedBasinWeight_pair_band F hf.continuous hinj hmono
      (fun x hx => Smale.FlowConstruction.strictAnti_flow_height hf hV₁ F hF hzero hdesc hx) hla
      hau hpa' haq' hpair hB hwB hstationary hpw hqw

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.exists_small_native_morse_field_block {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (heq : ∀ᶠ y in 𝓝 p, V y = c.descentField y) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ,
      0 < r ∧
        r ^ 2 < ε ∧
          Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
                Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
              c.splitChart.target ∧
            ∀
              z ∈
                Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
                  Metric.closedBall (0 : c.PositiveCoordinates) (2 * r),
              ∀ᶠ y in 𝓝 (c.splitChart.symm z), V y = c.descentField y := by
  obtain ⟨R, hR, hblock, hfield⟩ := exists_native_morse_field_block c heq
  obtain ⟨r, hr, hsmall⟩ :=
    exists_between (lt_min (half_pos hR) (lt_min hε (by norm_num : (0 : ℝ) < 1)))
  have h2r : 2 * r ≤ R := by linarith [hsmall.trans_le (min_le_left _ _)]
  have hrε : r < ε := (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hr1 : r < 1 := (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hr2 : r ^ 2 < ε := lt_trans (by nlinarith : r ^ 2 < r) hrε
  have hsub :
    Metric.closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆
      Metric.closedBall (0 : c.NegativeCoordinates) R ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) R :=
    fun z hz =>
    ⟨Metric.closedBall_subset_closedBall h2r hz.1, Metric.closedBall_subset_closedBall h2r hz.2⟩
  exact ⟨r, hr, hr2, hsub.trans hblock, fun z hz => hfield z (hsub hz)⟩

private theorem
    Degree.MorseRearrangement.blended_height_exterior_germ {M : Type*} [TopologicalSpace M]
    {f θ : M → ℝ} {P Q : ℝ → ℝ} {l u : ℝ} (hf : Continuous f)
    (hP : ∀ s ∉ Set.Ioo l u, P =ᶠ[𝓝 s] id) (hQ : ∀ s ∉ Set.Ioo l u, Q =ᶠ[𝓝 s] id) {x : M}
    (hx : f x ∉ Set.Ioo l u) : (fun y => blendHeight (θ y) P Q (f y)) =ᶠ[𝓝 x] f := by
  filter_upwards [hf.continuousAt.tendsto.eventually (hP _ hx),
    hf.continuousAt.tendsto.eventually (hQ _ hx)] with y hyP hyQ
  exact blendHeight_fixed hyP hyQ _

private theorem Degree.MorseRearrangement.contMDiff_globally_blended_height {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f θ : M → ℝ}
    {P Q : ℝ → ℝ} {l u : ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hθ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ (f ⁻¹' Set.Icc l u)) (hP : ContDiff ℝ ∞ P)
    (hQ : ContDiff ℝ ∞ Q) (hPfix : ∀ s ∉ Set.Ioo l u, P =ᶠ[𝓝 s] id)
    (hQfix : ∀ s ∉ Set.Ioo l u, Q =ᶠ[𝓝 s] id) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => blendHeight (θ x) P Q (f x)) := by
  intro x
  by_cases hx : f x ∈ Set.Ioo l u
  · have hnhds : f ⁻¹' Set.Icc l u ∈ 𝓝 x :=
      Filter.mem_of_superset ((isOpen_Ioo.preimage hf.continuous).mem_nhds hx)
        (fun _ hy => ⟨hy.1.le, hy.2.le⟩)
    have hw := (hθ x ⟨hx.1.le, hx.2.le⟩).contMDiffAt hnhds
    exact
      (hw.mul (hP.contMDiff.contMDiffAt.comp x (hf x))).add
        ((contMDiffAt_const.sub hw).mul (hQ.contMDiff.contMDiffAt.comp x (hf x)))
  · exact (hf x).congr_of_eventuallyEq (blended_height_exterior_germ hf.continuous hPfix hQfix hx)

private theorem Degree.MorseRearrangement.blended_height_one_translation_germ {M : Type*}
    [TopologicalSpace M] {f θ : M → ℝ} {P Q : ℝ → ℝ} {p : M} {k : ℝ} (hf : ContinuousAt f p)
    (hθ : θ =ᶠ[𝓝 p] fun _ => 1) (hP : P =ᶠ[𝓝 (f p)] fun s => s + k) :
    (fun x => blendHeight (θ x) P Q (f x)) =ᶠ[𝓝 p] fun x => f x + k := by
  filter_upwards [hθ, hf.tendsto.eventually hP] with x hx hPx
  rw [hx, blendHeight_one]
  exact hPx

private theorem Degree.MorseRearrangement.blended_height_zero_translation_germ {M : Type*}
    [TopologicalSpace M] {f θ : M → ℝ} {P Q : ℝ → ℝ} {p : M} {k : ℝ} (hf : ContinuousAt f p)
    (hθ : θ =ᶠ[𝓝 p] fun _ => 0) (hQ : Q =ᶠ[𝓝 (f p)] fun s => s + k) :
    (fun x => blendHeight (θ x) P Q (f x)) =ᶠ[𝓝 p] fun x => f x + k := by
  filter_upwards [hθ, hf.tendsto.eventually hQ] with x hx hQx
  rw [hx, blendHeight_zero]
  exact hQx

private theorem Degree.MorseRearrangement.blended_height_directional_derivative {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f θ : M → ℝ}
    {P Q : ℝ → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => blendHeight (θ x) P Q (f x)))
    (hP : Differentiable ℝ P) (hQ : Differentiable ℝ Q) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) (hθ : ∀ x t, θ (F t x) = θ x)
    (x : M) :
    mvfderiv 𝓘(ℝ, E) (fun y => blendHeight (θ y) P Q (f y)) x (V x) =
      (θ x * deriv P (f x) + (1 - θ x) * deriv Q (f x)) * mvfderiv 𝓘(ℝ, E) f x (V x) := by
  have hw : HasDerivAt (fun t => θ (F t x)) 0 0 := by
    have heq : (fun t => θ (F t x)) = fun _ => θ x := funext (hθ x)
    rw [heq]
    exact hasDerivAt_const _ _
  have hdf := Smale.FlowConstruction.hasDerivAt_comp_integralCurve hf (hF x) 0
  have hdg := Smale.FlowConstruction.hasDerivAt_comp_integralCurve hg (hF x) 0
  have hh := hasDerivAt_blended_height hdf hw (hP _).hasDerivAt (hQ _).hasDerivAt
  have heq := hdg.unique hh
  have hdf0 := congrArg (fun y : M => mvfderiv 𝓘(ℝ, E) f y (V y)) (F.map_zero_apply x)
  have hdg0 :=
    congrArg (fun y : M => mvfderiv 𝓘(ℝ, E) (fun z => blendHeight (θ z) P Q (f z)) y (V y))
      (F.map_zero_apply x)
  change
    mvfderiv 𝓘(ℝ, E) (fun z => blendHeight (θ z) P Q (f z)) (F 0 x) (V (F 0 x)) =
      (θ (F 0 x) * deriv P (f (F 0 x)) + (1 - θ (F 0 x)) * deriv Q (f (F 0 x))) *
        mvfderiv 𝓘(ℝ, E) f (F 0 x) (V (F 0 x)) at heq
  rw [hdg0, hdf0, F.map_zero_apply] at heq
  exact heq

private theorem Degree.MorseRearrangement.exists_rearranged_morse_function_of_stationary_weight
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f θ : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} (F : Flow ℝ M)
    (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {p q : M} {l u p' q' : ℝ} (hp : f p ∈ Set.Ioo l u) (hq : f q ∈ Set.Ioo l u)
    (hp' : p' ∈ Set.Ioo l u) (hq' : q' ∈ Set.Ioo l u)
    (hpair : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, f x ∈ Set.Ioo l u → x = p ∨ x = q)
    (hθ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ (f ⁻¹' Set.Icc l u))
    (hθrange : ∀ x, θ x ∈ Set.Icc (0 : ℝ) 1) (hθinv : ∀ x t, θ (F t x) = θ x)
    (hpgerm : θ =ᶠ[𝓝 p] fun _ => 1) (hqgerm : θ =ᶠ[𝓝 q] fun _ => 0) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f ∧
            g p = p' ∧
              g q = q' ∧
                (∀ x,
                    x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) g x (V x) < 0) ∧
                  (∀ x, f x ∉ Set.Ioo l u → g =ᶠ[𝓝 x] f) ∧
                    (g =ᶠ[𝓝 p] fun x => f x + (p' - f p)) ∧
                      (g =ᶠ[𝓝 q] fun x => f x + (q' - f q)) ∧
                        (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
                            x ≠ p → x ≠ q → g =ᶠ[𝓝 x] f) ∧
                          (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
                            ∃ k : ℝ, g =ᶠ[𝓝 x] fun y => f y + k) := by
  obtain ⟨P, -, hPtrans, -, -, hPpos, hPfix⟩ :=
    exists_increasing_interval_translation_with_exterior_germs hp hp'
  obtain ⟨Q, -, hQtrans, -, -, hQpos, hQfix⟩ :=
    exists_increasing_interval_translation_with_exterior_germs hq hq'
  let g : M → ℝ := fun x => blendHeight (θ x) P Q (f x)
  have hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g :=
    contMDiff_globally_blended_height hf hθ P.contMDiff.contDiff Q.contMDiff.contDiff hPfix hQfix
  have hgp : g =ᶠ[𝓝 p] fun x => f x + (p' - f p) :=
    blended_height_one_translation_germ hf.continuous.continuousAt hpgerm hPtrans
  have hgq : g =ᶠ[𝓝 q] fun x => f x + (q' - f q) :=
    blended_height_zero_translation_germ hf.continuous.continuousAt hqgerm hQtrans
  have hexterior (x : M) (hx : f x ∉ Set.Ioo l u) : g =ᶠ[𝓝 x] f :=
    blended_height_exterior_germ hf.continuous hPfix hQfix hx
  have hothers (x : M) (hx : x ∈ Smale.ManifoldMorse.criticalPoints E f) (hxp : x ≠ p)
    (hxq : x ≠ q) : g =ᶠ[𝓝 x] f := hexterior x (fun hb => (hpair x hx hb).elim hxp hxq)
  have hkeep (x : M) (hx : x ∈ Smale.ManifoldMorse.criticalPoints E f) :
    ∃ k : ℝ, g =ᶠ[𝓝 x] fun y => f y + k := by
    by_cases hxp : x = p
    · subst x
      exact ⟨p' - f p, hgp⟩
    by_cases hxq : x = q
    · subst x
      exact ⟨q' - f q, hgq⟩
    exact ⟨0, by simpa only [add_zero] using hothers x hx hxp hxq⟩
  have hdescent (x : M) (hx : x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    mvfderiv 𝓘(ℝ, E) g x (V x) < 0 := by
    rw [blended_height_directional_derivative hf hg
        (P.contMDiff.contDiff.differentiable (by simp))
        (Q.contMDiff.contDiff.differentiable (by simp)) F hF hθinv x]
    exact
      mul_neg_of_pos_of_neg (positive_blended_slope (hθrange x) (hPpos _) (hQpos _)) (hdesc x hx)
  have hcrit : Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f := by
    ext x
    constructor
    · intro hx
      by_contra hnot
      exact Degree.FlowCancellation.not_critical_of_directional_neg (hdescent x hnot) hx
    · intro hx
      obtain ⟨k, hk⟩ := hkeep x hx
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = 0
      rw [MorseCancel.mfderiv_of_add_const_germ (hf.mdifferentiableAt (by simp)) hk]
      exact hx
  have hmg : Smale.ManifoldMorse.IsMorse E g := by
    intro x
    by_cases hx : x ∈ Smale.ManifoldMorse.criticalPoints E f
    · obtain ⟨k, hk⟩ := hkeep x hx
      exact MorseCancel.isMorseAt_of_add_const_germ (hm x) hk
    · have hreg : x ∉ Smale.ManifoldMorse.criticalPoints E g := by rwa [hcrit]
      exact Degree.MorseCancellationPreservation.isMorseAt_of_regular hg hreg
  refine ⟨g, hg, hmg, hcrit, ?_, ?_, hdescent, hexterior, hgp, hgq, hothers, hkeep⟩
  · have hh := hgp.self_of_nhds
    dsimp only at hh
    linarith
  · have hh := hgq.self_of_nhds
    dsimp only at hh
    linarith

private theorem Degree.MorseRearrangement.exists_morse_rearrangement_of_no_connection {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f)) {p q : M}
    (cp : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (cq : Smale.ManifoldMorse.SignedMorseChart (E := E) f q)
    (hfp : ∀ᶠ y in 𝓝 p, V y = cp.descentField y) (hfq : ∀ᶠ y in 𝓝 q, V y = cq.descentField y)
    {l u p' q' : ℝ} (hp : f p ∈ Set.Ioo l u) (hq : f q ∈ Set.Ioo l u) (hpq : f p < f q)
    (hp' : p' ∈ Set.Ioo l u) (hq' : q' ∈ Set.Ioo l u)
    (hpair : ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, f z ∈ Set.Icc l u → z = p ∨ z = q)
    (hnoconnection :
      ∀ x,
        ¬(Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q) ∧
            Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f ∧
            g p = p' ∧
              g q = q' ∧
                (∀ x,
                    x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) g x (V x) < 0) ∧
                  (∀ x, f x ∉ Set.Ioo l u → g =ᶠ[𝓝 x] f) ∧
                    (g =ᶠ[𝓝 p] fun x => f x + (p' - f p)) ∧
                      (g =ᶠ[𝓝 q] fun x => f x + (q' - f q)) ∧
                        (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
                            x ≠ p → x ≠ q → g =ᶠ[𝓝 x] f) ∧
                          (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
                            MorseCancel.nativeMorseIndex E g x =
                              MorseCancel.nativeMorseIndex E f x) := by
  obtain ⟨a, hpa, haq⟩ := exists_between hpq
  obtain ⟨rp, hrp, hrpa, hbp, hfieldp⟩ :=
    MorseCancel.exists_small_native_morse_field_block cp hfp (sub_pos.mpr hpa)
  obtain ⟨rq, hrq, hrqa, hbq, hfieldq⟩ :=
    MorseCancel.exists_small_native_morse_field_block cq hfq (sub_pos.mpr haq)
  have hpa' : f p + rp ^ 2 ≤ a := by linarith
  have haq' : a ≤ f q - rq ^ 2 := by linarith
  have hregular (x : M) (hx : f x ∈ Set.Ioo (f p) (f q)) :
    x ∉ Smale.ManifoldMorse.criticalPoints E f := by
    intro hcrit
    rcases hpair x hcrit ⟨hp.1.le.trans hx.1.le, hx.2.le.trans hq.2.le⟩ with heq | heq
    · rw [heq] at hx
      exact lt_irrefl _ hx.1
    · rw [heq] at hx
      exact lt_irrefl _ hx.2
  have hbandp :
    ∀ x, f x ∈ Set.Icc (f p + rp ^ 2) a → x ∉ Smale.ManifoldMorse.criticalPoints E f := by
    intro x hx
    apply hregular x
    exact ⟨by nlinarith [hx.1, sq_pos_of_pos hrp], hx.2.trans_lt haq⟩
  have hbandq :
    ∀ x, f x ∈ Set.Icc a (f q - rq ^ 2) → x ∉ Smale.ManifoldMorse.criticalPoints E f := by
    intro x hx
    apply hregular x
    exact ⟨hpa.trans_le hx.1, by nlinarith [hx.2, sq_pos_of_pos hrq]⟩
  obtain ⟨W, hW, hWrange, hWinv, hWp, hWq⟩ :=
    exists_stationary_pair_weight hf hV F hF hzero hdesc hinj cp cq hrp hrq (hp.1.trans hpa)
      (haq.trans hq.2) hpair hbp hbq hfieldp hfieldq hpa' haq' hbandp hbandq hnoconnection
  obtain ⟨g, hg, hmg, hcrit, hgp, hgq, hdescent, hexterior, hpgerm, hqgerm, hothers, -⟩ :=
    exists_rearranged_morse_function_of_stationary_weight hf hm F hF hdesc hp hq hp' hq'
      (fun x hx hband => hpair x hx ⟨hband.1.le, hband.2.le⟩) hW hWrange hWinv hWp hWq
  refine ⟨g, hg, hmg, hcrit, hgp, hgq, hdescent, hexterior, hpgerm, hqgerm, hothers, ?_⟩
  intro x hx
  by_cases hxp : x = p
  · subst x
    exact MorseCancel.nativeMorseIndex_of_add_const_germ cp hpgerm
  by_cases hxq : x = q
  · subst x
    exact MorseCancel.nativeMorseIndex_of_add_const_germ cq hqgerm
  exact MorseCancel.nativeMorseIndex_congr_germ (hothers x hx hxp hxq)

private theorem
    MorseCancel.injOn_of_exchanged_values {X Y : Type*} {f g : X → Y} {S : Set X} {p q : X}
    (hinj : Set.InjOn f S) (hp : p ∈ S) (hq : q ∈ S) (hgp : g p = f q) (hgq : g q = f p)
    (hothers : ∀ x ∈ S, x ≠ p → x ≠ q → g x = f x) : Set.InjOn g S := by
  classical
  have hform (x : X) (hx : x ∈ S) : g x = f (Equiv.swap p q x) := by
    by_cases hxp : x = p
    · subst x
      simpa only [Equiv.swap_apply_left] using hgp
    by_cases hxq : x = q
    · subst x
      simpa only [Equiv.swap_apply_right] using hgq
    simpa only [Equiv.swap_apply_def, ite_eq_right hxp, ite_eq_right hxq] using hothers x hx hxp hxq
  have hmaps : Set.MapsTo (Equiv.swap p q) S S := by
    intro x hx
    by_cases hxp : x = p
    · subst x
      simpa only [Equiv.swap_apply_left] using hq
    by_cases hxq : x = q
    · subst x
      simpa only [Equiv.swap_apply_right] using hp
    simpa only [Equiv.swap_apply_def, ite_eq_right hxp, ite_eq_right hxq] using hx
  intro x hx y hy hxy
  apply (Equiv.swap p q).injective
  apply hinj (hmaps hx) (hmaps hy)
  rw [← hform x hx, ← hform y hy]
  exact hxy

private theorem
    MorseCancel.nativeMorseCount_eq_of_preserved_indices {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    (hcrit : Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f)
    (hindex :
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E g x = nativeMorseIndex E f x)
    (k : ℕ) : nativeMorseCount E g k = nativeMorseCount E f k := by
  have heq :
    {x : M | x ∈ Smale.ManifoldMorse.criticalPoints E g ∧ nativeMorseIndex E g x = k} =
      {x : M | x ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f x = k} := by
    ext x
    change (_ ∧ _) ↔ (_ ∧ _)
    rw [hcrit]
    by_cases hx : x ∈ Smale.ManifoldMorse.criticalPoints E f
    · rw [hindex x hx]
    · simp only [hx, false_and]
  exact congrArg Set.ncard heq

private theorem MorseCancel.adapted_surgery_system_after_value_exchange {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {p q : M} [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (S : AdaptedWindows E f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hmg : Smale.ManifoldMorse.IsMorse E g) (hp : p ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hq : q ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hcrit : Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f)
    (hgp : g p = f q) (hgq : g q = f p)
    (hothers : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, x ≠ p → x ≠ q → g =ᶠ[𝓝 x] f) :
    Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) ∧ Nonempty (AdaptedWindows E g) := by
  have hinj : Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) := by
    rw [hcrit]
    exact
      injOn_of_exchanged_values S.distinct hp hq hgp hgq
        (fun x hx hxp hxq => (hothers x hx hxp hxq).self_of_nhds)
  exact ⟨hinj, nonempty_adaptedSurgeryWindows hg hmg hinj⟩

private theorem
    MorseCancel.exists_flow_preserving_value_exchange {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f))
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hmodels :
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
        ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x,
          ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p q : Smale.ManifoldMorse.criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : Smale.ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hnoconnection :
      ∀ x,
        ¬(Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q.val) ∧
            Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p.val))) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f ∧
            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) ∧
              g p = f q ∧
                g q = f p ∧
                  (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
                      x ≠ p.val → x ≠ q.val → g =ᶠ[𝓝 x] f) ∧
                    (∀ x,
                        x ∉ Smale.ManifoldMorse.criticalPoints E g →
                          mvfderiv 𝓘(ℝ, E) g x (V x) < 0) ∧
                      (∀ x ∈ Smale.ManifoldMorse.criticalPoints E g,
                          ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) g x,
                            ∀ᶠ y in 𝓝 x, V y = c.descentField y) ∧
                        (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
                            nativeMorseIndex E g x = nativeMorseIndex E f x) ∧
                          ∀ k, nativeMorseCount E g k = nativeMorseCount E f k := by
  obtain ⟨S⟩ := Smale.ManifoldMorse.nonempty_surgeryWindows hf hm hinj
  obtain ⟨cp, hcp⟩ := hmodels p p.property
  obtain ⟨cq, hcq⟩ := hmodels q q.property
  have hp : f p ∈ Set.Ioo (S.lower p) (S.upper q) :=
    ⟨S.lower_lt_value p, hpq.trans (S.value_lt_upper q)⟩
  have hq : f q ∈ Set.Ioo (S.lower p) (S.upper q) :=
    ⟨(S.lower_lt_value p).trans hpq, S.value_lt_upper q⟩
  obtain ⟨g, hg, hmg, hcrit, hgp, hgq, hdescent, -, hpgerm, hqgerm, hothers, hindices⟩ :=
    Degree.MorseRearrangement.exists_morse_rearrangement_of_no_connection hf hm hV F hF hzero
      hdesc hinj cp cq hcp hcq hp hq hpq hq hp (surgery_pair_band_isolation S p q hconsecutive)
      hnoconnection
  have hinjg : Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) := by
    rw [hcrit]
    exact
      injOn_of_exchanged_values hinj p.property q.property hgp hgq
        (fun x hx hxp hxq => (hothers x hx hxp hxq).self_of_nhds)
  have hnewmodels :
    ∀ x ∈ Smale.ManifoldMorse.criticalPoints E g,
      ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) g x,
        ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    intro x hx
    rw [hcrit] at hx
    by_cases hxp : x = p.val
    · subst x
      obtain ⟨c, hc⟩ := exists_signed_morse_chart_of_shift_germ_preserving_field cp hpgerm
      exact ⟨c, hc ▸ hcp⟩
    by_cases hxq : x = q.val
    · subst x
      obtain ⟨c, hc⟩ := exists_signed_morse_chart_of_shift_germ_preserving_field cq hqgerm
      exact ⟨c, hc ▸ hcq⟩
    obtain ⟨c, hc⟩ := hmodels x hx
    obtain ⟨d, hd⟩ := exists_signed_morse_chart_of_germ_preserving_field c (hothers x hx hxp hxq)
    exact ⟨d, hd ▸ hc⟩
  exact
    ⟨g, hg, hmg, hcrit, hinjg, hgp, hgq, hothers, (fun x hx => hdescent x (hcrit ▸ hx)),
      hnewmodels, hindices, nativeMorseCount_eq_of_preserved_indices hcrit hindices⟩

attribute [local instance 100] Classical.propDecidable in
private def
    Degree.MorseRearrangement.upperValueRank {X : Type*} [Fintype X] (h : X → ℝ) (x : X) : ℕ :=
  (Finset.univ.filter (fun y => h x < h y)).card

private def Degree.MorseRearrangement.finiteIndexDisorder {X : Type*} [Fintype X] (h : X → ℝ)
    (w : X → ℕ) : ℕ :=
  ∑ x, w x * upperValueRank h x

private theorem
    Degree.MorseRearrangement.upperValueRank_comp_equiv {X : Type*} [Fintype X] {Y : Type*}
    [Fintype Y] (h : Y → ℝ) (e : X ≃ Y) (x : X) :
    upperValueRank (h ∘ e) x = upperValueRank h (e x) := by
  classical
  unfold upperValueRank
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))

private theorem Degree.MorseRearrangement.finiteIndexDisorder_comp_equiv {X : Type*} [Fintype X]
    {Y : Type*} [Fintype Y] (h : Y → ℝ) (w : Y → ℕ) (e : X ≃ Y) :
    finiteIndexDisorder (h ∘ e) (w ∘ e) = finiteIndexDisorder h w := by
  classical
  unfold finiteIndexDisorder
  calc
    _ = ∑ x, w (e x) * upperValueRank h (e x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [upperValueRank_comp_equiv]
      rfl
    _ = _ := e.sum_comp (fun y => w y * upperValueRank h y)

private theorem
    Degree.MorseRearrangement.upperValueRank_consecutive {X : Type*} [Fintype X] {h : X → ℝ}
    (hi : Function.Injective h) {p q : X} (hpq : h p < h q)
    (hconsecutive : ∀ x, ¬(h p < h x ∧ h x < h q)) :
    upperValueRank h p = upperValueRank h q + 1 := by
  classical
  have hset :
    Finset.univ.filter (fun x => h p < h x) =
      Insert.insert q (Finset.univ.filter (fun x => h q < h x)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hx
      by_cases hxq : x = q
      · exact Or.inl hxq
      · apply Or.inr
        by_contra hnot
        have hlt : h x < h q := lt_of_le_of_ne (le_of_not_gt hnot) (fun heq => hxq (hi heq))
        exact hconsecutive x ⟨hx, hlt⟩
    · rintro (rfl | hx)
      · exact hpq
      · exact hpq.trans hx
  unfold upperValueRank
  rw [hset, Finset.card_insert_of_notMem (by simp)]

attribute [local instance 100] Classical.propDecidable in
private theorem
    Degree.MorseRearrangement.sum_erase_two_nat {X : Type*} [Fintype X] (v : X → ℕ) {p q : X}
    (hpq : p ≠ q) : ∑ x, v x = (∑ x ∈ (Finset.univ.erase p).erase q, v x) + v p + v q := by
  classical
  have hp := Finset.sum_erase_add (s := Finset.univ) v (Finset.mem_univ p)
  have hq :=
    Finset.sum_erase_add (s := Finset.univ.erase p) v
      (by simp [Ne.symm hpq] : q ∈ Finset.univ.erase p)
  omega

attribute [local instance 100] Classical.propDecidable in
private theorem
    Degree.MorseRearrangement.weighted_sum_swap_identity {X : Type*} [Fintype X] (w v : X → ℕ)
    {p q : X} (hpq : p ≠ q) :
    (∑ x, w x * v (Equiv.swap p q x)) + w p * v p + w q * v q =
      (∑ x, w x * v x) + w p * v q + w q * v p := by
  classical
  have hnew := sum_erase_two_nat (fun x => w x * v (Equiv.swap p q x)) hpq
  have hold := sum_erase_two_nat (fun x => w x * v x) hpq
  have hrest :
    (∑ x ∈ (Finset.univ.erase p).erase q, w x * v (Equiv.swap p q x)) =
      ∑ x ∈ (Finset.univ.erase p).erase q, w x * v x := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxq := (Finset.mem_erase.mp hx).1
    have hxp := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
    simp only [Equiv.swap_apply_def, ite_eq_right hxp, ite_eq_right hxq]
  rw [hrest] at hnew
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right] at hnew
  omega

attribute [local instance 100] Classical.propDecidable in
private theorem
    Degree.MorseRearrangement.finiteIndexDisorder_swap_lt {X : Type*} [Fintype X] {h : X → ℝ}
    (hi : Function.Injective h) (w : X → ℕ) {p q : X} (hpq : h p < h q)
    (hconsecutive : ∀ x, ¬(h p < h x ∧ h x < h q)) (hw : w q < w p) :
    finiteIndexDisorder (h ∘ Equiv.swap p q) w < finiteIndexDisorder h w := by
  classical
  have hne : p ≠ q := fun heq => (ne_of_lt hpq) (congrArg h heq)
  have hrank := upperValueRank_consecutive hi hpq hconsecutive
  have hid := weighted_sum_swap_identity w (upperValueRank h) hne
  have hnew :
    finiteIndexDisorder (h ∘ Equiv.swap p q) w = ∑ x, w x * upperValueRank h (Equiv.swap p q x) :=
    by
    unfold finiteIndexDisorder
    apply Finset.sum_congr rfl
    intro x _
    rw [upperValueRank_comp_equiv]
  rw [hrank] at hid
  simp only [Nat.mul_add, Nat.mul_one] at hid
  change _ < ∑ x, w x * upperValueRank h x
  rw [hnew]
  omega

private theorem Degree.MorseRearrangement.exists_adjacent_index_inversion {X : Type*} [Finite X]
    {h : X → ℝ} (hi : Function.Injective h) (w : X → ℕ) (hnot : ¬∀ x y, h x < h y → w x ≤ w y) :
    ∃ p q, h p < h q ∧ (∀ x, ¬(h p < h x ∧ h x < h q)) ∧ w q < w p := by
  classical
  let := Fintype.ofFinite X
  let _ : LinearOrder X := LinearOrder.lift' h hi
  let _ : LocallyFiniteOrder X := Fintype.toLocallyFiniteOrder
  have hnotmono : ¬Monotone w := by
    intro hm
    apply hnot
    intro x y hxy
    exact hm (show x ≤ y from hxy.le)
  have hnotadj : ¬∀ x y : X, x ⋖ y → w x ≤ w y := by
    intro hadj
    exact hnotmono ((monotone_iff_forall_covBy w).mpr hadj)
  simp only [Classical.not_forall, not_le] at hnotadj
  obtain ⟨p, q, hcover, hweights⟩ := hnotadj
  exact ⟨p, q, hcover.lt, fun x hx => hcover.2 hx.1 hx.2, hweights⟩

private theorem
    Degree.MorseRearrangement.exists_consecutive_below_of_intermediate {X : Type*} [Finite X]
    {h : X → ℝ} {p q : X} (hintermediate : ∃ x, h p < h x ∧ h x < h q) :
    ∃ r, h p < h r ∧ h r < h q ∧ ∀ x, ¬(h r < h x ∧ h x < h q) := by
  classical
  let := Fintype.ofFinite X
  obtain ⟨w, hpw, hwq⟩ := hintermediate
  let K := Finset.univ.filter (fun x => h x < h q)
  have hw : w ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwq⟩
  obtain ⟨r, hr, hmax⟩ := K.exists_max_image h ⟨w, hw⟩
  refine ⟨r, hpw.trans_le (hmax w hw), (Finset.mem_filter.mp hr).2, ?_⟩
  intro x hx
  exact (not_lt_of_ge (hmax x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.2⟩))) hx.1

private def
    Degree.MorseRearrangement.beforeValueRank {X : Type*} [Fintype X] (h : X → ℝ) (q : X) : ℕ :=
  upperValueRank (fun x => -h x) q

attribute [local instance 100] Classical.propDecidable in
private theorem Degree.MorseRearrangement.beforeValueRank_exchange_lt {X : Type*} [Fintype X]
    {h g : X → ℝ} (hi : Function.Injective h) {p q : X} (hpq : h p < h q)
    (hconsecutive : ∀ x, ¬(h p < h x ∧ h x < h q)) (hgp : g p = h q) (hgq : g q = h p)
    (hothers : ∀ x, x ≠ p → x ≠ q → g x = h x) : beforeValueRank g q < beforeValueRank h q := by
  classical
  have hform : (fun x => -g x) = (fun x => -h x) ∘ Equiv.swap p q := by
    funext x
    by_cases hxp : x = p
    · subst x
      simp only [Function.comp_apply, Equiv.swap_apply_left, hgp]
    by_cases hxq : x = q
    · subst x
      simp only [Function.comp_apply, Equiv.swap_apply_right, hgq]
    simp only [Function.comp_apply, Equiv.swap_apply_def, ite_eq_right hxp, ite_eq_right hxq,
      hothers x hxp hxq]
  have hnew : beforeValueRank g q = beforeValueRank h p := by
    unfold beforeValueRank
    rw [hform, upperValueRank_comp_equiv, Equiv.swap_apply_right]
  have hneg : Function.Injective (fun x => -h x) := fun x y hxy => hi (neg_injective hxy)
  have hgap : beforeValueRank h q = beforeValueRank h p + 1 := by
    apply upperValueRank_consecutive hneg (neg_lt_neg hpq)
    intro x hx
    exact hconsecutive x ⟨neg_lt_neg_iff.mp hx.2, neg_lt_neg_iff.mp hx.1⟩
  omega

private theorem
    MorseCancel.exists_flow_preserving_consecutive_pair {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M] {f₀ : M → ℝ}
    (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f₀) (hm₀ : Smale.ManifoldMorse.IsMorse E f₀)
    (hinj₀ : Set.InjOn f₀ (Smale.ManifoldMorse.criticalPoints E f₀))
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f₀, V x = 0)
    (hdesc₀ : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f₀ → mvfderiv 𝓘(ℝ, E) f₀ x (V x) < 0)
    (hmodels₀ :
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f₀,
        ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) f₀ x,
          ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p r q : Smale.ManifoldMorse.criticalPoints E f₀) (hrp : f₀ r < f₀ p) (hpq : f₀ p < f₀ q)
    (hnoconnection :
      ∀ j : Smale.ManifoldMorse.criticalPoints E f₀,
        j ≠ q →
          j ≠ p →
            j ≠ r →
              ∀ x,
                ¬(Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q.val) ∧
                    Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 j.val))) :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          Smale.ManifoldMorse.criticalPoints E f = Smale.ManifoldMorse.criticalPoints E f₀ ∧
            Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f) ∧
              f p = f₀ p ∧
                f r = f₀ r ∧
                  f p < f q ∧
                    (∀ z : Smale.ManifoldMorse.criticalPoints E f₀, ¬(f p < f z ∧ f z < f q)) ∧
                      (∀ x,
                          x ∉ Smale.ManifoldMorse.criticalPoints E f →
                            mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
                        (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
                            ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x,
                              ∀ᶠ y in 𝓝 x, V y = c.descentField y) ∧
                          ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f₀,
                            nativeMorseIndex E f x = nativeMorseIndex E f₀ x := by
  classical
  let _ := (Smale.ManifoldMorse.finite_criticalPoints hf₀ hm₀).fintype
  let P : ℕ → Prop := fun n =>
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          Smale.ManifoldMorse.criticalPoints E f = Smale.ManifoldMorse.criticalPoints E f₀ ∧
            Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f) ∧
              f p = f₀ p ∧
                f r = f₀ r ∧
                  f p < f q ∧
                    (∀ x,
                        x ∉ Smale.ManifoldMorse.criticalPoints E f →
                          mvfderiv 𝓘(ℝ, E) f x (V x) < 0) ∧
                      (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
                          ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) f x,
                            ∀ᶠ y in 𝓝 x, V y = c.descentField y) ∧
                        (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f₀,
                            nativeMorseIndex E f x = nativeMorseIndex E f₀ x) ∧
                          Degree.MorseRearrangement.beforeValueRank
                              (fun x : Smale.ManifoldMorse.criticalPoints E f₀ => f x) q =
                            n
  have hex : ∃ n, P n :=
    ⟨Degree.MorseRearrangement.beforeValueRank
        (fun x : Smale.ManifoldMorse.criticalPoints E f₀ => f₀ x) q,
      f₀, hf₀, hm₀, rfl, hinj₀, rfl, rfl, hpq, hdesc₀, hmodels₀, fun _ _ => rfl, rfl⟩
  obtain ⟨f, hf, hm, hcrit, hinj, hfp, hfr, hfpq, hdesc, hmodels, hindices, hrank⟩ :=
    Nat.find_spec hex
  have hconsecutive : ∀ z : Smale.ManifoldMorse.criticalPoints E f₀, ¬(f p < f z ∧ f z < f q) := by
    by_contra hnot
    push Not at hnot
    obtain ⟨z, hpz, hzq, hbefore⟩ :=
      Degree.MorseRearrangement.exists_consecutive_below_of_intermediate (h :=
        fun x : Smale.ManifoldMorse.criticalPoints E f₀ => f x) (p := p) (q := q) hnot
    have hzp : z.val ≠ p.val := fun h => (ne_of_lt hpz) (congrArg f h).symm
    have hzq' : z.val ≠ q.val := fun h => (ne_of_lt hzq) (congrArg f h)
    have hzr : z.val ≠ r.val := by
      intro h
      have hrp' : f r < f p := by rw [hfr, hfp]; exact hrp
      exact (not_lt_of_gt hpz) (by simpa only [h] using hrp')
    let zf : Smale.ManifoldMorse.criticalPoints E f := ⟨z.val, by rw [hcrit]; exact z.property⟩
    let qf : Smale.ManifoldMorse.criticalPoints E f := ⟨q.val, by rw [hcrit]; exact q.property⟩
    have hbeforef : ∀ s : Smale.ManifoldMorse.criticalPoints E f, ¬(f zf < f s ∧ f s < f qf) := by
      intro s hs
      exact hbefore ⟨s.val, by rw [← hcrit]; exact s.property⟩ hs
    obtain ⟨g, hg, hmg, hcritg, hinjg, hgz, hgq, hothers, hdescg, hmodelsg, hindicesg, -⟩ :=
      exists_flow_preserving_value_exchange hf hm hinj hV F hF (fun x hx => hzero x (hcrit ▸ hx))
        hdesc hmodels zf qf hzq hbeforef
        (hnoconnection z (fun h => hzq' (congrArg Subtype.val h))
          (fun h => hzp (congrArg Subtype.val h)) (fun h => hzr (congrArg Subtype.val h)))
    have hpcrit : p.val ∈ Smale.ManifoldMorse.criticalPoints E f := by
      rw [hcrit]
      exact p.property
    have hrcrit : r.val ∈ Smale.ManifoldMorse.criticalPoints E f := by
      rw [hcrit]
      exact r.property
    have hpq' : p.val ≠ q.val := fun h => (ne_of_lt hfpq) (congrArg f h)
    have hrq' : r.val ≠ q.val := by
      intro h
      have hrp' : f r < f p := by rw [hfr, hfp]; exact hrp
      have hlt : f r < f q := hrp'.trans hfpq
      exact (ne_of_lt hlt) (congrArg f h)
    have hgp : g p = f p := (hothers p hpcrit hzp.symm hpq').self_of_nhds
    have hgr : g r = f r := (hothers r hrcrit hzr.symm hrq').self_of_nhds
    have hidxg₀ (x : M) (hx : x ∈ Smale.ManifoldMorse.criticalPoints E f₀) :
      nativeMorseIndex E g x = nativeMorseIndex E f₀ x :=
      (hindicesg x (by rw [hcrit]; exact hx)).trans (hindices x hx)
    have hdecrease :
      Degree.MorseRearrangement.beforeValueRank
          (fun x : Smale.ManifoldMorse.criticalPoints E f₀ => g x) q <
        Degree.MorseRearrangement.beforeValueRank
          (fun x : Smale.ManifoldMorse.criticalPoints E f₀ => f x) q := by
      apply
        Degree.MorseRearrangement.beforeValueRank_exchange_lt (h :=
          fun x : Smale.ManifoldMorse.criticalPoints E f₀ => f x) (g :=
          fun x : Smale.ManifoldMorse.criticalPoints E f₀ => g x) (p := z) (q := q)
          (fun x y h =>
            Subtype.ext
              (hinj (by rw [hcrit]; exact x.property) (by rw [hcrit]; exact y.property) h))
          hzq hbefore hgz hgq
      intro x hxz hxq
      exact
        (hothers x (by rw [hcrit]; exact x.property) (fun h => hxz (Subtype.ext h))
            (fun h => hxq (Subtype.ext h))).self_of_nhds
    have hminimal :=
      Nat.find_min' hex
        ⟨g, hg, hmg, hcritg.trans hcrit, hinjg, hgp.trans hfp, hgr.trans hfr,
          (by rw [hgp, hgq]; exact hpz), hdescg, hmodelsg, hidxg₀, rfl⟩
    rw [← hrank] at hminimal
    exact (not_le_of_gt hdecrease) hminimal
  exact ⟨f, hf, hm, hcrit, hinj, hfp, hfr, hfpq, hconsecutive, hdesc, hmodels, hindices⟩

private theorem
    MorseCancel.isOpen_forward_basin_of_native_index_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hmodel : ∀ᶠ y in 𝓝 p, V y = c.descentField y)
    (hindex : Module.finrank ℝ c.NegativeCoordinates = 0) :
    IsOpen {x : M | Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p)} := by
  let : Subsingleton c.NegativeCoordinates :=
    (Module.finrank_eq_zero_iff_of_free ℝ c.NegativeCoordinates).mp hindex
  obtain ⟨r, hr, -, hbasin⟩ :=
    exists_descending_morse_basin_block c hf (hV.of_le (by simp)) F hF hzero hdesc hmodel
  have hnear : ∀ᶠ y in 𝓝 p, Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p) := by
    filter_upwards [morse_coordinate_neighborhood c hr hr] with y hy
    exact ((hbasin y hy.1 hy.2.1 hy.2.2).1).mpr (Subsingleton.elim _ _)
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨t, ht⟩ := (hx.eventually (eventually_eventually_nhds.mpr hnear)).exists
  have hc : Continuous (fun y => F t y) := F.continuous continuous_const continuous_id
  filter_upwards [hc.continuousAt.tendsto.eventually ht] with y hy
  exact (flow_time_atTop_limit_iff F t y p).mp hy

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.cancel_unique_zero_one_connection {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {p q z : M}
    (cp : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (cq : Smale.ManifoldMorse.SignedMorseChart (E := E) f q) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hindexp : nativeMorseIndex E f p = 0)
    (hindexq : nativeMorseIndex E f q = 1)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f))
    (hpc : p ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hqc : q ∈ Smale.ManifoldMorse.criticalPoints E f) (hpq : f p < f q) {l u : ℝ} (hl : l < f p)
    (hu : f q < u)
    (hpair : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc l u → x = p ∨ x = q)
    (hp : Filter.Tendsto (fun t => F t z) Filter.atTop (𝓝 p))
    (hq : Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q))
    (hunique :
      ∀ x,
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) → ∃ t, F t z = x)
    (heqp : ∀ᶠ x in 𝓝 p, V x = cp.descentField x) (heqq : ∀ᶠ x in 𝓝 q, V x = cq.descentField x) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          (Smale.ManifoldMorse.criticalPoints E g).ncard + 2 =
              (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ x,
                x ∈ Smale.ManifoldMorse.criticalPoints E g ↔
                  x ∈ Smale.ManifoldMorse.criticalPoints E f ∧ x ≠ p ∧ x ≠ q) ∧
              ∀ x, f x ∉ Set.Ioo l u → g =ᶠ[𝓝 x] f := by
  have hp0 : Module.finrank ℝ cp.NegativeCoordinates = 0 :=
    (nativeMorseIndex_eq_chart cp).symm.trans hindexp
  have hq1 : Module.finrank ℝ cq.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart cq).symm.trans hindexq
  have hdim : Module.finrank ℝ E = (Module.finrank ℝ E - 1) + 1 := by
    have h := cq.finrank_negative_add_positive
    omega
  have hindex :
    Fintype.card { i // cq.weights i = -1 } = Fintype.card { i // cp.weights i = -1 } + 1 := by
    have h :
      Module.finrank ℝ cq.NegativeCoordinates = Module.finrank ℝ cp.NegativeCoordinates + 1 := by
      omega
    simpa only [Smale.ManifoldMorse.SignedMorseChart.NegativeCoordinates,
      Smale.MorseHandle.NegativeSpace, finrank_euclideanSpace] using h
  have hbasin : ∀ᶠ x in 𝓝 z, Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) :=
    (isOpen_forward_basin_of_native_index_zero cp hf hV F hF hzero hdesc heqp hp0).mem_nhds hp
  have htrans :
    Smale.NativeTransversality.At 𝓘(ℝ, E) 𝓘(ℝ, E) 𝓘(ℝ, E) (fun _ : M => z) (fun x : M => x) z z :=
    by
    intro _ w
    refine ⟨(0, w), ?_⟩
    change
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun _ : M => z) z 0 +
          mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun x : M => x) z w =
        w
    rw [map_zero, zero_add]
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) id z w = w
    rw [mfderiv_id]
    rfl
  exact
    cancel_unique_connection_of_transverse_basin_sheets cp cq hf hm hdim hindex V hV hzero hdesc F
      hF hinj hpc hqc hpq hl hu hpair hp hq hunique heqp heqq (S := fun _ : M => z) (T :=
      fun x : M => x) mdifferentiableAt_const mdifferentiableAt_id rfl rfl
      (Filter.Eventually.of_forall (fun _ => hq)) hbasin htrans

private def Smale.EmbeddedCellAttachment.oldHomologyEquiv {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ) :
    SingularMayerVietoris.SingularHomology D.old k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology D.oldNeighborhood k :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv D.oldHomotopyEquiv k

private def Smale.EmbeddedCellAttachment.overlapHomologyEquiv {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (↥(D.oldNeighborhood ∩ D.diskPatch)) k :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv D.overlapSphereEquiv k

private def Smale.EmbeddedCellAttachment.attachingHomologyMap {N X : Type} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology D.old k :=
  SingularMayerVietoris.singularHomologyMap D.attachingSphere k

private def Smale.EmbeddedCellAttachment.oldHomologyMap {N X : Type} [NormedAddCommGroup N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ) :
    SingularMayerVietoris.SingularHomology D.old k →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology X k :=
  SingularMayerVietoris.singularHomologyMap (SingularMayerVietoris.subtypeInclusion D.old) k

private def Smale.EmbeddedCellAttachment.cellConnectingMap {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ) :
    SingularMayerVietoris.SingularHomology X (k + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k :=
  (D.overlapHomologyEquiv k).symm.toLinearMap.comp
    (SingularMayerVietoris.connectingHomomorphism D.oldNeighborhood D.diskPatch
      D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover k)

private theorem Smale.EmbeddedCellAttachment.diskPatch_homology_subsingleton {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : Smale.EmbeddedCellAttachment N X) (k : ℕ) (hk : k ≠ 0) :
    Subsingleton (SingularMayerVietoris.SingularHomology D.diskPatch k) := by
  let := D.diskPatch_contractible
  exact PeriodTorusHigherHomology.contractible_homology_subsingleton D.diskPatch k hk

private theorem Smale.EmbeddedCellAttachment.coverLeft_old {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k) :
    (D.oldHomologyEquiv k).symm
        (SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch k
            (D.overlapHomologyEquiv k a)).1 =
      D.attachingHomologyMap k a := by
  rw [SingularMayerVietoris.leftHomologyMap_apply]
  change
    SingularMayerVietoris.singularHomologyMap D.oldRetraction k
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.inclusion Set.inter_subset_left)
          k (SingularMayerVietoris.singularHomologyMap D.overlapSphereEquiv.toFun k a)) =
      SingularMayerVietoris.singularHomologyMap D.attachingSphere k a
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp, ←
    LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp]
  change
    SingularMayerVietoris.singularHomologyMap (D.overlapOldMap.comp D.overlapSphereEquiv.toFun) k
        a =
      _
  rw [D.overlapOldMap_comp_sphere]

private theorem Smale.EmbeddedCellAttachment.coverRight_old {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology D.old k) :
    SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k
        (D.oldHomologyEquiv k a, 0) =
      D.oldHomologyMap k a := by
  rw [SingularMayerVietoris.rightHomologyMap_apply, map_zero, add_zero]
  change
    SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion D.oldNeighborhood) k
        (SingularMayerVietoris.singularHomologyMap D.oldInclusion k a) =
      SingularMayerVietoris.singularHomologyMap (SingularMayerVietoris.subtypeInclusion D.old) k a
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

private theorem Smale.EmbeddedCellAttachment.coverLeft_formula {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ)
    (hk : k ≠ 0) (a : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k) :
    SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch k
        (D.overlapHomologyEquiv k a) =
      (D.oldHomologyEquiv k (D.attachingHomologyMap k a), 0) := by
  let := D.diskPatch_homology_subsingleton k hk
  apply Prod.ext
  · exact (D.oldHomologyEquiv k).symm_apply_eq.mp (D.coverLeft_old k a)
  · exact Subsingleton.elim _ _

private theorem Smale.EmbeddedCellAttachment.coverRight_formula {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ)
    (hk : k ≠ 0)
    (b :
      SingularMayerVietoris.SingularHomology D.oldNeighborhood k ×
        SingularMayerVietoris.SingularHomology D.diskPatch k) :
    SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k b =
      D.oldHomologyMap k ((D.oldHomologyEquiv k).symm b.1) := by
  let := D.diskPatch_homology_subsingleton k hk
  have hb : (D.oldHomologyEquiv k ((D.oldHomologyEquiv k).symm b.1), 0) = b :=
    Prod.ext ((D.oldHomologyEquiv k).apply_symm_apply b.1) (Subsingleton.elim _ _)
  calc
    _ =
        SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k
          (D.oldHomologyEquiv k ((D.oldHomologyEquiv k).symm b.1), 0) :=
      congrArg (SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k) hb.symm
    _ = _ := D.coverRight_old k _

private theorem Smale.EmbeddedCellAttachment.cellConnecting_eq_zero_iff {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : Smale.EmbeddedCellAttachment N X) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology X (k + 1)) :
    D.cellConnectingMap k a = 0 ↔
      SingularMayerVietoris.connectingHomomorphism D.oldNeighborhood D.diskPatch
          D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover k a =
        0 := by
  change (D.overlapHomologyEquiv k).symm _ = 0 ↔ _ = 0
  constructor
  · intro h
    exact (D.overlapHomologyEquiv k).symm.injective (h.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]

private theorem Smale.EmbeddedCellAttachment.range_coverRight {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ)
    (hk : k ≠ 0) :
    LinearMap.range (SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k) =
      LinearMap.range (D.oldHomologyMap k) := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨(D.oldHomologyEquiv k).symm b.1, (D.coverRight_formula k hk b).symm⟩
  · rintro ⟨b, rfl⟩
    exact ⟨(D.oldHomologyEquiv k b, 0), D.coverRight_old k b⟩

private theorem Smale.EmbeddedCellAttachment.cell_exact_at_old {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ)
    (hk : k ≠ 0) :
    LinearMap.range (D.attachingHomologyMap k) = LinearMap.ker (D.oldHomologyMap k) := by
  ext a
  constructor
  · rintro ⟨s, rfl⟩
    have hzero :=
      LinearMap.congr_fun
        (SingularMayerVietoris.leftHomologyMap_comp_right D.oldNeighborhood D.diskPatch k)
        (D.overlapHomologyEquiv k s)
    change
      SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k
          (SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch k
            (D.overlapHomologyEquiv k s)) =
        0 at hzero
    rw [D.coverLeft_formula k hk, D.coverRight_old] at hzero
    exact hzero
  · intro ha
    have hpair :
      (D.oldHomologyEquiv k a, 0) ∈
        LinearMap.ker (SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k) := by
      change
        SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch k
            (D.oldHomologyEquiv k a, 0) =
          0
      rw [D.coverRight_old]
      exact ha
    rw [←
      SingularMayerVietoris.exact_at_pair D.oldNeighborhood D.diskPatch D.isOpen_oldNeighborhood
        D.isOpen_diskPatch D.open_cover k] at hpair
    obtain ⟨c, hc⟩ := hpair
    refine ⟨(D.overlapHomologyEquiv k).symm c, ?_⟩
    have hc' :
      SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch k
          (D.overlapHomologyEquiv k ((D.overlapHomologyEquiv k).symm c)) =
        (D.oldHomologyEquiv k a, 0) := by
      rw [LinearEquiv.apply_symm_apply]
      exact hc
    rw [D.coverLeft_formula k hk] at hc'
    have heq :=
      congrArg
        (fun b :
            SingularMayerVietoris.SingularHomology D.oldNeighborhood k ×
              SingularMayerVietoris.SingularHomology D.diskPatch k =>
          b.1)
        hc'
    exact (D.oldHomologyEquiv k).injective heq

private theorem
    Smale.EmbeddedCellAttachment.cell_exact_at_ambient {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ) :
    LinearMap.range (D.oldHomologyMap (k + 1)) = LinearMap.ker (D.cellConnectingMap k) := by
  rw [← D.range_coverRight (k + 1) (Nat.succ_ne_zero k),
    SingularMayerVietoris.exact_at_ambient D.oldNeighborhood D.diskPatch D.isOpen_oldNeighborhood
      D.isOpen_diskPatch D.open_cover k]
  ext a
  exact (D.cellConnecting_eq_zero_iff k a).symm

private theorem
    Smale.EmbeddedCellAttachment.mem_range_cellConnecting {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k) :
    a ∈ LinearMap.range (D.cellConnectingMap k) ↔
      D.overlapHomologyEquiv k a ∈
        LinearMap.range
          (SingularMayerVietoris.connectingHomomorphism D.oldNeighborhood D.diskPatch
            D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover k) := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    change _ = D.overlapHomologyEquiv k ((D.overlapHomologyEquiv k).symm _)
    rw [LinearEquiv.apply_symm_apply]
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change (D.overlapHomologyEquiv k).symm _ = a
    rw [hx, LinearEquiv.symm_apply_apply]

private theorem
    Smale.EmbeddedCellAttachment.coverLeft_eq_zero_iff {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ)
    (hk : k ≠ 0) (a : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k) :
    SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch k
          (D.overlapHomologyEquiv k a) =
        0 ↔
      D.attachingHomologyMap k a = 0 := by
  rw [D.coverLeft_formula k hk]
  constructor
  · intro h
    have heq :=
      congrArg
        (fun b :
            SingularMayerVietoris.SingularHomology D.oldNeighborhood k ×
              SingularMayerVietoris.SingularHomology D.diskPatch k =>
          b.1)
        h
    exact (D.oldHomologyEquiv k).injective (heq.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]
    rfl

private theorem
    Smale.EmbeddedCellAttachment.cell_exact_at_sphere {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) (k : ℕ)
    (hk : k ≠ 0) :
    LinearMap.range (D.cellConnectingMap k) = LinearMap.ker (D.attachingHomologyMap k) := by
  ext a
  rw [D.mem_range_cellConnecting k,
    SingularMayerVietoris.exact_at_intersection D.oldNeighborhood D.diskPatch
      D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover k]
  exact D.coverLeft_eq_zero_iff k hk a

private theorem
    Smale.EmbeddedCellAttachment.cellConnecting_zero_apply {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X)
    [PathConnectedSpace (Metric.sphere (0 : N) 1)]
    (a : SingularMayerVietoris.SingularHomology X 1) : D.cellConnectingMap 0 a = 0 := by
  let : ContractibleSpace D.diskPatch := D.diskPatch_contractible
  let q : C(Metric.sphere (0 : N) 1, D.diskPatch) :=
    (ContinuousMap.inclusion Set.inter_subset_right).comp D.overlapSphereEquiv.toFun
  have hc :
    D.overlapHomologyEquiv 0 (D.cellConnectingMap 0 a) ∈
      LinearMap.ker (SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch 0) := by
    rw [←
      SingularMayerVietoris.exact_at_intersection D.oldNeighborhood D.diskPatch
        D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover 0]
    exact (D.mem_range_cellConnecting 0 _).mp ⟨a, rfl⟩
  change
    SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch 0
        (D.overlapHomologyEquiv 0 (D.cellConnectingMap 0 a)) =
      0 at hc
  have h := congrArg Prod.snd hc
  rw [SingularMayerVietoris.leftHomologyMap_apply] at h
  have hz : SingularMayerVietoris.singularHomologyMap q 0 (D.cellConnectingMap 0 a) = 0 := by
    rw [PeriodTorusHigherHomology.singularHomologyMap_comp]
    exact neg_eq_zero.mp h
  apply SphereHomology.singularHomologyMap_zero_injective q
  exact hz.trans (map_zero _).symm

private theorem MorseCancel.cell_oldHomologyMap_zero_injective {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X)
    [PathConnectedSpace (Metric.sphere (0 : N) 1)] : Function.Injective (D.oldHomologyMap 0) := by
  let : ContractibleSpace D.diskPatch := D.diskPatch_contractible
  let q : C(Metric.sphere (0 : N) 1, D.diskPatch) :=
    (ContinuousMap.inclusion Set.inter_subset_right).comp D.overlapSphereEquiv.toFun
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  have hpair :
    (D.oldHomologyEquiv 0 a, 0) ∈
      LinearMap.ker (SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch 0) := by
    change
      SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch 0
          (D.oldHomologyEquiv 0 a, 0) =
        0
    rw [D.coverRight_old]
    exact ha
  rw [←
    SingularMayerVietoris.exact_at_pair D.oldNeighborhood D.diskPatch D.isOpen_oldNeighborhood
      D.isOpen_diskPatch D.open_cover 0] at hpair
  obtain ⟨c, hc⟩ := hpair
  have hq :
    SingularMayerVietoris.singularHomologyMap q 0 ((D.overlapHomologyEquiv 0).symm c) = 0 := by
    have h := congrArg Prod.snd hc
    rw [SingularMayerVietoris.leftHomologyMap_apply] at h
    rw [PeriodTorusHigherHomology.singularHomologyMap_comp]
    change
      SingularMayerVietoris.singularHomologyMap (ContinuousMap.inclusion Set.inter_subset_right) 0
          (D.overlapHomologyEquiv 0 ((D.overlapHomologyEquiv 0).symm c)) =
        0
    rw [LinearEquiv.apply_symm_apply]
    exact neg_eq_zero.mp h
  have hz : (D.overlapHomologyEquiv 0).symm c = 0 :=
    SphereHomology.singularHomologyMap_zero_injective q (hq.trans (map_zero _).symm)
  have hc0 : c = 0 := by
    apply (D.overlapHomologyEquiv 0).symm.injective
    exact hz.trans (map_zero _).symm
  rw [hc0, map_zero] at hc
  apply (D.oldHomologyEquiv 0).injective
  exact (congrArg Prod.fst hc).symm.trans (map_zero _).symm

private theorem MorseCancel.cell_oldHomologyMap_zero_surjective {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X)
    [PathConnectedSpace (Metric.sphere (0 : N) 1)] : Function.Surjective (D.oldHomologyMap 0) := by
  let : ContractibleSpace D.diskPatch := D.diskPatch_contractible
  let q : C(Metric.sphere (0 : N) 1, D.diskPatch) :=
    (ContinuousMap.inclusion Set.inter_subset_right).comp D.overlapSphereEquiv.toFun
  intro a
  obtain ⟨⟨b, c⟩, hbc⟩ :=
    SingularMayerVietoris.rightHomologyMap_zero_surjective D.oldNeighborhood D.diskPatch
      D.isOpen_oldNeighborhood D.isOpen_diskPatch D.open_cover a
  obtain ⟨z, hz⟩ := SphereHomology.singularHomologyMap_zero_surjective q c
  let v := D.overlapHomologyEquiv 0 z
  have hv :
    SingularMayerVietoris.singularHomologyMap (ContinuousMap.inclusion Set.inter_subset_right) 0
        v =
      c := by
    rw [PeriodTorusHigherHomology.singularHomologyMap_comp] at hz
    exact hz
  have hzero :=
    LinearMap.congr_fun
      (SingularMayerVietoris.leftHomologyMap_comp_right D.oldNeighborhood D.diskPatch 0) v
  change
    SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch 0
        (SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch 0 v) =
      0 at hzero
  rw [SingularMayerVietoris.leftHomologyMap_apply, SingularMayerVietoris.rightHomologyMap_apply,
    map_neg, hv] at hzero
  have hrel :
    SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion D.oldNeighborhood) 0
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.inclusion Set.inter_subset_left)
          0 v) =
      SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion D.diskPatch) 0 c := by
    apply sub_eq_zero.mp
    simpa only [sub_eq_add_neg] using hzero
  refine
    ⟨(D.oldHomologyEquiv 0).symm
        (b +
          SingularMayerVietoris.singularHomologyMap
            (ContinuousMap.inclusion Set.inter_subset_left) 0 v),
      ?_⟩
  rw [← D.coverRight_old, LinearEquiv.apply_symm_apply,
    SingularMayerVietoris.rightHomologyMap_apply, map_zero, add_zero, map_add, hrel]
  exact hbc

private theorem MorseCancel.cell_oldHomologyMap_zero_bijective {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X)
    [PathConnectedSpace (Metric.sphere (0 : N) 1)] : Function.Bijective (D.oldHomologyMap 0) :=
  ⟨cell_oldHomologyMap_zero_injective D, cell_oldHomologyMap_zero_surjective D⟩

attribute [local instance 100] Classical.propDecidable in
private def MorseCancel.componentChainWeight {X : Type} [TopologicalSpace X] (x : X) :
    FirstHurewicz.Chains X 0 →ₗ[ℤ] ℤ :=
  FirstHurewicz.chainLift X 0 (fun σ => if Joined x (σ (stdSimplex.vertex 0)) then 1 else 0)

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.componentChainWeight_point {X : Type} [TopologicalSpace X] (x y : X) :
    componentChainWeight x (FirstHurewicz.pointChain y) = if Joined x y then 1 else 0 := by
  exact FirstHurewicz.chainLift_simplex X 0 _ _

private theorem MorseCancel.componentChainWeight_boundary {X : Type} [TopologicalSpace X] (x : X)
    (b : FirstHurewicz.Chains X 1) : componentChainWeight x (FirstHurewicz.boundaryOne X b) = 0 :=
  by
  classical
  have heq : (componentChainWeight x).comp (FirstHurewicz.boundaryOne X) = 0 := by
    apply FirstHurewicz.chainMap_ext X 1
    intro σ
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, FirstHurewicz.boundaryOne_simplex,
      map_sub, componentChainWeight, FirstHurewicz.chainLift_simplex, ContinuousMap.comp_apply,
      FirstHurewicz.simplexFace_zero_zero, FirstHurewicz.simplexFace_zero_one]
    have hp : Joined (σ (stdSimplex.vertex 0)) (σ (stdSimplex.vertex 1)) :=
      ⟨FirstHurewicz.simplexPath σ⟩
    have hi : Joined x (σ (stdSimplex.vertex 1)) ↔ Joined x (σ (stdSimplex.vertex 0)) :=
      ⟨fun h => h.trans hp.symm, fun h => h.trans hp⟩
    rw [hi, sub_self]
  exact LinearMap.congr_fun heq b

private theorem MorseCancel.pointClass_eq_iff_joined {X : Type} [TopologicalSpace X] (x y : X) :
    PeriodTorusHigherHomology.pointClass x = PeriodTorusHigherHomology.pointClass y ↔
      Joined x y := by
  classical
  constructor
  · intro h
    by_contra hn
    obtain ⟨b, hb⟩ :=
      (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 0
            (PeriodTorusHigherHomology.pointCycle x) (PeriodTorusHigherHomology.pointCycle y)).mp
        h
    have he := congrArg (componentChainWeight x) hb
    change
      componentChainWeight x (FirstHurewicz.boundaryOne X b) =
        componentChainWeight x (FirstHurewicz.pointChain x - FirstHurewicz.pointChain y) at he
    rw [componentChainWeight_boundary, map_sub, componentChainWeight_point,
      componentChainWeight_point, ite_eq_left (Joined.refl x), ite_eq_right hn] at he
    norm_num at he
  · rintro ⟨p⟩
    apply
      (SingularMayerVietoris.ModuleHomology.cycleClass_eq_iff (FirstHurewicz.singularComplex X) 0
          (PeriodTorusHigherHomology.pointCycle x) (PeriodTorusHigherHomology.pointCycle y)).mpr
    exact ⟨FirstHurewicz.pathChain p.symm, FirstHurewicz.boundaryOne_pathChain p.symm⟩

private theorem MorseCancel.joined_iff_of_homologyZero_injective {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y))
    (hf : Function.Injective (SingularMayerVietoris.singularHomologyMap f 0)) (x y : X) :
    Joined (f x) (f y) ↔ Joined x y := by
  rw [← pointClass_eq_iff_joined, ← pointClass_eq_iff_joined, ←
    PeriodTorusHigherHomology.singularHomologyMap_pointClass f, ←
    PeriodTorusHigherHomology.singularHomologyMap_pointClass f, hf.eq_iff]

private theorem
    MorseCancel.pathConnectedSpace_of_homologyZero_injective {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [Nonempty X] [PathConnectedSpace Y] (f : C(X, Y))
    (hf : Function.Injective (SingularMayerVietoris.singularHomologyMap f 0)) :
    PathConnectedSpace X := by
  exact
    ⟨inferInstance, fun x y =>
      (joined_iff_of_homologyZero_injective f hf x y).mp (PathConnectedSpace.joined (f x) (f y))⟩

private theorem MorseCancel.pathConnectedSpace_of_homotopyEquiv {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [PathConnectedSpace Y] (e : X ≃ₕ Y) : PathConnectedSpace X := by
  let : Nonempty X := ⟨e.invFun (Classical.arbitrary Y)⟩
  exact
    pathConnectedSpace_of_homologyZero_injective e.toFun
      (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv e 0).injective

attribute [local instance 100] Classical.propDecidable in
private def
    Smale.ManifoldMorse.MorseSurgeryData.cellOldHomologyEquiv {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) (k : ℕ) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (d.coreCellPresentation hf).old k :=
  PeriodTorusHigherHomology.homeomorphHomologyEquiv (d.cellOldHomeomorph hf) k

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.MorseSurgeryData.cellTotalHomologyEquiv {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) :
    SingularMayerVietoris.SingularHomology
        (↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap)) k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } k :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (d.coreUnionHomotopyEquiv hf) k

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.MorseSurgeryData.coreBoundaryHomologyMap {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        k →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k :=
  SingularMayerVietoris.singularHomologyMap d.coreBoundaryMap k

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.MorseSurgeryData.lowerRealizationHomologyMap {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (k : ℕ) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } k :=
  SingularMayerVietoris.singularHomologyMap d.realizedLowerInclusion k

attribute [local instance 100] Classical.propDecidable in
private def
    Smale.ManifoldMorse.MorseSurgeryData.morseConnectingMap {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) (k : ℕ) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } (k + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        k :=
  ((d.coreCellPresentation hf).cellConnectingMap k).comp
    (d.cellTotalHomologyEquiv hf (k + 1)).symm.toLinearMap

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.cellAttachingHomology_compare {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        k) :
    (d.coreCellPresentation hf).attachingHomologyMap k a =
      d.cellOldHomologyEquiv hf k (d.coreBoundaryHomologyMap k a) := by
  change
    SingularMayerVietoris.singularHomologyMap (d.coreCellPresentation hf).attachingSphere k a =
      SingularMayerVietoris.singularHomologyMap (d.cellOldHomeomorph hf).toHomotopyEquiv.toFun k
        (SingularMayerVietoris.singularHomologyMap d.coreBoundaryMap k a)
  rw [d.coreCell_attaching_eq, PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.cellOldHomology_compare {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) (a : SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k) :
    d.cellTotalHomologyEquiv hf k
        ((d.coreCellPresentation hf).oldHomologyMap k (d.cellOldHomologyEquiv hf k a)) =
      d.lowerRealizationHomologyMap k a := by
  change
    SingularMayerVietoris.singularHomologyMap (d.coreUnionHomotopyEquiv hf).toFun k
        (SingularMayerVietoris.singularHomologyMap
          (SingularMayerVietoris.subtypeInclusion (d.coreCellPresentation hf).old) k
          (SingularMayerVietoris.singularHomologyMap
            (d.cellOldHomeomorph hf).toHomotopyEquiv.toFun k a)) =
      SingularMayerVietoris.singularHomologyMap d.realizedLowerInclusion k a
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp, ←
    LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.morseConnecting_compare {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap) (k + 1)) :
    d.morseConnectingMap hf k (d.cellTotalHomologyEquiv hf (k + 1) a) =
      (d.coreCellPresentation hf).cellConnectingMap k a := by
  change
    (d.coreCellPresentation hf).cellConnectingMap k
        ((d.cellTotalHomologyEquiv hf (k + 1)).symm (d.cellTotalHomologyEquiv hf (k + 1) a)) =
      _
  rw [LinearEquiv.symm_apply_apply]

public
theorem Smale.HomologyTransport.exact_of_equivalences {R A B C A' B' C' : Type*} [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B'] [AddCommGroup C']
    [Module R C'] (eA : A ≃ₗ[R] A') (eB : B ≃ₗ[R] B') (eC : C ≃ₗ[R] C') (f : A →ₗ[R] B)
    (g : B →ₗ[R] C) (f' : A' →ₗ[R] B') (g' : B' →ₗ[R] C') (hf : ∀ a, f' (eA a) = eB (f a))
    (hg : ∀ b, g' (eB b) = eC (g b)) (hexact : LinearMap.range f = LinearMap.ker g) :
    LinearMap.range f' = LinearMap.ker g' := by
  ext b'
  constructor
  · rintro ⟨a', rfl⟩
    obtain ⟨a, rfl⟩ := eA.surjective a'
    have hfa : g (f a) = 0 := by
      have hmem : f a ∈ LinearMap.range f := ⟨a, rfl⟩
      rw [hexact] at hmem
      exact hmem
    change g' (f' (eA a)) = 0
    rw [hf, hg, hfa, map_zero]
  · intro hb'
    obtain ⟨b, rfl⟩ := eB.surjective b'
    have hgb : g b = 0 := eC.injective ((hg b).symm.trans (hb'.trans (map_zero eC).symm))
    have hb : b ∈ LinearMap.range f := by
      rw [hexact]
      exact hgb
    obtain ⟨a, ha⟩ := hb
    exact ⟨eA a, (hf a).trans (congrArg eB ha)⟩

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.morse_exact_at_lower {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) (hk : k ≠ 0) :
    LinearMap.range (d.coreBoundaryHomologyMap k) =
      LinearMap.ker (d.lowerRealizationHomologyMap k) := by
  refine
    Smale.HomologyTransport.exact_of_equivalences (LinearEquiv.refl ℤ _)
      (d.cellOldHomologyEquiv hf k).symm (d.cellTotalHomologyEquiv hf k)
      ((d.coreCellPresentation hf).attachingHomologyMap k)
      ((d.coreCellPresentation hf).oldHomologyMap k) (d.coreBoundaryHomologyMap k)
      (d.lowerRealizationHomologyMap k) ?_ ?_ ((d.coreCellPresentation hf).cell_exact_at_old k hk)
  · intro a
    change
      d.coreBoundaryHomologyMap k a =
        (d.cellOldHomologyEquiv hf k).symm ((d.coreCellPresentation hf).attachingHomologyMap k a)
    rw [d.cellAttachingHomology_compare, LinearEquiv.symm_apply_apply]
  · intro a
    have h := d.cellOldHomology_compare hf k ((d.cellOldHomologyEquiv hf k).symm a)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.morse_exact_at_upper {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) :
    LinearMap.range (d.lowerRealizationHomologyMap (k + 1)) =
      LinearMap.ker (d.morseConnectingMap hf k) := by
  refine
    Smale.HomologyTransport.exact_of_equivalences (d.cellOldHomologyEquiv hf (k + 1)).symm
      (d.cellTotalHomologyEquiv hf (k + 1)) (LinearEquiv.refl ℤ _)
      ((d.coreCellPresentation hf).oldHomologyMap (k + 1))
      ((d.coreCellPresentation hf).cellConnectingMap k) (d.lowerRealizationHomologyMap (k + 1))
      (d.morseConnectingMap hf k) ?_ ?_ ((d.coreCellPresentation hf).cell_exact_at_ambient k)
  · intro a
    have h := d.cellOldHomology_compare hf (k + 1) ((d.cellOldHomologyEquiv hf (k + 1)).symm a)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  · exact d.morseConnecting_compare hf k

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.morse_exact_at_attachingSphere {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) (hk : k ≠ 0) :
    LinearMap.range (d.morseConnectingMap hf k) = LinearMap.ker (d.coreBoundaryHomologyMap k) := by
  refine
    Smale.HomologyTransport.exact_of_equivalences (d.cellTotalHomologyEquiv hf (k + 1))
      (LinearEquiv.refl ℤ _) (d.cellOldHomologyEquiv hf k).symm
      ((d.coreCellPresentation hf).cellConnectingMap k)
      ((d.coreCellPresentation hf).attachingHomologyMap k) (d.morseConnectingMap hf k)
      (d.coreBoundaryHomologyMap k) ?_ ?_ ((d.coreCellPresentation hf).cell_exact_at_sphere k hk)
  · exact d.morseConnecting_compare hf k
  · intro a
    change
      d.coreBoundaryHomologyMap k a =
        (d.cellOldHomologyEquiv hf k).symm ((d.coreCellPresentation hf).attachingHomologyMap k a)
    rw [d.cellAttachingHomology_compare, LinearEquiv.symm_apply_apply]

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.lowerHomology_subsingleton_of_upper_and_sphere
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [T2Space M] {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hf : Continuous f) (k : ℕ) (hk : k ≠ 0)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } k)]
    [Subsingleton
        (SingularMayerVietoris.SingularHomology
          (Metric.sphere (0 : d.chart.NegativeCoordinates) 1) k)] :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k) := by
  have hall :
    ∀ a : SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k, a = 0 :=
    by
    intro a
    have ha : a ∈ LinearMap.ker (d.lowerRealizationHomologyMap k) := Subsingleton.elim _ _
    rw [← d.morse_exact_at_lower hf k hk] at ha
    obtain ⟨s, hs⟩ := ha
    have hs0 : s = 0 := Subsingleton.elim _ _
    rw [hs0, map_zero] at hs
    exact hs.symm
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

private theorem Smale.ManifoldMorse.MorseSurgeryData.attachingSphere_pathConnected {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates) :
    PathConnectedSpace (Metric.sphere (0 : d.chart.NegativeCoordinates) 1) :=
  isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by omega)) _ zero_le_one)

private theorem Smale.ManifoldMorse.MorseSurgeryData.morseConnecting_zero_apply {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    (a : SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 1) :
    d.morseConnectingMap hf 0 a = 0 := by
  let := d.attachingSphere_pathConnected hindex
  exact (d.coreCellPresentation hf).cellConnecting_zero_apply _

private theorem Smale.ManifoldMorse.MorseSurgeryData.lowerRealization_one_surjective {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates) :
    Function.Surjective (d.lowerRealizationHomologyMap 1) := by
  intro a
  have ha : a ∈ LinearMap.ker (d.morseConnectingMap hf 0) :=
    d.morseConnecting_zero_apply hf hindex a
  rw [← d.morse_exact_at_upper hf 0] at ha
  exact ha

private theorem Smale.ManifoldMorse.MorseSurgeryData.upperHomologyOne_subsingleton {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 1)] :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 1) :=
  (d.lowerRealization_one_surjective hf hindex).subsingleton

private theorem
    MorseCancel.native_lowerRealization_zero_bijective {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates) :
    Function.Bijective (d.lowerRealizationHomologyMap 0) := by
  let := d.attachingSphere_pathConnected hindex
  have hi := cell_oldHomologyMap_zero_bijective (d.coreCellPresentation hf)
  have heq :
    d.lowerRealizationHomologyMap 0 =
      (d.cellTotalHomologyEquiv hf 0).toLinearMap.comp
        (((d.coreCellPresentation hf).oldHomologyMap 0).comp
          (d.cellOldHomologyEquiv hf 0).toLinearMap) := by
    ext a
    exact (d.cellOldHomology_compare hf 0 a).symm
  rw [heq]
  exact
    (d.cellTotalHomologyEquiv hf 0).bijective.comp
      (hi.comp (d.cellOldHomologyEquiv hf 0).bijective)

private theorem MorseCancel.native_lower_pathConnected_of_upper {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    [PathConnectedSpace { z : M // f z ≤ f p + d.radius ^ 2 }] :
    PathConnectedSpace { z : M // f z ≤ f p - d.radius ^ 2 } := by
  let := d.attachingSphere_pathConnected hindex
  let : Nonempty { z : M // f z ≤ f p - d.radius ^ 2 } :=
    ⟨d.coreBoundaryMap (Classical.arbitrary (Metric.sphere (0 : d.chart.NegativeCoordinates) 1))⟩
  exact
    pathConnectedSpace_of_homologyZero_injective d.realizedLowerInclusion
      (native_lowerRealization_zero_bijective d hf hindex).1

private def Smale.ManifoldMorse.SurgeryWindows.values {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) : Finset ℝ :=
  (S.finite.image f).toFinset

private def Smale.ManifoldMorse.SurgeryWindows.count {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) : ℕ :=
  S.values.card

private def Smale.ManifoldMorse.SurgeryWindows.point {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) :
    Fin S.count ≃ Smale.ManifoldMorse.criticalPoints E f :=
  ((S.values.orderIsoOfFin rfl).toEquiv.trans
        (Equiv.setCongr (S.finite.image f).coe_toFinset)).trans
    (Equiv.Set.imageOfInjOn f (Smale.ManifoldMorse.criticalPoints E f) S.distinct).symm

private theorem Smale.ManifoldMorse.SurgeryWindows.point_value {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (i : Fin S.count) :
    f (S.point i) = S.values.orderEmbOfFin rfl i := by
  let e := Equiv.Set.imageOfInjOn f (Smale.ManifoldMorse.criticalPoints E f) S.distinct
  let v : f '' Smale.ManifoldMorse.criticalPoints E f :=
    Equiv.setCongr (S.finite.image f).coe_toFinset (S.values.orderIsoOfFin rfl i)
  have h :=
    congrArg (fun x : f '' Smale.ManifoldMorse.criticalPoints E f => (x : ℝ))
      (e.apply_symm_apply v)
  exact h

private theorem
    Smale.ManifoldMorse.SurgeryWindows.point_strictMono {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) :
    StrictMono (fun i : Fin S.count => f (S.point i)) := by
  intro i j hij
  change f (S.point i) < f (S.point j)
  rw [S.point_value, S.point_value]
  exact (S.values.orderEmbOfFin rfl).strictMono hij

private theorem
    Smale.ManifoldMorse.SurgeryWindows.point_consecutive {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (i j : Fin S.count) (hij : i.val + 1 = j.val) :
    ∀ r : Smale.ManifoldMorse.criticalPoints E f, ¬(f (S.point i) < f r ∧ f r < f (S.point j)) := by
  intro r hr
  obtain ⟨k, rfl⟩ := S.point.surjective r
  have hik : i < k := S.point_strictMono.lt_iff_lt.mp hr.1
  have hkj : k < j := S.point_strictMono.lt_iff_lt.mp hr.2
  have hik' : i.val < k.val := hik
  have hkj' : k.val < j.val := hkj
  omega

private theorem
    Smale.ManifoldMorse.SurgeryWindows.ordered_windows {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (i j : Fin S.count) (hij : i < j) :
    S.upper (S.point i) < S.lower (S.point j) :=
  S.upper_lt_lower _ _ (S.point_strictMono hij)

private theorem Smale.ManifoldMorse.SurgeryWindows.consecutive_regular {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (i j : Fin S.count) (hij : i.val + 1 = j.val) :
    ∀ x,
      f x ∈ Set.Icc (S.upper (S.point i)) (S.lower (S.point j)) →
        x ∉ Smale.ManifoldMorse.criticalPoints E f :=
  S.regular_between _ _ (S.point_consecutive i j hij)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SurgeryWindows.exists_consecutiveBandBridge {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (i j : Fin S.count)
    (hij : i.val + 1 = j.val) :
    letI := Smale.RegularLevel.chartedSpace hf (S.data (S.point i)).upper_regular
    letI := Smale.RegularLevel.chartedSpace hf (S.data (S.point j)).lower_regular
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      ∃ b :
        Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
          (S.data (S.point i)).UpperLevel (S.data (S.point j)).LowerLevel ∞,
        D '' {x : M | f x ≤ S.upper (S.point i)} = {x : M | f x ≤ S.lower (S.point j)} ∧
          ∀ x : (S.data (S.point i)).UpperLevel, (b x : M) = D x := by
  have hlt : i < j := by change i.val < j.val; omega
  exact S.exists_bandBridge hf _ _ (S.point_strictMono hlt) (S.point_consecutive i j hij)

private theorem
    Smale.ManifoldMorse.mem_criticalPoints_of_localMin {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {p : M} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hmin : IsLocalMin f p) :
    p ∈ criticalPoints E f := by
  let e := chartAt E p
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas p
  have hp : p ∈ e.source := mem_chart_source E p
  apply (mem_criticalPoints_iff hf he hp).mpr
  have hmin' : IsLocalMin f (e.symm (e p)) := by rw [e.left_inv hp]; exact hmin
  exact (hmin'.comp_continuous (e.continuousAt_symm (e.map_source hp))).fderiv_eq_zero

private theorem
    Smale.ManifoldMorse.mem_criticalPoints_of_localMax {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    {p : M} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hmax : IsLocalMax f p) :
    p ∈ criticalPoints E f := by
  let e := chartAt E p
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas p
  have hp : p ∈ e.source := mem_chart_source E p
  apply (mem_criticalPoints_iff hf he hp).mpr
  have hmax' : IsLocalMax f (e.symm (e p)) := by rw [e.left_inv hp]; exact hmax
  exact (hmax'.comp_continuous (e.continuousAt_symm (e.map_source hp))).fderiv_eq_zero

private theorem Smale.ManifoldMorse.unique_extrema_of_two_critical_values {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} [CompactSpace M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {p q : M} (hpq : f p < f q) (hcrit : ∀ x ∈ criticalPoints E f, x = p ∨ x = q) :
    (∀ x, f x ≤ f p → x = p) ∧ (∀ x, f q ≤ f x → x = q) := by
  obtain ⟨u, _, hmin⟩ :=
    isCompact_univ.exists_isMinOn ⟨p, Set.mem_univ p⟩ hf.continuous.continuousOn
  obtain ⟨v, _, hmax⟩ :=
    isCompact_univ.exists_isMaxOn ⟨q, Set.mem_univ q⟩ hf.continuous.continuousOn
  have humin : IsLocalMin f u := Filter.Eventually.of_forall (fun x => hmin (Set.mem_univ x))
  have hvmax : IsLocalMax f v := Filter.Eventually.of_forall (fun x => hmax (Set.mem_univ x))
  have hup : u = p := by
    rcases hcrit u (mem_criticalPoints_of_localMin hf humin) with h | h
    · exact h
    · have hle : f u ≤ f p := hmin (Set.mem_univ p)
      rw [h] at hle
      exact False.elim (not_le_of_gt hpq hle)
  have hvq : v = q := by
    rcases hcrit v (mem_criticalPoints_of_localMax hf hvmax) with h | h
    · have hle : f q ≤ f v := hmax (Set.mem_univ q)
      rw [h] at hle
      exact False.elim (not_le_of_gt hpq hle)
    · exact h
  have hglobalMin (x : M) : f p ≤ f x := by rw [← hup]; exact hmin (Set.mem_univ x)
  have hglobalMax (x : M) : f x ≤ f q := by rw [← hvq]; exact hmax (Set.mem_univ x)
  constructor
  · intro x hx
    have hlocal : IsLocalMin f x := Filter.Eventually.of_forall (fun y => hx.trans (hglobalMin y))
    rcases hcrit x (mem_criticalPoints_of_localMin hf hlocal) with h | h
    · exact h
    · rw [h] at hx
      exact False.elim (not_le_of_gt hpq hx)
  · intro x hx
    have hlocal : IsLocalMax f x := Filter.Eventually.of_forall (fun y => (hglobalMax y).trans hx)
    rcases hcrit x (mem_criticalPoints_of_localMax hf hlocal) with h | h
    · rw [h] at hx
      exact False.elim (not_le_of_gt hpq hx)
    · exact h

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.negative_eq_zero_of_localMin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hmin : IsLocalMin f p)
    (u : c.NegativeCoordinates) : u = 0 := by
  by_contra hu
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  obtain ⟨U, hUmin, hU, hpU⟩ := _root_.mem_nhds_iff.mp hmin
  obtain ⟨r, hr, hblock⟩ := c.exists_closed_productBlock_in hU hpU
  let z : c.NegativeCoordinates := (r / ‖u‖) • u
  have hz : ‖z‖ = r := by
    rw [show z = (r / ‖u‖) • u from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hr hnorm), div_mul_cancel₀ _ hnorm.ne']
  have hpoint :=
    hblock
      (show (z, (0 : c.PositiveCoordinates)) ∈ Metric.closedBall 0 r ×ˢ Metric.closedBall 0 r from
        ⟨mem_closedBall_zero_iff.mpr hz.le, by
          simpa only [mem_closedBall_zero_iff, norm_zero] using hr.le⟩)
  have hh := hUmin hpoint.2
  change f p ≤ f (c.splitChart.symm (z, (0 : c.PositiveCoordinates))) at hh
  rw [c.splitChart_inverse_equation hpoint.1, hz, norm_zero] at hh
  nlinarith [sq_pos_of_pos hr]

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.subsingleton_negative_of_localMin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hmin : IsLocalMin f p) :
    Subsingleton c.NegativeCoordinates :=
  ⟨fun u v =>
    (c.negative_eq_zero_of_localMin hmin u).trans (c.negative_eq_zero_of_localMin hmin v).symm⟩

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.positive_eq_zero_of_localMax {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hmax : IsLocalMax f p)
    (v : c.PositiveCoordinates) : v = 0 := by
  by_contra hv
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  obtain ⟨U, hUmax, hU, hpU⟩ := _root_.mem_nhds_iff.mp hmax
  obtain ⟨r, hr, hblock⟩ := c.exists_closed_productBlock_in hU hpU
  let z : c.PositiveCoordinates := (r / ‖v‖) • v
  have hz : ‖z‖ = r := by
    rw [show z = (r / ‖v‖) • v from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hr hnorm), div_mul_cancel₀ _ hnorm.ne']
  have hpoint :=
    hblock
      (show ((0 : c.NegativeCoordinates), z) ∈ Metric.closedBall 0 r ×ˢ Metric.closedBall 0 r from
        ⟨by simpa only [mem_closedBall_zero_iff, norm_zero] using hr.le,
          mem_closedBall_zero_iff.mpr hz.le⟩)
  have hh := hUmax hpoint.2
  change f (c.splitChart.symm ((0 : c.NegativeCoordinates), z)) ≤ f p at hh
  rw [c.splitChart_inverse_equation hpoint.1, norm_zero, hz] at hh
  nlinarith [sq_pos_of_pos hr]

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.subsingleton_positive_of_localMax {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hmax : IsLocalMax f p) :
    Subsingleton c.PositiveCoordinates :=
  ⟨fun u v =>
    (c.positive_eq_zero_of_localMax hmax u).trans (c.positive_eq_zero_of_localMax hmax v).symm⟩

private theorem Smale.exists_small_sublevel_subset {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {f : X → ℝ} (hf : Continuous f) {p : X} (hunique : ∀ x, f x ≤ f p → x = p) {U : Set X}
    (hU : IsOpen U) (hpU : p ∈ U) : ∃ ε > (0 : ℝ), {x | f x ≤ f p + ε} ⊆ U := by
  by_cases hne : Uᶜ.Nonempty
  · obtain ⟨q, hq, hmin⟩ := hU.isClosed_compl.isCompact.exists_isMinOn hne hf.continuousOn
    have hgap : f p < f q := by
      by_contra! h
      exact hq (hunique q h ▸ hpU)
    refine ⟨(f q - f p) / 2, half_pos (sub_pos.mpr hgap), ?_⟩
    intro x hx
    by_contra hxU
    have hqx : f q ≤ f x := hmin hxU
    change f x ≤ f p + (f q - f p) / 2 at hx
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x _
    by_contra hx
    exact hne ⟨x, hx⟩

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.exists_minimum_disk_sublevel_with_height
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hf : Continuous f)
    (hunique : ∀ x, f x ≤ f p → x = p) {b : ℝ} (hb : f p < b) :
    ∃ ρ > (0 : ℝ),
      f p + ρ ^ 2 < b ∧
        ∃ e : Smale.MorseHandle.UnitDisk c.PositiveCoordinates ≃ₜ { x : M // f x ≤ f p + ρ ^ 2 },
          ∀ v, f (e v).1 = f p + ρ ^ 2 * ‖(v : c.PositiveCoordinates)‖ ^ 2 := by
  have hglobal : ∀ x, f p ≤ f x := by
    intro x
    by_contra! h
    have hxp := hunique x h.le
    rw [hxp] at h
    exact lt_irrefl _ h
  have hmin : IsLocalMin f p := Filter.Eventually.of_forall hglobal
  let : Subsingleton c.NegativeCoordinates := c.subsingleton_negative_of_localMin hmin
  obtain ⟨R, hR, hblockR⟩ := c.exists_closed_productBlock
  obtain ⟨ε, hε, hsublevel⟩ :=
    Smale.exists_small_sublevel_subset hf hunique c.splitChart.open_source c.splitChart_mem_source
  let δ := Min.min ε (b - f p)
  have hδ : 0 < δ := lt_min hε (sub_pos.mpr hb)
  let ρ := Min.min (R / 2) (Min.min 1 (δ / 2))
  have hρ : 0 < ρ := lt_min (half_pos hR) (lt_min zero_lt_one (half_pos hδ))
  have hρR : ρ ≤ R / 2 := min_le_left _ _
  have hρone : ρ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hρδ : ρ ≤ δ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hρsq : ρ ^ 2 < δ := by nlinarith
  have hsqε : ρ ^ 2 < ε := hρsq.trans_le (min_le_left _ _)
  have hsqb : ρ ^ 2 < b - f p := hρsq.trans_le (min_le_right _ _)
  have hblock :
    Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
      c.splitChart.target := by
    intro z hz
    have hr : 2 * ρ ≤ R := by linarith
    exact
      hblockR
        ⟨Metric.closedBall_subset_closedBall hr hz.1, Metric.closedBall_subset_closedBall hr hz.2⟩
  let z₀ : Smale.MorseHandle.UnitDisk c.NegativeCoordinates := ⟨0, by simp⟩
  let h : C(Smale.MorseHandle.UnitDisk c.PositiveCoordinates, { x : M // f x ≤ f p + ρ ^ 2 }) :=
    { toFun := fun v =>
        ⟨c.attachingHandleMap ρ hρ hblock (z₀, v), c.attachingHandleMap_upper ρ hρ hblock (z₀, v)⟩
      continuous_toFun :=
        ((c.attachingHandleMap ρ hρ hblock).continuous.comp
              (continuous_const.prodMk continuous_id)).subtype_mk
          _ }
  have hinj : Function.Injective h := by
    intro v w hvw
    have heq := c.attachingHandleMap_injective ρ hρ hblock (congrArg Subtype.val hvw)
    exact congrArg Prod.snd heq
  have hsurj : Function.Surjective h := by
    intro y
    have hyS : y.1 ∈ c.splitChart.source :=
      hsublevel
        (show f y.1 ≤ f p + ε from by
          have hy := y.2
          linarith)
    have heq := c.splitChart_equation hyS
    have hnegative : (c.splitChart y.1).1 = 0 := Subsingleton.elim _ _
    rw [hnegative, norm_zero] at heq
    have hypos : ‖(c.splitChart y.1).2‖ ≤ ρ := by
      have hy := y.2
      nlinarith [norm_nonneg (c.splitChart y.1).2]
    have hylower : f p - ρ ^ 2 ≤ f y.1 := by
      have hy := hglobal y.1
      linarith [sq_nonneg ρ]
    obtain ⟨⟨u, v⟩, huv⟩ :=
      (c.mem_range_attachingHandleMap_iff_inequalities ρ hρ hblock hyS).mpr ⟨hypos, hylower⟩
    have hu : u = z₀ := Subsingleton.elim _ _
    subst u
    exact ⟨v, Subtype.ext huv⟩
  refine ⟨ρ, hρ, by linarith, ?_⟩
  refine
    ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective h ⟨hinj, hsurj⟩) h.continuous, ?_⟩
  intro v
  change f (c.attachingHandleMap ρ hρ hblock (z₀, v)) = _
  rw [c.attachingHandleMap_quadratic]
  change
    f p +
        (-‖(ρ * Real.sqrt (1 + ‖(v : c.PositiveCoordinates)‖ ^ 2)) •
                  (0 : c.NegativeCoordinates)‖ ^
              2 +
          ‖ρ • (v : c.PositiveCoordinates)‖ ^ 2) =
      _
  simp only [smul_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), neg_zero, zero_add,
    norm_smul, Real.norm_eq_abs, abs_of_pos hρ, mul_pow]

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.finrank_positive_of_localMin {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hmin : IsLocalMin f p) :
    Module.finrank ℝ c.PositiveCoordinates = Module.finrank ℝ E := by
  let : Unique c.NegativeCoordinates :=
    { default := 0, uniq := c.negative_eq_zero_of_localMin hmin }
  let e : (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] c.PositiveCoordinates :=
    (Smale.MorseHandle.splitLinearEquiv c.weights).trans
      (LinearEquiv.uniqueProd (R := ℝ) (M := c.PositiveCoordinates) (M₂ := c.NegativeCoordinates))
  simpa using e.finrank_eq.symm

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.SignedMorseChart.minimumPositiveIsometry {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hmin : IsLocalMin f p) :
    c.PositiveCoordinates ≃ₗᵢ[ℝ] Smale.Hemisphere.Ambient (Module.finrank ℝ E) :=
  (stdOrthonormalBasis ℝ c.PositiveCoordinates).repr.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (c.finrank_positive_of_localMin hmin)))

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.SignedMorseChart.minimumDiskHomeomorph {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hmin : IsLocalMin f p) :
    Smale.MorseHandle.UnitDisk c.PositiveCoordinates ≃ₜ
      Smale.Hemisphere.Ball (Module.finrank ℝ E) :=
  (c.minimumPositiveIsometry hmin).toHomeomorph.subtype (p := fun x => x ∈ Metric.closedBall 0 1)
    (q := fun x => x ∈ Metric.closedBall 0 1)
    (fun x => by
      simp only [mem_closedBall_zero_iff, LinearIsometryEquiv.coe_toHomeomorph,
        LinearIsometryEquiv.norm_map])

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.norm_minimumDiskHomeomorph_symm {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (hmin : IsLocalMin f p)
    (v : Smale.Hemisphere.Ball (Module.finrank ℝ E)) :
    ‖((c.minimumDiskHomeomorph hmin).symm v : c.PositiveCoordinates)‖ =
      ‖(v : Smale.Hemisphere.Ambient (Module.finrank ℝ E))‖ := by
  change
    ‖(c.minimumPositiveIsometry hmin).symm (v : Smale.Hemisphere.Ambient (Module.finrank ℝ E))‖ =
      _
  exact (c.minimumPositiveIsometry hmin).symm.norm_map _

private def Smale.Hemisphere.tail {n : ℕ} (y : Sphere n) : Ambient n :=
  WithLp.toLp 2 (fun i => (y : Ambient (n + 1)) i.succ)

private theorem Smale.Hemisphere.head_sq_add_tail_norm_sq {n : ℕ} (y : Sphere n) :
    (y : Ambient (n + 1)) 0 ^ 2 + ‖tail y‖ ^ 2 = 1 := by
  have hy : ‖(y : Ambient (n + 1))‖ ^ 2 = 1 := by
    rw [mem_sphere_zero_iff_norm.mp y.property]
    exact one_pow 2
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ] at hy
  rw [EuclideanSpace.real_norm_sq_eq]
  exact hy

private theorem Smale.Hemisphere.tail_mem_ball {n : ℕ} (y : Sphere n) :
    tail y ∈ Metric.closedBall (0 : Ambient n) 1 := by
  rw [mem_closedBall_zero_iff]
  have hy := head_sq_add_tail_norm_sq y
  nlinarith [sq_nonneg ((y : Ambient (n + 1)) 0), norm_nonneg (tail y)]

private def Smale.Hemisphere.disk {n : ℕ} (y : Sphere n) : Ball n :=
  ⟨tail y, tail_mem_ball y⟩

private theorem Smale.Hemisphere.radius_disk {n : ℕ} (y : Sphere n) :
    radius (disk y) = |(y : Ambient (n + 1)) 0| := by
  have hy := head_sq_add_tail_norm_sq y
  have hs : 1 - ‖tail y‖ ^ 2 = (y : Ambient (n + 1)) 0 ^ 2 := by linarith
  change Real.sqrt (1 - ‖tail y‖ ^ 2) = _
  rw [hs, Real.sqrt_sq_eq_abs]

private theorem Smale.Hemisphere.point_disk_of_nonneg {n : ℕ} (y : Sphere n)
    (hy : 0 ≤ (y : Ambient (n + 1)) 0) : point Bool.true (disk y) = y := by
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [radius_disk, abs_of_nonneg hy]
  · rfl

private theorem Smale.Hemisphere.point_disk_of_nonpos {n : ℕ} (y : Sphere n)
    (hy : (y : Ambient (n + 1)) 0 ≤ 0) : point Bool.false (disk y) = y := by
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [radius_disk, abs_of_nonpos hy]
  · rfl

private theorem
    Smale.Hemisphere.point_jointly_surjective {n : ℕ} (y : Sphere n) : ∃ b x, point b x = y :=
  by
  rcases le_total 0 ((y : Ambient (n + 1)) 0) with hy | hy
  · exact ⟨Bool.true, disk y, point_disk_of_nonneg y hy⟩
  · exact ⟨Bool.false, disk y, point_disk_of_nonpos y hy⟩

private def Smale.DiskDouble.hemisphereMap (n : ℕ) :
    Smale.Hemisphere.Ball n ⊕ Smale.Hemisphere.Ball n → Smale.Hemisphere.Sphere n :=
  Sum.elim (Smale.Hemisphere.point Bool.false) (Smale.Hemisphere.point Bool.true)

private theorem Smale.DiskDouble.continuous_hemisphereMap (n : ℕ) : Continuous (hemisphereMap n) :=
  continuous_sum_dom.mpr
    ⟨Smale.Hemisphere.continuous_point Bool.false, Smale.Hemisphere.continuous_point Bool.true⟩

private theorem Smale.DiskDouble.hemisphereMap_respects (n : ℕ)
    (x y : Smale.Hemisphere.Ball n ⊕ Smale.Hemisphere.Ball n)
    (h : Smale.DiskDouble.Rel (Homeomorph.refl (Boundary (Smale.Hemisphere.Ambient n))) x y) :
    hemisphereMap n x = hemisphereMap n y := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact h.elim
    | inr y =>
      obtain ⟨z, rfl, rfl⟩ := h
      exact Smale.Hemisphere.point_boundary z
  | inr x => cases y <;> exact h.elim

private def Smale.DiskDouble.sphereMap (n : ℕ) :
    Space (Homeomorph.refl (Boundary (Smale.Hemisphere.Ambient n))) → Smale.Hemisphere.Sphere n :=
  Quot.lift (hemisphereMap n) (hemisphereMap_respects n)

private theorem Smale.DiskDouble.continuous_sphereMap (n : ℕ) : Continuous (sphereMap n) :=
  continuous_quot_lift (hemisphereMap_respects n) (continuous_hemisphereMap n)

private theorem
    Smale.DiskDouble.sphereMap_injective (n : ℕ) : Function.Injective (sphereMap n) := by
  intro a b
  induction a using Quot.inductionOn with
  | _ x =>
    induction b using Quot.inductionOn with
    | _ y =>
      intro h
      cases x with
      | inl x =>
        cases y with
        | inl y =>
          have hxy := Smale.Hemisphere.point_injective Bool.false h
          subst y
          rfl
        | inr y => exact Quot.sound ((Smale.Hemisphere.point_false_eq_true_iff x y).mp h)
      | inr x =>
        cases y with
        | inl y =>
          exact (Quot.sound ((Smale.Hemisphere.point_false_eq_true_iff y x).mp h.symm)).symm
        | inr y =>
          have hxy := Smale.Hemisphere.point_injective Bool.true h
          subst y
          rfl

private theorem
    Smale.DiskDouble.sphereMap_surjective (n : ℕ) : Function.Surjective (sphereMap n) := by
  intro y
  obtain ⟨b, x, hx⟩ := Smale.Hemisphere.point_jointly_surjective y
  cases b
  · exact ⟨Quot.mk _ (.inl x), hx⟩
  · exact ⟨Quot.mk _ (.inr x), hx⟩

private def Smale.DiskDouble.homeomorphSphere (n : ℕ) :
    Space (Homeomorph.refl (Boundary (Smale.Hemisphere.Ambient n))) ≃ₜ
      Smale.Hemisphere.Sphere n :=
  Continuous.homeoOfEquivCompactToT2 (f :=
    Equiv.ofBijective (sphereMap n) ⟨sphereMap_injective n, sphereMap_surjective n⟩)
    (continuous_sphereMap n)

private def Smale.DiskDouble.twistedHomeomorphSphere (n : ℕ)
    (e : Boundary (Smale.Hemisphere.Ambient n) ≃ₜ Boundary (Smale.Hemisphere.Ambient n)) :
    Space e ≃ₜ Smale.Hemisphere.Sphere n :=
  (homeomorphUntwisted e).trans (homeomorphSphere n)

private structure Smale.TwoDiskDecomposition (n : ℕ) (M : Type*) [TopologicalSpace M] where
  boundaryEquiv :
    DiskDouble.Boundary (Hemisphere.Ambient n) ≃ₜ DiskDouble.Boundary (Hemisphere.Ambient n)
  left : C(Hemisphere.Ball n, M)
  right : C(Hemisphere.Ball n, M)
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  covers : ∀ p : M, (∃ x, left x = p) ∨ ∃ y, right y = p
  overlap :
    ∀ x y,
      left x = right y ↔
        ∃ z : DiskDouble.Boundary (Hemisphere.Ambient n),
          x = DiskDouble.boundary (Hemisphere.Ambient n) z ∧
            y = DiskDouble.boundary (Hemisphere.Ambient n) (boundaryEquiv z)

private def Smale.TwoDiskDecomposition.sumMap {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : Smale.TwoDiskDecomposition n M) :
    Smale.Hemisphere.Ball n ⊕ Smale.Hemisphere.Ball n → M :=
  Sum.elim d.left d.right

private theorem
    Smale.TwoDiskDecomposition.continuous_sumMap {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : Smale.TwoDiskDecomposition n M) : Continuous d.sumMap :=
  continuous_sum_dom.mpr ⟨d.left.continuous, d.right.continuous⟩

private theorem Smale.TwoDiskDecomposition.sumMap_respects {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : Smale.TwoDiskDecomposition n M) (x y : Smale.Hemisphere.Ball n ⊕ Smale.Hemisphere.Ball n)
    (h : Smale.DiskDouble.Rel d.boundaryEquiv x y) : d.sumMap x = d.sumMap y := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact h.elim
    | inr y => exact (d.overlap x y).mpr h
  | inr x => cases y <;> exact h.elim

private def Smale.TwoDiskDecomposition.quotientMap {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : Smale.TwoDiskDecomposition n M) : Smale.DiskDouble.Space d.boundaryEquiv → M :=
  Quot.lift d.sumMap d.sumMap_respects

private theorem
    Smale.TwoDiskDecomposition.continuous_quotientMap {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : Smale.TwoDiskDecomposition n M) : Continuous d.quotientMap :=
  continuous_quot_lift d.sumMap_respects d.continuous_sumMap

private theorem
    Smale.TwoDiskDecomposition.quotientMap_injective {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : Smale.TwoDiskDecomposition n M) : Function.Injective d.quotientMap := by
  intro a b
  induction a using Quot.inductionOn with
  | _ x =>
    induction b using Quot.inductionOn with
    | _ y =>
      intro h
      cases x with
      | inl x =>
        cases y with
        | inl y =>
          have hxy := d.left_injective h
          subst y
          rfl
        | inr y => exact Quot.sound ((d.overlap x y).mp h)
      | inr x =>
        cases y with
        | inl y => exact (Quot.sound ((d.overlap y x).mp h.symm)).symm
        | inr y =>
          have hxy := d.right_injective h
          subst y
          rfl

private theorem
    Smale.TwoDiskDecomposition.quotientMap_surjective {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : Smale.TwoDiskDecomposition n M) : Function.Surjective d.quotientMap := by
  intro p
  rcases d.covers p with ⟨x, hx⟩ | ⟨y, hy⟩
  · exact ⟨Quot.mk _ (.inl x), hx⟩
  · exact ⟨Quot.mk _ (.inr y), hy⟩

private def Smale.TwoDiskDecomposition.quotientHomeomorph {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : Smale.TwoDiskDecomposition n M) [T2Space M] :
    Smale.DiskDouble.Space d.boundaryEquiv ≃ₜ M :=
  Continuous.homeoOfEquivCompactToT2 (f :=
    Equiv.ofBijective d.quotientMap ⟨d.quotientMap_injective, d.quotientMap_surjective⟩)
    d.continuous_quotientMap

private def Smale.TwoDiskDecomposition.homeomorphSphere {n : ℕ} {M : Type*} [TopologicalSpace M]
    (d : Smale.TwoDiskDecomposition n M) [T2Space M] : M ≃ₜ Smale.Hemisphere.Sphere n :=
  d.quotientHomeomorph.symm.trans (Smale.DiskDouble.twistedHomeomorphSphere n d.boundaryEquiv)

private structure
    Smale.SublevelDisk (n : ℕ) {M : Type*} [TopologicalSpace M] (f : M → ℝ) (a : ℝ) where
  homeomorph : Hemisphere.Ball n ≃ₜ { x : M // f x ≤ a }
  boundary_iff : ∀ v, f (homeomorph v).1 = a ↔ ‖(v : Hemisphere.Ambient n)‖ = 1

private def Smale.SublevelDisk.map {n : ℕ} {M : Type*} [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : Smale.SublevelDisk n f a) : C(Smale.Hemisphere.Ball n, M)
    where
  toFun v := (d.homeomorph v).1
  continuous_toFun := continuous_subtype_val.comp d.homeomorph.continuous

private theorem
    Smale.SublevelDisk.map_injective {n : ℕ} {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    {a : ℝ} (d : Smale.SublevelDisk n f a) : Function.Injective d.map := by
  intro v w h
  exact d.homeomorph.injective (Subtype.ext h)

private def
    Smale.SublevelDisk.boundaryMap {n : ℕ} {M : Type*} [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (d : Smale.SublevelDisk n f a) :
    C(Smale.DiskDouble.Boundary (Smale.Hemisphere.Ambient n), { x : M // f x = a })
    where
  toFun
    z :=
    ⟨d.map (Smale.DiskDouble.boundary _ z),
      (d.boundary_iff _).mpr
        (by simpa only [Smale.DiskDouble.boundary, mem_sphere_zero_iff_norm] using z.2)⟩
  continuous_toFun :=
    (d.map.continuous.comp
          (continuous_subtype_val.subtype_mk
            (fun z => Metric.sphere_subset_closedBall z.2))).subtype_mk
      _

private theorem Smale.SublevelDisk.boundaryMap_injective {n : ℕ} {M : Type*} [TopologicalSpace M]
    {f : M → ℝ} {a : ℝ} (d : Smale.SublevelDisk n f a) : Function.Injective d.boundaryMap := by
  intro z w h
  have heq : d.map (Smale.DiskDouble.boundary _ z) = d.map (Smale.DiskDouble.boundary _ w) :=
    congrArg (fun y : { x : M // f x = a } => y.1) h
  have h' := d.map_injective heq
  apply Subtype.ext
  exact congrArg (fun v : Smale.Hemisphere.Ball n => (v : Smale.Hemisphere.Ambient n)) h'

private theorem Smale.SublevelDisk.boundaryMap_surjective {n : ℕ} {M : Type*} [TopologicalSpace M]
    {f : M → ℝ} {a : ℝ} (d : Smale.SublevelDisk n f a) : Function.Surjective d.boundaryMap := by
  intro y
  let v := d.homeomorph.symm ⟨y.1, y.2.le⟩
  have hv : (d.homeomorph v).1 = y.1 :=
    congrArg Subtype.val (d.homeomorph.apply_symm_apply ⟨y.1, y.2.le⟩)
  have hnorm : ‖(v : Smale.Hemisphere.Ambient n)‖ = 1 :=
    (d.boundary_iff v).mp (by rw [hv]; exact y.2)
  let z : Smale.DiskDouble.Boundary (Smale.Hemisphere.Ambient n) :=
    ⟨v.1, mem_sphere_zero_iff_norm.mpr hnorm⟩
  refine ⟨z, Subtype.ext ?_⟩
  exact hv

private def
    Smale.SublevelDisk.boundaryHomeomorph {n : ℕ} {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    {a : ℝ} (d : Smale.SublevelDisk n f a) [T2Space M] :
    Smale.DiskDouble.Boundary (Smale.Hemisphere.Ambient n) ≃ₜ { x : M // f x = a } :=
  Continuous.homeoOfEquivCompactToT2 (f :=
    Equiv.ofBijective d.boundaryMap ⟨d.boundaryMap_injective, d.boundaryMap_surjective⟩)
    d.boundaryMap.continuous

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SignedMorseChart.exists_minimumSublevelDisk {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    [CompactSpace M] {f : M → ℝ} {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : Continuous f) (hunique : ∀ x, f x ≤ f p → x = p) {b : ℝ} (hb : f p < b) :
    ∃ a ∈ Set.Ioo (f p) b, Nonempty (Smale.SublevelDisk (Module.finrank ℝ E) f a) := by
  have hglobal : ∀ x, f p ≤ f x := by
    intro x
    by_contra! h
    have hxp := hunique x h.le
    rw [hxp] at h
    exact lt_irrefl _ h
  have hmin : IsLocalMin f p := Filter.Eventually.of_forall hglobal
  obtain ⟨ρ, hρ, hab, e, he⟩ := exists_minimum_disk_sublevel_with_height c hf hunique hb
  let d := (c.minimumDiskHomeomorph hmin).symm.trans e
  have hd (v : Smale.Hemisphere.Ball (Module.finrank ℝ E)) :
    f (d v).1 = f p + ρ ^ 2 * ‖(v : Smale.Hemisphere.Ambient (Module.finrank ℝ E))‖ ^ 2 := by
    change f (e ((c.minimumDiskHomeomorph hmin).symm v)).1 = _
    rw [he, c.norm_minimumDiskHomeomorph_symm]
  refine ⟨f p + ρ ^ 2, ⟨by linarith [sq_pos_of_pos hρ], hab⟩, ⟨⟨d, ?_⟩⟩⟩
  intro v
  rw [hd]
  constructor
  · intro h
    have hs : ‖(v : Smale.Hemisphere.Ambient (Module.finrank ℝ E))‖ ^ 2 = 1 :=
      mul_left_cancel₀ (pow_ne_zero 2 hρ.ne') (by linarith)
    nlinarith [norm_nonneg (v : Smale.Hemisphere.Ambient (Module.finrank ℝ E))]
  · intro h
    rw [h, one_pow, mul_one]

private def Smale.FlowConstruction.stretchHeight (c k r : ℝ) : ℝ :=
  r + (k - 1) * Max.max 0 (r - c)

private theorem Smale.FlowConstruction.stretchHeight_of_le {c k r : ℝ} (hr : r ≤ c) :
    stretchHeight c k r = r := by
  simp only [stretchHeight, max_eq_left (sub_nonpos.mpr hr), MulZeroClass.mul_zero, add_zero]

private theorem Smale.FlowConstruction.stretchHeight_of_ge {c k r : ℝ} (hr : c ≤ r) :
    stretchHeight c k r = c + k * (r - c) := by
  rw [stretchHeight, max_eq_right (sub_nonneg.mpr hr)]
  ring

private theorem Smale.FlowConstruction.stretchHeight_inverse {c k : ℝ} (hk : 0 < k) (r : ℝ) :
    stretchHeight c k⁻¹ (stretchHeight c k r) = r := by
  by_cases hr : r ≤ c
  · rw [stretchHeight_of_le hr, stretchHeight_of_le hr]
  · have hcr : c < r := lt_of_not_ge hr
    have hs : c ≤ stretchHeight c k r := by
      rw [stretchHeight_of_ge hcr.le]
      exact le_add_of_nonneg_right (mul_nonneg hk.le (sub_nonneg.mpr hcr.le))
    rw [stretchHeight_of_ge hs, stretchHeight_of_ge hcr.le]
    field_simp
    ring

private theorem Smale.FlowConstruction.continuous_stretchHeight (c k : ℝ) :
    Continuous (stretchHeight c k) :=
  continuous_id.add
    (continuous_const.mul (continuous_const.max (continuous_id.sub continuous_const)))

private def Smale.FlowConstruction.stretchHeightHomeomorph (c k : ℝ) (hk : 0 < k) : ℝ ≃ₜ ℝ
    where
  toFun := stretchHeight c k
  invFun := stretchHeight c k⁻¹
  left_inv := stretchHeight_inverse hk
  right_inv r := by simpa only [inv_inv] using stretchHeight_inverse (c := c) (inv_pos.mpr hk) r
  continuous_toFun := continuous_stretchHeight c k
  continuous_invFun := continuous_stretchHeight c k⁻¹

private theorem Smale.FlowConstruction.stretchHeight_endpoint {c a b : ℝ} (hca : c < a) :
    stretchHeight c ((b - c) / (a - c)) a = b := by
  rw [stretchHeight_of_ge hca.le, div_mul_cancel₀ _ (sub_ne_zero.mpr hca.ne')]
  ring

private theorem Smale.FlowConstruction.stretchHeight_endpoint_iff {c a b r : ℝ} (hca : c < a)
    (hcb : c < b) : stretchHeight c ((b - c) / (a - c)) r = b ↔ r = a := by
  have hk : 0 < (b - c) / (a - c) := div_pos (sub_pos.mpr hcb) (sub_pos.mpr hca)
  constructor
  · intro h
    exact
      (stretchHeightHomeomorph c ((b - c) / (a - c)) hk).injective
        (h.trans (stretchHeight_endpoint hca).symm)
  · rintro rfl
    exact stretchHeight_endpoint hca

private theorem
    Smale.FlowConstruction.stretchHeight_le_target {c a b r : ℝ} (hca : c < a) (hcb : c < b)
    (hr : r ≤ a) : stretchHeight c ((b - c) / (a - c)) r ≤ b := by
  by_cases hrc : r ≤ c
  · rw [stretchHeight_of_le hrc]
    exact hrc.trans hcb.le
  · have hcr : c ≤ r := le_of_not_ge hrc
    have hk : 0 ≤ (b - c) / (a - c) := (div_pos (sub_pos.mpr hcb) (sub_pos.mpr hca)).le
    rw [stretchHeight_of_ge hcr]
    calc
      _ ≤ c + ((b - c) / (a - c)) * (a - c) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (sub_le_sub_right hr c) hk)
      _ = b := by rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hca.ne')]; ring

private def
    Smale.FlowConstruction.stretchFlow {X : Type*} [TopologicalSpace X] (F : Flow ℝ X) (f : X → ℝ)
    (c k : ℝ) (x : X) : X :=
  F (stretchHeight c k (f x) - f x) x

private theorem Smale.FlowConstruction.continuous_stretchFlow {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) (f : X → ℝ) (hf : Continuous f) (c k : ℝ) : Continuous (stretchFlow F f c k) :=
  F.continuous (((continuous_stretchHeight c k).comp hf).sub hf) continuous_id

private theorem
    Smale.FlowConstruction.stretchFlow_height {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {f : X → ℝ} {c d a b : ℝ}
    (hF : ∀ x t, f x ∈ Set.Icc c d → f x + t ∈ Set.Icc c d → f (F t x) = f x + t) (hca : c < a)
    (hcb : c < b) (ha : a ≤ d) (hb : b ≤ d) {x : X} (hx : f x ≤ a) :
    f (stretchFlow F f c ((b - c) / (a - c)) x) = stretchHeight c ((b - c) / (a - c)) (f x) := by
  by_cases hxc : f x ≤ c
  · simp only [stretchFlow, stretchHeight_of_le hxc, sub_self, F.map_zero_apply]
  · have hcx : c ≤ f x := le_of_not_ge hxc
    have hk : 0 < (b - c) / (a - c) := div_pos (sub_pos.mpr hcb) (sub_pos.mpr hca)
    have hslo : c ≤ stretchHeight c ((b - c) / (a - c)) (f x) := by
      rw [stretchHeight_of_ge hcx]
      exact le_add_of_nonneg_right (mul_nonneg hk.le (sub_nonneg.mpr hcx))
    have hshi := stretchHeight_le_target hca hcb hx
    have hsum :
      f x + (stretchHeight c ((b - c) / (a - c)) (f x) - f x) =
        stretchHeight c ((b - c) / (a - c)) (f x) := by ring
    have hh :=
      hF x (stretchHeight c ((b - c) / (a - c)) (f x) - f x) ⟨hcx, hx.trans ha⟩
        (by rw [hsum]; exact ⟨hslo, hshi.trans hb⟩)
    exact hh.trans hsum

private theorem Smale.FlowConstruction.stretchFlow_le_target {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} {c d a b : ℝ}
    (hF : ∀ x t, f x ∈ Set.Icc c d → f x + t ∈ Set.Icc c d → f (F t x) = f x + t) (hca : c < a)
    (hcb : c < b) (ha : a ≤ d) (hb : b ≤ d) {x : X} (hx : f x ≤ a) :
    f (stretchFlow F f c ((b - c) / (a - c)) x) ≤ b := by
  rw [stretchFlow_height F hF hca hcb ha hb hx]
  exact stretchHeight_le_target hca hcb hx

private theorem
    Smale.FlowConstruction.stretchFlow_inverse {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {f : X → ℝ} {c d a b : ℝ}
    (hF : ∀ x t, f x ∈ Set.Icc c d → f x + t ∈ Set.Icc c d → f (F t x) = f x + t) (hca : c < a)
    (hcb : c < b) (ha : a ≤ d) (hb : b ≤ d) {x : X} (hx : f x ≤ a) :
    stretchFlow F f c ((a - c) / (b - c)) (stretchFlow F f c ((b - c) / (a - c)) x) = x := by
  have hh := stretchFlow_height F hF hca hcb ha hb hx
  have hk : 0 < (b - c) / (a - c) := div_pos (sub_pos.mpr hcb) (sub_pos.mpr hca)
  have hi : (a - c) / (b - c) = ((b - c) / (a - c))⁻¹ := (inv_div _ _).symm
  change
    F
        (stretchHeight c ((a - c) / (b - c)) (f (stretchFlow F f c ((b - c) / (a - c)) x)) -
          f (stretchFlow F f c ((b - c) / (a - c)) x))
        (F (stretchHeight c ((b - c) / (a - c)) (f x) - f x) x) =
      x
  rw [hh, hi, stretchHeight_inverse hk, ← F.map_add]
  rw [show
      f x - stretchHeight c ((b - c) / (a - c)) (f x) +
          (stretchHeight c ((b - c) / (a - c)) (f x) - f x) =
        0
      by ring,
    F.map_zero_apply]

private def Smale.FlowConstruction.regularSublevelHomeomorphOfFlow {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} {c d a b : ℝ}
    (hF : ∀ x t, f x ∈ Set.Icc c d → f x + t ∈ Set.Icc c d → f (F t x) = f x + t)
    (hf : Continuous f) (hca : c < a) (hcb : c < b) (ha : a ≤ d) (hb : b ≤ d) :
    { x : X // f x ≤ a } ≃ₜ { x : X // f x ≤ b }
    where
  toFun
    x := ⟨stretchFlow F f c ((b - c) / (a - c)) x.1, stretchFlow_le_target F hF hca hcb ha hb x.2⟩
  invFun
    x := ⟨stretchFlow F f c ((a - c) / (b - c)) x.1, stretchFlow_le_target F hF hcb hca hb ha x.2⟩
  left_inv x := Subtype.ext (stretchFlow_inverse F hF hca hcb ha hb x.2)
  right_inv x := Subtype.ext (stretchFlow_inverse F hF hcb hca hb ha x.2)
  continuous_toFun :=
    ((continuous_stretchFlow F f hf c _).comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((continuous_stretchFlow F f hf c _).comp continuous_subtype_val).subtype_mk _

private theorem Smale.FlowConstruction.regularSublevelHomeomorphOfFlow_level_iff {X : Type*}
    [TopologicalSpace X] (F : Flow ℝ X) {f : X → ℝ} {c d a b : ℝ}
    (hF : ∀ x t, f x ∈ Set.Icc c d → f x + t ∈ Set.Icc c d → f (F t x) = f x + t)
    (hf : Continuous f) (hca : c < a) (hcb : c < b) (ha : a ≤ d) (hb : b ≤ d)
    (x : { x : X // f x ≤ a }) :
    f ((regularSublevelHomeomorphOfFlow F hF hf hca hcb ha hb) x).1 = b ↔ f x.1 = a := by
  change f (stretchFlow F f c ((b - c) / (a - c)) x.1) = b ↔ _
  rw [stretchFlow_height F hF hca hcb ha hb x.2]
  exact stretchHeight_endpoint_iff hca hcb

private theorem Smale.FlowConstruction.exists_regularSublevelHomeomorph_with_level {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {c a b : ℝ} (hca : c < a) (hcb : c < b)
    (hband : ∀ x, f x ∈ Set.Icc c (Max.max a b) → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    ∃ e : { x : M // f x ≤ a } ≃ₜ { x : M // f x ≤ b }, ∀ x, f (e x).1 = b ↔ f x.1 = a := by
  obtain ⟨F, hF⟩ := exists_heightTranslatingFlow hf hband
  refine
    ⟨regularSublevelHomeomorphOfFlow F hF hf.continuous hca hcb (le_max_left a b)
        (le_max_right a b),
      ?_⟩
  exact
    regularSublevelHomeomorphOfFlow_level_iff F hF hf.continuous hca hcb (le_max_left a b)
      (le_max_right a b)

private def
    Smale.SublevelDisk.transport {M : Type*} [TopologicalSpace M] {n : ℕ} {f : M → ℝ} {a b : ℝ}
    (d : Smale.SublevelDisk n f a) (e : { x : M // f x ≤ a } ≃ₜ { x : M // f x ≤ b })
    (he : ∀ x, f (e x).1 = b ↔ f x.1 = a) : Smale.SublevelDisk n f b
    where
  homeomorph := d.homeomorph.trans e
  boundary_iff v := (he (d.homeomorph v)).trans (d.boundary_iff v)

private theorem
    Smale.FlowConstruction.nonempty_regularSublevelDisk {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {n : ℕ} {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {c a b : ℝ} (hca : c < a) (hcb : c < b)
    (hband : ∀ x, f x ∈ Set.Icc c (Max.max a b) → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (d : Smale.SublevelDisk n f a) : Nonempty (Smale.SublevelDisk n f b) := by
  obtain ⟨e, he⟩ := exists_regularSublevelHomeomorph_with_level hf hca hcb hband
  exact ⟨d.transport e he⟩

private theorem Smale.ManifoldMorse.SignedMorseChart.nonempty_sublevelDisk_before_next_critical
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {f : M → ℝ} {p : M} (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hunique : ∀ x, f x ≤ f p → x = p) {b : ℝ} (hb : f p < b)
    (hregular : ∀ x, f p < f x → f x ≤ b → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    Nonempty (Smale.SublevelDisk (Module.finrank ℝ E) f b) := by
  obtain ⟨a, ha, ⟨d⟩⟩ := c.exists_minimumSublevelDisk hf.continuous hunique hb
  obtain ⟨l, hpl, hla⟩ := exists_between ha.1
  apply Smale.FlowConstruction.nonempty_regularSublevelDisk hf hla (hla.trans ha.2) _ d
  intro x hx
  apply hregular x (hpl.trans_le hx.1)
  exact hx.2.trans (max_le ha.2.le le_rfl)

private theorem Smale.ManifoldMorse.criticalPoints_neg {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) :
    criticalPoints E (fun x => -f x) = criticalPoints E f := by
  ext x
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (-f) x = 0 ↔ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0
  rw [mfderiv_neg]
  exact neg_eq_zero

private def Smale.ManifoldMorse.SignedMorseChart.neg {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) :
    Smale.ManifoldMorse.SignedMorseChart (E := E) (fun x => -f x) p
    where
  weights i := -c.weights i
  signs
    i := by
    rcases c.signs i with h | h
    · exact Or.inr (by rw [h]; ring)
    · exact Or.inl (by rw [h])
  chart := c.chart
  mem_source := c.mem_source
  center := c.center
  equation y
    hy := by
    rw [c.equation y hy]
    simp only [neg_mul, Finset.sum_neg_distrib, neg_add]
  inverse_equation y
    hy := by
    rw [c.inverse_equation y hy]
    simp only [neg_mul, Finset.sum_neg_distrib, neg_add]

private def Smale.ManifoldMorse.SurgeryWindows.first {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (h : 0 < S.count) :
    Smale.ManifoldMorse.criticalPoints E f :=
  S.point ⟨0, h⟩

private def
    Smale.ManifoldMorse.SurgeryWindows.last {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (h : 0 < S.count) :
    Smale.ManifoldMorse.criticalPoints E f :=
  S.point ⟨S.count - 1, Nat.sub_lt h zero_lt_one⟩

private theorem
    Smale.ManifoldMorse.SurgeryWindows.value_first_le {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (h : 0 < S.count)
    (p : Smale.ManifoldMorse.criticalPoints E f) : f (S.first h) ≤ f p := by
  have hle : (⟨0, h⟩ : Fin S.count) ≤ S.point.symm p := Nat.zero_le _
  simpa only [first, Equiv.apply_symm_apply] using S.point_strictMono.monotone hle

private theorem
    Smale.ManifoldMorse.SurgeryWindows.value_le_last {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (h : 0 < S.count)
    (p : Smale.ManifoldMorse.criticalPoints E f) : f p ≤ f (S.last h) := by
  have hle : S.point.symm p ≤ (⟨S.count - 1, Nat.sub_lt h zero_lt_one⟩ : Fin S.count) :=
    Nat.le_sub_one_of_lt (S.point.symm p).isLt
  simpa only [last, Equiv.apply_symm_apply] using S.point_strictMono.monotone hle

private theorem Smale.ManifoldMorse.SurgeryWindows.count_pos {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) [Nonempty M] : 0 < S.count := by
  obtain ⟨p, -, hmin⟩ :=
    isCompact_univ.exists_isMinOn Set.univ_nonempty hf.continuous.continuousOn
  have hp : p ∈ Smale.ManifoldMorse.criticalPoints E f :=
    Smale.ManifoldMorse.mem_criticalPoints_of_localMin hf
      (Filter.Eventually.of_forall (fun x => hmin (Set.mem_univ x)))
  exact lt_of_le_of_lt (Nat.zero_le _) (S.point.symm ⟨p, hp⟩).isLt

private theorem
    Smale.ManifoldMorse.SurgeryWindows.first_globalMin {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (h : 0 < S.count) (x : M) : f (S.first h) ≤ f x := by
  obtain ⟨p, -, hmin⟩ :=
    isCompact_univ.exists_isMinOn ⟨x, Set.mem_univ x⟩ hf.continuous.continuousOn
  have hp : p ∈ Smale.ManifoldMorse.criticalPoints E f :=
    Smale.ManifoldMorse.mem_criticalPoints_of_localMin hf
      (Filter.Eventually.of_forall (fun y => hmin (Set.mem_univ y)))
  exact (S.value_first_le h ⟨p, hp⟩).trans (hmin (Set.mem_univ x))

private theorem
    Smale.ManifoldMorse.SurgeryWindows.last_globalMax {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (h : 0 < S.count) (x : M) : f x ≤ f (S.last h) := by
  obtain ⟨p, -, hmax⟩ :=
    isCompact_univ.exists_isMaxOn ⟨x, Set.mem_univ x⟩ hf.continuous.continuousOn
  have hp : p ∈ Smale.ManifoldMorse.criticalPoints E f :=
    Smale.ManifoldMorse.mem_criticalPoints_of_localMax hf
      (Filter.Eventually.of_forall (fun y => hmax (Set.mem_univ y)))
  exact (hmax (Set.mem_univ x)).trans (S.value_le_last h ⟨p, hp⟩)

private theorem Smale.ManifoldMorse.SurgeryWindows.unique_first {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (h : 0 < S.count) (x : M) (hx : f x ≤ f (S.first h)) :
    x = (S.first h).val := by
  have hxcrit : x ∈ Smale.ManifoldMorse.criticalPoints E f :=
    Smale.ManifoldMorse.mem_criticalPoints_of_localMin hf
      (Filter.Eventually.of_forall (fun y => hx.trans (S.first_globalMin hf h y)))
  exact S.distinct hxcrit (S.first h).property (le_antisymm hx (S.first_globalMin hf h x))

private theorem
    Smale.ManifoldMorse.SurgeryWindows.last_upper_univ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (h : 0 < S.count) :
    {x : M | f x ≤ S.upper (S.last h)} = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact (S.last_globalMax hf h x).trans (S.value_lt_upper (S.last h)).le

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.SurgeryWindows.first_index_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (h : 0 < S.count) :
    Module.finrank ℝ (S.data (S.first h)).chart.NegativeCoordinates = 0 := by
  let :=
    (S.data (S.first h)).chart.subsingleton_negative_of_localMin
      (Filter.Eventually.of_forall (S.first_globalMin hf h))
  exact Module.finrank_zero_of_subsingleton

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SurgeryWindows.last_index_dimension {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (h : 0 < S.count) :
    Module.finrank ℝ (S.data (S.last h)).chart.NegativeCoordinates = Module.finrank ℝ E := by
  let :=
    (S.data (S.last h)).chart.subsingleton_positive_of_localMax
      (Filter.Eventually.of_forall (S.last_globalMax hf h))
  have hz : Module.finrank ℝ (S.data (S.last h)).chart.PositiveCoordinates = 0 :=
    Module.finrank_zero_of_subsingleton
  simpa only [hz, add_zero] using (S.data (S.last h)).chart.finrank_negative_add_positive

private theorem Smale.ManifoldMorse.SurgeryWindows.nonempty_firstSublevelDisk {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) [FiniteDimensional ℝ E] [T2Space M] (h : 0 < S.count) :
    Nonempty (Smale.SublevelDisk (Module.finrank ℝ E) f (S.upper (S.first h))) := by
  apply
    (S.data (S.first h)).chart.nonempty_sublevelDisk_before_next_critical hf (S.unique_first hf h)
      (S.value_lt_upper (S.first h))
  intro x hxlo hxhi hxcrit
  have hxlower : S.lower (S.first h) ≤ f x := (S.lower_lt_value (S.first h)).le.trans hxlo.le
  have hxp := S.isolated (S.first h) x hxcrit ⟨hxlower, hxhi⟩
  rw [hxp] at hxlo
  exact lt_irrefl _ hxlo

private def Smale.FlowConstruction.sublevelInclusion {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    {a b : ℝ} (hab : a ≤ b) : C({ x : M // f x ≤ a }, { x : M // f x ≤ b })
    where
  toFun x := ⟨x.1, x.2.trans hab⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

private theorem Smale.FlowConstruction.sublevel_deformation_height {M : Type*} [TopologicalSpace M]
    {f : M → ℝ} {a b : ℝ} (F : Flow ℝ M)
    (hF : ∀ x t, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b → f (F t x) = f x + t) {x : M}
    (hx : f x ≤ b) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    f (F (u * Min.min 0 (a - f x)) x) = f x + u * Min.min 0 (a - f x) := by
  by_cases hxa : f x ≤ a
  · rw [min_eq_left (sub_nonneg.mpr hxa), MulZeroClass.mul_zero, F.map_zero_apply, add_zero]
  · have hax : a ≤ f x := (lt_of_not_ge hxa).le
    rw [min_eq_right (sub_nonpos.mpr hax)]
    apply hF x _ ⟨hax, hx⟩
    have htime : u * (a - f x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu.1 (sub_nonpos.mpr hax)
    have hprod : 0 ≤ (1 - u) * (f x - a) := mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hax)
    exact ⟨by nlinarith, by linarith⟩

private theorem Smale.FlowConstruction.sublevel_deformation_mem {M : Type*} [TopologicalSpace M]
    {f : M → ℝ} {a b : ℝ} (F : Flow ℝ M)
    (hF : ∀ x t, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b → f (F t x) = f x + t) {x : M}
    (hx : f x ≤ b) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) : f (F (u * Min.min 0 (a - f x)) x) ≤ b :=
  by
  rw [sublevel_deformation_height F hF hx hu]
  exact (add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos hu.1 (min_le_left _ _))).trans hx

private theorem Smale.FlowConstruction.sublevel_retraction_mem {M : Type*} [TopologicalSpace M]
    {f : M → ℝ} {a b : ℝ} (F : Flow ℝ M)
    (hF : ∀ x t, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b → f (F t x) = f x + t) {x : M}
    (hx : f x ≤ b) : f (F (Min.min 0 (a - f x)) x) ≤ a := by
  have h :=
    sublevel_deformation_height F hF hx (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
  simp only [one_mul] at h
  rw [h]
  have hm := min_le_right (0 : ℝ) (a - f x)
  linarith

private def Smale.FlowConstruction.sublevelRetraction {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    {a b : ℝ} (F : Flow ℝ M)
    (hF : ∀ x t, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b → f (F t x) = f x + t)
    (hf : Continuous f) : C({ x : M // f x ≤ b }, { x : M // f x ≤ a })
    where
  toFun x := ⟨F (Min.min 0 (a - f x.1)) x.1, sublevel_retraction_mem F hF x.2⟩
  continuous_toFun :=
    (F.continuous (continuous_const.min (continuous_const.sub (hf.comp continuous_subtype_val)))
          continuous_subtype_val).subtype_mk
      _

private theorem Smale.FlowConstruction.sublevelRetraction_inclusion {M : Type*} [TopologicalSpace M]
    {f : M → ℝ} {a b : ℝ} (F : Flow ℝ M)
    (hF : ∀ x t, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b → f (F t x) = f x + t)
    (hf : Continuous f) (hab : a ≤ b) (x : { x : M // f x ≤ a }) :
    sublevelRetraction F hF hf (sublevelInclusion hab x) = x := by
  apply Subtype.ext
  change F (Min.min 0 (a - f x.1)) x.1 = x.1
  rw [min_eq_left (sub_nonneg.mpr x.2), F.map_zero_apply]

private def Smale.FlowConstruction.sublevelDeformation {M : Type*} [TopologicalSpace M] {f : M → ℝ}
    {a b : ℝ} (F : Flow ℝ M)
    (hF : ∀ x t, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b → f (F t x) = f x + t)
    (hf : Continuous f) (hab : a ≤ b) :
    (ContinuousMap.id { x : M // f x ≤ b }).HomotopyRel
      ((sublevelInclusion hab).comp (sublevelRetraction F hF hf)) {x | f x.1 ≤ a}
    where
  toFun
    p := ⟨F (p.1.1 * Min.min 0 (a - f p.2.1)) p.2.1, sublevel_deformation_mem F hF p.2.2 p.1.2⟩
  continuous_toFun :=
    (F.continuous
          ((continuous_subtype_val.comp continuous_fst).mul
            (continuous_const.min
              (continuous_const.sub (hf.comp (continuous_subtype_val.comp continuous_snd)))))
          (continuous_subtype_val.comp continuous_snd)).subtype_mk
      _
  map_zero_left
    x := by
    apply Subtype.ext
    change F ((0 : ℝ) * Min.min 0 (a - f x.1)) x.1 = x.1
    rw [MulZeroClass.zero_mul, F.map_zero_apply]
  map_one_left
    x := by
    apply Subtype.ext
    change F ((1 : ℝ) * Min.min 0 (a - f x.1)) x.1 = F (Min.min 0 (a - f x.1)) x.1
    rw [one_mul]
  prop' u x
    hx := by
    apply Subtype.ext
    change F (u.1 * Min.min 0 (a - f x.1)) x.1 = x.1
    rw [min_eq_left (sub_nonneg.mpr hx), MulZeroClass.mul_zero, F.map_zero_apply]

private def
    Smale.FlowConstruction.regularSublevelHomotopyEquivOfFlow {M : Type*} [TopologicalSpace M]
    {f : M → ℝ} {a b : ℝ} (F : Flow ℝ M)
    (hF : ∀ x t, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b → f (F t x) = f x + t)
    (hf : Continuous f) (hab : a ≤ b) : { x : M // f x ≤ a } ≃ₕ { x : M // f x ≤ b }
    where
  toFun := sublevelInclusion hab
  invFun := sublevelRetraction F hF hf
  left_inv := by
    have heq :
      (sublevelRetraction F hF hf).comp (sublevelInclusion hab) =
        ContinuousMap.id { x : M // f x ≤ a } := by
      apply ContinuousMap.ext
      intro x
      exact sublevelRetraction_inclusion F hF hf hab x
    rw [heq]
  right_inv := ⟨(sublevelDeformation F hF hf hab).toHomotopy.symm⟩

private theorem Smale.FlowConstruction.exists_regularSublevelHomotopyEquiv {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    ∃ e : { x : M // f x ≤ a } ≃ₕ { x : M // f x ≤ b }, ∀ x, (e x).1 = x.1 := by
  obtain ⟨F, hF⟩ := exists_heightTranslatingFlow hf hband
  exact ⟨regularSublevelHomotopyEquivOfFlow F hF hf.continuous hab, fun _ => rfl⟩

private theorem MorseCancel.ordered_upper_pathConnected_of_later_transfers {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f : M → ℝ} (S : Smale.ManifoldMorse.SurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (i : Fin S.count)
    (htransfer :
      ∀ j : Fin S.count,
        i.val < j.val →
          PathConnectedSpace { x : M // f x ≤ S.upper (S.point j) } →
            PathConnectedSpace { x : M // f x ≤ S.lower (S.point j) }) :
    PathConnectedSpace { x : M // f x ≤ S.upper (S.point i) } := by
  have hall :
    ∀ k : ℕ,
      ∀ i : Fin S.count,
        S.count - 1 - i.val = k →
          (∀ j : Fin S.count,
              i.val < j.val →
                PathConnectedSpace { x : M // f x ≤ S.upper (S.point j) } →
                  PathConnectedSpace { x : M // f x ≤ S.lower (S.point j) }) →
            PathConnectedSpace { x : M // f x ≤ S.upper (S.point i) } := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hki hindices
      have hpos : 0 < S.count := (Nat.zero_le i.val).trans_lt i.isLt
      by_cases hlast : i.val = S.count - 1
      · have hi : S.point i = S.last hpos := congrArg S.point (Fin.ext hlast)
        have hset : {x : M | f x ≤ S.upper (S.point i)} = Set.univ := by
          rw [hi]
          exact S.last_upper_univ hf hpos
        have hp : IsPathConnected {x : M | f x ≤ S.upper (S.point i)} :=
          hset.symm ▸ isPathConnected_univ
        exact isPathConnected_iff_pathConnectedSpace.mp hp
      · have hjlt : i.val + 1 < S.count := by omega
        let j : Fin S.count := ⟨i.val + 1, hjlt⟩
        have hjmeasure : S.count - 1 - j.val < k := by
          dsimp [j]
          omega
        have hupper : PathConnectedSpace { x : M // f x ≤ S.upper (S.point j) } :=
          ih _ hjmeasure j rfl (fun q hq => hindices q (by dsimp [j] at hq; omega))
        let : PathConnectedSpace { x : M // f x ≤ S.lower (S.point j) } :=
          hindices j (by dsimp [j]; omega) hupper
        have hij : i < j := by change i.val < i.val + 1; omega
        obtain ⟨e, -⟩ :=
          Smale.FlowConstruction.exists_regularSublevelHomotopyEquiv hf
            (S.ordered_windows i j hij).le (S.consecutive_regular i j rfl)
        exact pathConnectedSpace_of_homotopyEquiv e
  exact hall _ i rfl htransfer

private theorem MorseCancel.cell_old_empty_of_empty_boundary {N X : Type} [NormedAddCommGroup N]
     [TopologicalSpace X] [PreconnectedSpace X]
    (D : Smale.EmbeddedCellAttachment N X) [IsEmpty (Metric.sphere (0 : N) 1)] : D.old = ∅ := by
  have hdisjoint (z : Smale.MorseHandle.UnitDisk N) : D.cell z ∉ D.old := by
    intro hz
    exact
      isEmptyElim
        (⟨z.val, mem_sphere_zero_iff_norm.mpr ((D.boundary z).mp hz)⟩ : Metric.sphere (0 : N) 1)
  have heq : D.old = (Set.range D.cell)ᶜ := by
    ext x
    constructor
    · intro hx ⟨z, hz⟩
      exact hdisjoint z (hz ▸ hx)
    · intro hx
      have hc : x ∈ D.old ∪ Set.range D.cell := by rw [D.cover]; trivial
      exact hc.resolve_right hx
  have hc : IsClopen D.old := ⟨D.old_closed, heq.symm ▸ D.cell_closed.isClosed_range.isOpen_compl⟩
  rcases isClopen_iff.mp hc with h | h
  · exact h
  · let z : Smale.MorseHandle.UnitDisk N := ⟨0, by simp⟩
    exact False.elim (hdisjoint z (h ▸ Set.mem_univ _))

private theorem MorseCancel.native_zero_handle_lower_isEmpty {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 0)
    [PathConnectedSpace { z : M // f z ≤ f p + d.radius ^ 2 }] :
    IsEmpty { z : M // f z ≤ f p - d.radius ^ 2 } := by
  let : Subsingleton d.chart.NegativeCoordinates :=
    (Module.finrank_eq_zero_iff_of_free ℝ d.chart.NegativeCoordinates).mp hindex
  let : IsEmpty (Metric.sphere (0 : d.chart.NegativeCoordinates) 1) :=
    ⟨fun v => by
      have h := mem_sphere_zero_iff_norm.mp v.property
      rw [Subsingleton.elim v.val 0, norm_zero] at h
      norm_num at h⟩
  let : PathConnectedSpace ↥({z : M | f z ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap) :=
    pathConnectedSpace_of_homotopyEquiv (d.coreUnionHomotopyEquiv hf)
  have he := cell_old_empty_of_empty_boundary (d.coreCellPresentation hf)
  refine ⟨fun x => ?_⟩
  have hx := (d.cellOldHomeomorph hf x).property
  exact (Set.eq_empty_iff_forall_notMem.mp he) _ hx

private theorem
    Smale.SublevelDisk.circle_nullhomotopies {M : Type*} [TopologicalSpace M] [T2Space M]
    {f : M → ℝ} {a : ℝ} {n : ℕ} (d : Smale.SublevelDisk (n + 1) f a) (hn : 1 < n) :
    ∀ g : C(Smale.Hemisphere.Sphere 1, { x : M // f x = a }),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  let e : Smale.Hemisphere.Sphere n ≃ₜ { x : M // f x = a } := d.boundaryHomeomorph
  let forward : C(Smale.Hemisphere.Sphere n, { x : M // f x = a }) := ⟨e, e.continuous⟩
  let backward : C({ x : M // f x = a }, Smale.Hemisphere.Sphere n) := ⟨e.symm, e.symm.continuous⟩
  intro g
  obtain ⟨q, hq⟩ := NoExotic.sphere_sphere_nullhomotopic hn (backward.comp g)
  have heq : forward.comp (backward.comp g) = g := by
    apply ContinuousMap.ext
    intro x
    exact e.apply_symm_apply (g x)
  have hh : (forward.comp (backward.comp g)).Homotopic (ContinuousMap.const _ (e q)) :=
    (ContinuousMap.Homotopic.refl forward).comp hq
  exact ⟨e q, heq ▸ hh⟩

private def Smale.FlowConstruction.regularLevelHomeomorphOfFlow {M : Type*} [TopologicalSpace M]
    {f : M → ℝ} {a b : ℝ} (hab : a ≤ b) (F : Flow ℝ M)
    (hF : ∀ x t, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b → f (F t x) = f x + t) :
    { x : M // f x = a } ≃ₜ { x : M // f x = b } := by
  have hup (x : { x : M // f x = a }) : f (F (b - a) x) = b := by
    have hs : f x ∈ Set.Icc a b := by rw [x.property]; exact ⟨le_rfl, hab⟩
    have ht : f x + (b - a) ∈ Set.Icc a b := by
      rw [x.property, add_sub_cancel]
      exact ⟨hab, le_rfl⟩
    simpa only [x.property, add_sub_cancel] using hF x (b - a) hs ht
  have hdown (y : { x : M // f x = b }) : f (F (a - b) y) = a := by
    have hs : f y ∈ Set.Icc a b := by rw [y.property]; exact ⟨hab, le_rfl⟩
    have ht : f y + (a - b) ∈ Set.Icc a b := by
      rw [y.property, add_sub_cancel]
      exact ⟨le_rfl, hab⟩
    simpa only [y.property, add_sub_cancel] using hF y (a - b) hs ht
  refine
    { toFun := fun x => ⟨F (b - a) x, hup x⟩
      invFun := fun y => ⟨F (a - b) y, hdown y⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := (F.continuous continuous_const continuous_subtype_val).subtype_mk _
      continuous_invFun := (F.continuous continuous_const continuous_subtype_val).subtype_mk _ }
  · intro x
    apply Subtype.ext
    change F (a - b) (F (b - a) x) = x
    rw [← F.map_add, show a - b + (b - a) = 0 by ring, F.map_zero_apply]
  · intro y
    apply Subtype.ext
    change F (b - a) (F (a - b) y) = y
    rw [← F.map_add, show b - a + (a - b) = 0 by ring, F.map_zero_apply]

private theorem Smale.FlowConstruction.nonempty_regularLevelHomeomorph {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    Nonempty ({ x : M // f x = a } ≃ₜ { x : M // f x = b }) := by
  obtain ⟨F, hF⟩ := exists_heightTranslatingFlow hf hband
  exact ⟨regularLevelHomeomorphOfFlow hab F hF⟩

private theorem Smale.FlowConstruction.circle_nullhomotopies_regular_level {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hnull :
      ∀ g : C(Smale.Hemisphere.Sphere 1, { x : M // f x = a }),
        ∃ q, g.Homotopic (ContinuousMap.const _ q)) :
    ∀ g : C(Smale.Hemisphere.Sphere 1, { x : M // f x = b }),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  obtain ⟨e⟩ := nonempty_regularLevelHomeomorph hf hab hband
  let forward : C({ x : M // f x = a }, { x : M // f x = b }) := ⟨e, e.continuous⟩
  let backward : C({ x : M // f x = b }, { x : M // f x = a }) := ⟨e.symm, e.symm.continuous⟩
  intro g
  obtain ⟨q, hq⟩ := hnull (backward.comp g)
  have heq : forward.comp (backward.comp g) = g := by
    apply ContinuousMap.ext
    intro x
    exact e.apply_symm_apply (g x)
  have hh : (forward.comp (backward.comp g)).Homotopic (ContinuousMap.const _ (e q)) :=
    (ContinuousMap.Homotopic.refl forward).comp hq
  exact ⟨e q, heq ▸ hh⟩

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.SurgeryWindows.lower_circle_nullhomotopies_of_middle_indices
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {f : M → ℝ} (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (j : Fin S.count) (hj : 0 < j.val)
    (hindex :
      ∀ i : Fin S.count,
        0 < i.val →
          i.val < j.val →
            Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 2 ∨
              Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 3) :
    ∀ g : C(Smale.Hemisphere.Sphere 1, (S.data (S.point j)).LowerLevel),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  have hupper :
    ∀ n : ℕ,
      ∀ hn : n < S.count,
        n < j.val →
          ∀ g : C(Smale.Hemisphere.Sphere 1, (S.data (S.point ⟨n, hn⟩)).UpperLevel),
            ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
    intro n
    induction n with
    | zero =>
      intro hn _
      obtain ⟨d⟩ := S.nonempty_firstSublevelDisk hf hn
      have d' : Smale.SublevelDisk 6 f (S.upper (S.first hn)) := hdim ▸ d
      exact d'.circle_nullhomotopies (n := 5) (by norm_num)
    | succ n ih =>
      intro hn hnj
      have hn' : n < S.count := by omega
      have hprev := ih hn' (by omega)
      have hlt : (⟨n, hn'⟩ : Fin S.count) < ⟨n + 1, hn⟩ := Nat.lt_succ_self n
      have hlow :
        ∀ g : C(Smale.Hemisphere.Sphere 1, (S.data (S.point ⟨n + 1, hn⟩)).LowerLevel),
          ∃ q, g.Homotopic (ContinuousMap.const _ q) :=
        Smale.FlowConstruction.circle_nullhomotopies_regular_level hf
          (S.ordered_windows _ _ hlt).le (S.consecutive_regular _ _ rfl) hprev
      rcases hindex ⟨n + 1, hn⟩ (Nat.succ_pos n) hnj with htwo | hthree
      · let :
          Fact
            (Module.finrank ℝ (S.data (S.point ⟨n + 1, hn⟩)).chart.NegativeCoordinates = 1 + 1) :=
          ⟨htwo⟩
        exact
          (S.data (S.point ⟨n + 1, hn⟩)).upper_circle_nullhomotopies hf 1 (by norm_num) (by omega)
            hlow
      · let :
          Fact
            (Module.finrank ℝ (S.data (S.point ⟨n + 1, hn⟩)).chart.NegativeCoordinates = 2 + 1) :=
          ⟨hthree⟩
        exact
          (S.data (S.point ⟨n + 1, hn⟩)).upper_circle_nullhomotopies hf 2 (by norm_num) (by omega)
            hlow
  have hprev : j.val - 1 < S.count := by omega
  have hprevj : (⟨j.val - 1, hprev⟩ : Fin S.count) < j := by
    change j.val - 1 < j.val
    omega
  exact
    Smale.FlowConstruction.circle_nullhomotopies_regular_level hf
      (S.ordered_windows _ _ hprevj).le
      (S.consecutive_regular _ _ (by change j.val - 1 + 1 = j.val; omega))
      (hupper (j.val - 1) hprev hprevj)

private theorem MorseCancel.native_index_zero_point_unique {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hn : 0 < S.count) (hcount : nativeMorseCount E f 0 = 1) :
    ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
      nativeMorseIndex E f z = 0 → z = (S.first hn).val := by
  have hfirst : nativeMorseIndex E f (S.first hn) = 0 :=
    (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
  change
    {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 0}.ncard =
      1 at hcount
  obtain ⟨z₀, hz₀⟩ := Set.ncard_eq_one.mp hcount
  have hfirstmem :
    (S.first hn).val ∈
      {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 0} :=
    ⟨(S.first hn).property, hfirst⟩
  rw [hz₀, Set.mem_singleton_iff] at hfirstmem
  intro z hz hi
  have hzmem :
    z ∈ {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 0} :=
    ⟨hz, hi⟩
  rw [hz₀, Set.mem_singleton_iff] at hzmem
  exact hzmem.trans hfirstmem.symm

private theorem MorseCancel.native_index_one_excluded {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
       {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hcount : nativeMorseCount E f 1 = 0) :
    ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z ≠ 1 := by
  have hfinite :
    {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 1}.Finite :=
    S.finite.subset (fun _ hz => hz.1)
  have hempty :
    {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 1} = ∅ :=
    (Set.ncard_eq_zero hfinite).mp hcount
  intro z hz hi
  have hmem :
    z ∈ {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = 1} :=
    ⟨hz, hi⟩
  rw [hempty] at hmem
  exact hmem

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.lower_circle_nullhomotopies_of_ordered_native_indices {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hpindex : nativeMorseIndex E f p = 2) (hzero : nativeMorseCount E f 0 = 1)
    (hone : nativeMorseCount E f 1 = 0)
    (horder :
      ∀ r : Smale.ManifoldMorse.criticalPoints E f, f r < f p → nativeMorseIndex E f r ≤ 2) :
    ∀ γ : C(Smale.Hemisphere.Sphere 1, (S.data p).LowerLevel),
      ∃ z, γ.Homotopic (ContinuousMap.const _ z) := by
  obtain ⟨j, rfl⟩ := S.point.surjective p
  have hn : 0 < S.count := (Nat.zero_le j.val).trans_lt j.isLt
  have hpnotfirst : S.point j ≠ S.first hn := by
    intro hpfirst
    have hfirst : nativeMorseIndex E f (S.first hn) = 0 :=
      (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
    rw [hpfirst] at hpindex
    omega
  have hj : 0 < j.val := by
    by_contra hj
    have hj0 : j.val = 0 := by omega
    have heq : S.point j = S.first hn := congrArg S.point (Fin.ext hj0)
    exact hpnotfirst heq
  have hmiddle (i : Fin S.count) (hi : 0 < i.val) (hij : i.val < j.val) :
    Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 2 ∨
      Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 3 := by
    have hvalues : f (S.point i) < f (S.point j) := S.point_strictMono (show i < j from hij)
    have hle := horder (S.point i) hvalues
    have hne0 : nativeMorseIndex E f (S.point i) ≠ 0 := by
      intro hindex
      have heq : (S.point i).val = (S.first hn).val :=
        native_index_zero_point_unique S hf hn hzero _ (S.point i).property hindex
      have heq' : S.point i = S.point ⟨0, hn⟩ := Subtype.ext heq
      have hival := congrArg Fin.val (S.point.injective heq')
      change i.val = 0 at hival
      omega
    have hne1 := native_index_one_excluded S hone _ (S.point i).property
    have hindex : nativeMorseIndex E f (S.point i) = 2 := by omega
    exact Or.inl ((nativeMorseIndex_eq_chart (S.data (S.point i)).chart).symm.trans hindex)
  exact S.lower_circle_nullhomotopies_of_middle_indices hf hdim j hj hmiddle

private def MorseCancel.zeroChainCycle {X : Type} [TopologicalSpace X] :
    FirstHurewicz.Chains X 0 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 0
    where
  toFun
    z :=
    SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex X) 0 z
      (by
        have h := (FirstHurewicz.singularComplex X).shape 0 0 (by simp)
        exact congrArg (fun f => f.hom z) h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def MorseCancel.zeroChainClass {X : Type} [TopologicalSpace X] :
    FirstHurewicz.Chains X 0 →ₗ[ℤ] SingularMayerVietoris.SingularHomology X 0 :=
  (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 0).comp
    zeroChainCycle

private theorem MorseCancel.zeroChainClass_surjective {X : Type} [TopologicalSpace X] :
    Function.Surjective (zeroChainClass (X := X)) := by
  intro a
  obtain ⟨c, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (FirstHurewicz.singularComplex X) 0
      a
  exact ⟨c.val, rfl⟩

private theorem MorseCancel.homologyZero_linearMap_ext {X : Type} [TopologicalSpace X] {A : Type}
    [AddCommGroup A] [Module ℤ A] {L K : SingularMayerVietoris.SingularHomology X 0 →ₗ[ℤ] A}
    (h :
      ∀ x : X,
        L (PeriodTorusHigherHomology.pointClass x) = K (PeriodTorusHigherHomology.pointClass x)) :
    L = K := by
  have heq : L.comp zeroChainClass = K.comp zeroChainClass := by
    apply FirstHurewicz.chainMap_ext X 0
    intro σ
    have hσ : σ = ContinuousMap.const (FirstHurewicz.Simplex 0) (σ (stdSimplex.vertex 0)) := by
      ext t
      exact congrArg σ (FirstHurewicz.simplexZero_eq_vertex t)
    rw [hσ]
    exact h _
  apply LinearMap.ext
  intro a
  obtain ⟨z, rfl⟩ := zeroChainClass_surjective a
  exact LinearMap.congr_fun heq z

private def
    MorseCancel.cellDiskBoundaryHomologyMap {N X : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) 0 →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology D.diskPatch 0 :=
  SingularMayerVietoris.singularHomologyMap
    ((ContinuousMap.inclusion Set.inter_subset_right).comp D.overlapSphereEquiv.toFun) 0

private theorem MorseCancel.cell_oldHomologyMap_zero_iff {N X : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [TopologicalSpace X] (D : Smale.EmbeddedCellAttachment N X)
    (a : SingularMayerVietoris.SingularHomology D.old 0) :
    D.oldHomologyMap 0 a = 0 ↔
      ∃ z : SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) 0,
        D.attachingHomologyMap 0 z = a ∧ cellDiskBoundaryHomologyMap D z = 0 := by
  constructor
  · intro ha
    have hp :
      (D.oldHomologyEquiv 0 a, 0) ∈
        LinearMap.ker (SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch 0) := by
      change
        SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch 0
            (D.oldHomologyEquiv 0 a, 0) =
          0
      rw [D.coverRight_old]
      exact ha
    rw [←
      SingularMayerVietoris.exact_at_pair D.oldNeighborhood D.diskPatch D.isOpen_oldNeighborhood
        D.isOpen_diskPatch D.open_cover 0] at hp
    obtain ⟨c, hc⟩ := hp
    let z := (D.overlapHomologyEquiv 0).symm c
    have hL :
      SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch 0
          (D.overlapHomologyEquiv 0 z) =
        (D.oldHomologyEquiv 0 a, 0) := by
      dsimp [z]
      rw [LinearEquiv.apply_symm_apply]
      exact hc
    refine ⟨z, ?_, ?_⟩
    · rw [← D.coverLeft_old, hL, LinearEquiv.symm_apply_apply]
    · have hs := congrArg Prod.snd hL
      rw [SingularMayerVietoris.leftHomologyMap_apply] at hs
      change SingularMayerVietoris.singularHomologyMap _ 0 z = 0
      rw [PeriodTorusHigherHomology.singularHomologyMap_comp]
      exact neg_eq_zero.mp hs
  · rintro ⟨z, hza, hz⟩
    have hL :
      SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch 0
          (D.overlapHomologyEquiv 0 z) =
        (D.oldHomologyEquiv 0 a, 0) := by
      apply Prod.ext
      · exact (D.oldHomologyEquiv 0).symm_apply_eq.mp ((D.coverLeft_old 0 z).trans hza)
      · rw [SingularMayerVietoris.leftHomologyMap_apply]
        rw [cellDiskBoundaryHomologyMap, PeriodTorusHigherHomology.singularHomologyMap_comp] at hz
        exact neg_eq_zero.mpr hz
    have hzero :=
      LinearMap.congr_fun
        (SingularMayerVietoris.leftHomologyMap_comp_right D.oldNeighborhood D.diskPatch 0)
        (D.overlapHomologyEquiv 0 z)
    change
      SingularMayerVietoris.rightHomologyMap D.oldNeighborhood D.diskPatch 0
          (SingularMayerVietoris.leftHomologyMap D.oldNeighborhood D.diskPatch 0
            (D.overlapHomologyEquiv 0 z)) =
        0 at hzero
    rw [hL, D.coverRight_old] at hzero
    exact hzero

private theorem MorseCancel.cell_oldHomologyMap_injective_of_attaching_component {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : Smale.EmbeddedCellAttachment N X) (p : D.old)
    (hcomponent : ∀ u, Joined (D.attachingSphere u) p) :
    Function.Injective (D.oldHomologyMap 0) := by
  let c : C(D.diskPatch, D.old) := ContinuousMap.const _ p
  have heq :
    D.attachingHomologyMap 0 =
      (SingularMayerVietoris.singularHomologyMap c 0).comp (cellDiskBoundaryHomologyMap D) := by
    apply homologyZero_linearMap_ext
    intro u
    change
      SingularMayerVietoris.singularHomologyMap D.attachingSphere 0
          (PeriodTorusHigherHomology.pointClass u) =
        SingularMayerVietoris.singularHomologyMap c 0
          (SingularMayerVietoris.singularHomologyMap _ 0 (PeriodTorusHigherHomology.pointClass u))
    rw [PeriodTorusHigherHomology.singularHomologyMap_pointClass,
      PeriodTorusHigherHomology.singularHomologyMap_pointClass,
      PeriodTorusHigherHomology.singularHomologyMap_pointClass]
    exact (pointClass_eq_iff_joined _ _).mpr (hcomponent u)
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  obtain ⟨z, hza, hz⟩ := (cell_oldHomologyMap_zero_iff D a).mp ha
  rw [← hza, heq, LinearMap.comp_apply, hz, map_zero]

private theorem MorseCancel.cell_old_pathConnected_of_attaching_component {N X : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace X]
    (D : Smale.EmbeddedCellAttachment N X) [PathConnectedSpace X] (p : D.old)
    (hcomponent : ∀ u, Joined (D.attachingSphere u) p) : PathConnectedSpace D.old := by
  let : Nonempty D.old := ⟨p⟩
  exact
    pathConnectedSpace_of_homologyZero_injective (SingularMayerVietoris.subtypeInclusion D.old)
      (cell_oldHomologyMap_injective_of_attaching_component D p hcomponent)

private theorem MorseCancel.native_lower_pathConnected_of_attaching_component {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (a : { z : M // f z ≤ f p - d.radius ^ 2 }) (hcomponent : ∀ u, Joined (d.coreBoundaryMap u) a)
    [PathConnectedSpace { z : M // f z ≤ f p + d.radius ^ 2 }] :
    PathConnectedSpace { z : M // f z ≤ f p - d.radius ^ 2 } := by
  let : PathConnectedSpace ↥({z : M | f z ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap) :=
    pathConnectedSpace_of_homotopyEquiv (d.coreUnionHomotopyEquiv hf)
  let : PathConnectedSpace (d.coreCellPresentation hf).old :=
    cell_old_pathConnected_of_attaching_component (d.coreCellPresentation hf)
      (d.cellOldHomeomorph hf a)
      (fun u => by
        rw [d.coreCell_attaching_eq]
        exact (hcomponent u).map (d.cellOldHomeomorph hf).continuous)
  exact pathConnectedSpace_of_homotopyEquiv (d.cellOldHomeomorph hf).toHomotopyEquiv

private theorem MorseCancel.native_attaching_component_of_pairwise_joined {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hindex : 0 < Module.finrank ℝ d.chart.NegativeCoordinates)
    (hjoined : ∀ u v, Joined (d.coreBoundaryMap u) (d.coreBoundaryMap v)) :
    ∃ a : { z : M // f z ≤ f p - d.radius ^ 2 }, ∀ u, Joined (d.coreBoundaryMap u) a := by
  let : Nontrivial d.chart.NegativeCoordinates := Module.nontrivial_of_finrank_pos hindex
  obtain ⟨v, hv⟩ : (Metric.sphere (0 : d.chart.NegativeCoordinates) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  exact ⟨d.coreBoundaryMap ⟨v, hv⟩, fun u => hjoined u ⟨v, hv⟩⟩

private theorem MorseCancel.native_minimum_count_one_of_one_handle_components {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f : M → ℝ} (S : Smale.ManifoldMorse.SurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hcomponents :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E f p = 1 →
          ∃ a : { z : M // f z ≤ f p - (S.data p).radius ^ 2 },
            ∀ u, Joined ((S.data p).coreBoundaryMap u) a) :
    nativeMorseCount E f 0 = 1 := by
  classical
  have hn := S.count_pos hf
  have hfirst : nativeMorseIndex E f (S.first hn) = 0 :=
    (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
  let K : Finset (Fin S.count) :=
    Finset.univ.filter (fun i => nativeMorseIndex E f (S.point i) = 0)
  have hK : K.Nonempty := ⟨⟨0, hn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfirst⟩⟩
  let j : Fin S.count := K.max' hK
  have hjzero : nativeMorseIndex E f (S.point j) = 0 := (Finset.mem_filter.mp (K.max'_mem hK)).2
  have hmax (i : Fin S.count) (hi : nativeMorseIndex E f (S.point i) = 0) : i ≤ j :=
    K.le_max' i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  have htail (i : Fin S.count) (hji : j.val < i.val)
    (hupper : PathConnectedSpace { x : M // f x ≤ S.upper (S.point i) }) :
    PathConnectedSpace { x : M // f x ≤ S.lower (S.point i) } := by
    let : PathConnectedSpace { x : M // f x ≤ f (S.point i) + (S.data (S.point i)).radius ^ 2 } :=
      hupper
    have hne : nativeMorseIndex E f (S.point i) ≠ 0 := by
      intro hi
      have hm : i.val ≤ j.val := hmax i hi
      omega
    have heq := nativeMorseIndex_eq_chart (S.data (S.point i)).chart
    by_cases hone : nativeMorseIndex E f (S.point i) = 1
    · obtain ⟨a, ha⟩ := hcomponents (S.point i) hone
      exact
        native_lower_pathConnected_of_attaching_component (S.data (S.point i)) hf.continuous a ha
    · exact native_lower_pathConnected_of_upper (S.data (S.point i)) hf.continuous (by omega)
  let : PathConnectedSpace { x : M // f x ≤ f (S.point j) + (S.data (S.point j)).radius ^ 2 } :=
    ordered_upper_pathConnected_of_later_transfers S hf j htail
  let : IsEmpty { x : M // f x ≤ f (S.point j) - (S.data (S.point j)).radius ^ 2 } :=
    native_zero_handle_lower_isEmpty (S.data (S.point j)) hf.continuous
      ((nativeMorseIndex_eq_chart (S.data (S.point j)).chart).symm.trans hjzero)
  have hjfirst : j.val = 0 := by
    by_contra hj
    have hlt : (⟨0, hn⟩ : Fin S.count) < j := by change 0 < j.val; omega
    have hbelow : f (S.first hn) ≤ S.lower (S.point j) :=
      (S.value_lt_upper (S.first hn)).le.trans (S.ordered_windows _ _ hlt).le
    exact
      isEmptyElim
        (⟨S.first hn, hbelow⟩ :
          { x : M // f x ≤ f (S.point j) - (S.data (S.point j)).radius ^ 2 })
  have hset :
    {x : M | x ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f x = 0} =
      {(S.first hn).val} := by
    ext x
    constructor
    · rintro ⟨hx, hi⟩
      obtain ⟨i, he⟩ := S.point.surjective ⟨x, hx⟩
      have hi0 : nativeMorseIndex E f (S.point i) = 0 := by simpa only [he] using hi
      have hle : i.val ≤ j.val := hmax i hi0
      have hi0' : i.val = 0 := by omega
      have hip : S.point i = S.first hn := congrArg S.point (Fin.ext hi0')
      exact Set.mem_singleton_iff.mpr (congrArg Subtype.val (he.symm.trans hip))
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      exact hx ▸ ⟨(S.first hn).property, hfirst⟩
  exact Set.ncard_eq_one.mpr ⟨(S.first hn).val, hset⟩

private theorem MorseCancel.exists_native_one_handle_joining_components {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f : M → ℝ} (S : Smale.ManifoldMorse.SurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hmin : nativeMorseCount E f 0 ≠ 1) :
    ∃ p : Smale.ManifoldMorse.criticalPoints E f,
      nativeMorseIndex E f p = 1 ∧
        ∃ u v, ¬Joined ((S.data p).coreBoundaryMap u) ((S.data p).coreBoundaryMap v) := by
  classical
  by_contra h
  apply hmin
  apply native_minimum_count_one_of_one_handle_components S hf
  intro p hp
  have hindex : 0 < Module.finrank ℝ (S.data p).chart.NegativeCoordinates := by
    rw [← nativeMorseIndex_eq_chart (S.data p).chart, hp]
    exact zero_lt_one
  apply native_attaching_component_of_pairwise_joined (S.data p) hindex
  intro u v
  by_contra huv
  exact h ⟨p, hp, u, v, huv⟩

private theorem MorseCancel.cancel_realized_higher_minimum {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f₀ : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f₀) (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f₀)
    (hm₀ : Smale.ManifoldMorse.IsMorse E f₀) {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (G : Flow ℝ M) (hG : ∀ x, IsMIntegralCurve (fun t => G t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f₀, V x = 0)
    (hdesc₀ : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f₀ → mvfderiv 𝓘(ℝ, E) f₀ x (V x) < 0)
    (hmodels₀ :
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f₀,
        ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) f₀ x,
          ∀ᶠ y in 𝓝 x, V y = c.descentField y)
    (p r q : Smale.ManifoldMorse.criticalPoints E f₀) (hpzero : nativeMorseIndex E f₀ p = 0)
    (hqone : nativeMorseIndex E f₀ q = 1) (hrp : f₀ r < f₀ p) (hp : f₀ p < S.lower q)
    (u v : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hback :
      ∀ x : (S.data q).LowerLevel,
        Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ↔
          x ∈ Set.range (S.data q).surgery.attachingSphere)
    (hu :
      Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere u).val) Filter.atTop
        (𝓝 p.val))
    (hv :
      Filter.Tendsto (fun t => G t ((S.data q).surgery.attachingSphere v).val) Filter.atTop
        (𝓝 r.val))
    (hnoconnection :
      ∀ j : Smale.ManifoldMorse.criticalPoints E f₀,
        j ≠ q →
          j ≠ p →
            j ≠ r →
              ∀ x,
                ¬(Filter.Tendsto (fun t => G t x) Filter.atBot (𝓝 q.val) ∧
                    Filter.Tendsto (fun t => G t x) Filter.atTop (𝓝 j.val))) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) ∧
            (Smale.ManifoldMorse.criticalPoints E g).ncard + 2 =
              (Smale.ManifoldMorse.criticalPoints E f₀).ncard := by
  have hpr : p ≠ r := fun h => (ne_of_lt hrp) (congrArg (fun x => f₀ x.val) h).symm
  obtain ⟨hzback, hunique⟩ :=
    unique_connection_of_distinct_minimum_branches S hf₀.continuous G p r q hqone hpr hp u v hback
      hu hv
  obtain ⟨f, hf, hm, hcrit, hinj, -, -, hpq, hconsecutive, hdesc, hmodels, hindices⟩ :=
    exists_flow_preserving_consecutive_pair hf₀ hm₀ S.distinct hV G hG hzero hdesc₀ hmodels₀ p r q
      hrp (hp.trans (S.lower_lt_value q)) hnoconnection
  let pf : Smale.ManifoldMorse.criticalPoints E f := ⟨p.val, by rw [hcrit]; exact p.property⟩
  let qf : Smale.ManifoldMorse.criticalPoints E f := ⟨q.val, by rw [hcrit]; exact q.property⟩
  have hconsecutivef : ∀ z : Smale.ManifoldMorse.criticalPoints E f, ¬(f pf < f z ∧ f z < f qf) :=
    by
    intro z hz
    exact hconsecutive ⟨z.val, by rw [← hcrit]; exact z.property⟩ hz
  obtain ⟨T⟩ := Smale.ManifoldMorse.nonempty_surgeryWindows hf hm hinj
  obtain ⟨cp, hcp⟩ := hmodels pf pf.property
  obtain ⟨cq, hcq⟩ := hmodels qf qf.property
  obtain ⟨g, hg, hmg, hcard, hcritg, hexterior⟩ :=
    cancel_unique_zero_one_connection cp cq hf hm ((hindices p p.property).trans hpzero)
      ((hindices q q.property).trans hqone) hV G hG (fun x hx => hzero x (hcrit ▸ hx)) hdesc hinj
      pf.property qf.property hpq (T.lower_lt_value pf) (T.value_lt_upper qf)
      (surgery_pair_band_isolation T pf qf hconsecutivef) hu hzback hunique hcp hcq
  have hkeep :=
    surviving_critical_germs_of_pair_band (surgery_pair_band_isolation T pf qf hconsecutivef)
      hcritg hexterior
  have hinjg :=
    distinct_critical_values_of_surviving_germs hinj (fun x hx => ((hcritg x).mp hx).1) hkeep
  exact ⟨g, hg, hmg, hinjg, hcard.trans (congrArg Set.ncard hcrit)⟩

private theorem MorseCancel.exists_excellent_morse_reduction_of_multiple_minima {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f₀ : M → ℝ} (S : AdaptedWindows E f₀)
    (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f₀) (hm₀ : Smale.ManifoldMorse.IsMorse E f₀)
    (hmin : nativeMorseCount E f₀ 0 ≠ 1) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) ∧
            (Smale.ManifoldMorse.criticalPoints E g).ncard + 2 =
              (Smale.ManifoldMorse.criticalPoints E f₀).ncard := by
  obtain ⟨q, hqone, u, v, hnot⟩ :=
    exists_native_one_handle_joining_components S.toSurgeryWindows hf₀ hmin
  obtain
    ⟨V, G, p, r, hV, hG, hzero, hdesc, hgerms, hpzero, hrzero, hpr, hp, hr, hback, hu, hv, -,
      hnoconnection⟩ :=
    S.realize_one_handle_minimum_branches hf₀ q hqone u v hnot
  have hmodels (x : M) (hx : x ∈ Smale.ManifoldMorse.criticalPoints E f₀) :
    ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) f₀ x,
      ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    refine ⟨(S.data ⟨x, hx⟩).chart, ?_⟩
    filter_upwards [hgerms x hx, S.critical_model_germ ⟨x, hx⟩] with y h₁ h₂
    exact h₁.trans h₂
  have hne : f₀ p ≠ f₀ r := fun h => hpr (Subtype.ext (S.distinct p.property r.property h))
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact
      cancel_realized_higher_minimum S.toSurgeryWindows hf₀ hm₀ hV G hG hzero hdesc hmodels r p q
        hrzero hqone hlt hr v u hback hv hu (fun j hjq hjr hjp => hnoconnection j hjq hjp hjr)
  · exact
      cancel_realized_higher_minimum S.toSurgeryWindows hf₀ hm₀ hV G hG hzero hdesc hmodels p r q
        hpzero hqone hgt hp u v hback hu hv hnoconnection

private theorem MorseCancel.isMorseAt_neg {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (hm : Smale.ManifoldMorse.IsMorseAt E f p) :
    Smale.ManifoldMorse.IsMorseAt E (fun x => -f x) p := by
  obtain ⟨e, he, hp, hregular | hH⟩ := hm
  · refine ⟨e, he, hp, Or.inl ?_⟩
    change fderiv ℝ (fun x => -f (e.symm x)) (e p) ≠ 0
    rw [fderiv_fun_neg, neg_ne_zero]
    exact hregular
  · refine ⟨e, he, hp, Or.inr ?_⟩
    have hd : fderiv ℝ ((fun x => -f x) ∘ e.symm) = fun z => -fderiv ℝ (f ∘ e.symm) z := by
      funext z
      exact fderiv_fun_neg
    rw [hd, fderiv_fun_neg]
    change Function.Bijective (fun v => -(fderiv ℝ (fderiv ℝ (f ∘ e.symm)) (e p) v))
    exact neg_bijective.comp hH

private theorem MorseCancel.isMorse_neg {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} (hm : Smale.ManifoldMorse.IsMorse E f) :
    Smale.ManifoldMorse.IsMorse E (fun x => -f x) := fun x => isMorseAt_neg (hm x)

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.negative_finrank_neg_chart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) :
    Module.finrank ℝ c.neg.NegativeCoordinates = Module.finrank ℝ c.PositiveCoordinates := by
  simp only [Smale.ManifoldMorse.SignedMorseChart.NegativeCoordinates,
    Smale.ManifoldMorse.SignedMorseChart.PositiveCoordinates, Smale.MorseHandle.NegativeSpace,
    Smale.MorseHandle.PositiveSpace, finrank_euclideanSpace]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro i
  change -c.weights i = -1 ↔ c.weights i ≠ -1
  rcases c.signs i with h | h <;> norm_num [h]

private theorem MorseCancel.nativeMorseIndex_neg_add {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) :
    nativeMorseIndex E (fun x => -f x) p + nativeMorseIndex E f p = Module.finrank ℝ E := by
  rw [nativeMorseIndex_eq_chart c.neg, nativeMorseIndex_eq_chart c, negative_finrank_neg_chart]
  exact (Nat.add_comm _ _).trans c.finrank_negative_add_positive

private theorem
    MorseCancel.nativeMorseCount_neg {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} [FiniteDimensional ℝ E]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f) {k : ℕ}
    (hk : k ≤ Module.finrank ℝ E) :
    nativeMorseCount E (fun x => -f x) (Module.finrank ℝ E - k) = nativeMorseCount E f k := by
  unfold nativeMorseCount
  congr 1
  ext z
  rw [Smale.ManifoldMorse.criticalPoints_neg]
  change
    (z ∈ Smale.ManifoldMorse.criticalPoints E f ∧
        nativeMorseIndex E (fun x => -f x) z = Module.finrank ℝ E - k) ↔
      (z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k)
  constructor
  · rintro ⟨hz, hi⟩
    obtain ⟨c⟩ := Smale.ManifoldMorse.nonempty_signedMorseChart hf hm z hz
    have hsum := nativeMorseIndex_neg_add c
    exact ⟨hz, by omega⟩
  · rintro ⟨hz, hi⟩
    obtain ⟨c⟩ := Smale.ManifoldMorse.nonempty_signedMorseChart hf hm z hz
    have hsum := nativeMorseIndex_neg_add c
    exact ⟨hz, by omega⟩

private theorem MorseCancel.exists_minimal_excellent_morse_system (E : Type*) (M : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          ∃ _ : AdaptedWindows E f,
            ∀ g : M → ℝ,
              ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
                Smale.ManifoldMorse.IsMorse E g →
                  Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
                    (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
                      (Smale.ManifoldMorse.criticalPoints E g).ncard := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f) ∧
            (Smale.ManifoldMorse.criticalPoints E f).ncard = n
  obtain ⟨f₀, hf₀, hm₀, -, hinj₀⟩ :=
    Smale.ManifoldMorse.exists_morse_function_with_distinct_critical_values E M
  have hex : ∃ n, P n :=
    ⟨(Smale.ManifoldMorse.criticalPoints E f₀).ncard, f₀, hf₀, hm₀, hinj₀, rfl⟩
  obtain ⟨f, hf, hm, hinj, hcard⟩ := Nat.find_spec hex
  obtain ⟨S⟩ := nonempty_adaptedSurgeryWindows hf hm hinj
  refine ⟨f, hf, hm, S, ?_⟩
  intro g hg hmg hinjg
  rw [hcard]
  exact Nat.find_min' hex ⟨g, hg, hmg, hinjg, rfl⟩

private theorem MorseCancel.minimal_excellent_morse_forbids_pair_removal {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {f g : M → ℝ}
    (hminimal :
      ∀ h : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h →
          Smale.ManifoldMorse.IsMorse E h →
            Set.InjOn h (Smale.ManifoldMorse.criticalPoints E h) →
              (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
                (Smale.ManifoldMorse.criticalPoints E h).ncard)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (hmg : Smale.ManifoldMorse.IsMorse E g)
    (hinjg : Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g)) :
    (Smale.ManifoldMorse.criticalPoints E g).ncard + 2 ≠
      (Smale.ManifoldMorse.criticalPoints E f).ncard := by
  have hle := hminimal g hg hmg hinjg
  omega

private theorem MorseCancel.distinct_critical_values_neg {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f)) :
    Set.InjOn (fun x => -f x) (Smale.ManifoldMorse.criticalPoints E (fun x => -f x)) := by
  rw [Smale.ManifoldMorse.criticalPoints_neg]
  intro x hx y hy hxy
  exact hinj hx hy (neg_injective hxy)

private theorem MorseCancel.minimal_excellent_morse_neg {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hminimal :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          Smale.ManifoldMorse.IsMorse E g →
            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
              (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
                (Smale.ManifoldMorse.criticalPoints E g).ncard) :
    ∀ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
        Smale.ManifoldMorse.IsMorse E g →
          Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
            (Smale.ManifoldMorse.criticalPoints E (fun x => -f x)).ncard ≤
              (Smale.ManifoldMorse.criticalPoints E g).ncard := by
  intro g hg hmg hinjg
  have hh :=
    hminimal (fun x => -g x) hg.neg (isMorse_neg hmg) (distinct_critical_values_neg hinjg)
  simpa only [Smale.ManifoldMorse.criticalPoints_neg] using hh

private theorem
    Smale.FiniteSignedCancellation.opposite_signs_distinct {a b : SignType} (h : a * b = -1) :
    a ≠ b := by cases a <;> cases b <;> simp_all

private theorem Smale.FiniteSignedCancellation.cast_add_eq_zero_of_opposite {a b : SignType}
    (h : a * b = -1) : (a : ℤ) + (b : ℤ) = 0 := by cases a <;> cases b <;> simp_all

private theorem
    Smale.FiniteSignedCancellation.sum_sdiff_pair {X : Type*} [DecidableEq X] (s : Finset X)
    (σ : X → SignType) {x y : X} (hx : x ∈ s) (hy : y ∈ s) (hxy : σ x * σ y = -1) :
    ∑ z ∈ s \ { x, y }, (σ z : ℤ) = ∑ z ∈ s, (σ z : ℤ) := by
  classical
  have hne : x ≠ y := fun h => opposite_signs_distinct hxy (congrArg σ h)
  have hsub : ({ x, y } : Finset X) ⊆ s := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hx
    · exact Finset.mem_singleton.mp hz ▸ hy
  have hsum : ∑ z ∈ ({ x, y } : Finset X), (σ z : ℤ) = 0 := by
    rw [Finset.sum_pair hne]
    exact cast_add_eq_zero_of_opposite hxy
  have h := Finset.sum_sdiff (f := fun z => (σ z : ℤ)) hsub
  simpa only [hsum, add_zero] using h

private theorem Smale.FiniteSignedCancellation.sum_sdiff_pair_of_eq {X : Type*} [DecidableEq X]
    (s : Finset X) (σ τ : X → SignType) {x y : X} (hx : x ∈ s) (hy : y ∈ s) (hxy : σ x * σ y = -1)
    (heq : ∀ z ∈ s \ { x, y }, τ z = σ z) : ∑ z ∈ s \ { x, y }, (τ z : ℤ) = ∑ z ∈ s, (σ z : ℤ) := by
  calc
    _ = ∑ z ∈ s \ { x, y }, (σ z : ℤ) :=
      Finset.sum_congr rfl (fun z hz => congrArg (fun a : SignType => (a : ℤ)) (heq z hz))
    _ = _ := sum_sdiff_pair s σ hx hy hxy

private theorem Smale.FiniteSignedCancellation.card_eq_natAbs_sum_of_no_opposite {X : Type*}
    (s : Finset X) (σ : X → SignType) (hunit : ∀ x ∈ s, σ x = 1 ∨ σ x = -1)
    (hno : ∀ x ∈ s, ∀ y ∈ s, σ x * σ y ≠ -1) : s.card = (∑ x ∈ s, (σ x : ℤ)).natAbs := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  have heq (y : X) (hy : y ∈ s) : σ y = σ x := by
    rcases hunit x hx with hxp | hxn <;> rcases hunit y hy with hyp | hyn
    · exact hyp.trans hxp.symm
    · exact (hno x hx y hy (by rw [hxp, hyn]; simp)).elim
    · exact (hno x hx y hy (by rw [hxn, hyp]; simp)).elim
    · exact hyn.trans hxn.symm
  have hsum : (∑ y ∈ s, (σ y : ℤ)) = ∑ _ ∈ s, (σ x : ℤ) := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [heq y hy]
  rw [hsum]
  rcases hunit x hx with hp | hn
  · simp [hp]
  · simp [hn]

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.MorseSurgeryData.exists_finite_belt_cancellation_step {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (D : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ γ : C(Smale.Hemisphere.Sphere 1, D.LowerLevel),
        ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient 3)
    (P : Finset (Smale.Hemisphere.Sphere 2)) (g : C(Smale.Hemisphere.Sphere 2, D.UpperLevel))
    (hP : (P : Set (Smale.Hemisphere.Sphere 2)) = D.beltIntersectionPoints 2 g)
    (hgood : D.IsTransverseBeltSphere hf hdim hindex g) (x y : Smale.Hemisphere.Sphere 2)
    (hx : x ∈ P) (hy : y ∈ P)
    (hxy : D.beltIntersectionSign 2 r g x * D.beltIntersectionSign 2 r g y = -1) :
    letI := Smale.RegularLevel.chartedSpace hf D.upper_regular
    ∃ e :
      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E) D.UpperLevel
        D.UpperLevel ∞,
      ∃ g' : C(Smale.Hemisphere.Sphere 2, D.UpperLevel),
        Smale.SupportedDiffeomorph.IsotopicToIdentity e ∧
          (∀ z, g' z = e (g z)) ∧
            D.IsTransverseBeltSphere hf hdim hindex g' ∧
              ((P \ { x, y } : Finset (Smale.Hemisphere.Sphere 2)) :
                    Set (Smale.Hemisphere.Sphere 2)) =
                  D.beltIntersectionPoints 2 g' ∧
                (∀ z ∈ P \ { x, y }, (g' : Smale.Hemisphere.Sphere 2 → D.UpperLevel) =ᶠ[𝓝 z] g) ∧
                  (∑ z ∈ P \ { x, y }, (D.beltIntersectionSign 2 r g' z : ℤ)) =
                    ∑ z ∈ P, (D.beltIntersectionSign 2 r g z : ℤ) := by
  let _ := Smale.RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  obtain ⟨hg, hinj, hi, ht⟩ := hgood
  have hxB : x ∈ D.beltIntersectionPoints 2 g := hP ▸ hx
  have hyB : y ∈ D.beltIntersectionPoints 2 g := hP ▸ hy
  obtain ⟨e, g', hiso, heq, hg', hinj', hi', ht', hpoints, hgerm, hsign⟩ :=
    D.exists_signed_belt_cancellation_step hf hdim hindex hnull r g hg hinj hi ht x y hxB hyB hxy
  have hP' :
    ((P \ { x, y } : Finset (Smale.Hemisphere.Sphere 2)) : Set (Smale.Hemisphere.Sphere 2)) =
      D.beltIntersectionPoints 2 g' := by
    rw [hpoints, ← hP]
    simp only [Finset.coe_sdiff, Finset.coe_insert, Finset.coe_singleton]
  have hmem (z : Smale.Hemisphere.Sphere 2) (hz : z ∈ P \ { x, y }) :
    z ∈ D.beltIntersectionPoints 2 g' := hP' ▸ hz
  refine ⟨e, g', hiso, heq, ⟨hg', hinj', hi', ht'⟩, hP', ?_, ?_⟩
  · exact fun z hz => hgerm z (hmem z hz)
  · exact
      Smale.FiniteSignedCancellation.sum_sdiff_pair_of_eq P (D.beltIntersectionSign 2 r g)
        (D.beltIntersectionSign 2 r g') (x := x) (y := y) hx hy hxy
        (fun z hz => hsign z (hmem z hz))

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.exists_finite_belt_reduction {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (D : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ γ : C(Smale.Hemisphere.Sphere 1, D.LowerLevel),
        ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient 3)
    (P : Finset (Smale.Hemisphere.Sphere 2)) (g : C(Smale.Hemisphere.Sphere 2, D.UpperLevel))
    (hP : (P : Set (Smale.Hemisphere.Sphere 2)) = D.beltIntersectionPoints 2 g)
    (hgood : D.IsTransverseBeltSphere hf hdim hindex g) :
    letI := Smale.RegularLevel.chartedSpace hf D.upper_regular
    ∃ e :
      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E) D.UpperLevel
        D.UpperLevel ∞,
      ∃ g' : C(Smale.Hemisphere.Sphere 2, D.UpperLevel),
        ∃ P' : Finset (Smale.Hemisphere.Sphere 2),
          Smale.SupportedDiffeomorph.IsotopicToIdentity e ∧
            (∀ x, g' x = e (g x)) ∧
              D.IsTransverseBeltSphere hf hdim hindex g' ∧
                (P' : Set (Smale.Hemisphere.Sphere 2)) = D.beltIntersectionPoints 2 g' ∧
                  P' ⊆ P ∧
                    (∀ x ∈ P', (g' : Smale.Hemisphere.Sphere 2 → D.UpperLevel) =ᶠ[𝓝 x] g) ∧
                      (∑ x ∈ P', (D.beltIntersectionSign 2 r g' x : ℤ)) =
                          ∑ x ∈ P, (D.beltIntersectionSign 2 r g x : ℤ) ∧
                        ∀ x ∈ P',
                          ∀ y ∈ P',
                            D.beltIntersectionSign 2 r g' x * D.beltIntersectionSign 2 r g' y ≠
                              -1 := by
  let _ := Smale.RegularLevel.chartedSpace hf D.upper_regular
  induction P using Finset.strongInductionOn generalizing g with
  | _ P
    ih =>
    by_cases hpair :
      ∃ x ∈ P, ∃ y ∈ P, D.beltIntersectionSign 2 r g x * D.beltIntersectionSign 2 r g y = -1
    · obtain ⟨x, hx, y, hy, hxy⟩ := hpair
      obtain ⟨e₁, g₁, hiso₁, heq₁, hgood₁, hR, hgerm₁, hsum₁⟩ :=
        D.exists_finite_belt_cancellation_step hf hdim hindex hnull r P g hP hgood x y hx hy hxy
      let R : Finset (Smale.Hemisphere.Sphere 2) := P \ { x, y }
      have hsubpair : ({ x, y } : Finset (Smale.Hemisphere.Sphere 2)) ⊆ P := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hx
        · exact Finset.mem_singleton.mp hz ▸ hy
      have hRlt : R ⊂ P := Finset.sdiff_ssubset hsubpair ⟨x, by simp⟩
      obtain ⟨e₂, g₂, P₂, hiso₂, heq₂, hgood₂, hP₂, hsub₂, hgerm₂, hsum₂, hno₂⟩ :=
        ih R hRlt g₁ hR hgood₁
      refine
        ⟨e₁.trans e₂, g₂, P₂, hiso₁.trans hiso₂, ?_, hgood₂, hP₂, hsub₂.trans Finset.sdiff_subset,
          ?_, hsum₂.trans hsum₁, hno₂⟩
      · intro z
        change g₂ z = e₂ (e₁ (g z))
        rw [heq₂, heq₁]
      · intro z hz
        exact (hgerm₂ z hz).trans (hgerm₁ z (hsub₂ hz))
    · refine
        ⟨Diffeomorph.refl _ _ _, g, P, Smale.SupportedDiffeomorph.isotopicToIdentity_refl,
          fun _ => rfl, hgood, hP, fun _ hx => hx, fun _ _ => Filter.EventuallyEq.refl _ _, rfl,
          ?_⟩
      intro x hx y hy hxy
      exact hpair ⟨x, hx, y, hy, hxy⟩

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.exists_minimal_signed_belt_sphere {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (D : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ γ : C(Smale.Hemisphere.Sphere 1, D.LowerLevel),
        ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient 3)
    (g : C(Smale.Hemisphere.Sphere 2, D.UpperLevel))
    (hgood : D.IsTransverseBeltSphere hf hdim hindex g) :
    letI := Smale.RegularLevel.chartedSpace hf D.upper_regular
    ∃ e :
      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E) D.UpperLevel
        D.UpperLevel ∞,
      ∃ g' : C(Smale.Hemisphere.Sphere 2, D.UpperLevel),
        Smale.SupportedDiffeomorph.IsotopicToIdentity e ∧
          (∀ x, g' x = e (g x)) ∧
            D.IsTransverseBeltSphere hf hdim hindex g' ∧
              D.beltIntersectionPoints 2 g' ⊆ D.beltIntersectionPoints 2 g ∧
                (∀ x ∈ D.beltIntersectionPoints 2 g',
                    (g' : Smale.Hemisphere.Sphere 2 → D.UpperLevel) =ᶠ[𝓝 x] g) ∧
                  (∀ hfin' : (D.beltIntersectionPoints 2 g').Finite,
                      D.beltIntersectionCount 2 r g' hfin' =
                        D.beltIntersectionCount 2 r g
                          (D.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood)) ∧
                    (D.beltIntersectionPoints 2 g').ncard =
                      (D.beltIntersectionCount 2 r g
                          (D.finite_points_of_isTransverseBeltSphere hf hdim hindex
                            hgood)).natAbs := by
  let _ := Smale.RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  let hfin := D.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood
  obtain ⟨e, g', P', hiso, heq, hgood', hP', hsub, hgerm, hsum, hno⟩ :=
    D.exists_finite_belt_reduction hf hdim hindex hnull r hfin.toFinset g hfin.coe_toFinset hgood
  have hunit :
    ∀ x ∈ P', D.beltIntersectionSign 2 r g' x = 1 ∨ D.beltIntersectionSign 2 r g' x = -1 := by
    obtain ⟨hg', _, _, ht'⟩ := hgood'
    intro x hx
    exact D.beltIntersectionSign_unit hf 3 2 hindex r g' hg' ht' x (hP' ▸ hx)
  have hmem (x : Smale.Hemisphere.Sphere 2) (hx : x ∈ D.beltIntersectionPoints 2 g') : x ∈ P' := by
    change x ∈ (P' : Set (Smale.Hemisphere.Sphere 2))
    rw [hP']
    exact hx
  refine ⟨e, g', hiso, heq, hgood', ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxP : x ∈ P' := hmem x hx
    exact hfin.mem_toFinset.mp (hsub hxP)
  · intro x hx
    exact hgerm x (hmem x hx)
  · intro hfin'
    have hPfin : hfin'.toFinset = P' := by
      apply Finset.coe_injective
      exact hfin'.coe_toFinset.trans hP'.symm
    change (∑ x ∈ hfin'.toFinset, (D.beltIntersectionSign 2 r g' x : ℤ)) = _
    rw [hPfin]
    exact hsum
  · calc
      (D.beltIntersectionPoints 2 g').ncard = P'.card := by rw [← hP', Set.ncard_coe_finset]
      _ = (∑ x ∈ P', (D.beltIntersectionSign 2 r g' x : ℤ)).natAbs :=
        (Smale.FiniteSignedCancellation.card_eq_natAbs_sum_of_no_opposite P'
          (D.beltIntersectionSign 2 r g') hunit hno)
      _ = _ := congrArg Int.natAbs hsum

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.exists_single_belt_intersection_of_unit_count
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ γ : C(Smale.Hemisphere.Sphere 1, D.LowerLevel),
        ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient 3)
    (g : C(Smale.Hemisphere.Sphere 2, D.UpperLevel))
    (hgood : D.IsTransverseBeltSphere hf hdim hindex g)
    (hcount :
      (D.beltIntersectionCount 2 r g
            (D.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood)).natAbs =
        1) :
    letI := Smale.RegularLevel.chartedSpace hf D.upper_regular
    ∃ e :
      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E) D.UpperLevel
        D.UpperLevel ∞,
      ∃ g' : C(Smale.Hemisphere.Sphere 2, D.UpperLevel),
        ∃ x : Smale.Hemisphere.Sphere 2,
          Smale.SupportedDiffeomorph.IsotopicToIdentity e ∧
            (∀ y, g' y = e (g y)) ∧
              D.IsTransverseBeltSphere hf hdim hindex g' ∧
                D.beltIntersectionPoints 2 g' = { x } ∧
                  Set.range g' ∩ Set.range D.surgery.beltSphere = {g' x} := by
  let _ := Smale.RegularLevel.chartedSpace hf D.upper_regular
  obtain ⟨e, g', hiso, heq, hgood', _, _, _, hsize⟩ :=
    D.exists_minimal_signed_belt_sphere hf hdim hindex hnull r g hgood
  have hone : (D.beltIntersectionPoints 2 g').ncard = 1 := hsize.trans hcount
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hone
  refine ⟨e, g', x, hiso, heq, hgood', hx, ?_⟩
  have himage :
    g' '' D.beltIntersectionPoints 2 g' = Set.range g' ∩ Set.range D.surgery.beltSphere := by
    change g' '' (g' ⁻¹' Set.range D.surgery.beltSphere) = _
    rw [Set.image_preimage_eq_inter_range, Set.inter_comm]
  rw [← himage, hx, Set.image_singleton]

attribute [local instance 100] Classical.propDecidable in
private theorem AdaptedWindows.remove_connections_of_index_le {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hpq : f p < f q)
    (hconsecutive : ∀ r : Smale.ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (n m : ℕ) (hqindex : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = n + 1)
    (hppos : Module.finrank ℝ (S.data p).chart.PositiveCoordinates = m + 1)
    (hle :
      Module.finrank ℝ (S.data q).chart.NegativeCoordinates ≤
        Module.finrank ℝ (S.data p).chart.NegativeCoordinates) :
    ∃ (V : (z : M) → TangentSpace 𝓘(ℝ, E) z) (G : Flow ℝ M),
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun z => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ z, IsMIntegralCurve (fun t => G t z) V) ∧
          (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, V z = 0) ∧
            (∀ z, z ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f z (V z) < 0) ∧
              (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, V y = S.field y) ∧
                ∀ z,
                  ¬(Filter.Tendsto (fun t => G t z) Filter.atBot (𝓝 q.val) ∧
                      Filter.Tendsto (fun t => G t z) Filter.atTop (𝓝 p.val)) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).lower_regular
  let _ := Smale.RegularLevel.isManifold hf (S.data p).upper_regular
  let _ : CompactSpace (S.data p).UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = n + 1) := ⟨hqindex⟩
  let _ : Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = m + 1) := ⟨hppos⟩
  obtain ⟨D, b, -, hb, horbit⟩ := S.exists_orbit_bandBridge hf p q hpq hconsecutive
  have horbit' (x : (S.data p).UpperLevel) : ∃ t, S.flow t x = (b x : M) := by
    obtain ⟨t, ht⟩ := horbit x
    exact ⟨t, ht.trans (hb x).symm⟩
  let α := (S.data p).transportedAttachingSphere (S.data q) n b.toHomeomorph
  have hα : ContMDiff (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ α :=
    (S.data p).transportedAttachingSphere_smooth (S.data q) hf n b
  have hB := (S.data p).belt_smooth hf m
  have hdim :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) + Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) <
      Module.finrank ℝ (Smale.RegularLevel.Model E) := by
    simp only [Smale.RegularLevel.Model, finrank_euclideanSpace, Fintype.card_fin]
    have hh := (S.data p).chart.finrank_negative_add_positive
    omega
  obtain ⟨e, he, hdisjoint⟩ :=
    Degree.MorseRearrangement.exists_ambient_disjoint_diffeomorph_of_dimension hα hB hdim
  have hbasins :
    ∀ x : (S.data p).UpperLevel,
      ¬(Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 q.val) ∧
          Filter.Tendsto (fun t => S.flow t (e x)) Filter.atTop (𝓝 p.val)) := by
    rintro x ⟨hxq, hxp⟩
    obtain ⟨v, hv⟩ := (S.transported_attaching_basin_iff hf p q n b.toHomeomorph horbit' x).mp hxq
    have hB := (S.belt_basin_iff hf p (e x)).mp hxp
    have hαx : e x ∈ Set.range (e ∘ α) := ⟨v, congrArg e hv⟩
    exact Set.disjoint_left.mp hdisjoint hαx hB
  have hpc : f p < f p + (S.data p).radius ^ 2 := S.toSurgeryWindows.value_lt_upper p
  have hqc : f p + (S.data p).radius ^ 2 < f q :=
    (S.separated p q hpq).trans (S.toSurgeryWindows.lower_lt_value q)
  obtain ⟨a, hpa, hac⟩ := exists_between hpc
  obtain ⟨b', hcb, hbq⟩ := exists_between hqc
  let z : (S.data p).UpperLevel := α (Classical.arbitrary (Smale.Hemisphere.Sphere n))
  obtain
    ⟨_, _, _, V, H, G, -, -, -, -, -, -, hgeometry, hV, hG, hzeros, hneg, hgerms, -, hend, -,
      hleft, hright⟩ :=
    Degree.FlowSuspension.exists_native_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral hac hcb
      (MorseCancel.surgery_pair_inner_band_regular p q hconsecutive hpa hbq)
      (S.data p).upper_regular z e he
  obtain ⟨hback, hforward⟩ :=
    Degree.FlowSuspension.whole_level_basins_of_holonomy S.flow H G Subtype.val e
      (fun x => (hgeometry x).2.1) (fun x => (hgeometry x).2.2) hend hleft hright
  refine ⟨V, G, hV, hG, fun x hx => (hzeros x).mpr (S.zero x hx), hneg, hgerms, ?_⟩
  exact
    Degree.FlowSuspension.no_connection_of_level_basin_disjointness S.flow G hf.continuous hqc hpc
      e (fun x => hback x q.val) (fun x => hforward x p.val) hbasins

private theorem MorseCancel.unitSphere_isEmpty_of_finrank_zero {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [FiniteDimensional ℝ A] (hA : Module.finrank ℝ A = 0) :
    IsEmpty (Smale.PuncturedHandle.UnitSphere A) := by
  let _ : Subsingleton A := (Module.finrank_eq_zero_iff_of_free ℝ A).mp hA
  refine ⟨fun v => ?_⟩
  have hh := mem_sphere_zero_iff_norm.mp v.property
  rw [Subsingleton.elim (v : A) 0, norm_zero] at hh
  norm_num at hh

private theorem
    AdaptedWindows.no_connection_of_upper_index_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hpq : f p < f q) (hqzero : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 0) :
    ∀ x,
      ¬(Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 q.val) ∧
          Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)) := by
  let _ := MorseCancel.unitSphere_isEmpty_of_finrank_zero hqzero
  rintro x ⟨hxq, hxp⟩
  obtain ⟨t, ht⟩ :=
    Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hxq hxp
      (S.toSurgeryWindows.lower_lt_value q)
      ((S.toSurgeryWindows.value_lt_upper p).trans (S.separated p q hpq))
  let y : (S.data q).LowerLevel := ⟨S.flow t x, ht⟩
  have hlim : Filter.Tendsto (fun s => S.flow s (y : M)) Filter.atBot (𝓝 q.val) :=
    (MorseCancel.flow_time_atBot_limit_iff S.flow t x q.val).mpr hxq
  obtain ⟨v, -⟩ := (S.attaching_basin_iff hf q y).mp hlim
  exact isEmptyElim v

private theorem
    AdaptedWindows.no_connection_of_lower_positive_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hpq : f p < f q) (hpzero : Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 0) :
    ∀ x,
      ¬(Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 q.val) ∧
          Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)) := by
  let _ := MorseCancel.unitSphere_isEmpty_of_finrank_zero hpzero
  rintro x ⟨hxq, hxp⟩
  obtain ⟨t, ht⟩ :=
    Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hxq hxp
      ((S.separated p q hpq).trans (S.toSurgeryWindows.lower_lt_value q))
      (S.toSurgeryWindows.value_lt_upper p)
  let y : (S.data p).UpperLevel := ⟨S.flow t x, ht⟩
  have hlim : Filter.Tendsto (fun s => S.flow s (y : M)) Filter.atTop (𝓝 p.val) :=
    (MorseCancel.flow_time_atTop_limit_iff S.flow t x p.val).mpr hxp
  obtain ⟨v, -⟩ := (S.belt_basin_iff hf p y).mp hlim
  exact isEmptyElim v

private theorem AdaptedWindows.remove_connections_of_nonincreasing_indices {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : Smale.ManifoldMorse.criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : Smale.ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hle :
      Module.finrank ℝ (S.data q).chart.NegativeCoordinates ≤
        Module.finrank ℝ (S.data p).chart.NegativeCoordinates) :
    ∃ (V : (z : M) → TangentSpace 𝓘(ℝ, E) z) (G : Flow ℝ M),
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun z => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ z, IsMIntegralCurve (fun t => G t z) V) ∧
          (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, V z = 0) ∧
            (∀ z, z ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f z (V z) < 0) ∧
              (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, V y = S.field y) ∧
                ∀ z,
                  ¬(Filter.Tendsto (fun t => G t z) Filter.atBot (𝓝 q.val) ∧
                      Filter.Tendsto (fun t => G t z) Filter.atTop (𝓝 p.val)) := by
  by_cases hqzero : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 0
  · exact
      ⟨S.field, S.flow, S.smooth, S.integral, S.zero, S.descent, fun _ _ =>
        Filter.Eventually.of_forall (fun _ => rfl),
        S.no_connection_of_upper_index_zero hf p q hpq hqzero⟩
  by_cases hpzero : Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 0
  · exact
      ⟨S.field, S.flow, S.smooth, S.integral, S.zero, S.descent, fun _ _ =>
        Filter.Eventually.of_forall (fun _ => rfl),
        S.no_connection_of_lower_positive_zero hf p q hpq hpzero⟩
  exact
    S.remove_connections_of_index_le hf p q hpq hconsecutive
      (Module.finrank ℝ (S.data q).chart.NegativeCoordinates - 1)
      (Module.finrank ℝ (S.data p).chart.PositiveCoordinates - 1) (by omega) (by omega) hle

private theorem
    AdaptedWindows.exchange_nonincreasing_native_indices {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hpq : f p < f q)
    (hconsecutive : ∀ r : Smale.ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hle : MorseCancel.nativeMorseIndex E f q ≤ MorseCancel.nativeMorseIndex E f p) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f ∧
            g p = f q ∧
              g q = f p ∧
                (∀ z,
                    f z ∉ Set.Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) →
                      g =ᶠ[𝓝 z] f) ∧
                  (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                      z ≠ p.val → z ≠ q.val → g =ᶠ[𝓝 z] f) ∧
                    Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) ∧
                      Nonempty (AdaptedWindows E g) ∧
                        (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                            MorseCancel.nativeMorseIndex E g z =
                              MorseCancel.nativeMorseIndex E f z) ∧
                          ∀ k,
                            MorseCancel.nativeMorseCount E g k =
                              MorseCancel.nativeMorseCount E f k := by
  have hle' :
    Module.finrank ℝ (S.data q).chart.NegativeCoordinates ≤
      Module.finrank ℝ (S.data p).chart.NegativeCoordinates := by
    rwa [MorseCancel.nativeMorseIndex_eq_chart (S.data q).chart,
      MorseCancel.nativeMorseIndex_eq_chart (S.data p).chart] at hle
  obtain ⟨V, G, hV, hG, hzeros, hneg, hgerms, hnoconnection⟩ :=
    S.remove_connections_of_nonincreasing_indices hf p q hpq hconsecutive hle'
  have hpgerm : ∀ᶠ y in 𝓝 p.val, V y = (S.data p).chart.descentField y := by
    filter_upwards [hgerms p p.property, S.critical_model_germ p] with y hy hmodel
    exact hy.trans hmodel
  have hqgerm : ∀ᶠ y in 𝓝 q.val, V y = (S.data q).chart.descentField y := by
    filter_upwards [hgerms q q.property, S.critical_model_germ q] with y hy hmodel
    exact hy.trans hmodel
  have hpband : f p ∈ Set.Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) :=
    ⟨S.toSurgeryWindows.lower_lt_value p, hpq.trans (S.toSurgeryWindows.value_lt_upper q)⟩
  have hqband : f q ∈ Set.Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) :=
    ⟨(S.toSurgeryWindows.lower_lt_value p).trans hpq, S.toSurgeryWindows.value_lt_upper q⟩
  obtain ⟨g, hg, hmg, hcrit, hgp, hgq, -, hexterior, -, -, hothers, hindices⟩ :=
    Degree.MorseRearrangement.exists_morse_rearrangement_of_no_connection hf hm hV G hG hzeros
      hneg S.distinct (S.data p).chart (S.data q).chart hpgerm hqgerm hpband hqband hpq hqband
      hpband (MorseCancel.surgery_pair_band_isolation S.toSurgeryWindows p q hconsecutive)
      hnoconnection
  obtain ⟨hinj, hnew⟩ :=
    MorseCancel.adapted_surgery_system_after_value_exchange S hg hmg p.property q.property hcrit
      hgp hgq hothers
  exact
    ⟨g, hg, hmg, hcrit, hgp, hgq, hexterior, hothers, hinj, hnew, hindices,
      MorseCancel.nativeMorseCount_eq_of_preserved_indices hcrit hindices⟩

attribute [local instance 100] Classical.propDecidable in
private def MorseCancel.nativeIndexDisorder (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) : ℕ :=
  if hfinite : (Smale.ManifoldMorse.criticalPoints E f).Finite then
    let _ := hfinite.fintype
    Degree.MorseRearrangement.finiteIndexDisorder
      (fun x : Smale.ManifoldMorse.criticalPoints E f => f x)
      (fun x : Smale.ManifoldMorse.criticalPoints E f => nativeMorseIndex E f x)
  else 0

private theorem MorseCancel.nativeIndexDisorder_eq_of_finite {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (hfinite : (Smale.ManifoldMorse.criticalPoints E f).Finite) :
    letI := hfinite.fintype
    nativeIndexDisorder E f =
      Degree.MorseRearrangement.finiteIndexDisorder
        (fun x : Smale.ManifoldMorse.criticalPoints E f => f x)
        (fun x : Smale.ManifoldMorse.criticalPoints E f => nativeMorseIndex E f x) := by
  classical simp only [nativeIndexDisorder, dite_eq_left hfinite]

private theorem MorseCancel.nativeIndexDisorder_transport {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    (hfinite : (Smale.ManifoldMorse.criticalPoints E f).Finite)
    (hcrit : Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f)
    (hindex :
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E g x = nativeMorseIndex E f x) :
    letI := hfinite.fintype
    nativeIndexDisorder E g =
      Degree.MorseRearrangement.finiteIndexDisorder
        (fun x : Smale.ManifoldMorse.criticalPoints E f => g x)
        (fun x : Smale.ManifoldMorse.criticalPoints E f => nativeMorseIndex E f x) := by
  classical
  let _ := hfinite.fintype
  have hgfinite : (Smale.ManifoldMorse.criticalPoints E g).Finite := hcrit.symm ▸ hfinite
  let _ := hgfinite.fintype
  let e : Smale.ManifoldMorse.criticalPoints E f ≃ Smale.ManifoldMorse.criticalPoints E g :=
    Equiv.setCongr hcrit.symm
  rw [nativeIndexDisorder_eq_of_finite hgfinite]
  rw [←
    Degree.MorseRearrangement.finiteIndexDisorder_comp_equiv
      (fun x : Smale.ManifoldMorse.criticalPoints E g => g x)
      (fun x : Smale.ManifoldMorse.criticalPoints E g => nativeMorseIndex E g x) e]
  have hw :
    ((fun x : Smale.ManifoldMorse.criticalPoints E g => nativeMorseIndex E g x) ∘ e) =
      fun x : Smale.ManifoldMorse.criticalPoints E f => nativeMorseIndex E f x := by
    funext x
    exact hindex x x.property
  rw [hw]
  rfl

private theorem MorseCancel.nativeIndexDisorder_exchange_lt {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    (hfinite : (Smale.ManifoldMorse.criticalPoints E f).Finite)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f))
    (p q : Smale.ManifoldMorse.criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : Smale.ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hindexlt : nativeMorseIndex E f q < nativeMorseIndex E f p)
    (hcrit : Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f)
    (hgp : g p = f q) (hgq : g q = f p)
    (hothers : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, x ≠ p.val → x ≠ q.val → g =ᶠ[𝓝 x] f)
    (hindex :
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E g x = nativeMorseIndex E f x) :
    nativeIndexDisorder E g < nativeIndexDisorder E f := by
  classical
  let _ : DecidableEq (Smale.ManifoldMorse.criticalPoints E f) := fun a b =>
    Classical.propDecidable (a = b)
  let _ := hfinite.fintype
  have hform :
    (fun x : Smale.ManifoldMorse.criticalPoints E f => g x) =
      (fun x : Smale.ManifoldMorse.criticalPoints E f => f x) ∘ Equiv.swap p q := by
    funext x
    by_cases hxp : x = p
    · subst x
      simpa only [Function.comp_apply, Equiv.swap_apply_left] using hgp
    by_cases hxq : x = q
    · subst x
      simpa only [Function.comp_apply, Equiv.swap_apply_right] using hgq
    have hh :=
      (hothers x x.property (fun h => hxp (Subtype.ext h))
          (fun h => hxq (Subtype.ext h))).self_of_nhds
    simpa only [Function.comp_apply, Equiv.swap_apply_def, ite_eq_right hxp,
      ite_eq_right hxq] using hh
  rw [nativeIndexDisorder_transport hfinite hcrit hindex,
    nativeIndexDisorder_eq_of_finite hfinite, hform]
  have hi : Function.Injective (fun x : Smale.ManifoldMorse.criticalPoints E f => f x) :=
    fun x y h => Subtype.ext (hinj x.property y.property h)
  exact
    Degree.MorseRearrangement.finiteIndexDisorder_swap_lt (h :=
      fun x : Smale.ManifoldMorse.criticalPoints E f => f x) hi
      (fun x : Smale.ManifoldMorse.criticalPoints E f => nativeMorseIndex E f x) (p := p) (q := q)
      hpq hconsecutive hindexlt

private theorem
    MorseCancel.exists_index_ordered_morse_system_preserving_critical_points {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]
    {f₀ : M → ℝ} (S₀ : AdaptedWindows E f₀) (hf₀ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f₀)
    (hm₀ : Smale.ManifoldMorse.IsMorse E f₀) :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          Smale.ManifoldMorse.criticalPoints E f = Smale.ManifoldMorse.criticalPoints E f₀ ∧
            (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f₀,
                nativeMorseIndex E f x = nativeMorseIndex E f₀ x) ∧
              ∃ _ : AdaptedWindows E f,
                (∀ p q : Smale.ManifoldMorse.criticalPoints E f,
                    f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q) ∧
                  ∀ k, nativeMorseCount E f k = nativeMorseCount E f₀ k := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          Smale.ManifoldMorse.criticalPoints E f = Smale.ManifoldMorse.criticalPoints E f₀ ∧
            (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f₀,
                nativeMorseIndex E f x = nativeMorseIndex E f₀ x) ∧
              Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f) ∧ nativeIndexDisorder E f = n
  have hex : ∃ n, P n :=
    ⟨nativeIndexDisorder E f₀, f₀, hf₀, hm₀, rfl, fun _ _ => rfl, S₀.distinct, rfl⟩
  obtain ⟨f, hf, hm, hcrit, hindices, hinj, hdisorder⟩ := Nat.find_spec hex
  obtain ⟨S⟩ := nonempty_adaptedSurgeryWindows hf hm hinj
  have horder :
    ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
      f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q := by
    by_contra hnot
    let _ := S.finite.fintype
    obtain ⟨p, q, hpq, hconsecutive, hinversion⟩ :=
      Degree.MorseRearrangement.exists_adjacent_index_inversion (h :=
        fun x : Smale.ManifoldMorse.criticalPoints E f => f x)
        (fun x y h => Subtype.ext (hinj x.property y.property h))
        (fun x : Smale.ManifoldMorse.criticalPoints E f => nativeMorseIndex E f x) hnot
    obtain ⟨g, hg, hmg, hcritg, hgp, hgq, -, hothers, hinjg, -, hindicesg, -⟩ :=
      S.exchange_nonincreasing_native_indices hf hm p q hpq hconsecutive hinversion.le
    have hdecrease : nativeIndexDisorder E g < nativeIndexDisorder E f :=
      nativeIndexDisorder_exchange_lt S.finite hinj p q hpq hconsecutive hinversion hcritg hgp hgq
        hothers hindicesg
    have hindicesg₀ (x : M) (hx : x ∈ Smale.ManifoldMorse.criticalPoints E f₀) :
      nativeMorseIndex E g x = nativeMorseIndex E f₀ x :=
      (hindicesg x (by rw [hcrit]; exact hx)).trans (hindices x hx)
    have hminimal := Nat.find_min' hex ⟨g, hg, hmg, hcritg.trans hcrit, hindicesg₀, hinjg, rfl⟩
    rw [← hdisorder] at hminimal
    exact (not_le_of_gt hdecrease) hminimal
  exact
    ⟨f, hf, hm, hcrit, hindices, S, horder,
      nativeMorseCount_eq_of_preserved_indices hcrit hindices⟩

private theorem
    MorseCancel.minimal_excellent_morse_minimum_count_one {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f)
    (hminimal :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          Smale.ManifoldMorse.IsMorse E g →
            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
              (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
                (Smale.ManifoldMorse.criticalPoints E g).ncard) :
    nativeMorseCount E f 0 = 1 := by
  by_contra hmin
  obtain ⟨g, hg, hmg, hinjg, hcount⟩ :=
    exists_excellent_morse_reduction_of_multiple_minima S hf hm hmin
  exact minimal_excellent_morse_forbids_pair_removal hminimal hg hmg hinjg hcount

private theorem
    MorseCancel.minimal_excellent_morse_extreme_counts_one {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f)
    (hminimal :
      ∀ g : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g →
          Smale.ManifoldMorse.IsMorse E g →
            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) →
              (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
                (Smale.ManifoldMorse.criticalPoints E g).ncard) :
    nativeMorseCount E f 0 = 1 ∧ nativeMorseCount E f (Module.finrank ℝ E) = 1 := by
  refine ⟨minimal_excellent_morse_minimum_count_one S hf hm hminimal, ?_⟩
  obtain ⟨T⟩ :=
    nonempty_adaptedSurgeryWindows hf.neg (isMorse_neg hm)
      (distinct_critical_values_neg S.distinct)
  have hmin :=
    minimal_excellent_morse_minimum_count_one T hf.neg (isMorse_neg hm)
      (minimal_excellent_morse_neg hminimal)
  have hcounts := nativeMorseCount_neg hf hm (le_refl (Module.finrank ℝ E))
  rw [Nat.sub_self] at hcounts
  exact hcounts.symm.trans hmin

attribute [local instance 100] Classical.propDecidable in
private theorem
    AdaptedWindows.exists_transverse_middle_belt_loop {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (p q : Smale.ManifoldMorse.criticalPoints E f) (hp : MorseCancel.nativeMorseIndex E f p = 0)
    (hq : MorseCancel.nativeMorseIndex E f q = 1)
    [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 4 + 1)]
    (u : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hbranches :
      ∀ w : Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
        Filter.Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere w).val) Filter.atTop
          (𝓝 p.val))
    {a : ℝ} (hqa : S.toSurgeryWindows.upper q ≤ a)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hlow :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        f z ≤ a → MorseCancel.nativeMorseIndex E f z ≤ 2) :
    let _ := Smale.RegularLevel.chartedSpace hf ha
    ∃ δ : C(Smale.Hemisphere.Sphere 1, { y : M // f y = a }),
      ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ δ ∧
        Function.Injective δ ∧
          (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) δ z)) ∧
            ∃ (z₀ : Smale.Hemisphere.Sphere 1) (v :
              Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (β :
              Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1 → { y : M // f y = a }),
              MDifferentiableAt (𝓡 4) 𝓘(ℝ, Smale.RegularLevel.Model E) β v ∧
                β v = δ z₀ ∧
                  Smale.NativeTransversality.At (𝓡 1) (𝓡 4) 𝓘(ℝ, Smale.RegularLevel.Model E) δ β
                      z₀ v ∧
                    (∀ᶠ w in 𝓝 v,
                        Filter.Tendsto (fun t => S.flow t (β w).val) Filter.atTop (𝓝 q.val)) ∧
                      (∀ z,
                          Filter.Tendsto (fun t => S.flow t (δ z).val) Filter.atTop (𝓝 q.val) ↔
                            z = z₀) ∧
                        ∀ z,
                          Filter.Tendsto (fun t => S.flow t (δ z).val) Filter.atTop (𝓝 p.val) ∨
                            Filter.Tendsto (fun t => S.flow t (δ z).val) Filter.atTop (𝓝 q.val) :=
  by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.isManifold hf (S.data q).upper_regular
  let _ := Smale.RegularLevel.isManifold hf ha
  obtain ⟨v, γ, hγ, hγi, hγd, hreach, z₀, hsingle, htrans, hendpoints⟩ :=
    S.exists_transverse_belt_circle_reaching_level_with_endpoints hf p q hp hq 4 u hbranches hqa
      ha hlow (by omega) (by omega) (by omega)
  obtain ⟨t₀, ht₀⟩ := hreach z₀
  let za : { y : M // f y = a } := ⟨S.flow t₀ (γ z₀).val, ht₀⟩
  obtain ⟨D, hsource, -, horbit⟩ :=
    S.exists_native_level_basin_transport hf (S.data q).upper_regular ha (γ z₀) za
  have hγsource (z : Circle) : γ z ∈ D.source := hsource.symm ▸ hreach z
  have hΓsmooth : ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (D ∘ γ) := by
    intro z
    exact
      (D.contMDiffOn_toFun.contMDiffAt (D.open_source.mem_nhds (hγsource z))).comp z
        hγ.contMDiffAt
  let Γ : C(Circle, { y : M // f y = a }) := ⟨D ∘ γ, hΓsmooth.continuous⟩
  have hΓi : Function.Injective Γ := by
    intro z w hzw
    exact hγi (D.toPartialEquiv.injOn (hγsource z) (hγsource w) hzw)
  have hΓd : ∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) Γ z) := by
    intro z
    change Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) (D ∘ γ) z)
    rw [mfderiv_comp z (D.mdifferentiableAt (by simp) (hγsource z))
        (hγ.mdifferentiableAt (by simp))]
    exact (Smale.PartialChart.bijective_mfderiv D (hγsource z)).1.comp (hγd z)
  have hcross : (S.data q).surgery.beltSphere v = γ z₀ := ((hsingle z₀ v).mpr ⟨rfl, rfl⟩).symm
  have hvsource : (S.data q).surgery.beltSphere v ∈ D.source := hcross.symm ▸ hγsource z₀
  let β := D ∘ (S.data q).surgery.beltSphere
  have hβ : MDifferentiableAt (𝓡 4) 𝓘(ℝ, Smale.RegularLevel.Model E) β v :=
    (D.mdifferentiableAt (by simp) hvsource).comp v
      (((S.data q).belt_smooth hf 4).mdifferentiableAt (by simp))
  have hβcross : β v = Γ z₀ := congrArg D hcross
  have hΓtrans :
    Smale.NativeTransversality.At (𝓡 1) (𝓡 4) 𝓘(ℝ, Smale.RegularLevel.Model E) Γ β z₀ v :=
    (Degree.TransverseGerms.native_transversality_partial_diffeomorph_iff D
          (hγ.mdifferentiableAt (by simp))
          (((S.data q).belt_smooth hf 4).mdifferentiableAt (by simp)) hcross (hγsource z₀)).mp
      (fun _ => htrans)
  have hβbasin :
    ∀ᶠ w in 𝓝 v, Filter.Tendsto (fun t => S.flow t (β w).val) Filter.atTop (𝓝 q.val) := by
    have hnear :=
      (((S.data q).belt_smooth hf 4).continuous.tendsto v) (D.open_source.mem_nhds hvsource)
    filter_upwards [hnear] with w hw
    obtain ⟨t, ht⟩ := horbit ((S.data q).surgery.beltSphere w) hw
    change S.flow t ((S.data q).surgery.beltSphere w).val = (β w).val at ht
    rw [← ht]
    exact
      (MorseCancel.flow_time_atTop_limit_iff S.flow t _ q.val).mpr
        ((S.belt_basin_iff hf q ((S.data q).surgery.beltSphere w)).mpr ⟨w, rfl⟩)
  have hforward (z : Circle) :
    Filter.Tendsto (fun t => S.flow t (Γ z).val) Filter.atTop (𝓝 q.val) ↔ z = z₀ := by
    obtain ⟨t, ht⟩ := horbit (γ z) (hγsource z)
    change S.flow t (γ z).val = (Γ z).val at ht
    have hbasin :
      Filter.Tendsto (fun s => S.flow s (Γ z).val) Filter.atTop (𝓝 q.val) ↔
        γ z ∈ Set.range (S.data q).surgery.beltSphere := by
      rw [← ht]
      exact
        (MorseCancel.flow_time_atTop_limit_iff S.flow t (γ z).val q.val).trans
          (S.belt_basin_iff hf q (γ z))
    rw [hbasin]
    constructor
    · rintro ⟨w, hw⟩
      exact ((hsingle z w).mp hw.symm).1
    · intro hz
      exact ⟨v, ((hsingle z v).mpr ⟨hz, rfl⟩).symm⟩
  have hΓends (z : Circle) :
    Filter.Tendsto (fun t => S.flow t (Γ z).val) Filter.atTop (𝓝 p.val) ∨
      Filter.Tendsto (fun t => S.flow t (Γ z).val) Filter.atTop (𝓝 q.val) := by
    obtain ⟨t, ht⟩ := horbit (γ z) (hγsource z)
    change S.flow t (γ z).val = (Γ z).val at ht
    rw [← ht]
    exact
      (hendpoints z).imp ((MorseCancel.flow_time_atTop_limit_iff S.flow t _ p.val).mpr)
        ((MorseCancel.flow_time_atTop_limit_iff S.flow t _ q.val).mpr)
  let δ : C(Smale.Hemisphere.Sphere 1, { y : M // f y = a }) :=
    ⟨Γ ∘ MorseCancel.standardCircleParametrization,
      Γ.continuous.comp MorseCancel.standardCircleParametrization.continuous⟩
  let z := MorseCancel.standardCircleParametrization.symm z₀
  have hz : MorseCancel.standardCircleParametrization z = z₀ :=
    MorseCancel.standardCircleParametrization.apply_symm_apply z₀
  have hδcross : β v = δ z := by
    change β v = Γ (MorseCancel.standardCircleParametrization z)
    rw [hz]
    exact hβcross
  have hδtrans :
    Smale.NativeTransversality.At (𝓡 1) (𝓡 4) 𝓘(ℝ, Smale.RegularLevel.Model E) δ β z v := by
    intro _
    let B : EuclideanSpace ℝ (Fin 4) →L[ℝ] Smale.RegularLevel.Model E :=
      mfderiv (𝓡 4) 𝓘(ℝ, Smale.RegularLevel.Model E) β v
    apply MorseCancel.transverse_comp_standardCircle hΓsmooth B z
    rw [hz]
    exact hΓtrans hβcross
  refine
    ⟨δ, MorseCancel.contMDiff_comp_standardCircle hΓsmooth,
      MorseCancel.injective_comp_standardCircle hΓi,
      MorseCancel.injective_derivative_comp_standardCircle hΓsmooth hΓd, z, v, β, hβ, hδcross,
      hδtrans, hβbasin, ?_, fun w => hΓends (MorseCancel.standardCircleParametrization w)⟩
  intro w
  change
    Filter.Tendsto (fun t => S.flow t (Γ (MorseCancel.standardCircleParametrization w)).val)
        Filter.atTop (𝓝 q.val) ↔
      _
  rw [hforward]
  exact
    ⟨fun hw => MorseCancel.standardCircleParametrization.injective (hw.trans hz.symm), fun hw =>
      hw ▸ hz⟩

private theorem
    MorseCancel.exists_transverse_sheet_of_circle_placement {A B E HA HB H X Y N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [TopologicalSpace HA] {I : ModelWithCorners ℝ A HA}
    [TopologicalSpace X] [ChartedSpace HA X] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace HB] {I' : ModelWithCorners ℝ B HB} [TopologicalSpace Y] [ChartedSpace HB Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    [TopologicalSpace N] [ChartedSpace H N] (P : Diffeomorph J J N N ∞) {γ δ : X → N} {β : Y → N}
    {x : X} {y : Y} (hγ : MDifferentiableAt I J γ x) (hβ : MDifferentiableAt I' J β y)
    (hplace : ∀ z, P (γ z) = δ z) (hcross : β y = δ x)
    (htrans : Smale.NativeTransversality.At I I' J δ β x y) :
    ∃ β' : Y → N,
      MDifferentiableAt I' J β' y ∧
        β' y = γ x ∧ Smale.NativeTransversality.At I I' J γ β' x y ∧ ∀ z, P (β' z) = β z := by
  let β' := P.symm ∘ β
  have hβ' : MDifferentiableAt I' J β' y :=
    (P.symm.contMDiff.mdifferentiableAt (by simp)).comp y hβ
  have hcross' : β' y = γ x := by
    apply P.injective
    change P (P.symm (β y)) = P (γ x)
    rw [P.apply_symm_apply, hcross, hplace]
  have hforward (z : Y) : P (β' z) = β z := P.apply_symm_apply (β z)
  refine ⟨β', hβ', hcross', ?_, hforward⟩
  apply
    (Degree.TransverseGerms.native_transversality_partial_diffeomorph_iff P.toPartialDiffeomorph
        hγ hβ' hcross' (Set.mem_univ _)).mpr
  have hγeq : P.toPartialDiffeomorph ∘ γ = δ := funext hplace
  have hβeq : P.toPartialDiffeomorph ∘ β' = β := funext hforward
  rw [hγeq, hβeq]
  exact htrans

private theorem Degree.DiskShrinking.exists_embedded_disk_isotopy_of_path {D E M : Type*}
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f g : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    (hfi : Set.InjOn f (Metric.closedBall (0 : D) 1))
    (hgi : Set.InjOn g (Metric.closedBall (0 : D) 1))
    (hfd : ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (hgd : ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) g x))
    (n : ℕ) (hn : 0 < n) (hdim : Module.finrank ℝ D + n = Module.finrank ℝ E)
    (hE : 2 ≤ Module.finrank ℝ E) (γ : Path (f 0) (g 0)) :
    ∃ P : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity P ∧
        ∀ x ∈ Metric.closedBall (0 : D) 1, P (f x) = g x := by
  obtain ⟨P, hP, hP0, -⟩ :=
    MorseCancel.exists_isotopic_pointMoving_of_path (J := 𝓘(ℝ, E)) isOpen_univ γ
      (fun _ => Set.mem_univ _)
  have hPf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ (P ∘ f) := P.contMDiff.comp hf
  have hPfi : Set.InjOn (P ∘ f) (Metric.closedBall (0 : D) 1) := by
    intro x hx y hy hh
    exact hfi hx hy (P.injective hh)
  have hPfd :
    ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) (P ∘ f) x) := by
    intro x hx
    rw [mfderiv_comp x (P.contMDiff.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
    have hi : Function.Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) P (f x) : E →L[ℝ] E) :=
      Smale.PartialChart.bijective_mfderiv P.toPartialDiffeomorph (Set.mem_univ _)
    exact hi.1.comp (hfd x hx)
  obtain ⟨Q, hQ, hformula⟩ :=
    exists_embedded_disk_isotopy_of_same_center hPf hg hPfi hgi hPfd hgd n hn hdim hE hP0
  exact ⟨P.trans Q, hP.trans hQ, hformula⟩

private theorem
    Degree.DiskShrinking.exists_embedded_disk_isotopy {D E M : Type*} [NormedAddCommGroup D]
    [InnerProductSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f g : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    (hfi : Set.InjOn f (Metric.closedBall (0 : D) 1))
    (hgi : Set.InjOn g (Metric.closedBall (0 : D) 1))
    (hfd : ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (hgd : ∀ x ∈ Metric.closedBall (0 : D) 1, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) g x))
    (n : ℕ) (hn : 0 < n) (hdim : Module.finrank ℝ D + n = Module.finrank ℝ E)
    (hE : 2 ≤ Module.finrank ℝ E) :
    ∃ P : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity P ∧
        ∀ x ∈ Metric.closedBall (0 : D) 1, P (f x) = g x :=
  exists_embedded_disk_isotopy_of_path hf hg hfi hgi hfd hgd n hn hdim hE
    (Joined.somePath (PathConnectedSpace.joined (f 0) (g 0)))

private theorem MorseCancel.exists_embedded_avoidance_into_level_basin {E M A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [FiniteDimensional ℝ A] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) {d : ℕ}
    (hhigh :
      ∀ p : Smale.ManifoldMorse.criticalPoints E f,
        a ≤ f p → Module.finrank ℝ E - nativeMorseIndex E f p ≤ d)
    (hlow : ∀ p : Smale.ManifoldMorse.criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ d)
    (f₀ : C(A, M)) (hf₀ : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ f₀)
    (hself : 2 * Module.finrank ℝ A < Module.finrank ℝ E)
    (hobstacle : Module.finrank ℝ A + d < Module.finrank ℝ E) {K L C : Set A} (hK : IsCompact K)
    (hL : IsCompact L) (hC : IsClosed C) (hinj : Set.InjOn f₀ K)
    (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) f₀ x))
    (hfixed : ∀ x ∈ L ∩ C, f₀ x ∈ Degree.FlowCancellation.levelBasin S.flow f a) :
    ∃ g : C(A, M),
      ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ g ∧
        f₀.HomotopicRel g C ∧
          Topology.IsClosedEmbedding (fun x : K => g x) ∧
            (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) g x)) ∧
              (∀ x y, g x = g y → f₀ x = f₀ y) ∧
                ∀ x,
                  (f₀ x ∈ Degree.FlowCancellation.levelBasin S.flow f a ∨ x ∈ L) →
                    g x ∈ Degree.FlowCancellation.levelBasin S.flow f a := by
  let _ := S.finite.fintype
  let J := EndpointBasinIndex (E := E) (f := f) a
  let Z := EuclideanSpace ℝ (Fin 0)
  let V := EuclideanSpace ℝ (Fin d)
  let _ : Countable J := endpointBasinIndex_countable S a
  let _ : DiscreteTopology J := inferInstance
  let _ : ChartedSpace Z J := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold 𝓘(ℝ, Z) ∞ J := IsManifold.of_discreteTopology ∞
  obtain ⟨b, hb, hcover⟩ := S.exists_endpoint_obstruction_global_images hf a hhigh hlow
  have hs : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞ (fun p : J × V => b p.1 p.2) :=
    contMDiff_discrete_family b hb
  let B : C(J × V, M) := ⟨fun p => b p.1 p.2, hs.continuous⟩
  have hrange : Set.range B = (Degree.FlowCancellation.levelBasin S.flow f a)ᶜ := by
    rw [levelBasin_compl_eq_endpoint_obstruction S hf hreg, hcover]
    exact range_discrete_family b
  have hclosed : IsClosed (Set.range B) := by
    rw [hrange, levelBasin_compl_eq_endpoint_obstruction S hf hreg]
    exact isClosed_endpoint_obstruction S hf a
  have hdim : Module.finrank ℝ A + Module.finrank ℝ (Z × V) < Module.finrank ℝ E := by
    simpa only [Z, V, Module.finrank_prod, finrank_euclideanSpace_fin, zero_add] using hobstacle
  have hfixed' : ∀ x ∈ L ∩ C, f₀ x ∉ Set.range B := by
    intro x hx
    rw [hrange, Set.mem_compl_iff, Classical.not_not]
    exact hfixed x hx
  obtain ⟨g, hg, hhom, hemb, hder, hnoNew, havoid⟩ :=
    Smale.ManifoldImmersion.exists_embedded_avoidance_on_compact_of_isClosed_range f₀ B hf₀ hs
      hclosed hself hdim hK hL hC hinj hderiv hfixed'
  refine ⟨g, hg, hhom, hemb, hder, hnoNew, ?_⟩
  intro x hx
  have hx' : f₀ x ∉ Set.range B ∨ x ∈ L := by
    simpa only [hrange, Set.mem_compl_iff, Classical.not_not] using hx
  simpa only [hrange, Set.mem_compl_iff, Classical.not_not] using havoid x hx'

private theorem Smale.SphereBoundary.exists_extension_immersive_on_sphere {E G H N : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
    [Fact (Module.finrank ℝ E = n + 1)] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] {f : E → N}
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {γ : Metric.sphere (0 : E) 1 → N}
    (hext : ∀ x : Metric.sphere (0 : E) 1, f x.1 = γ x)
    (hγ : ∀ x, Function.Injective (mfderiv (𝓡 n) J γ x))
    (hdim : n + Module.finrank ℝ E < Module.finrank ℝ G) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        (∀ x : Metric.sphere (0 : E) 1, g x.1 = γ x) ∧
          ∀ x : Metric.sphere (0 : E) 1, Function.Injective (mfderiv 𝓘(ℝ, E) J g x.1) := by
  have hb : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (Subtype.val : Metric.sphere (0 : E) 1 → E) :=
    contMDiff_coe_sphere
  have hzero (x : Metric.sphere (0 : E) 1) : definingFunction x.1 = 0 :=
    (definingFunction_eq_zero_iff x.1).mpr x.property
  have hd :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) + Module.finrank ℝ E < Module.finrank ℝ G := by
    simpa only [finrank_euclideanSpace_fin] using hdim
  obtain ⟨g, hg, hhom, hderiv⟩ :=
    Smale.ManifoldImmersion.exists_compact_boundary_derivative_repair
      (⟨f, hf.continuous⟩ : C(E, N)) hf hb contDiff_definingFunction hzero hd
      (common_kernel_of_immersive_sphere_extension hf hext hγ)
  refine ⟨g, hg, ?_, ?_⟩
  · intro x
    exact (hhom.fst_eq_snd (hzero x)).symm.trans (hext x)
  · intro x
    exact hderiv x.1 ⟨x, rfl⟩

private theorem Smale.exists_embedded_disk_extension_of_smooth_extension {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {f : Hemisphere.Ambient 2 → N}
    (hf : ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) J ∞ f) {γ : Hemisphere.Sphere 1 → N}
    (hext : ∀ x : Hemisphere.Sphere 1, f x.1 = γ x) (hγinj : Function.Injective γ)
    (hγderiv : ∀ x, Function.Injective (mfderiv (𝓡 1) J γ x)) (hdim : 5 ≤ Module.finrank ℝ G) :
    ∃ g : C(Hemisphere.Ambient 2, N),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) J ∞ g ∧
        (∀ x : Hemisphere.Sphere 1, g x.1 = γ x) ∧
          Topology.IsClosedEmbedding (fun x : Hemisphere.Ball 2 => g x.1) ∧
            ∀ x : Hemisphere.Ball 2,
              Function.Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) J g x.1) := by
  let : Fact (Module.finrank ℝ (Hemisphere.Ambient 2) = 1 + 1) :=
    ⟨by simp only [Hemisphere.Ambient, finrank_euclideanSpace_fin]⟩
  have hd : 1 + Module.finrank ℝ (Hemisphere.Ambient 2) < Module.finrank ℝ G := by
    simp only [Hemisphere.Ambient, finrank_euclideanSpace_fin]
    omega
  obtain ⟨f₁, hf₁, hboundary₁, hderiv₁⟩ :=
    SphereBoundary.exists_extension_immersive_on_sphere (n := 1) hf hext hγderiv hd
  let K : Set (Hemisphere.Ambient 2) := Metric.closedBall 0 1
  let C : Set (Hemisphere.Ambient 2) := Metric.sphere 0 1
  have hK : IsCompact K := ProperSpace.isCompact_closedBall 0 1
  have hC : IsClosed C := Metric.isClosed_sphere
  have hfixed : Set.InjOn f₁ (K ∩ C) := by
    intro x hx y hy hxy
    let xs : Hemisphere.Sphere 1 := ⟨x, hx.2⟩
    let ys : Hemisphere.Sphere 1 := ⟨y, hy.2⟩
    have hboundaryeq : γ xs = γ ys := (hboundary₁ xs).symm.trans (hxy.trans (hboundary₁ ys))
    exact congrArg Subtype.val (hγinj hboundaryeq)
  have hderiv : ∀ x ∈ K ∩ C, Function.Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) J f₁ x) :=
    fun x hx => hderiv₁ ⟨x, hx.2⟩
  obtain ⟨g, hg, hhom, hemb, hderivg⟩ :=
    ManifoldImmersion.exists_relative_compact_embedding_twoDimensional f₁ hf₁
      (by simp only [Hemisphere.Ambient, finrank_euclideanSpace_fin]) hdim hK hC hfixed hderiv
  refine ⟨g, hg, ?_, hemb, fun x => hderivg x.1 x.property⟩
  intro x
  exact (hhom.fst_eq_snd x.property).symm.trans (hboundary₁ x)

private def Smale.RadialFilling.direction {n : ℕ} (b : Smale.Hemisphere.Sphere n)
    (v : Smale.Hemisphere.Ambient (n + 1)) : Smale.Hemisphere.Sphere n := by
  classical
    exact
    if hv : v = 0 then b
    else
      ⟨NormedSpace.normalize v, by
        simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hv⟩

private theorem Smale.RadialFilling.direction_coe {n : ℕ} (b : Smale.Hemisphere.Sphere n)
    {v : Smale.Hemisphere.Ambient (n + 1)} (hv : v ≠ 0) :
    (direction b v : Smale.Hemisphere.Ambient (n + 1)) = NormedSpace.normalize v := by
  classical simp only [direction, dite_eq_right hv]

private theorem
    Smale.RadialFilling.direction_of_mem_sphere {n : ℕ} (b v : Smale.Hemisphere.Sphere n) :
    direction b v.1 = v := by
  have hn : ‖v.1‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
  have hv : v.1 ≠ 0 := by intro h; simp [h] at hn
  apply Subtype.ext
  rw [direction_coe b hv, NormedSpace.normalize_eq_self_of_norm_eq_one hn]

private theorem Smale.RadialFilling.contMDiffAt_direction {n : ℕ} (b : Smale.Hemisphere.Sphere n)
    {v : Smale.Hemisphere.Ambient (n + 1)} (hv : v ≠ 0) :
    ContMDiffAt 𝓘(ℝ, Smale.Hemisphere.Ambient (n + 1)) (𝓡 n) ∞ (direction b) v := by
  let V : TopologicalSpace.Opens (Smale.Hemisphere.Ambient (n + 1)) :=
    ⟨{w | w ≠ 0}, isOpen_ne_fun continuous_id continuous_const⟩
  have : Fact (Module.finrank ℝ (Smale.Hemisphere.Ambient (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hnorm :
    ContMDiff 𝓘(ℝ, Smale.Hemisphere.Ambient (n + 1)) 𝓘(ℝ, Smale.Hemisphere.Ambient (n + 1)) ∞
      (fun w : V => NormedSpace.normalize (w : Smale.Hemisphere.Ambient (n + 1))) :=
    NoExotic.contMDiff_normalize contMDiff_subtype_val (fun w => w.2)
  have hmem (w : V) :
    NormedSpace.normalize (w : Smale.Hemisphere.Ambient (n + 1)) ∈
      Metric.sphere (0 : Smale.Hemisphere.Ambient (n + 1)) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize w.2
  have hsphere := hnorm.codRestrict_sphere (n := n) hmem
  have hs :
    ContMDiff 𝓘(ℝ, Smale.Hemisphere.Ambient (n + 1)) (𝓡 n) ∞ (fun w : V => direction b w.1) := by
    apply hsphere.congr
    intro w
    exact Subtype.ext (direction_coe b w.2)
  exact (contMDiffAt_subtype_iff (U := V) (f := direction b) (x := ⟨v, hv⟩)).mp (hs ⟨v, hv⟩)

private def Smale.RadialFilling.radialTime {n : ℕ} (v : Smale.Hemisphere.Ambient (n + 1)) :
    unitInterval :=
  Set.projIcc 0 1 zero_le_one (1 - ‖v‖)

private theorem Smale.RadialFilling.coe_radialTime {n : ℕ} (v : Smale.Hemisphere.Ambient (n + 1)) :
    (radialTime v : ℝ) = Max.max 0 (Min.min 1 (1 - ‖v‖)) :=
  rfl

private theorem
    Smale.RadialFilling.radialTime_le_quarter {n : ℕ} {v : Smale.Hemisphere.Ambient (n + 1)}
    (hv : 3 / 4 ≤ ‖v‖) : (radialTime v : ℝ) ≤ 1 / 4 := by
  rw [coe_radialTime]
  exact max_le (by norm_num) ((min_le_right _ _).trans (by linarith))

private theorem Smale.RadialFilling.three_quarters_le_radialTime {n : ℕ}
    {v : Smale.Hemisphere.Ambient (n + 1)} (hv : ‖v‖ ≤ 1 / 4) : 3 / 4 ≤ (radialTime v : ℝ) := by
  rw [coe_radialTime]
  exact le_max_of_le_right (le_min (by norm_num) (by linarith))

private theorem
    Smale.RadialFilling.contMDiffAt_radialTime {n : ℕ} {v : Smale.Hemisphere.Ambient (n + 1)}
    (hv : 0 < ‖v‖) (hunit : ‖v‖ < 1) :
    ContMDiffAt 𝓘(ℝ, Smale.Hemisphere.Ambient (n + 1)) (𝓡∂ 1) ∞ radialTime v := by
  have : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  have hp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ (Set.projIcc (0 : ℝ) 1 zero_le_one) (Set.Icc 0 1) :=
    contMDiffOn_projIcc
  have hm : 1 - ‖v‖ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hn : Set.Icc (0 : ℝ) 1 ∈ 𝓝 (1 - ‖v‖) := Icc_mem_nhds (by linarith) (by linarith)
  have hproj := (hp _ hm).contMDiffAt hn
  have hnorm : ContDiffAt ℝ ∞ (Norm.norm : Smale.Hemisphere.Ambient (n + 1) → ℝ) v :=
    contDiffAt_norm ℝ (norm_pos_iff.mp hv)
  exact hproj.comp v (contDiffAt_const.sub hnorm).contMDiffAt

private def Smale.RadialFilling.filling {n : ℕ} {M : Type*} [TopologicalSpace M]
    {f : C(Smale.Hemisphere.Sphere n, M)} {c : M} (H : f.Homotopy (ContinuousMap.const _ c))
    (b : Smale.Hemisphere.Sphere n) (v : Smale.Hemisphere.Ambient (n + 1)) : M :=
  H (radialTime v, direction b v)

private theorem Smale.RadialFilling.filling_eq_center {n : ℕ} {M : Type*} [TopologicalSpace M]
    {f : C(Smale.Hemisphere.Sphere n, M)} {c : M} (H : f.Homotopy (ContinuousMap.const _ c))
    (b : Smale.Hemisphere.Sphere n)
    (htop : ∀ t : unitInterval, ∀ x, 3 / 4 ≤ (t : ℝ) → H (t, x) = c)
    {v : Smale.Hemisphere.Ambient (n + 1)} (hv : ‖v‖ ≤ 1 / 4) : filling H b v = c :=
  htop _ _ (three_quarters_le_radialTime hv)

private theorem Smale.RadialFilling.filling_eq_boundary {n : ℕ} {M : Type*} [TopologicalSpace M]
    {f : C(Smale.Hemisphere.Sphere n, M)} {c : M} (H : f.Homotopy (ContinuousMap.const _ c))
    (b : Smale.Hemisphere.Sphere n)
    (hbottom : ∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H (t, x) = f x)
    {v : Smale.Hemisphere.Ambient (n + 1)} (hv : 3 / 4 ≤ ‖v‖) :
    filling H b v = f (direction b v) :=
  hbottom _ _ (radialTime_le_quarter hv)

private theorem Smale.RadialFilling.filling_on_sphere {n : ℕ} {M : Type*} [TopologicalSpace M]
    {f : C(Smale.Hemisphere.Sphere n, M)} {c : M} (H : f.Homotopy (ContinuousMap.const _ c))
    (b : Smale.Hemisphere.Sphere n)
    (hbottom : ∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H (t, x) = f x)
    (v : Smale.Hemisphere.Sphere n) : filling H b v.1 = f v := by
  have hn : ‖v.1‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
  rw [filling_eq_boundary H b hbottom (by rw [hn]; norm_num), direction_of_mem_sphere]

private theorem Smale.RadialFilling.contMDiff_filling {n : ℕ} {G K M : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace K] {J : ModelWithCorners ℝ G K} [TopologicalSpace M]
    [ChartedSpace K M] {f : C(Smale.Hemisphere.Sphere n, M)} {c : M}
    (H : f.Homotopy (ContinuousMap.const _ c)) (b : Smale.Hemisphere.Sphere n)
    (hf : ContMDiff (𝓡 n) J ∞ f) (hH : ContMDiff ((𝓡∂ 1).prod (𝓡 n)) J ∞ H)
    (hbottom : ∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H (t, x) = f x)
    (htop : ∀ t : unitInterval, ∀ x, 3 / 4 ≤ (t : ℝ) → H (t, x) = c) :
    ContMDiff 𝓘(ℝ, Smale.Hemisphere.Ambient (n + 1)) J ∞ (filling H b) := by
  intro v
  by_cases hinner : ‖v‖ < 1 / 4
  · apply (contMDiffAt_const (c := c)).congr_of_eventuallyEq
    have hn : {w : Smale.Hemisphere.Ambient (n + 1) | ‖w‖ < 1 / 4} ∈ 𝓝 v :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds hinner
    filter_upwards [hn] with w hw
    exact filling_eq_center H b htop (le_of_lt hw)
  · by_cases houter : 3 / 4 < ‖v‖
    · have hv : v ≠ 0 := norm_pos_iff.mp (by linarith)
      have hs := (hf (direction b v)).comp v (contMDiffAt_direction b hv)
      apply hs.congr_of_eventuallyEq
      have hn : {w : Smale.Hemisphere.Ambient (n + 1) | 3 / 4 < ‖w‖} ∈ 𝓝 v :=
        (isOpen_lt continuous_const continuous_norm).mem_nhds houter
      filter_upwards [hn] with w hw
      exact filling_eq_boundary H b hbottom (le_of_lt hw)
    · have hv : 0 < ‖v‖ := by linarith [le_of_not_gt hinner]
      have hunit : ‖v‖ < 1 := by linarith [le_of_not_gt houter]
      exact
        (hH (radialTime v, direction b v)).comp v (f := fun w => (radialTime w, direction b w))
          ((contMDiffAt_radialTime hv hunit).prodMk
            (contMDiffAt_direction b (norm_pos_iff.mp hv)))

private theorem Smale.exists_smooth_nullhomotopy_of_homotopySixSphere {E G H X M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X] [CompactSpace X]
    [TopologicalSpace M] [ChartedSpace G M] [IsManifold 𝓘(ℝ, G) ∞ M] (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E < 6) (f : C(X, M)) (hf : ContMDiff I 𝓘(ℝ, G) ∞ f) :
    ∃ c : M,
      ∃ H : f.Homotopy (ContinuousMap.const X c),
        ContMDiff ((𝓡∂ 1).prod I) 𝓘(ℝ, G) ∞ H ∧
          (∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H (t, x) = f x) ∧
            (∀ t : unitInterval, ∀ x, 3 / 4 ≤ (t : ℝ) → H (t, x) = c) := by
  obtain ⟨c, ⟨H⟩⟩ := manifoldMap_nullhomotopic_of_homotopySixSphere (I := I) e hdim f
  obtain ⟨H', hH', hlo, hhi⟩ :=
    ManifoldSmoothing.exists_smooth_homotopy_with_collars hf contMDiff_const H
  exact ⟨c, H', hH', hlo, hhi⟩

private theorem Smale.exists_smooth_disk_extension_of_homotopySixSphere {G M : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace M] [ChartedSpace G M]
    [IsManifold 𝓘(ℝ, G) ∞ M] (e : M ≃ₕ Smale.SixSphere) {n : ℕ} (hn : n < 6)
    (f : C(Hemisphere.Sphere n, M)) (hf : ContMDiff (𝓡 n) 𝓘(ℝ, G) ∞ f) :
    ∃ (c : M) (F : Hemisphere.Ambient (n + 1) → M),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient (n + 1)) 𝓘(ℝ, G) ∞ F ∧
        (∀ v : Hemisphere.Sphere n, F v.1 = f v) ∧ ∀ v, ‖v‖ ≤ 1 / 4 → F v = c := by
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) < 6 := by
    simpa only [finrank_euclideanSpace_fin] using hn
  obtain ⟨c, H, hH, hlo, hhi⟩ := exists_smooth_nullhomotopy_of_homotopySixSphere e hd f hf
  obtain ⟨v, hv⟩ : (Hemisphere.Sphere n).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  let b : Hemisphere.Sphere n := ⟨v, hv⟩
  exact
    ⟨c, RadialFilling.filling H b, RadialFilling.contMDiff_filling H b hf hH hlo hhi,
      RadialFilling.filling_on_sphere H b hlo, fun _ hv =>
      RadialFilling.filling_eq_center H b hhi hv⟩

private theorem Smale.exists_embedded_disk_of_homotopySixSphere {G M : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace M] [ChartedSpace G M]
    [IsManifold 𝓘(ℝ, G) ∞ M] [T2Space M] (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ G = 6) (γ : C(Hemisphere.Sphere 1, M))
    (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, G) ∞ γ) (hγinj : Function.Injective γ)
    (hγderiv : ∀ x, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, G) γ x)) :
    ∃ g : C(Hemisphere.Ambient 2, M),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, G) ∞ g ∧
        (∀ x : Hemisphere.Sphere 1, g x.1 = γ x) ∧
          Topology.IsClosedEmbedding (fun x : Hemisphere.Ball 2 => g x.1) ∧
            ∀ x : Hemisphere.Ball 2,
              Function.Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, G) g x.1) := by
  obtain ⟨-, f, hf, hext, -⟩ :=
    exists_smooth_disk_extension_of_homotopySixSphere e (n := 1) (by decide) γ hγ
  exact exists_embedded_disk_extension_of_smooth_extension hf hext hγinj hγderiv (by omega)

private theorem
    MorseCancel.exists_disk_in_level_basin_of_index_cut {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hhigh : ∀ p : Smale.ManifoldMorse.criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : Smale.ManifoldMorse.criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ : C(Smale.Hemisphere.Sphere 1, M)) (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ γ)
    (hγinj : Function.Injective γ) (hγderiv : ∀ x, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) γ x))
    (hlevel : ∀ z, f (γ z) = a) :
    ∃ g : C(Smale.Hemisphere.Ambient 2, M),
      ContMDiff 𝓘(ℝ, Smale.Hemisphere.Ambient 2) 𝓘(ℝ, E) ∞ g ∧
        (∀ z : Smale.Hemisphere.Sphere 1, g z.val = γ z) ∧
          Topology.IsClosedEmbedding (fun z : Smale.Hemisphere.Ball 2 => g z.val) ∧
            (∀ z : Smale.Hemisphere.Ball 2,
                Function.Injective (mfderiv 𝓘(ℝ, Smale.Hemisphere.Ambient 2) 𝓘(ℝ, E) g z.val)) ∧
              ∀ z : Smale.Hemisphere.Ball 2,
                g z.val ∈ Degree.FlowCancellation.levelBasin S.flow f a := by
  obtain ⟨g₀, hg₀, hboundary, hemb, hderiv⟩ :=
    Smale.exists_embedded_disk_of_homotopySixSphere e hdim γ hγ hγinj hγderiv
  let K : Set (Smale.Hemisphere.Ambient 2) := Metric.closedBall 0 1
  let C : Set (Smale.Hemisphere.Ambient 2) := Metric.sphere 0 1
  have hK : IsCompact K := ProperSpace.isCompact_closedBall _ _
  have hC : IsClosed C := Metric.isClosed_sphere
  have hinj : Set.InjOn g₀ K := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hfixed (z : Smale.Hemisphere.Ambient 2) (hz : z ∈ K ∩ C) :
    g₀ z ∈ Degree.FlowCancellation.levelBasin S.flow f a := by
    refine ⟨0, ?_⟩
    rw [S.flow.map_zero_apply, hboundary ⟨z, hz.2⟩, hlevel]
  have hhigh' (p : Smale.ManifoldMorse.criticalPoints E f) (hp : a ≤ f p) :
    Module.finrank ℝ E - nativeMorseIndex E f p ≤ 3 := by
    have hh := hhigh p hp
    omega
  obtain ⟨g, hg, hhom, hembg, hderg, -, hbasin⟩ :=
    exists_embedded_avoidance_into_level_basin S hf hreg hhigh' hlow g₀ hg₀
      (by simp only [Smale.Hemisphere.Ambient, finrank_euclideanSpace_fin]; omega)
      (by simp only [Smale.Hemisphere.Ambient, finrank_euclideanSpace_fin]; omega) hK hK hC hinj
      (fun z hz => hderiv ⟨z, hz⟩) hfixed
  refine ⟨g, hg, ?_, hembg, fun z => hderg z.val z.property, ?_⟩
  · intro z
    exact (hhom.fst_eq_snd z.property).symm.trans (hboundary z)
  · intro z
    exact hbasin z.val (Or.inr z.property)

private theorem MorseCancel.exists_actual_regular_level_disk_of_index_cut {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hhigh : ∀ p : Smale.ManifoldMorse.criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : Smale.ManifoldMorse.criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ : C(Smale.Hemisphere.Sphere 1, M)) (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ γ)
    (hγinj : Function.Injective γ) (hγderiv : ∀ x, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) γ x))
    (hlevel : ∀ z, f (γ z) = a) :
    ∃ D : C(Smale.Hemisphere.Ball 2, { y : M // f y = a }),
      ∀ z : Smale.Hemisphere.Sphere 1,
        (D ⟨z.val, Metric.sphere_subset_closedBall z.property⟩).val = γ z := by
  obtain ⟨g, hg, hboundary, -, -, hbasin⟩ :=
    exists_disk_in_level_basin_of_index_cut S hf e hdim hreg hhigh hlow γ hγ hγinj hγderiv hlevel
  obtain ⟨v, hv⟩ : (Metric.sphere (0 : Smale.Hemisphere.Ambient 2) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  let z₀ : { y : M // f y = a } := ⟨γ ⟨v, hv⟩, hlevel ⟨v, hv⟩⟩
  let _ := Smale.RegularLevel.chartedSpace hf hreg
  obtain ⟨Φ, hsource, htarget, hformula, -⟩ :=
    Degree.FlowCancellation.exists_native_level_flow_cylinder hf hreg S.smooth S.flow S.integral
      (fun y hy => S.descent y (hreg y hy)) z₀
  have hcont : Continuous (fun z : Smale.Hemisphere.Ball 2 => Φ.symm (g z.val)) :=
    Φ.contMDiffOn_invFun.continuousOn.comp_continuous (g.continuous.comp continuous_subtype_val)
      (fun z => htarget.symm ▸ hbasin z)
  let D : C(Smale.Hemisphere.Ball 2, { y : M // f y = a }) :=
    ⟨fun z => (Φ.symm (g z.val)).1, continuous_fst.comp hcont⟩
  refine ⟨D, ?_⟩
  intro z
  let p : { y : M // f y = a } := ⟨γ z, hlevel z⟩
  have hp : (p, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; trivial
  have hφ : Φ (p, 0) = γ z := by rw [hformula, S.flow.map_zero_apply]
  have hi : Φ.symm (Φ (p, 0)) = (p, 0) := Φ.left_inv' hp
  rw [hφ] at hi
  change (Φ.symm (g z.val)).1.val = γ z
  rw [hboundary z]
  exact congrArg (fun q : { y : M // f y = a } × ℝ => q.1.val) hi

private theorem MorseCancel.circle_nullhomotopy_of_disk {N : Type*} [TopologicalSpace N]
    (γ : C(Smale.Hemisphere.Sphere 1, N)) (D : C(Smale.Hemisphere.Ball 2, N))
    (hboundary :
      ∀ z : Smale.Hemisphere.Sphere 1,
        D ⟨z.val, Metric.sphere_subset_closedBall z.property⟩ = γ z) :
    ∃ c : N, γ.Homotopic (ContinuousMap.const _ c) := by
  let c := D ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  let H : γ.Homotopy (ContinuousMap.const _ c) :=
    { toFun := fun p => D (Smale.DiskCone.point p)
      continuous_toFun := D.continuous.comp Smale.DiskCone.continuous_point
      map_zero_left := by
        intro z
        have he :
          Smale.DiskCone.point (0, z) =
            (⟨z.val, Metric.sphere_subset_closedBall z.property⟩ : Smale.Hemisphere.Ball 2) := by
          apply Subtype.ext
          simp [Smale.DiskCone.point]
        rw [he]
        exact hboundary z
      map_one_left := by
        intro z
        have he :
          Smale.DiskCone.point (1, z) =
            (⟨0, Metric.mem_closedBall_self zero_le_one⟩ : Smale.Hemisphere.Ball 2) := by
          apply Subtype.ext
          simp [Smale.DiskCone.point]
        exact congrArg D he }
  exact ⟨c, ⟨H⟩⟩

private theorem MorseCancel.exists_smooth_embedded_disk_of_continuous_filling {G N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace N]
    [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N] [T2Space N] (γ : C(Smale.Hemisphere.Sphere 1, N))
    (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, G) ∞ γ) (hγinj : Function.Injective γ)
    (hγderiv : ∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, G) γ z))
    (hdim : 5 ≤ Module.finrank ℝ G) (D : C(Smale.Hemisphere.Ball 2, N))
    (hboundary :
      ∀ z : Smale.Hemisphere.Sphere 1,
        D ⟨z.val, Metric.sphere_subset_closedBall z.property⟩ = γ z) :
    ∃ g : C(Smale.Hemisphere.Ambient 2, N),
      ContMDiff 𝓘(ℝ, Smale.Hemisphere.Ambient 2) 𝓘(ℝ, G) ∞ g ∧
        (∀ z : Smale.Hemisphere.Sphere 1, g z.val = γ z) ∧
          Topology.IsClosedEmbedding (fun z : Smale.Hemisphere.Ball 2 => g z.val) ∧
            ∀ z : Smale.Hemisphere.Ball 2,
              Function.Injective (mfderiv 𝓘(ℝ, Smale.Hemisphere.Ambient 2) 𝓘(ℝ, G) g z.val) := by
  obtain ⟨c, ⟨H⟩⟩ := circle_nullhomotopy_of_disk γ D hboundary
  obtain ⟨H', hH', hlo, hhi⟩ :=
    Smale.ManifoldSmoothing.exists_smooth_homotopy_with_collars hγ contMDiff_const H
  obtain ⟨v, hv⟩ : (Metric.sphere (0 : Smale.Hemisphere.Ambient 2) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  let b : Smale.Hemisphere.Sphere 1 := ⟨v, hv⟩
  have hsmooth := Smale.RadialFilling.contMDiff_filling H' b hγ hH' hlo hhi
  have hext := Smale.RadialFilling.filling_on_sphere H' b hlo
  exact Smale.exists_embedded_disk_extension_of_smooth_extension hsmooth hext hγinj hγderiv hdim

private theorem MorseCancel.exists_embedded_regular_level_disk_of_index_cut {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hhigh : ∀ p : Smale.ManifoldMorse.criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : Smale.ManifoldMorse.criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ : C(Smale.Hemisphere.Sphere 1, M)) (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ γ)
    (hγinj : Function.Injective γ) (hγderiv : ∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) γ z))
    (hlevel : ∀ z, f (γ z) = a) :
    let _ := Smale.RegularLevel.chartedSpace hf hreg
    ∃ g : C(Smale.Hemisphere.Ambient 2, { y : M // f y = a }),
      ContMDiff 𝓘(ℝ, Smale.Hemisphere.Ambient 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g ∧
        (∀ z : Smale.Hemisphere.Sphere 1, (g z.val).val = γ z) ∧
          Topology.IsClosedEmbedding (fun z : Smale.Hemisphere.Ball 2 => g z.val) ∧
            ∀ z : Smale.Hemisphere.Ball 2,
              Function.Injective
                (mfderiv 𝓘(ℝ, Smale.Hemisphere.Ambient 2) 𝓘(ℝ, Smale.RegularLevel.Model E) g
                  z.val) := by
  let _ := Smale.RegularLevel.chartedSpace hf hreg
  let _ := Smale.RegularLevel.isManifold hf hreg
  obtain ⟨D, hD⟩ :=
    exists_actual_regular_level_disk_of_index_cut S hf e hdim hreg hhigh hlow γ hγ hγinj hγderiv
      hlevel
  let γL : C(Smale.Hemisphere.Sphere 1, { y : M // f y = a }) :=
    ⟨fun z => ⟨γ z, hlevel z⟩, γ.continuous.subtype_mk _⟩
  have hγL : ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γL :=
    (Smale.RegularLevel.contMDiff_iff_inclusion hf hreg (𝓡 1) γL).mpr hγ
  have hinj : Function.Injective γL := fun x y hxy => hγinj (congrArg Subtype.val hxy)
  have hderiv (z : Smale.Hemisphere.Sphere 1) :
    Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) γL z) :=
    Smale.RegularLevel.injective_mfderiv_of_inclusion hf hreg (𝓡 1) γL z hγ.contMDiffAt
      (hγderiv z)
  have hdimL : 5 ≤ Module.finrank ℝ (Smale.RegularLevel.Model E) := by
    simp only [Smale.RegularLevel.Model, finrank_euclideanSpace_fin, hdim]
    norm_num
  have hboundary (z : Smale.Hemisphere.Sphere 1) :
    D ⟨z.val, Metric.sphere_subset_closedBall z.property⟩ = γL z := Subtype.ext (hD z)
  obtain ⟨g, hg, hboundaryg, hemb, hderivg⟩ :=
    exists_smooth_embedded_disk_of_continuous_filling γL hγL hinj hderiv hdimL D hboundary
  exact ⟨g, hg, fun z => congrArg Subtype.val (hboundaryg z), hemb, hderivg⟩

private theorem
    MorseCancel.exists_native_middle_level_circle_disk {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hhigh : ∀ p : Smale.ManifoldMorse.criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : Smale.ManifoldMorse.criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ : C(Smale.Hemisphere.Sphere 1, { y : M // f y = a })) :
    let _ := Smale.RegularLevel.chartedSpace hf hreg
    ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) γ z)) →
          ∃ g : C(Smale.Hemisphere.Ambient 2, { y : M // f y = a }),
            ContMDiff 𝓘(ℝ, Smale.Hemisphere.Ambient 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g ∧
              (∀ z : Smale.Hemisphere.Sphere 1, g z.val = γ z) ∧
                Topology.IsClosedEmbedding (fun z : Smale.Hemisphere.Ball 2 => g z.val) ∧
                  (∀ z : Smale.Hemisphere.Ball 2,
                    Function.Injective
                      (mfderiv 𝓘(ℝ, Smale.Hemisphere.Ambient 2) 𝓘(ℝ, Smale.RegularLevel.Model E) g
                        z.val)) := by
  let _ := Smale.RegularLevel.chartedSpace hf hreg
  let _ := Smale.RegularLevel.isManifold hf hreg
  change
    ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) γ z)) → _
  intro hγ hγi hγd
  let γM : C(Smale.Hemisphere.Sphere 1, M) :=
    ⟨Subtype.val ∘ γ, continuous_subtype_val.comp γ.continuous⟩
  have hγM : ContMDiff (𝓡 1) 𝓘(ℝ, E) ∞ γM :=
    (Smale.RegularLevel.contMDiff_inclusion hf hreg).comp hγ
  have hγMi : Function.Injective γM := Subtype.val_injective.comp hγi
  have hγMd : ∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) γM z) := by
    intro z
    change Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (Subtype.val ∘ γ) z)
    rw [mfderiv_comp z
        ((Smale.RegularLevel.contMDiff_inclusion hf hreg).mdifferentiableAt (by simp))
        (hγ.mdifferentiableAt (by simp))]
    exact (Smale.RegularLevel.injective_mfderiv_inclusion hf hreg (γ z)).comp (hγd z)
  obtain ⟨g, hg, hb, hemb, hgd⟩ :=
    exists_embedded_regular_level_disk_of_index_cut S hf e hdim hreg hhigh hlow γM hγM hγMi hγMd
      (fun z => (γ z).property)
  exact ⟨g, hg, fun z => Subtype.ext (hb z), hemb, hgd⟩

private theorem
    MorseCancel.exists_native_middle_level_circle_isotopy {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} [PathConnectedSpace M]
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (e : M ≃ₕ Smale.SixSphere)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hhigh : ∀ p : Smale.ManifoldMorse.criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : Smale.ManifoldMorse.criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (γ δ : C(Smale.Hemisphere.Sphere 1, { y : M // f y = a })) :
    let _ := Smale.RegularLevel.chartedSpace hf hreg
    ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) γ z)) →
          ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ δ →
            Function.Injective δ →
              (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) δ z)) →
                ∃ P :
                  Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
                    { y : M // f y = a } { y : M // f y = a } ∞,
                  Smale.SupportedDiffeomorph.IsotopicToIdentity P ∧ ∀ z, P (γ z) = δ z := by
  let _ := Smale.RegularLevel.chartedSpace hf hreg
  let _ := Smale.RegularLevel.isManifold hf hreg
  let _ : CompactSpace { y : M // f y = a } :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  change
    ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ →
      Function.Injective γ →
        (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) γ z)) →
          ContMDiff (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ δ →
            Function.Injective δ →
              (∀ z, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, Smale.RegularLevel.Model E) δ z)) → _
  intro hγ hγi hγd hδ hδi hδd
  obtain ⟨g, hg, hgb, hge, hgd⟩ :=
    exists_native_middle_level_circle_disk S hf e hdim hreg hhigh hlow γ hγ hγi hγd
  obtain ⟨h, hh, hhb, hhe, hhd⟩ :=
    exists_native_middle_level_circle_disk S hf e hdim hreg hhigh hlow δ hδ hδi hδd
  let _ := S.pathConnectedSpace_middle_level hf hdim hreg hhigh hlow (g 0)
  have hgi : Set.InjOn g (Metric.closedBall (0 : Smale.Hemisphere.Ambient 2) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hge.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hhi : Set.InjOn h (Metric.closedBall (0 : Smale.Hemisphere.Ambient 2) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hhe.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hcodim :
    Module.finrank ℝ (Smale.Hemisphere.Ambient 2) + 3 =
      Module.finrank ℝ (Smale.RegularLevel.Model E) := by
    simp only [Smale.Hemisphere.Ambient, Smale.RegularLevel.Model, finrank_euclideanSpace_fin,
      hdim]
  have hmodel : 2 ≤ Module.finrank ℝ (Smale.RegularLevel.Model E) := by
    simp only [Smale.RegularLevel.Model, finrank_euclideanSpace_fin, hdim]
    omega
  obtain ⟨P, hP, hformula⟩ :=
    Degree.DiskShrinking.exists_embedded_disk_isotopy hg hh hgi hhi (fun x hx => hgd ⟨x, hx⟩)
      (fun x hx => hhd ⟨x, hx⟩) 3 (by omega) hcodim hmodel
  refine ⟨P, hP, ?_⟩
  intro z
  rw [← hgb z, hformula z.val (Metric.sphere_subset_closedBall z.property), hhb z]

private def
    MorseCancel.cancelled {m : ℕ} (σ : Fin m → ℝ) (φ : Model m → ℝ) (t : ℝ) (p : Model m) : ℝ :=
  cubic σ (-t) p + 2 * t * φ p * p.1

private theorem MorseCancel.contDiff_cancelled_family {m : ℕ} (σ : Fin m → ℝ) {φ : Model m → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (Function.uncurry (cancelled σ φ)) := by
  exact
    ((contDiff_cubic_family σ).comp (contDiff_fst.neg.prodMk contDiff_snd)).add
      (((contDiff_const.mul contDiff_fst).mul (hφ.comp contDiff_snd)).mul contDiff_snd.fst)

private theorem MorseCancel.cancelled_zero {m : ℕ} (σ : Fin m → ℝ) (φ : Model m → ℝ) :
    cancelled σ φ 0 = cubic σ 0 := by
  funext p
  simp [cancelled]

private theorem MorseCancel.cancelled_germ_plateau {m : ℕ} (σ : Fin m → ℝ) {φ : Model m → ℝ}
    {U : Set (Model m)} (hU : IsOpen U) (hφU : Set.EqOn φ (fun _ => 1) U) (t : ℝ) {p : Model m}
    (hp : p ∈ U) : cancelled σ φ t =ᶠ[𝓝 p] cubic σ t := by
  filter_upwards [hU.mem_nhds hp] with q hq
  simp [cancelled, cubic, hφU hq]
  ring

private theorem
    MorseCancel.cancelled_eq_off_support {m : ℕ} (σ : Fin m → ℝ) (φ : Model m → ℝ) (t : ℝ)
    {p : Model m} (hp : p ∉ tsupport φ) : cancelled σ φ t p = cubic σ (-t) p := by
  simp [cancelled, image_eq_zero_of_notMem_tsupport hp]

private theorem
    MorseCancel.cancelled_germ_off_support {m : ℕ} (σ : Fin m → ℝ) (φ : Model m → ℝ) (t : ℝ)
    {p : Model m} (hp : p ∉ tsupport φ) : cancelled σ φ t =ᶠ[𝓝 p] cubic σ (-t) := by
  filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hp] with q hq
  exact cancelled_eq_off_support σ φ t hq

private theorem MorseCancel.exists_exact_cubic_birth {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    {φ : Model m → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) {U : Set (Model m)}
    (hU : IsOpen U) (h0 : (0 : Model m) ∈ U) (hφU : Set.EqOn φ (fun _ => 1) U) :
    ∃ a : ℝ,
      0 < a ∧
        (a, (0 : Fin m → ℝ)) ∈ U ∧
          (-a, (0 : Fin m → ℝ)) ∈ U ∧
            ∃ g : Model m → ℝ,
              ContDiff ℝ ∞ g ∧
                (∀ p, fderiv ℝ g p = 0 ↔ p = (a, 0) ∨ p = (-a, 0)) ∧
                  (∀ p ∈ U, g =ᶠ[𝓝 p] cubic σ (-(a ^ 2))) ∧
                    ∀ p, p ∉ tsupport φ → g =ᶠ[𝓝 p] cubic σ (a ^ 2) := by
  let K := tsupport φ \ U
  have hK : IsCompact K := hc.diff hU
  have hD :=
    (Smale.MorsePerturbation.contDiff_spatialDerivative
        (contDiff_cancelled_family σ hφ)).continuous
  have hO : IsOpen {t : ℝ | ∀ p ∈ K, fderiv ℝ (cancelled σ φ t) p ≠ 0} :=
    Smale.MorsePerturbation.isOpen_forall_mem_compact hK
      (isClosed_eq hD continuous_const).isOpen_compl
  have hO0 : (0 : ℝ) ∈ {t : ℝ | ∀ p ∈ K, fderiv ℝ (cancelled σ φ t) p ≠ 0} := by
    intro p hp hcrit
    rw [cancelled_zero] at hcrit
    exact hp.2 ((cubic_zero_unique_critical σ hσ p).mp hcrit ▸ h0)
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hO0)
  obtain ⟨r, hr, hrball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  obtain ⟨a, ha, har⟩ := exists_between (lt_min hr (lt_min zero_lt_one hδ))
  have ha1 : a < 1 := (lt_min_iff.mp (lt_min_iff.mp har).2).1
  have haδ : a < δ := (lt_min_iff.mp (lt_min_iff.mp har).2).2
  have haa : a ^ 2 < δ := by nlinarith
  have htrans : ∀ p ∈ K, fderiv ℝ (cancelled σ φ (-(a ^ 2))) p ≠ 0 :=
    hδball (by simpa [Real.dist_eq, abs_of_nonneg (sq_nonneg a)] using haa)
  have hp : (a, (0 : Fin m → ℝ)) ∈ U := by
    apply hrball
    simpa [mem_ball_zero_iff, abs_of_pos ha] using And.intro (lt_min_iff.mp har).1 hr
  have hq : (-a, (0 : Fin m → ℝ)) ∈ U := by
    apply hrball
    simpa [mem_ball_zero_iff, abs_of_pos ha] using And.intro (lt_min_iff.mp har).1 hr
  refine
    ⟨a, ha, hp, hq, cancelled σ φ (-(a ^ 2)),
      (contDiff_cancelled_family σ hφ).comp (contDiff_const.prodMk contDiff_id), ?_,
      (fun p hpU => cancelled_germ_plateau σ hU hφU _ hpU), ?_⟩
  · intro p
    by_cases hpU : p ∈ U
    · rw [(cancelled_germ_plateau σ hU hφU (-(a ^ 2)) hpU).fderiv_eq]
      exact negative_parameter_critical_iff σ hσ a p
    · have hreg : fderiv ℝ (cancelled σ φ (-(a ^ 2))) p ≠ 0 := by
        by_cases hpS : p ∈ tsupport φ
        · exact htrans p ⟨hpS, hpU⟩
        · rw [(cancelled_germ_off_support σ φ (-(a ^ 2)) hpS).fderiv_eq, neg_neg]
          exact positive_parameter_no_critical σ hσ (sq_pos_of_pos ha) p
      constructor
      · exact fun h => False.elim (hreg h)
      · rintro (rfl | rfl)
        · exact False.elim (hpU hp)
        · exact False.elim (hpU hq)
  · intro p hpS
    simpa only [neg_neg] using cancelled_germ_off_support σ φ (-(a ^ 2)) hpS

end Mathoverflow1973

end
