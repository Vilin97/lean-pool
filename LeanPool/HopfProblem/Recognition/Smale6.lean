/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Recognition.Degree2
public import LeanPool.HopfProblem.PeriodFamily.HolomorphicPeriodMap2
import all LeanPool.HopfProblem.Recognition.Smale1
import all LeanPool.HopfProblem.Recognition.Smale2
import all LeanPool.HopfProblem.Recognition.Smale3
import all LeanPool.HopfProblem.Recognition.Smale4
import all LeanPool.HopfProblem.Recognition.Smale5
import all LeanPool.HopfProblem.Recognition.Degree1
import all LeanPool.HopfProblem.Recognition.Degree2
import all LeanPool.HopfProblem.PeriodFamily.HolomorphicPeriodMap2

/-!
# Hopf problem: recognition · smale 6

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

private theorem MorseCancel.exists_regular_cubic_chart_of_native_vertical_field {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {m : ℕ}
    [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞)
    {U : Set (Fin m → ℝ)} (hsource : Φ.source = U ×ˢ Set.univ) (h0 : (0 : Fin m → ℝ) ∈ U)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel :
      ∀ y ∈ Φ.target,
        V y =
          Smale.FlowConstruction.partialChartField Φ.symm (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V) :
    ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      Ψ.target = Φ.target ∧
        Set.Ioo (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Ψ.source ∧
          (∀ s, Ψ (s, 0) = F (cubicAxisClock a s) (Φ (0, 0))) ∧
            (∀ x ∈ Ψ.target, V x = nativeCubicDescent σ Ψ (-(a ^ 2)) x) ∧
              Ψ.source ⊆ Set.Ioo (-a) a ×ˢ Set.univ ∧ ∀ p, Ψ (cubicFlowCylinder σ a p) = Φ p := by
  apply exists_native_regular_cubic_field_chart σ ha Φ hsource h0 V F hF (fun z => Φ (z, 0))
  intro p hp
  have hz : p.1 ∈ U := by rw [hsource] at hp; exact hp.1
  simpa only [zero_add] using
    (Degree.FlowSuspension.native_vertical_cylinder_flow Φ hsource hV hmodel F hF p.1 hz 0
        p.2).symm

private def Degree.FieldChartGluing.threeChartMap {Z M : Type*} (f₀ fₘ f₁ : (ℝ × Z) → M) (a b : ℝ)
    (p : ℝ × Z) : M :=
  if p.1 ≤ a then f₀ p else if b ≤ p.1 then f₁ p else fₘ p

private theorem Degree.FieldChartGluing.threeChartMap_left_germ {Z M : Type*} [TopologicalSpace Z]
     (f₀ fₘ f₁ : (ℝ × Z) → M) {a b : ℝ} {p : ℝ × Z} (hp : p.1 < a) :
    threeChartMap f₀ fₘ f₁ a b =ᶠ[𝓝 p] f₀ := by
  filter_upwards [continuousAt_fst.eventually (eventually_lt_nhds hp)] with q hq
  simp only [threeChartMap, ite_eq_left hq.le]

private theorem Degree.FieldChartGluing.threeChartMap_middle_germ {Z M : Type*} [TopologicalSpace Z]
     (f₀ fₘ f₁ : (ℝ × Z) → M) {a b : ℝ} {p : ℝ × Z} (ha : a < p.1) (hb : p.1 < b) :
    threeChartMap f₀ fₘ f₁ a b =ᶠ[𝓝 p] fₘ := by
  filter_upwards [continuousAt_fst.eventually (eventually_gt_nhds ha),
    continuousAt_fst.eventually (eventually_lt_nhds hb)] with q hqa hqb
  simp only [threeChartMap, ite_eq_right (not_le_of_gt hqa), ite_eq_right (not_le_of_gt hqb)]

private theorem Degree.FieldChartGluing.threeChartMap_right_germ {Z M : Type*} [TopologicalSpace Z]
     (f₀ fₘ f₁ : (ℝ × Z) → M) {a b : ℝ} (hab : a < b) {p : ℝ × Z} (hp : b < p.1) :
    threeChartMap f₀ fₘ f₁ a b =ᶠ[𝓝 p] f₁ := by
  filter_upwards [continuousAt_fst.eventually (eventually_gt_nhds hp)] with q hq
  simp only [threeChartMap, ite_eq_right (not_le_of_gt (hab.trans hq)), ite_eq_left hq.le]

private theorem
    Degree.FieldChartGluing.threeChartMap_left_closed_germ {Z M : Type*} [TopologicalSpace Z]
    [Zero Z] (f₀ fₘ f₁ : (ℝ × Z) → M) {a b : ℝ} (hab : a < b) (heq : f₀ =ᶠ[𝓝 (a, (0 : Z))] fₘ)
    {s : ℝ} (hs : s ≤ a) : threeChartMap f₀ fₘ f₁ a b =ᶠ[𝓝 (s, (0 : Z))] f₀ := by
  rcases hs.lt_or_eq with hs | hs
  · exact threeChartMap_left_germ f₀ fₘ f₁ hs
  · subst s
    filter_upwards [heq, continuousAt_fst.eventually (eventually_lt_nhds hab)] with p hp hpb
    by_cases hpa : p.1 ≤ a
    · simp only [threeChartMap, ite_eq_left hpa]
    · simp only [threeChartMap, ite_eq_right hpa, ite_eq_right (not_le_of_gt hpb)]
      exact hp.symm

private theorem
    Degree.FieldChartGluing.threeChartMap_right_closed_germ {Z M : Type*} [TopologicalSpace Z]
    [Zero Z] (f₀ fₘ f₁ : (ℝ × Z) → M) {a b : ℝ} (hab : a < b) (heq : f₁ =ᶠ[𝓝 (b, (0 : Z))] fₘ)
    {s : ℝ} (hs : b ≤ s) : threeChartMap f₀ fₘ f₁ a b =ᶠ[𝓝 (s, (0 : Z))] f₁ := by
  rcases hs.eq_or_lt with hs | hs
  · subst s
    filter_upwards [heq, continuousAt_fst.eventually (eventually_gt_nhds hab)] with p hp hpa
    by_cases hpb : b ≤ p.1
    · simp only [threeChartMap, ite_eq_right (not_le_of_gt hpa), ite_eq_left hpb]
    · simp only [threeChartMap, ite_eq_right (not_le_of_gt hpa), ite_eq_right hpb]
      exact hp.symm
  · exact threeChartMap_right_germ f₀ fₘ f₁ hab hs

private theorem Degree.FieldChartGluing.exists_glued_three_native_field_charts {Z E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    (Φ₀ Φₘ Φ₁ : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞) (W : (ℝ × Z) → ℝ × Z)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hfield₀ : ∀ y ∈ Φ₀.target, V y = Smale.FlowConstruction.partialChartField Φ₀.symm W y)
    (hfieldₘ : ∀ y ∈ Φₘ.target, V y = Smale.FlowConstruction.partialChartField Φₘ.symm W y)
    (hfield₁ : ∀ y ∈ Φ₁.target, V y = Smale.FlowConstruction.partialChartField Φ₁.symm W y)
    {l a b r : ℝ} (hla : l ≤ a) (hab : a < b) (hbr : b ≤ r)
    (hsource₀ : ∀ s ∈ Set.Icc l a, (s, (0 : Z)) ∈ Φ₀.source)
    (hsourceₘ : ∀ s ∈ Set.Ioo a b, (s, (0 : Z)) ∈ Φₘ.source)
    (hsource₁ : ∀ s ∈ Set.Icc b r, (s, (0 : Z)) ∈ Φ₁.source)
    (hgerm₀ : (Φ₀ : (ℝ × Z) → M) =ᶠ[𝓝 (a, (0 : Z))] Φₘ)
    (hgerm₁ : (Φ₁ : (ℝ × Z) → M) =ᶠ[𝓝 (b, (0 : Z))] Φₘ) (γ : ℝ → M)
    (hinj : Set.InjOn γ (Set.Icc l r)) (haxis₀ : ∀ s ∈ Set.Icc l a, Φ₀ (s, 0) = γ s)
    (haxisₘ : ∀ s ∈ Set.Ioo a b, Φₘ (s, 0) = γ s) (haxis₁ : ∀ s ∈ Set.Icc b r, Φ₁ (s, 0) = γ s) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞,
      Set.Icc l r ×ˢ {(0 : Z)} ⊆ Φ.source ∧
        (∀ s ∈ Set.Icc l r, Φ (s, 0) = γ s) ∧
          (∀ y ∈ Φ.target, V y = Smale.FlowConstruction.partialChartField Φ.symm W y) ∧
            ((Φ : (ℝ × Z) → M) =ᶠ[𝓝 (l, (0 : Z))] Φ₀) ∧
              ((Φ : (ℝ × Z) → M) =ᶠ[𝓝 (r, (0 : Z))] Φ₁) := by
  let f := threeChartMap Φ₀ Φₘ Φ₁ a b
  have haxis (s : ℝ) (hs : s ∈ Set.Icc l r) : f (s, 0) = γ s := by
    by_cases hsa : s ≤ a
    · exact
        (threeChartMap_left_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₀ hsa).eq_of_nhds.trans
          (haxis₀ s ⟨hs.1, hsa⟩)
    · by_cases hbs : b ≤ s
      · exact
          (threeChartMap_right_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₁ hbs).eq_of_nhds.trans
            (haxis₁ s ⟨hbs, hs.2⟩)
      · exact
          (threeChartMap_middle_germ Φ₀ Φₘ Φ₁ (lt_of_not_ge hsa)
                (lt_of_not_ge hbs)).eq_of_nhds.trans
            (haxisₘ s ⟨lt_of_not_ge hsa, lt_of_not_ge hbs⟩)
  have hfinj : Set.InjOn f (Set.Icc l r ×ˢ {(0 : Z)}) := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩ ⟨t, w⟩ ⟨ht, hw⟩ heq
    have hz0 : z = 0 := hz
    have hw0 : w = 0 := hw
    subst z
    subst w
    rw [haxis s hs, haxis t ht] at heq
    exact congrArg (fun s : ℝ => (s, (0 : Z))) (hinj hs ht heq)
  have hlocal :
    ∀ p ∈ Set.Icc l r ×ˢ {(0 : Z)},
      ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞,
        p ∈ Ψ.source ∧
          f =ᶠ[𝓝 p] Ψ ∧
            ∀ y ∈ Ψ.target, V y = Smale.FlowConstruction.partialChartField Ψ.symm W y := by
    rintro ⟨s, z⟩ ⟨hs, hz⟩
    have hz0 : z = 0 := hz
    subst z
    by_cases hsa : s ≤ a
    · exact
        ⟨Φ₀, hsource₀ s ⟨hs.1, hsa⟩, threeChartMap_left_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₀ hsa,
          hfield₀⟩
    · by_cases hbs : b ≤ s
      · exact
          ⟨Φ₁, hsource₁ s ⟨hbs, hs.2⟩, threeChartMap_right_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₁ hbs,
            hfield₁⟩
      · exact
          ⟨Φₘ, hsourceₘ s ⟨lt_of_not_ge hsa, lt_of_not_ge hbs⟩,
            threeChartMap_middle_germ Φ₀ Φₘ Φ₁ (lt_of_not_ge hsa) (lt_of_not_ge hbs), hfieldₘ⟩
  obtain ⟨Φ, hsource, hmap, hfield⟩ :=
    exists_native_field_chart_near_compact f W V
      (CompactIccSpace.isCompact_Icc.prod isCompact_singleton) hfinj hlocal
  refine ⟨Φ, hsource, fun s hs => (hmap (s, 0)).trans (haxis s hs), hfield, ?_, ?_⟩
  · filter_upwards [threeChartMap_left_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₀ hla] with p hp
    exact (hmap p).trans hp
  · filter_upwards [threeChartMap_right_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₁ hbr] with p hp
    exact (hmap p).trans hp

private theorem Degree.FieldChartGluing.injective_closed_axis_of_regular_chart {Z E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞) {l r : ℝ} (γ : ℝ → M)
    (hsource : ∀ s ∈ Set.Ioo l r, (s, (0 : Z)) ∈ Φ.source)
    (hregular : ∀ s ∈ Set.Ioo l r, γ s = Φ (s, 0)) (hleft : γ l ∉ Φ.target)
    (hright : γ r ∉ Φ.target) (hne : γ l ≠ γ r) : Set.InjOn γ (Set.Icc l r) := by
  have htarget (s : ℝ) (hs : s ∈ Set.Ioo l r) : γ s ∈ Φ.target := by
    rw [hregular s hs]
    exact Φ.map_source' (hsource s hs)
  have hleftOnly (s : ℝ) (hs : s ∈ Set.Icc l r) (heq : γ s = γ l) : s = l := by
    by_cases hsl : s = l
    · exact hsl
    by_cases hsr : s = r
    · subst s
      exact (hne heq.symm).elim
    have hi : s ∈ Set.Ioo l r := ⟨lt_of_le_of_ne hs.1 (Ne.symm hsl), lt_of_le_of_ne hs.2 hsr⟩
    exact (hleft (heq ▸ htarget s hi)).elim
  have hrightOnly (s : ℝ) (hs : s ∈ Set.Icc l r) (heq : γ s = γ r) : s = r := by
    by_cases hsr : s = r
    · exact hsr
    by_cases hsl : s = l
    · subst s
      exact (hne heq).elim
    have hi : s ∈ Set.Ioo l r := ⟨lt_of_le_of_ne hs.1 (Ne.symm hsl), lt_of_le_of_ne hs.2 hsr⟩
    exact (hright (heq ▸ htarget s hi)).elim
  intro s hs t ht heq
  by_cases hsl : s = l
  · subst s
    exact (hleftOnly t ht heq.symm).symm
  by_cases hsr : s = r
  · subst s
    exact (hrightOnly t ht heq.symm).symm
  by_cases htl : t = l
  · subst t
    exact hleftOnly s hs heq
  by_cases htr : t = r
  · subst t
    exact hrightOnly s hs heq
  have hs' : s ∈ Set.Ioo l r := ⟨lt_of_le_of_ne hs.1 (Ne.symm hsl), lt_of_le_of_ne hs.2 hsr⟩
  have ht' : t ∈ Set.Ioo l r := ⟨lt_of_le_of_ne ht.1 (Ne.symm htl), lt_of_le_of_ne ht.2 htr⟩
  rw [hregular s hs', hregular t ht'] at heq
  exact congrArg Prod.fst (Φ.toOpenPartialHomeomorph.injOn (hsource s hs') (hsource t ht') heq)

private theorem Degree.FieldChartGluing.exists_closed_axis_native_field_chart {Z E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    (Φ₀ Φₘ Φ₁ : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞) (W : (ℝ × Z) → ℝ × Z)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hfield₀ : ∀ y ∈ Φ₀.target, V y = Smale.FlowConstruction.partialChartField Φ₀.symm W y)
    (hfieldₘ : ∀ y ∈ Φₘ.target, V y = Smale.FlowConstruction.partialChartField Φₘ.symm W y)
    (hfield₁ : ∀ y ∈ Φ₁.target, V y = Smale.FlowConstruction.partialChartField Φ₁.symm W y)
    {l a b r : ℝ} (hla : l < a) (hab : a < b) (hbr : b < r)
    (hsource₀ : ∀ s ∈ Set.Icc l a, (s, (0 : Z)) ∈ Φ₀.source)
    (hsourceₘ : ∀ s ∈ Set.Ioo l r, (s, (0 : Z)) ∈ Φₘ.source)
    (hsource₁ : ∀ s ∈ Set.Icc b r, (s, (0 : Z)) ∈ Φ₁.source)
    (hgerm₀ : (Φ₀ : (ℝ × Z) → M) =ᶠ[𝓝 (a, (0 : Z))] Φₘ)
    (hgerm₁ : (Φ₁ : (ℝ × Z) → M) =ᶠ[𝓝 (b, (0 : Z))] Φₘ)
    (haxis₀ : ∀ s ∈ Set.Ioc l a, Φ₀ (s, 0) = Φₘ (s, 0))
    (haxis₁ : ∀ s ∈ Set.Ico b r, Φ₁ (s, 0) = Φₘ (s, 0)) (hleft : Φ₀ (l, 0) ∉ Φₘ.target)
    (hright : Φ₁ (r, 0) ∉ Φₘ.target) (hne : Φ₀ (l, 0) ≠ Φ₁ (r, 0)) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) (ℝ × Z) M ∞,
      Set.Icc l r ×ˢ {(0 : Z)} ⊆ Φ.source ∧
        (∀ y ∈ Φ.target, V y = Smale.FlowConstruction.partialChartField Φ.symm W y) ∧
          Φ (l, 0) = Φ₀ (l, 0) ∧
            Φ (r, 0) = Φ₁ (r, 0) ∧
              (∀ s ∈ Set.Ioo l r, Φ (s, 0) = Φₘ (s, 0)) ∧
                ((Φ : (ℝ × Z) → M) =ᶠ[𝓝 (l, (0 : Z))] Φ₀) ∧
                  ((Φ : (ℝ × Z) → M) =ᶠ[𝓝 (r, (0 : Z))] Φ₁) := by
  let γ : ℝ → M := fun s => threeChartMap Φ₀ Φₘ Φ₁ a b (s, 0)
  have hγ₀ (s : ℝ) (hs : s ≤ a) : γ s = Φ₀ (s, 0) :=
    (threeChartMap_left_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₀ hs).eq_of_nhds
  have hγ₁ (s : ℝ) (hs : b ≤ s) : γ s = Φ₁ (s, 0) :=
    (threeChartMap_right_closed_germ Φ₀ Φₘ Φ₁ hab hgerm₁ hs).eq_of_nhds
  have hγₘ (s : ℝ) (hs : s ∈ Set.Ioo a b) : γ s = Φₘ (s, 0) :=
    (threeChartMap_middle_germ Φ₀ Φₘ Φ₁ hs.1 hs.2).eq_of_nhds
  have hregular (s : ℝ) (hs : s ∈ Set.Ioo l r) : γ s = Φₘ (s, 0) := by
    by_cases hsa : s ≤ a
    · exact (hγ₀ s hsa).trans (haxis₀ s ⟨hs.1, hsa⟩)
    by_cases hbs : b ≤ s
    · exact (hγ₁ s hbs).trans (haxis₁ s ⟨hbs, hs.2⟩)
    exact hγₘ s ⟨lt_of_not_ge hsa, lt_of_not_ge hbs⟩
  have hinj : Set.InjOn γ (Set.Icc l r) :=
    injective_closed_axis_of_regular_chart Φₘ γ hsourceₘ hregular
      (by rw [hγ₀ l hla.le]; exact hleft) (by rw [hγ₁ r hbr.le]; exact hright)
      (by rw [hγ₀ l hla.le, hγ₁ r hbr.le]; exact hne)
  obtain ⟨Φ, hsource, haxis, hfield, hg₀, hg₁⟩ :=
    exists_glued_three_native_field_charts Φ₀ Φₘ Φ₁ W V hfield₀ hfieldₘ hfield₁ hla.le hab hbr.le
      hsource₀ (fun s hs => hsourceₘ s ⟨hla.trans hs.1, hs.2.trans hbr⟩) hsource₁ hgerm₀ hgerm₁ γ
      hinj (fun s hs => (hγ₀ s hs.2).symm) (fun s hs => (hγₘ s hs).symm)
      (fun s hs => (hγ₁ s hs.1).symm)
  have hlr : l ≤ r := (hla.trans (hab.trans hbr)).le
  refine
    ⟨Φ, hsource, hfield, (haxis l ⟨le_rfl, hlr⟩).trans (hγ₀ l hla.le),
      (haxis r ⟨hlr, le_rfl⟩).trans (hγ₁ r hbr.le), ?_, hg₀, hg₁⟩
  exact fun s hs => (haxis s ⟨hs.1.le, hs.2.le⟩).trans (hregular s hs)

private theorem
    MorseCancel.exists_cubic_spatial_overlap_germ {m : ℕ} {M : Type*} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) (Φ Ψ : Model m → M) {c r : ℝ} (hr : 0 < r) {l : Filter ℝ} [Filter.NeBot l]
    (hlim : Filter.Tendsto (fun t => cubicFlowCylinder σ a (0, t)) l (𝓝 (c, (0 : Fin m → ℝ))))
    {J : Set ℝ} (hJ : IsOpen J) (hJl : J ∈ l)
    (hmatch :
      ∀ᶠ z : Fin m → ℝ in 𝓝 0,
        ∀ t ∈ J,
          cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r →
            Φ (cubicFlowCylinder σ a (z, t)) = Ψ (cubicFlowCylinder σ a (z, t))) :
    ∃ T ∈ J,
      cubicFlowCylinder σ a (0, T) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r ∧
        Φ =ᶠ[𝓝 (cubicFlowCylinder σ a (0, T))] Ψ := by
  have hnear : ∀ᶠ t in l, cubicFlowCylinder σ a (0, t) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r :=
    hlim.eventually (Metric.ball_mem_nhds _ hr)
  have hJevent : ∀ᶠ t in l, t ∈ J := hJl
  obtain ⟨T, hTJ, hTball⟩ := (hJevent.and hnear).exists
  let C := cubicFlowCylinderChart σ ha
  let p₀ : (Fin m → ℝ) × ℝ := (0, T)
  have htime : (fun p => Φ (C p)) =ᶠ[𝓝 p₀] (fun p => Ψ (C p)) := by
    have hball : ∀ᶠ p in 𝓝 p₀, C p ∈ Metric.ball (c, (0 : Fin m → ℝ)) r :=
      (contDiff_cubicFlowCylinder σ a).continuous.continuousAt.eventually
        (Metric.isOpen_ball.mem_nhds hTball)
    filter_upwards [continuousAt_fst.eventually hmatch,
      continuousAt_snd.eventually (hJ.mem_nhds hTJ), hball] with p hp hpt hpball
    exact hp p.2 hpt (Metric.ball_subset_closedBall hpball)
  have hCt : C p₀ ∈ C.target := C.map_source' (Set.mem_univ p₀)
  have hi : C.symm (C p₀) = p₀ := C.left_inv' (Set.mem_univ p₀)
  have hInv : Filter.Tendsto C.symm (𝓝 (C p₀)) (𝓝 p₀) := by
    have hh : Filter.Tendsto C.symm (𝓝 (C p₀)) (𝓝 (C.symm (C p₀))) :=
      C.toOpenPartialHomeomorph.symm.continuousAt hCt |>.tendsto
    rwa [hi] at hh
  refine ⟨T, hTJ, hTball, ?_⟩
  filter_upwards [hInv.eventually htime, C.open_target.mem_nhds hCt] with p hp hpt
  have hright : C (C.symm p) = p := C.right_inv' hpt
  change Φ (C (C.symm p)) = Ψ (C (C.symm p)) at hp
  rwa [hright] at hp

private theorem MorseCancel.cubicFlowCylinder_forward_stays_box {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) (z : Fin m → ℝ) {c r T : ℝ} (hr : 0 < r)
    (hlim :
      Filter.Tendsto (fun t => cubicFlowCylinder σ a (z, t)) Filter.atTop
        (𝓝 (c, (0 : Fin m → ℝ))))
    (hT : cubicFlowCylinder σ a (z, T) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r) {t : ℝ}
    (ht : T ≤ t) : cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r := by
  have hnear :
    ∀ᶠ u in Filter.atTop, cubicFlowCylinder σ a (z, u) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r :=
    hlim.eventually (Metric.ball_mem_nhds _ hr)
  obtain ⟨u, hu, hut⟩ := (hnear.and (Filter.eventually_ge_atTop t)).exists
  exact cubicFlowCylinder_stays_axis_ball σ ha z ⟨ht, hut⟩ hT (Metric.ball_subset_closedBall hu)

private theorem MorseCancel.cubicFlowCylinder_backward_stays_box {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) (z : Fin m → ℝ) {c r T : ℝ} (hr : 0 < r)
    (hlim :
      Filter.Tendsto (fun t => cubicFlowCylinder σ a (z, t)) Filter.atBot
        (𝓝 (c, (0 : Fin m → ℝ))))
    (hT : cubicFlowCylinder σ a (z, T) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r) {t : ℝ}
    (ht : t ≤ T) : cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (c, (0 : Fin m → ℝ)) r := by
  have hnear :
    ∀ᶠ u in Filter.atBot, cubicFlowCylinder σ a (z, u) ∈ Metric.ball (c, (0 : Fin m → ℝ)) r :=
    hlim.eventually (Metric.ball_mem_nhds _ hr)
  obtain ⟨u, hu, hut⟩ := (hnear.and (Filter.eventually_le_atBot t)).exists
  exact cubicFlowCylinder_stays_axis_ball σ ha z ⟨hut, ht⟩ (Metric.ball_subset_closedBall hu) hT

private theorem MorseCancel.strictMono_cubicAxisParameter {a : ℝ} (ha : 0 < a) :
    StrictMono (cubicAxisParameter a) := by
  intro s t hst
  exact mul_lt_mul_of_pos_left (strictMono_tanh (mul_lt_mul_of_pos_left hst ha)) ha

private theorem MorseCancel.tendsto_cubicFlowCylinder_axis_atTop {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) :
    Filter.Tendsto (fun t => cubicFlowCylinder σ a (0, t)) Filter.atTop
      (𝓝 (a, (0 : Fin m → ℝ))) := by
  simpa only [cubicFlowCylinder_axis] using tendsto_cubicModelOrbit_atTop (m := m) ha

private theorem MorseCancel.tendsto_cubicFlowCylinder_axis_atBot {m : ℕ} (σ : Fin m → ℝ) {a : ℝ}
    (ha : 0 < a) :
    Filter.Tendsto (fun t => cubicFlowCylinder σ a (0, t)) Filter.atBot
      (𝓝 (-a, (0 : Fin m → ℝ))) := by
  simpa only [cubicFlowCylinder_axis] using tendsto_cubicModelOrbit_atBot (m := m) ha

private theorem
    MorseCancel.cubicFlowCylinder_zero_clock {m : ℕ} (σ : Fin m → ℝ) {a s : ℝ} (ha : 0 < a)
    (hs : s ∈ Set.Ioo (-a) a) :
    cubicFlowCylinder σ a (0, cubicAxisClock a s) = (s, (0 : Fin m → ℝ)) := by
  rw [cubicFlowCylinder_axis]
  change (cubicAxisParameter a (cubicAxisClock a s), 0) = (s, 0)
  rw [cubicAxisParameter_clock ha hs]

private theorem
    MorseCancel.incoming_axis_segment_in_box {m : ℕ} (σ : Fin m → ℝ) {a r T : ℝ} (ha : 0 < a)
    (hr : 0 < r)
    (hstart : cubicFlowCylinder σ a (0, T) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) r) :
    ∀ s ∈ Set.Icc (cubicAxisParameter a T) a,
      (s, (0 : Fin m → ℝ)) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) r ∧
        (s < a → T ≤ cubicAxisClock a s) := by
  intro s hs
  rcases hs.2.lt_or_eq with hsa | hsa
  · have hs' : s ∈ Set.Ioo (-a) a := ⟨(cubicAxisParameter_mem ha T).1.trans_le hs.1, hsa⟩
    have ht : T ≤ cubicAxisClock a s := by
      apply (strictMono_cubicAxisParameter ha).le_iff_le.mp
      rw [cubicAxisParameter_clock ha hs']
      exact hs.1
    have hb :=
      cubicFlowCylinder_forward_stays_box σ ha 0 hr (tendsto_cubicFlowCylinder_axis_atTop σ ha)
        hstart ht
    rw [cubicFlowCylinder_zero_clock σ ha hs'] at hb
    exact ⟨hb, fun _ => ht⟩
  · subst s
    exact ⟨Metric.mem_closedBall_self hr.le, fun h => (lt_irrefl _ h).elim⟩

private theorem
    MorseCancel.outgoing_axis_segment_in_box {m : ℕ} (σ : Fin m → ℝ) {a r T : ℝ} (ha : 0 < a)
    (hr : 0 < r)
    (hstart : cubicFlowCylinder σ a (0, T) ∈ Metric.closedBall (-a, (0 : Fin m → ℝ)) r) :
    ∀ s ∈ Set.Icc (-a) (cubicAxisParameter a T),
      (s, (0 : Fin m → ℝ)) ∈ Metric.closedBall (-a, (0 : Fin m → ℝ)) r ∧
        (-a < s → cubicAxisClock a s ≤ T) := by
  intro s hs
  rcases hs.1.eq_or_lt with has | has
  · subst s
    exact ⟨Metric.mem_closedBall_self hr.le, fun h => (lt_irrefl _ h).elim⟩
  · have hs' : s ∈ Set.Ioo (-a) a := ⟨has, hs.2.trans_lt (cubicAxisParameter_mem ha T).2⟩
    have ht : cubicAxisClock a s ≤ T := by
      apply (strictMono_cubicAxisParameter ha).le_iff_le.mp
      rw [cubicAxisParameter_clock ha hs']
      exact hs.2
    have hb :=
      cubicFlowCylinder_backward_stays_box σ ha 0 hr (tendsto_cubicFlowCylinder_axis_atBot σ ha)
        hstart ht
    rw [cubicFlowCylinder_zero_clock σ ha hs'] at hb
    exact ⟨hb, fun _ => ht⟩

private theorem
    MorseCancel.exists_matched_full_cubic_field_chart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {m : ℕ} (σ : Fin m → ℝ)
    {a : ℝ} (ha : 0 < a) (Φq Φm Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hqfield : ∀ y ∈ Φq.target, V y = nativeCubicDescent σ Φq (-(a ^ 2)) y)
    (hmfield : ∀ y ∈ Φm.target, V y = nativeCubicDescent σ Φm (-(a ^ 2)) y)
    (hpfield : ∀ y ∈ Φp.target, V y = nativeCubicDescent σ Φp (-(a ^ 2)) y) {rq rp : ℝ}
    (hrq : 0 < rq) (hrp : 0 < rp) (hboxq : Metric.closedBall (-a, (0 : Fin m → ℝ)) rq ⊆ Φq.source)
    (hboxp : Metric.closedBall (a, (0 : Fin m → ℝ)) rp ⊆ Φp.source)
    (hmiddle : ∀ s ∈ Set.Ioo (-a) a, (s, (0 : Fin m → ℝ)) ∈ Φm.source)
    (hleft : Φq (-a, 0) ∉ Φm.target) (hright : Φp (a, 0) ∉ Φm.target)
    (hne : Φq (-a, 0) ≠ Φp (a, 0))
    (hmatchq :
      ∀ᶠ z : Fin m → ℝ in 𝓝 0,
        ∀ t : ℝ,
          t ≤ -1 →
            cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (-a, (0 : Fin m → ℝ)) rq →
              Φq (cubicFlowCylinder σ a (z, t)) = Φm (cubicFlowCylinder σ a (z, t)))
    (hmatchp :
      ∀ᶠ z : Fin m → ℝ in 𝓝 0,
        ∀ t : ℝ,
          2 ≤ t →
            cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) rp →
              Φp (cubicFlowCylinder σ a (z, t)) = Φm (cubicFlowCylinder σ a (z, t))) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source ∧
        (∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(a ^ 2)) y) ∧
          Φ (-a, 0) = Φq (-a, 0) ∧
            Φ (a, 0) = Φp (a, 0) ∧
              (∀ s ∈ Set.Ioo (-a) a, Φ (s, 0) = Φm (s, 0)) ∧
                ((Φ : Model m → M) =ᶠ[𝓝 (-a, (0 : Fin m → ℝ))] Φq) ∧
                  ((Φ : Model m → M) =ᶠ[𝓝 (a, (0 : Fin m → ℝ))] Φp) := by
  have hqmatch :
    ∀ᶠ z : Fin m → ℝ in 𝓝 0,
      ∀ t ∈ Set.Iio (-1 : ℝ),
        cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (-a, (0 : Fin m → ℝ)) rq →
          Φq (cubicFlowCylinder σ a (z, t)) = Φm (cubicFlowCylinder σ a (z, t)) := by
    filter_upwards [hmatchq] with z hz
    exact fun t ht => hz t ht.le
  have hpmatch :
    ∀ᶠ z : Fin m → ℝ in 𝓝 0,
      ∀ t ∈ Set.Ioi (2 : ℝ),
        cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) rp →
          Φp (cubicFlowCylinder σ a (z, t)) = Φm (cubicFlowCylinder σ a (z, t)) := by
    filter_upwards [hmatchp] with z hz
    exact fun t ht => hz t ht.le
  obtain ⟨Tq, hTq, hqball, hgq⟩ :=
    exists_cubic_spatial_overlap_germ σ ha Φq Φm hrq (tendsto_cubicFlowCylinder_axis_atBot σ ha)
      isOpen_Iio (Filter.Iio_mem_atBot (-1 : ℝ)) hqmatch
  obtain ⟨Tp, hTp, hpball, hgp⟩ :=
    exists_cubic_spatial_overlap_germ σ ha Φp Φm hrp (tendsto_cubicFlowCylinder_axis_atTop σ ha)
      isOpen_Ioi (Filter.Ioi_mem_atTop (2 : ℝ)) hpmatch
  have hcutq := cubicAxisParameter_mem ha Tq
  have hcutp := cubicAxisParameter_mem ha Tp
  have horder : cubicAxisParameter a Tq < cubicAxisParameter a Tp :=
    strictMono_cubicAxisParameter ha (by change Tq < -1 at hTq; change 2 < Tp at hTp; linarith)
  have hgq' : (Φq : Model m → M) =ᶠ[𝓝 (cubicAxisParameter a Tq, 0)] Φm := by
    simpa only [cubicFlowCylinder_axis, cubicModelOrbit] using hgq
  have hgp' : (Φp : Model m → M) =ᶠ[𝓝 (cubicAxisParameter a Tp, 0)] Φm := by
    simpa only [cubicFlowCylinder_axis, cubicModelOrbit] using hgp
  have hqsegment := outgoing_axis_segment_in_box σ ha hrq (Metric.ball_subset_closedBall hqball)
  have hpsegment := incoming_axis_segment_in_box σ ha hrp (Metric.ball_subset_closedBall hpball)
  have hqaxis (s : ℝ) (hs : s ∈ Set.Ioc (-a) (cubicAxisParameter a Tq)) : Φq (s, 0) = Φm (s, 0) :=
    by
    have hs' : s ∈ Set.Ioo (-a) a := ⟨hs.1, hs.2.trans_lt hcutq.2⟩
    obtain ⟨hb, ht⟩ := hqsegment s ⟨hs.1.le, hs.2⟩
    have hball :
      cubicFlowCylinder σ a (0, cubicAxisClock a s) ∈
        Metric.closedBall (-a, (0 : Fin m → ℝ)) rq := by
      rw [cubicFlowCylinder_zero_clock σ ha hs']; exact hb
    have hh := hmatchq.self_of_nhds (cubicAxisClock a s) ((ht hs.1).trans hTq.le) hball
    simpa only [cubicFlowCylinder_zero_clock σ ha hs'] using hh
  have hpaxis (s : ℝ) (hs : s ∈ Set.Ico (cubicAxisParameter a Tp) a) : Φp (s, 0) = Φm (s, 0) := by
    have hs' : s ∈ Set.Ioo (-a) a := ⟨hcutp.1.trans_le hs.1, hs.2⟩
    obtain ⟨hb, ht⟩ := hpsegment s ⟨hs.1, hs.2.le⟩
    have hball :
      cubicFlowCylinder σ a (0, cubicAxisClock a s) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) rp :=
      by rw [cubicFlowCylinder_zero_clock σ ha hs']; exact hb
    have hh := hmatchp.self_of_nhds (cubicAxisClock a s) (hTp.le.trans (ht hs.2)) hball
    simpa only [cubicFlowCylinder_zero_clock σ ha hs'] using hh
  exact
    Degree.FieldChartGluing.exists_closed_axis_native_field_chart Φq Φm Φp
      (cubicDescent σ (-(a ^ 2))) V hqfield hmfield hpfield hcutq.1 horder hcutp.2
      (fun s hs => hboxq (hqsegment s hs).1) hmiddle (fun s hs => hboxp (hpsegment s hs).1) hgq'
      hgp' hqaxis hpaxis hleft hright hne

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.exists_full_cubic_chart_from_corrected_cylinder {Z E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M] {m : ℕ}
    {V W : (x : M) → TangentSpace 𝓘(ℝ, E) x} (σ : Fin m → ℝ) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    {a : ℝ} (ha : 0 < a) (Φq Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z}
    (hAsource : A.source = U ×ˢ Set.univ)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hqfield : ∀ y ∈ Φq.target, V y = nativeCubicDescent σ Φq (-(a ^ 2)) y)
    (hpfield : ∀ y ∈ Φp.target, V y = nativeCubicDescent σ Φp (-(a ^ 2)) y)
    (hAfield :
      ∀ y ∈ A.target,
        V y = Smale.FlowConstruction.partialChartField A.symm (fun _ : Z × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (L₁ : Smale.MorseHandle.NegativeSpace σ ≃L[ℝ] Smale.MorseHandle.NegativeSpace σ)
    (L₂ : Smale.MorseHandle.PositiveSpace σ ≃L[ℝ] Smale.MorseHandle.PositiveSpace σ)
    (Q P : (Smale.MorseHandle.NegativeSpace σ × Smale.MorseHandle.PositiveSpace σ) → Z)
    (v₀ v₁ : (Smale.MorseHandle.NegativeSpace σ × Smale.MorseHandle.PositiveSpace σ) → ℝ)
    {Oq Op : Set (Smale.MorseHandle.NegativeSpace σ × Smale.MorseHandle.PositiveSpace σ)}
    (hOq : IsOpen Oq) (hOp : IsOpen Op) (h0q : 0 ∈ Oq) (h0p : 0 ∈ Op) (hQU : ∀ u ∈ Oq, Q u ∈ U)
    (hPU : ∀ u ∈ Op, P u ∈ U) {Rq Rp Tq Tp : ℝ} (hRq : 0 < Rq) (hRp : 0 < Rp)
    (hboxq : Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq ⊆ Φq.source)
    (hboxp : Metric.closedBall (a, (0 : Fin m → ℝ)) Rp ⊆ Φp.source)
    (hsliceq :
      ∀ u ∈ Oq,
        cubicFlowCylinder σ a ((Smale.MorseHandle.splitCoordinates σ).symm u, Tq) ∈
          Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq)
    (hslicep :
      ∀ u ∈ Op,
        cubicFlowCylinder σ a ((Smale.MorseHandle.splitCoordinates σ).symm u, Tp) ∈
          Metric.closedBall (a, (0 : Fin m → ℝ)) Rp)
    (hphaseq :
      ∀ u ∈ Oq,
        Φq (cubicFlowCylinder σ a ((Smale.MorseHandle.splitCoordinates σ).symm u, Tq)) =
          A (Q u, Tq + v₀ u))
    (hphasep :
      ∀ u ∈ Op,
        Φp (cubicFlowCylinder σ a ((Smale.MorseHandle.splitCoordinates σ).symm u, Tp)) =
          A (P u, Tp + v₁ u))
    (Ξ :
      PartialDiffeomorph
        𝓘(ℝ, (Smale.MorseHandle.NegativeSpace σ × Smale.MorseHandle.PositiveSpace σ) × ℝ) 𝓘(ℝ, E)
        ((Smale.MorseHandle.NegativeSpace σ × Smale.MorseHandle.PositiveSpace σ) × ℝ) M ∞)
    {O : Set (Smale.MorseHandle.NegativeSpace σ × Smale.MorseHandle.PositiveSpace σ)}
    (hO : IsOpen O) (h0O : 0 ∈ O) (hΞsource : Ξ.source = O ×ˢ Set.univ)
    (hΞtarget : Ξ.target = A.target)
    (hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hΞfield :
      ∀ y ∈ Ξ.target,
        W y =
          Smale.FlowConstruction.partialChartField Ξ.symm
            (fun _ :
                (Smale.MorseHandle.NegativeSpace σ × Smale.MorseHandle.PositiveSpace σ) × ℝ =>
              (0, 1))
            y)
    (G : Flow ℝ M) (hG : ∀ x, IsMIntegralCurve (fun t => G t x) W)
    (hWq : ∀ᶠ y in 𝓝 (Φq (-a, 0)), W y = V y) (hWp : ∀ᶠ y in 𝓝 (Φp (a, 0)), W y = V y)
    (hne : Φq (-a, 0) ≠ Φp (a, 0))
    (hleft :
      ∀ᶠ u in 𝓝 (0 : Smale.MorseHandle.NegativeSpace σ × Smale.MorseHandle.PositiveSpace σ),
        ∀ t : ℝ, t ≤ -1 → Ξ (u, t) = A (Q u, t + v₀ u))
    (hright :
      ∀ᶠ u in 𝓝 (0 : Smale.MorseHandle.NegativeSpace σ × Smale.MorseHandle.PositiveSpace σ),
        ∀ t : ℝ, 2 ≤ t → Ξ (u, t) = A (P (L₁ u.1, L₂ u.2), t + v₁ (L₁ u.1, L₂ u.2))) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source ∧
        (∀ y ∈ Φ.target, W y = nativeCubicDescent σ Φ (-(a ^ 2)) y) ∧
          Φ (-a, 0) = Φq (-a, 0) ∧ Φ (a, 0) = Φp (a, 0) ∧ Φ (0, 0) = Ξ (0, 0) := by
  let e := Smale.MorseHandle.splitCoordinates σ
  let L := L₁.prodCongr L₂
  let T := splitTransverseChange e L₁ L₂
  let D := transverseFieldChange T
  have hqsrc : (-a, (0 : Fin m → ℝ)) ∈ Φq.source := hboxq (Metric.mem_closedBall_self hRq.le)
  have hpsrc : (a, (0 : Fin m → ℝ)) ∈ Φp.source := hboxp (Metric.mem_closedBall_self hRp.le)
  obtain ⟨Ψq, rq, hrq, hΨqbox, hΨqsub, _, hΨqmap, hΨqfield⟩ :=
    Degree.FieldChartGluing.exists_controlled_field_germ_chart Φq (cubicDescent σ (-(a ^ 2))) V W
      hqfield hqsrc hWq Metric.isOpen_ball (Metric.mem_ball_self hRq)
  have hcontrolq :
    Metric.closedBall (-a, (0 : Fin m → ℝ)) rq ⊆ Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq :=
    fun p hp => Metric.ball_subset_closedBall (hΨqsub (hΨqbox hp)).2
  obtain ⟨ΦpB, _, hpBsource, hpBaxis, hpBfield, hpBflow⟩ :=
    exists_signed_block_changed_cubic_chart σ hσ L₁ L₂ Φp V (-(a ^ 2)) hpfield
  have hDcenter : D (a, 0) = (a, 0) := by change (a, T 0) = (a, 0); rw [map_zero]
  have hOpcoord : IsOpen (D ⁻¹' Metric.ball (a, (0 : Fin m → ℝ)) Rp) :=
    Metric.isOpen_ball.preimage D.continuous
  have hpO : (a, (0 : Fin m → ℝ)) ∈ D ⁻¹' Metric.ball (a, (0 : Fin m → ℝ)) Rp := by
    change D (a, 0) ∈ Metric.ball (a, (0 : Fin m → ℝ)) Rp
    rw [hDcenter]
    exact Metric.mem_ball_self hRp
  have hWpB : ∀ᶠ y in 𝓝 (ΦpB (a, 0)), W y = V y := by rw [hpBaxis]; exact hWp
  obtain ⟨Ψp, rp, hrp, hΨpbox, hΨpsub, _, hΨpmap, hΨpfield⟩ :=
    Degree.FieldChartGluing.exists_controlled_field_germ_chart ΦpB (cubicDescent σ (-(a ^ 2))) V W
      hpBfield ((hpBsource a).mpr hpsrc) hWpB hOpcoord hpO
  have hnewp (z : Fin m → ℝ) (t : ℝ) :
    Ψp (cubicFlowCylinder σ a (z, t)) = Φp (cubicFlowCylinder σ a (e.symm (L (e z)), t)) := by
    have hh := hpBflow a t (e z)
    change
      ΦpB (cubicFlowCylinder σ a (e.symm (e z), t)) =
        Φp (cubicFlowCylinder σ a (e.symm (L (e z)), t)) at hh
    rw [e.symm_apply_apply] at hh
    exact (hΨpmap _).trans hh
  have hcontrolp (z : Fin m → ℝ) (t : ℝ)
    (hp : cubicFlowCylinder σ a (z, t) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) rp) :
    cubicFlowCylinder σ a (e.symm (L (e z)), t) ∈ Metric.closedBall (a, (0 : Fin m → ℝ)) Rp := by
    have hb : D (cubicFlowCylinder σ a (z, t)) ∈ Metric.ball (a, (0 : Fin m → ℝ)) Rp :=
      (hΨpsub (hΨpbox hp)).2
    have hc : D (cubicFlowCylinder σ a (z, t)) = cubicFlowCylinder σ a (e.symm (L (e z)), t) :=
      signed_block_change_cubic_cylinder σ hσ L₁ L₂ a t z
    rw [hc] at hb
    exact Metric.ball_subset_closedBall hb
  let R := Smale.PartialChart.restrictTarget e.toDiffeomorph.toPartialDiffeomorph hO
  have hRtarget : R.target = O := by
    ext u
    change
      (u ∈
            (Set.univ :
              Set (Smale.MorseHandle.NegativeSpace σ × Smale.MorseHandle.PositiveSpace σ)) ∧
          u ∈ O) ↔
        u ∈ O
    simp only [Set.mem_univ, true_and]
  have hR0 : (0 : Fin m → ℝ) ∈ R.source := by
    change (0 : Fin m → ℝ) ∈ Set.univ ∧ e 0 ∈ O
    rw [map_zero]
    exact ⟨Set.mem_univ _, h0O⟩
  obtain ⟨B₀, hBsource, hBtarget, hBmap, hBfield⟩ :=
    Degree.FlowSuspension.exists_native_phase_cylinder Ξ hΞsource R hRtarget (fun _ => (0 : ℝ))
      contDiff_const W hΞfield
  obtain ⟨Φm, hmTarget, hmidAxis, _, hmField, _, hcompose⟩ :=
    exists_regular_cubic_chart_of_native_vertical_field σ ha B₀ hBsource hR0 W hW hBfield G hG
  have hmid (z : Fin m → ℝ) (t : ℝ) : Φm (cubicFlowCylinder σ a (z, t)) = Ξ (e z, t) := by
    rw [hcompose, hBmap]
    change Ξ (e z, t + 0) = Ξ (e z, t)
    rw [add_zero]
  have hmTargetA : Φm.target = A.target := hmTarget.trans (hBtarget.trans hΞtarget)
  have hzeroAt (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) {c : ℝ}
    (hc : (c, (0 : Fin m → ℝ)) ∈ Φ.source) (hcrit : c ^ 2 = a ^ 2)
    (hf : ∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(a ^ 2)) y) : V (Φ (c, 0)) = 0 := by
    rw [hf _ (Φ.map_source' hc)]
    apply (partialChartField_zero_iff Φ (cubicDescent σ (-(a ^ 2))) (Φ.map_source' hc)).mpr
    have hi : Φ.symm (Φ (c, (0 : Fin m → ℝ))) = (c, 0) := Φ.left_inv' hc
    rw [hi]
    ext i <;> simp [cubicDescent, hcrit]
  have hzeroq : V (Φq (-a, 0)) = 0 := hzeroAt Φq hqsrc (by ring) hqfield
  have hzerop : V (Φp (a, 0)) = 0 := hzeroAt Φp hpsrc rfl hpfield
  have hAregular (y : M) (hy : y ∈ A.target) : V y ≠ 0 := by
    intro hz
    rw [hAfield y hy] at hz
    have hh := (partialChartField_zero_iff A (fun _ : Z × ℝ => (0, 1)) hy).mp hz
    exact one_ne_zero (congrArg Prod.snd hh)
  have hqval : Ψq (-a, 0) = Φq (-a, 0) := hΨqmap _
  have hpval : Ψp (a, 0) = Φp (a, 0) := (hΨpmap _).trans (hpBaxis a)
  have hqnot : Ψq (-a, 0) ∉ Φm.target := by
    rw [hqval, hmTargetA]
    exact fun h => hAregular _ h hzeroq
  have hpnot : Ψp (a, 0) ∉ Φm.target := by
    rw [hpval, hmTargetA]
    exact fun h => hAregular _ h hzerop
  obtain ⟨hmatchq, hmatchp⟩ :=
    matched_cubic_time_formulas σ ha Φq Φp A hAsource hV hqfield hpfield hAfield F hF e L Q P v₀
      v₁ hOq hOp h0q h0p hQU hPU hboxq hboxp hsliceq hslicep hphaseq hphasep Ψq Ψp Φm Ξ hΨqmap
      hnewp hmid hcontrolq hcontrolp hleft hright
  obtain ⟨Φ, haxis, hfield, hΦq, hΦp, hΦmid, _, _⟩ :=
    exists_matched_full_cubic_field_chart σ ha Ψq Φm Ψp W hΨqfield hmField hΨpfield hrq hrp hΨqbox
      hΨpbox (fun s hs => hmidAxis ⟨hs, rfl⟩) hqnot hpnot (by rw [hqval, hpval]; exact hne)
      hmatchq hmatchp
  have hmid0 : Φm (0, 0) = Ξ (0, 0) := by
    have hh := hmid 0 0
    simpa only [cubicFlowCylinder_zero_time, map_zero] using hh
  exact
    ⟨Φ, haxis, hfield, hΦq.trans hqval, hΦp.trans hpval, (hΦmid 0 ⟨by linarith, ha⟩).trans hmid0⟩

private theorem Degree.FlowSuspension.cylinder_phase_basin_coordinates {E Z M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [TopologicalSpace M] (F : Flow ℝ M) (Φ : Z × ℝ → M)
    (Q : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Z) E Z ∞)
    (hflow : ∀ z ∈ Q.target, ∀ t : ℝ, Φ (z, t) = F t (Φ (z, 0))) (Ξ : E → M) (v : E → ℝ)
    (hphase : ∀ u ∈ Q.source, Ξ u = Φ (Q u, v u)) (Basin : M → Prop)
    (hshift : ∀ t x, Basin (F t x) ↔ Basin x) (R : E → Prop)
    (hbasin : ∀ u ∈ Q.source, Basin (Ξ u) ↔ R u) :
    ∀ z ∈ Q.target, ∀ b : ℝ, Basin (Φ (z, b)) ↔ R (Q.symm z) := by
  intro z hz b
  have hu := Q.map_target' hz
  have hi : Q (Q.symm z) = z := Q.right_inv' hz
  have hphase' : Ξ (Q.symm z) = F (v (Q.symm z)) (Φ (z, 0)) := by
    rw [hphase (Q.symm z) hu, hi, hflow z hz]
  have hend : Basin (Ξ (Q.symm z)) ↔ Basin (Φ (z, 0)) := by
    rw [hphase']
    exact hshift _ _
  have hslice : Basin (Φ (z, b)) ↔ Basin (Φ (z, 0)) := by
    rw [hflow z hz b]
    exact hshift _ _
  exact hslice.trans (hend.symm.trans (hbasin _ hu))

private theorem
    Degree.FlowSuspension.cylinder_outgoing_basin_labels {Z M : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [TopologicalSpace M] {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (F : Flow ℝ M) (Φ : Z × ℝ → M)
    (Q : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (hflow : ∀ z ∈ Q.target, ∀ t : ℝ, Φ (z, t) = F t (Φ (z, 0))) (Ξ : (A × B) → M)
    (v : (A × B) → ℝ) (hphase : ∀ u ∈ Q.source, Ξ u = Φ (Q u, v u)) {q : M}
    (hbasin : ∀ u ∈ Q.source, Filter.Tendsto (fun t => F t (Ξ u)) Filter.atBot (𝓝 q) ↔ u.2 = 0) :
    ∀ z ∈ Q.target,
      ∀ b : ℝ,
        Filter.Tendsto (fun t => F t (Φ (z, b))) Filter.atBot (𝓝 q) ↔
          ∃ x : A, (x, (0 : B)) ∈ Q.source ∧ Q (x, 0) = z := by
  have hcoord :=
    cylinder_phase_basin_coordinates F Φ Q hflow Ξ v hphase
      (fun x => Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q))
      (fun t x => MorseCancel.flow_time_atBot_limit_iff F t x q) (fun u : A × B => u.2 = 0) hbasin
  intro z hz b
  rw [hcoord z hz b]
  constructor
  · intro hu
    have hpair : Q.symm z = ((Q.symm z).1, (0 : B)) := Prod.ext rfl hu
    refine ⟨(Q.symm z).1, hpair ▸ Q.map_target' hz, ?_⟩
    rw [← hpair]
    exact Q.right_inv' hz
  · rintro ⟨x, hx, hQx⟩
    have hi : Q.symm (Q (x, (0 : B))) = (x, 0) := Q.left_inv' hx
    rw [← hQx, hi]

private theorem
    Degree.FlowSuspension.cylinder_incoming_basin_labels {Z M : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [TopologicalSpace M] {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (F : Flow ℝ M) (Φ : Z × ℝ → M)
    (P : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, Z) (A × B) Z ∞)
    (hflow : ∀ z ∈ P.target, ∀ t : ℝ, Φ (z, t) = F t (Φ (z, 0))) (Ξ : (A × B) → M)
    (v : (A × B) → ℝ) (hphase : ∀ u ∈ P.source, Ξ u = Φ (P u, v u)) {p : M}
    (hbasin : ∀ u ∈ P.source, Filter.Tendsto (fun t => F t (Ξ u)) Filter.atTop (𝓝 p) ↔ u.1 = 0) :
    ∀ z ∈ P.target,
      ∀ b : ℝ,
        Filter.Tendsto (fun t => F t (Φ (z, b))) Filter.atTop (𝓝 p) ↔
          ∃ y ∈ P.source, y.1 = 0 ∧ P y = z := by
  have hcoord :=
    cylinder_phase_basin_coordinates F Φ P hflow Ξ v hphase
      (fun x => Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
      (fun t x => MorseCancel.flow_time_atTop_limit_iff F t x p) (fun u : A × B => u.1 = 0) hbasin
  intro z hz b
  rw [hcoord z hz b]
  constructor
  · intro hu
    exact ⟨P.symm z, P.map_target' hz, hu, P.right_inv' hz⟩
  · rintro ⟨y, hy, hy0, hPy⟩
    have hi : P.symm (P y) = y := P.left_inv' hy
    rw [← hPy, hi]
    exact hy0

private theorem MorseCancel.cubicFlowCylinder_transverse_zero_iff {m : ℕ} (σ : Fin m → ℝ) (a T : ℝ)
    (z : Fin m → ℝ) (i : Fin m) : (cubicFlowCylinder σ a (z, T)).2 i = 0 ↔ z i = 0 := by
  simp [cubicFlowCylinder, Real.exp_ne_zero]

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.incoming_cubic_slice_basin {m : ℕ} {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (σ : Fin m → ℝ) (a T : ℝ)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) (F : Flow ℝ M) {p : M}
    (hbasin :
      ∀ z ∈ Φ.source,
        Filter.Tendsto (fun t => F t (Φ z)) Filter.atTop (𝓝 p) ↔ ∀ i, σ i = -1 → z.2 i = 0)
    (u : Smale.MorseHandle.NegativeSpace σ × Smale.MorseHandle.PositiveSpace σ)
    (hu : cubicFlowCylinder σ a ((Smale.MorseHandle.splitCoordinates σ).symm u, T) ∈ Φ.source) :
    Filter.Tendsto
        (fun t =>
          F t (Φ (cubicFlowCylinder σ a ((Smale.MorseHandle.splitCoordinates σ).symm u, T))))
        Filter.atTop (𝓝 p) ↔
      u.1 = 0 := by
  rw [hbasin _ hu]
  have he :
    (∀ i,
        σ i = -1 →
          (cubicFlowCylinder σ a ((Smale.MorseHandle.splitCoordinates σ).symm u, T)).2 i = 0) ↔
      ∀ i, σ i = -1 → (Smale.MorseHandle.splitCoordinates σ).symm u i = 0 := by
    simp only [cubicFlowCylinder_transverse_zero_iff]
  rw [he, ← Degree.TransverseGerms.splitCoordinates_negative_zero_iff]
  rw [(Smale.MorseHandle.splitCoordinates σ).apply_symm_apply]

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.outgoing_cubic_slice_basin {m : ℕ} {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1) (a T : ℝ)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) (F : Flow ℝ M) {q : M}
    (hbasin :
      ∀ z ∈ Φ.source,
        Filter.Tendsto (fun t => F t (Φ z)) Filter.atBot (𝓝 q) ↔ ∀ i, σ i = 1 → z.2 i = 0)
    (u : Smale.MorseHandle.NegativeSpace σ × Smale.MorseHandle.PositiveSpace σ)
    (hu : cubicFlowCylinder σ a ((Smale.MorseHandle.splitCoordinates σ).symm u, T) ∈ Φ.source) :
    Filter.Tendsto
        (fun t =>
          F t (Φ (cubicFlowCylinder σ a ((Smale.MorseHandle.splitCoordinates σ).symm u, T))))
        Filter.atBot (𝓝 q) ↔
      u.2 = 0 := by
  rw [hbasin _ hu]
  have he :
    (∀ i,
        σ i = 1 →
          (cubicFlowCylinder σ a ((Smale.MorseHandle.splitCoordinates σ).symm u, T)).2 i = 0) ↔
      ∀ i, σ i = 1 → (Smale.MorseHandle.splitCoordinates σ).symm u i = 0 := by
    simp only [cubicFlowCylinder_transverse_zero_iff]
  rw [he, ← Degree.TransverseGerms.splitCoordinates_positive_zero_iff σ hσ]
  rw [(Smale.MorseHandle.splitCoordinates σ).apply_symm_apply]

private theorem Degree.FlowCancellation.exists_native_lyapunov_residence {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    {C : Set M} (hC : IsCompact C) (hneg : ∀ x ∈ C, mvfderiv 𝓘(ℝ, E) f x (V x) < 0) :
    ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ C := by
  by_cases hne : C.Nonempty
  swap
  · exact ⟨1, zero_lt_one, fun γ _ => ⟨0, ⟨le_rfl, zero_le_one⟩, fun h => hne ⟨γ 0, h⟩⟩⟩
  have hspeed := (MorseCancel.contMDiff_directionalDerivative hf hV).continuous
  obtain ⟨v, hv, hmaxspeed⟩ := hC.exists_isMaxOn hne hspeed.continuousOn
  let δ := -mvfderiv 𝓘(ℝ, E) f v (V v)
  have hδ : 0 < δ := neg_pos.mpr (hneg v hv)
  have hbound (x : M) (hx : x ∈ C) : mvfderiv 𝓘(ℝ, E) f x (V x) ≤ -δ := by
    have hh : mvfderiv 𝓘(ℝ, E) f x (V x) ≤ mvfderiv 𝓘(ℝ, E) f v (V v) := hmaxspeed hx
    simpa only [δ, neg_neg] using hh
  obtain ⟨p, hp, hmin⟩ := hC.exists_isMinOn hne hf.continuous.continuousOn
  obtain ⟨q, hq, hmax⟩ := hC.exists_isMaxOn hne hf.continuous.continuousOn
  let T := (f q - f p + 1) / δ
  have hpq : f p ≤ f q := hmax hp
  have hT : 0 < T := div_pos (by linarith) hδ
  have hδT : δ * T = f q - f p + 1 := by
    dsimp [T]
    field_simp [hδ.ne']
  refine ⟨T, hT, ?_⟩
  intro γ hγ
  by_contra! hstay
  have hd (t : ℝ) : HasDerivAt (f ∘ γ) (mvfderiv 𝓘(ℝ, E) f (γ t) (V (γ t))) t :=
    Smale.FlowConstruction.hasDerivAt_comp_integralCurve hf hγ t
  have hdiff : Differentiable ℝ (f ∘ γ) := fun t => (hd t).differentiableAt
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT.le⟩
  have hlast : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have hdrop :=
    (convex_Icc (0 : ℝ) T).image_sub_le_mul_sub_of_deriv_le hdiff.continuous.continuousOn
      hdiff.differentiableOn
      (fun t ht => by
        rw [(hd t).deriv]
        exact hbound (γ t) (hstay t (interior_subset ht)))
      0 h0 T hlast hT.le
  simp only [Function.comp_apply, sub_zero, neg_mul] at hdrop
  rw [hδT] at hdrop
  have hlo : f p ≤ f (γ T) := hmin (hstay T hlast)
  have hhi : f (γ 0) ≤ f q := hmax (hstay 0 h0)
  linarith

private theorem Degree.FlowCancellation.combine_native_residence_bounds {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {B N U : Set M}
    (houter :
      ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ B \ N)
    (hinner :
      ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ U)
    (hnoreturn :
      ∀ γ : ℝ → M,
        IsMIntegralCurve γ V → ∀ a b : ℝ, γ a ∈ N → γ b ∈ N → ∀ t ∈ Set.Icc a b, γ t ∈ U) :
    ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ B := by
  obtain ⟨T₀, hT₀, hout⟩ := houter
  obtain ⟨T₁, hT₁, hin⟩ := hinner
  refine ⟨2 * T₀ + T₁, by linarith, ?_⟩
  intro γ hγ
  by_contra! hstay
  obtain ⟨a, ha, haout⟩ := hout γ hγ
  have haN : γ a ∈ N := by
    by_contra haN
    exact haout ⟨hstay a ⟨ha.1, by linarith [ha.2]⟩, haN⟩
  obtain ⟨b, hb, hbout⟩ := hout (γ ∘ (· + (T₀ + T₁))) (hγ.comp_add (T₀ + T₁))
  have hbN : γ (b + (T₀ + T₁)) ∈ N := by
    by_contra hbN
    exact hbout ⟨hstay (b + (T₀ + T₁)) ⟨by linarith [hb.1], by linarith [hb.2]⟩, hbN⟩
  obtain ⟨t, ht, htout⟩ := hin (γ ∘ (· + T₀)) (hγ.comp_add T₀)
  exact
    htout
      (hnoreturn γ hγ a (b + (T₀ + T₁)) haN hbN (t + T₀)
        ⟨by linarith [ha.2, ht.1], by linarith [hb.1, ht.2]⟩)

private theorem Degree.FlowCancellation.exists_perturbed_band_residence {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
    {V' : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hV' : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} {K N U : Set M}
    (hK : IsClosed K) (hN : IsOpen N) (hKN : K ⊆ N) (hNU : N ⊆ U) (hoff : ∀ x ∉ K, V' x = V x)
    (hneg : ∀ x, f x ∈ Set.Icc c d → x ∉ N → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hnoreturn : ∀ x ∈ N, ∀ t : ℝ, 0 ≤ t → F t x ∈ N → ∀ s ∈ Set.Icc (0 : ℝ) t, F s x ∈ U)
    (hinner :
      ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V' → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ U) :
    ∃ T : ℝ,
      0 < T ∧
        ∀ γ : ℝ → M, IsMIntegralCurve γ V' → ∃ t ∈ Set.Icc (0 : ℝ) T, f (γ t) ∉ Set.Icc c d := by
  have hcompact : IsCompact (f ⁻¹' Set.Icc c d \ N) :=
    ((isClosed_Icc.preimage hf.continuous).inter hN.isClosed_compl).isCompact
  have houter :=
    exists_native_lyapunov_residence hf hV' hcompact
      (by
        intro x hx
        rw [hoff x (fun h => hx.2 (hKN h))]
        exact hneg x hx.1 hx.2)
  exact
    combine_native_residence_bounds houter hinner
      (fun γ hγ a b ha hb =>
        native_no_return_of_supported_perturbation (hV.of_le (by simp)) F hcurve hK hKN hNU hoff
          hnoreturn hγ ha hb)

private def MorseCancel.transverseEnergy {m : ℕ} (σ : Fin m → ℝ) (p : Model m) : ℝ :=
  ∑ i, (σ i * p.2 i) ^ 2

private theorem MorseCancel.transverseEnergy_nonneg {m : ℕ} (σ : Fin m → ℝ) (p : Model m) :
    0 ≤ transverseEnergy σ p :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

private theorem MorseCancel.transverseEnergy_zero_iff {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    (p : Model m) : transverseEnergy σ p = 0 ↔ p.2 = 0 := by
  constructor
  · intro h
    funext i
    have hh :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (σ i * p.2 i))).mp h i
        (Finset.mem_univ i)
    exact (mul_eq_zero.mp (sq_eq_zero_iff.mp hh)).resolve_left (hσ i)
  · intro h
    simp [transverseEnergy, h]

private def MorseCancel.fieldLyapunov {m : ℕ} (σ : Fin m → ℝ) (k : ℝ) (p : Model m) : ℝ :=
  p.1 + k * ∑ i, σ i * p.2 i ^ 2

private theorem MorseCancel.contDiff_fieldLyapunov {m : ℕ} (σ : Fin m → ℝ) (k : ℝ) :
    ContDiff ℝ ∞ (fieldLyapunov σ k) := by
  unfold fieldLyapunov
  fun_prop

private theorem
    MorseCancel.hasFDerivAt_fieldLyapunov {m : ℕ} (σ : Fin m → ℝ) (k : ℝ) (p : Model m) :
    HasFDerivAt (fieldLyapunov σ k)
      (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ) +
        k •
          ∑ i,
            (2 * σ i * p.2 i) •
              ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))))
      p := by
  have hx := (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).hasFDerivAt (x := p)
  have hy (i : Fin m) :=
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))).hasFDerivAt
      (x := p)
  have hq := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => ((hy i).pow 2).const_mul (σ i))
  convert! hx.add (hq.const_mul k) using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [mul_assoc, mul_comm]

private theorem MorseCancel.fieldLyapunov_speed {m : ℕ} (σ : Fin m → ℝ) (k a : ℝ) (φ : Model m → ℝ)
    (p : Model m) :
    fderiv ℝ (fieldLyapunov σ k) p (cancelledDescent σ a φ p) =
      (cancelledDescent σ a φ p).1 - 2 * k * transverseEnergy σ p := by
  rw [(hasFDerivAt_fieldLyapunov σ k p).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
  change
    (cancelledDescent σ a φ p).1 + k * (∑ i, 2 * σ i * p.2 i * (cancelledDescent σ a φ p).2 i) = _
  have hsum :
    (∑ i, 2 * σ i * p.2 i * (cancelledDescent σ a φ p).2 i) = -2 * transverseEnergy σ p := by
    rw [transverseEnergy, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change 2 * σ i * p.2 i * (-σ i * p.2 i) = _
    ring
  rw [hsum]
  ring

private theorem MorseCancel.exists_compact_fieldLyapunov {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0)
    {a : ℝ} (ha : 0 < a) {φ : Model m → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφnonneg : ∀ p, 0 ≤ φ p)
    (hone : ∀ s ∈ Set.Icc (-a) a, φ (s, 0) = 1) {C : Set (Model m)} (hC : IsCompact C) :
    ∃ k : ℝ,
      0 ≤ k ∧
        ContDiff ℝ ∞ (fieldLyapunov σ k) ∧
          ∀ p ∈ C, fderiv ℝ (fieldLyapunov σ k) p (cancelledDescent σ a φ p) < 0 := by
  let O : ℕ → Set (Model m) := fun n =>
    {p | (cancelledDescent σ a φ p).1 - 2 * (n : ℝ) * transverseEnergy σ p < 0}
  have henergy : Continuous (transverseEnergy σ) := by
    unfold transverseEnergy
    fun_prop
  have hO (n : ℕ) : IsOpen (O n) :=
    isOpen_lt
      ((contDiff_cancelledDescent σ a hφ).continuous.fst.sub (continuous_const.mul henergy))
      continuous_const
  have hcover : C ⊆ ⋃ n, O n := by
    intro p hp
    by_cases hz : p.2 = 0
    · apply Set.mem_iUnion.mpr
      refine ⟨0, ?_⟩
      have he : p = (p.1, (0 : Fin m → ℝ)) := Prod.ext rfl hz
      have hh := cancelledDescent_axis_negative σ ha hφnonneg hone p.1
      have hneg : (cancelledDescent σ a φ p).1 < 0 :=
        (congrArg (fun q : Model m => (cancelledDescent σ a φ q).1) he).trans_lt hh
      simpa only [O, Set.mem_ofPred_eq, Nat.cast_zero, MulZeroClass.mul_zero,
        MulZeroClass.zero_mul, sub_zero] using hneg
    · have hpos : 0 < transverseEnergy σ p :=
        lt_of_le_of_ne (transverseEnergy_nonneg σ p)
          (Ne.symm (fun he => hz ((transverseEnergy_zero_iff σ hσ p).mp he)))
      obtain ⟨n, hn⟩ := exists_nat_gt ((cancelledDescent σ a φ p).1 / (2 * transverseEnergy σ p))
      have hh := (div_lt_iff₀ (mul_pos (by norm_num) hpos)).mp hn
      apply Set.mem_iUnion.mpr
      refine ⟨n, ?_⟩
      change (cancelledDescent σ a φ p).1 - 2 * (n : ℝ) * transverseEnergy σ p < 0
      nlinarith
  have hmono : Monotone O := by
    intro i j hij p hp
    have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    have he := transverseEnergy_nonneg σ p
    change (cancelledDescent σ a φ p).1 - 2 * (i : ℝ) * transverseEnergy σ p < 0 at hp
    change (cancelledDescent σ a φ p).1 - 2 * (j : ℝ) * transverseEnergy σ p < 0
    nlinarith
  obtain ⟨n, hn⟩ :=
    hC.elim_directed_cover O hO hcover
      (fun i j => ⟨Max.max i j, hmono (le_max_left i j), hmono (le_max_right i j)⟩)
  refine ⟨n, by positivity, contDiff_fieldLyapunov σ n, ?_⟩
  intro p hp
  rw [fieldLyapunov_speed]
  exact hn hp

private theorem MorseCancel.exists_compact_lyapunov_residence {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] {L : D → ℝ} {W : D → D} (hL : ContDiff ℝ ∞ L) (hW : Continuous W)
    {C : Set D} (hC : IsCompact C) (hneg : ∀ x ∈ C, fderiv ℝ L x (W x) < 0) :
    ∃ T : ℝ,
      0 < T ∧
        ∀ γ : ℝ → D,
          (∀ t ∈ Set.Icc (0 : ℝ) T, γ t ∈ C → HasDerivAt γ (W (γ t)) t) →
            ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ C := by
  by_cases hne : C.Nonempty
  swap
  · exact ⟨1, zero_lt_one, fun γ _ => ⟨0, ⟨le_rfl, zero_le_one⟩, fun h => hne ⟨γ 0, h⟩⟩⟩
  have hspeed : Continuous (fun x => fderiv ℝ L x (W x)) :=
    (hL.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk hW)
  obtain ⟨v, hv, hmaxspeed⟩ := hC.exists_isMaxOn hne hspeed.continuousOn
  let δ := -fderiv ℝ L v (W v)
  have hδ : 0 < δ := neg_pos.mpr (hneg v hv)
  have hbound (x : D) (hx : x ∈ C) : fderiv ℝ L x (W x) ≤ -δ := by
    have hh : fderiv ℝ L x (W x) ≤ fderiv ℝ L v (W v) := hmaxspeed hx
    simpa only [δ, neg_neg] using hh
  obtain ⟨p, hp, hmin⟩ := hC.exists_isMinOn hne hL.continuous.continuousOn
  obtain ⟨q, hq, hmax⟩ := hC.exists_isMaxOn hne hL.continuous.continuousOn
  let T := (L q - L p + 1) / δ
  have hpq : L p ≤ L q := hmax hp
  have hT : 0 < T := div_pos (by linarith) hδ
  have hδT : δ * T = L q - L p + 1 := by
    dsimp [T]
    field_simp [hδ.ne']
  refine ⟨T, hT, ?_⟩
  intro γ hγ
  by_contra! hstay
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasDerivAt (fun u => L (γ u)) (fderiv ℝ L (γ t) (W (γ t))) t :=
    (hL.differentiable (by simp) (γ t)).hasFDerivAt.comp_hasDerivAt t (hγ t ht (hstay t ht))
  have hcont : ContinuousOn (fun t => L (γ t)) (Set.Icc (0 : ℝ) T) := fun t ht =>
    (hd t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun t => L (γ t)) (Set.Icc (0 : ℝ) T) := fun t ht =>
    (hd t ht).differentiableAt.differentiableWithinAt
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT.le⟩
  have hlast : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have hdrop :=
    (convex_Icc (0 : ℝ) T).image_sub_le_mul_sub_of_deriv_le hcont (hdiff.mono interior_subset)
      (fun t ht => by
        rw [(hd t (interior_subset ht)).deriv]
        exact hbound (γ t) (hstay t (interior_subset ht)))
      0 h0 T hlast hT.le
  simp only [sub_zero, neg_mul] at hdrop
  rw [hδT] at hdrop
  have hlo : L p ≤ L (γ T) := hmin (hstay T hlast)
  have hhi : L (γ 0) ≤ L q := hmax (hstay 0 h0)
  linarith

private theorem
    MorseCancel.hasDerivAt_partialChart_integralCurve {D E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, D) M D ∞) (W : D → D)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {γ : ℝ → M} (hγ : IsMIntegralCurve γ V) {t : ℝ}
    (ht : γ t ∈ e.source) (hV : V (γ t) = Smale.FlowConstruction.partialChartField e W (γ t)) :
    HasDerivAt (e ∘ γ) (W (e (γ t))) t := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, D) :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have hinv := he.comp_symm_deriv (e'.map_source ht)
  rw [e'.left_inv ht] at hinv
  have hd := (he.mdifferentiableAt ht).hasMFDerivAt.comp t (hγ t)
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasMFDerivAt_iff_hasFDerivAt.mp
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, D) e (γ t) ((NormedSpace.fromTangentSpace t r) • V (γ t)) =
      (NormedSpace.fromTangentSpace t r) •
        (NormedSpace.fromTangentSpace (e (γ t))).symm (W (e (γ t)))
  rw [map_smul, hV, Smale.FlowConstruction.partialChartField_eq_mfderiv_symm e W ht]
  have hv := congrArg (fun A : D →L[ℝ] D => A (W (e (γ t)))) hinv
  exact congrArg (fun v => (NormedSpace.fromTangentSpace t r) • v) hv

private theorem MorseCancel.exists_native_compact_lyapunov_residence {D E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (Φ : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, E) D M ∞)
    {L : D → ℝ} {W : D → D} (hL : ContDiff ℝ ∞ L) (hW : Continuous W) {C : Set D}
    (hC : IsCompact C) (hsource : C ⊆ Φ.source) (hneg : ∀ x ∈ C, fderiv ℝ L x (W x) < 0)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ∀ x ∈ Φ '' C, V x = Smale.FlowConstruction.partialChartField Φ.symm W x) :
    ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ Φ '' C := by
  obtain ⟨T, hT, hTbound⟩ := exists_compact_lyapunov_residence hL hW hC hneg
  refine ⟨T, hT, ?_⟩
  intro γ hγ
  by_contra! hstay
  have hcoords (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) : Φ.symm (γ t) ∈ C := by
    obtain ⟨z, hz, he⟩ := hstay t ht
    have hh : Φ.symm (Φ z) = z := Φ.left_inv' (hsource hz)
    rw [← he, hh]
    exact hz
  obtain ⟨t, ht, hout⟩ :=
    hTbound (Φ.symm ∘ γ)
      (fun t ht _ =>
        hasDerivAt_partialChart_integralCurve Φ.symm W hγ
          (by
            obtain ⟨z, hz, he⟩ := hstay t ht
            exact he ▸ Φ.map_source' (hsource hz))
          (hV (γ t) (hstay t ht)))
  exact hout (hcoords t ht)

private theorem MorseCancel.exists_native_cancelledDescent_residence_bound {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {m : ℕ}
    (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞) {φ : Model m → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφnonneg : ∀ p, 0 ≤ φ p) (hone : ∀ s ∈ Set.Icc (-a) a, φ (s, 0) = 1)
    {C : Set (Model m)} (hC : IsCompact C) (hsource : C ⊆ Φ.source)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV :
      ∀ x ∈ Φ '' C,
        V x = Smale.FlowConstruction.partialChartField Φ.symm (cancelledDescent σ a φ) x) :
    ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ Φ '' C := by
  obtain ⟨k, -, hL, hneg⟩ := exists_compact_fieldLyapunov σ hσ ha hφ hφnonneg hone hC
  exact
    exists_native_compact_lyapunov_residence Φ hL (contDiff_cancelledDescent σ a hφ).continuous hC
      hsource hneg hV

private theorem
    MorseCancel.exists_native_cubic_field_finite_passage {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i ≠ 0) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} {N U : Set M} (hN : IsOpen N)
    (hNU : N ⊆ U) (haxisN : ∀ s ∈ Set.Icc (-a) a, Φ (s, 0) ∈ N) {C : Set (Model m)}
    (hC : IsCompact C) (hCΦ : C ⊆ Φ.source) (hUC : U ⊆ Φ '' C)
    (hneg : ∀ x, f x ∈ Set.Icc c d → x ∉ N → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hnoreturn : ∀ x ∈ N, ∀ t : ℝ, 0 ≤ t → F t x ∈ N → ∀ s ∈ Set.Icc (0 : ℝ) t, F s x ∈ U) :
    ∃ (K : Set M) (V' : (x : M) → TangentSpace 𝓘(ℝ, E) x),
      IsCompact K ∧
        K ⊆ N ∧
          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
            (∀ x, V' x = 0 ↔ V x = 0 ∧ x ≠ Φ (a, 0) ∧ x ≠ Φ (-a, 0)) ∧
              (∀ x ∉ K, ∀ᶠ y in 𝓝 x, V' y = V y) ∧
                ∃ T : ℝ,
                  0 < T ∧
                    ∀ γ : ℝ → M,
                      IsMIntegralCurve γ V' → ∃ t ∈ Set.Icc (0 : ℝ) T, f (γ t) ∉ Set.Icc c d := by
  obtain ⟨φ, hφ, hc, hsupp, hsuppN, hrange, hone, V', hV', heq, hzero, hkeep⟩ :=
    exists_native_cubic_field_cancellation_in σ hσ ha Φ haxis V hV hmodel hN haxisN
  have hK : IsCompact (Φ '' tsupport φ) :=
    hc.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hsupp)
  obtain ⟨T₀, hT₀, hres⟩ :=
    exists_native_cancelledDescent_residence_bound σ hσ ha Φ hφ (fun p => (hrange p).1) hone hC
      hCΦ
      (fun x hx =>
        heq x
          (by
            obtain ⟨z, hz, rfl⟩ := hx
            exact Φ.map_source' (hCΦ hz)))
  have hinner :
    ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V' → ∃ t ∈ Set.Icc (0 : ℝ) T, γ t ∉ U := by
    refine ⟨T₀, hT₀, ?_⟩
    intro γ hγ
    obtain ⟨t, ht, hout⟩ := hres γ hγ
    exact ⟨t, ht, fun h => hout (hUC h)⟩
  refine ⟨Φ '' tsupport φ, V', hK, hsuppN, hV', hzero, hkeep, ?_⟩
  exact
    Degree.FlowCancellation.exists_perturbed_band_residence hf hV hV' F hcurve hK.isClosed hN
      hsuppN hNU (fun x hx => (hkeep x hx).self_of_nhds) hneg hnoreturn hinner

private theorem MorseCancel.native_cubic_axis_flow {m : ℕ} {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) (t : ℝ) :
    F t (Φ (0, 0)) = Φ (cubicModelOrbit a t) := by
  have hmem (s : ℝ) : cubicModelOrbit a s ∈ Φ.source := by
    have hs := cubicAxisParameter_mem ha s
    exact haxis ⟨⟨hs.1.le, hs.2.le⟩, rfl⟩
  have hΓ : IsMIntegralCurve (Φ ∘ cubicModelOrbit a) V := by
    intro s
    have hd :=
      Smale.FlowConstruction.hasMFDerivAt_lift_partialChartCurve Φ.symm
        (cubicDescent σ (-(a ^ 2))) (hasDerivAt_cubicModelOrbit σ a s) (hmem s)
    have he := hmodel (Φ (cubicModelOrbit a s)) (Φ.map_source' (hmem s))
    change
      HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ ∘ cubicModelOrbit a) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (nativeCubicDescent σ Φ (-(a ^ 2)) (Φ (cubicModelOrbit a s)))) at hd
    rw [← he] at hd
    exact hd
  have hinit : F 0 (Φ (0, 0)) = (Φ ∘ cubicModelOrbit a) 0 := by
    simp only [F.map_zero_apply, Function.comp_apply, cubicModelOrbit_zero]
    rfl
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hV (hcurve (Φ (0, 0))) hΓ hinit
  exact congrFun heq t

private theorem MorseCancel.native_cubic_axis_orbit {m : ℕ} {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) :
    Set.range (fun t : ℝ => F t (Φ (0, 0))) = Φ '' (Set.Ioo (-a) a ×ˢ {(0 : Fin m → ℝ)}) ∧
      Filter.Tendsto (fun t : ℝ => F t (Φ (0, 0))) Filter.atTop (𝓝 (Φ (a, 0))) ∧
        Filter.Tendsto (fun t : ℝ => F t (Φ (0, 0))) Filter.atBot (𝓝 (Φ (-a, 0))) := by
  have heq : (fun t : ℝ => F t (Φ (0, 0))) = Φ ∘ cubicModelOrbit a :=
    funext (native_cubic_axis_flow σ ha Φ haxis hV hmodel F hcurve)
  have hp : (a, (0 : Fin m → ℝ)) ∈ Φ.source := haxis ⟨⟨by linarith, le_rfl⟩, rfl⟩
  have hq : (-a, (0 : Fin m → ℝ)) ∈ Φ.source := haxis ⟨⟨le_rfl, by linarith⟩, rfl⟩
  rw [heq]
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.range_comp, range_cubicModelOrbit ha]
  · exact
      (Φ.mdifferentiableAt (by simp) hp).continuousAt.tendsto.comp
        (tendsto_cubicModelOrbit_atTop ha)
  · exact
      (Φ.mdifferentiableAt (by simp) hq).continuousAt.tendsto.comp
        (tendsto_cubicModelOrbit_atBot ha)

private theorem MorseCancel.native_cubic_closed_axis {m : ℕ} {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1 (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) :
    Φ '' (Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)}) =
      Insert.insert (Φ (a, 0))
        (Insert.insert (Φ (-a, 0)) (Set.range (fun t : ℝ => F t (Φ (0, 0))))) := by
  rw [(native_cubic_axis_orbit σ ha Φ haxis hV hmodel F hcurve).1]
  ext x
  constructor
  · rintro ⟨⟨s, z⟩, ⟨hs, hz⟩, rfl⟩
    have hz0 : z = 0 := hz
    subst z
    by_cases hsright : s = a
    · exact Or.inl (congrArg (fun r => Φ (r, 0)) hsright)
    by_cases hsleft : s = -a
    · exact Or.inr (Or.inl (congrArg (fun r => Φ (r, 0)) hsleft))
    · exact
        Or.inr
          (Or.inr
            ⟨(s, 0), ⟨⟨lt_of_le_of_ne hs.1 (Ne.symm hsleft), lt_of_le_of_ne hs.2 hsright⟩, rfl⟩,
              rfl⟩)
  · rintro (hx | hx | hx)
    · exact ⟨(a, 0), ⟨⟨by linarith, le_rfl⟩, rfl⟩, hx.symm⟩
    · exact ⟨(-a, 0), ⟨⟨le_rfl, by linarith⟩, rfl⟩, hx.symm⟩
    · obtain ⟨⟨s, z⟩, ⟨hs, hz⟩, he⟩ := hx
      exact ⟨(s, z), ⟨⟨hs.1.le, hs.2.le⟩, hz⟩, he⟩

private theorem Degree.FlowCancellation.exists_uniform_directed_band_crossing {X : Type*}
    [TopologicalSpace X] (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hlower : ∀ x, f x = c → D x < 0) (hupper : ∀ x, f x = d → D x < 0)
    (hres : ∃ T : ℝ, 0 < T ∧ ∀ x, ∃ t ∈ Set.Icc (0 : ℝ) T, f (F t x) ∉ Set.Icc c d) :
    ∃ T : ℝ, 0 < T ∧ (∀ x, f x ≤ d → f (F T x) < c) ∧ ∀ x, c ≤ f x → d < f (F (-T) x) := by
  obtain ⟨T, hT, hexit⟩ := hres
  have hforward : ∀ x, f x ≤ d → f (F T x) < c := by
    intro x hx
    obtain ⟨t, ht, hout⟩ := hexit x
    have hhi := forwardInvariant_sublevel_of_boundary F hf hD hder hupper x hx t ht.1
    have hlo : f (F t x) < c := lt_of_not_ge (fun h => hout ⟨h, hhi⟩)
    rcases ht.2.eq_or_lt with he | he
    · simpa only [he] using hlo
    · have hh :=
        strict_sublevel_entry_of_boundary F hf hD hder hlower (F t x) hlo.le (T - t)
          (sub_pos.mpr he)
      simpa only [← F.map_add, sub_add_cancel] using hh
  refine ⟨T, hT, hforward, ?_⟩
  intro x hx
  apply lt_of_not_ge
  intro hback
  have hh := hforward (F (-T) x) hback
  rw [← F.map_add, add_neg_cancel, F.map_zero_apply] at hh
  exact (not_lt_of_ge hx) hh

private theorem Degree.FlowCancellation.continuousOn_band_entryTime {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hlower : ∀ x, f x = c → D x < 0) (hupper : ∀ x, f x = d → D x < 0)
    (hres : ∃ T : ℝ, 0 < T ∧ ∀ x, ∃ t ∈ Set.Icc (0 : ℝ) T, f (F t x) ∉ Set.Icc c d) :
    ContinuousOn (Smale.FlowConstruction.entryTime F {x | f x ≤ c}) {x | f x ≤ d} := by
  obtain ⟨T, hT, hforward, -⟩ :=
    exists_uniform_directed_band_crossing F hf hD hder hlower hupper hres
  have hclosed : IsClosed {x | f x ≤ c} := isClosed_le hf continuous_const
  have hentry : ∀ x ∈ {y | f y ≤ c}, ∀ t : ℝ, 0 < t → F t x ∈ interior {y | f y ≤ c} := by
    intro x hx t ht
    have hh := strict_sublevel_entry_of_boundary F hf hD hder hlower x hx t ht
    exact
      Eq.mpr
        (congrArg (fun S : Set X => F t x ∈ S)
          (interior_sublevel_eq_of_boundary F hf hder hlower))
        hh
  exact
    Smale.FlowConstruction.continuousOn_entryTime F hclosed
      (forwardInvariant_sublevel_of_boundary F hf hD hder hlower) hentry
      (fun x hx => ⟨T, hT.le, (hforward x hx).le⟩)

private theorem Degree.FlowCancellation.exists_native_flow_band_crossing {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    {c d : ℝ} (hlower : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hupper : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hres :
      ∃ T : ℝ,
        0 < T ∧
          ∀ γ : ℝ → M, IsMIntegralCurve γ V → ∃ t ∈ Set.Icc (0 : ℝ) T, f (γ t) ∉ Set.Icc c d) :
    ∃ F : Flow ℝ M,
      (∀ x, IsMIntegralCurve (fun t => F t x) V) ∧
        (∃ T : ℝ, 0 < T ∧ (∀ x, f x ≤ d → f (F T x) < c) ∧ ∀ x, c ≤ f x → d < f (F (-T) x)) ∧
          ContinuousOn (Smale.FlowConstruction.entryTime F {x | f x ≤ c}) {x | f x ≤ d} := by
  have hV₁ := hV.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  let F := Smale.FlowConstruction.compactFlow hV₁
  have hcurve (x : M) : IsMIntegralCurve (fun t => F t x) V :=
    Smale.FlowConstruction.isMIntegralCurve_compactFlow hV₁ x
  let D (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  have hD : Continuous D := (MorseCancel.contMDiff_directionalDerivative hf hV).continuous
  have hder (x : M) (t : ℝ) : HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t :=
    Smale.FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) t
  have hres' : ∃ T : ℝ, 0 < T ∧ ∀ x, ∃ t ∈ Set.Icc (0 : ℝ) T, f (F t x) ∉ Set.Icc c d := by
    obtain ⟨T, hT, hbound⟩ := hres
    exact ⟨T, hT, fun x => hbound (fun t => F t x) (hcurve x)⟩
  exact
    ⟨F, hcurve, exists_uniform_directed_band_crossing F hf.continuous hD hder hlower hupper hres',
      continuousOn_band_entryTime F hf.continuous hD hder hlower hupper hres'⟩

private theorem
    MorseCancel.exists_cubic_connection_finite_passage {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i ≠ 0) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f))
    (hp : Φ (a, 0) ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hq : Φ (-a, 0) ∈ Smale.ManifoldMorse.criticalPoints E f) (hpq : f (Φ (a, 0)) < f (Φ (-a, 0)))
    {c d : ℝ} (hc : c < f (Φ (a, 0))) (hd : f (Φ (-a, 0)) < d)
    (hpair :
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
        f x ∈ Set.Icc c d → x = Φ (a, 0) ∨ x = Φ (-a, 0))
    (hunique :
      ∀ x ∉ Smale.ManifoldMorse.criticalPoints E f,
        Filter.Tendsto (fun t : ℝ => F t x) Filter.atBot (𝓝 (Φ (-a, 0))) →
          Filter.Tendsto (fun t : ℝ => F t x) Filter.atTop (𝓝 (Φ (a, 0))) →
            ∃ t : ℝ, F t (Φ (0, 0)) = x) :
    ∃ (K : Set M) (V' : (x : M) → TangentSpace 𝓘(ℝ, E) x),
      IsCompact K ∧
        K ⊆ Φ.target ∩ f ⁻¹' Set.Ioo c d ∧
          ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
            (∀ x, V' x = 0 ↔ V x = 0 ∧ x ≠ Φ (a, 0) ∧ x ≠ Φ (-a, 0)) ∧
              (∀ x ∉ K, ∀ᶠ y in 𝓝 x, V' y = V y) ∧
                (∃ T : ℝ,
                    0 < T ∧
                      ∀ γ : ℝ → M,
                        IsMIntegralCurve γ V' → ∃ t ∈ Set.Icc (0 : ℝ) T, f (γ t) ∉ Set.Icc c d) ∧
                  ∃ G : Flow ℝ M,
                    (∀ x, IsMIntegralCurve (fun t => G t x) V') ∧
                      (∃ T : ℝ,
                          0 < T ∧
                            (∀ x, f x ≤ d → f (G T x) < c) ∧ ∀ x, c ≤ f x → d < f (G (-T) x)) ∧
                        ContinuousOn (Smale.FlowConstruction.entryTime G {x | f x ≤ c})
                          {x | f x ≤ d} := by
  have hV₁ := hV.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  obtain ⟨hrange, htop, hbot⟩ := native_cubic_axis_orbit σ ha Φ haxis hV₁ hmodel F hcurve
  have hclosed := native_cubic_closed_axis σ ha Φ haxis hV₁ hmodel F hcurve
  have hmono := Smale.FlowConstruction.antitone_flow_height hf F hcurve hzero hdesc (Φ (0, 0))
  have hztop := hf.continuous.continuousAt.tendsto.comp htop
  have hzbot := hf.continuous.continuousAt.tendsto.comp hbot
  have hzband (t : ℝ) : f (F t (Φ (0, 0))) ∈ Set.Icc (f (Φ (a, 0))) (f (Φ (-a, 0))) :=
    ⟨hmono.le_of_tendsto hztop t, hmono.ge_of_tendsto hzbot t⟩
  let A := Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)}
  have hAband : Φ '' A ⊆ f ⁻¹' Set.Ioo c d := by
    intro x hx
    rw [hclosed] at hx
    rcases hx with hx | hx | ⟨t, ht⟩
    · rw [hx]
      exact ⟨hc, lt_trans hpq hd⟩
    · rw [hx]
      exact ⟨lt_trans hc hpq, hd⟩
    · rw [← ht]
      exact ⟨lt_of_lt_of_le hc (hzband t).1, lt_of_le_of_lt (hzband t).2 hd⟩
  have hopen : IsOpen (Φ.source ∩ Φ ⁻¹' (f ⁻¹' Set.Ioo c d)) :=
    Φ.toOpenPartialHomeomorph.isOpen_inter_preimage (isOpen_Ioo.preimage hf.continuous)
  have hAsub : A ⊆ Φ.source ∩ Φ ⁻¹' (f ⁻¹' Set.Ioo c d) := fun x hx =>
    ⟨haxis hx, hAband ⟨x, hx, rfl⟩⟩
  obtain ⟨C, hC, hAC, hCsub⟩ :=
    exists_compact_between
      (show IsCompact A from CompactIccSpace.isCompact_Icc.prod isCompact_singleton) hopen hAsub
  have hCΦ : C ⊆ Φ.source := fun x hx => (hCsub hx).1
  let U := Φ '' interior C
  have hU : IsOpen U :=
    Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_interior
      (fun x hx => hCΦ (interior_subset hx))
  have hAU : Φ '' A ⊆ U := Set.image_mono hAC
  have hpU : Φ (a, (0 : Fin m → ℝ)) ∈ U := hAU ⟨(a, 0), ⟨⟨by linarith, le_rfl⟩, rfl⟩, rfl⟩
  have hqU : Φ (-a, (0 : Fin m → ℝ)) ∈ U := hAU ⟨(-a, 0), ⟨⟨le_rfl, by linarith⟩, rfl⟩, rfl⟩
  have hzU (t : ℝ) : F t (Φ (0, 0)) ∈ U := by
    apply hAU
    rw [hclosed]
    exact Or.inr (Or.inr ⟨t, rfl⟩)
  obtain ⟨N, hN, hNU, hpN, hqN, hzN, hnoreturn⟩ :=
    Degree.FlowCancellation.exists_native_connection_no_return hf hV F hcurve hzero hdesc hinj hp
      hq hpq (fun x hx hh => hpair x hx ⟨le_trans hc.le hh.1, le_trans hh.2 hd.le⟩) hzband hunique
      hU hpU hqU hzU
  have haxisN (s : ℝ) (hs : s ∈ Set.Icc (-a) a) : Φ (s, (0 : Fin m → ℝ)) ∈ N := by
    have hh : Φ (s, (0 : Fin m → ℝ)) ∈ Φ '' A := ⟨(s, 0), ⟨hs, rfl⟩, rfl⟩
    rw [hclosed] at hh
    rcases hh with hh | hh | ⟨t, ht⟩
    · exact hh ▸ hpN
    · exact hh ▸ hqN
    · exact ht ▸ hzN t
  have hneg (x : M) (hx : f x ∈ Set.Icc c d) (hout : x ∉ N) : mvfderiv 𝓘(ℝ, E) f x (V x) < 0 := by
    apply hdesc x
    intro hcrit
    rcases hpair x hcrit hx with he | he
    · exact hout (he ▸ hpN)
    · exact hout (he ▸ hqN)
  obtain ⟨K, V', hK, hKN, hV', hzeros, hkeep, hpass⟩ :=
    exists_native_cubic_field_finite_passage σ hσ ha Φ haxis hf V hV hmodel F hcurve hN hNU haxisN
      hC hCΦ (Set.image_mono interior_subset) hneg hnoreturn
  have hKsub : K ⊆ Φ.target ∩ f ⁻¹' Set.Ioo c d := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hNU (hKN hx)
    exact ⟨Φ.map_source' (hCΦ (interior_subset hz)), (hCsub (interior_subset hz)).2⟩
  have hcd : c ≤ d := by linarith
  have hboundary (x : M) (hx : f x = c ∨ f x = d) : mvfderiv 𝓘(ℝ, E) f x (V' x) < 0 := by
    have hxK : x ∉ K := by
      intro hxK
      have hh : f x ∈ Set.Ioo c d := (hKsub hxK).2
      rcases hx with hx | hx <;> rw [hx] at hh
      · exact (lt_irrefl c) hh.1
      · exact (lt_irrefl d) hh.2
    have hreg : x ∉ Smale.ManifoldMorse.criticalPoints E f := by
      intro hcrit
      have hxb : f x ∈ Set.Icc c d := by
        rcases hx with hx | hx <;> rw [hx]
        · exact ⟨le_rfl, hcd⟩
        · exact ⟨hcd, le_rfl⟩
      rcases hpair x hcrit hxb with he | he
      · rw [he] at hx
        rcases hx with hx | hx <;> linarith
      · rw [he] at hx
        rcases hx with hx | hx <;> linarith
    rw [(hkeep x hxK).self_of_nhds]
    exact hdesc x hreg
  refine ⟨K, V', hK, hKsub, hV', hzeros, hkeep, hpass, ?_⟩
  exact
    Degree.FlowCancellation.exists_native_flow_band_crossing hf hV'
      (fun x hx => hboundary x (Or.inl hx)) (fun x hx => hboundary x (Or.inr hx)) hpass

private theorem Degree.FlowCancellation.hasDerivAt_comp_native_integralCurve_at {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {γ : ℝ → M} {t : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (γ t)) (hγ : IsMIntegralCurve γ V) :
    HasDerivAt (f ∘ γ) (mvfderiv 𝓘(ℝ, E) f (γ t) (V (γ t))) t := by
  have hd := hf.hasMFDerivAt.comp t (hγ t)
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasMFDerivAt_iff_hasFDerivAt.mp
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change
    (mvfderiv 𝓘(ℝ, E) f (γ t)) ((NormedSpace.fromTangentSpace t r) • V (γ t)) =
      (NormedSpace.fromTangentSpace t r) • (mvfderiv 𝓘(ℝ, E) f (γ t)) (V (γ t))
  exact map_smul _ _ _

private theorem
    Degree.FlowCancellation.mvfderiv_signedLevelTime {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ}
    (hboundary : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) {x : M}
    (hx : x ∈ levelBasin F f c) : mvfderiv 𝓘(ℝ, E) (signedLevelTime F f c) x (V x) = -1 := by
  obtain ⟨hB, hsmooth, hshift⟩ := smooth_signed_level_time hf hV F hcurve hboundary
  have hlocal := (hsmooth x hx).contMDiffAt (hB.mem_nhds hx)
  have hlocal0 : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (signedLevelTime F f c) (F 0 x) := by
    rw [F.map_zero_apply]
    exact hlocal.mdifferentiableAt (by simp)
  have hd := hasDerivAt_comp_native_integralCurve_at hlocal0 (hcurve x)
  have heq :
    (signedLevelTime F f c ∘ (fun t => F t x)) = fun t : ℝ => signedLevelTime F f c x - t :=
    funext (hshift x hx)
  rw [heq] at hd
  have hh := hd.unique ((hasDerivAt_id (0 : ℝ)).const_sub (signedLevelTime F f c x))
  have he :=
    congrArg (fun y : M => mvfderiv 𝓘(ℝ, E) (signedLevelTime F f c) y (V y)) (F.map_zero_apply x)
  exact he.symm.trans hh

private def Degree.FlowCancellation.crossingBasin {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    (f : X → ℝ) (c d : ℝ) : Set X :=
  levelBasin F f c ∩ levelBasin F f d

private def Degree.FlowCancellation.crossingDuration {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    (f : X → ℝ) (c d : ℝ) (x : X) : ℝ :=
  signedLevelTime F f c x - signedLevelTime F f d x

private def Degree.FlowCancellation.flowBandHeight {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    (f : X → ℝ) (c d : ℝ) (x : X) : ℝ :=
  c + (d - c) * signedLevelTime F f c x / crossingDuration F f c d x

private theorem Degree.FlowCancellation.crossingDuration_pos {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hc : ∀ x, f x = c → D x < 0) (hcd : c < d) {x : X} (hx : x ∈ crossingBasin F f c d) :
    0 < crossingDuration F f c d x := by
  apply sub_pos.mpr
  by_contra h
  have hle := le_of_not_gt h
  have hh :=
    forwardInvariant_sublevel_of_boundary F hf hD hder hc (F (signedLevelTime F f c x) x)
      (signedLevelTime_hits F f c hx.1).le (signedLevelTime F f d x - signedLevelTime F f c x)
      (sub_nonneg.mpr hle)
  rw [← F.map_add, sub_add_cancel, signedLevelTime_hits F f d hx.2] at hh
  exact (not_le_of_gt hcd) hh

private theorem Degree.FlowCancellation.crossingDuration_flow {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hc : ∀ x, f x = c → D x < 0) (hd : ∀ x, f x = d → D x < 0) {x : X}
    (hx : x ∈ crossingBasin F f c d) (s : ℝ) :
    crossingDuration F f c d (F s x) = crossingDuration F f c d x := by
  simp only [crossingDuration, signedLevelTime_flow F hf hD hder hc hx.1 s,
    signedLevelTime_flow F hf hD hder hd hx.2 s]
  ring

private theorem Degree.FlowCancellation.flowBandHeight_flow {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hc : ∀ x, f x = c → D x < 0) (hd : ∀ x, f x = d → D x < 0) {x : X}
    (hx : x ∈ crossingBasin F f c d) (s : ℝ) :
    flowBandHeight F f c d (F s x) =
      flowBandHeight F f c d x - ((d - c) / crossingDuration F f c d x) * s := by
  simp only [flowBandHeight, crossingDuration_flow F hf hD hder hc hd hx s,
    signedLevelTime_flow F hf hD hder hc hx.1 s]
  ring

private theorem Degree.FlowCancellation.flowBandHeight_lower {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hc : ∀ x, f x = c → D x < 0) {x : X} (hx : f x = c) : flowBandHeight F f c d x = c := by
  simp only [flowBandHeight, signedLevelTime_eq_zero F hf hD hder hc hx, MulZeroClass.mul_zero,
    zero_div, add_zero]

private theorem Degree.FlowCancellation.flowBandHeight_upper {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t) {c d : ℝ}
    (hc : ∀ x, f x = c → D x < 0) (hd : ∀ x, f x = d → D x < 0) (hcd : c < d) {x : X}
    (hx : x ∈ crossingBasin F f c d) (hfx : f x = d) : flowBandHeight F f c d x = d := by
  have hz := signedLevelTime_eq_zero F hf hD hder hd hfx
  have hpos := crossingDuration_pos F hf hD hder hc hcd hx
  have heq : signedLevelTime F f c x = crossingDuration F f c d x := by
    simp only [crossingDuration, hz, sub_zero]
  rw [flowBandHeight, heq, mul_div_cancel_right₀ _ hpos.ne']
  ring

private theorem Degree.FlowCancellation.smooth_flowBandHeight {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} (hcd : c < d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hd : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) :
    IsOpen (crossingBasin F f c d) ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (flowBandHeight F f c d) (crossingBasin F f c d) ∧
        ∀ x ∈ crossingBasin F f c d,
          mvfderiv 𝓘(ℝ, E) (flowBandHeight F f c d) x (V x) =
              -((d - c) / crossingDuration F f c d x) ∧
            mvfderiv 𝓘(ℝ, E) (flowBandHeight F f c d) x (V x) < 0 := by
  obtain ⟨hBc, htc, -⟩ := smooth_signed_level_time hf hV F hcurve hc
  obtain ⟨hBd, htd, -⟩ := smooth_signed_level_time hf hV F hcurve hd
  let D (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  have hD : Continuous D := (MorseCancel.contMDiff_directionalDerivative hf hV).continuous
  have hder (x : M) (t : ℝ) : HasDerivAt (fun s => f (F s x)) (D (F t x)) t :=
    Smale.FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) t
  have hB : IsOpen (crossingBasin F f c d) := hBc.inter hBd
  have hpos (x : M) (hx : x ∈ crossingBasin F f c d) : 0 < crossingDuration F f c d x :=
    crossingDuration_pos F hf.continuous hD hder hc hcd hx
  have hsc := htc.mono (Set.inter_subset_left : crossingBasin F f c d ⊆ levelBasin F f c)
  have hsd := htd.mono (Set.inter_subset_right : crossingBasin F f c d ⊆ levelBasin F f d)
  have hA : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (crossingDuration F f c d) (crossingBasin F f c d) :=
    hsc.sub hsd
  have hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (flowBandHeight F f c d) (crossingBasin F f c d) :=
    contMDiffOn_const.add ((contMDiffOn_const.mul hsc).div₀ hA (fun x hx => (hpos x hx).ne'))
  refine ⟨hB, hg, ?_⟩
  intro x hx
  have hlocal : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (flowBandHeight F f c d) (F 0 x) := by
    rw [F.map_zero_apply]
    exact ((hg x hx).contMDiffAt (hB.mem_nhds hx)).mdifferentiableAt (by simp)
  have hchain := hasDerivAt_comp_native_integralCurve_at hlocal (hcurve x)
  have heq :
    (flowBandHeight F f c d ∘ (fun t => F t x)) = fun t =>
      flowBandHeight F f c d x - ((d - c) / crossingDuration F f c d x) * t :=
    funext (fun t => flowBandHeight_flow F hf.continuous hD hder hc hd hx t)
  rw [heq] at hchain
  have hline :=
    ((hasDerivAt_id (0 : ℝ)).const_mul ((d - c) / crossingDuration F f c d x)).const_sub
      (flowBandHeight F f c d x)
  have hnative :
    mvfderiv 𝓘(ℝ, E) (flowBandHeight F f c d) x (V x) = -((d - c) / crossingDuration F f c d x) :=
    by
    have he :=
      congrArg (fun y : M => mvfderiv 𝓘(ℝ, E) (flowBandHeight F f c d) y (V y))
        (F.map_zero_apply x)
    exact he.symm.trans (by simpa using hchain.unique hline)
  exact ⟨hnative, hnative ▸ neg_neg_of_pos (div_pos (sub_pos.mpr hcd) (hpos x hx))⟩

private def Degree.FlowCancellation.logarithmicCoordinate (η L t : ℝ) : ℝ :=
  Real.log (1 + (t / η) ^ 2) / L

private theorem Degree.FlowCancellation.contDiff_logarithmicCoordinate (η L : ℝ) :
    ContDiff ℝ ∞ (logarithmicCoordinate η L) := by
  apply ContDiff.div_const
  apply ContDiff.log
  · exact contDiff_const.add ((contDiff_id.div_const η).pow 2)
  · intro t
    positivity

private theorem Degree.FlowCancellation.hasDerivAt_logarithmicCoordinate {η L : ℝ} (hη : 0 < η)
    (hL : 0 < L) (t : ℝ) :
    HasDerivAt (logarithmicCoordinate η L) (2 * t / (L * (η ^ 2 + t ^ 2))) t := by
  have hp : 1 + (t / η) ^ 2 ≠ 0 := by positivity
  have hh := (((((hasDerivAt_id t).div_const η).pow 2).const_add 1).log hp).div_const L
  convert hh using 1 <;> try rfl
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp

private theorem
    Degree.FlowCancellation.logarithmicCoordinate_weighted_deriv_bound {η L : ℝ} (hη : 0 < η)
    (hL : 0 < L) (t : ℝ) : |t * deriv (logarithmicCoordinate η L) t| ≤ 2 / L := by
  rw [(hasDerivAt_logarithmicCoordinate hη hL t).deriv]
  have hden : 0 < η ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hη) (sq_nonneg t)
  have heq : t * (2 * t / (L * (η ^ 2 + t ^ 2))) = (2 / L) * (t ^ 2 / (η ^ 2 + t ^ 2)) := by
    field_simp
  rw [heq, abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_right (by positivity) ((div_le_one hden).mpr (by nlinarith))

private theorem
    Degree.FlowCancellation.exists_logarithmic_cutoff {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ χ : ℝ → ℝ,
      ContDiff ℝ ∞ χ ∧
        HasCompactSupport χ ∧
          (∀ᶠ t in 𝓝 0, χ t = 1) ∧
            (∀ t, ε ≤ |t| → χ t = 0) ∧
              (∀ t, χ t ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ t, |t * deriv χ t| < δ := by
  obtain ⟨β, hβ, hcompact, hsupp, hone, hrange⟩ :=
    Smale.exists_compact_smooth_cutoff (K := {(0 : ℝ)}) (U := Metric.ball 0 1) isCompact_singleton
      Metric.isOpen_ball (by simp)
  obtain ⟨C, hC⟩ := hcompact.deriv.exists_bound_of_continuous (hβ.continuous_deriv (by simp))
  let B : ℝ := Max.max C 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound (t : ℝ) : |deriv β t| ≤ B := by
    have hh := hC t
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (by dsimp [B]; linarith [le_max_left C 0])
  let L : ℝ := 2 * B / δ + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hsmall : B * (2 / L) < δ := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hL).mpr
    dsimp [L]
    have hd : δ * (2 * B / δ) = 2 * B := by field_simp
    nlinarith
  let η : ℝ := ε / Real.exp L
  have hη : 0 < η := div_pos hε (Real.exp_pos L)
  let q := logarithmicCoordinate η L
  have hq : ContDiff ℝ ∞ q := contDiff_logarithmicCoordinate η L
  have hqzero : q 0 = 0 := by simp [q, logarithmicCoordinate]
  let χ : ℝ → ℝ := β ∘ q
  have hχ : ContDiff ℝ ∞ χ := hβ.comp hq
  have hout (t : ℝ) (ht : ε ≤ |t|) : χ t = 0 := by
    have hratio : Real.exp L ≤ |t / η| := by
      rw [abs_div, abs_of_pos hη, le_div_iff₀ hη]
      have he : Real.exp L * η = ε := by dsimp [η]; field_simp
      simpa only [he] using ht
    have heone : 1 ≤ Real.exp L := Real.one_le_exp_iff.mpr hL.le
    have hlower : L ≤ Real.log (1 + (t / η) ^ 2) := by
      apply (Real.le_log_iff_exp_le (by positivity)).mpr
      nlinarith [sq_abs (t / η)]
    have honeq : 1 ≤ q t := (le_div_iff₀ hL).mpr (by simpa using hlower)
    have hnotsupp : q t ∉ tsupport β := by
      intro hh
      have hball := hsupp hh
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] at hball
      linarith [hball.2]
    change β (q t) = 0
    exact image_eq_zero_of_notMem_tsupport hnotsupp
  have hcompactχ : HasCompactSupport χ := by
    apply HasCompactSupport.intro (CompactIccSpace.isCompact_Icc : IsCompact (Set.Icc (-ε) ε))
    intro t ht
    apply hout
    by_contra h
    have hh := abs_lt.mp (lt_of_not_ge h)
    exact ht ⟨hh.1.le, hh.2.le⟩
  have hnear : ∀ᶠ t in 𝓝 0, χ t = 1 := by
    have hb : ∀ᶠ r in 𝓝 (0 : ℝ), β r = 1 := by simpa only [nhdsSet_singleton] using hone
    have ht : Filter.Tendsto q (𝓝 0) (𝓝 0) := by
      have hh : Filter.Tendsto q (𝓝 0) (𝓝 (q 0)) := hq.continuous.continuousAt
      simpa only [hqzero] using hh
    exact ht.eventually hb
  refine ⟨χ, hχ, hcompactχ, hnear, hout, fun t => hrange (q t), ?_⟩
  intro t
  have hder : deriv χ t = deriv β (q t) * deriv q t :=
    ((hβ.differentiable (by simp)).differentiableAt.hasDerivAt.comp t
        (hq.differentiable (by simp)).differentiableAt.hasDerivAt).deriv
  rw [hder]
  have he : |t * (deriv β (q t) * deriv q t)| = |deriv β (q t)| * |t * deriv q t| := by
    rw [← abs_mul]; congr 1; ring
  rw [he]
  exact
    lt_of_le_of_lt
      (mul_le_mul (hbound _) (logarithmicCoordinate_weighted_deriv_bound hη hL t) (abs_nonneg _)
        hB.le)
      hsmall

private theorem
    Degree.FlowCancellation.deriv_eq_zero_of_nonneg_zero {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ)
    (hnonneg : ∀ t, 0 ≤ χ t) {t : ℝ} (ht : χ t = 0) : deriv χ t = 0 := by
  have hm : IsLocalMin χ t :=
    Filter.Eventually.of_forall
      (fun s => by
        change χ t ≤ χ s
        rw [ht]
        exact hnonneg s)
  exact hm.hasDerivAt_eq_zero (hχ t).hasDerivAt

private theorem Degree.FlowCancellation.weighted_blend_neg {α a b r s z μ C δ : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (ha : a ≤ -μ) (hb : b ≤ -μ) (hC : 0 ≤ C) (hr : |r| ≤ C * |s|)
    (hz : |s * z| ≤ δ) (hsmall : C * δ < μ) : b + α * (a - b) - z * r < 0 := by
  have hbase : b + α * (a - b) ≤ -μ := by
    nlinarith [mul_nonneg hα.1 (sub_nonneg.mpr ha),
      mul_nonneg (sub_nonneg.mpr hα.2) (sub_nonneg.mpr hb)]
  have herr : |z * r| ≤ C * δ :=
    calc
      |z * r| = |z| * |r| := abs_mul _ _
      _ ≤ |z| * (C * |s|) := (mul_le_mul_of_nonneg_left hr (abs_nonneg _))
      _ = C * |s * z| := by rw [abs_mul]; ring
      _ ≤ C * δ := mul_le_mul_of_nonneg_left hz hC
  linarith [neg_abs_le (z * r)]

private theorem
    Degree.FlowCancellation.hasDerivAt_flow_height_zero {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x) (F : Flow ℝ M)
    (hcurve : IsMIntegralCurve (fun t => F t x) V) :
    HasDerivAt (fun t => f (F t x)) (mvfderiv 𝓘(ℝ, E) f x (V x)) 0 := by
  have hf0 : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (F 0 x) := by
    rw [F.map_zero_apply]
    exact hf
  have hh := hasDerivAt_comp_native_integralCurve_at hf0 hcurve
  have he := congrArg (fun y : M => mvfderiv 𝓘(ℝ, E) f y (V y)) (F.map_zero_apply x)
  exact he ▸ hh

private def
    Degree.FlowCancellation.descentBlend {M : Type*} (χ : ℝ → ℝ) (θ f g : M → ℝ) (x : M) : ℝ :=
  g x + χ (θ x) * (f x - g x)

private theorem Degree.FlowCancellation.mvfderiv_descentBlend {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {χ : ℝ → ℝ} {θ f g : M → ℝ} {x : M}
    (hχ : ContDiff ℝ ∞ χ) (hθ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ x)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f x) (hg : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g x)
    (F : Flow ℝ M) (hcurve : IsMIntegralCurve (fun t => F t x) V)
    (htime : mvfderiv 𝓘(ℝ, E) θ x (V x) = -1) :
    mvfderiv 𝓘(ℝ, E) (descentBlend χ θ f g) x (V x) =
      mvfderiv 𝓘(ℝ, E) g x (V x) +
          χ (θ x) * (mvfderiv 𝓘(ℝ, E) f x (V x) - mvfderiv 𝓘(ℝ, E) g x (V x)) -
        deriv χ (θ x) * (f x - g x) := by
  have dθ := hasDerivAt_flow_height_zero (hθ.mdifferentiableAt (by simp)) F hcurve
  have df := hasDerivAt_flow_height_zero (hf.mdifferentiableAt (by simp)) F hcurve
  have dg := hasDerivAt_flow_height_zero (hg.mdifferentiableAt (by simp)) F hcurve
  rw [htime] at dθ
  have dχ := ((hχ.differentiable (by simp)) (θ (F 0 x))).hasDerivAt.comp 0 dθ
  have db := dg.add (dχ.mul (df.sub dg))
  have hb : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (descentBlend χ θ f g) x :=
    hg.add ((hχ.contMDiff.contMDiffAt.comp x hθ).mul (hf.sub hg))
  have dn := hasDerivAt_flow_height_zero (hb.mdifferentiableAt (by simp)) F hcurve
  have he := dn.unique db
  simp only [Pi.sub_apply, Function.comp_apply, F.map_zero_apply] at he
  exact he.trans (by ring)

private theorem
    Degree.FlowCancellation.exists_native_descent_blend {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {U : Set M} (hU : IsOpen U) {θ f g : M → ℝ}
    (hθ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ U) (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U) (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (htime : ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) θ x (V x) = -1)
    (hgneg : ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) g x (V x) < 0) {ε μ C : ℝ} (hε : 0 < ε) (hμ : 0 < μ)
    (hC : 0 ≤ C)
    (hcollar :
      ∀ x ∈ U,
        |θ x| < ε →
          mvfderiv 𝓘(ℝ, E) f x (V x) ≤ -μ ∧
            mvfderiv 𝓘(ℝ, E) g x (V x) ≤ -μ ∧ |f x - g x| ≤ C * |θ x|) :
    ∃ b : M → ℝ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b U ∧
        (∀ x ∈ U, mvfderiv 𝓘(ℝ, E) b x (V x) < 0) ∧
          (∀ x ∈ U, θ x = 0 → b =ᶠ[𝓝 x] f) ∧
            (∀ x, ε ≤ |θ x| → b x = g x) ∧ ∀ x ∈ U, ε < |θ x| → b =ᶠ[𝓝 x] g := by
  let δ := μ / (C + 1)
  have hδ : 0 < δ := div_pos hμ (by positivity)
  have hsmall : C * δ < μ := by
    dsimp [δ]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < C + 1)]
    nlinarith
  obtain ⟨χ, hχ, -, hone, hzero, hrange, hweight⟩ := exists_logarithmic_cutoff hε hδ
  let b := descentBlend χ θ f g
  have hb : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b U :=
    hg.add ((hχ.contMDiff.comp_contMDiffOn hθ).mul (hf.sub hg))
  have hout (x : M) (hx : ε ≤ |θ x|) : b x = g x := by
    simp only [b, descentBlend, hzero _ hx, MulZeroClass.zero_mul, add_zero]
  refine ⟨b, hb, ?_, ?_, hout, ?_⟩
  · intro x hx
    have hder :=
      mvfderiv_descentBlend hχ ((hθ x hx).contMDiffAt (hU.mem_nhds hx))
        ((hf x hx).contMDiffAt (hU.mem_nhds hx)) ((hg x hx).contMDiffAt (hU.mem_nhds hx)) F
        (hcurve x) (htime x hx)
    change mvfderiv 𝓘(ℝ, E) (descentBlend χ θ f g) x (V x) < 0
    rw [hder]
    by_cases hnear : |θ x| < ε
    · obtain ⟨hdf, hdg, hdiff⟩ := hcollar x hx hnear
      exact weighted_blend_neg (hrange _) hdf hdg hC hdiff (hweight _).le hsmall
    · have hz := hzero (θ x) (le_of_not_gt hnear)
      have hdχ :=
        deriv_eq_zero_of_nonneg_zero (hχ.differentiable (by simp)) (fun t => (hrange t).1) hz
      simpa only [hz, hdχ, MulZeroClass.zero_mul, add_zero, sub_zero] using hgneg x hx
  · intro x hx hxzero
    have ht : ContinuousAt θ x := (hθ x hx).continuousWithinAt.continuousAt (hU.mem_nhds hx)
    have hone' : ∀ᶠ t in 𝓝 (θ x), χ t = 1 := by simpa only [hxzero] using hone
    filter_upwards [ht.eventually hone'] with y hy
    change g y + χ (θ y) * (f y - g y) = f y
    rw [hy]
    ring
  · intro x hx hxout
    have ht : ContinuousAt (fun y => |θ y|) x :=
      ((hθ x hx).continuousWithinAt.continuousAt (hU.mem_nhds hx)).abs
    filter_upwards [ht (eventually_gt_nhds hxout)] with y hy
    exact hout y hy.le

private def
    Degree.FlowCancellation.flowTube {X : Type*} [TopologicalSpace X] (F : Flow ℝ X) (S : Set X)
    (ε : ℝ) : Set X :=
  (fun q : ℝ × X => F q.1 q.2) '' (Set.Icc (-ε) ε ×ˢ S)

private theorem
    Degree.FlowCancellation.isCompact_flowTube {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
    {S : Set X} (hS : IsCompact S) (ε : ℝ) : IsCompact (flowTube F S ε) :=
  (CompactIccSpace.isCompact_Icc.prod hS).image (F.continuous continuous_fst continuous_snd)

private theorem Degree.FlowCancellation.exists_flowTube_subset {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {S N : Set X} (hS : IsCompact S) (hN : IsOpen N) (hSN : S ⊆ N) :
    ∃ ε : ℝ, 0 < ε ∧ flowTube F S ε ⊆ N := by
  have hopen : IsOpen {t : ℝ | ∀ x ∈ S, F t x ∈ N} :=
    Smale.MorsePerturbation.isOpen_forall_mem_compact hS
      (hN.preimage (F.continuous continuous_fst continuous_snd))
  have hzero : (0 : ℝ) ∈ {t : ℝ | ∀ x ∈ S, F t x ∈ N} := by
    intro x hx
    simpa only [F.map_zero_apply] using hSN hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hzero)
  refine ⟨r / 2, half_pos hr, ?_⟩
  rintro y ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
  apply hball ?_ x hx
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
  constructor <;> linarith [ht.1, ht.2]

private theorem Degree.FlowCancellation.mem_flowTube_of_signedTime {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) (f : X → ℝ) (c : ℝ) {ε : ℝ} {x : X} (hx : x ∈ levelBasin F f c)
    (ht : |signedLevelTime F f c x| ≤ ε) : x ∈ flowTube F {y | f y = c} ε := by
  refine
    ⟨(-signedLevelTime F f c x, F (signedLevelTime F f c x) x),
      ⟨?_, signedLevelTime_hits F f c hx⟩, ?_⟩
  · constructor <;> linarith [(abs_le.mp ht).1, (abs_le.mp ht).2]
  · simp only [← F.map_add, neg_add_cancel, F.map_zero_apply]

private theorem
    Degree.FlowCancellation.exists_compact_negative_margin {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsCompact S) {D : X → ℝ} (hD : ContinuousOn D S) (hneg : ∀ x ∈ S, D x < 0) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ x ∈ S, D x < -μ := by
  by_cases hne : S.Nonempty
  · obtain ⟨p, hp, hmax⟩ := hS.exists_isMaxOn hne hD
    refine ⟨-D p / 2, by linarith [hneg p hp], ?_⟩
    intro x hx
    have hle : D x ≤ D p := hmax hx
    linarith [hneg p hp]
  · exact ⟨1, zero_lt_one, fun x hx => (hne ⟨x, hx⟩).elim⟩

private theorem Degree.FlowCancellation.contMDiffOn_directionalDerivative {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {U : Set M} (hU : IsOpen U)
    {g : M → ℝ} (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => mvfderiv 𝓘(ℝ, E) g x (V x)) U := by
  have ht :=
    (hg.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hU.uniqueMDiffOn).comp hV.contMDiffOn
      (fun x hx => hx)
  have hh := (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp_contMDiffOn ht
  apply hh.congr
  intro x hx
  change
    (NormedSpace.fromTangentSpace (g x)) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x (V x)) =
      (NormedSpace.fromTangentSpace (g x)) (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g U x (V x))
  rw [mfderivWithin_of_isOpen hU hx]

private theorem Degree.FlowCancellation.exists_native_time_collar_bounds {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} [CompactSpace M] {U : Set M}
    (hU : IsOpen U) {f g : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ}
    (hlevel : {x | f x = c} ⊆ U) (hbasin : U ⊆ levelBasin F f c) (heq : ∀ x, f x = c → g x = f x)
    (hfc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hgc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) g x (V x) < 0) :
    ∃ ε μ C : ℝ,
      0 < ε ∧
        0 < μ ∧
          0 ≤ C ∧
            ∀ x ∈ U,
              |signedLevelTime F f c x| < ε →
                mvfderiv 𝓘(ℝ, E) f x (V x) ≤ -μ ∧
                  mvfderiv 𝓘(ℝ, E) g x (V x) ≤ -μ ∧ |f x - g x| ≤ C * |signedLevelTime F f c x| :=
  by
  let S : Set M := {x | f x = c}
  have hS : IsCompact S := (isClosed_eq hf.continuous continuous_const).isCompact
  let Df (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  let Dg (x : M) := mvfderiv 𝓘(ℝ, E) g x (V x)
  have hDf : Continuous Df := (MorseCancel.contMDiff_directionalDerivative hf hV).continuous
  have hDg : ContinuousOn Dg U := (contMDiffOn_directionalDerivative hU hg hV).continuousOn
  have hmax : ContinuousOn (fun x => Max.max (Df x) (Dg x)) U :=
    continuous_max.comp_continuousOn (hDf.continuousOn.prodMk hDg)
  obtain ⟨μ, hμ, hmargin⟩ :=
    exists_compact_negative_margin hS (hmax.mono hlevel)
      (fun x hx => max_lt (hfc x hx) (hgc x hx))
  let N : Set M := U ∩ (fun x => Max.max (Df x) (Dg x)) ⁻¹' Set.Iio (-μ)
  have hN : IsOpen N := hmax.isOpen_inter_preimage hU isOpen_Iio
  have hSN : S ⊆ N := fun x hx => ⟨hlevel hx, hmargin x hx⟩
  obtain ⟨ε, hε, htube⟩ := exists_flowTube_subset F hS hN hSN
  let K := flowTube F S ε
  have hK : IsCompact K := isCompact_flowTube F hS ε
  have hKU : K ⊆ U := fun x hx => (htube hx).1
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn (hDf.continuousOn.sub (hDg.mono hKU))
  let C : ℝ := Max.max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hbound (x : M) (hx : x ∈ K) : ‖Df x - Dg x‖ ≤ C := (hC₀ x hx).trans (le_max_left _ _)
  refine ⟨ε, μ, C, hε, hμ, hC, ?_⟩
  intro x hx hxε
  have hxK : x ∈ K := mem_flowTube_of_signedTime F f c (hbasin hx) hxε.le
  have hxN := htube hxK
  have hneg : Max.max (Df x) (Dg x) < -μ := hxN.2
  refine
    ⟨(lt_of_le_of_lt (le_max_left _ _) hneg).le, (lt_of_le_of_lt (le_max_right _ _) hneg).le, ?_⟩
  let θ := signedLevelTime F f c x
  let y := F θ x
  have hy : f y = c := signedLevelTime_hits F f c (hbasin hx)
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (-ε) ε) : F t y ∈ K := ⟨(t, y), ⟨ht, hy⟩, rfl⟩
  let ℓ (t : ℝ) := f (F t y) - g (F t y)
  have hd (t : ℝ) (ht : t ∈ Set.Icc (-ε) ε) : HasDerivAt ℓ (Df (F t y) - Dg (F t y)) t := by
    have hgpoint :=
      ((hg (F t y) (hKU (hpoint t ht))).contMDiffAt
            (hU.mem_nhds (hKU (hpoint t ht)))).mdifferentiableAt
        (by simp)
    exact
      (hasDerivAt_comp_native_integralCurve_at (hf.mdifferentiableAt (by simp)) (hcurve y)).sub
        (hasDerivAt_comp_native_integralCurve_at hgpoint (hcurve y))
  have h0 : (0 : ℝ) ∈ Set.Icc (-ε) ε := ⟨by linarith, hε.le⟩
  have hθ : -θ ∈ Set.Icc (-ε) ε := by
    constructor <;> linarith [(abs_lt.mp hxε).1, (abs_lt.mp hxε).2]
  have hmvt :=
    (convex_Icc (-ε) ε).norm_image_sub_le_of_norm_deriv_le
      (fun t ht => (hd t ht).differentiableAt)
      (fun t ht => by rw [(hd t ht).deriv]; exact hbound _ (hpoint t ht)) h0 hθ
  have hreturn : F (-θ) y = x := by
    dsimp [y]
    rw [← F.map_add, neg_add_cancel, F.map_zero_apply]
  simpa only [ℓ, F.map_zero_apply, hreturn, heq y hy, sub_self, sub_zero, Real.norm_eq_abs,
    abs_neg] using hmvt

private theorem Degree.FlowCancellation.exists_boundary_germ_correction {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {U : Set M} (hU : IsOpen U) {f g : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c : ℝ}
    (hlevel : {x | f x = c} ⊆ U) (hbasin : U ⊆ levelBasin F f c) (heq : ∀ x, f x = c → g x = f x)
    (hfc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hgneg : ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) g x (V x) < 0) {r : ℝ} (hr : 0 < r) :
    ∃ b : M → ℝ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b U ∧
        (∀ x ∈ U, mvfderiv 𝓘(ℝ, E) b x (V x) < 0) ∧
          (∀ x, f x = c → b =ᶠ[𝓝 x] f) ∧ ∀ x ∈ U, r ≤ |signedLevelTime F f c x| → b =ᶠ[𝓝 x] g := by
  obtain ⟨ε₀, μ, C, hε₀, hμ, hC, hbounds⟩ :=
    exists_native_time_collar_bounds hU hf hg hV F hcurve hlevel hbasin heq hfc
      (fun x hx => hgneg x (hlevel hx))
  let ε := Min.min ε₀ (r / 2)
  have hε : 0 < ε := lt_min hε₀ (half_pos hr)
  have hεr : ε < r := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨-, hθ, -⟩ := smooth_signed_level_time hf hV F hcurve hfc
  have htime (x : M) (hx : x ∈ U) : mvfderiv 𝓘(ℝ, E) (signedLevelTime F f c) x (V x) = -1 :=
    mvfderiv_signedLevelTime hf hV F hcurve hfc (hbasin hx)
  obtain ⟨b, hb, hbneg, hbone, -, hboff⟩ :=
    exists_native_descent_blend hU (hθ.mono hbasin) hf.contMDiffOn hg F hcurve htime hgneg hε hμ
      hC (fun x hx ht => hbounds x hx (lt_of_lt_of_le ht (min_le_left _ _)))
  refine ⟨b, hb, hbneg, ?_, fun x hx ht => hboff x hx (hεr.trans_le ht)⟩
  intro x hx
  apply hbone x (hlevel hx)
  let D (y : M) := mvfderiv 𝓘(ℝ, E) f y (V y)
  have hD : Continuous D := (MorseCancel.contMDiff_directionalDerivative hf hV).continuous
  exact
    signedLevelTime_eq_zero F hf.continuous hD
      (fun y t => Smale.FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve y) t) hfc hx

private theorem Degree.FlowCancellation.exists_signedTime_level_separation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} (hcd : c ≠ d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hlevel : {x | f x = d} ⊆ levelBasin F f c) :
    ∃ r : ℝ, 0 < r ∧ ∀ x, f x = d → r < |signedLevelTime F f c x| := by
  obtain ⟨-, hθ, -⟩ := smooth_signed_level_time hf hV F hcurve hc
  have hS : IsCompact {x | f x = d} := (isClosed_eq hf.continuous continuous_const).isCompact
  obtain ⟨r, hr, hmargin⟩ :=
    exists_compact_negative_margin hS ((hθ.continuousOn.mono hlevel).abs.neg)
      (fun x hx => by
        apply neg_neg_of_pos
        apply abs_pos.mpr
        intro hz
        have hhit := signedLevelTime_hits F f c (hlevel hx)
        rw [hz, F.map_zero_apply] at hhit
        exact hcd (hhit.symm.trans hx))
  refine ⟨r, hr, fun x hx => ?_⟩
  have hh : -|signedLevelTime F f c x| < -r := hmargin x hx
  linarith

private theorem Degree.FlowCancellation.exists_boundary_correction_preserving_level {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {U : Set M} (hU : IsOpen U) {f g : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} (hcd : c ≠ d)
    (hcU : {x | f x = c} ⊆ U) (hdU : {x | f x = d} ⊆ U) (hbasin : U ⊆ levelBasin F f c)
    (heq : ∀ x, f x = c → g x = f x) (hfc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hgneg : ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) g x (V x) < 0) :
    ∃ b : M → ℝ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b U ∧
        (∀ x ∈ U, mvfderiv 𝓘(ℝ, E) b x (V x) < 0) ∧
          (∀ x, f x = c → b =ᶠ[𝓝 x] f) ∧ ∀ x, f x = d → b =ᶠ[𝓝 x] g := by
  obtain ⟨r, hr, hsep⟩ :=
    exists_signedTime_level_separation hf hV F hcurve hcd hfc (hdU.trans hbasin)
  obtain ⟨b, hb, hbneg, hbc, hboff⟩ :=
    exists_boundary_germ_correction hU hf hg hV F hcurve hcU hbasin heq hfc hgneg hr
  exact ⟨b, hb, hbneg, hbc, fun x hx => hboff x (hdU hx) (hsep x hx).le⟩

private theorem Degree.FlowCancellation.band_subset_crossingBasin {X : Type*} [TopologicalSpace X]
    (F : Flow ℝ X) {f : X → ℝ} (hf : Continuous f) {c d T : ℝ} (hT : 0 < T)
    (hforward : ∀ x, f x ≤ d → f (F T x) < c) (hbackward : ∀ x, c ≤ f x → d < f (F (-T) x)) :
    f ⁻¹' Set.Icc c d ⊆ crossingBasin F f c d := by
  intro x hx
  have hcont : Continuous (fun t : ℝ => f (F t x)) :=
    hf.comp (F.continuous continuous_id continuous_const)
  constructor
  · obtain ⟨t, -, ht⟩ :=
      intermediate_value_Icc' hT.le hcont.continuousOn
        (show c ∈ Set.Icc (f (F T x)) (f (F 0 x)) from
          ⟨(hforward x hx.2).le, by simpa only [F.map_zero_apply] using hx.1⟩)
    exact ⟨t, ht⟩
  · obtain ⟨t, -, ht⟩ :=
      intermediate_value_Icc' (show -T ≤ (0 : ℝ) by linarith) hcont.continuousOn
        (show d ∈ Set.Icc (f (F 0 x)) (f (F (-T) x)) from
          ⟨by simpa only [F.map_zero_apply] using hx.2, (hbackward x hx.1).le⟩)
    exact ⟨t, ht⟩

private theorem Degree.FlowCancellation.exists_smooth_band_height_germs {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} (hcd : c < d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hd : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hcross : ∃ T : ℝ, 0 < T ∧ (∀ x, f x ≤ d → f (F T x) < c) ∧ ∀ x, c ≤ f x → d < f (F (-T) x)) :
    ∃ (U : Set M) (g : M → ℝ),
      IsOpen U ∧
        f ⁻¹' Set.Icc c d ⊆ U ∧
          ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U ∧
            (∀ x ∈ U, mvfderiv 𝓘(ℝ, E) g x (V x) < 0) ∧ ∀ x, f x = c ∨ f x = d → g =ᶠ[𝓝 x] f := by
  let U := crossingBasin F f c d
  let g := flowBandHeight F f c d
  obtain ⟨hU, hg, hgder⟩ := smooth_flowBandHeight hf hV F hcurve hcd hc hd
  obtain ⟨T, hT, hforward, hbackward⟩ := hcross
  have hband : f ⁻¹' Set.Icc c d ⊆ U :=
    band_subset_crossingBasin F hf.continuous hT hforward hbackward
  have hcU : {x | f x = c} ⊆ U := fun x hx =>
    hband (show f x ∈ Set.Icc c d from ⟨by rw [hx], by rw [hx]; exact hcd.le⟩)
  have hdU : {x | f x = d} ⊆ U := fun x hx =>
    hband (show f x ∈ Set.Icc c d from ⟨by rw [hx]; exact hcd.le, by rw [hx]⟩)
  let D (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  have hD : Continuous D := (MorseCancel.contMDiff_directionalDerivative hf hV).continuous
  have hder (x : M) (t : ℝ) : HasDerivAt (fun s => f (F s x)) (D (F t x)) t :=
    Smale.FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) t
  have hgc (x : M) (hx : f x = c) : g x = f x :=
    (flowBandHeight_lower F hf.continuous hD hder hc hx).trans hx.symm
  have hgd (x : M) (hx : f x = d) : g x = f x :=
    (flowBandHeight_upper F hf.continuous hD hder hc hd hcd (hdU hx) hx).trans hx.symm
  obtain ⟨b, hb, hbneg, hbc, hbd⟩ :=
    exists_boundary_correction_preserving_level hU hf hg hV F hcurve hcd.ne hcU hdU
      Set.inter_subset_left hgc hc (fun x hx => (hgder x hx).2)
  have hbdval (x : M) (hx : f x = d) : b x = f x := (hbd x hx).eq_of_nhds.trans (hgd x hx)
  obtain ⟨k, hk, hkneg, hkd, hkc⟩ :=
    exists_boundary_correction_preserving_level hU hf hb hV F hcurve hcd.ne' hdU hcU
      Set.inter_subset_right hbdval hd hbneg
  refine ⟨U, k, hU, hband, hk, hkneg, ?_⟩
  intro x hx
  rcases hx with hx | hx
  · exact (hkc x hx).trans (hbc x hx)
  · exact hkd x hx

private def
    Degree.FlowCancellation.bandReplacement {X : Type*} (f g : X → ℝ) (c d : ℝ) (x : X) : ℝ := by
  classical exact if f x ∈ Set.Ioo c d then g x else f x

private theorem
    Degree.FlowCancellation.bandReplacement_germ_boundary {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {c d : ℝ} {x : X} (heq : g =ᶠ[𝓝 x] f) :
    bandReplacement f g c d =ᶠ[𝓝 x] f ∧ bandReplacement f g c d =ᶠ[𝓝 x] g := by
  have hh : bandReplacement f g c d =ᶠ[𝓝 x] f := by
    filter_upwards [heq] with y hy
    simp only [bandReplacement, hy, ite_self]
  exact ⟨hh, hh.trans heq.symm⟩

private theorem
    Degree.FlowCancellation.bandReplacement_germ_interior {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {c d : ℝ} (hf : Continuous f) {x : X} (hx : f x ∈ Set.Ioo c d) :
    bandReplacement f g c d =ᶠ[𝓝 x] g := by
  filter_upwards [(isOpen_Ioo.preimage hf).mem_nhds hx] with y hy
  exact ite_eq_left hy

private theorem
    Degree.FlowCancellation.bandReplacement_germ_exterior {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {c d : ℝ} (hf : Continuous f) {x : X} (hx : f x ∉ Set.Icc c d) :
    bandReplacement f g c d =ᶠ[𝓝 x] f := by
  filter_upwards [((isClosed_Icc.preimage hf).isOpen_compl).mem_nhds hx] with y hy
  exact ite_eq_right (fun h => hy ⟨h.1.le, h.2.le⟩)

private theorem
    Degree.FlowCancellation.bandReplacement_germ_on_closed {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {c d : ℝ} (hf : Continuous f) (hboundary : ∀ x, f x = c ∨ f x = d → g =ᶠ[𝓝 x] f)
    {x : X} (hx : f x ∈ Set.Icc c d) : bandReplacement f g c d =ᶠ[𝓝 x] g := by
  by_cases hc : f x = c
  · exact (bandReplacement_germ_boundary (hboundary x (Or.inl hc))).2
  by_cases hd : f x = d
  · exact (bandReplacement_germ_boundary (hboundary x (Or.inr hd))).2
  exact
    bandReplacement_germ_interior hf ⟨lt_of_le_of_ne hx.1 (Ne.symm hc), lt_of_le_of_ne hx.2 hd⟩

private theorem
    Degree.FlowCancellation.bandReplacement_germ_off_open {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} {c d : ℝ} (hf : Continuous f) (hboundary : ∀ x, f x = c ∨ f x = d → g =ᶠ[𝓝 x] f)
    {x : X} (hx : f x ∉ Set.Ioo c d) : bandReplacement f g c d =ᶠ[𝓝 x] f := by
  by_cases hc : f x = c
  · exact (bandReplacement_germ_boundary (hboundary x (Or.inl hc))).1
  by_cases hd : f x = d
  · exact (bandReplacement_germ_boundary (hboundary x (Or.inr hd))).1
  apply bandReplacement_germ_exterior hf
  intro h
  exact hx ⟨lt_of_le_of_ne h.1 (Ne.symm hc), lt_of_le_of_ne h.2 hd⟩

private theorem
    Degree.FlowCancellation.contMDiff_bandReplacement {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {c d : ℝ} {U : Set M}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U) (hU : IsOpen U)
    (hband : f ⁻¹' Set.Icc c d ⊆ U) (hboundary : ∀ x, f x = c ∨ f x = d → g =ᶠ[𝓝 x] f) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (bandReplacement f g c d) := by
  intro x
  by_cases hx : f x ∈ Set.Icc c d
  · exact
      ((hg x (hband hx)).contMDiffAt (hU.mem_nhds (hband hx))).congr_of_eventuallyEq
        (bandReplacement_germ_on_closed hf.continuous hboundary hx)
  · exact hf.contMDiffAt.congr_of_eventuallyEq (bandReplacement_germ_exterior hf.continuous hx)

private theorem Degree.FlowCancellation.mvfderiv_eq_of_germ {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f g : M → ℝ} {x : M} (heq : f =ᶠ[𝓝 x] g) :
    mvfderiv 𝓘(ℝ, E) f x (V x) = mvfderiv 𝓘(ℝ, E) g x (V x) := by
  unfold mvfderiv
  rw [heq.mfderiv_eq, heq.eq_of_nhds]

private theorem
    Degree.FlowCancellation.exists_global_band_lyapunov {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} (hcd : c < d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hd : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hcross : ∃ T : ℝ, 0 < T ∧ (∀ x, f x ≤ d → f (F T x) < c) ∧ ∀ x, c ≤ f x → d < f (F (-T) x)) :
    ∃ b : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b ∧
        (∀ x, f x ∈ Set.Icc c d → mvfderiv 𝓘(ℝ, E) b x (V x) < 0) ∧
          ∀ x, f x ∉ Set.Ioo c d → b =ᶠ[𝓝 x] f := by
  obtain ⟨U, g, hU, hband, hg, hgneg, hgerm⟩ :=
    exists_smooth_band_height_germs hf hV F hcurve hcd hc hd hcross
  refine ⟨bandReplacement f g c d, contMDiff_bandReplacement hf hg hU hband hgerm, ?_, ?_⟩
  · intro x hx
    rw [mvfderiv_eq_of_germ (V := V) (bandReplacement_germ_on_closed hf.continuous hgerm hx)]
    exact hgneg x (hband hx)
  · intro x hx
    exact bandReplacement_germ_off_open hf.continuous hgerm hx

private def
    MorseCancel.hessian {m : ℕ} (σ : Fin m → ℝ) (p : Model m) : Model m →L[ℝ] Model m →L[ℝ] ℝ :=
  (2 * p.1) •
      (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).smulRight
        (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)) +
    ∑ i,
      (2 * σ i) •
        (((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))).smulRight
          ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))))

private theorem MorseCancel.hessian_apply {m : ℕ} (σ : Fin m → ℝ) (p v w : Model m) :
    hessian σ p v w = 2 * p.1 * v.1 * w.1 + ∑ i, 2 * σ i * v.2 i * w.2 i := by
  simp [hessian, mul_assoc]

private theorem MorseCancel.hasFDerivAt_differential {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) :
    HasFDerivAt (differential σ t) (hessian σ p) p := by
  have hx := (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).hasFDerivAt (x := p)
  let L (i : Fin m) : Model m →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ))
  have hq :=
    HasFDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => (((L i).hasFDerivAt (x := p)).const_mul (2 * σ i)).smul_const (L i))
  convert
      (((hx.pow 2).add_const t).smul_const (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ))).add hq using
      1 <;>
    first
    | rfl
    | ( apply ContinuousLinearMap.ext; intro v
        apply ContinuousLinearMap.ext; intro w
        simp [hessian, L, mul_assoc])

private theorem MorseCancel.fderiv_cubic_hessian {m : ℕ} (σ : Fin m → ℝ) (t : ℝ) (p : Model m) :
    fderiv ℝ (fderiv ℝ (cubic σ t)) p = hessian σ p := by
  rw [show fderiv ℝ (cubic σ t) = differential σ t from funext (fderiv_cubic σ t)]
  exact (hasFDerivAt_differential σ t p).fderiv

private theorem
    MorseCancel.hessian_bijective {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0) {p : Model m}
    (hp : p.1 ≠ 0) : Function.Bijective (hessian σ p) := by
  have hi : Function.Injective (hessian σ p) := by
    apply (injective_iff_map_eq_zero (hessian σ p)).mpr
    intro v hv
    have hx := congrArg (fun L : Model m →L[ℝ] ℝ => L (1, 0)) hv
    have hx' : 2 * p.1 * v.1 = 0 := by simpa [hessian_apply] using hx
    have hvx : v.1 = 0 := (mul_eq_zero.mp hx').resolve_left (mul_ne_zero (by norm_num) hp)
    apply Prod.ext hvx
    funext i
    have hy := congrArg (fun L : Model m →L[ℝ] ℝ => L (0, Pi.single i 1)) hv
    have hy' : 2 * σ i * v.2 i = 0 := by simpa [hessian_apply, Pi.single_apply] using hy
    exact (mul_eq_zero.mp hy').resolve_left (mul_ne_zero (by norm_num) (hσ i))
  have hd : Module.finrank ℝ (Model m) = Module.finrank ℝ (Model m →L[ℝ] ℝ) := by
    calc
      _ = Module.finrank ℝ (Model m →ₗ[ℝ] ℝ) := Subspace.dual_finrank_eq.symm
      _ = _ :=
        (LinearMap.toContinuousLinearMap : (Model m →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (Model m →L[ℝ] ℝ)).finrank_eq
  exact
    ⟨hi,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := (hessian σ p).toLinearMap)
            hd).mp
        hi⟩

private theorem MorseCancel.cubic_isMorse {m : ℕ} (σ : Fin m → ℝ) (hσ : ∀ i, σ i ≠ 0) {t : ℝ}
    (ht : t ≠ 0) : Smale.MorsePerturbation.IsMorse (cubic σ t) := by
  intro p hcrit
  rw [fderiv_cubic_hessian]
  apply hessian_bijective σ hσ
  intro hp
  have h := ((critical_iff σ hσ t p).mp hcrit).1
  exact ht (by simpa [hp] using h)

private theorem Degree.NativeCubicCancellation.exists_cutoff {m : ℕ} {V : Set (MorseCancel.Model m)}
    (hV : IsOpen V) (h0 : (0 : MorseCancel.Model m) ∈ V) :
    ∃ φ : MorseCancel.Model m → ℝ,
      ContDiff ℝ ∞ φ ∧
        HasCompactSupport φ ∧
          tsupport φ ⊆ V ∧
            ∃ U : Set (MorseCancel.Model m),
              IsOpen U ∧ (0 : MorseCancel.Model m) ∈ U ∧ Set.EqOn φ (fun _ => 1) U := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0)
  let φ : ContDiffBump (0 : MorseCancel.Model m) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine
    ⟨φ, φ.contDiff, φ.hasCompactSupport, ?_, Metric.ball 0 (r / 4), Metric.isOpen_ball,
      Metric.mem_ball_self (by positivity), ?_⟩
  · rw [φ.tsupport_eq]
    intro p hp
    apply hball
    exact lt_of_le_of_lt hp (by change r / 2 < r; linarith)
  · intro p hp
    exact φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hp)

private theorem Degree.MorseCancellationPreservation.isMorseAt_of_same_germ {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}
    {x : M} (hf : Smale.ManifoldMorse.IsMorseAt E f x) (heq : g =ᶠ[𝓝 x] f) :
    Smale.ManifoldMorse.IsMorseAt E g x := by
  obtain ⟨e, he, hx, hgood⟩ := hf
  refine ⟨e, he, hx, ?_⟩
  have ht : Filter.Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
    have h := e.symm.continuousAt (e.map_source hx)
    rw [ContinuousAt, e.left_inv hx] at h
    exact h
  have hc : g ∘ e.symm =ᶠ[𝓝 (e x)] f ∘ e.symm := heq.comp_tendsto ht
  rw [hc.fderiv_eq, (hc.fderiv (𝕜 := ℝ)).fderiv_eq]
  exact hgood

private theorem Degree.MorseCancellationPreservation.isMorseAt_of_regular {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {g : M → ℝ} (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) {x : M}
    (hreg : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x ≠ 0) : Smale.ManifoldMorse.IsMorseAt E g x := by
  let e := chartAt E x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ e.source := mem_chart_source E x
  refine ⟨e, he, hx, Or.inl ?_⟩
  intro hc
  exact hreg ((Smale.ManifoldMorse.mem_criticalPoints_iff hg he hx).mpr hc)

private theorem Degree.MorseCancellationPreservation.isMorse_of_critical_germs {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f g : M → ℝ} (hf : Smale.ManifoldMorse.IsMorse E f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hkeep : ∀ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = 0 → g =ᶠ[𝓝 x] f) :
    Smale.ManifoldMorse.IsMorse E g := by
  intro x
  by_cases hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = 0
  · exact isMorseAt_of_same_germ (hf x) (hkeep x hx)
  · exact isMorseAt_of_regular hg hx

private theorem Degree.FlowCancellation.not_critical_of_directional_neg {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {g : M → ℝ} {x : M}
    (hneg : mvfderiv 𝓘(ℝ, E) g x (V x) < 0) : x ∉ Smale.ManifoldMorse.criticalPoints E g := by
  intro hx
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = 0 at hx
  unfold mvfderiv at hneg
  rw [hx] at hneg
  simp at hneg

private theorem Degree.FlowCancellation.remove_morse_band_pair {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V) {c d : ℝ} (hcd : c < d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hd : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hcross : ∃ T : ℝ, 0 < T ∧ (∀ x, f x ≤ d → f (F T x) < c) ∧ ∀ x, c ≤ f x → d < f (F (-T) x))
    {p q : M} (hpq : p ≠ q) (hp : p ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hq : q ∈ Smale.ManifoldMorse.criticalPoints E f) (hpc : f p ∈ Set.Icc c d)
    (hqc : f q ∈ Set.Icc c d)
    (hpair : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc c d → x = p ∨ x = q) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          (Smale.ManifoldMorse.criticalPoints E g).ncard + 2 =
              (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ x,
                x ∈ Smale.ManifoldMorse.criticalPoints E g ↔
                  x ∈ Smale.ManifoldMorse.criticalPoints E f ∧ x ≠ p ∧ x ≠ q) ∧
              ∀ x, f x ∉ Set.Ioo c d → g =ᶠ[𝓝 x] f := by
  obtain ⟨g, hg, hneg, hgerm⟩ := exists_global_band_lyapunov hf hV F hcurve hcd hc hd hcross
  have hreg (x : M) (hx : f x ∈ Set.Icc c d) : x ∉ Smale.ManifoldMorse.criticalPoints E g :=
    not_critical_of_directional_neg (hneg x hx)
  have hnew (x : M) :
    x ∈ Smale.ManifoldMorse.criticalPoints E g ↔
      x ∈ Smale.ManifoldMorse.criticalPoints E f ∧ x ≠ p ∧ x ≠ q := by
    constructor
    · intro hx
      have hout : f x ∉ Set.Icc c d := fun h => hreg x h hx
      have he := hgerm x (fun h => hout ⟨h.1.le, h.2.le⟩)
      have hcrit : x ∈ Smale.ManifoldMorse.criticalPoints E f := by
        change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0
        rw [← he.mfderiv_eq]
        exact hx
      exact ⟨hcrit, fun h => hout (h ▸ hpc), fun h => hout (h ▸ hqc)⟩
    · rintro ⟨hx, hxp, hxq⟩
      have hout : f x ∉ Set.Icc c d := fun h => (hpair x hx h).elim hxp hxq
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = 0
      rw [(hgerm x (fun h => hout ⟨h.1.le, h.2.le⟩)).mfderiv_eq]
      exact hx
  have hmg : Smale.ManifoldMorse.IsMorse E g := by
    apply Degree.MorseCancellationPreservation.isMorse_of_critical_germs hm hg
    intro x hx
    apply hgerm x
    intro h
    exact hreg x ⟨h.1.le, h.2.le⟩ hx
  have heq :
    Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f \ { p, q } := by
    ext x
    simpa only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hnew x
  have hsub : { p, q } ⊆ Smale.ManifoldMorse.criticalPoints E f := by
    intro x hx
    rcases hx with rfl | hx
    · exact hp
    · exact Set.mem_singleton_iff.mp hx ▸ hq
  refine ⟨g, hg, hmg, ?_, hnew, hgerm⟩
  rw [heq, ← Set.ncard_pair hpq]
  exact Set.ncard_sdiff_add_ncard_of_subset hsub (Smale.ManifoldMorse.finite_criticalPoints hf hm)

private theorem
    MorseCancel.cancel_unique_native_cubic_connection {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i ≠ 0) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Set.Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) (F : Flow ℝ M)
    (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f))
    (hp : Φ (a, 0) ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hq : Φ (-a, 0) ∈ Smale.ManifoldMorse.criticalPoints E f) (hpq : f (Φ (a, 0)) < f (Φ (-a, 0)))
    {c d : ℝ} (hc : c < f (Φ (a, 0))) (hd : f (Φ (-a, 0)) < d)
    (hpair :
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
        f x ∈ Set.Icc c d → x = Φ (a, 0) ∨ x = Φ (-a, 0))
    (hunique :
      ∀ x ∉ Smale.ManifoldMorse.criticalPoints E f,
        Filter.Tendsto (fun t : ℝ => F t x) Filter.atBot (𝓝 (Φ (-a, 0))) →
          Filter.Tendsto (fun t : ℝ => F t x) Filter.atTop (𝓝 (Φ (a, 0))) →
            ∃ t : ℝ, F t (Φ (0, 0)) = x) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          (Smale.ManifoldMorse.criticalPoints E g).ncard + 2 =
              (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ x,
                x ∈ Smale.ManifoldMorse.criticalPoints E g ↔
                  x ∈ Smale.ManifoldMorse.criticalPoints E f ∧ x ≠ Φ (a, 0) ∧ x ≠ Φ (-a, 0)) ∧
              ∀ x, f x ∉ Set.Ioo c d → g =ᶠ[𝓝 x] f := by
  obtain ⟨K, V', -, hKsub, hV', -, hkeep, -, G, hGcurve, hcross, -⟩ :=
    exists_cubic_connection_finite_passage σ hσ ha Φ haxis hf V hV hmodel F hcurve hzero hdesc
      hinj hp hq hpq hc hd hpair hunique
  have hcd : c < d := lt_trans hc (lt_trans hpq hd)
  have hboundary (x : M) (hx : f x = c ∨ f x = d) : mvfderiv 𝓘(ℝ, E) f x (V' x) < 0 := by
    have hxK : x ∉ K := by
      intro hxK
      have hh : f x ∈ Set.Ioo c d := (hKsub hxK).2
      rcases hx with hx | hx <;> rw [hx] at hh
      · exact (lt_irrefl c) hh.1
      · exact (lt_irrefl d) hh.2
    have hreg : x ∉ Smale.ManifoldMorse.criticalPoints E f := by
      intro hcrit
      have hxb : f x ∈ Set.Icc c d := by
        rcases hx with hx | hx <;> rw [hx]
        · exact ⟨le_rfl, hcd.le⟩
        · exact ⟨hcd.le, le_rfl⟩
      rcases hpair x hcrit hxb with he | he
      · rw [he] at hx
        rcases hx with hx | hx <;> linarith
      · rw [he] at hx
        rcases hx with hx | hx <;> linarith
    rw [(hkeep x hxK).self_of_nhds]
    exact hdesc x hreg
  have hneq : Φ (a, (0 : Fin m → ℝ)) ≠ Φ (-a, 0) := by
    intro h
    exact hpq.ne (congrArg f h)
  exact
    Degree.FlowCancellation.remove_morse_band_pair hf hm hV' G hGcurve hcd
      (fun x hx => hboundary x (Or.inl hx)) (fun x hx => hboundary x (Or.inr hx)) hcross hneq hp
      hq ⟨hc.le, (hpq.trans hd).le⟩ ⟨(hc.trans hpq).le, hd.le⟩ hpair

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.cancel_unique_native_transverse_connection {Z E M : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1) {a : ℝ} (ha : 0 < a)
    (Φq Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (A : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) {U : Set Z}
    (hAsource : A.source = U ×ˢ Set.univ) {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) {b s : ℝ} (hs : 0 < s)
    (hheight : ∀ z ∈ A.source, z.2 ∈ Set.Ioo (0 : ℝ) 1 → f (A z) = b - s * z.2)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hqfield : ∀ y ∈ Φq.target, V y = nativeCubicDescent σ Φq (-(a ^ 2)) y)
    (hpfield : ∀ y ∈ Φp.target, V y = nativeCubicDescent σ Φp (-(a ^ 2)) y)
    (hAfield :
      ∀ y ∈ A.target,
        V y = Smale.FlowConstruction.partialChartField A.symm (fun _ : Z × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f))
    (Q P :
      PartialDiffeomorph
        𝓘(ℝ, Smale.MorseHandle.NegativeSpace σ × Smale.MorseHandle.PositiveSpace σ) 𝓘(ℝ, Z)
        (Smale.MorseHandle.NegativeSpace σ × Smale.MorseHandle.PositiveSpace σ) Z ∞)
    (H :
      PartialDiffeomorph
        𝓘(ℝ, Smale.MorseHandle.NegativeSpace σ × Smale.MorseHandle.PositiveSpace σ)
        𝓘(ℝ, Smale.MorseHandle.NegativeSpace σ × Smale.MorseHandle.PositiveSpace σ)
        (Smale.MorseHandle.NegativeSpace σ × Smale.MorseHandle.PositiveSpace σ)
        (Smale.MorseHandle.NegativeSpace σ × Smale.MorseHandle.PositiveSpace σ) ∞)
    (h0 : 0 ∈ H.source) (hH0 : H 0 = 0) (hQ0 : Q 0 = 0) (hP0 : P 0 = 0)
    (hQsource : Q.source = H.source) (hPsource : P.source = H.target) (hQtarget : Q.target = U)
    (hPtarget : P.target = U) (hdiagram : ∀ u ∈ H.source, P (H u) = Q u)
    (htrans :
      Smale.NativeTransversality.At 𝓘(ℝ, Smale.MorseHandle.NegativeSpace σ)
        𝓘(ℝ, Smale.MorseHandle.PositiveSpace σ)
        𝓘(ℝ, Smale.MorseHandle.NegativeSpace σ × Smale.MorseHandle.PositiveSpace σ)
        (fun x => H (x, 0)) (fun y => (0, y)) 0 0)
    (v₀ v₁ : (Smale.MorseHandle.NegativeSpace σ × Smale.MorseHandle.PositiveSpace σ) → ℝ)
    (hv₀ : ContDiff ℝ ∞ v₀) (hv₁ : ContDiff ℝ ∞ v₁) (hv₀zero : v₀ 0 = 0) (hv₁zero : v₁ 0 = 0)
    {Rq Rp Tq Tp : ℝ} (hRq : 0 < Rq) (hRp : 0 < Rp)
    (hboxq : Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq ⊆ Φq.source)
    (hboxp : Metric.closedBall (a, (0 : Fin m → ℝ)) Rp ⊆ Φp.source)
    (hsliceq :
      ∀ u ∈ Q.source,
        cubicFlowCylinder σ a ((Smale.MorseHandle.splitCoordinates σ).symm u, Tq) ∈
          Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq)
    (hslicep :
      ∀ u ∈ P.source,
        cubicFlowCylinder σ a ((Smale.MorseHandle.splitCoordinates σ).symm u, Tp) ∈
          Metric.closedBall (a, (0 : Fin m → ℝ)) Rp)
    (hphaseq :
      ∀ u ∈ Q.source,
        Φq (cubicFlowCylinder σ a ((Smale.MorseHandle.splitCoordinates σ).symm u, Tq)) =
          A (Q u, Tq + v₀ u))
    (hphasep :
      ∀ u ∈ P.source,
        Φp (cubicFlowCylinder σ a ((Smale.MorseHandle.splitCoordinates σ).symm u, Tp)) =
          A (P u, Tp + v₁ u))
    (hqbasin :
      ∀ z ∈ Φq.source,
        Filter.Tendsto (fun t => F t (Φq z)) Filter.atBot (𝓝 (Φq (-a, 0))) ↔
          ∀ i, σ i = 1 → z.2 i = 0)
    (hpbasin :
      ∀ z ∈ Φp.source,
        Filter.Tendsto (fun t => F t (Φp z)) Filter.atTop (𝓝 (Φp (a, 0))) ↔
          ∀ i, σ i = -1 → z.2 i = 0)
    (hold :
      ∀ x,
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 (Φq (-a, 0))) →
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 (Φp (a, 0))) → ∃ t, F t (A (0, 0)) = x)
    (hp : Φp (a, 0) ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hq : Φq (-a, 0) ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hpq : f (Φp (a, 0)) < f (Φq (-a, 0))) {c d : ℝ} (hc : c < f (Φp (a, 0)))
    (hd : f (Φq (-a, 0)) < d)
    (hpair :
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
        f x ∈ Set.Icc c d → x = Φp (a, 0) ∨ x = Φq (-a, 0)) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          (Smale.ManifoldMorse.criticalPoints E g).ncard + 2 =
              (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ x,
                x ∈ Smale.ManifoldMorse.criticalPoints E g ↔
                  x ∈ Smale.ManifoldMorse.criticalPoints E f ∧ x ≠ Φp (a, 0) ∧ x ≠ Φq (-a, 0)) ∧
              ∀ x, f x ∉ Set.Ioo c d → g =ᶠ[𝓝 x] f := by
  have hV1 := hV.of_le (show (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) by simp)
  have hQU : Q.target ⊆ U := fun _ hz => hQtarget ▸ hz
  have hPU : P.target ⊆ U := fun _ hz => hPtarget ▸ hz
  have hflow (z : Z) (hz : z ∈ U) (t : ℝ) : A (z, t) = F t (A (z, 0)) := by
    simpa only [zero_add] using
      (Degree.FlowSuspension.native_vertical_cylinder_flow A hAsource hV1 hAfield F hF z hz 0
          t).symm
  have hleft :=
    Degree.FlowSuspension.cylinder_outgoing_basin_labels F A Q (fun z hz => hflow z (hQU hz))
      (fun u => Φq (cubicFlowCylinder σ a ((Smale.MorseHandle.splitCoordinates σ).symm u, Tq)))
      (fun u => Tq + v₀ u) hphaseq
      (fun u hu => outgoing_cubic_slice_basin σ hσ a Tq Φq F hqbasin u (hboxq (hsliceq u hu)))
  have hright :=
    Degree.FlowSuspension.cylinder_incoming_basin_labels F A P (fun z hz => hflow z (hPU hz))
      (fun u => Φp (cubicFlowCylinder σ a ((Smale.MorseHandle.splitCoordinates σ).symm u, Tp)))
      (fun u => Tp + v₁ u) hphasep
      (fun u hu => incoming_cubic_slice_basin σ a Tp Φp F hpbasin u (hboxp (hslicep u hu)))
  rw [hQtarget, hQsource] at hleft
  rw [hPtarget, hPsource] at hright
  have hheightAux : ∀ z ∈ A.source, z.2 ∈ Set.Ioo (0 : ℝ) 1 → f (A z) / s = b / s - z.2 := by
    intro z hz ht
    rw [hheight z hz ht]
    field_simp
  obtain
    ⟨L₁, L₂, N, W, G, Ξ, _, hNsub, hW, hG, hzeroW, hdescW, hgerm, hΞsource, hΞtarget, hΞfield,
      hΞaxis, hunique, hmatch⟩ :=
    Degree.FlowSuspension.exists_unique_phase_corrected_cylinder A hAsource (hf.div_const s)
      hheightAux V hV hAfield F hF Q P H h0 hH0 hQ0 hP0 (fun _ hz => hQsource ▸ hz)
      (fun _ hz => hPsource ▸ hz) hQtarget hPtarget hdiagram htrans (fun z hz => hleft z hz 0)
      (fun z hz => hright z hz 1) hold hv₀ hv₁ hv₀zero hv₁zero
  have hdescWf (x : M) (hx : x ∉ Smale.ManifoldMorse.criticalPoints E f) :
    mvfderiv 𝓘(ℝ, E) f x (W x) < 0 :=
    (Degree.FlowTimeChange.descending_height_div_const_iff (hf.mdifferentiableAt (by simp)) hs
          (W x)).mp
      (hdescW x
        ((Degree.FlowTimeChange.descending_height_div_const_iff (hf.mdifferentiableAt (by simp))
              hs (V x)).mpr
          (hdesc x hx)))
  have hAregular (x : M) (hx : x ∈ A.target) : V x ≠ 0 := by
    intro hz
    rw [hAfield x hx] at hz
    have hh := (partialChartField_zero_iff A (fun _ : Z × ℝ => (0, 1)) hx).mp hz
    exact one_ne_zero (congrArg Prod.snd hh)
  have hqN : Φq (-a, 0) ∉ N := fun hx => hAregular _ (hNsub hx) (hzero _ hq)
  have hpN : Φp (a, 0) ∉ N := fun hx => hAregular _ (hNsub hx) (hzero _ hp)
  have hQ0source : 0 ∈ Q.source := hQsource ▸ h0
  have hP0source : 0 ∈ P.source := by
    rw [hPsource, ← hH0]
    exact H.map_source' h0
  have hne : Φq (-a, 0) ≠ Φp (a, 0) := by
    intro h
    exact hpq.ne (congrArg f h.symm)
  obtain ⟨Γ, hΓaxis, hΓfield, hΓq, hΓp, hΓcenter⟩ :=
    exists_full_cubic_chart_from_corrected_cylinder σ hσ ha Φq Φp A hAsource hV1 hqfield hpfield
      hAfield F hF L₁ L₂ Q P v₀ v₁ Q.open_source P.open_source hQ0source hP0source
      (fun u hu => hQU (Q.map_source' hu)) (fun u hu => hPU (P.map_source' hu)) hRq hRp hboxq
      hboxp hsliceq hslicep hphaseq hphasep Ξ Q.open_source hQ0source hΞsource hΞtarget
      (hW.of_le (by simp)) hΞfield G hG (hgerm _ hqN) (hgerm _ hpN) hne
      (hmatch.mono fun _ h => h.1) (hmatch.mono fun _ h => h.2)
  have hΓ0 : Γ (0, 0) = A (0, 0) := hΓcenter.trans (hΞaxis 0)
  have hσne : ∀ i, σ i ≠ 0 := by
    intro i
    rcases hσ i with hi | hi <;> rw [hi] <;> norm_num
  have hcancel :=
    cancel_unique_native_cubic_connection σ hσne ha Γ hΓaxis hf hm W hW hΓfield G hG
      (fun x hx => (hzeroW x).mpr (hzero x hx)) hdescWf hinj (by rw [hΓp]; exact hp)
      (by rw [hΓq]; exact hq) (by rw [hΓp, hΓq]; exact hpq) (by rw [hΓp]; exact hc)
      (by rw [hΓq]; exact hd) (by simpa only [hΓp, hΓq] using hpair)
      (by
        intro x _ hbot htop
        rw [hΓq] at hbot
        rw [hΓp] at htop
        rw [hΓ0]
        exact hunique x hbot htop)
  simpa only [hΓp, hΓq] using hcancel

private theorem MorseCancel.cancel_native_endpoint_slice_data {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1) {a : ℝ} (ha : 0 < a)
    (Φq Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (A : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞) {Rq Rp Tq Tp : ℝ}
    (D : NativeEndpointSliceData σ a Φq Φp A Rq Rp Tq Tp)
    (htrans :
      Smale.NativeTransversality.At 𝓘(ℝ, Smale.MorseHandle.NegativeSpace σ)
        𝓘(ℝ, Smale.MorseHandle.PositiveSpace σ) 𝓘(ℝ, Fin m → ℝ) (fun x => D.Q (x, 0))
        (fun y => D.P (0, y)) 0 0)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    {b s : ℝ} (hs : 0 < s)
    (hheight : ∀ z ∈ A.source, z.2 ∈ Set.Ioo (0 : ℝ) 1 → f (A z) = b - s * z.2)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hqfield : ∀ y ∈ Φq.target, V y = nativeCubicDescent σ Φq (-(a ^ 2)) y)
    (hpfield : ∀ y ∈ Φp.target, V y = nativeCubicDescent σ Φp (-(a ^ 2)) y)
    (hAfield :
      ∀ y ∈ A.target,
        V y =
          Smale.FlowConstruction.partialChartField A.symm (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f)) (hRq : 0 < Rq) (hRp : 0 < Rp)
    (hboxq : Metric.closedBall (-a, (0 : Fin m → ℝ)) Rq ⊆ Φq.source)
    (hboxp : Metric.closedBall (a, (0 : Fin m → ℝ)) Rp ⊆ Φp.source)
    (hqbasin :
      ∀ z ∈ Φq.source,
        Filter.Tendsto (fun t => F t (Φq z)) Filter.atBot (𝓝 (Φq (-a, 0))) ↔
          ∀ i, σ i = 1 → z.2 i = 0)
    (hpbasin :
      ∀ z ∈ Φp.source,
        Filter.Tendsto (fun t => F t (Φp z)) Filter.atTop (𝓝 (Φp (a, 0))) ↔
          ∀ i, σ i = -1 → z.2 i = 0)
    (hold :
      ∀ x,
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 (Φq (-a, 0))) →
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 (Φp (a, 0))) → ∃ t, F t (A (0, 0)) = x)
    (hp : Φp (a, 0) ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hq : Φq (-a, 0) ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hpq : f (Φp (a, 0)) < f (Φq (-a, 0))) {c d : ℝ} (hc : c < f (Φp (a, 0)))
    (hd : f (Φq (-a, 0)) < d)
    (hpair :
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
        f x ∈ Set.Icc c d → x = Φp (a, 0) ∨ x = Φq (-a, 0)) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          (Smale.ManifoldMorse.criticalPoints E g).ncard + 2 =
              (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ x,
                x ∈ Smale.ManifoldMorse.criticalPoints E g ↔
                  x ∈ Smale.ManifoldMorse.criticalPoints E f ∧ x ≠ Φp (a, 0) ∧ x ≠ Φq (-a, 0)) ∧
              ∀ x, f x ∉ Set.Ioo c d → g =ᶠ[𝓝 x] f := by
  have hrelative :=
    Degree.TransverseGerms.relative_transverse_of_label_sheets D.Q D.P D.H D.zero_source D.H_zero
      D.Q_zero D.P_zero (fun _ hz => D.Q_source ▸ hz) (fun _ hz => D.P_source ▸ hz) D.diagram
      htrans
  exact
    cancel_unique_native_transverse_connection σ hσ ha Φq Φp A D.source hf hm hs hheight V hV
      hqfield hpfield hAfield F hF hzero hdesc hinj D.Q D.P D.H D.zero_source D.H_zero D.Q_zero
      D.P_zero D.Q_source D.P_source D.Q_target D.P_target D.diagram hrelative D.phaseQ D.phaseP
      D.smooth_phaseQ D.smooth_phaseP D.zero_phaseQ D.zero_phaseP hRq hRp hboxq hboxp D.sliceQ
      D.sliceP D.formulaQ D.formulaP hqbasin hpbasin hold hp hq hpq hc hd hpair

private structure MorseCancel.NativeConnectionCancellationData {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] (f : M → ℝ)
    (p q : M) (m : ℕ) where
  σ : Fin m → ℝ
  signs : ∀ i, σ i = -1 ∨ σ i = 1
  field : (y : M) → TangentSpace 𝓘(ℝ, E) y
  smooth_field :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun y => (⟨y, field y⟩ : TangentBundle 𝓘(ℝ, E) M))
  flow : Flow ℝ M
  integral : ∀ y, IsMIntegralCurve (fun t => flow t y) field
  zero : ∀ y ∈ Smale.ManifoldMorse.criticalPoints E f, field y = 0
  descent : ∀ y, y ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (field y) < 0
  Φq : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞
  Φp : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞
  endpointQ : Φq (-(1 / 2 : ℝ), 0) = q
  endpointP : Φp (1 / 2, 0) = p
  fieldQ : ∀ y ∈ Φq.target, field y = nativeCubicDescent σ Φq (-(1 / 2 : ℝ) ^ 2) y
  fieldP : ∀ y ∈ Φp.target, field y = nativeCubicDescent σ Φp (-(1 / 2 : ℝ) ^ 2) y
  A : PartialDiffeomorph 𝓘(ℝ, (Fin m → ℝ) × ℝ) 𝓘(ℝ, E) ((Fin m → ℝ) × ℝ) M ∞
  vertical :
    ∀ y ∈ A.target,
      field y =
        Smale.FlowConstruction.partialChartField A.symm (fun _ : (Fin m → ℝ) × ℝ => (0, 1)) y
  speed : ℝ
  positive_speed : 0 < speed
  height : ℝ
  height_formula : ∀ z ∈ A.source, z.2 ∈ Set.Ioo (0 : ℝ) 1 → f (A z) = height - speed * z.2
  Rq : ℝ
  Rp : ℝ
  Tq : ℝ
  Tp : ℝ
  positive_Rq : 0 < Rq
  positive_Rp : 0 < Rp
  boxQ : Metric.closedBall (-(1 / 2 : ℝ), (0 : Fin m → ℝ)) Rq ⊆ Φq.source
  boxP : Metric.closedBall (1 / 2, (0 : Fin m → ℝ)) Rp ⊆ Φp.source
  basinQ :
    ∀ z ∈ Φq.source,
      Filter.Tendsto (fun t => flow t (Φq z)) Filter.atBot (𝓝 q) ↔ ∀ i, σ i = 1 → z.2 i = 0
  basinP :
    ∀ z ∈ Φp.source,
      Filter.Tendsto (fun t => flow t (Φp z)) Filter.atTop (𝓝 p) ↔ ∀ i, σ i = -1 → z.2 i = 0
  unique :
    ∀ y,
      Filter.Tendsto (fun t => flow t y) Filter.atBot (𝓝 q) →
        Filter.Tendsto (fun t => flow t y) Filter.atTop (𝓝 p) → ∃ t, flow t (A (0, 0)) = y
  slices : NativeEndpointSliceData σ (1 / 2) Φq Φp A Rq Rp Tq Tp

private def
    MorseCancel.NativeConnectionCancellationData.Transverse {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {m : ℕ}
    {f : M → ℝ} {p q : M} (D : MorseCancel.NativeConnectionCancellationData (E := E) f p q m) :
    Prop :=
  Smale.NativeTransversality.At 𝓘(ℝ, Smale.MorseHandle.NegativeSpace D.σ)
    𝓘(ℝ, Smale.MorseHandle.PositiveSpace D.σ) 𝓘(ℝ, Fin m → ℝ) (fun x => D.slices.Q (x, 0))
    (fun y => D.slices.P (0, y)) 0 0

private theorem
    MorseCancel.NativeConnectionCancellationData.cancel {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ} {p q : M}
    (D : MorseCancel.NativeConnectionCancellationData (E := E) f p q m) (htrans : D.Transverse)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f))
    (hp : p ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hq : q ∈ Smale.ManifoldMorse.criticalPoints E f) (hpq : f p < f q) {c d : ℝ} (hc : c < f p)
    (hd : f q < d)
    (hpair : ∀ y ∈ Smale.ManifoldMorse.criticalPoints E f, f y ∈ Set.Icc c d → y = p ∨ y = q) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          (Smale.ManifoldMorse.criticalPoints E g).ncard + 2 =
              (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ y,
                y ∈ Smale.ManifoldMorse.criticalPoints E g ↔
                  y ∈ Smale.ManifoldMorse.criticalPoints E f ∧ y ≠ p ∧ y ≠ q) ∧
              ∀ y, f y ∉ Set.Ioo c d → g =ᶠ[𝓝 y] f := by
  have hh :=
    MorseCancel.cancel_native_endpoint_slice_data D.σ D.signs (by norm_num) D.Φq D.Φp D.A D.slices
      htrans hf hm D.positive_speed D.height_formula D.field D.smooth_field D.fieldQ D.fieldP
      D.vertical D.flow D.integral D.zero D.descent hinj D.positive_Rq D.positive_Rp D.boxQ D.boxP
      (by simpa only [D.endpointQ] using D.basinQ) (by simpa only [D.endpointP] using D.basinP)
      (by simpa only [D.endpointQ, D.endpointP] using D.unique) (by rw [D.endpointP]; exact hp)
      (by rw [D.endpointQ]; exact hq) (by rw [D.endpointP, D.endpointQ]; exact hpq)
      (by rw [D.endpointP]; exact hc) (by rw [D.endpointQ]; exact hd)
      (by simpa only [D.endpointP, D.endpointQ] using hpair)
  simpa only [D.endpointP, D.endpointQ] using hh

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.exists_native_connection_cancellation_data {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {f : M → ℝ}
    {p q x : M} (cp : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (cq : Smale.ManifoldMorse.SignedMorseChart (E := E) f q) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = m + 1)
    (hindex :
      Fintype.card { i // cq.weights i = -1 } = Fintype.card { i // cp.weights i = -1 } + 1)
    (V : (y : M) → TangentSpace 𝓘(ℝ, E) y)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ y ∈ Smale.ManifoldMorse.criticalPoints E f, V y = 0)
    (hdesc : ∀ y, y ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (V y) < 0)
    (F : Flow ℝ M) (hF : ∀ y, IsMIntegralCurve (fun t => F t y) V)
    (hpc : p ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hqc : q ∈ Smale.ManifoldMorse.criticalPoints E f) (hpq : f p < f q) {c d : ℝ} (hc : c < f p)
    (hd : f q < d)
    (hpair : ∀ y ∈ Smale.ManifoldMorse.criticalPoints E f, f y ∈ Set.Icc c d → y = p ∨ y = q)
    (hp : Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p))
    (hq : Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q))
    (hunique :
      ∀ y,
        Filter.Tendsto (fun t => F t y) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 p) → ∃ t, F t x = y)
    (heqp : ∀ᶠ y in 𝓝 p, V y = cp.descentField y) (heqq : ∀ᶠ y in 𝓝 q, V y = cq.descentField y) :
    ∃ D : NativeConnectionCancellationData (E := E) f p q m,
      (∀ y ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ z in 𝓝 y, D.field z = V z) ∧
        (∀ y,
            Set.range (fun t => D.flow t y) = Set.range (fun t => F t y) ∧
              (∀ z,
                  Filter.Tendsto (fun t => D.flow t y) Filter.atTop (𝓝 z) ↔
                    Filter.Tendsto (fun t => F t y) Filter.atTop (𝓝 z)) ∧
                ∀ z,
                  Filter.Tendsto (fun t => D.flow t y) Filter.atBot (𝓝 z) ↔
                    Filter.Tendsto (fun t => F t y) Filter.atBot (𝓝 z)) ∧
          ∃ t, F t x = D.A 0 := by
  obtain
    ⟨x₀, r, b, W, G, U, A, hxp, hxq, hr, hW, hG, hzeros, hneg, hgerms, hmono, hp₀, hq₀, hunique₀,
      _, h0U, hAsource, hAaxis, hheight, hAfield, hgeometry, hreference⟩ :=
    Degree.FlowTimeChange.exists_normalized_connection_cylinder hf hdim V hV hzero hdesc F hF hpq
      hc hd hpair hp hq hunique
  have hgp : ∀ᶠ y in 𝓝 p, W y = cp.descentField y := by
    filter_upwards [hgerms p hpc, heqp] with y h₁ h₂
    exact h₁.trans h₂
  have hgq : ∀ᶠ y in 𝓝 q, W y = cq.descentField y := by
    filter_upwards [hgerms q hqc, heqq] with y h₁ h₂
    exact h₁.trans h₂
  obtain
    ⟨σ, Ψq, Ψp, B, Rq, Rp, Tq, Tp, hσ, hRq, hRp, hqval, hpval, hqbox, hpbox, hqfield, hpfield,
      hqbasin, hpbasin, hBsub, _, hBmap, hBfield, ⟨D⟩⟩ :=
    exists_actual_connection_slice_data cp cq hf.continuous hdim hindex hW G hG hmono hxp hxq hp₀
      hq₀ hgp hgq A hAsource h0U hAfield hAaxis
  have hB0 : B (0, 0) = x₀ := by rw [hBmap, hAaxis, G.map_zero_apply]
  refine
    ⟨{  σ := σ
        signs := hσ
        field := W
        smooth_field := hW
        flow := G
        integral := hG
        zero := hzeros
        descent := hneg
        Φq := Ψq
        Φp := Ψp
        endpointQ := hqval
        endpointP := hpval
        fieldQ := hqfield
        fieldP := hpfield
        A := B
        vertical := hBfield
        speed := r
        positive_speed := hr
        height := b
        height_formula := ?_
        Rq := Rq
        Rp := Rp
        Tq := Tq
        Tp := Tp
        positive_Rq := hRq
        positive_Rp := hRp
        boxQ := hqbox
        boxP := hpbox
        basinQ := hqbasin
        basinP := hpbasin
        unique := ?_
        slices := D }, hgerms, hgeometry, ?_⟩
  · intro z hz ht
    rw [hBmap]
    exact hheight z (hBsub hz) ⟨ht.1.le, ht.2.le⟩
  · intro y hyq hyp
    rw [hB0]
    exact hunique₀ y hyq hyp
  · change ∃ t, F t x = B (0, 0)
    rw [hB0]
    exact hreference

private theorem Degree.TransverseGerms.derivative_first_of_time_independent_label {A Z : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : ℝ × A → Z × ℝ} {f : A → Z} (hF : DifferentiableAt ℝ F 0) (hf : DifferentiableAt ℝ f 0)
    (hlabel : (fun u : ℝ × A => (F u).1) =ᶠ[𝓝 0] (fun u : ℝ × A => f u.2)) :
    ∀ u : ℝ × A, (fderiv ℝ F 0 u).1 = fderiv ℝ f 0 u.2 := by
  have hsnd : HasFDerivAt (fun u : ℝ × A => u.2) (ContinuousLinearMap.snd ℝ ℝ A) 0 :=
    (ContinuousLinearMap.snd ℝ ℝ A).hasFDerivAt
  have hd :
    HasFDerivAt (fun u : ℝ × A => f u.2) ((fderiv ℝ f 0).comp (ContinuousLinearMap.snd ℝ ℝ A))
      0 :=
    hf.hasFDerivAt.comp (f := fun u : ℝ × A => u.2) 0 hsnd
  have heq : fderiv ℝ (fun u : ℝ × A => (F u).1) 0 = fderiv ℝ (fun u : ℝ × A => f u.2) 0 :=
    hlabel.fderiv_eq
  rw [hF.hasFDerivAt.fst.fderiv, hd.fderiv] at heq
  intro u
  exact congrArg (fun L : (ℝ × A) →L[ℝ] Z => L u) heq

private theorem
    Degree.TransverseGerms.transverse_labels_of_time_independent_flow_sheets {A B Z : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {F : ℝ × A → Z × ℝ} {G : ℝ × B → Z × ℝ} {f : A → Z}
    {g : B → Z} (hF : DifferentiableAt ℝ F 0) (hG : DifferentiableAt ℝ G 0)
    (hf : DifferentiableAt ℝ f 0) (hg : DifferentiableAt ℝ g 0)
    (hlabelF : (fun u : ℝ × A => (F u).1) =ᶠ[𝓝 0] (fun u : ℝ × A => f u.2))
    (hlabelG : (fun u : ℝ × B => (G u).1) =ᶠ[𝓝 0] (fun u : ℝ × B => g u.2))
    (htrans : Function.Surjective ((fderiv ℝ F 0).coprod (fderiv ℝ G 0))) :
    Function.Surjective ((fderiv ℝ f 0).coprod (fderiv ℝ g 0)) := by
  have hfirstF := derivative_first_of_time_independent_label hF hf hlabelF
  have hfirstG := derivative_first_of_time_independent_label hG hg hlabelG
  intro z
  obtain ⟨⟨u, v⟩, huv⟩ := htrans (z, 0)
  refine ⟨(u.2, v.2), ?_⟩
  change fderiv ℝ f 0 u.2 + fderiv ℝ g 0 v.2 = z
  rw [← hfirstF u, ← hfirstG v]
  exact congrArg Prod.fst huv

private theorem Degree.TransverseGerms.transverse_labels_of_native_flow_sheets {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (C : PartialDiffeomorph 𝓘(ℝ, Z × ℝ) 𝓘(ℝ, E) (Z × ℝ) M ∞) (hC0 : (0 : Z × ℝ) ∈ C.source)
    (F : ℝ × A → M) (G : ℝ × B → M) (hF : MDifferentiableAt 𝓘(ℝ, ℝ × A) 𝓘(ℝ, E) F 0)
    (hG : MDifferentiableAt 𝓘(ℝ, ℝ × B) 𝓘(ℝ, E) G 0) (hF0 : F 0 = C 0) (hG0 : G 0 = C 0)
    {f : A → Z} {g : B → Z} (hf : DifferentiableAt ℝ f 0) (hg : DifferentiableAt ℝ g 0)
    (hlabelF : (fun u : ℝ × A => (C.symm (F u)).1) =ᶠ[𝓝 0] (fun u : ℝ × A => f u.2))
    (hlabelG : (fun u : ℝ × B => (C.symm (G u)).1) =ᶠ[𝓝 0] (fun u : ℝ × B => g u.2))
    (htrans : Smale.NativeTransversality.At 𝓘(ℝ, ℝ × A) 𝓘(ℝ, ℝ × B) 𝓘(ℝ, E) F G 0 0) :
    Smale.NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) 𝓘(ℝ, Z) f g 0 0 := by
  have hFt : F 0 ∈ C.target := hF0.symm ▸ C.map_source' hC0
  have hGt : G 0 ∈ C.target := hG0.symm ▸ C.map_source' hC0
  have hFb : MDifferentiableAt 𝓘(ℝ, ℝ × A) 𝓘(ℝ, Z × ℝ) (C.symm ∘ F) 0 :=
    (C.symm.mdifferentiableAt (by simp) hFt).comp (f := F) 0 hF
  have hGb : MDifferentiableAt 𝓘(ℝ, ℝ × B) 𝓘(ℝ, Z × ℝ) (C.symm ∘ G) 0 :=
    (C.symm.mdifferentiableAt (by simp) hGt).comp (f := G) 0 hG
  have hcross : G 0 = F 0 := hG0.trans hF0.symm
  have ht :=
    Smale.ChartMapPerturbation.transverse_in_chart C.symm hF hG hcross hFt (htrans hcross)
  rw [mfderiv_eq_fderiv, mfderiv_eq_fderiv] at ht
  have hl :=
    transverse_labels_of_time_independent_flow_sheets hFb.differentiableAt hGb.differentiableAt hf
      hg hlabelF hlabelG ht
  intro _
  rw [mfderiv_eq_fderiv, mfderiv_eq_fderiv]
  exact hl

private def MorseCancel.NativeConnectionCancellationData.outgoingSheet {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {m : ℕ} {f : M → ℝ} {p q : M}
    (D : MorseCancel.NativeConnectionCancellationData (E := E) f p q m)
    (w : ℝ × Smale.MorseHandle.NegativeSpace D.σ) : M :=
  D.flow (w.1 - D.Tq)
    (D.Φq
      (MorseCancel.cubicFlowCylinder D.σ (1 / 2)
        ((Smale.MorseHandle.splitCoordinates D.σ).symm (w.2, 0), D.Tq)))

private def MorseCancel.NativeConnectionCancellationData.incomingSheet {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {m : ℕ} {f : M → ℝ} {p q : M}
    (D : MorseCancel.NativeConnectionCancellationData (E := E) f p q m)
    (w : ℝ × Smale.MorseHandle.PositiveSpace D.σ) : M :=
  D.flow (w.1 - D.Tp)
    (D.Φp
      (MorseCancel.cubicFlowCylinder D.σ (1 / 2)
        ((Smale.MorseHandle.splitCoordinates D.σ).symm (0, w.2), D.Tp)))

private theorem MorseCancel.NativeConnectionCancellationData.outgoingSheet_properties {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {m : ℕ} {f : M → ℝ}
    {p q : M} (D : MorseCancel.NativeConnectionCancellationData (E := E) f p q m) :
    ContMDiffAt 𝓘(ℝ, ℝ × Smale.MorseHandle.NegativeSpace D.σ) 𝓘(ℝ, E) ∞ D.outgoingSheet 0 ∧
      D.outgoingSheet 0 = D.A 0 ∧
        (fun w : ℝ × Smale.MorseHandle.NegativeSpace D.σ =>
            (D.A.symm (D.outgoingSheet w)).1) =ᶠ[𝓝 0]
          (fun w : ℝ × Smale.MorseHandle.NegativeSpace D.σ => D.slices.Q (w.2, 0)) := by
  have hflow :=
    Degree.FlowSuspension.native_vertical_cylinder_flow D.A D.slices.source
      (D.smooth_field.of_le (by simp)) D.vertical D.flow D.integral
  have hQU : D.slices.Q.target ⊆ D.slices.labelDomain := fun _ hz => D.slices.Q_target ▸ hz
  have hQ0 : 0 ∈ D.slices.Q.source := D.slices.Q_source ▸ D.slices.zero_source
  have hh :=
    Degree.FlowSuspension.phase_flow_subsheet_properties D.A D.slices.source D.flow hflow
      D.slices.Q hQU hQ0 D.slices.Q_zero
      (fun u =>
        D.Φq
          (MorseCancel.cubicFlowCylinder D.σ (1 / 2)
            ((Smale.MorseHandle.splitCoordinates D.σ).symm u, D.Tq)))
      D.slices.phaseQ D.Tq D.slices.smooth_phaseQ D.slices.zero_phaseQ D.slices.formulaQ
      (ContinuousLinearMap.inl ℝ (Smale.MorseHandle.NegativeSpace D.σ)
        (Smale.MorseHandle.PositiveSpace D.σ))
  unfold outgoingSheet
  simpa only [ContinuousLinearMap.inl_apply, Prod.fst_zero, Prod.snd_zero, zero_sub] using hh

private theorem MorseCancel.NativeConnectionCancellationData.incomingSheet_properties {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {m : ℕ} {f : M → ℝ}
    {p q : M} (D : MorseCancel.NativeConnectionCancellationData (E := E) f p q m) :
    ContMDiffAt 𝓘(ℝ, ℝ × Smale.MorseHandle.PositiveSpace D.σ) 𝓘(ℝ, E) ∞ D.incomingSheet 0 ∧
      D.incomingSheet 0 = D.A 0 ∧
        (fun w : ℝ × Smale.MorseHandle.PositiveSpace D.σ =>
            (D.A.symm (D.incomingSheet w)).1) =ᶠ[𝓝 0]
          (fun w : ℝ × Smale.MorseHandle.PositiveSpace D.σ => D.slices.P (0, w.2)) := by
  have hflow :=
    Degree.FlowSuspension.native_vertical_cylinder_flow D.A D.slices.source
      (D.smooth_field.of_le (by simp)) D.vertical D.flow D.integral
  have hPU : D.slices.P.target ⊆ D.slices.labelDomain := fun _ hz => D.slices.P_target ▸ hz
  have hP0 : 0 ∈ D.slices.P.source := by
    rw [D.slices.P_source, ← D.slices.H_zero]
    exact D.slices.H.map_source' D.slices.zero_source
  have hh :=
    Degree.FlowSuspension.phase_flow_subsheet_properties D.A D.slices.source D.flow hflow
      D.slices.P hPU hP0 D.slices.P_zero
      (fun u =>
        D.Φp
          (MorseCancel.cubicFlowCylinder D.σ (1 / 2)
            ((Smale.MorseHandle.splitCoordinates D.σ).symm u, D.Tp)))
      D.slices.phaseP D.Tp D.slices.smooth_phaseP D.slices.zero_phaseP D.slices.formulaP
      (ContinuousLinearMap.inr ℝ (Smale.MorseHandle.NegativeSpace D.σ)
        (Smale.MorseHandle.PositiveSpace D.σ))
  unfold incomingSheet
  simpa only [ContinuousLinearMap.inr_apply, Prod.fst_zero, Prod.snd_zero, zero_sub] using hh

private theorem
    MorseCancel.NativeConnectionCancellationData.transverse_of_native_sheets {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {m : ℕ} {f : M → ℝ}
    {p q : M} (D : MorseCancel.NativeConnectionCancellationData (E := E) f p q m)
    (htrans :
      Smale.NativeTransversality.At 𝓘(ℝ, ℝ × Smale.MorseHandle.NegativeSpace D.σ)
        𝓘(ℝ, ℝ × Smale.MorseHandle.PositiveSpace D.σ) 𝓘(ℝ, E) D.outgoingSheet D.incomingSheet 0
        0) :
    D.Transverse := by
  obtain ⟨hout, hout0, houtlabel⟩ := D.outgoingSheet_properties
  obtain ⟨hin, hin0, hinlabel⟩ := D.incomingSheet_properties
  have hQ0 : 0 ∈ D.slices.Q.source := D.slices.Q_source ▸ D.slices.zero_source
  have hP0 : 0 ∈ D.slices.P.source := by
    rw [D.slices.P_source, ← D.slices.H_zero]
    exact D.slices.H.map_source' D.slices.zero_source
  have hQdiff :=
    (D.slices.Q.contMDiffOn_toFun.contDiffOn.contDiffAt
          (D.slices.Q.open_source.mem_nhds hQ0)).differentiableAt
      (by simp)
  have hPdiff :=
    (D.slices.P.contMDiffOn_toFun.contDiffOn.contDiffAt
          (D.slices.P.open_source.mem_nhds hP0)).differentiableAt
      (by simp)
  have hq :
    DifferentiableAt ℝ (fun x : Smale.MorseHandle.NegativeSpace D.σ => D.slices.Q (x, 0)) 0 :=
    hQdiff.comp (f := fun x : Smale.MorseHandle.NegativeSpace D.σ => (x, 0)) 0
      (ContinuousLinearMap.inl ℝ (Smale.MorseHandle.NegativeSpace D.σ)
          (Smale.MorseHandle.PositiveSpace D.σ)).differentiableAt
  have hp :
    DifferentiableAt ℝ (fun y : Smale.MorseHandle.PositiveSpace D.σ => D.slices.P (0, y)) 0 :=
    hPdiff.comp (f := fun y : Smale.MorseHandle.PositiveSpace D.σ => (0, y)) 0
      (ContinuousLinearMap.inr ℝ (Smale.MorseHandle.NegativeSpace D.σ)
          (Smale.MorseHandle.PositiveSpace D.σ)).differentiableAt
  have hA0 : (0 : (Fin m → ℝ) × ℝ) ∈ D.A.source := by
    rw [D.slices.source]
    exact ⟨D.slices.zero_domain, Set.mem_univ _⟩
  exact
    Degree.TransverseGerms.transverse_labels_of_native_flow_sheets D.A hA0 D.outgoingSheet
      D.incomingSheet (hout.mdifferentiableAt (by simp)) (hin.mdifferentiableAt (by simp)) hout0
      hin0 hq hp houtlabel hinlabel htrans

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.NativeConnectionCancellationData.outgoing_basin_chart {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {m : ℕ} {f : M → ℝ}
    {p q : M} (D : MorseCancel.NativeConnectionCancellationData (E := E) f p q m) :
    ∃ P :
      PartialDiffeomorph
        𝓘(ℝ, (Smale.MorseHandle.NegativeSpace D.σ × Smale.MorseHandle.PositiveSpace D.σ) × ℝ)
        𝓘(ℝ, E) ((Smale.MorseHandle.NegativeSpace D.σ × Smale.MorseHandle.PositiveSpace D.σ) × ℝ)
        M ∞,
      (0 : (Smale.MorseHandle.NegativeSpace D.σ × Smale.MorseHandle.PositiveSpace D.σ) × ℝ) ∈
          P.source ∧
        P 0 = D.A 0 ∧
          D.outgoingSheet =ᶠ[𝓝 0]
              (fun w : ℝ × Smale.MorseHandle.NegativeSpace D.σ => P ((w.2, 0), w.1)) ∧
            ∀ w ∈ P.source,
              Filter.Tendsto (fun t => D.flow t (P w)) Filter.atBot (𝓝 q) ↔ w.1.2 = 0 := by
  have hflow :=
    Degree.FlowSuspension.native_vertical_cylinder_flow D.A D.slices.source
      (D.smooth_field.of_le (by simp)) D.vertical D.flow D.integral
  have hQU : D.slices.Q.target ⊆ D.slices.labelDomain := fun _ hz => D.slices.Q_target ▸ hz
  have hQ0 : 0 ∈ D.slices.Q.source := D.slices.Q_source ▸ D.slices.zero_source
  let S := fun u =>
    D.Φq
      (MorseCancel.cubicFlowCylinder D.σ (1 / 2)
        ((Smale.MorseHandle.splitCoordinates D.σ).symm u, D.Tq))
  have hbasin (u) (hu : u ∈ D.slices.Q.source) :
    Filter.Tendsto (fun t => D.flow t (S u)) Filter.atBot (𝓝 q) ↔ u.2 = 0 :=
    MorseCancel.outgoing_cubic_slice_basin D.σ D.signs (1 / 2) D.Tq D.Φq D.flow D.basinQ u
      (D.boxQ (D.slices.sliceQ u hu))
  obtain ⟨P, -, h0P, hP0, hformula, hplane⟩ :=
    Degree.FlowSuspension.exists_phase_flow_basin_chart D.A D.slices.source D.flow hflow
      D.slices.Q hQU hQ0 D.slices.Q_zero S D.slices.phaseQ D.Tq D.slices.smooth_phaseQ
      D.slices.zero_phaseQ D.slices.formulaQ
      (fun y => Filter.Tendsto (fun t => D.flow t y) Filter.atBot (𝓝 q))
      (fun t y => MorseCancel.flow_time_atBot_limit_iff D.flow t y q) (fun u => u.2 = 0) hbasin
  have heq :=
    Degree.FlowSuspension.phase_flow_chart_subsheet_germ P D.slices.Q.open_source hQ0 D.flow S
      D.Tq hformula
      (ContinuousLinearMap.inl ℝ (Smale.MorseHandle.NegativeSpace D.σ)
        (Smale.MorseHandle.PositiveSpace D.σ))
  refine ⟨P, h0P, hP0, ?_, hplane⟩
  unfold outgoingSheet
  simpa only [ContinuousLinearMap.inl_apply] using heq

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.NativeConnectionCancellationData.incoming_basin_chart {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {m : ℕ} {f : M → ℝ}
    {p q : M} (D : MorseCancel.NativeConnectionCancellationData (E := E) f p q m) :
    ∃ P :
      PartialDiffeomorph
        𝓘(ℝ, (Smale.MorseHandle.NegativeSpace D.σ × Smale.MorseHandle.PositiveSpace D.σ) × ℝ)
        𝓘(ℝ, E) ((Smale.MorseHandle.NegativeSpace D.σ × Smale.MorseHandle.PositiveSpace D.σ) × ℝ)
        M ∞,
      (0 : (Smale.MorseHandle.NegativeSpace D.σ × Smale.MorseHandle.PositiveSpace D.σ) × ℝ) ∈
          P.source ∧
        P 0 = D.A 0 ∧
          D.incomingSheet =ᶠ[𝓝 0]
              (fun w : ℝ × Smale.MorseHandle.PositiveSpace D.σ => P ((0, w.2), w.1)) ∧
            ∀ w ∈ P.source,
              Filter.Tendsto (fun t => D.flow t (P w)) Filter.atTop (𝓝 p) ↔ w.1.1 = 0 := by
  have hflow :=
    Degree.FlowSuspension.native_vertical_cylinder_flow D.A D.slices.source
      (D.smooth_field.of_le (by simp)) D.vertical D.flow D.integral
  have hPU : D.slices.P.target ⊆ D.slices.labelDomain := fun _ hz => D.slices.P_target ▸ hz
  have hP0 : 0 ∈ D.slices.P.source := by
    rw [D.slices.P_source, ← D.slices.H_zero]
    exact D.slices.H.map_source' D.slices.zero_source
  let S := fun u =>
    D.Φp
      (MorseCancel.cubicFlowCylinder D.σ (1 / 2)
        ((Smale.MorseHandle.splitCoordinates D.σ).symm u, D.Tp))
  have hbasin (u) (hu : u ∈ D.slices.P.source) :
    Filter.Tendsto (fun t => D.flow t (S u)) Filter.atTop (𝓝 p) ↔ u.1 = 0 :=
    MorseCancel.incoming_cubic_slice_basin D.σ (1 / 2) D.Tp D.Φp D.flow D.basinP u
      (D.boxP (D.slices.sliceP u hu))
  obtain ⟨P, -, h0P, hPzero, hformula, hplane⟩ :=
    Degree.FlowSuspension.exists_phase_flow_basin_chart D.A D.slices.source D.flow hflow
      D.slices.P hPU hP0 D.slices.P_zero S D.slices.phaseP D.Tp D.slices.smooth_phaseP
      D.slices.zero_phaseP D.slices.formulaP
      (fun y => Filter.Tendsto (fun t => D.flow t y) Filter.atTop (𝓝 p))
      (fun t y => MorseCancel.flow_time_atTop_limit_iff D.flow t y p) (fun u => u.1 = 0) hbasin
  have heq :=
    Degree.FlowSuspension.phase_flow_chart_subsheet_germ P D.slices.P.open_source hP0 D.flow S
      D.Tp hformula
      (ContinuousLinearMap.inr ℝ (Smale.MorseHandle.NegativeSpace D.σ)
        (Smale.MorseHandle.PositiveSpace D.σ))
  refine ⟨P, h0P, hPzero, ?_, hplane⟩
  unfold incomingSheet
  simpa only [ContinuousLinearMap.inr_apply] using heq

private theorem Degree.TransverseGerms.native_transversality_of_sheet_factorizations
    {A B U V E HU HV HE X Y M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace HU] [TopologicalSpace HV] [TopologicalSpace HE]
    {I : ModelWithCorners ℝ U HU} {I' : ModelWithCorners ℝ V HV} {J : ModelWithCorners ℝ E HE}
    [TopologicalSpace X] [ChartedSpace HU X] [TopologicalSpace Y] [ChartedSpace HV Y]
    [TopologicalSpace M] [ChartedSpace HE M] {F : X → M} {G : Y → M} {f : A → M} {g : B → M}
    {u : X → A} {v : Y → B} {x : X} {y : Y} (hf : MDifferentiableAt 𝓘(ℝ, A) J f 0)
    (hg : MDifferentiableAt 𝓘(ℝ, B) J g 0) (hu : MDifferentiableAt I 𝓘(ℝ, A) u x)
    (hv : MDifferentiableAt I' 𝓘(ℝ, B) v y) (hu0 : u x = 0) (hv0 : v y = 0)
    (hF : F =ᶠ[𝓝 x] (f ∘ u)) (hG : G =ᶠ[𝓝 y] (g ∘ v)) (hcross : G y = F x)
    (htrans : Smale.NativeTransversality.At I I' J F G x y) :
    Smale.NativeTransversality.At 𝓘(ℝ, A) 𝓘(ℝ, B) J f g 0 0 := by
  have hfx : MDifferentiableAt 𝓘(ℝ, A) J f (u x) := hu0 ▸ hf
  have hgy : MDifferentiableAt 𝓘(ℝ, B) J g (v y) := hv0 ▸ hg
  have hFd :
    (mfderiv I J F x : U →L[ℝ] E) =
      (mfderiv 𝓘(ℝ, A) J f 0 : A →L[ℝ] E).comp (mfderiv I 𝓘(ℝ, A) u x) := by
    have heq : (mfderiv I J F x : U →L[ℝ] E) = mfderiv I J (f ∘ u) x := hF.mfderiv_eq
    rw [heq, mfderiv_comp x hfx hu, hu0]
  have hGd :
    (mfderiv I' J G y : V →L[ℝ] E) =
      (mfderiv 𝓘(ℝ, B) J g 0 : B →L[ℝ] E).comp (mfderiv I' 𝓘(ℝ, B) v y) := by
    have heq : (mfderiv I' J G y : V →L[ℝ] E) = mfderiv I' J (g ∘ v) y := hG.mfderiv_eq
    rw [heq, mfderiv_comp y hgy hv, hv0]
  intro _ z
  obtain ⟨⟨a, b⟩, hab⟩ := htrans hcross z
  refine ⟨(mfderiv I 𝓘(ℝ, A) u x a, mfderiv I' 𝓘(ℝ, B) v y b), ?_⟩
  rw [hFd, hGd] at hab
  exact hab

private theorem Degree.TransverseGerms.exists_native_plane_factorization {A Z U E HU HE X M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace HU] [TopologicalSpace HE] {I : ModelWithCorners ℝ U HU}
    {J : ModelWithCorners ℝ E HE} [TopologicalSpace X] [ChartedSpace HU X] [TopologicalSpace M]
    [ChartedSpace HE M] (P : PartialDiffeomorph 𝓘(ℝ, Z) J Z M ∞) (hP0 : (0 : Z) ∈ P.source)
    (L : A →L[ℝ] Z) (R : Z →L[ℝ] A) (hRL : ∀ a, R (L a) = a) {F : X → M} {x : X}
    (hF : MDifferentiableAt I J F x) (hx : F x = P 0)
    (hplane : ∀ᶠ y in 𝓝 x, ∃ a, P.symm (F y) = L a) :
    ∃ u : X → A, MDifferentiableAt I 𝓘(ℝ, A) u x ∧ u x = 0 ∧ F =ᶠ[𝓝 x] (fun y => P (L (u y))) := by
  let u : X → A := fun y => R (P.symm (F y))
  have hxt : F x ∈ P.target := hx.symm ▸ P.map_source' hP0
  have hi := (P.symm.mdifferentiableAt (by simp) hxt).comp x hF
  have hu : MDifferentiableAt I 𝓘(ℝ, A) u x := R.differentiableAt.mdifferentiableAt.comp x hi
  have hu0 : u x = 0 := by
    change R (P.symm (F x)) = 0
    have hi0 : P.symm (P 0) = 0 := P.left_inv' hP0
    rw [hx, hi0, map_zero]
  refine ⟨u, hu, hu0, ?_⟩
  filter_upwards [hF.continuousAt (P.open_target.mem_nhds hxt), hplane] with y hy hplaneY
  obtain ⟨a, ha⟩ := hplaneY
  change F y = P (L (R (P.symm (F y))))
  rw [ha, hRL]
  exact (P.right_inv' hy).symm.trans (congrArg P ha)

private theorem
    Degree.TransverseGerms.exists_native_plane_sheet_factorization {A Z U E HU HE X M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace HU] [TopologicalSpace HE] {I : ModelWithCorners ℝ U HU}
    {J : ModelWithCorners ℝ E HE} [TopologicalSpace X] [ChartedSpace HU X] [TopologicalSpace M]
    [ChartedSpace HE M] (P : PartialDiffeomorph 𝓘(ℝ, Z) J Z M ∞) (hP0 : (0 : Z) ∈ P.source)
    (L : A →L[ℝ] Z) (R : Z →L[ℝ] A) (hRL : ∀ a, R (L a) = a) {F : X → M} {x : X}
    (hF : MDifferentiableAt I J F x) (hx : F x = P 0)
    (hplane : ∀ᶠ y in 𝓝 x, ∃ a, P.symm (F y) = L a) {f : A → M}
    (hmodel : f =ᶠ[𝓝 0] (fun a => P (L a))) :
    ∃ u : X → A, MDifferentiableAt I 𝓘(ℝ, A) u x ∧ u x = 0 ∧ F =ᶠ[𝓝 x] (f ∘ u) := by
  obtain ⟨u, hu, hu0, hfactor⟩ := exists_native_plane_factorization P hP0 L R hRL hF hx hplane
  have hut : Filter.Tendsto u (𝓝 x) (𝓝 (0 : A)) := hu0 ▸ hu.continuousAt
  have hcomp := hmodel.comp_tendsto hut
  exact ⟨u, hu, hu0, hfactor.trans hcomp.symm⟩

private theorem
    Degree.TransverseGerms.exists_native_basin_sheet_factorization {A Z U E HU HE X M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace HU] [TopologicalSpace HE] {I : ModelWithCorners ℝ U HU}
    {J : ModelWithCorners ℝ E HE} [TopologicalSpace X] [ChartedSpace HU X] [TopologicalSpace M]
    [ChartedSpace HE M] (P : PartialDiffeomorph 𝓘(ℝ, Z) J Z M ∞) (hP0 : (0 : Z) ∈ P.source)
    (L : A →L[ℝ] Z) (R : Z →L[ℝ] A) (hRL : ∀ a, R (L a) = a) {F : X → M} {x : X}
    (hF : MDifferentiableAt I J F x) (hx : F x = P 0) (Basin : M → Prop)
    (hbasin : ∀ z ∈ P.source, Basin (P z) → ∃ a, z = L a) (hFbasin : ∀ᶠ y in 𝓝 x, Basin (F y))
    {f : A → M} (hmodel : f =ᶠ[𝓝 0] (fun a => P (L a))) :
    ∃ u : X → A, MDifferentiableAt I 𝓘(ℝ, A) u x ∧ u x = 0 ∧ F =ᶠ[𝓝 x] (f ∘ u) := by
  have hxt : F x ∈ P.target := hx.symm ▸ P.map_source' hP0
  have hplane : ∀ᶠ y in 𝓝 x, ∃ a, P.symm (F y) = L a := by
    filter_upwards [hF.continuousAt (P.open_target.mem_nhds hxt), hFbasin] with y hy hby
    have hb : Basin (P (P.symm (F y))) := (P.right_inv' hy).symm ▸ hby
    exact hbasin (P.symm (F y)) (P.map_target' hy) hb
  exact exists_native_plane_sheet_factorization P hP0 L R hRL hF hx hplane hmodel

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.NativeConnectionCancellationData.outgoing_basin_factorization {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {m : ℕ} {f : M → ℝ}
    {p q : M} {U H X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [TopologicalSpace H]
    {I : ModelWithCorners ℝ U H} [TopologicalSpace X] [ChartedSpace H X]
    (D : MorseCancel.NativeConnectionCancellationData (E := E) f p q m) {F : X → M} {x : X}
    (hF : MDifferentiableAt I 𝓘(ℝ, E) F x) (hx : F x = D.A 0)
    (hbasin : ∀ᶠ y in 𝓝 x, Filter.Tendsto (fun t => D.flow t (F y)) Filter.atBot (𝓝 q)) :
    ∃ u : X → ℝ × Smale.MorseHandle.NegativeSpace D.σ,
      MDifferentiableAt I 𝓘(ℝ, ℝ × Smale.MorseHandle.NegativeSpace D.σ) u x ∧
        u x = 0 ∧ F =ᶠ[𝓝 x] (D.outgoingSheet ∘ u) := by
  obtain ⟨P, hP0, hzero, hmodel, hplane⟩ := D.outgoing_basin_chart
  let A := Smale.MorseHandle.NegativeSpace D.σ
  let B := Smale.MorseHandle.PositiveSpace D.σ
  let L : (ℝ × A) →L[ℝ] ((A × B) × ℝ) :=
    ((ContinuousLinearMap.inl ℝ A B).comp (ContinuousLinearMap.snd ℝ ℝ A)).prod
      (ContinuousLinearMap.fst ℝ ℝ A)
  let R : ((A × B) × ℝ) →L[ℝ] (ℝ × A) :=
    (ContinuousLinearMap.snd ℝ (A × B) ℝ).prod
      ((ContinuousLinearMap.fst ℝ A B).comp (ContinuousLinearMap.fst ℝ (A × B) ℝ))
  have hRL (a : ℝ × A) : R (L a) = a := rfl
  have hp (w) (hw : w ∈ P.source)
    (hb : Filter.Tendsto (fun t => D.flow t (P w)) Filter.atBot (𝓝 q)) : ∃ a, w = L a := by
    have hz := (hplane w hw).mp hb
    refine ⟨(w.2, w.1.1), ?_⟩
    exact Prod.ext (Prod.ext rfl hz) rfl
  exact
    Degree.TransverseGerms.exists_native_basin_sheet_factorization P hP0 L R hRL hF
      (hx.trans hzero.symm) (fun y => Filter.Tendsto (fun t => D.flow t y) Filter.atBot (𝓝 q)) hp
      hbasin hmodel

attribute [local instance 100] Classical.propDecidable in
private theorem
    MorseCancel.NativeConnectionCancellationData.incoming_basin_factorization {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {m : ℕ} {f : M → ℝ}
    {p q : M} {U H X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [TopologicalSpace H]
    {I : ModelWithCorners ℝ U H} [TopologicalSpace X] [ChartedSpace H X]
    (D : MorseCancel.NativeConnectionCancellationData (E := E) f p q m) {F : X → M} {x : X}
    (hF : MDifferentiableAt I 𝓘(ℝ, E) F x) (hx : F x = D.A 0)
    (hbasin : ∀ᶠ y in 𝓝 x, Filter.Tendsto (fun t => D.flow t (F y)) Filter.atTop (𝓝 p)) :
    ∃ u : X → ℝ × Smale.MorseHandle.PositiveSpace D.σ,
      MDifferentiableAt I 𝓘(ℝ, ℝ × Smale.MorseHandle.PositiveSpace D.σ) u x ∧
        u x = 0 ∧ F =ᶠ[𝓝 x] (D.incomingSheet ∘ u) := by
  obtain ⟨P, hP0, hzero, hmodel, hplane⟩ := D.incoming_basin_chart
  let A := Smale.MorseHandle.NegativeSpace D.σ
  let B := Smale.MorseHandle.PositiveSpace D.σ
  let L : (ℝ × B) →L[ℝ] ((A × B) × ℝ) :=
    ((ContinuousLinearMap.inr ℝ A B).comp (ContinuousLinearMap.snd ℝ ℝ B)).prod
      (ContinuousLinearMap.fst ℝ ℝ B)
  let R : ((A × B) × ℝ) →L[ℝ] (ℝ × B) :=
    (ContinuousLinearMap.snd ℝ (A × B) ℝ).prod
      ((ContinuousLinearMap.snd ℝ A B).comp (ContinuousLinearMap.fst ℝ (A × B) ℝ))
  have hRL (a : ℝ × B) : R (L a) = a := rfl
  have hp (w) (hw : w ∈ P.source)
    (hb : Filter.Tendsto (fun t => D.flow t (P w)) Filter.atTop (𝓝 p)) : ∃ a, w = L a := by
    have hz := (hplane w hw).mp hb
    refine ⟨(w.2, w.1.2), ?_⟩
    exact Prod.ext (Prod.ext hz rfl) rfl
  exact
    Degree.TransverseGerms.exists_native_basin_sheet_factorization P hP0 L R hRL hF
      (hx.trans hzero.symm) (fun y => Filter.Tendsto (fun t => D.flow t y) Filter.atTop (𝓝 p)) hp
      hbasin hmodel

private theorem MorseCancel.NativeConnectionCancellationData.transverse_of_native_basin_sheets
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {m : ℕ} {f : M → ℝ} {p q : M} {U V H H' X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ U H} {I' : ModelWithCorners ℝ V H'} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    (D : MorseCancel.NativeConnectionCancellationData (E := E) f p q m) {F : X → M} {G : Y → M}
    {x : X} {y : Y} (hF : MDifferentiableAt I 𝓘(ℝ, E) F x) (hG : MDifferentiableAt I' 𝓘(ℝ, E) G y)
    (hx : F x = D.A 0) (hy : G y = D.A 0)
    (hFbasin : ∀ᶠ z in 𝓝 x, Filter.Tendsto (fun t => D.flow t (F z)) Filter.atBot (𝓝 q))
    (hGbasin : ∀ᶠ z in 𝓝 y, Filter.Tendsto (fun t => D.flow t (G z)) Filter.atTop (𝓝 p))
    (htrans : Smale.NativeTransversality.At I I' 𝓘(ℝ, E) F G x y) : D.Transverse := by
  obtain ⟨u, hu, hu0, hFu⟩ := D.outgoing_basin_factorization hF hx hFbasin
  obtain ⟨v, hv, hv0, hGv⟩ := D.incoming_basin_factorization hG hy hGbasin
  apply D.transverse_of_native_sheets
  exact
    Degree.TransverseGerms.native_transversality_of_sheet_factorizations
      (D.outgoingSheet_properties.1.mdifferentiableAt (by simp))
      (D.incomingSheet_properties.1.mdifferentiableAt (by simp)) hu hv hu0 hv0 hFu hGv
      (hy.trans hx.symm) htrans

private theorem MorseCancel.NativeConnectionCancellationData.cancel_of_transverse_basin_sheets
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {m : ℕ} {f : M → ℝ} {p q : M} {U V H H' X Y : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ U H} {I' : ModelWithCorners ℝ V H'} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
    (D : MorseCancel.NativeConnectionCancellationData (E := E) f p q m) {F : X → M} {G : Y → M}
    {x : X} {y : Y} (hF : MDifferentiableAt I 𝓘(ℝ, E) F x) (hG : MDifferentiableAt I' 𝓘(ℝ, E) G y)
    (hx : F x = D.A 0) (hy : G y = D.A 0)
    (hFbasin : ∀ᶠ z in 𝓝 x, Filter.Tendsto (fun t => D.flow t (F z)) Filter.atBot (𝓝 q))
    (hGbasin : ∀ᶠ z in 𝓝 y, Filter.Tendsto (fun t => D.flow t (G z)) Filter.atTop (𝓝 p))
    (htrans : Smale.NativeTransversality.At I I' 𝓘(ℝ, E) F G x y)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f))
    (hp : p ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hq : q ∈ Smale.ManifoldMorse.criticalPoints E f) (hpq : f p < f q) {c d : ℝ} (hc : c < f p)
    (hd : f q < d)
    (hpair : ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, f z ∈ Set.Icc c d → z = p ∨ z = q) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          (Smale.ManifoldMorse.criticalPoints E g).ncard + 2 =
              (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ z,
                z ∈ Smale.ManifoldMorse.criticalPoints E g ↔
                  z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q) ∧
              ∀ z, f z ∉ Set.Ioo c d → g =ᶠ[𝓝 z] f :=
  D.cancel (D.transverse_of_native_basin_sheets hF hG hx hy hFbasin hGbasin htrans) hf hm hinj hp
    hq hpq hc hd hpair

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.cancel_unique_connection_of_transverse_basin_sheets {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ}
    {A B HA HB X Y : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [TopologicalSpace HA] [TopologicalSpace HB] {I : ModelWithCorners ℝ A HA}
    {I' : ModelWithCorners ℝ B HB} [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y]
    [ChartedSpace HB Y] {f : M → ℝ} {p q z : M}
    (cp : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (cq : Smale.ManifoldMorse.SignedMorseChart (E := E) f q) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = m + 1)
    (hindex :
      Fintype.card { i // cq.weights i = -1 } = Fintype.card { i // cp.weights i = -1 } + 1)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f))
    (hpc : p ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hqc : q ∈ Smale.ManifoldMorse.criticalPoints E f) (hpq : f p < f q) {c d : ℝ} (hc : c < f p)
    (hd : f q < d)
    (hpair : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, f x ∈ Set.Icc c d → x = p ∨ x = q)
    (hp : Filter.Tendsto (fun t => F t z) Filter.atTop (𝓝 p))
    (hq : Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q))
    (hunique :
      ∀ x,
        Filter.Tendsto (fun t => F t x) Filter.atBot (𝓝 q) →
          Filter.Tendsto (fun t => F t x) Filter.atTop (𝓝 p) → ∃ t, F t z = x)
    (heqp : ∀ᶠ x in 𝓝 p, V x = cp.descentField x) (heqq : ∀ᶠ x in 𝓝 q, V x = cq.descentField x)
    {S : X → M} {T : Y → M} {x : X} {y : Y} (hS : MDifferentiableAt I 𝓘(ℝ, E) S x)
    (hT : MDifferentiableAt I' 𝓘(ℝ, E) T y) (hS0 : S x = z) (hT0 : T y = z)
    (hSbasin : ∀ᶠ u in 𝓝 x, Filter.Tendsto (fun t => F t (S u)) Filter.atBot (𝓝 q))
    (hTbasin : ∀ᶠ u in 𝓝 y, Filter.Tendsto (fun t => F t (T u)) Filter.atTop (𝓝 p))
    (htrans : Smale.NativeTransversality.At I I' 𝓘(ℝ, E) S T x y) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          (Smale.ManifoldMorse.criticalPoints E g).ncard + 2 =
              (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
            (∀ x,
                x ∈ Smale.ManifoldMorse.criticalPoints E g ↔
                  x ∈ Smale.ManifoldMorse.criticalPoints E f ∧ x ≠ p ∧ x ≠ q) ∧
              ∀ x, f x ∉ Set.Ioo c d → g =ᶠ[𝓝 x] f := by
  obtain ⟨D, -, hgeometry, t₀, ht₀⟩ :=
    exists_native_connection_cancellation_data cp cq hf hdim hindex V hV hzero hdesc F hF hpc hqc
      hpq hc hd hpair hp hq hunique heqp heqq
  let τ := Degree.SmoothODE.nativeFlowTimeDiffeomorph_of_field hV F hF t₀
  have hτ (u : M) : τ u = F t₀ u := rfl
  have hS' : MDifferentiableAt I 𝓘(ℝ, E) (τ ∘ S) x :=
    (τ.contMDiff.mdifferentiableAt (by simp)).comp x hS
  have hT' : MDifferentiableAt I' 𝓘(ℝ, E) (τ ∘ T) y :=
    (τ.contMDiff.mdifferentiableAt (by simp)).comp y hT
  have hS0' : (τ ∘ S) x = D.A 0 := by rw [Function.comp_apply, hτ, hS0, ht₀]
  have hT0' : (τ ∘ T) y = D.A 0 := by rw [Function.comp_apply, hτ, hT0, ht₀]
  have hSb : ∀ᶠ u in 𝓝 x, Filter.Tendsto (fun t => D.flow t ((τ ∘ S) u)) Filter.atBot (𝓝 q) := by
    filter_upwards [hSbasin] with u hu
    apply ((hgeometry ((τ ∘ S) u)).2.2 q).mpr
    exact (flow_time_atBot_limit_iff F t₀ (S u) q).mpr hu
  have hTb : ∀ᶠ u in 𝓝 y, Filter.Tendsto (fun t => D.flow t ((τ ∘ T) u)) Filter.atTop (𝓝 p) := by
    filter_upwards [hTbasin] with u hu
    apply ((hgeometry ((τ ∘ T) u)).2.1 p).mpr
    exact (flow_time_atTop_limit_iff F t₀ (T u) p).mpr hu
  have ht : Smale.NativeTransversality.At I I' 𝓘(ℝ, E) (τ ∘ S) (τ ∘ T) x y :=
    (Degree.TransverseGerms.native_transversality_partial_diffeomorph_iff τ.toPartialDiffeomorph
          hS hT (hT0.trans hS0.symm) (Set.mem_univ _)).mp
      htrans
  exact
    D.cancel_of_transverse_basin_sheets hS' hT' hS0' hT0' hSb hTb ht hf hm hinj hpc hqc hpq hc hd
      hpair

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.cancel_of_transverse_level_isotopy {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {m : ℕ} {A B HA HB X Y : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace HA] [TopologicalSpace HB] {I : ModelWithCorners ℝ A HA}
    {I' : ModelWithCorners ℝ B HB} [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y]
    [ChartedSpace HB Y] {f : M → ℝ} {p q : M}
    (cp : Smale.ManifoldMorse.SignedMorseChart (E := E) f p)
    (cq : Smale.ManifoldMorse.SignedMorseChart (E := E) f q) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = m + 1)
    (hindex :
      Fintype.card { i // cq.weights i = -1 } = Fintype.card { i // cp.weights i = -1 } + 1)
    (V : (z : M) → TangentSpace 𝓘(ℝ, E) z)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun z => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hzero : ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, V z = 0)
    (hdesc : ∀ z, z ∉ Smale.ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f z (V z) < 0)
    (F : Flow ℝ M) (hF : ∀ z, IsMIntegralCurve (fun t => F t z) V)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f))
    (hpc : p ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hqc : q ∈ Smale.ManifoldMorse.criticalPoints E f) {l u a b c : ℝ} (hl : l < f p)
    (hu : f q < u)
    (hpair : ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, f z ∈ Set.Icc l u → z = p ∨ z = q)
    (ha : a < c) (hb : c < b) (hpc' : f p < c) (hqc' : c < f q)
    (hband : ∀ z, f z ∈ Set.Icc a b → z ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hreg : ∀ z, f z = c → z ∉ Smale.ManifoldMorse.criticalPoints E f)
    (heqp : ∀ᶠ z in 𝓝 p, V z = cp.descentField z) (heqq : ∀ᶠ z in 𝓝 q, V z = cq.descentField z) :
    letI := Smale.RegularLevel.chartedSpace hf hreg
    ∀ D :
      Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
        { z : M // f z = c } { z : M // f z = c } ∞,
      Smale.SupportedDiffeomorph.IsotopicToIdentity D →
        {z : { w : M // f w = c } |
                Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q) ∧
                  Filter.Tendsto (fun t => F t (D z)) Filter.atTop (𝓝 p)}.ncard =
            1 →
          ∀ (α : X → { z : M // f z = c }) (β : Y → { z : M // f z = c }) (x : X) (y : Y),
            MDifferentiableAt I 𝓘(ℝ, Smale.RegularLevel.Model E) α x →
              MDifferentiableAt I' 𝓘(ℝ, Smale.RegularLevel.Model E) β y →
                β y = α x →
                  Smale.NativeTransversality.At I I' 𝓘(ℝ, Smale.RegularLevel.Model E) α β x y →
                    (∀ᶠ z in 𝓝 x, Filter.Tendsto (fun t => F t (α z)) Filter.atBot (𝓝 q)) →
                      (∀ᶠ z in 𝓝 y, Filter.Tendsto (fun t => F t (D (β z))) Filter.atTop (𝓝 p)) →
                        ∃ g : M → ℝ,
                          ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
                            Smale.ManifoldMorse.IsMorse E g ∧
                              (Smale.ManifoldMorse.criticalPoints E g).ncard + 2 =
                                  (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
                                (∀ z,
                                    z ∈ Smale.ManifoldMorse.criticalPoints E g ↔
                                      z ∈ Smale.ManifoldMorse.criticalPoints E f ∧
                                        z ≠ p ∧ z ≠ q) ∧
                                  ∀ z, f z ∉ Set.Ioo l u → g =ᶠ[𝓝 z] f := by
  let _ := Smale.RegularLevel.chartedSpace hf hreg
  let _ := Smale.RegularLevel.isManifold hf hreg
  intro D hD hcount α β x y hα hβ hcross htrans hαbasin hβbasin
  obtain
    ⟨r, C, W, V', H, G, -, -, -, -, -, -, hgeometry, hV', hG, hzeros, hneg, hgerms, -, hend, -,
      hleft, hright⟩ :=
    Degree.FlowSuspension.exists_native_regular_level_isotopy_realization hf hV hdesc F hF ha hb
      hband hreg (α x) D hD
  obtain ⟨hback, hforward⟩ :=
    Degree.FlowSuspension.whole_level_basins_of_holonomy F H G Subtype.val D
      (fun z => (hgeometry z).2.1) (fun z => (hgeometry z).2.2) hend hleft hright
  have hαb : ∀ᶠ z in 𝓝 x, Filter.Tendsto (fun t => G t (α z)) Filter.atBot (𝓝 q) := by
    filter_upwards [hαbasin] with z hz
    exact (hback (α z) q).mpr hz
  have hβb : ∀ᶠ z in 𝓝 y, Filter.Tendsto (fun t => G t (β z)) Filter.atTop (𝓝 p) := by
    filter_upwards [hβbasin] with z hz
    exact (hforward (β z) p).mpr hz
  obtain ⟨z₀, hz₀⟩ := Set.ncard_eq_one.mp hcount
  have hαq : Filter.Tendsto (fun t => F t (α x)) Filter.atBot (𝓝 q) := hαbasin.self_of_nhds
  have hαp : Filter.Tendsto (fun t => F t (D (α x))) Filter.atTop (𝓝 p) := by
    rw [← hcross]
    exact hβbasin.self_of_nhds
  have hαeq : α x = z₀ := by
    have hh :
      α x ∈
        {z : { w : M // f w = c } |
          Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q) ∧
            Filter.Tendsto (fun t => F t (D z)) Filter.atTop (𝓝 p)} :=
      ⟨hαq, hαp⟩
    rw [hz₀] at hh
    exact Set.mem_singleton_iff.mp hh
  have huniq (z : { w : M // f w = c }) (hzq : Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q))
    (hzp : Filter.Tendsto (fun t => F t (D z)) Filter.atTop (𝓝 p)) : z = α x := by
    have hh :
      z ∈
        {z : { w : M // f w = c } |
          Filter.Tendsto (fun t => F t z) Filter.atBot (𝓝 q) ∧
            Filter.Tendsto (fun t => F t (D z)) Filter.atTop (𝓝 p)} :=
      ⟨hzq, hzp⟩
    rw [hz₀] at hh
    exact (Set.mem_singleton_iff.mp hh).trans hαeq.symm
  obtain ⟨hqG, hpG, huniqueG⟩ :=
    Degree.FlowSuspension.unique_connection_of_level_basin_intersection F G hf.continuous hqc'
      hpc' D (fun z => hback z q) (fun z => hforward z p) (α x) hαq hαp huniq
  obtain ⟨hS, hT, hS0, hT0, hSb, hTb, ht⟩ :=
    Degree.FlowSuspension.native_transverse_basin_tubes_of_level_maps hf hreg hV' G hG
      (fun z hz => hneg z (hreg z hz)) α β x y hα hβ hcross htrans hαb hβb
  have hgermp : ∀ᶠ z in 𝓝 p, V' z = cp.descentField z := by
    filter_upwards [hgerms p hpc, heqp] with z hz hz'
    exact hz.trans hz'
  have hgermq : ∀ᶠ z in 𝓝 q, V' z = cq.descentField z := by
    filter_upwards [hgerms q hqc, heqq] with z hz hz'
    exact hz.trans hz'
  exact
    cancel_unique_connection_of_transverse_basin_sheets cp cq hf hm hdim hindex V' hV'
      (fun z hz => (hzeros z).mpr (hzero z hz)) hneg G hG hinj hpc hqc (hpc'.trans hqc') hl hu
      hpair hpG hqG huniqueG hgermp hgermq hS hT hS0 hT0 hSb hTb ht

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.surjective_beltNormal_derivative {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (v : Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    Function.Surjective
      (mfderiv 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates) d.beltNormal
        (d.surgery.beltSphere v)) := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  let w : d.chart.PositiveCoordinates := d.radius • (v : d.chart.PositiveCoordinates)
  let γ : d.chart.NegativeCoordinates → M := fun u => d.chart.splitChart.symm (u, w)
  let n : M → d.chart.NegativeCoordinates := fun x => (d.chart.splitChart x).1
  have hmodel : (0, w) ∈ d.chart.splitChart.target := d.belt_model_mem_target v
  have hγ : ContMDiffAt 𝓘(ℝ, d.chart.NegativeCoordinates) 𝓘(ℝ, E) ∞ γ 0 :=
    (d.chart.splitChart.contMDiffOn_invFun.contMDiffAt
          (d.chart.splitChart.open_target.mem_nhds hmodel)).comp
      0 (contDiffAt_id.prodMk contDiffAt_const).contMDiffAt
  have hpoint : γ 0 = (d.surgery.beltSphere v : M) := by rw [d.belt_eq, d.chart.beltCoreMap_coe]
  have hn :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, d.chart.NegativeCoordinates) ∞ n (d.surgery.beltSphere v : M) :=
    contDiff_fst.contMDiff.contMDiffAt.comp _
      (d.chart.splitChart.contMDiffOn_toFun.contMDiffAt
        (d.chart.splitChart.open_source.mem_nhds (d.belt_mem_normalDomain v)))
  have hnear : ∀ᶠ u : d.chart.NegativeCoordinates in 𝓝 0, (u, w) ∈ d.chart.splitChart.target :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (d.chart.splitChart.open_target.mem_nhds hmodel)
  have hheight :
    f ∘ γ =ᶠ[𝓝 (0 : d.chart.NegativeCoordinates)] (fun u => f p - ‖u‖ ^ 2 + ‖w‖ ^ 2) := by
    filter_upwards [hnear] with u hu
    exact d.chart.splitChart_inverse_equation hu
  have hheight₀ : mfderiv 𝓘(ℝ, d.chart.NegativeCoordinates) 𝓘(ℝ, ℝ) (f ∘ γ) 0 = 0 := by
    rw [hheight.mfderiv_eq, mfderiv_eq_fderiv, fderiv_add_const, fderiv_const_sub,
      fderiv_norm_sq_apply]
    simp
    rfl
  have hnormal : n ∘ γ =ᶠ[𝓝 (0 : d.chart.NegativeCoordinates)] id := by
    filter_upwards [hnear] with u hu
    exact congrArg Prod.fst (d.chart.splitChart.right_inv' hu)
  have hnormal₀ :
    mfderiv 𝓘(ℝ, d.chart.NegativeCoordinates) 𝓘(ℝ, d.chart.NegativeCoordinates) (n ∘ γ) 0 =
      ContinuousLinearMap.id ℝ d.chart.NegativeCoordinates := by
    rw [hnormal.mfderiv_eq, mfderiv_id]
    rfl
  let R : d.chart.NegativeCoordinates →L[ℝ] E :=
    mfderiv 𝓘(ℝ, d.chart.NegativeCoordinates) 𝓘(ℝ, E) γ 0
  let L : E →L[ℝ] ℝ := mvfderiv 𝓘(ℝ, E) f (d.surgery.beltSphere v : M)
  let B : E →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, d.chart.NegativeCoordinates) n (d.surgery.beltSphere v : M)
  have hLpoint : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (γ 0) : E →L[ℝ] ℝ) = L := by
    rw [hpoint]
    rfl
  have hLR₀ : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (γ 0) : E →L[ℝ] ℝ).comp R = 0 :=
    (mfderiv_comp 0 (hf.mdifferentiableAt (by simp)) (hγ.mdifferentiableAt (by simp))).symm.trans
      hheight₀
  have hLR : L.comp R = 0 := (congrArg (fun T : E →L[ℝ] ℝ => T.comp R) hLpoint).symm.trans hLR₀
  have hnγ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, d.chart.NegativeCoordinates) n (γ 0) := by
    rw [hpoint]
    exact hn.mdifferentiableAt (by simp)
  have hBpoint :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, d.chart.NegativeCoordinates) n (γ 0) :
        E →L[ℝ] d.chart.NegativeCoordinates) =
      B := by rw [hpoint]
  have hBR₀ :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, d.chart.NegativeCoordinates) n (γ 0) :
            E →L[ℝ] d.chart.NegativeCoordinates).comp
        R =
      ContinuousLinearMap.id ℝ d.chart.NegativeCoordinates :=
    (mfderiv_comp 0 hnγ (hγ.mdifferentiableAt (by simp))).symm.trans hnormal₀
  have hBR : B.comp R = ContinuousLinearMap.id ℝ d.chart.NegativeCoordinates :=
    (congrArg (fun T : E →L[ℝ] d.chart.NegativeCoordinates => T.comp R) hBpoint).symm.trans hBR₀
  exact
    Smale.RegularLevel.surjective_normal_derivative_of_tangent_lift hf d.upper_regular
      (d.surgery.beltSphere v) (hn.mdifferentiableAt (by simp)) R hLR hBR

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.MorseSurgeryData.range_belt_derivative_eq_normal_kernel {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (v : Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    (mfderiv (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) d.surgery.beltSphere v).range =
      (mfderiv 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates) d.beltNormal
          (d.surgery.beltSphere v)).ker := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] Smale.RegularLevel.Model E :=
    mfderiv (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) d.surgery.beltSphere v
  let Q : Smale.RegularLevel.Model E →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates) d.beltNormal
      (d.surgery.beltSphere v)
  change A.range = Q.ker
  have hQA : Q.comp A = 0 := d.beltNormal_derivative_comp_belt hf n v
  have hsub : A.range ≤ Q.ker := by
    rintro _ ⟨u, rfl⟩
    change Q (A u) = 0
    exact congrArg (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ] d.chart.NegativeCoordinates => T u) hQA
  have hAi : Function.Injective A := d.belt_derivative_injective hf n v
  have hArank : Module.finrank ℝ A.range = n := by
    rw [LinearMap.finrank_range_of_inj hAi]
    exact finrank_euclideanSpace_fin
  have hQ : Function.Surjective Q := d.surjective_beltNormal_derivative hf v
  have hQrank : Module.finrank ℝ Q.range = Module.finrank ℝ d.chart.NegativeCoordinates := by
    rw [LinearMap.range_eq_top.mpr hQ, finrank_top]
  have hdimQ := Q.toLinearMap.finrank_range_add_finrank_ker
  have hsplit := d.chart.finrank_negative_add_positive
  have hpos : Module.finrank ℝ d.chart.PositiveCoordinates = n + 1 := Fact.out
  have hmodel : Module.finrank ℝ (Smale.RegularLevel.Model E) = Module.finrank ℝ E - 1 :=
    finrank_euclideanSpace_fin
  apply Submodule.eq_of_le_of_finrank_eq hsub
  rw [hArank]
  omega

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.MorseSurgeryData.bijective_beltNormal_comp_of_transverse {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (n m : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g) (x : Smale.Hemisphere.Sphere m)
      (v : Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates),
      d.surgery.beltSphere v = g x →
        Function.Surjective
            ((mfderiv (𝓡 m) 𝓘(ℝ, Smale.RegularLevel.Model E) g x :
                  EuclideanSpace ℝ (Fin m) →L[ℝ] Smale.RegularLevel.Model E).coprod
              (mfderiv (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) d.surgery.beltSphere v :
                EuclideanSpace ℝ (Fin n) →L[ℝ] Smale.RegularLevel.Model E)) →
          Function.Bijective
            (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x) := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  intro hg x v hxy ht
  let Q : Smale.RegularLevel.Model E →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates) d.beltNormal
      (d.surgery.beltSphere v)
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] Smale.RegularLevel.Model E :=
    mfderiv (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) d.surgery.beltSphere v
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] Smale.RegularLevel.Model E :=
    mfderiv (𝓡 m) 𝓘(ℝ, Smale.RegularLevel.Model E) g x
  have hQ : Function.Surjective Q := d.surjective_beltNormal_derivative hf v
  have hQB : Q.comp B = 0 := d.beltNormal_derivative_comp_belt hf n v
  have hBA : Function.Surjective (B.coprod A) :=
    Smale.TransverseCoordinates.surjective_coprod_swap A B ht
  have hi : Function.Bijective (Q.comp A) :=
    Smale.TransverseCoordinates.bijective_normal_comp Q B A hQ hBA hQB
      (by simpa only [finrank_euclideanSpace_fin] using hdim.symm)
  have hx : g x ∈ d.beltNormalDomain := hxy ▸ d.belt_mem_normalDomain v
  have hnormal :=
    (d.contMDiffOn_beltNormal hf).contMDiffAt (d.isOpen_beltNormalDomain.mem_nhds hx)
  have heq : mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x = Q.comp A := by
    rw [mfderiv_comp x (hnormal.mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp)), ←
      hxy]
    rfl
  rw [heq]
  exact hi

private def Smale.TransverseCoordinates.sumMap {D Z A : Type*} [NormedAddCommGroup D]
    [NormedAddCommGroup A] (f : D → A) (g : Z → A) (q : D × Z) : A :=
  f q.1 + g q.2 - f 0

private theorem Smale.TransverseCoordinates.sumMap_left {D Z A : Type*} [NormedAddCommGroup D]
    [NormedAddCommGroup Z] [NormedAddCommGroup A] (f : D → A) (g : Z → A) (hzero : g 0 = f 0)
    (x : D) : sumMap f g (x, 0) = f x := by simp [sumMap, hzero]

private theorem Smale.TransverseCoordinates.sumMap_right {D Z A : Type*} [NormedAddCommGroup D]
    [NormedAddCommGroup A] (f : D → A) (g : Z → A) (z : Z) : sumMap f g (0, z) = g z := by
  simp [sumMap, add_sub_cancel_left]

private theorem Smale.TransverseCoordinates.contDiffOn_sumMap {D Z A : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup A]
    [NormedSpace ℝ A] {f : D → A} {g : Z → A} {U : Set D} {V : Set Z} (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiffOn ℝ ∞ g V) : ContDiffOn ℝ ∞ (sumMap f g) (U ×ˢ V) :=
  ((hf.comp contDiff_fst.contDiffOn (fun _ hx => hx.1)).add
        (hg.comp contDiff_snd.contDiffOn (fun _ hx => hx.2))).sub
    contDiffOn_const

private theorem
    Smale.TransverseCoordinates.hasFDerivAt_sumMap_zero {D Z A : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup A]
    [NormedSpace ℝ A] {f : D → A} {g : Z → A} (hf : DifferentiableAt ℝ f 0)
    (hg : DifferentiableAt ℝ g 0) :
    HasFDerivAt (sumMap f g) ((fderiv ℝ f 0).coprod (fderiv ℝ g 0)) (0, 0) := by
  have hfst := (ContinuousLinearMap.fst ℝ D Z).hasFDerivAt (x := (0, 0))
  have hsnd := (ContinuousLinearMap.snd ℝ D Z).hasFDerivAt (x := (0, 0))
  have hd :=
    ((hf.hasFDerivAt.comp (0, 0) hfst).add (hg.hasFDerivAt.comp (0, 0) hsnd)).sub
      (hasFDerivAt_const (f 0) (0, 0))
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro q
  simp [ContinuousLinearMap.coprod_apply]

private def Smale.NativeEuclideanEmbedding.SmoothRetraction.sheetCoordinates {E M D Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup D] {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (f : D → M) (g : Z → M) : D × Z → M :=
  r.toFun ∘ Smale.TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g)

private def Smale.NativeEuclideanEmbedding.SmoothRetraction.sheetCoordinateDomain {E M D Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup D] {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (f : D → M) (g : Z → M) (U : Set D) (V : Set Z) : Set (D × Z) :=
  (U ×ˢ V) ∩ Smale.TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g) ⁻¹' r.domain

private theorem
    Smale.NativeEuclideanEmbedding.SmoothRetraction.sheetCoordinates_left {E M D Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup D] [NormedAddCommGroup Z] {e : Smale.NativeEuclideanEmbedding E M}
    (r : e.SmoothRetraction) (f : D → M) (g : Z → M) (hzero : g 0 = f 0) (x : D) :
    r.sheetCoordinates f g (x, 0) = f x := by
  have hsum :=
    Smale.TransverseCoordinates.sumMap_left (e.toFun ∘ f) (e.toFun ∘ g) (congrArg e.toFun hzero) x
  change r.toFun (Smale.TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g) (x, 0)) = f x
  rw [hsum]
  exact r.retract (f x)

private theorem
    Smale.NativeEuclideanEmbedding.SmoothRetraction.sheetCoordinates_right {E M D Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup D] {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    (f : D → M) (g : Z → M) (z : Z) : r.sheetCoordinates f g (0, z) = g z := by
  rw [sheetCoordinates, Function.comp_apply, Smale.TransverseCoordinates.sumMap_right]
  exact r.retract (g z)

private theorem Smale.NativeEuclideanEmbedding.SmoothRetraction.zero_mem_sheetCoordinateDomain
    {E M D Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup D] [NormedAddCommGroup Z]
    {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) (f : D → M) (g : Z → M)
    {U : Set D} {V : Set Z} (hU : (0 : D) ∈ U) (hV : (0 : Z) ∈ V) :
    (0, 0) ∈ r.sheetCoordinateDomain f g U V := by
  refine ⟨⟨hU, hV⟩, ?_⟩
  change Smale.TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g) (0, 0) ∈ r.domain
  rw [Smale.TransverseCoordinates.sumMap_right]
  exact r.contains ⟨g 0, rfl⟩

private theorem Smale.NativeEuclideanEmbedding.SmoothRetraction.isOpen_sheetCoordinateDomain
    {E M D Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    {f : D → M} {g : Z → M} {U : Set D} {V : Set Z} (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U) (hg : ContMDiffOn 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ g V) :
    IsOpen (r.sheetCoordinateDomain f g U V) :=
  (Smale.TransverseCoordinates.contDiffOn_sumMap (e.smooth.comp_contMDiffOn hf).contDiffOn
        (e.smooth.comp_contMDiffOn hg).contDiffOn).continuousOn.isOpen_inter_preimage
    (hU.prod hV) r.open_domain

private theorem Smale.NativeEuclideanEmbedding.SmoothRetraction.contMDiffOn_sheetCoordinates
    {E M D Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    {f : D → M} {g : Z → M} {U : Set D} {V : Set Z} (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ g V) :
    ContMDiffOn 𝓘(ℝ, D × Z) 𝓘(ℝ, E) ∞ (r.sheetCoordinates f g)
      (r.sheetCoordinateDomain f g U V) :=
  r.smooth.comp
    ((Smale.TransverseCoordinates.contDiffOn_sumMap (e.smooth.comp_contMDiffOn hf).contDiffOn
          (e.smooth.comp_contMDiffOn hg).contDiffOn).contMDiffOn.mono
      Set.inter_subset_left)
    (fun _ hx => hx.2)

private theorem Smale.NativeEuclideanEmbedding.SmoothRetraction.mfderiv_sheetCoordinates_zero
    {E M D Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] {e : Smale.NativeEuclideanEmbedding E M} (r : e.SmoothRetraction)
    {f : D → M} {g : Z → M} (hzero : g 0 = f 0) (hf : ContMDiffAt 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f 0)
    (hg : ContMDiffAt 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ g 0) :
    mfderiv 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (r.sheetCoordinates f g) (0, 0) =
      (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0) := by
  have heF := (e.smooth.contMDiffAt.comp 0 hf).contDiffAt
  have heG := (e.smooth.contMDiffAt.comp 0 hg).contDiffAt
  have hsum :=
    Smale.TransverseCoordinates.hasFDerivAt_sumMap_zero (heF.differentiableAt (by simp))
      (heG.differentiableAt (by simp))
  have hbase :
    Smale.TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g) (0, 0) = e.toFun (f 0) := by
    rw [Smale.TransverseCoordinates.sumMap_right]
    exact congrArg e.toFun hzero
  have hr :
    MDifferentiableAt (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun
      (Smale.TransverseCoordinates.sumMap (e.toFun ∘ f) (e.toFun ∘ g) (0, 0)) := by
    rw [hbase]
    exact
      (r.smooth.contMDiffAt (r.open_domain.mem_nhds (r.contains ⟨f 0, rfl⟩))).mdifferentiableAt
        (by simp)
  have hdf :
    fderiv ℝ (e.toFun ∘ f) 0 =
      (mfderiv 𝓘(ℝ, E) (𝓡 e.ambientDimension) e.toFun (f 0)).comp (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0) :=
    by
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp 0 (e.smooth.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
  have hdg :
    fderiv ℝ (e.toFun ∘ g) 0 =
      (mfderiv 𝓘(ℝ, E) (𝓡 e.ambientDimension) e.toFun (f 0)).comp (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0) :=
    by
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp 0 (e.smooth.mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp))]
    rw [hzero]
  rw [sheetCoordinates, mfderiv_comp (0, 0) hr hsum.differentiableAt.mdifferentiableAt,
    mfderiv_eq_fderiv, hsum.fderiv, hbase, hdf, hdg]
  apply ContinuousLinearMap.ext
  intro q
  have hleft :=
    congrArg (fun L => L ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0) q.1)) (r.mfderiv_retract_comp (f 0))
  have hright :=
    congrArg (fun L => L ((mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0) q.2)) (r.mfderiv_retract_comp (f 0))
  let R : EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ] E :=
    mfderiv (𝓡 e.ambientDimension) 𝓘(ℝ, E) r.toFun (e.toFun (f 0))
  let T : E →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
    mfderiv 𝓘(ℝ, E) (𝓡 e.ambientDimension) e.toFun (f 0)
  let F : D →L[ℝ] E := mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0
  let G : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0
  change R (T (F q.1) + T (G q.2)) = F q.1 + G q.2
  change R (T (F q.1)) = F q.1 at hleft
  change R (T (G q.2)) = G q.2 at hright
  rw [map_add, hleft, hright]

private theorem Smale.TransverseCoordinates.isInvertible_coprod_of_surjective {D Z E : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z]
    [FiniteDimensional ℝ E] (F : D →L[ℝ] E) (G : Z →L[ℝ] E)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht : Function.Surjective (F.coprod G)) : (F.coprod G).IsInvertible := by
  have hd : Module.finrank ℝ (D × Z) = Module.finrank ℝ E := by
    simpa only [Module.finrank_prod] using hdim
  have hi : Function.Injective (F.coprod G) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr ht
  let L := (LinearEquiv.ofBijective (F.coprod G).toLinearMap ⟨hi, ht⟩).toContinuousLinearEquiv
  exact ⟨L, rfl⟩

private theorem Smale.exists_simultaneous_sheetChart {E M D Z : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {f : D → M} {g : Z → M} {U : Set D} {V : Set Z} (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : D) ∈ U) (h0V : (0 : Z) ∈ V) (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ g V) (hzero : g 0 = f 0)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht :
      Function.Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0)))
    {O : Set M} (hO : IsOpen O) (h0O : f 0 ∈ O) :
    ∃ a : ℝ,
      0 < a ∧
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞,
          Metric.closedBall (0 : D) a ×ˢ Metric.closedBall (0 : Z) a ⊆ Φ.source ∧
            Φ.source ⊆ U ×ˢ V ∧
              Φ.target ⊆ O ∧
                (∀ x, (x, 0) ∈ Φ.source → Φ (x, 0) = f x) ∧
                  (∀ z, (0, z) ∈ Φ.source → Φ (0, z) = g z) := by
  let : Nonempty M := ⟨f 0⟩
  obtain ⟨e⟩ := nonempty_nativeEuclideanEmbedding (E := E) (M := M)
  obtain ⟨r⟩ := e.nonempty_smoothRetraction
  let W₀ := r.sheetCoordinateDomain f g U V
  have hW₀ : IsOpen W₀ := r.isOpen_sheetCoordinateDomain hU hV hf hg
  have hs : ContMDiffOn 𝓘(ℝ, D × Z) 𝓘(ℝ, E) ∞ (r.sheetCoordinates f g) W₀ :=
    r.contMDiffOn_sheetCoordinates hf hg
  let W := W₀ ∩ r.sheetCoordinates f g ⁻¹' O
  have hW : IsOpen W := hs.continuousOn.isOpen_inter_preimage hW₀ hO
  have h0W : (0, 0) ∈ W := by
    refine ⟨r.zero_mem_sheetCoordinateDomain f g h0U h0V, ?_⟩
    change r.sheetCoordinates f g (0, 0) ∈ O
    rw [r.sheetCoordinates_left f g hzero]
    exact h0O
  have hinv : (mfderiv 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (r.sheetCoordinates f g) (0, 0)).IsInvertible := by
    rw [r.mfderiv_sheetCoordinates_zero hzero (hf.contMDiffAt (hU.mem_nhds h0U))
        (hg.contMDiffAt (hV.mem_nhds h0V))]
    exact
      TransverseCoordinates.isInvertible_coprod_of_surjective (D := D) (Z := Z) (E := E) _ _ hdim
        ht
  obtain ⟨Φ, h0Φ, hΦW, heq⟩ :=
    exists_partialDiffeomorph_into_manifold hW h0W (hs.mono Set.inter_subset_left) hinv
  obtain ⟨a, ha, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Φ.open_source.mem_nhds h0Φ)
  refine ⟨a, ha, Φ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [closedBall_prod_same]
    exact hball
  · intro q hq
    exact (hΦW hq).1.1
  · intro y hy
    have hq := Φ.map_target' hy
    have hmem := (hΦW hq).2
    change r.sheetCoordinates f g (Φ.invFun y) ∈ O at hmem
    rw [heq hq] at hmem
    exact (Φ.right_inv' hy) ▸ hmem
  · intro x hx
    exact (heq hx).symm.trans (r.sheetCoordinates_left f g hzero x)
  · intro z hz
    exact (heq hz).symm.trans (r.sheetCoordinates_right f g z)

private theorem Smale.exists_clean_simultaneous_sheetChart {E M D Z : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {f : D → M} {g : Z → M} {U : Set D} {V : Set Z} (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : D) ∈ U) (h0V : (0 : Z) ∈ V) (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ g V) (hzero : g 0 = f 0)
    (hembf : Topology.IsEmbedding (fun x : U => f x))
    (hembg : Topology.IsEmbedding (fun z : V => g z))
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht :
      Function.Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0)))
    {O : Set M} (hO : IsOpen O) (h0O : f 0 ∈ O) :
    ∃ b : ℝ,
      0 < b ∧
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞,
          Metric.closedBall (0 : D) b ×ˢ Metric.closedBall (0 : Z) b ⊆ Φ.source ∧
            Φ.source ⊆ U ×ˢ V ∧
              Φ.target ⊆ O ∧
                (∀ x, (x, 0) ∈ Φ.source → Φ (x, 0) = f x) ∧
                  (∀ z, (0, z) ∈ Φ.source → Φ (0, z) = g z) ∧
                    (∀ q ∈ Φ.source, (Φ q ∈ f '' U ↔ q.2 = 0) ∧ (Φ q ∈ g '' V ↔ q.1 = 0)) := by
  obtain ⟨a, ha, Φ, hprod, hsource, htarget, hleft, hright⟩ :=
    exists_simultaneous_sheetChart hU hV h0U h0V hf hg hzero hdim ht hO h0O
  have hballU : IsOpen {x : U | (x : D) ∈ Metric.ball 0 a} :=
    Metric.isOpen_ball.preimage continuous_subtype_val
  have hballV : IsOpen {z : V | (z : Z) ∈ Metric.ball 0 a} :=
    Metric.isOpen_ball.preimage continuous_subtype_val
  obtain ⟨A, hA, hpreA⟩ := hembf.isInducing.isOpen_iff.mp hballU
  obtain ⟨B, hB, hpreB⟩ := hembg.isInducing.isOpen_iff.mp hballV
  have h0A : f 0 ∈ A := by
    have hz : (⟨0, h0U⟩ : U) ∈ {x : U | (x : D) ∈ Metric.ball 0 a} := Metric.mem_ball_self ha
    rw [← hpreA] at hz
    exact hz
  have h0B : g 0 ∈ B := by
    have hz : (⟨0, h0V⟩ : V) ∈ {z : V | (z : Z) ∈ Metric.ball 0 a} := Metric.mem_ball_self ha
    rw [← hpreB] at hz
    exact hz
  have hsmallF {x : D} (hx : x ∈ U) (hxA : f x ∈ A) : x ∈ Metric.closedBall 0 a := by
    have hx' : (⟨x, hx⟩ : U) ∈ (fun x : U => f x) ⁻¹' A := hxA
    rw [hpreA] at hx'
    exact Metric.ball_subset_closedBall hx'
  have hsmallG {z : Z} (hz : z ∈ V) (hzB : g z ∈ B) : z ∈ Metric.closedBall 0 a := by
    have hz' : (⟨z, hz⟩ : V) ∈ (fun z : V => g z) ⁻¹' B := hzB
    rw [hpreB] at hz'
    exact Metric.ball_subset_closedBall hz'
  let Ψ := PartialChart.restrictTarget Φ (hA.inter hB)
  have h0Φ : (0, 0) ∈ Φ.source :=
    hprod ⟨Metric.mem_closedBall_self ha.le, Metric.mem_closedBall_self ha.le⟩
  have hcenter : Φ (0, 0) = f 0 := hleft 0 h0Φ
  have h0Ψ : (0, 0) ∈ Ψ.source := by
    refine ⟨h0Φ, ?_⟩
    change Φ (0, 0) ∈ A ∩ B
    rw [hcenter]
    exact ⟨h0A, hzero ▸ h0B⟩
  obtain ⟨b, hb, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Ψ.open_source.mem_nhds h0Ψ)
  refine
    ⟨b, hb, Ψ, ?_, fun _ hq => hsource hq.1, fun _ hy => htarget hy.1, (fun x hx => hleft x hx.1),
      (fun z hz => hright z hz.1), ?_⟩
  · rw [closedBall_prod_same]
    exact hball
  · rintro ⟨x, z⟩ hq
    have hAq : Φ (x, z) ∈ A := hq.2.1
    have hBq : Φ (x, z) ∈ B := hq.2.2
    constructor
    · constructor
      · rintro ⟨u, hu, heq⟩
        have huA : f u ∈ A := heq ▸ hAq
        have haxis : (u, 0) ∈ Φ.source := hprod ⟨hsmallF hu huA, Metric.mem_closedBall_self ha.le⟩
        have hpair : (x, z) = (u, 0) :=
          Φ.toPartialEquiv.injOn hq.1 haxis (heq.symm.trans (hleft u haxis).symm)
        exact congrArg Prod.snd hpair
      · intro hz
        change z = 0 at hz
        subst z
        exact ⟨x, (hsource hq.1).1, (hleft x hq.1).symm⟩
    · constructor
      · rintro ⟨v, hv, heq⟩
        have hvB : g v ∈ B := heq ▸ hBq
        have haxis : (0, v) ∈ Φ.source := hprod ⟨Metric.mem_closedBall_self ha.le, hsmallG hv hvB⟩
        have hpair : (x, z) = (0, v) :=
          Φ.toPartialEquiv.injOn hq.1 haxis (heq.symm.trans (hright v haxis).symm)
        exact congrArg Prod.fst hpair
      · intro hx
        change x = 0 at hx
        subst x
        exact ⟨z, (hsource hq.1).2, (hright z hq.1).symm⟩

private theorem Smale.exists_clean_crossingChart_of_parametrizations {E M D Z N P A B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace N] [ChartedSpace D N]
    [TopologicalSpace P] [ChartedSpace Z P] {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : Topology.IsEmbedding F) (hembG : Topology.IsEmbedding G)
    (c : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, D) A N ∞) (d : PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, Z) B P ∞)
    (hc0 : (0 : A) ∈ c.source) (hd0 : (0 : B) ∈ d.source) (hxy : G (d 0) = F (c 0))
    (hdim : Module.finrank ℝ A + Module.finrank ℝ B = Module.finrank ℝ E)
    (ht :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c 0)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0))))
    {O : Set M} (hO : IsOpen O) (hxO : F (c 0) ∈ O) :
    ∃ a : ℝ,
      0 < a ∧
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, E) (A × B) M ∞,
          Metric.closedBall (0 : A) a ×ˢ Metric.closedBall (0 : B) a ⊆ Φ.source ∧
            Φ.source ⊆ c.source ×ˢ d.source ∧
              Φ.target ⊆ O ∧
                Φ (0, 0) = F (c 0) ∧
                  (∀ u, (u, 0) ∈ Φ.source → Φ (u, 0) = F (c u)) ∧
                    (∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (d v)) ∧
                      (∀ q ∈ Φ.source,
                        (Φ q ∈ Set.range F ↔ q.2 = 0) ∧ (Φ q ∈ Set.range G ↔ q.1 = 0)) := by
  let f := F ∘ c
  let g := G ∘ d
  have hf : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ f c.source := hF.comp_contMDiffOn c.contMDiffOn_toFun
  have hg : ContMDiffOn 𝓘(ℝ, B) 𝓘(ℝ, E) ∞ g d.source := hG.comp_contMDiffOn d.contMDiffOn_toFun
  have hembf : Topology.IsEmbedding (fun u : c.source => f u) :=
    hembF.comp c.toOpenPartialHomeomorph.isOpenEmbedding_restrict.isEmbedding
  have hembg : Topology.IsEmbedding (fun v : d.source => g v) :=
    hembG.comp d.toOpenPartialHomeomorph.isOpenEmbedding_restrict.isEmbedding
  have hdf :
    mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) f 0 =
      (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c 0)).comp (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, D) c 0) :=
    mfderiv_comp 0 (hF.mdifferentiableAt (by simp)) (c.mdifferentiableAt (by simp) hc0)
  have hdg :
    mfderiv 𝓘(ℝ, B) 𝓘(ℝ, E) g 0 =
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0)).comp (mfderiv 𝓘(ℝ, B) 𝓘(ℝ, Z) d 0) :=
    mfderiv_comp 0 (hG.mdifferentiableAt (by simp)) (d.mdifferentiableAt (by simp) hd0)
  have ht' :
    Function.Surjective ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) f 0).coprod (mfderiv 𝓘(ℝ, B) 𝓘(ℝ, E) g 0)) := by
    rw [hdf, hdg]
    intro w
    obtain ⟨⟨u, v⟩, huv⟩ := ht w
    obtain ⟨a, ha⟩ := (PartialChart.bijective_mfderiv c hc0).2 u
    obtain ⟨b, hb⟩ := (PartialChart.bijective_mfderiv d hd0).2 v
    refine ⟨(a, b), ?_⟩
    let DF : D →L[ℝ] E := mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c 0)
    let DG : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0)
    let C : A →L[ℝ] D := mfderiv 𝓘(ℝ, A) 𝓘(ℝ, D) c 0
    let Q : B →L[ℝ] Z := mfderiv 𝓘(ℝ, B) 𝓘(ℝ, Z) d 0
    change DF (C a) + DG (Q b) = w
    change C a = u at ha
    change Q b = v at hb
    rw [ha, hb]
    exact huv
  obtain ⟨U, hU, hpreU⟩ := hembF.isInducing.isOpen_iff.mp c.open_target
  obtain ⟨V, hV, hpreV⟩ := hembG.isInducing.isOpen_iff.mp d.open_target
  have hxU : F (c 0) ∈ U := by
    change c 0 ∈ F ⁻¹' U
    rw [hpreU]
    exact c.map_source' hc0
  have hyV : G (d 0) ∈ V := by
    change d 0 ∈ G ⁻¹' V
    rw [hpreV]
    exact d.map_source' hd0
  have hxV : F (c 0) ∈ V := hxy ▸ hyV
  obtain ⟨a, ha, Φ, hprod, hsource, htarget, hleft, hright, himages⟩ :=
    exists_clean_simultaneous_sheetChart c.open_source d.open_source hc0 hd0 hf hg hxy hembf hembg
      hdim ht' (hO.inter (hU.inter hV)) ⟨hxO, hxU, hxV⟩
  refine
    ⟨a, ha, Φ, hprod, hsource, fun _ hq => (htarget hq).1,
      hleft 0 (hprod ⟨Metric.mem_closedBall_self ha.le, Metric.mem_closedBall_self ha.le⟩), hleft,
      hright, ?_⟩
  intro q hq
  have hqUV := (htarget (Φ.map_source' hq)).2
  have hrangeF : Φ q ∈ Set.range F ↔ Φ q ∈ f '' c.source := by
    constructor
    · rintro ⟨n, hn⟩
      have hnU : F n ∈ U := hn ▸ hqUV.1
      have hnT : n ∈ c.target := by
        change n ∈ F ⁻¹' U at hnU
        rwa [hpreU] at hnU
      refine ⟨c.invFun n, c.map_target' hnT, ?_⟩
      exact (congrArg F (c.right_inv' hnT)).trans hn
    · rintro ⟨u, _, hu⟩
      exact ⟨c u, hu⟩
  have hrangeG : Φ q ∈ Set.range G ↔ Φ q ∈ g '' d.source := by
    constructor
    · rintro ⟨p, hp⟩
      have hpV : G p ∈ V := hp ▸ hqUV.2
      have hpT : p ∈ d.target := by
        change p ∈ G ⁻¹' V at hpV
        rwa [hpreV] at hpV
      refine ⟨d.invFun p, d.map_target' hpT, ?_⟩
      exact (congrArg G (d.right_inv' hpT)).trans hp
    · rintro ⟨v, _, hv⟩
      exact ⟨d v, hv⟩
  exact ⟨hrangeF.trans (himages q hq).1, hrangeG.trans (himages q hq).2⟩

private theorem Smale.exists_clean_crossingChart {E M D Z N P : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N] [TopologicalSpace P]
    [ChartedSpace Z P] [IsManifold 𝓘(ℝ, Z) ∞ P] {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : Topology.IsEmbedding F) (hembG : Topology.IsEmbedding G) (x : N) (y : P)
    (hxy : G y = F x) (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht :
      Function.Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y)))
    {O : Set M} (hO : IsOpen O) (hxO : F x ∈ O) :
    ∃ a : ℝ,
      0 < a ∧
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞,
          Metric.closedBall (0 : D) a ×ˢ Metric.closedBall (0 : Z) a ⊆ Φ.source ∧
            Φ.source ⊆
                (NativeParametrization.centered (D := D) x).source ×ˢ
                  (NativeParametrization.centered (D := Z) y).source ∧
              Φ.target ⊆ O ∧
                Φ (0, 0) = F x ∧
                  (∀ u,
                      (u, 0) ∈ Φ.source →
                        Φ (u, 0) = F (NativeParametrization.centered (D := D) x u)) ∧
                    (∀ v,
                        (0, v) ∈ Φ.source →
                          Φ (0, v) = G (NativeParametrization.centered (D := Z) y v)) ∧
                      (∀ q ∈ Φ.source,
                        (Φ q ∈ Set.range F ↔ q.2 = 0) ∧ (Φ q ∈ Set.range G ↔ q.1 = 0)) := by
  let c := NativeParametrization.centered (D := D) x
  let d := NativeParametrization.centered (D := Z) y
  have hc0 : (0 : D) ∈ c.source := NativeParametrization.zero_mem_centered_source x
  have hd0 : (0 : Z) ∈ d.source := NativeParametrization.zero_mem_centered_source y
  have hcx : c 0 = x := NativeParametrization.centered_zero x
  have hdy : d 0 = y := NativeParametrization.centered_zero y
  have hxy' : G (d 0) = F (c 0) := by rw [hcx, hdy]; exact hxy
  have ht' :
    Function.Surjective
      ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c 0)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0))) := by
    rw [hcx, hdy]
    exact ht
  have hxO' : F (c 0) ∈ O := by rw [hcx]; exact hxO
  obtain ⟨a, ha, Φ, hprod, hsource, htarget, hcenter, hleft, hright, himages⟩ :=
    exists_clean_crossingChart_of_parametrizations hF hG hembF hembG c d hc0 hd0 hxy' hdim ht' hO
      hxO'
  exact
    ⟨a, ha, Φ, hprod, hsource, htarget, hcenter.trans (congrArg F hcx), hleft, hright, himages⟩

private theorem
    Smale.exists_isolating_crossing_neighborhood {E M D Z N P : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N] [TopologicalSpace P]
    [ChartedSpace Z P] [IsManifold 𝓘(ℝ, Z) ∞ P] {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : Topology.IsEmbedding F) (hembG : Topology.IsEmbedding G) (x : N) (y : P)
    (hxy : G y = F x) (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht :
      Function.Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y))) :
    ∃ O : Set M, IsOpen O ∧ F x ∈ O ∧ O ∩ (Set.range F ∩ Set.range G) = {F x} := by
  obtain ⟨a, ha, Φ, hprod, -, -, hcenter, -, -, himages⟩ :=
    exists_clean_crossingChart hF hG hembF hembG x y hxy hdim ht isOpen_univ (Set.mem_univ _)
  have h0Φ : (0, 0) ∈ Φ.source :=
    hprod ⟨Metric.mem_closedBall_self ha.le, Metric.mem_closedBall_self ha.le⟩
  have hFx : F x ∈ Φ.target := hcenter ▸ Φ.map_source' h0Φ
  refine ⟨Φ.target, Φ.open_target, hFx, ?_⟩
  ext w
  constructor
  · rintro ⟨hw, hwF, hwG⟩
    let q := Φ.invFun w
    have hq : q ∈ Φ.source := Φ.map_target' hw
    have heq : Φ q = w := Φ.right_inv' hw
    have hqF : Φ q ∈ Set.range F := heq.symm ▸ hwF
    have hqG : Φ q ∈ Set.range G := heq.symm ▸ hwG
    have hq0 : q = (0, 0) := Prod.ext ((himages q hq).2.mp hqG) ((himages q hq).1.mp hqF)
    exact Set.mem_singleton_iff.mpr (heq.symm.trans ((congrArg Φ hq0).trans hcenter))
  · intro hw
    rcases Set.mem_singleton_iff.mp hw with rfl
    exact ⟨hFx, ⟨x, rfl⟩, ⟨y, hxy⟩⟩

private theorem
    Smale.isDiscrete_transverse_intersections {E M D Z N P : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N] [TopologicalSpace P]
    [ChartedSpace Z P] [IsManifold 𝓘(ℝ, Z) ∞ P] {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : Topology.IsEmbedding F) (hembG : Topology.IsEmbedding G)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht :
      ∀ x y,
        G y = F x →
          Function.Surjective
            ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y))) :
    IsDiscrete (Set.range F ∩ Set.range G) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  rintro z ⟨⟨x, rfl⟩, ⟨y, hxy⟩⟩
  obtain ⟨O, hO, -, heq⟩ :=
    exists_isolating_crossing_neighborhood hF hG hembF hembG x y hxy hdim (ht x y hxy)
  exact ⟨O, hO, heq⟩

private theorem Smale.finite_transverse_intersections {E M D Z N P : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N] [TopologicalSpace P]
    [ChartedSpace Z P] [IsManifold 𝓘(ℝ, Z) ∞ P] [CompactSpace N] [CompactSpace P] {F : N → M}
    {G : P → M} (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hinjF : Function.Injective F) (hinjG : Function.Injective G)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht :
      ∀ x y,
        G y = F x →
          Function.Surjective
            ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y))) :
    (Set.range F ∩ Set.range G).Finite := by
  have hembF := (hF.continuous.isClosedEmbedding hinjF).isEmbedding
  have hembG := (hG.continuous.isClosedEmbedding hinjG).isEmbedding
  exact
    ((isCompact_range hF.continuous).inter_right (isCompact_range hG.continuous).isClosed).finite
      (isDiscrete_transverse_intersections hF hG hembF hembG hdim ht)

private def Smale.SphereBoundary.definingFunction {E : Type*} [NormedAddCommGroup E] (x : E) : ℝ :=
  ‖x‖ ^ 2 - 1

private theorem Smale.SphereBoundary.contDiff_definingFunction {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] : ContDiff ℝ ∞ (definingFunction (E := E)) :=
  (contDiff_id.norm_sq (𝕜 := ℝ)).sub contDiff_const

private theorem Smale.SphereBoundary.definingFunction_eq_zero_iff {E : Type*} [NormedAddCommGroup E]
    (x : E) : definingFunction x = 0 ↔ x ∈ Metric.sphere (0 : E) 1 := by
  simp only [definingFunction, Metric.mem_sphere, dist_zero_right]
  constructor
  · intro h
    nlinarith [norm_nonneg x]
  · intro h
    rw [h]
    norm_num

private theorem Smale.SphereBoundary.fderiv_definingFunction {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : E) : fderiv ℝ (definingFunction (E := E)) x = 2 • innerSL ℝ x :=
  ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.sub_const 1).fderiv

private theorem Smale.SphereBoundary.fderiv_definingFunction_eq_zero_iff {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x v : E) :
    fderiv ℝ (definingFunction (E := E)) x v = 0 ↔ Inner.inner ℝ x v = 0 := by
  rw [fderiv_definingFunction]
  rw [two_smul, add_apply]
  change Inner.inner ℝ x v + Inner.inner ℝ x v = 0 ↔ Inner.inner ℝ x v = 0
  constructor
  · intro h
    linarith
  · intro h
    rw [h, add_zero]

private theorem Smale.SphereBoundary.common_kernel_of_immersive_sphere_extension {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [TopologicalSpace N] [ChartedSpace H N] {f : E → N}
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {γ : Metric.sphere (0 : E) 1 → N}
    (hext : ∀ x : Metric.sphere (0 : E) 1, f x.1 = γ x)
    (hγ : ∀ x, Function.Injective (mfderiv (𝓡 n) J γ x)) :
    ∀ y,
      definingFunction y = 0 →
        ∀ v : E,
          mfderiv 𝓘(ℝ, E) J f y v = 0 → fderiv ℝ (definingFunction (E := E)) y v = 0 → v = 0 := by
  intro y hy v hfv hρv
  let x : Metric.sphere (0 : E) 1 := ⟨y, (definingFunction_eq_zero_iff y).mp hy⟩
  have hinner : Inner.inner ℝ y v = 0 := (fderiv_definingFunction_eq_zero_iff y v).mp hρv
  have hrange : v ∈ (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : E) 1 → E) x).range := by
    rw [range_mvfderiv_subtypeVal]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hinner
  obtain ⟨w, hw⟩ := hrange
  change (mfderiv (𝓡 n) 𝓘(ℝ, E) (Subtype.val : Metric.sphere (0 : E) 1 → E) x) w = v at hw
  have hextfun : (f ∘ (Subtype.val : Metric.sphere (0 : E) 1 → E)) = γ := funext hext
  have hchain :
    mfderiv (𝓡 n) J γ x =
      (mfderiv 𝓘(ℝ, E) J f y).comp
        (mfderiv (𝓡 n) 𝓘(ℝ, E) (Subtype.val : Metric.sphere (0 : E) 1 → E) x) := by
    rw [← hextfun,
      mfderiv_comp x (hf.mdifferentiableAt (by simp))
        ((contMDiff_coe_sphere (m := (∞ : ℕ∞ω))).mdifferentiableAt (by simp))]
  have hγzero : mfderiv (𝓡 n) J γ x w = 0 := by
    rw [hchain]
    change
      (mfderiv 𝓘(ℝ, E) J f y)
          ((mfderiv (𝓡 n) 𝓘(ℝ, E) (Subtype.val : Metric.sphere (0 : E) 1 → E) x) w) =
        0
    rw [hw]
    exact hfv
  have hwzero : w = 0 := (hγ x) (by simpa only [map_zero] using hγzero)
  rw [hwzero, map_zero] at hw
  exact hw.symm

private def Smale.SphereNormalCoordinates.inclusionDerivative {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    (x : Metric.sphere (0 : V) 1) : EuclideanSpace ℝ (Fin n) →L[ℝ] V :=
  mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : V) 1 → V) x

private theorem Smale.SphereNormalCoordinates.inner_inclusionDerivative_zero {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]
    (x : Metric.sphere (0 : V) 1) (u : EuclideanSpace ℝ (Fin n)) :
    Inner.inner ℝ (x : V) (inclusionDerivative x u) = 0 := by
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
  rw [← range_mvfderiv_subtypeVal (n := n) x]
  exact ⟨u, rfl⟩

private theorem Smale.SphereNormalCoordinates.inner_self_eq_one {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (x : Metric.sphere (0 : V) 1) : Inner.inner ℝ (x : V) x = 1 := by
  have hx : ‖(x : V)‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  rw [real_inner_self_eq_norm_sq, hx, one_pow]

private def Smale.SphereNormalCoordinates.normalFrame {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) : (ℝ × N) →L[ℝ] V :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (x : V)).coprod ((inclusionDerivative x).comp A.inverse)

private theorem Smale.SphereNormalCoordinates.normalFrame_apply {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (z : ℝ × N) :
    normalFrame x A z = z.1 • (x : V) + inclusionDerivative x (A.inverse z.2) :=
  rfl

private theorem Smale.SphereNormalCoordinates.inner_normalFrame {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (z : ℝ × N) :
    Inner.inner ℝ (x : V) (normalFrame x A z) = z.1 := by
  rw [normalFrame_apply, inner_add_right, inner_smul_right, inner_self_eq_one,
    inner_inclusionDerivative_zero, mul_one, add_zero]

private theorem
    Smale.SphereNormalCoordinates.bijective_normalFrame {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible) :
    Function.Bijective (normalFrame x A) := by
  constructor
  · intro z w hzw
    have hfst : z.1 = w.1 := by
      simpa only [inner_normalFrame] using congrArg (fun v : V => Inner.inner ℝ (x : V) v) hzw
    have ht : inclusionDerivative x (A.inverse z.2) = inclusionDerivative x (A.inverse w.2) := by
      rw [normalFrame_apply, normalFrame_apply, hfst] at hzw
      exact add_left_cancel hzw
    have hJ : Function.Injective (inclusionDerivative (n := n) x) :=
      injective_mvfderiv_subtypeVal_sphere x
    exact Prod.ext hfst (hA.inverse.injective (hJ ht))
  · intro v
    have ht : v - Inner.inner ℝ (x : V) v • (x : V) ∈ (inclusionDerivative (n := n) x).range := by
      change
        v - Inner.inner ℝ (x : V) v • (x : V) ∈
          (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : V) 1 → V) x).range
      rw [range_mvfderiv_subtypeVal]
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      rw [inner_sub_right, inner_smul_right, inner_self_eq_one, mul_one, sub_self]
    obtain ⟨u, hu⟩ := ht
    change inclusionDerivative x u = v - Inner.inner ℝ (x : V) v • (x : V) at hu
    refine ⟨(Inner.inner ℝ (x : V) v, A u), ?_⟩
    rw [normalFrame_apply, hA.inverse_apply_self, hu]
    abel

private def Smale.SphereNormalCoordinates.normalJacobian {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] (j : (ℝ × N) ≃L[ℝ] V) (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) : ℝ :=
  ((normalFrame x A).comp j.symm.toContinuousLinearMap).det

private theorem
    Smale.SphereNormalCoordinates.normalJacobian_ne_zero {V N : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N] {n : ℕ}
    [Fact (Module.finrank ℝ V = n + 1)] [FiniteDimensional ℝ V] (j : (ℝ × N) ≃L[ℝ] V)
    (x : Metric.sphere (0 : V) 1) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible) :
    normalJacobian j x A ≠ 0 := by
  apply (Smale.RegularValues.bijective_iff_det_ne_zero _).mp
  exact (bijective_normalFrame x A hA).comp j.symm.bijective

private theorem Smale.SphereNormalCoordinates.normalJacobian_change_normal_model {V N : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)] {N' : Type*} [NormedAddCommGroup N']
    [NormedSpace ℝ N'] (r : (ℝ × N) ≃L[ℝ] V) (j : N' ≃L[ℝ] N) (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible) :
    normalJacobian ((ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) j).trans r)
        x (j.symm.toContinuousLinearMap.comp A) =
      normalJacobian r x A := by
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] N' := j.symm.toContinuousLinearMap.comp A
  have hj : j.symm.toContinuousLinearMap.IsInvertible := ⟨j.symm, rfl⟩
  have hB : B.IsInvertible := hj.comp hA
  have hinv (z : N) : B.inverse (j.symm z) = A.inverse z := by
    apply hB.injective
    rw [hB.self_apply_inverse]
    change j.symm z = j.symm (A (A.inverse z))
    rw [hA.self_apply_inverse]
  unfold normalJacobian
  apply congrArg ContinuousLinearMap.det
  apply ContinuousLinearMap.ext
  intro v
  change
    (r.symm v).1 • (x : V) + inclusionDerivative x (B.inverse (j.symm (r.symm v).2)) =
      (r.symm v).1 • (x : V) + inclusionDerivative x (A.inverse (r.symm v).2)
  rw [hinv]

private def
    Smale.ManifoldMorse.MorseSurgeryData.beltNormalReference {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m) :
    (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient (m + 1) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod, hdim, Nat.add_comm])

private def Smale.ManifoldMorse.MorseSurgeryData.beltIntersectionJacobian {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient (m + 1))
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel) (x : Smale.Hemisphere.Sphere m) : ℝ :=
  letI : Fact (Module.finrank ℝ (Smale.Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  Smale.SphereNormalCoordinates.normalJacobian j x
    (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x)

private def
    Smale.ManifoldMorse.MorseSurgeryData.beltIntersectionSign {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient (m + 1))
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel) (x : Smale.Hemisphere.Sphere m) : SignType :=
  SignType.sign (d.beltIntersectionJacobian m j g x)

private def Smale.ManifoldMorse.MorseSurgeryData.beltIntersectionPoints {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel) : Set (Smale.Hemisphere.Sphere m) :=
  g ⁻¹' Set.range d.surgery.beltSphere

private theorem
    Smale.ManifoldMorse.MorseSurgeryData.beltIntersectionSigns_opposite_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient (m + 1))
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel) (x y : Smale.Hemisphere.Sphere m) :
    d.beltIntersectionSign m j g x * d.beltIntersectionSign m j g y = -1 ↔
      d.beltIntersectionJacobian m j g x * d.beltIntersectionJacobian m j g y < 0 := by
  unfold beltIntersectionSign
  rw [← sign_mul, sign_eq_neg_one_iff]

private def Smale.ManifoldMorse.MorseSurgeryData.beltIntersectionCount {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient (m + 1))
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel)
    (hfin : (d.beltIntersectionPoints m g).Finite) : ℤ :=
  ∑ x ∈ hfin.toFinset, (d.beltIntersectionSign m j g x : ℤ)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.beltIntersectionJacobian_ne_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (n m : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient (m + 1))
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (x : Smale.Hemisphere.Sphere m),
      x ∈ d.beltIntersectionPoints m g → d.beltIntersectionJacobian m j g x ≠ 0 := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  let _ : Fact (Module.finrank ℝ (Smale.Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  intro hg ht x hx
  obtain ⟨v, hv⟩ := hx
  have hA := d.bijective_beltNormal_comp_of_transverse hf n m hdim g hg x v hv (ht x v hv)
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x
  have hAi : A.IsInvertible :=
    ⟨(LinearEquiv.ofBijective A.toLinearMap hA).toContinuousLinearEquiv, rfl⟩
  exact Smale.SphereNormalCoordinates.normalJacobian_ne_zero j x A hAi

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.beltIntersectionSign_unit {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (n m : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient (m + 1))
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (x : Smale.Hemisphere.Sphere m),
      x ∈ d.beltIntersectionPoints m g →
        d.beltIntersectionSign m j g x = 1 ∨ d.beltIntersectionSign m j g x = -1 := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  intro hg ht x hx
  have hn : d.beltIntersectionSign m j g x ≠ 0 :=
    sign_ne_zero.mpr (d.beltIntersectionJacobian_ne_zero hf n m hdim j g hg ht x hx)
  rcases SignType.trichotomy (d.beltIntersectionSign m j g x) with h | h | h
  · exact Or.inr h
  · exact (hn h).elim
  · exact Or.inl h

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.finite_beltIntersectionPoints {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    [T2Space M] [CompactSpace M] (n m : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g) (_hinj : Function.Injective g)
      (_ht :
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            d.surgery.beltSphere x y),
      (d.beltIntersectionPoints m g).Finite := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  let _ := Smale.RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  intro hg hinj ht
  have hdim' :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) + Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) =
      Module.finrank ℝ (Smale.RegularLevel.Model E) := by
    simp only [Smale.RegularLevel.Model, finrank_euclideanSpace_fin]
    have hp : Module.finrank ℝ d.chart.PositiveCoordinates = n + 1 := Fact.out
    have hs := d.chart.finrank_negative_add_positive
    omega
  have hfin :=
    Smale.finite_transverse_intersections hg (d.belt_smooth hf n) hinj
      d.belt_isClosedEmbedding.injective hdim' (fun x y hxy => ht x y hxy)
  have hpre : (g ⁻¹' (Set.range g ∩ Set.range d.surgery.beltSphere)).Finite :=
    hfin.preimage hinj.injOn
  exact hpre.subset (fun x hx => ⟨⟨x, rfl⟩, hx⟩)

private def Smale.TransverseCoordinates.normalCoordinate {D B E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) : M → B :=
  Prod.snd ∘ Φ.symm

private theorem Smale.TransverseCoordinates.contMDiffOn_normalCoordinate {D B E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, B) ∞ (normalCoordinate Φ) Φ.target := by
  have hs : ContMDiff 𝓘(ℝ, D × B) 𝓘(ℝ, B) ∞ (Prod.snd : D × B → B) := contDiff_snd.contMDiff
  exact hs.comp_contMDiffOn Φ.contMDiffOn_invFun

private theorem Smale.TransverseCoordinates.mfderiv_normalCoordinate {D B E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {p : M} (hp : p ∈ Φ.target) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) p =
      (ContinuousLinearMap.snd ℝ D B).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, D × B) Φ.symm p) := by
  have hs : ContMDiff 𝓘(ℝ, D × B) 𝓘(ℝ, B) ∞ (Prod.snd : D × B → B) := contDiff_snd.contMDiff
  have hd :
    mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, B) (Prod.snd : D × B → B) (Φ.symm p) =
      ContinuousLinearMap.snd ℝ D B := by
    rw [mfderiv_eq_fderiv]
    exact (ContinuousLinearMap.snd ℝ D B).fderiv
  rw [normalCoordinate,
    mfderiv_comp p (hs.mdifferentiableAt (by simp)) (Φ.symm.mdifferentiableAt (by simp) hp), hd]
  rfl

private theorem Smale.TransverseCoordinates.surjective_mfderiv_normalCoordinate {D B E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {p : M} (hp : p ∈ Φ.target) :
    Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) p) := by
  rw [mfderiv_normalCoordinate Φ hp]
  exact
    (show Function.Surjective (ContinuousLinearMap.snd ℝ D B) from fun w => ⟨(0, w), rfl⟩).comp
      (Smale.PartialChart.bijective_mfderiv Φ.symm hp).2

private theorem Smale.TransverseCoordinates.normalCoordinate_sheet_eventually_zero {D B E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {N : Type*} [TopologicalSpace N]
    {F : N → M} (hF : Continuous F) (hclean : ∀ q ∈ Φ.source, Φ q ∈ Set.range F ↔ q.2 = 0) {x : N}
    (hx : F x ∈ Φ.target) : (normalCoordinate Φ ∘ F) =ᶠ[𝓝 x] (fun _ => 0) := by
  filter_upwards [hF.continuousAt.preimage_mem_nhds (Φ.open_target.mem_nhds hx)] with y hy
  have hq : Φ.invFun (F y) ∈ Φ.source := Φ.map_target' hy
  exact (hclean _ hq).mp ⟨y, (Φ.right_inv' hy).symm⟩

private theorem Smale.TransverseCoordinates.normalDerivative_comp_sheet_eq_zero {D B E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {G N : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [TopologicalSpace N] [ChartedSpace G N] {F : N → M}
    (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F) (hclean : ∀ q ∈ Φ.source, Φ q ∈ Set.range F ↔ q.2 = 0)
    {x : N} (hx : F x ∈ Φ.target) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) (F x)).comp (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x) = 0 :=
  by
  have heq := normalCoordinate_sheet_eventually_zero Φ hF.continuous hclean hx
  have hzero : mfderiv 𝓘(ℝ, G) 𝓘(ℝ, B) (normalCoordinate Φ ∘ F) x = 0 := by
    rw [heq.mfderiv_eq]
    simp only [mfderiv_const]
    rfl
  have hnormal := (contMDiffOn_normalCoordinate Φ).contMDiffAt (Φ.open_target.mem_nhds hx)
  rw [mfderiv_comp x (hnormal.mdifferentiableAt (by simp))
      (hF.mdifferentiableAt (by simp))] at hzero
  exact hzero

public
theorem Smale.StripCoordinates.hasDerivAt_verticalSlice {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : (ℝ × ℝ) → E} {t s : ℝ} (hF : DifferentiableAt ℝ F (t, s)) :
    HasDerivAt (fun u : ℝ => F (t, u)) (fderiv ℝ F (t, s) (0, 1)) s := by
  have hi : HasDerivAt (fun u : ℝ => (t, u)) (0, 1) s :=
    (hasDerivAt_const s t).prodMk (hasDerivAt_id s)
  exact hF.hasFDerivAt.comp_hasDerivAt s hi

private theorem Smale.StripCoordinates.hasDerivAt_horizontalSlice {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : (ℝ × ℝ) → E} {t s : ℝ} (hF : DifferentiableAt ℝ F (t, s)) :
    HasDerivAt (fun u : ℝ => F (u, s)) (fderiv ℝ F (t, s) (1, 0)) t := by
  have hi : HasDerivAt (fun u : ℝ => (u, s)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t s)
  exact hF.hasFDerivAt.comp_hasDerivAt t hi

private abbrev Smale.StripCoordinates.Space (A B : Type*) :=
  (ℝ × A) × B

private def
    Smale.StripCoordinates.center {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    (t : ℝ) : Space A B :=
  ((t, 0), 0)

private def Smale.StripCoordinates.model {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] (v : ℝ → B) (p : ℝ × ℝ) : Space A B :=
  ((p.1, 0), p.2 • v p.1)

private def
    Smale.StripCoordinates.normalDerivative {A B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (F : (ℝ × ℝ) → Space A B) (t : ℝ) : B :=
  fderiv ℝ (fun p => (F p).2) (t, 0) (0, 1)

private def Smale.StripCoordinates.blend {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (v : ℝ → B) (F₀ F₁ : (ℝ × ℝ) → Space A B)
    (β₀ β₁ : ℝ → ℝ) (p : ℝ × ℝ) : Space A B :=
  model v p + β₀ p.1 • (F₀ p - model v p) + β₁ p.1 • (F₁ p - model v p)

private theorem Smale.StripCoordinates.contDiff_model {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B} (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (model (A := A) v) :=
  (contDiff_fst.prodMk contDiff_const).prodMk (contDiff_snd.smul (hv.comp contDiff_fst))

private theorem Smale.StripCoordinates.contDiff_blend {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B}
    {F₀ F₁ : (ℝ × ℝ) → Space A B} {β₀ β₁ : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hF₀ : ContDiff ℝ ∞ F₀)
    (hF₁ : ContDiff ℝ ∞ F₁) (hβ₀ : ContDiff ℝ ∞ β₀) (hβ₁ : ContDiff ℝ ∞ β₁) :
    ContDiff ℝ ∞ (blend v F₀ F₁ β₀ β₁) :=
  ((contDiff_model hv).add ((hβ₀.comp contDiff_fst).smul (hF₀.sub (contDiff_model hv)))).add
    ((hβ₁.comp contDiff_fst).smul (hF₁.sub (contDiff_model hv)))

private theorem Smale.StripCoordinates.model_zero {A B : Type*} [NormedAddCommGroup A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (v : ℝ → B) (t : ℝ) :
    model (A := A) v (t, 0) = Smale.StripCoordinates.center t := by
  simp only [model, Smale.StripCoordinates.center, zero_smul]

private theorem
    Smale.StripCoordinates.blend_zero {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B} {F₀ F₁ : (ℝ × ℝ) → Space A B}
    {β₀ β₁ : ℝ → ℝ} (h₀ : ∀ t, β₀ t ≠ 0 → F₀ (t, 0) = Smale.StripCoordinates.center t)
    (h₁ : ∀ t, β₁ t ≠ 0 → F₁ (t, 0) = Smale.StripCoordinates.center t) (t : ℝ) :
    blend v F₀ F₁ β₀ β₁ (t, 0) = Smale.StripCoordinates.center t := by
  have hterm₀ : β₀ t • (F₀ (t, 0) - model v (t, 0)) = 0 := by
    by_cases h : β₀ t = 0
    · rw [h, zero_smul]
    · rw [h₀ t h, model_zero, sub_self, smul_zero]
  have hterm₁ : β₁ t • (F₁ (t, 0) - model v (t, 0)) = 0 := by
    by_cases h : β₁ t = 0
    · rw [h, zero_smul]
    · rw [h₁ t h, model_zero, sub_self, smul_zero]
  change
    model v (t, 0) + β₀ t • (F₀ (t, 0) - model v (t, 0)) + β₁ t • (F₁ (t, 0) - model v (t, 0)) =
      Smale.StripCoordinates.center t
  rw [hterm₀, hterm₁, add_zero, add_zero, model_zero]

private theorem Smale.StripCoordinates.blend_eq_left {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B}
    {F₀ F₁ : (ℝ × ℝ) → Space A B} {β₀ β₁ : ℝ → ℝ} {p : ℝ × ℝ} (h₀ : β₀ p.1 = 1)
    (h₁ : β₁ p.1 = 0) : blend v F₀ F₁ β₀ β₁ p = F₀ p := by
  simp only [blend, h₀, h₁, one_smul, zero_smul, add_zero]
  rw [← add_sub_assoc, add_sub_cancel_left]

private theorem Smale.StripCoordinates.blend_eq_right {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B}
    {F₀ F₁ : (ℝ × ℝ) → Space A B} {β₀ β₁ : ℝ → ℝ} {p : ℝ × ℝ} (h₀ : β₀ p.1 = 0)
    (h₁ : β₁ p.1 = 1) : blend v F₀ F₁ β₀ β₁ p = F₁ p := by
  simp only [blend, h₀, h₁, one_smul, zero_smul, add_zero]
  rw [← add_sub_assoc, add_sub_cancel_left]

private theorem Smale.StripCoordinates.normalDerivative_blend {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B}
    {F₀ F₁ : (ℝ × ℝ) → Space A B} {β₀ β₁ : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (hF₀ : ContDiff ℝ ∞ F₀)
    (hF₁ : ContDiff ℝ ∞ F₁) (hβ₀ : ContDiff ℝ ∞ β₀) (hβ₁ : ContDiff ℝ ∞ β₁)
    (h₀ : ∀ t, β₀ t ≠ 0 → normalDerivative F₀ t = v t)
    (h₁ : ∀ t, β₁ t ≠ 0 → normalDerivative F₁ t = v t) (t : ℝ) :
    normalDerivative (blend v F₀ F₁ β₀ β₁) t = v t := by
  have hm : HasDerivAt (fun s : ℝ => s • v t) (v t) 0 := by
    simpa only [one_smul, id_eq] using (hasDerivAt_id (0 : ℝ)).smul_const (v t)
  have hd₀ :=
    hasDerivAt_verticalSlice (t := t) (s := 0) (hF₀.snd.contDiffAt.differentiableAt (by simp))
  have hd₁ :=
    hasDerivAt_verticalSlice (t := t) (s := 0) (hF₁.snd.contDiffAt.differentiableAt (by simp))
  have hterm₀ : β₀ t • (normalDerivative F₀ t - v t) = 0 := by
    by_cases h : β₀ t = 0
    · rw [h, zero_smul]
    · rw [h₀ t h, sub_self, smul_zero]
  have hterm₁ : β₁ t • (normalDerivative F₁ t - v t) = 0 := by
    by_cases h : β₁ t = 0
    · rw [h, zero_smul]
    · rw [h₁ t h, sub_self, smul_zero]
  have hblend :
    HasDerivAt (fun s : ℝ => (blend v F₀ F₁ β₀ β₁ (t, s)).2)
      (v t + β₀ t • (normalDerivative F₀ t - v t) + β₁ t • (normalDerivative F₁ t - v t)) 0 :=
    HasDerivAt.add (HasDerivAt.add hm (HasDerivAt.const_smul (β₀ t) (HasDerivAt.sub hd₀ hm)))
      (HasDerivAt.const_smul (β₁ t) (HasDerivAt.sub hd₁ hm))
  have hblend' : HasDerivAt (fun s : ℝ => (blend v F₀ F₁ β₀ β₁ (t, s)).2) (v t) 0 := by
    simpa only [hterm₀, hterm₁, add_zero] using hblend
  exact
    (hasDerivAt_verticalSlice
          ((contDiff_blend hv hF₀ hF₁ hβ₀ hβ₁).snd.contDiffAt.differentiableAt (by simp))).unique
      hblend'

private structure Smale.StripNormalData (A B : Type*) [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (S : Set M) (k : (ℝ × ℝ) → M) where
  chart :
    PartialDiffeomorph 𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E) (StripCoordinates.Space A B) M ∞
  line : Set.MapsTo StripCoordinates.center (Set.Icc (0 : ℝ) 1) chart.source
  sheet : ∀ q ∈ chart.source, chart q ∈ S ↔ q.2 = 0
  center : ∀ t, k (t, 0) = chart (StripCoordinates.center t)
  normal_nonzero :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      fderiv ℝ (TransverseCoordinates.normalCoordinate chart ∘ k) (t, 0) (0, 1) ≠ 0

private theorem Smale.StripCoordinates.horizontal_derivative_of_center {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {F : (ℝ × ℝ) → Space A B} {t : ℝ} (hF : DifferentiableAt ℝ F (t, 0))
    (hc : ∀ s, F (s, 0) = Smale.StripCoordinates.center s) :
    fderiv ℝ F (t, 0) (1, 0) = Smale.StripCoordinates.center 1 := by
  have hd := hasDerivAt_horizontalSlice hF
  have heq : (fun s : ℝ => F (s, 0)) = Smale.StripCoordinates.center := funext hc
  rw [heq] at hd
  have hcenter :
    HasDerivAt (Smale.StripCoordinates.center : ℝ → Space A B) (Smale.StripCoordinates.center 1)
      t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : A))).prodMk (hasDerivAt_const t (0 : B))
  exact hd.unique hcenter

private theorem Smale.StripCoordinates.horizontal_derivative_of_center_germ {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {F : (ℝ × ℝ) → Space A B} {t : ℝ} (hF : DifferentiableAt ℝ F (t, 0))
    (hc : (fun s : ℝ => F (s, 0)) =ᶠ[𝓝 t] Smale.StripCoordinates.center) :
    fderiv ℝ F (t, 0) (1, 0) = Smale.StripCoordinates.center 1 := by
  have hd := hasDerivAt_horizontalSlice hF
  have hcenter :
    HasDerivAt (Smale.StripCoordinates.center : ℝ → Space A B) (Smale.StripCoordinates.center 1)
      t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : A))).prodMk (hasDerivAt_const t (0 : B))
  exact hd.unique (hcenter.congr_of_eventuallyEq hc)

private theorem
    Smale.StripCoordinates.normalDerivative_eq_snd_fderiv {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {F : (ℝ × ℝ) → Space A B} {t : ℝ}
    (hF : DifferentiableAt ℝ F (t, 0)) : normalDerivative F t = (fderiv ℝ F (t, 0) (0, 1)).2 := by
  have hd := hF.hasFDerivAt.snd
  rw [normalDerivative, hd.fderiv]
  rfl

private theorem Smale.StripCoordinates.injective_of_horizontal_and_normal {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    (L : (ℝ × ℝ) →L[ℝ] Space A B) (hh : L (1, 0) = Smale.StripCoordinates.center 1)
    (hn : (L (0, 1)).2 ≠ 0) : Function.Injective L := by
  have hker : ∀ p : ℝ × ℝ, L p = 0 → p = 0 := by
    rintro ⟨a, b⟩ hp
    have hsplit : (a, b) = a • ((1 : ℝ), 0) + b • (0, 1) := by ext <;> simp
    rw [hsplit, map_add, map_smul, map_smul, hh] at hp
    have hb0 : b • (L (0, 1)).2 = 0 := by
      simpa [Smale.StripCoordinates.center] using congrArg Prod.snd hp
    have hb : b = 0 := (smul_eq_zero.mp hb0).resolve_right hn
    subst b
    have ha : a = 0 := by
      simpa [Smale.StripCoordinates.center] using congrArg (fun q : Space A B => q.1.1) hp
    subst a
    rfl
  intro p q hpq
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub, hpq, sub_self]

private theorem
    Smale.StripCoordinates.injective_fderiv_at_center {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {F : (ℝ × ℝ) → Space A B} {t : ℝ}
    (hF : DifferentiableAt ℝ F (t, 0)) (hc : ∀ s, F (s, 0) = Smale.StripCoordinates.center s)
    (hn : normalDerivative F t ≠ 0) : Function.Injective (fderiv ℝ F (t, 0)) := by
  apply
    injective_of_horizontal_and_normal (fderiv ℝ F (t, 0)) (horizontal_derivative_of_center hF hc)
  rwa [← normalDerivative_eq_snd_fderiv hF]

private def Smale.StripCoordinates.sheetTransverseInclusion {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] : A →L[ℝ] Space A B :=
  (ContinuousLinearMap.inl ℝ (ℝ × A) B).comp (ContinuousLinearMap.inr ℝ ℝ A)

private theorem
    Smale.StripCoordinates.sheetTransverseInclusion_apply {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] (a : A) :
    (sheetTransverseInclusion : A →L[ℝ] Space A B) a = ((0, a), 0) :=
  rfl

private theorem
    Smale.StripCoordinates.sheetTransverse_eq_strip_iff {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] (L : (ℝ × ℝ) →L[ℝ] Space A B)
    (hh : L (1, 0) = Smale.StripCoordinates.center 1) (hn : (L (0, 1)).2 ≠ 0) (a : A)
    (p : ℝ × ℝ) : sheetTransverseInclusion a = L p ↔ a = 0 ∧ p = 0 := by
  constructor
  · intro heq
    have hsplit : p = p.1 • ((1 : ℝ), 0) + p.2 • (0, 1) := by ext <;> simp
    have hexp : L p = p.1 • Smale.StripCoordinates.center 1 + p.2 • L (0, 1) := by
      conv_lhs => rw [hsplit]
      rw [map_add, map_smul, map_smul, hh]
    rw [hexp] at heq
    have hp2zero : p.2 • (L (0, 1)).2 = 0 := by
      simpa [sheetTransverseInclusion_apply, Smale.StripCoordinates.center] using
        (congrArg Prod.snd heq).symm
    have hp2 : p.2 = 0 := (smul_eq_zero.mp hp2zero).resolve_right hn
    rw [hp2, zero_smul, add_zero] at heq
    have hp1 : p.1 = 0 := by
      simpa [sheetTransverseInclusion_apply, Smale.StripCoordinates.center] using
        (congrArg (fun q : Space A B => q.1.1) heq).symm
    have ha : a = 0 := by
      simpa [sheetTransverseInclusion_apply, Smale.StripCoordinates.center] using
        congrArg (fun q : Space A B => q.1.2) heq
    exact ⟨ha, Prod.ext hp1 hp2⟩
  · rintro ⟨rfl, rfl⟩
    rw [map_zero, map_zero]

private theorem Smale.StripCoordinates.injective_sheetTransverse_normalQuotient {A B Z : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] (L : (ℝ × ℝ) →L[ℝ] Space A B) (Q : Space A B →L[ℝ] Z)
    (hh : L (1, 0) = Smale.StripCoordinates.center 1) (hn : (L (0, 1)).2 ≠ 0)
    (hker : Q.ker = L.range) : Function.Injective (Q.comp sheetTransverseInclusion) := by
  have hz : ∀ a : A, Q (sheetTransverseInclusion a) = 0 → a = 0 := by
    intro a ha
    have hmem : sheetTransverseInclusion a ∈ L.range := by
      rw [← hker]
      exact ha
    obtain ⟨p, hp⟩ := hmem
    exact ((sheetTransverse_eq_strip_iff L hh hn a p).mp hp.symm).1
  intro a b hab
  apply sub_eq_zero.mp
  apply hz
  change (Q.comp sheetTransverseInclusion) (a - b) = 0
  rw [map_sub, hab, sub_self]

private theorem Smale.StripCoordinates.ker_comp_eq_range_of_injective {A B Z : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : Space A B →L[ℝ] V) (L : (ℝ × ℝ) →L[ℝ] Space A B) (Q : V →L[ℝ] Z)
    (hT : Function.Injective T) (hker : Q.ker = (T.comp L).range) : (Q.comp T).ker = L.range := by
  ext v
  constructor
  · intro hv
    have hmem : T v ∈ (T.comp L).range := by
      rw [← hker]
      exact hv
    obtain ⟨p, hp⟩ := hmem
    exact ⟨p, hT hp⟩
  · rintro ⟨p, rfl⟩
    have hmem : T (L p) ∈ Q.ker := by
      rw [hker]
      exact ⟨p, rfl⟩
    exact hmem

private def
    Smale.StripNormalData.coordinateMap {A B E M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k) : (ℝ × ℝ) → Smale.StripCoordinates.Space A B :=
  d.chart.symm ∘ k

private theorem Smale.StripNormalData.center_mem_target {A B E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    k (t, 0) ∈ d.chart.target := by
  rw [d.center t]
  exact d.chart.map_source' (d.line ht)

private theorem
    Smale.StripNormalData.coordinate_center_germ {A B E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (fun s : ℝ => d.coordinateMap (s, 0)) =ᶠ[𝓝 t] Smale.StripCoordinates.center := by
  have hc : Continuous (Smale.StripCoordinates.center : ℝ → Smale.StripCoordinates.Space A B) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  filter_upwards [hc.continuousAt.preimage_mem_nhds
      (d.chart.open_source.mem_nhds (d.line ht))] with
    s hs
  change d.chart.invFun (k (s, 0)) = Smale.StripCoordinates.center s
  rw [d.center s, d.chart.left_inv' hs]

private theorem Smale.StripNormalData.coordinate_center {A B E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    d.coordinateMap (t, 0) = Smale.StripCoordinates.center t :=
  (d.coordinate_center_germ ht).eq_of_nhds

private theorem
    Smale.StripNormalData.contDiffAt_coordinateMap {A B E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0)) : ContDiffAt ℝ ∞ d.coordinateMap (t, 0) :=
  ((d.chart.contMDiffOn_invFun.contMDiffAt
          (d.chart.open_target.mem_nhds (d.center_mem_target ht))).comp
      (t, 0) hk).contDiffAt

private theorem Smale.StripNormalData.horizontal_coordinateDerivative {A B E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : Smale.StripNormalData A B (E := E) S k) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0)) :
    fderiv ℝ d.coordinateMap (t, 0) (1, 0) = Smale.StripCoordinates.center 1 :=
  Smale.StripCoordinates.horizontal_derivative_of_center_germ
    ((d.contDiffAt_coordinateMap ht hk).differentiableAt (by simp)) (d.coordinate_center_germ ht)

private theorem Smale.StripNormalData.normal_coordinateDerivative_nonzero {A B E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : Smale.StripNormalData A B (E := E) S k) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0)) :
    (fderiv ℝ d.coordinateMap (t, 0) (0, 1)).2 ≠ 0 := by
  rw [←
    Smale.StripCoordinates.normalDerivative_eq_snd_fderiv
      ((d.contDiffAt_coordinateMap ht hk).differentiableAt (by simp))]
  exact d.normal_nonzero t ht

private theorem
    Smale.StripNormalData.native_derivative_factor {A B E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0)) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k (t, 0) =
      (mfderiv 𝓘(ℝ, Smale.StripCoordinates.Space A B) 𝓘(ℝ, E) d.chart
            (Smale.StripCoordinates.center t)).comp
        (fderiv ℝ d.coordinateMap (t, 0)) := by
  have hcoords := d.contDiffAt_coordinateMap ht hk
  have heq : (d.chart ∘ d.coordinateMap) =ᶠ[𝓝 (t, 0)] k := by
    filter_upwards [hk.continuousAt.preimage_mem_nhds
        (d.chart.open_target.mem_nhds (d.center_mem_target ht))] with
      p hp
    change d.chart (d.chart.invFun (k p)) = k p
    exact d.chart.right_inv' hp
  have hcsource : d.coordinateMap (t, 0) ∈ d.chart.source := by
    rw [d.coordinate_center ht]
    exact d.line ht
  rw [← heq.mfderiv_eq,
    mfderiv_comp (t, 0) (d.chart.mdifferentiableAt (by simp) hcsource)
      (hcoords.contMDiffAt.mdifferentiableAt (by simp)),
    d.coordinate_center ht, mfderiv_eq_fderiv]
  rfl

private theorem
    Smale.TransverseCoordinates.mfderiv_zero_section {D B E M : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {f : D → M}
    (hzero : ∀ x, Φ (x, 0) = f x) {x : D} (hx : (x, 0) ∈ Φ.source) :
    mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x =
      (mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, E) Φ (x, 0)).comp (ContinuousLinearMap.inl ℝ D B) := by
  have heq : f = Φ ∘ (ContinuousLinearMap.inl ℝ D B) := funext (fun y => (hzero y).symm)
  have hinl : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, D × B) ∞ (ContinuousLinearMap.inl ℝ D B) :=
    (ContinuousLinearMap.inl ℝ D B).contDiff.contMDiff
  rw [heq, mfderiv_comp x (Φ.mdifferentiableAt (by simp) hx) (hinl.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv, (ContinuousLinearMap.inl ℝ D B).fderiv]
  rfl

private theorem
    Smale.TransverseCoordinates.ker_normalDerivative_eq_range_zero_section {D B E M : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {f : D → M}
    (hzero : ∀ x, Φ (x, 0) = f x) {x : D} (hx : (x, 0) ∈ Φ.source) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) (f x)).ker =
      (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x).range := by
  let L : (D × B) →L[ℝ] E := mfderiv 𝓘(ℝ, D × B) 𝓘(ℝ, E) Φ (x, 0)
  let R : E →L[ℝ] (D × B) := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, D × B) Φ.symm (Φ (x, 0))
  have hdiff : Φ.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ, D × B) 𝓘(ℝ, E) :=
    ⟨Φ.mdifferentiableOn (by simp), Φ.symm.mdifferentiableOn (by simp)⟩
  have hRL : R.comp L = ContinuousLinearMap.id ℝ (D × B) := hdiff.symm_comp_deriv hx
  have hRL_apply (q : D × B) : R (L q) = q := by
    change (R.comp L) q = q
    rw [hRL]
    rfl
  have hsurj : Function.Surjective L := (Smale.PartialChart.bijective_mfderiv Φ hx).2
  have hnormal :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) (f x) = (ContinuousLinearMap.snd ℝ D B).comp R :=
    by
    rw [← hzero x, mfderiv_normalCoordinate Φ (Φ.map_source' hx)]
    rfl
  rw [hnormal, mfderiv_zero_section Φ hzero hx]
  ext v
  constructor
  · intro hv
    obtain ⟨⟨a, b⟩, hab⟩ := hsurj v
    have hb : b = 0 := by
      change (R v).2 = 0 at hv
      rw [← hab, hRL_apply] at hv
      exact hv
    subst b
    exact ⟨a, hab⟩
  · rintro ⟨a, rfl⟩
    change (R (L (a, 0))).2 = 0
    rw [hRL_apply]

private def
    Smale.StripNormalData.normalFrame {A B Z E M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S : Set M}
    {k : (ℝ × ℝ) → M} (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (t : ℝ) : A →L[ℝ] Z :=
  (fderiv ℝ (Smale.TransverseCoordinates.normalCoordinate Ψ ∘ d.chart)
        (Smale.StripCoordinates.center t)).comp
    Smale.StripCoordinates.sheetTransverseInclusion

private theorem
    Smale.StripNormalData.contDiffOn_normalFrame {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.normalFrame Ψ)
      {t |
        Smale.StripCoordinates.center t ∈ d.chart.source ∧
          d.chart (Smale.StripCoordinates.center t) ∈ Ψ.target} := by
  intro t ht
  have hnormal :=
    (Smale.TransverseCoordinates.contMDiffOn_normalCoordinate Ψ).contMDiffAt
      (Ψ.open_target.mem_nhds ht.2)
  have hchart := d.chart.contMDiffOn_toFun.contMDiffAt (d.chart.open_source.mem_nhds ht.1)
  have htransition :
    ContDiffAt ℝ ∞ (Smale.TransverseCoordinates.normalCoordinate Ψ ∘ d.chart)
      (Smale.StripCoordinates.center t) :=
    (hnormal.comp (Smale.StripCoordinates.center t) hchart).contDiffAt
  have hcenter :
    ContDiff ℝ ∞ (Smale.StripCoordinates.center : ℝ → Smale.StripCoordinates.Space A B) :=
    (contDiff_id.prodMk contDiff_const).prodMk contDiff_const
  exact
    (((htransition.fderiv_right (by simp)).comp t hcenter.contDiffAt).clm_comp
        contDiffAt_const).contDiffWithinAt

private theorem Smale.StripNormalData.exists_open_normalFrame_domain {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞)
    (htarget : ∀ t ∈ Set.Icc (0 : ℝ) 1, d.chart (Smale.StripCoordinates.center t) ∈ Ψ.target) :
    ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (0 : ℝ) 1 ⊆ U ∧ ContDiffOn ℝ ∞ (d.normalFrame Ψ) U := by
  have hcenter :
    Continuous (Smale.StripCoordinates.center : ℝ → Smale.StripCoordinates.Space A B) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hW : IsOpen (d.chart.source ∩ d.chart ⁻¹' Ψ.target) :=
    d.chart.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage d.chart.open_source Ψ.open_target
  refine
    ⟨Smale.StripCoordinates.center ⁻¹' (d.chart.source ∩ d.chart ⁻¹' Ψ.target),
      hW.preimage hcenter, fun t ht => ⟨d.line ht, htarget t ht⟩, ?_⟩
  exact d.contDiffOn_normalFrame Ψ

private theorem Smale.StripNormalData.injective_normalFrame_of_strip_germ {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0))
    {f : (ℝ × ℝ) → M} (hzero : ∀ x, Ψ (x, 0) = f x) {p : ℝ × ℝ} (hp : (p, 0) ∈ Ψ.source)
    {c : (ℝ × ℝ) → (ℝ × ℝ)} (hc : ContDiffAt ℝ ∞ c p) (hcp : c p = (t, 0))
    (hcs : Function.Surjective (fderiv ℝ c p)) (hgerm : f =ᶠ[𝓝 p] k ∘ c) :
    Function.Injective (d.normalFrame Ψ t) := by
  let T : Smale.StripCoordinates.Space A B →L[ℝ] E :=
    mfderiv 𝓘(ℝ, Smale.StripCoordinates.Space A B) 𝓘(ℝ, E) d.chart
      (Smale.StripCoordinates.center t)
  let L : (ℝ × ℝ) →L[ℝ] Smale.StripCoordinates.Space A B := fderiv ℝ d.coordinateMap (t, 0)
  let Q : E →L[ℝ] Z :=
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Z) (Smale.TransverseCoordinates.normalCoordinate Ψ) (f p)
  let J : (ℝ × ℝ) →L[ℝ] E := mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p
  let K : (ℝ × ℝ) →L[ℝ] E := mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k (t, 0)
  have hfp : f p = d.chart (Smale.StripCoordinates.center t) := by
    have heq := hgerm.eq_of_nhds
    dsimp only [Function.comp_apply] at heq
    rw [hcp, d.center t] at heq
    exact heq
  have htarget : f p ∈ Ψ.target := by
    have h := Ψ.map_source' hp
    rwa [hzero p] at h
  have hk' : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (c p) := by
    rw [hcp]
    exact hk
  have hdf :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p =
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k (t, 0)).comp (fderiv ℝ c p) := by
    rw [hgerm.mfderiv_eq,
      mfderiv_comp p (hk'.mdifferentiableAt (by simp))
        (hc.contMDiffAt.mdifferentiableAt (by simp)),
      hcp, mfderiv_eq_fderiv]
    rfl
  have hker : Q.ker = (T.comp L).range := by
    have h1 : Q.ker = J.range :=
      Smale.TransverseCoordinates.ker_normalDerivative_eq_range_zero_section Ψ hzero hp
    have h2 : J.range = K.range := by
      change (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p).range = K.range
      rw [hdf]
      exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hcs)
    have h3 : K.range = (T.comp L).range := by
      change (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k (t, 0)).range = (T.comp L).range
      rw [d.native_derivative_factor ht hk]
      rfl
    exact h1.trans (h2.trans h3)
  have hT : Function.Injective T := (Smale.PartialChart.bijective_mfderiv d.chart (d.line ht)).1
  have hinj :
    Function.Injective ((Q.comp T).comp Smale.StripCoordinates.sheetTransverseInclusion) :=
    Smale.StripCoordinates.injective_sheetTransverse_normalQuotient L (Q.comp T)
      (d.horizontal_coordinateDerivative ht hk) (d.normal_coordinateDerivative_nonzero ht hk)
      (Smale.StripCoordinates.ker_comp_eq_range_of_injective T L Q hT hker)
  have hnormal :=
    (Smale.TransverseCoordinates.contMDiffOn_normalCoordinate Ψ).contMDiffAt
      (Ψ.open_target.mem_nhds htarget)
  have hnormal' :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Z) ∞ (Smale.TransverseCoordinates.normalCoordinate Ψ)
      (d.chart (Smale.StripCoordinates.center t)) := by
    rw [← hfp]
    exact hnormal
  have htransition :
    fderiv ℝ (Smale.TransverseCoordinates.normalCoordinate Ψ ∘ d.chart)
        (Smale.StripCoordinates.center t) =
      Q.comp T := by
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp (Smale.StripCoordinates.center t) (hnormal'.mdifferentiableAt (by simp))
        (d.chart.mdifferentiableAt (by simp) (d.line ht))]
    rw [← hfp]
    rfl
  change
    Function.Injective
      ((fderiv ℝ (Smale.TransverseCoordinates.normalCoordinate Ψ ∘ d.chart)
            (Smale.StripCoordinates.center t)).comp
        Smale.StripCoordinates.sheetTransverseInclusion)
  rw [htransition]
  exact hinj

private def Smale.StripNormalData.sheetTransition {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    (ℝ × A) → ((ℝ × ℝ) × Z) :=
  (Ψ.symm ∘ d.chart) ∘ (ContinuousLinearMap.inl ℝ (ℝ × A) B)

private def Smale.StripNormalData.sheetDifferential {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) (t : ℝ) :
    (ℝ × A) →L[ℝ] ((ℝ × ℝ) × Z) :=
  fderiv ℝ (d.sheetTransition Ψ) (t, 0)

private theorem Smale.StripNormalData.contDiffAt_tubularTransition {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (Smale.StripCoordinates.center t) ∈ Ψ.target) :
    ContDiffAt ℝ ∞ (Ψ.symm ∘ d.chart) (Smale.StripCoordinates.center t) :=
  ((Ψ.contMDiffOn_invFun.contMDiffAt (Ψ.open_target.mem_nhds htarget)).comp
      (Smale.StripCoordinates.center t)
      (d.chart.contMDiffOn_toFun.contMDiffAt
        (d.chart.open_source.mem_nhds (d.line ht)))).contDiffAt

private theorem Smale.StripNormalData.contDiffAt_sheetTransition {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (Smale.StripCoordinates.center t) ∈ Ψ.target) :
    ContDiffAt ℝ ∞ (d.sheetTransition Ψ) (t, 0) :=
  (d.contDiffAt_tubularTransition Ψ ht htarget).comp (t, 0)
    (ContinuousLinearMap.inl ℝ (ℝ × A) B).contDiff.contDiffAt

private theorem
    Smale.StripNormalData.sheetDifferential_eq {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (Smale.StripCoordinates.center t) ∈ Ψ.target) :
    d.sheetDifferential Ψ t =
      (fderiv ℝ (Ψ.symm ∘ d.chart) (Smale.StripCoordinates.center t)).comp
        (ContinuousLinearMap.inl ℝ (ℝ × A) B) := by
  rw [sheetDifferential, sheetTransition,
    fderiv_comp (t, 0) ((d.contDiffAt_tubularTransition Ψ ht htarget).differentiableAt (by simp))
      (ContinuousLinearMap.inl ℝ (ℝ × A) B).differentiableAt,
    (ContinuousLinearMap.inl ℝ (ℝ × A) B).fderiv]
  rfl

private theorem
    Smale.StripNormalData.normal_sheetDifferential {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (Smale.StripCoordinates.center t) ∈ Ψ.target) :
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) Z).comp
        ((d.sheetDifferential Ψ t).comp (ContinuousLinearMap.inr ℝ ℝ A)) =
      d.normalFrame Ψ t := by
  have hn :
    fderiv ℝ (Smale.TransverseCoordinates.normalCoordinate Ψ ∘ d.chart)
        (Smale.StripCoordinates.center t) =
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) Z).comp
        (fderiv ℝ (Ψ.symm ∘ d.chart) (Smale.StripCoordinates.center t)) := by
    change
      fderiv ℝ ((ContinuousLinearMap.snd ℝ (ℝ × ℝ) Z) ∘ (Ψ.symm ∘ d.chart))
          (Smale.StripCoordinates.center t) =
        _
    rw [fderiv_comp _ (ContinuousLinearMap.snd ℝ (ℝ × ℝ) Z).differentiableAt
        ((d.contDiffAt_tubularTransition Ψ ht htarget).differentiableAt (by simp)),
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) Z).fderiv]
  rw [d.sheetDifferential_eq Ψ ht htarget, normalFrame, hn]
  rfl

private theorem Smale.StripNormalData.sheetTransition_center_germ {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {f : (ℝ × ℝ) → M}
    (hzero : ∀ p, Ψ (p, 0) = f p) {q : ℝ → (ℝ × ℝ)} {t : ℝ} (hq : ContinuousAt q t)
    (hp : (q t, 0) ∈ Ψ.source) {c : (ℝ × ℝ) → (ℝ × ℝ)} (hcq : ∀ s, c (q s) = (s, 0))
    (hgerm : f =ᶠ[𝓝 (q t)] k ∘ c) :
    (fun s : ℝ => d.sheetTransition Ψ (s, 0)) =ᶠ[𝓝 t] fun s => (q s, 0) := by
  have hs := (hq.prodMk continuousAt_const).preimage_mem_nhds (Ψ.open_source.mem_nhds hp)
  filter_upwards [hs, hgerm.comp_tendsto hq.tendsto] with s hsource heq
  dsimp only [Function.comp_apply] at heq
  rw [hcq s] at heq
  change Ψ.invFun (d.chart (Smale.StripCoordinates.center s)) = (q s, 0)
  rw [← d.center s, ← heq, ← hzero (q s)]
  exact Ψ.left_inv' hsource

private theorem Smale.StripNormalData.sheetDifferential_arc_of_germ {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (htarget : d.chart (Smale.StripCoordinates.center t) ∈ Ψ.target)
    {q : ℝ → (ℝ × ℝ)} {v : ℝ × ℝ} (hq : HasDerivAt q v t)
    (hgerm : (fun s : ℝ => d.sheetTransition Ψ (s, 0)) =ᶠ[𝓝 t] fun s => (q s, 0)) :
    d.sheetDifferential Ψ t (1, 0) = (v, 0) := by
  have hF := (d.contDiffAt_sheetTransition Ψ ht htarget).differentiableAt (by simp)
  have hi : HasDerivAt (fun s : ℝ => (s, (0 : A))) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : A))
  have hd := hF.hasFDerivAt.comp_hasDerivAt t hi
  have hq' : HasDerivAt (fun s => (q s, (0 : Z))) (v, 0) t :=
    hq.prodMk (hasDerivAt_const t (0 : Z))
  exact hd.unique (hq'.congr_of_eventuallyEq hgerm)

private abbrev Smale.WhitneyPairModel.Plane :=
  EuclideanSpace ℝ (Fin 2)

private abbrev Smale.WhitneyPairModel.Space :=
  (ℝ × ℝ) × (Plane × Plane)

private abbrev Smale.WhitneyPairModel.Sheet :=
  ℝ × Plane

private def Smale.WhitneyPairModel.firstSheet (p : Sheet) : Space :=
  ((p.1, 0), (p.2, 0))

private def Smale.WhitneyPairModel.secondSheet (h : ℝ) (p : Sheet) : Space :=
  ((p.1, h * (1 - p.1 ^ 2)), (0, p.2))

private def Smale.WhitneyPairModel.bigon (h : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.2 ∧ h * p.1 ^ 2 + p.2 ≤ h}

private def Smale.WhitneyPairModel.bigonEmbedding : (ℝ × ℝ) → Space := fun p => (p, (0, 0))

private theorem Smale.WhitneyPairModel.isClosed_bigon (h : ℝ) : IsClosed (bigon h) :=
  (isClosed_le continuous_const continuous_snd).inter
    (isClosed_le (show Continuous (fun p : ℝ × ℝ => h * p.1 ^ 2 + p.2) by fun_prop)
      continuous_const)

private theorem
    Smale.WhitneyPairModel.zero_mem_bigon {h : ℝ} (hh : 0 ≤ h) : (0 : ℝ × ℝ) ∈ bigon h := by
  exact ⟨le_rfl, by simpa using hh⟩

private theorem Smale.WhitneyPairModel.bigon_subset_rectangle {h : ℝ} (hh : 0 < h) :
    bigon h ⊆ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) h := by
  intro p hp
  rcases hp with ⟨ht, hupper⟩
  have hsq : p.1 ^ 2 ≤ 1 := by nlinarith
  have hheight : p.2 ≤ h := by nlinarith [sq_nonneg p.1]
  exact ⟨⟨by nlinarith, by nlinarith⟩, ht, hheight⟩

private theorem Smale.WhitneyPairModel.isCompact_bigon {h : ℝ} (hh : 0 < h) : IsCompact (bigon h) :=
  (CompactIccSpace.isCompact_Icc.prod CompactIccSpace.isCompact_Icc).of_isClosed_subset
    (isClosed_bigon h) (bigon_subset_rectangle hh)

private theorem Smale.WhitneyPairModel.mem_interior_bigon_iff (h : ℝ) (p : ℝ × ℝ) :
    p ∈ interior (bigon h) ↔ 0 < p.2 ∧ p.2 < h * (1 - p.1 ^ 2) := by
  constructor
  · intro hp
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
    have hd (a : ℝ) : Dist.dist (p.1, p.2 + a) p = |a| := by simp [Prod.dist_eq]
    have hm : (p.1, p.2 + (-ε / 2)) ∈ Metric.ball p ε := by
      change Dist.dist (p.1, p.2 + (-ε / 2)) p < ε
      rw [hd, abs_of_neg (by linarith)]
      linarith
    have hp' : (p.1, p.2 + ε / 2) ∈ Metric.ball p ε := by
      change Dist.dist (p.1, p.2 + ε / 2) p < ε
      rw [hd, abs_of_pos (by linarith)]
      linarith
    have hlo := (hball hm).1
    have hhi := (hball hp').2
    change 0 ≤ p.2 + (-ε / 2) at hlo
    change h * p.1 ^ 2 + (p.2 + ε / 2) ≤ h at hhi
    constructor <;> nlinarith
  · rintro ⟨hlo, hhi⟩
    let U : Set (ℝ × ℝ) := {q | 0 < q.2 ∧ h * q.1 ^ 2 + q.2 < h}
    have hU : IsOpen U :=
      (isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt (show Continuous (fun q : ℝ × ℝ => h * q.1 ^ 2 + q.2) by fun_prop)
          continuous_const)
    have hpU : p ∈ U := ⟨hlo, by nlinarith⟩
    exact
      mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset (hU.mem_nhds hpU) (fun _ hq => ⟨hq.1.le, hq.2.le⟩))

private theorem Smale.WhitneyPairModel.mem_frontier_bigon_iff (h : ℝ) (p : ℝ × ℝ) :
    p ∈ frontier (bigon h) ↔ p ∈ bigon h ∧ (p.2 = 0 ∨ p.2 = h * (1 - p.1 ^ 2)) := by
  rw [frontier, (isClosed_bigon h).closure_eq, Set.mem_sdiff, mem_interior_bigon_iff]
  constructor
  · rintro ⟨hp, hnot⟩
    refine ⟨hp, ?_⟩
    by_cases ht : p.2 = 0
    · exact Or.inl ht
    · right
      have hlo : 0 < p.2 := lt_of_le_of_ne hp.1 (Ne.symm ht)
      have hhi : ¬p.2 < h * (1 - p.1 ^ 2) := fun hlt => hnot ⟨hlo, hlt⟩
      have hupper := hp.2
      change h * p.1 ^ 2 + p.2 ≤ h at hupper
      nlinarith
  · rintro ⟨hp, ht | ht⟩
    · exact ⟨hp, fun hstrict => hstrict.1.ne' ht⟩
    · exact ⟨hp, fun hstrict => hstrict.2.ne ht⟩

private theorem Smale.WhitneyPairModel.starConvex_bigon {h : ℝ} (hh : 0 ≤ h) :
    StarConvex ℝ (0 : ℝ × ℝ) (bigon h) := by
  rw [starConvex_zero_iff]
  intro p hp a ha₀ ha₁
  rcases hp with ⟨ht, hupper⟩
  change 0 ≤ a * p.2 ∧ h * (a * p.1) ^ 2 + a * p.2 ≤ h
  refine ⟨mul_nonneg ha₀ ht, ?_⟩
  calc
    h * (a * p.1) ^ 2 + a * p.2 = a * (h * p.1 ^ 2 + p.2) - (a * (1 - a)) * (h * p.1 ^ 2) := by
      ring
    _ ≤ a * (h * p.1 ^ 2 + p.2) :=
      (sub_le_self _
        (mul_nonneg (mul_nonneg ha₀ (sub_nonneg.mpr ha₁)) (mul_nonneg hh (sq_nonneg _))))
    _ ≤ a * h := (mul_le_mul_of_nonneg_left hupper ha₀)
    _ ≤ h := by nlinarith

private theorem Smale.WhitneyPairModel.lowerArc_mem_bigon {h s : ℝ} (hh : 0 ≤ h) (hs : |s| ≤ 1) :
    (s, 0) ∈ bigon h := by
  have habs := abs_le.mp hs
  refine ⟨le_rfl, ?_⟩
  change h * s ^ 2 + 0 ≤ h
  have hsq : s ^ 2 ≤ 1 := by nlinarith
  simpa only [mul_one, add_zero] using mul_le_mul_of_nonneg_left hsq hh

private theorem Smale.WhitneyPairModel.upperArc_mem_bigon {h s : ℝ} (hh : 0 ≤ h) (hs : |s| ≤ 1) :
    (s, h * (1 - s ^ 2)) ∈ bigon h := by
  have habs := abs_le.mp hs
  refine ⟨mul_nonneg hh (by nlinarith), ?_⟩
  change h * s ^ 2 + h * (1 - s ^ 2) ≤ h
  nlinarith

private theorem Smale.WhitneyPairModel.exists_bigon_boundary_cover {h : ℝ} (hh : 0 < h)
    {D E O : Set (ℝ × ℝ)} (hD : IsOpen D) (hE : IsOpen E) (hO : IsOpen O) (hleft : (-1, 0) ∈ O)
    (hright : (1, 0) ∈ O) (hlower : Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) D)
    (hupper : Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) E) :
    ∃ U : Set (ℝ × ℝ),
      ∃ V : Set (ℝ × ℝ),
        IsOpen U ∧
          IsOpen V ∧
            U ⊆ D ∧
              V ⊆ E ∧
                U ∩ V ⊆ O ∧
                  Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) U ∧
                    Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1)
                        V ∧
                      frontier (bigon h) ⊆ U ∪ V := by
  let B : Set (ℝ × ℝ) := {p | p.2 < h * (1 - p.1 ^ 2) / 2}
  let T : Set (ℝ × ℝ) := {p | h * (1 - p.1 ^ 2) / 2 < p.2}
  have hB : IsOpen B := isOpen_lt continuous_snd (by fun_prop)
  have hT : IsOpen T := isOpen_lt (by fun_prop) continuous_snd
  let U := D ∩ (O ∪ B)
  let V := E ∩ (O ∪ T)
  have hU : IsOpen U := hD.inter (hO.union hB)
  have hV : IsOpen V := hE.inter (hO.union hT)
  have hheight {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) : 0 < h * (1 - (2 * t - 1) ^ 2) := by
    calc
      0 < 4 * h * t * (1 - t) :=
        mul_pos (mul_pos (mul_pos (by norm_num) hh) ht.1) (sub_pos.mpr ht.2)
      _ = h * (1 - (2 * t - 1) ^ 2) := by ring
  have hlowU : Set.MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Set.Icc 0 1) U := by
    intro t ht
    refine ⟨hlower ht, ?_⟩
    by_cases ht0 : t = 0
    · subst t
      exact Or.inl (by simpa using hleft)
    by_cases ht1 : t = 1
    · subst t
      exact Or.inl (by convert hright using 1; norm_num)
    right
    have hh' := hheight ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    change (0 : ℝ) < h * (1 - (2 * t - 1) ^ 2) / 2
    linarith
  have huppV : Set.MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Set.Icc 0 1) V :=
    by
    intro t ht
    refine ⟨hupper ht, ?_⟩
    by_cases ht0 : t = 0
    · subst t
      exact Or.inl (by simpa using hleft)
    by_cases ht1 : t = 1
    · subst t
      exact Or.inl (by convert hright using 1; norm_num)
    right
    have hh' := hheight ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    change h * (1 - (2 * t - 1) ^ 2) / 2 < h * (1 - (2 * t - 1) ^ 2)
    linarith
  refine ⟨U, V, hU, hV, Set.inter_subset_left, Set.inter_subset_left, ?_, hlowU, huppV, ?_⟩
  · intro p hp
    rcases hp.1.2 with hpO | hpB
    · exact hpO
    rcases hp.2.2 with hpO | hpT
    · exact hpO
    have hpB' : p.2 < h * (1 - p.1 ^ 2) / 2 := hpB
    have hpT' : h * (1 - p.1 ^ 2) / 2 < p.2 := hpT
    exact (lt_asymm hpB' hpT').elim
  · intro p hp
    obtain ⟨hpK, hpedge⟩ := (mem_frontier_bigon_iff h p).mp hp
    have hpr := bigon_subset_rectangle hh hpK
    let t := (p.1 + 1) / 2
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp [t]
      constructor <;> linarith [hpr.1.1, hpr.1.2]
    have hbase : p.1 = 2 * t - 1 := by dsimp [t]; ring
    rcases hpedge with hpzero | hpupper
    · left
      have heq : p = (2 * t - 1, 0) := Prod.ext hbase hpzero
      rw [heq]
      exact hlowU ht
    · right
      have heq : p = (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) := by
        apply Prod.ext hbase
        rw [← hbase]
        exact hpupper
      rw [heq]
      exact huppV ht

private def Smale.WhitneyPairModel.arcTime (p : ℝ × ℝ) : ℝ :=
  (p.1 + 1) / 2

private def Smale.WhitneyPairModel.leftCornerCoordinates (h : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (arcTime p - p.2 / (4 * h * (1 - arcTime p)), p.2 / (4 * h * (1 - arcTime p)))

private theorem Smale.WhitneyPairModel.contDiff_arcTime : ContDiff ℝ ∞ arcTime := by
  unfold arcTime
  fun_prop

private def Smale.WhitneyPairModel.bigonReflection : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)

private theorem Smale.WhitneyPairModel.bigonReflection_apply (p : ℝ × ℝ) :
    bigonReflection p = (-p.1, p.2) :=
  rfl

private theorem Smale.WhitneyPairModel.arcTime_bigonReflection (p : ℝ × ℝ) :
    arcTime (bigonReflection p) = 1 - arcTime p := by
  dsimp [arcTime, bigonReflection]
  ring

private def Smale.WhitneyPairModel.rightCornerCoordinates (h : ℝ) : (ℝ × ℝ) → ℝ × ℝ :=
  leftCornerCoordinates h ∘ bigonReflection

private theorem
    Smale.WhitneyPairModel.leftCornerCoordinates_exchange {h : ℝ} (hh : h ≠ 0) {p : ℝ × ℝ}
    (hp : arcTime p ≠ 1) :
    leftCornerCoordinates h (p.1, h * (1 - p.1 ^ 2) - p.2) = (leftCornerCoordinates h p).swap := by
  have hd : 4 * h * (1 - arcTime p) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hh) (sub_ne_zero.mpr (Ne.symm hp))
  have hheight : h * (1 - p.1 ^ 2) = arcTime p * (4 * h * (1 - arcTime p)) := by
    dsimp [arcTime]
    ring
  have hv :
    (h * (1 - p.1 ^ 2) - p.2) / (4 * h * (1 - arcTime p)) =
      arcTime p - p.2 / (4 * h * (1 - arcTime p)) := by
    rw [sub_div, hheight, mul_div_cancel_right₀ _ hd]
  apply Prod.ext
  · change arcTime p - (h * (1 - p.1 ^ 2) - p.2) / (4 * h * (1 - arcTime p)) = _
    rw [hv]
    dsimp [leftCornerCoordinates]
    ring
  · exact hv

end Mathoverflow1973

end
