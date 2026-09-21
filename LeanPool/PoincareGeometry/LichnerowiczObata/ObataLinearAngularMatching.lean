/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.SphereAngularIsometry
public import LeanPool.PoincareGeometry.LichnerowiczObata.RoundSouthPoleLog

/-! # Linear angular matching for the constructed Obata polar models -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur
open scoped Manifold ContDiff Topology
namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {n : ℕ} [hDimension : Fact (Module.finrank ℝ E = n + 1)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [PreconnectedSpace M]
  [CompactSpace M] [T2Space M] [Nonempty M]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

local instance linearAngularTangentFinrank (p : M) : Fact (Module.finrank ℝ (TM p) = n + 1) :=
  ⟨show Module.finrank ℝ E = n + 1 from Fact.out⟩

include hDimension in
/-- The two polar models of one Obata function match by an actual linear
isometry between the pole tangent spaces. Both pole derivatives, both full
polar metrics, and both regular coordinate homeomorphisms are retained. -/
theorem exists_obata_linearly_matched_polar_models
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a) (hb : ∀ x, -a ≤ f x ∧ f x ≤ a)
    (hH : ∀ (y : M) (v w : TM y),
      hessian (leviCivitaConnection (I := I)) f y v w = -K * f y * inner ℝ v w)
    (c d : M) {z z' : E} (hz : z ∈ (extChartAt I c).target) (hz' : z' ∈ (extChartAt I d).target)
    (hmax : ∀ x, f x = a ↔ x = (extChartAt I c).symm z)
    (hmin : ∀ x, f x = -a ↔ x = (extChartAt I d).symm z') :
    let p := (extChartAt I c).symm z
    let q := (extChartAt I d).symm z'
    ∃ Φ : TM p × ℝ → M, ∃ Ψ : TM q × ℝ → M,
      HasRadialPoleModel I Φ p ∧ HasRadialPoleModel I Ψ q ∧
      HasUnitPolarMetric I K Φ ∧ HasUnitPolarMetric I K Ψ ∧
      ∃ N : Metric.sphere (0 : TM p) 1 × Ioo 0 (Real.pi / Real.sqrt K) ≃ₜ
          {x : M // -a < f x ∧ f x < a},
      ∃ S : Metric.sphere (0 : TM q) 1 × Ioo 0 (Real.pi / Real.sqrt K) ≃ₜ
          {x : M // -a < f x ∧ f x < a},
        (∀ u, (N u : M) = Φ (u.1, u.2)) ∧
        (∀ u, (S u : M) = Ψ (u.1, u.2)) ∧
        (∀ u : Metric.sphere (0 : TM p) 1, ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
          obataRadial K a f (Φ (u, r)) = r) ∧
        (∀ u : Metric.sphere (0 : TM q) 1, ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
          obataRadial K a f (Ψ (u, r)) = Real.pi / Real.sqrt K - r) ∧
        (∀ u : Metric.sphere (0 : TM p) 1,
          IsMIntegralCurveOn (fun r => Φ (u, r)) (gradient (I := I) (obataRadial K a f))
            (Ioo 0 (Real.pi / Real.sqrt K))) ∧
        ∃ L : TM p ≃ₗᵢ[ℝ] TM q,
          (∀ u : Metric.sphere (0 : TM p) 1, ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
            Φ (u, Real.pi / Real.sqrt K - r) = Ψ (L (u : TM p), r)) ∧
          HasRoundNorthInverseExtension I K
            (N.symm.trans (curvatureRoundPolarHomeomorph hK)) p ∧
          HasRoundSouthInverseExtension I K
            (N.symm.trans (curvatureRoundPolarHomeomorph hK)) q := by
  obtain ⟨Φ, Ψ, hp, hq, hmN, hmS, N, S, hN, hS, hρN, hρS, hcN, A, hmatch, hregular⟩ :=
    exists_obata_matched_polar_models hf hnon hK ha hb hH c d hz hz' hmax hmin
  obtain ⟨hA, hAi, hmA, hmAi⟩ := hregular n Fact.out
  obtain ⟨L, hL⟩ := exists_linearIsometryEquiv_of_sphere_tangent_metric
    (n := n) A.toEquiv hA hAi hmA hmAi
  have hlinear : ∀ u : Metric.sphere (0 : TM ((extChartAt I c).symm z)) 1,
      ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
        Φ (u, Real.pi / Real.sqrt K - r) = Ψ (L (u : TM ((extChartAt I c).symm z)), r) := by
    intro u r hr
    rw [hL u]
    exact hmatch u r hr
  let : FiniteDimensional ℝ (TM ((extChartAt I c).symm z)) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let : CompleteSpace (TM ((extChartAt I c).symm z)) := FiniteDimensional.complete ℝ _
  exact ⟨Φ, Ψ, hp, hq, hmN, hmS, N, S, hN, hS, hρN, hρS, hcN, L, hlinear,
    hp.round_north_inverse_extension hK N hN,
    hq.round_south_inverse_extension L hK N hN hlinear⟩

end LichnerowiczObata
