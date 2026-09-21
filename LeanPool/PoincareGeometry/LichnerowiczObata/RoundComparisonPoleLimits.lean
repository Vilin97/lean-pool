/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataRegularMetricComparison

/-! # Limits of the regular comparison at both round poles -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur Manifold Filter
open scoped Manifold ContDiff Topology ENNReal
namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [T3Space M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

local instance : IsContMDiffRiemannianBundle I (↑(0 : ℕ)) E
    (TangentSpace I : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)
local instance : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

/-- Every approach to the round north pole has the same inverse limit;
no fixed angular direction is assumed. -/
theorem round_comparison_inverse_tendsto_north
    {R : ℝ} (hR : 0 < R) {U : Set M}
    (F : U ≃ₜ RoundPuncturedSphere R (roundNorth : RoundAmbient P))
    (ρ : M → ℝ) (p : M)
    (hb : ∀ y : U, riemannianEDist I (y : M) p ≤ ENNReal.ofReal (ρ y))
    (hρ : ∀ y : U, ρ y = (intrinsicRoundInverseCoordinates R ((F y).1 : RoundAmbient P)).2)
    {α : Type*} {l : Filter α} (γ : α → RoundPuncturedSphere R (roundNorth : RoundAmbient P))
    (hγ : Tendsto (fun i => ((γ i).1 : RoundAmbient P)) l (𝓝 (R • roundNorth))) :
    Tendsto (fun i => (F.symm (γ i) : M)) l (𝓝 p) := by
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  have hr := ((continuous_intrinsicRoundInverse_radius (P := P) R).tendsto
    (R • roundNorth)).comp hγ
  rw [intrinsicRoundInverse_radius_north hR] at hr
  have he : Tendsto (fun i => ENNReal.ofReal
      (intrinsicRoundInverseCoordinates R ((γ i).1 : RoundAmbient P)).2) l (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
  apply tendsto_iff_edist_tendsto_0.mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he (fun _ => bot_le)
  intro i
  change riemannianEDist I (F.symm (γ i) : M) p ≤
    ENNReal.ofReal (intrinsicRoundInverseCoordinates R ((γ i).1 : RoundAmbient P)).2
  have hi := hρ (F.symm (γ i))
  rw [F.apply_symm_apply] at hi
  rw [← hi]
  exact hb (F.symm (γ i))

/-- The analogous inverse limit at the south pole follows from the
remaining radial distance bound, uniformly over all angular directions. -/
theorem round_comparison_inverse_tendsto_south
    {R : ℝ} (hR : 0 < R) {U : Set M}
    (F : U ≃ₜ RoundPuncturedSphere R (roundNorth : RoundAmbient P))
    (ρ : M → ℝ) (p : M)
    (hb : ∀ y : U, riemannianEDist I (y : M) p ≤ ENNReal.ofReal (Real.pi * R - ρ y))
    (hρ : ∀ y : U, ρ y = (intrinsicRoundInverseCoordinates R ((F y).1 : RoundAmbient P)).2)
    {α : Type*} {l : Filter α} (γ : α → RoundPuncturedSphere R (roundNorth : RoundAmbient P))
    (hγ : Tendsto (fun i => ((γ i).1 : RoundAmbient P)) l (𝓝 (-R • roundNorth))) :
    Tendsto (fun i => (F.symm (γ i) : M)) l (𝓝 p) := by
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  have hr := ((continuous_intrinsicRoundInverse_radius (P := P) R).tendsto
    (-R • roundNorth)).comp hγ
  rw [intrinsicRoundInverse_radius_south hR] at hr
  have hs : Tendsto (fun i => Real.pi * R -
      (intrinsicRoundInverseCoordinates R ((γ i).1 : RoundAmbient P)).2) l (𝓝 0) := by
    simpa only [Function.comp_def, sub_self] using (tendsto_const_nhds (x := Real.pi * R)).sub hr
  have he : Tendsto (fun i => ENNReal.ofReal (Real.pi * R -
      (intrinsicRoundInverseCoordinates R ((γ i).1 : RoundAmbient P)).2)) l (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hs
  apply tendsto_iff_edist_tendsto_0.mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he (fun _ => bot_le)
  intro i
  change riemannianEDist I (F.symm (γ i) : M) p ≤
    ENNReal.ofReal (Real.pi * R - (intrinsicRoundInverseCoordinates R ((γ i).1 : RoundAmbient P)).2)
  have hi := hρ (F.symm (γ i))
  rw [F.apply_symm_apply] at hi
  rw [← hi]
  exact hb (F.symm (γ i))

/-- The data retained by `obata_regular_metric_comparison` give both
inverse limits in the ambient-approach filters of the actual round sphere. -/
theorem obata_comparison_inverse_pole_limits
    {K a : ℝ} (hK : 0 < K) (f : M → ℝ) (p q : M)
    (F : {x : M // -a < f x ∧ f x < a} ≃ₜ
      RoundPuncturedSphere (1 / Real.sqrt K) (roundNorth : RoundAmbient (TangentSpace I p)))
    (hb : ∀ x, riemannianEDist I x p ≤ ENNReal.ofReal (obataRadial K a f x) ∧
      riemannianEDist I x q ≤ ENNReal.ofReal (Real.pi / Real.sqrt K - obataRadial K a f x))
    (hρ : ∀ y : {x : M // -a < f x ∧ f x < a},
      obataRadial K a f (y : M) = (intrinsicRoundInverseCoordinates (1 / Real.sqrt K)
        ((F y).1 : RoundAmbient (TangentSpace I p))).2) :
    let ι := fun x : RoundPuncturedSphere (1 / Real.sqrt K)
      (roundNorth : RoundAmbient (TangentSpace I p)) => (x.1 : RoundAmbient (TangentSpace I p))
    Tendsto (fun x => (F.symm x : M))
      (Filter.comap ι (𝓝 ((1 / Real.sqrt K) • roundNorth))) (𝓝 p) ∧
    Tendsto (fun x => (F.symm x : M))
      (Filter.comap ι (𝓝 (-(1 / Real.sqrt K) • roundNorth))) (𝓝 q) := by
  have hR : 0 < 1 / Real.sqrt K := one_div_pos.mpr (Real.sqrt_pos.mpr hK)
  constructor
  · exact round_comparison_inverse_tendsto_north (I := I) hR F (obataRadial K a f) p
      (fun y => (hb y).1) hρ id tendsto_comap
  · apply round_comparison_inverse_tendsto_south (I := I) hR F (obataRadial K a f) q
      (fun y => ?_) hρ id tendsto_comap
    simpa only [mul_one_div] using (hb y).2

end LichnerowiczObata
