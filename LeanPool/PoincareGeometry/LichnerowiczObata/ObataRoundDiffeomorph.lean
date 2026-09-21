/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataGlobalMetricEmbedding
public import LeanPool.PoincareGeometry.LichnerowiczObata.RoundMetricDiffeomorph
public import LeanPool.PoincareGeometry.LichnerowiczObata.BochnerBound

/-! # The intrinsic round-sphere conclusion of the Obata equation -/

@[expose] public noncomputable section
open Bundle AlmostSchur
open scoped Manifold ContDiff Topology
namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
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

/-- A nonconstant solution of the Obata equation yields a genuine smooth
diffeomorphism to a sphere. Its scaled inclusion preserves the given metric,
so the target has precisely the round metric of radius `1 / sqrt K`.
The ambient dimension is proved in the conclusion, not assumed. -/
theorem obata_round_metric_diffeomorph
    (hdim : 1 < Module.rank ℝ E) {K : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TM x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w) :
    ∃ p : M, ∃ hA : Module.finrank ℝ (RoundAmbient (TM p)) = Module.finrank ℝ E + 1,
      letI : Fact (Module.finrank ℝ (RoundAmbient (TM p)) = Module.finrank ℝ E + 1) := ⟨hA⟩
      ∃ d : M ≃ₘ⟮I, 𝓡 (Module.finrank ℝ E)⟯ Metric.sphere (0 : RoundAmbient (TM p)) 1,
        ∀ (x : M) (v w : TM x),
          inner ℝ (mvfderiv I (fun y : M => (1 / Real.sqrt K) • (d y : RoundAmbient (TM p))) x v)
            (mvfderiv I (fun y : M => (1 / Real.sqrt K) • (d y : RoundAmbient (TM p))) x w) =
              inner ℝ v w := by
  obtain ⟨p, Q, _, _, hT, hm⟩ := obata_global_round_metric_embedding hdim hK hf hnon hH
  let : FiniteDimensional ℝ (TM p) := inferInstanceAs (FiniteDimensional ℝ E)
  have hA : Module.finrank ℝ (RoundAmbient (TM p)) = Module.finrank ℝ E + 1 := by
    rw [(WithLp.linearEquiv 2 ℝ (TM p × ℝ)).finrank_eq, Module.finrank_prod]
    simp only [Module.finrank_self]
    rfl
  refine ⟨p, hA, ?_⟩
  let : Fact (Module.finrank ℝ (RoundAmbient (TM p)) = Module.finrank ℝ E + 1) := ⟨hA⟩
  obtain ⟨d, _, hd⟩ := exists_round_metric_diffeomorph
    (one_div_pos.mpr (Real.sqrt_pos.mpr hK)) rfl Q hT hm
  exact ⟨d, hd⟩

/-- Equality in the sharp eigenvalue bound forces the round metric, with
both directions of the underlying diffeomorphism smooth. -/
theorem extremal_eigenfunction_round_metric_diffeomorph
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
    [LindelofSpace M]
    (hdim : 2 ≤ Module.finrank ℝ E) {K : ℝ} (hK : 0 < K)
    (hRic : ∀ (x : M) (v : TM x),
      ((Module.finrank ℝ E : ℝ) - 1) * K * ‖v‖ ^ 2 ≤
        CovariantDerivative.ricciCurvature (cov := leviCivitaConnection (I := I)) x v v)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    (heigen : ∀ x, laplacian (leviCivitaConnection (I := I)) f x =
      -((Module.finrank ℝ E : ℝ) * K) * f x) :
    ∃ p : M, ∃ hA : Module.finrank ℝ (RoundAmbient (TM p)) = Module.finrank ℝ E + 1,
      letI : Fact (Module.finrank ℝ (RoundAmbient (TM p)) = Module.finrank ℝ E + 1) := ⟨hA⟩
      ∃ d : M ≃ₘ⟮I, 𝓡 (Module.finrank ℝ E)⟯ Metric.sphere (0 : RoundAmbient (TM p)) 1,
        ∀ (x : M) (v w : TM x),
          inner ℝ (mvfderiv I (fun y : M => (1 / Real.sqrt K) • (d y : RoundAmbient (TM p))) x v)
            (mvfderiv I (fun y : M => (1 / Real.sqrt K) • (d y : RoundAmbient (TM p))) x w) =
              inner ℝ v w := by
  have hrank : 1 < Module.rank ℝ E := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast (show 1 < Module.finrank ℝ E by omega)
  exact obata_round_metric_diffeomorph hrank hK hf hnon
    (hessian_equation_of_extremal_eigenfunction hdim hRic (hf.of_le (by decide)) heigen)

end LichnerowiczObata
