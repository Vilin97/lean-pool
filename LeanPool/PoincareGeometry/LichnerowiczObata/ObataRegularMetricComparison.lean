/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataPolarInverse
public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataUniquePoles

/-! # The regular metric comparison from the Obata equation alone -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur Manifold
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

/-- The Hessian equation in dimension at least two supplies the unique
poles, a single differentiable regular round comparison preserving the
metric, and the radial distance bounds needed for endpoint extension.
No critical point, coordinate chart, or successor-dimension instance is
assumed in the statement. -/
theorem obata_regular_metric_comparison
    (hdim : 1 < Module.rank ℝ E) {K : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TM x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w) :
    ∃ a : ℝ, 0 < a ∧ (∀ x, -a ≤ f x ∧ f x ≤ a) ∧ ∃ p q : M,
      p ≠ q ∧ (∀ x, f x = a ↔ x = p) ∧ (∀ x, f x = -a ↔ x = q) ∧
      (∀ x, riemannianEDist I x p ≤ ENNReal.ofReal (obataRadial K a f x) ∧
        riemannianEDist I x q ≤ ENNReal.ofReal (Real.pi / Real.sqrt K - obataRadial K a f x)) ∧
      ∃ F : {x : M // -a < f x ∧ f x < a} ≃ₜ
          RoundPuncturedSphere (1 / Real.sqrt K) (roundNorth : RoundAmbient (TM p)),
        HasRoundNorthInverseExtension I K F p ∧
        ∃ T : M → RoundAmbient (TM p),
          (∀ y : {x : M // -a < f x ∧ f x < a},
            T (y : M) = ((F y).1 : RoundAmbient (TM p)) ∧
            ContMDiffAt I 𝓘(ℝ, RoundAmbient (TM p)) ∞ T (y : M) ∧
            ∀ v w : TM (y : M),
              inner ℝ (mfderiv I 𝓘(ℝ, RoundAmbient (TM p)) T (y : M) v)
                (mfderiv I 𝓘(ℝ, RoundAmbient (TM p)) T (y : M) w) = inner ℝ v w) ∧
          (∀ y : {x : M // -a < f x ∧ f x < a},
            obataRadial K a f (y : M) =
              (intrinsicRoundInverseCoordinates (1 / Real.sqrt K)
                ((F y).1 : RoundAmbient (TM p))).2) ∧
          ∃ G : RoundAmbient (TM p) → M,
            ∀ x : RoundPuncturedSphere (1 / Real.sqrt K) (roundNorth : RoundAmbient (TM p)),
              G (x.1 : RoundAmbient (TM p)) = (F.symm x : M) ∧
              MDifferentiableAt 𝓘(ℝ, RoundAmbient (TM p)) I G (x.1 : RoundAmbient (TM p)) := by
  have hf2 : ContMDiff I 𝓘(ℝ, ℝ) 2 f :=
    hf.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  obtain ⟨a, ha, hb, p, q, hp, hq, hpq, hmax, hmin, hdist⟩ :=
    obata_unique_poles hdim hK hf2 hnon hH
  have hpm : IsMaxOn f univ p := fun x _ => by rw [hp]; exact (hb x).2
  have hcrit : gradient (I := I) f p = 0 := gradient_eq_zero_of_local_extremum
    ((hf2 p).mdifferentiableAt (by norm_num)) (Or.inr (hpm.isLocalMax (by simp)))
  have hz := (extChartAt I p).map_source (mem_extChartAt_source (I := I) p)
  have he : (extChartAt I p).symm ((extChartAt I p) p) = p :=
    (extChartAt I p).left_inv (mem_extChartAt_source (I := I) p)
  have hcrit' : gradient (I := I) f ((extChartAt I p).symm ((extChartAt I p) p)) = 0 := by
    rw [he]
    exact hcrit
  have hmax' : ∀ x, f x = a ↔ x = (extChartAt I p).symm ((extChartAt I p) p) := by
    simpa only [he] using hmax
  have hpos : 0 < Module.finrank ℝ E := Module.finrank_pos_iff.mpr
    (rank_pos_iff_nontrivial.mp (lt_trans (by simp) hdim))
  let : Fact (Module.finrank ℝ E = (Module.finrank ℝ E - 1) + 1) := ⟨by omega⟩
  have hcomparison := exists_obata_regular_forward_differentiable
    (n := Module.finrank ℝ E - 1) hf hnon hK ha hH p hz hcrit' hmax'
  rw [he] at hcomparison
  exact ⟨a, ha, hb, p, q, hpq, hmax, hmin, hdist, hcomparison⟩

end LichnerowiczObata
