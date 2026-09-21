/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.SmoothPolarMetricComparison
public import LeanPool.PoincareGeometry.LichnerowiczObata.SmoothObataPolar

public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataLinearAngularMatching
public import LeanPool.PoincareGeometry.LichnerowiczObata.PolarMetricComparison
public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataUniquePoles

/-! # One metric comparison with both constructed pole extensions -/

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

/-- From the Obata equation alone, construct one regular comparison whose
metric and both pole extensions belong to the same polar model. -/
theorem obata_regular_metric_comparison_both_poles
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
        HasRoundNorthInverseExtension I K F p ∧ HasRoundSouthInverseExtension I K F q ∧
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
  have hz := (extChartAt I p).map_source (mem_extChartAt_source (I := I) p)
  have hz' := (extChartAt I q).map_source (mem_extChartAt_source (I := I) q)
  have he : (extChartAt I p).symm ((extChartAt I p) p) = p :=
    (extChartAt I p).left_inv (mem_extChartAt_source (I := I) p)
  have he' : (extChartAt I q).symm ((extChartAt I q) q) = q :=
    (extChartAt I q).left_inv (mem_extChartAt_source (I := I) q)
  have hmax' : ∀ x, f x = a ↔ x = (extChartAt I p).symm ((extChartAt I p) p) := by
    simpa only [he] using hmax
  have hmin' : ∀ x, f x = -a ↔ x = (extChartAt I q).symm ((extChartAt I q) q) := by
    simpa only [he'] using hmin
  have hpos : 0 < Module.finrank ℝ E := Module.finrank_pos_iff.mpr
    (rank_pos_iff_nontrivial.mp (lt_trans (by simp) hdim))
  let : Fact (Module.finrank ℝ E = (Module.finrank ℝ E - 1) + 1) := ⟨by omega⟩
  let : Fact (Module.finrank ℝ (TM p) = (Module.finrank ℝ E - 1) + 1) :=
    ⟨show Module.finrank ℝ E = (Module.finrank ℝ E - 1) + 1 from Fact.out⟩
  have hmodels := exists_obata_linearly_matched_polar_models
    (n := Module.finrank ℝ E - 1) hf hnon hK ha hb hH p q hz hz' hmax' hmin'
  rw [he, he'] at hmodels
  obtain ⟨Φ, Ψ, hpmodel, hqmodel, hmN, hmS, N, S, hN, hS, hρN, hρS, hcN, L, hmatch, hNorth, hSouth⟩ := hmodels
  let U : TopologicalSpace.Opens M :=
    ⟨{x | -a < f x ∧ f x < a},
      (isOpen_lt continuous_const hf.continuous).inter
        (isOpen_lt hf.continuous continuous_const)⟩
  have hpm : IsMaxOn f univ p := fun x _ => by rw [hp]; exact (hb x).2
  have hcrit : gradient (I := I) f p = 0 := gradient_eq_zero_of_local_extremum
    ((hf2 p).mdifferentiableAt (by norm_num)) (Or.inr (hpm.isLocalMax (by simp)))
  have hSmooth : ∀ u : Metric.sphere (0 : TM p) 1,
      ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
      ContMDiffAt ((𝓡 (Module.finrank ℝ E - 1)).prod 𝓘(ℝ, ℝ)) I ∞
        (fun q : Metric.sphere (0 : TM p) 1 × ℝ => Φ (q.1, q.2)) (u, r) := by
    intro u r hr
    apply hpmodel.contMDiffAt_obata_polar hf hnon hK ha hH hcrit hp ?_ hρN hcN u hr
    intro v s hs
    rw [← hN (v, ⟨s, hs⟩)]
    exact (N (v, ⟨s, hs⟩)).property
  obtain ⟨T, hT, G, hG⟩ := hmN.smooth_regular_comparison
    (n := Module.finrank ℝ E - 1) hK U N hN Fact.out hSmooth
  refine ⟨a, ha, hb, p, q, hpq, hmax, hmin, hdist,
    N.symm.trans (curvatureRoundPolarHomeomorph hK), hNorth, hSouth, T, hT, ?_, G, hG⟩
  intro y
  change obataRadial K a f (y : M) =
    (intrinsicRoundInverseCoordinates (1 / Real.sqrt K)
      (((curvatureRoundPolarHomeomorph hK) (N.symm y)).1 : RoundAmbient (TM p))).2
  rw [intrinsicRoundInverseCoordinates_apply hK]
  have hρ := hρN (N.symm y).1 (N.symm y).2 (N.symm y).2.property
  rw [← hN (N.symm y), N.apply_symm_apply] at hρ
  exact hρ

end LichnerowiczObata
