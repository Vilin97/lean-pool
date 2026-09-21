/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataGlobalHomeomorph
public import LeanPool.PoincareGeometry.LichnerowiczObata.RoundPoleForwardMetric

/-! # A globally smooth metric embedding onto the round sphere -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur
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

/-- The actual inverse of the constructed global round homeomorphism,
viewed in the Euclidean ambient space, is smooth and preserves the
Riemannian inner product everywhere, including both poles. -/
theorem obata_global_round_metric_embedding
    (hdim : 1 < Module.rank ℝ E) {K : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TM x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w) :
    ∃ p : M, ∃ Q : Metric.sphere (0 : RoundAmbient (TM p)) (1 / Real.sqrt K) ≃ₜ M,
      let T := fun y : M => (Q.symm y : RoundAmbient (TM p))
      ContMDiffAt I 𝓘(ℝ, RoundAmbient (TM p)) ∞ T
        (Q (roundNorthPoint (one_div_pos.mpr (Real.sqrt_pos.mpr hK)))) ∧
      ContMDiffAt I 𝓘(ℝ, RoundAmbient (TM p)) ∞ T
        (Q (roundSouthPoint (one_div_pos.mpr (Real.sqrt_pos.mpr hK)))) ∧
      ContMDiff I 𝓘(ℝ, RoundAmbient (TM p)) ∞ T ∧
        ∀ (x : M) (v w : TM x),
          inner ℝ (mvfderiv I T x v) (mvfderiv I T x w) = inner ℝ v w := by
  obtain ⟨a, ha, hb, p, q, hpq, hmax, hmin, Q, hQN, hQS,
    ⟨N, hN0, hNd, hNm, hNeq, δN, hδN, hNreg⟩,
    ⟨S, hS0, hSd, hSm, hSeq, δS, hδS, hSreg⟩, T, hT, G, hG⟩ :=
    obata_global_round_homeomorph hdim hK hf hnon hH
  let : FiniteDimensional ℝ (TM p) := inferInstanceAs (FiniteDimensional ℝ E)
  have hR : 0 < 1 / Real.sqrt K := one_div_pos.mpr (Real.sqrt_pos.mpr hK)
  let F := fun y : M => (Q.symm y : RoundAmbient (TM p))
  have hNorth := round_pole_forward_metric (I := I) (P := TM p) rfl hR (ε := 1) (by norm_num)
    (roundNorthPoint hR) (by simp [roundNorthPoint]) Q N
    (hN0.trans hQN.symm) hNd hNm hNeq
  have hSouth := round_pole_forward_metric (I := I) (P := TM p) rfl hR (ε := -1) (by norm_num)
    (roundSouthPoint hR) (by simp [roundSouthPoint, neg_smul]) Q S
    (hS0.trans hQS.symm) hSd hSm hSeq
  rw [hQN] at hNorth
  rw [hQS] at hSouth
  have hreg : ∀ x : M, x ≠ p → x ≠ q →
      ContMDiffAt I 𝓘(ℝ, RoundAmbient (TM p)) ∞ F x ∧
      ∀ v w : TM x, inner ℝ (mvfderiv I F x v) (mvfderiv I F x w) = inner ℝ v w := by
    intro x hxp hxq
    have hx : -a < f x ∧ f x < a :=
      ⟨lt_of_le_of_ne (hb x).1 (fun he => hxq ((hmin x).mp he.symm)),
        lt_of_le_of_ne (hb x).2 (fun he => hxp ((hmax x).mp he))⟩
    let y : {x : M // -a < f x ∧ f x < a} := ⟨x, hx⟩
    have hopen : IsOpen {x : M | -a < f x ∧ f x < a} :=
      (isOpen_lt continuous_const hf.continuous).inter (isOpen_lt hf.continuous continuous_const)
    have heq : F =ᶠ[𝓝 x] T := by
      filter_upwards [hopen.mem_nhds hx] with z hz
      exact (hT ⟨z, hz⟩).1.symm
    refine ⟨(hT y).2.1.congr_of_eventuallyEq heq, ?_⟩
    intro v w
    have hd := heq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, RoundAmbient (TM p)))
    simp only [mvfderiv, hd]
    convert (hT y).2.2 v w using 1
    rfl
  have hall : ∀ x : M, ContMDiffAt I 𝓘(ℝ, RoundAmbient (TM p)) ∞ F x ∧
      ∀ v w : TM x, inner ℝ (mvfderiv I F x v) (mvfderiv I F x w) = inner ℝ v w := by
    intro x
    by_cases hxp : x = p
    · subst x
      exact hNorth
    · by_cases hxq : x = q
      · subst x
        exact hSouth
      · exact hreg x hxp hxq
  refine ⟨p, Q, ?_, ?_, fun x => (hall x).1, fun x => (hall x).2⟩
  · rw [hQN]
    exact hNorth.1
  · rw [hQS]
    exact hSouth.1

end LichnerowiczObata
