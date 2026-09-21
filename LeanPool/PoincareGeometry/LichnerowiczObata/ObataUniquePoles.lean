/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataRegularConnected
public import LeanPool.PoincareGeometry.LichnerowiczObata.ContinuousPoleMaps
public import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Uniqueness of the two Obata poles -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local instance uniquePolesSmoothMetricZero : IsContMDiffRiemannianBundle I (↑(0 : ℕ)) E
    (TangentSpace I : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)
local instance uniquePolesContinuousMetric : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

/-- A nonconstant compact Obata function in dimension at least two has
exactly one maximum and one minimum. The radial distance upper bounds
extend to every point, including both poles. -/
theorem obata_unique_poles [CompactSpace M] [T2Space M] [Nonempty M] [PreconnectedSpace M]
    (hdim : 1 < Module.rank ℝ E) {K : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TangentSpace I x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w) :
    ∃ a : ℝ, 0 < a ∧ (∀ x, -a ≤ f x ∧ f x ≤ a) ∧ ∃ p q : M,
      f p = a ∧ f q = -a ∧ p ≠ q ∧
      (∀ x, f x = a ↔ x = p) ∧ (∀ x, f x = -a ↔ x = q) ∧
      ∀ x, riemannianEDist I x p ≤ ENNReal.ofReal (obataRadial K a f x) ∧
        riemannianEDist I x q ≤ ENNReal.ofReal (Real.pi / Real.sqrt K - obataRadial K a f x) := by
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  obtain ⟨a, ha, hb, hn, P, Q, hcP, hcQ, hPQ⟩ := exists_continuous_obata_pole_maps hK hf hnon hH
  let S := {x : M | -a < f x ∧ f x < a}
  obtain ⟨hd, hs⟩ := obata_regular_dense_preconnected hdim hK hf hnon hH hb hn
  have hz (y : M) (hy : f y = a ∨ f y = -a) : gradient (I := I) f y = 0 := by
    have he : ‖gradient (I := I) f y‖ ^ 2 = 0 := by
      rw [hn y]
      rcases hy with hy | hy <;> rw [hy] <;> ring
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp he)
  have hPm : MapsTo P S {y : M | gradient (I := I) f y = 0} :=
    fun x hx => hz (P x) (Or.inl (hPQ x hx).1)
  have hQm : MapsTo Q S {y : M | gradient (I := I) f y = 0} :=
    fun x hx => hz (Q x) (Or.inr (hPQ x hx).2.1)
  have hdisc := isDiscrete_obata_critical_set hK hf hnon hH
  obtain ⟨x₀, hx₀⟩ := hd.nonempty
  let p := P x₀
  let q := Q x₀
  have hP : ∀ x ∈ S, P x = p := fun x hx => hs.constant_of_mapsTo hdisc hcP hPm hx hx₀
  have hQ : ∀ x ∈ S, Q x = q := fun x hx => hs.constant_of_mapsTo hdisc hcQ hQm hx hx₀
  have hfp : f p = a := (hPQ x₀ hx₀).1
  have hfq : f q = -a := (hPQ x₀ hx₀).2.1
  have hR : Continuous (obataRadial K a f) :=
    (Real.continuous_arccos.comp (hf.continuous.div_const a)).div_const (Real.sqrt K)
  have hdp : Continuous (fun x => riemannianEDist I x p) := continuous_id.edist continuous_const
  have hdq : Continuous (fun x => riemannianEDist I x q) := continuous_id.edist continuous_const
  have hCp := isClosed_le hdp (ENNReal.continuous_ofReal.comp hR)
  have hCq := isClosed_le hdq (ENNReal.continuous_ofReal.comp
    ((continuous_const (y := Real.pi / Real.sqrt K)).sub hR))
  have hbp : S ⊆ {x | riemannianEDist I x p ≤ ENNReal.ofReal (obataRadial K a f x)} := by
    intro x hx
    simpa only [Set.mem_ofPred_eq, hP x hx] using (hPQ x hx).2.2.1
  have hbq : S ⊆ {x | riemannianEDist I x q ≤ ENNReal.ofReal (Real.pi / Real.sqrt K - obataRadial K a f x)} := by
    intro x hx
    simpa only [Set.mem_ofPred_eq, hQ x hx] using (hPQ x hx).2.2.2
  have hbp' (x : M) : riemannianEDist I x p ≤ ENNReal.ofReal (obataRadial K a f x) :=
    closure_minimal hbp hCp (hd x)
  have hbq' (x : M) : riemannianEDist I x q ≤ ENNReal.ofReal (Real.pi / Real.sqrt K - obataRadial K a f x) :=
    closure_minimal hbq hCq (hd x)
  refine ⟨a, ha, hb, p, q, hfp, hfq, ?_, ?_, ?_, fun x => ⟨hbp' x, hbq' x⟩⟩
  · intro hpq
    rw [hpq] at hfp
    linarith
  · intro x
    constructor
    · intro hx
      apply edist_eq_zero.mp
      apply le_antisymm _ bot_le
      change riemannianEDist I x p ≤ 0
      simpa only [obataRadial, hx, div_self ha.ne', Real.arccos_one, zero_div,
        ENNReal.ofReal_zero] using hbp' x
    · rintro rfl
      exact hfp
  · intro x
    constructor
    · intro hx
      apply edist_eq_zero.mp
      apply le_antisymm _ bot_le
      change riemannianEDist I x q ≤ 0
      simpa only [obataRadial, hx, neg_div, div_self ha.ne', Real.arccos_neg_one, sub_self,
        ENNReal.ofReal_zero] using hbq' x
    · rintro rfl
      exact hfq

end LichnerowiczObata
