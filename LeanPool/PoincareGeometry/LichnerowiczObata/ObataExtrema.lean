/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataEnergy
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # Extrema and critical values of an Obata function

The extrema are obtained from compactness; they are not assumed geometric data.
-/

@[expose] public noncomputable section
open Bundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "LC" => (leviCivitaConnection (I := I) (M := M))

/-- Fermat's theorem in a boundaryless manifold chart. -/
theorem gradient_eq_zero_of_local_extremum {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (hx : IsLocalExtr f x) :
    gradient (I := I) f x = 0 := by
  let φ := extChartAt I x
  have hxs : x ∈ φ.source := mem_extChartAt_source x
  have hxt : φ x ∈ φ.target := φ.map_source hxs
  have hc : ContinuousAt φ.symm (φ x) :=
    continuousAt_extChartAt_symm x
  have he : IsLocalExtr (f ∘ φ.symm) (φ x) := by
    have hx' : IsLocalExtr f (φ.symm (φ x)) := by simpa only [φ.left_inv hxs] using hx
    exact hx'.comp_continuous hc
  have hz := he.fderiv_eq_zero
  let e := trivializationAt E TM x
  have hd := fderiv_chart_comp f x x (mem_chart_source H x) hf
    (e.continuousLinearMapAt ℝ x (gradient (I := I) f x))
  have hinv : e.symmL ℝ x (e.continuousLinearMapAt ℝ x (gradient (I := I) f x)) =
      gradient (I := I) f x :=
    e.symmL_continuousLinearMapAt (mem_chart_source H x) (gradient (I := I) f x)
  change fderiv ℝ (f ∘ φ.symm) (φ x) _ = _ at hd
  rw [hz, zero_apply, hinv] at hd
  have hi := inner_gradient (I := I) f x (gradient (I := I) f x)
  exact (inner_self_eq_zero.mp (hi.trans hd.symm))

/-- A nonconstant Obata function has opposite nonzero extrema, with the
gradient norm determined everywhere by its value. -/
theorem obata_extrema [CompactSpace M] [Nonempty M] [PreconnectedSpace M]
    {K : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TM x), hessian LC f x v w = -K * f x * inner ℝ v w) :
    ∃ p q : M, 0 < f p ∧ f q = -f p ∧
      gradient (I := I) f p = 0 ∧ gradient (I := I) f q = 0 ∧
      (∀ x, -f p ≤ f x ∧ f x ≤ f p) ∧
      (∀ x, ‖gradient (I := I) f x‖ ^ 2 = K * ((f p) ^ 2 - (f x) ^ 2)) := by
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hf.continuous.continuousOn
  obtain ⟨q, _, hq⟩ := isCompact_univ.exists_isMinOn univ_nonempty hf.continuous.continuousOn
  have hgp := gradient_eq_zero_of_local_extremum
    ((hf p).mdifferentiableAt (by norm_num)) (Or.inr (hp.isLocalMax (by simp)))
  have hgq := gradient_eq_zero_of_local_extremum
    ((hf q).mdifferentiableAt (by norm_num)) (Or.inl (hq.isLocalMin (by simp)))
  have hbounds : ∀ x, f q ≤ f x ∧ f x ≤ f p := fun x => ⟨hq (mem_univ x), hp (mem_univ x)⟩
  have hlt : f q < f p := by
    have hle := (hbounds p).1
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · obtain ⟨x, y, hxy⟩ := hnon
      have hx := hbounds x
      have hy := hbounds y
      exfalso
      apply hxy
      linarith
  have he := obataEnergy_constant hf hH p q
  simp only [hgp, hgq, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at he
  have hs : f p ^ 2 = f q ^ 2 := by nlinarith
  have hneg : f q = -f p := by nlinarith [sq_nonneg (f p + f q)]
  have hpos : 0 < f p := by linarith
  refine ⟨p, q, hpos, hneg, hgp, hgq, ?_, ?_⟩
  · intro x
    simpa only [hneg] using hbounds x
  · intro x
    have hx := obataEnergy_constant hf hH x p
    rw [hgp, norm_zero] at hx
    nlinarith

/-- The only critical values are the positive maximum and its negative.
This does not yet assert uniqueness of either critical point. -/
theorem obata_critical_values [CompactSpace M] [Nonempty M] [PreconnectedSpace M]
    {K : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TM x), hessian LC f x v w = -K * f x * inner ℝ v w) :
    ∃ a : ℝ, 0 < a ∧ (∀ x, -a ≤ f x ∧ f x ≤ a) ∧
      (∀ x, gradient (I := I) f x = 0 ↔ f x = a ∨ f x = -a) := by
  obtain ⟨p, q, hp, hq, hgp, hgq, hb, hn⟩ := obata_extrema hK hf hnon hH
  refine ⟨f p, hp, hb, ?_⟩
  intro x
  rw [← sq_eq_sq_iff_eq_or_eq_neg]
  constructor
  · intro hz
    have he := hn x
    simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at he
    nlinarith
  · intro he
    have hz : ‖gradient (I := I) f x‖ ^ 2 = 0 := by rw [hn x, he, sub_self, mul_zero]
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (gradient (I := I) f x)])

end LichnerowiczObata
