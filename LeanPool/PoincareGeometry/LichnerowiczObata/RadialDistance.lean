/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.RegularizedRadial
public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataUniquePoles

/-! # The Obata radial coordinate is distance from its pole -/

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

/-- The global nonexpansion estimate gives both missing radial lower bounds. -/
theorem obataRadial_le_pole_distance {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f)
    (hb : ∀ x, -a ≤ f x ∧ f x ≤ a)
    (hn : ∀ x, ‖gradient (I := I) f x‖ ^ 2 = K * (a ^ 2 - f x ^ 2))
    {p q : M} (hp : f p = a) (hq : f q = -a) (x : M) :
    ENNReal.ofReal (obataRadial K a f x) ≤ riemannianEDist I x p ∧
    ENNReal.ofReal (Real.pi / Real.sqrt K - obataRadial K a f x) ≤ riemannianEDist I x q := by
  have hRp : obataRadial K a f p = 0 := by simp [obataRadial, hp, ha.ne']
  have hRq : obataRadial K a f q = Real.pi / Real.sqrt K := by
    simp [obataRadial, hq, ha.ne']
  have hRnon : 0 ≤ obataRadial K a f x :=
    div_nonneg (Real.arccos_nonneg _) (Real.sqrt_nonneg _)
  have hRle : obataRadial K a f x ≤ Real.pi / Real.sqrt K :=
    div_le_div_of_nonneg_right (Real.arccos_le_pi _) (Real.sqrt_nonneg _)
  constructor
  · simpa only [hRp, edist_eq_enorm_sub, sub_zero, ← ofReal_norm, Real.norm_eq_abs,
      abs_of_nonneg hRnon] using edist_obataRadial_le hK ha hf hb hn x p
  · simpa only [hRq, edist_eq_enorm_sub, ← ofReal_norm, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr hRle), neg_sub] using edist_obataRadial_le hK ha hf hb hn x q

variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- Radially parameterized gradient curves realize intrinsic distance on
every subsegment, not merely the unit-speed upper bound. -/
theorem riemannianEDist_obataRadial_curve_eq_abs [T2Space M]
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hb : ∀ x, -a ≤ f x ∧ f x ≤ a)
    (hn : ∀ x, ‖gradient (I := I) f x‖ ^ 2 = K * (a ^ 2 - f x ^ 2))
    {γ : ℝ → M}
    (hγ : IsMIntegralCurveOn γ (gradient (I := I) (obataRadial K a f))
      (Ioo 0 (Real.pi / Real.sqrt K)))
    (hs : ∀ t ∈ Ioo 0 (Real.pi / Real.sqrt K), -a < f (γ t) ∧ f (γ t) < a)
    (hr : ∀ t ∈ Ioo 0 (Real.pi / Real.sqrt K), obataRadial K a f (γ t) = t)
    {u w : ℝ} (hu : u ∈ Ioo 0 (Real.pi / Real.sqrt K))
    (hw : w ∈ Ioo 0 (Real.pi / Real.sqrt K)) :
    riemannianEDist I (γ u) (γ w) = ENNReal.ofReal |u - w| := by
  apply le_antisymm (riemannianEDist_obataRadial_curve_le_abs hK ha hf hn hγ hs u hu w hw)
  simpa only [hr u hu, hr w hw, edist_eq_enorm_sub, ← ofReal_norm, Real.norm_eq_abs] using
    edist_obataRadial_le hK ha (hf.of_le (by norm_num)) hb hn (γ u) (γ w)

/-- Every compact nonconstant Obata function in dimension at least two has
two unique poles, and its arccosine radial coordinate is exactly intrinsic
distance from the maximum pole. The complementary coordinate is distance
from the minimum pole. No minimizing property is assumed. -/
theorem exists_obata_pole_distance [CompactSpace M] [T2Space M] [Nonempty M] [PreconnectedSpace M]
    (hdim : 1 < Module.rank ℝ E) {K : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TangentSpace I x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w) :
    ∃ a : ℝ, 0 < a ∧ (∀ x, -a ≤ f x ∧ f x ≤ a) ∧ ∃ p q : M,
      f p = a ∧ f q = -a ∧ p ≠ q ∧
      (∀ x, f x = a ↔ x = p) ∧ (∀ x, f x = -a ↔ x = q) ∧
      ∀ x, riemannianEDist I x p = ENNReal.ofReal (obataRadial K a f x) ∧
        riemannianEDist I x q = ENNReal.ofReal (Real.pi / Real.sqrt K - obataRadial K a f x) := by
  obtain ⟨a, ha, hb, p, q, hp, hq, hpq, hup, huq, hd⟩ := obata_unique_poles hdim hK hf hnon hH
  obtain ⟨p₀, q₀, hpos, hmin, hgp, hgq, hb₀, hn₀⟩ := obata_extrema hK hf hnon hH
  have he : f p₀ = a := le_antisymm (hb p₀).2 (by simpa only [hp] using (hb₀ p).2)
  have hn : ∀ x, ‖gradient (I := I) f x‖ ^ 2 = K * (a ^ 2 - f x ^ 2) := by
    simpa only [he] using hn₀
  refine ⟨a, ha, hb, p, q, hp, hq, hpq, hup, huq, ?_⟩
  intro x
  have hl := obataRadial_le_pole_distance hK ha (hf.of_le (by norm_num)) hb hn hp hq x
  exact ⟨le_antisymm (hd x).1 hl.1, le_antisymm (hd x).2 hl.2⟩

end LichnerowiczObata
