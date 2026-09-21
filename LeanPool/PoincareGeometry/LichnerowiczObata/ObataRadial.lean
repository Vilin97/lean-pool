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

public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataExtrema
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! # The radial function associated to an Obata function

This is a candidate radial coordinate; its identification with distance and
the global polar-coordinate isometry remain separate obligations.
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

/-- Scalar chain rule for the actual Riemannian gradient. -/
theorem gradient_comp_hasDerivAt {f : M → ℝ} {g : ℝ → ℝ} {x : M} {c : ℝ}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (hg : HasDerivAt g c (f x)) :
    gradient (I := I) (g ∘ f) x = c • gradient (I := I) f x := by
  apply gradient_eq_of_inner
  intro v
  rw [real_inner_smul_left, inner_gradient]
  have hm := mvfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := I) x
    hg.differentiableAt.mdifferentiableAt hf v
  simp only [mvfderiv, mfderiv_eq_fderiv, hg.hasFDerivAt.fderiv] at hm
  change mvfderiv I (g ∘ f) x v = mvfderiv I f x v * c at hm
  simpa only [mul_comm] using hm.symm

/-- The usual arccosine expression, prior to proving that it is a distance. -/
def obataRadial (K a : ℝ) (f : M → ℝ) (x : M) : ℝ :=
  Real.arccos (f x / a) / Real.sqrt K
theorem gradient_obataRadial {K a : ℝ} {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hm : f x / a ≠ -1) (hp : f x / a ≠ 1) :
    gradient (I := I) (obataRadial K a f) x =
      ((-(1 / Real.sqrt (1 - (f x / a) ^ 2)) * (1 / a)) / Real.sqrt K) •
        gradient (I := I) f x := by
  have hd := ((Real.hasDerivAt_arccos hm hp).comp (f x)
    ((hasDerivAt_id (f x)).div_const a)).div_const (Real.sqrt K)
  have hgradient := gradient_comp_hasDerivAt hf hd
  exact hgradient

/-- The arccosine radial function satisfies the eikonal equation on regular levels. -/
theorem norm_gradient_obataRadial {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : -a < f x ∧ f x < a)
    (hn : ‖gradient (I := I) f x‖ ^ 2 = K * (a ^ 2 - f x ^ 2)) :
    ‖gradient (I := I) (obataRadial K a f) x‖ = 1 := by
  have hm : -1 < f x / a := (lt_div_iff₀ ha).2 (by nlinarith [hx.1])
  have hp : f x / a < 1 := (div_lt_iff₀ ha).2 (by simpa using hx.2)
  have hsq : 0 < 1 - (f x / a) ^ 2 := by nlinarith
  have he : ‖gradient (I := I) (obataRadial K a f) x‖ ^ 2 = 1 := by
    rw [gradient_obataRadial hf (ne_of_gt hm) (ne_of_lt hp), norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, hn]
    simp only [div_pow, mul_pow, neg_sq, one_pow]
    rw [Real.sq_sqrt (by simpa only [div_pow] using le_of_lt hsq),
      Real.sq_sqrt (le_of_lt hK)]
    have hd : 0 < a ^ 2 - f x ^ 2 := by nlinarith [hx.1, hx.2]
    field_simp [ne_of_gt ha, ne_of_gt hK, ne_of_gt hd]
  nlinarith [norm_nonneg (gradient (I := I) (obataRadial K a f) x)]

/-- Reconstruct the function from the candidate radial coordinate. -/
theorem obataRadial_cos {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (x : M) (hx : -a ≤ f x ∧ f x ≤ a) :
    a * Real.cos (Real.sqrt K * obataRadial K a f x) = f x := by
  have hm : -1 ≤ f x / a := (le_div_iff₀ ha).2 (by nlinarith [hx.1])
  have hp : f x / a ≤ 1 := (div_le_iff₀ ha).2 (by simpa using hx.2)
  have hk := ne_of_gt (Real.sqrt_pos.2 hK)
  rw [obataRadial, mul_div_cancel₀ _ hk, Real.cos_arccos hm hp]
  exact mul_div_cancel₀ _ (ne_of_gt ha)

/-- A genuine Obata function supplies a radial candidate with unit gradient
on all noncritical levels. No distance or geodesic assertion is assumed. -/
theorem exists_obata_radial_eikonal
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    [CompactSpace M] [Nonempty M] [PreconnectedSpace M]
    {K : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TangentSpace I x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w) :
    ∃ a : ℝ, 0 < a ∧
      (∀ x, 0 ≤ obataRadial K a f x ∧ obataRadial K a f x ≤ Real.pi / Real.sqrt K) ∧
      (∀ x, a * Real.cos (Real.sqrt K * obataRadial K a f x) = f x) ∧
      (∀ x, gradient (I := I) f x ≠ 0 →
        ‖gradient (I := I) (obataRadial K a f) x‖ = 1) := by
  obtain ⟨p, q, hp, hq, hgp, hgq, hb, hn⟩ := obata_extrema hK hf hnon hH
  refine ⟨f p, hp, ?_, ?_, ?_⟩
  · intro x
    exact ⟨div_nonneg (Real.arccos_nonneg _) (Real.sqrt_nonneg _),
      div_le_div_of_nonneg_right (Real.arccos_le_pi _) (Real.sqrt_nonneg _)⟩
  · intro x
    exact obataRadial_cos hK hp x (hb x)
  · intro x hx
    have hstrict : -f p < f x ∧ f x < f p := by
      have hsq : f x ^ 2 ≠ f p ^ 2 := by
        intro he
        have hz : ‖gradient (I := I) f x‖ ^ 2 = 0 := by rw [hn x, he, sub_self, mul_zero]
        apply hx
        exact norm_eq_zero.mp (by nlinarith [norm_nonneg (gradient (I := I) f x)])
      have hbounds := hb x
      constructor <;> apply lt_of_le_of_ne
      · exact hbounds.1
      · intro he
        apply hsq
        rw [← he]
        ring
      · exact hbounds.2
      · intro he
        exact hsq (congrArg (fun t : ℝ => t ^ 2) he)
    exact norm_gradient_obataRadial hK hp
      ((hf x).mdifferentiableAt (by norm_num)) hstrict (hn x)

end LichnerowiczObata
