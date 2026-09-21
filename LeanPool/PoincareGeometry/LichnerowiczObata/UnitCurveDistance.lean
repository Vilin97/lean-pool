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

public import LeanPool.PoincareGeometry.LichnerowiczObata.RadialVelocity

/-! # Riemannian distance bounds for unit-speed curves -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur MeasureTheory Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [I.Boundaryless] in
/-- The canonical Riemannian extended distance is bounded by elapsed time
alongAlmostSchur a C1 unit-speed curve. -/
theorem riemannianEDist_le_of_unit_velocity {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hv : ∀ t ∈ Icc a b, ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ = 1) :
    riemannianEDist I (γ a) (γ b) ≤ ENNReal.ofReal (b - a) := by
  apply (riemannianEDist_le_pathELength hc rfl rfl hab).trans_eq
  rw [pathELength_eq_lintegral_mfderiv_Icc]
  have he : (∫⁻ t in Icc a b, ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ) =
      ∫⁻ _ in Icc a b, (1 : ℝ≥0∞) := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro t ht
    change ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ = 1
    rw [← ofReal_norm, hv t ht]
    norm_num
  rw [he]
  simp [Real.volume_Icc]

/-- An integral curve of a C1 unit vector field obeys the intrinsic distance
bound on every closed subinterval of its open domain. -/
theorem riemannianEDist_le_integralCurve [T2Space M]
    {v : Π x : M, TangentSpace I x} {γ : ℝ → M} {s : Set ℝ}
    (hs : IsOpen s) (hγ : IsMIntegralCurveOn γ v s)
    (hc : ∀ t ∈ s, ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y => (⟨y, v y⟩ : TangentBundle I M)) (γ t))
    (hn : ∀ t ∈ s, ‖v (γ t)‖ = 1)
    {a b : ℝ} (hab : a ≤ b) (hi : Icc a b ⊆ s) :
    riemannianEDist I (γ a) (γ b) ≤ ENNReal.ofReal (b - a) := by
  apply riemannianEDist_le_of_unit_velocity hab
  · intro t ht
    exact (contMDiffAt_integralCurve (hc t (hi ht))
      (hγ.isMIntegralCurveAt (hs.mem_nhds (hi ht)))).contMDiffWithinAt
  · intro t ht
    have hd := (hγ t (hi ht)).hasMFDerivAt (hs.mem_nhds (hi ht))
    rw [hd.mfderiv]
    change ‖(1 : ℝ) • v (γ t)‖ = 1
    simpa only [one_smul] using hn t (hi ht)

variable [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- The actual radial gradient flow has the distance control required for
endpoint completion; no metric bound is assumed. -/
theorem riemannianEDist_le_obataRadial_curve [T2Space M]
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (hn : ∀ y, ‖gradient (I := I) f y‖ ^ 2 = K * (a ^ 2 - f y ^ 2))
    {γ : ℝ → M} {s : Set ℝ} (hs : IsOpen s)
    (hγ : IsMIntegralCurveOn γ (gradient (I := I) (obataRadial K a f)) s)
    (hlevel : ∀ t ∈ s, -a < f (γ t) ∧ f (γ t) < a)
    {u w : ℝ} (huw : u ≤ w) (hi : Icc u w ⊆ s) :
    riemannianEDist I (γ u) (γ w) ≤ ENNReal.ofReal (w - u) := by
  apply riemannianEDist_le_integralCurve hs hγ _ _ huw hi
  · intro t ht
    have hm : -1 < f (γ t) / a := (lt_div_iff₀ ha).2 (by nlinarith [(hlevel t ht).1])
    have hp : f (γ t) / a < 1 := (div_lt_iff₀ ha).2 (by simpa using (hlevel t ht).2)
    letI : IsContMDiffRiemannianBundle I (↑(1 : ℕ)) E (TangentSpace I : M → Type _) :=
      IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)
    exact contMDiffAt_gradient 1
      (contMDiffAt_obataRadial (hf (γ t)) (ne_of_gt hm) (ne_of_lt hp))
  · intro t ht
    exact norm_gradient_obataRadial hK ha ((hf _).mdifferentiableAt (by norm_num))
      (hlevel t ht) (hn _)

end LichnerowiczObata
