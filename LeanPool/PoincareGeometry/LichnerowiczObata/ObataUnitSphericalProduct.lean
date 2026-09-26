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

public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataSphericalMetricProduct
public import LeanPool.PoincareGeometry.LichnerowiczObata.UnitPolarCoordinates

/-! # The constructed Obata product in unit angular coordinates -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
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

/-- The same constructed regular product admits unit angular coordinates.
Its full metric has no auxiliary chart radius, and its ambient parameter map
is jointly differentiable at every point of the parameter cylinder. -/
theorem exists_obata_unit_spherical_product
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (v w : TM y),
      hessian (leviCivitaConnection (I := I)) f y v w = -K * f y * inner ℝ v w)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : ∀ x, f x = a ↔ x = (extChartAt I c).symm z) :
    let p := (extChartAt I c).symm z
    ∃ Φ : TM p × ℝ → M,
      HasRadialPoleModel I Φ p ∧
      ∃ Q : Metric.sphere (0 : TM p) 1 × Ioo 0 (Real.pi / Real.sqrt K) ≃ₜ
          {x : M // -a < f x ∧ f x < a},
        (∀ q, (Q q : M) = Φ (q.1, q.2)) ∧
        (∀ u : Metric.sphere (0 : TM p) 1, ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
          obataRadial K a f (Φ (u, r)) = r) ∧
        (∀ u : Metric.sphere (0 : TM p) 1,
          IsMIntegralCurveOn (fun r => Φ (u, r)) (gradient (I := I) (obataRadial K a f))
            (Ioo 0 (Real.pi / Real.sqrt K))) ∧
        ∀ u : Metric.sphere (0 : TM p) 1, ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
          MDifferentiableAt 𝓘(ℝ, TM p × ℝ) I Φ (u, r) ∧
          ∀ w v : TM p, inner ℝ (u : TM p) w = 0 → inner ℝ (u : TM p) v = 0 →
            ∀ s t : ℝ,
              inner ℝ (mfderiv 𝓘(ℝ, TM p × ℝ) I Φ (u, r) (w, s))
                (mfderiv 𝓘(ℝ, TM p × ℝ) I Φ (u, r) (v, t)) =
                  (Real.sin (Real.sqrt K * r) ^ 2 / K) * inner ℝ w v + s * t := by
  obtain ⟨η, hη, hcurves, hinit, t, ht, e, he0, hez, hderiv0, hpoleSmooth, hsmooth, htarget, hrad, hgradient,
    R, hR, htR, hball, hsource, hregular, hrays, Q, hQ, hmetric⟩ :=
    exists_obata_spherical_metric_product hf hnon hK ha hH c hz hcrit hmax
  let p := (extChartAt I c).symm z
  let L := (trivializationAt E TM c).continuousLinearMapAt ℝ p
  let Γ := fun q : TM p × ℝ => η ((extChartAt I c).symm (e (L q.1)), q.2)
  let Φ := fun q : TM p × ℝ => Γ (R • q.1, q.2)
  let S := unitSphereScale (P := TM p) R hR
  let Q₁ := (S.prodCongr (Homeomorph.refl (Ioo 0 (Real.pi / Real.sqrt K)))).trans Q
  refine ⟨Φ, ?_, Q₁, ?_, ?_, ?_, ?_⟩
  · let A : TM p →L[ℝ] E := (1 / t) • L
    let χ : TM p → M := (extChartAt I c).symm ∘ e ∘ A
    have hA0 : A 0 = 0 := map_zero A
    have heA0 : e (A 0) = z := by rw [hA0, hez]
    have hi : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I c).symm z := by
      simpa only [I.range_eq_univ, contMDiffWithinAt_univ] using
        (contMDiffWithinAt_extChartAt_symm_range (I := I) (n := ∞) c hz)
    have heA : ContDiffAt ℝ ∞ (e ∘ A) 0 := by
      apply ContDiffAt.comp (g := e) (f := (A : TM p → E))
      · rw [hA0]
        exact hpoleSmooth
      · exact A.contDiff.contDiffAt
    refine ⟨χ, ?_, ?_, ?_, min (2 * (t * R)) (Real.pi / Real.sqrt K),
      lt_min (mul_pos (by norm_num) htR.1)
        (div_pos Real.pi_pos (Real.sqrt_pos.mpr hK)), ?_⟩
    · change (extChartAt I c).symm (e (A 0)) = p
      rw [heA0]
    · exact (heA0 ▸ hi).comp 0 (contMDiffAt_iff_contDiffAt.mpr heA)
    · exact normalized_normal_chart_derivative_inner c hz ht.ne' hez hderiv0
    · intro u r hr
      have hh := (hrays (S u) r hr).symm
      have he : (r / (t * R)) • (S u : TM p) = (r / t) • (u : TM p) := by
        change (r / (t * R)) • (R • (u : TM p)) = _
        rw [smul_smul]
        congr 1
        field_simp
      rw [he] at hh
      change Φ (u, r) = (extChartAt I c).symm (e (A (r • (u : TM p))))
      have hA : A (r • (u : TM p)) = L ((r / t) • (u : TM p)) := by
        simp [A, map_smul, smul_smul, div_eq_mul_inv, mul_comm]
      rw [hA]
      exact hh
  · intro q
    exact hQ (S q.1, q.2)
  · intro u r hr
    exact ((hcurves _ (hregular (S u))).2.1 r hr).1
  · intro u
    exact (hcurves _ (hregular (S u))).1
  intro u r hr
  have hone : (1 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.2 (le_top : (1 : ℕ∞) ≤ ⊤)
  have hΓ : MDifferentiableAt 𝓘(ℝ, TM p × ℝ) I Γ (R • (u : TM p), r) :=
    mdifferentiableAt_normal_radial_joint hf.continuous (hη.of_le hone) c L
      ((hsmooth _ (hsource (S u))).differentiableAt (by norm_num))
      (htarget _ (hsource (S u))) (hregular (S u)) hr
  let A : TM p × ℝ →L[ℝ] TM p × ℝ :=
    (R • ContinuousLinearMap.id ℝ (TM p)).prodMap (ContinuousLinearMap.id ℝ ℝ)
  have hA : MDifferentiableAt 𝓘(ℝ, TM p × ℝ) 𝓘(ℝ, TM p × ℝ) A (u, r) :=
    mdifferentiableAt_iff_differentiableAt.mpr A.differentiableAt
  refine ⟨hΓ.comp (f := (A : TM p × ℝ → TM p × ℝ)) (g := Γ) (u, r) hA, ?_⟩
  intro w v hw hv s τ
  have hwR : inner ℝ (S u : TM p) (R • w) = 0 := by
    change inner ℝ (R • (u : TM p)) (R • w) = 0
    simp only [real_inner_smul_left, real_inner_smul_right, hw, mul_zero]
  have hvR : inner ℝ (S u : TM p) (R • v) = 0 := by
    change inner ℝ (R • (u : TM p)) (R • v) = 0
    simp only [real_inner_smul_left, real_inner_smul_right, hv, mul_zero]
  exact polar_metric_rescale_unit hR.ne' s τ hΓ
    (hmetric (S u) (R • w) (R • v) hwR hvR r hr s τ)

end LichnerowiczObata
