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

public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataUnitSphericalProduct
public import LeanPool.PoincareGeometry.LichnerowiczObata.RoundAmbientDirections
public import LeanPool.PoincareGeometry.LichnerowiczObata.IntrinsicRoundInverse
public import LeanPool.PoincareGeometry.LichnerowiczObata.PolarMetricNondegeneracy
public import LeanPool.PoincareGeometry.LichnerowiczObata.RoundPoleLog

/-! # The regular Obata-to-round comparison and its polar pullback metric -/

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

/-- A single regular comparison homeomorphism intertwines the constructed
Obata coordinates and the explicit round coordinates. Their pullback metrics
agree on every angular tangent and radial direction. Its inverse has a
differentiable ambient extension. Smoothness of the forward comparison and
extension over the poles are separate remaining steps. -/
theorem exists_obata_regular_round_comparison
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (v w : TM y),
      hessian (leviCivitaConnection (I := I)) f y v w = -K * f y * inner ℝ v w)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : ∀ x, f x = a ↔ x = (extChartAt I c).symm z) :
    let p := (extChartAt I c).symm z
    let Ψ := fun q : TM p × ℝ => roundPolarCurve (1 / Real.sqrt K)
      roundNorth (roundAngularInclusion q.1) q.2
    ∃ Φ : TM p × ℝ → M,
      HasRadialPoleModel I Φ p ∧
      ∃ Q : Metric.sphere (0 : TM p) 1 × Ioo 0 (Real.pi / Real.sqrt K) ≃ₜ
          {x : M // -a < f x ∧ f x < a},
        ∃ F : {x : M // -a < f x ∧ f x < a} ≃ₜ
            RoundPuncturedSphere (1 / Real.sqrt K) (roundNorth : RoundAmbient (TM p)),
        ∃ G : RoundAmbient (TM p) → M,
          (∀ x : RoundPuncturedSphere (1 / Real.sqrt K) (roundNorth : RoundAmbient (TM p)),
            G (x.1 : RoundAmbient (TM p)) = (F.symm x : M) ∧
            MDifferentiableAt 𝓘(ℝ, RoundAmbient (TM p)) I G (x.1 : RoundAmbient (TM p))) ∧
          (∀ q, (Q q : M) = Φ (q.1, q.2)) ∧
          (∀ u : Metric.sphere (0 : TM p) 1, ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
            obataRadial K a f (Φ (u, r)) = r) ∧
          (∀ u : Metric.sphere (0 : TM p) 1,
            IsMIntegralCurveOn (fun r => Φ (u, r)) (gradient (I := I) (obataRadial K a f))
              (Ioo 0 (Real.pi / Real.sqrt K))) ∧
          (∀ q, ((F (Q q)).1 : RoundAmbient (TM p)) = Ψ (q.1, q.2)) ∧
          ∀ u : Metric.sphere (0 : TM p) 1, ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
            MDifferentiableAt 𝓘(ℝ, TM p × ℝ) I Φ (u, r) ∧
            Set.InjOn (mfderiv 𝓘(ℝ, TM p × ℝ) I Φ (u, r))
              {q : TM p × ℝ | inner ℝ (u : TM p) q.1 = 0} ∧
            ∀ w v : TM p, inner ℝ (u : TM p) w = 0 → inner ℝ (u : TM p) v = 0 →
              ∀ s t : ℝ,
                inner ℝ (mfderiv 𝓘(ℝ, TM p × ℝ) I Φ (u, r) (w, s))
                  (mfderiv 𝓘(ℝ, TM p × ℝ) I Φ (u, r) (v, t)) =
                inner ℝ (fderiv ℝ Ψ (u, r) (w, s)) (fderiv ℝ Ψ (u, r) (v, t)) := by
  obtain ⟨Φ, hpole, Q, hQ, hradial, hcurves, hmetric⟩ :=
    exists_obata_unit_spherical_product hf hnon hK ha hH c hz hcrit hmax
  let F := Q.symm.trans (curvatureRoundPolarHomeomorph hK)
  let G := Φ ∘ intrinsicRoundInverseCoordinates (1 / Real.sqrt K)
  refine ⟨Φ, hpole, Q, F, G, ?_, hQ, hradial, hcurves, ?_, ?_⟩
  · intro x
    let q := (curvatureRoundPolarHomeomorph hK).symm x
    have hi := intrinsicRoundInverseCoordinates_eq_inverse hK x
    have hΦ := (hmetric q.1 q.2 q.2.property).1
    have hD := (contDiffAt_intrinsicRoundInverseCoordinates hK x).differentiableAt (by norm_num)
    have hΦ' : MDifferentiableAt 𝓘(ℝ, TM ((extChartAt I c).symm z) × ℝ) I Φ
        (intrinsicRoundInverseCoordinates (1 / Real.sqrt K)
          (x.1 : RoundAmbient (TM ((extChartAt I c).symm z)))) := by
      rw [hi]
      exact hΦ
    refine ⟨?_, hΦ'.comp (x.1 : RoundAmbient (TM ((extChartAt I c).symm z)))
      (mdifferentiableAt_iff_differentiableAt.mpr hD)⟩
    change Φ (intrinsicRoundInverseCoordinates (1 / Real.sqrt K)
      (x.1 : RoundAmbient (TM ((extChartAt I c).symm z)))) = (Q q : M)
    rw [hi]
    exact (hQ q).symm
  · intro q
    change (((curvatureRoundPolarHomeomorph hK) (Q.symm (Q q))).1 :
      RoundAmbient (TM ((extChartAt I c).symm z))) = _
    rw [Q.symm_apply_apply]
    exact curvatureRoundPolarHomeomorph_apply hK q
  intro u r hr
  refine ⟨(hmetric u r hr).1, ?_, ?_⟩
  · apply polar_derivative_injOn _ (obata_polar_coefficient_pos hK hr)
    intro v hv t
    exact (hmetric u r hr).2 v v hv hv t t
  intro w v hw hv s t
  rw [(hmetric u r hr).2 w v hw hv s t]
  exact (intrinsicRoundPolar_metric hK (u : TM ((extChartAt I c).symm z)) w v
    (mem_sphere_zero_iff_norm.mp u.property) hw hv r s t).symm

/-- The constructed regular comparison has a differentiable ambient inverse
at its north pole. Agreement holds for every punctured-sphere point of
sufficiently small radial coordinate, not only alongAlmostSchur an individual ray. -/
theorem exists_obata_regular_round_north_extension
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (v w : TM y),
      hessian (leviCivitaConnection (I := I)) f y v w = -K * f y * inner ℝ v w)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : ∀ x, f x = a ↔ x = (extChartAt I c).symm z) :
    let p := (extChartAt I c).symm z
    ∃ F : {x : M // -a < f x ∧ f x < a} ≃ₜ
        RoundPuncturedSphere (1 / Real.sqrt K) (roundNorth : RoundAmbient (TM p)),
      ∃ N : RoundAmbient (TM p) → M,
        N ((1 / Real.sqrt K) • roundNorth) = p ∧
        ContMDiffAt 𝓘(ℝ, RoundAmbient (TM p)) I ∞ N ((1 / Real.sqrt K) • roundNorth) ∧
        ∃ δ : ℝ, 0 < δ ∧
          ∀ x : RoundPuncturedSphere (1 / Real.sqrt K) (roundNorth : RoundAmbient (TM p)),
            (intrinsicRoundInverseCoordinates (1 / Real.sqrt K) (x.1 : RoundAmbient (TM p))).2 < δ →
              N (x.1 : RoundAmbient (TM p)) = (F.symm x : M) := by
  obtain ⟨Φ, hpole, Q, F, G, hG, hQ, hradial, hcurves, hF, hjet⟩ :=
    exists_obata_regular_round_comparison hf hnon hK ha hH c hz hcrit hmax
  let : FiniteDimensional ℝ (TM ((extChartAt I c).symm z)) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let : CompleteSpace (TM ((extChartAt I c).symm z)) := FiniteDimensional.complete ℝ _
  obtain ⟨N, hN0, hNd, hNm, δ, hδ, hN⟩ := hpole.exists_round_north_extension
    (one_div_pos.mpr (Real.sqrt_pos.mpr hK))
  refine ⟨F, N, hN0, hNd, δ, hδ, ?_⟩
  intro x hx
  let q := Q.symm (F.symm x)
  have hpoint : (x.1 : RoundAmbient (TM ((extChartAt I c).symm z))) =
      roundPolarCurve (1 / Real.sqrt K) roundNorth
        (roundAngularInclusion (q.1 : TM ((extChartAt I c).symm z))) q.2 := by
    simpa only [q, Homeomorph.apply_symm_apply] using hF q
  have hround : ((curvatureRoundPolarHomeomorph hK q).1 :
      RoundAmbient (TM ((extChartAt I c).symm z))) = (x.1 : RoundAmbient _) :=
    (curvatureRoundPolarHomeomorph_apply hK q).trans hpoint.symm
  have hcoords := intrinsicRoundInverseCoordinates_apply hK q
  rw [hround] at hcoords
  have hrδ : (q.2 : ℝ) < δ := by
    have hh : (intrinsicRoundInverseCoordinates (1 / Real.sqrt K)
        (x.1 : RoundAmbient (TM ((extChartAt I c).symm z)))).2 = (q.2 : ℝ) :=
      congrArg Prod.snd hcoords
    rw [← hh]
    exact hx
  rw [hpoint]
  have hh := (hN q.1 q.2 ⟨q.2.property.1, hrδ⟩).trans (hQ q).symm
  simpa only [q, Homeomorph.apply_symm_apply] using hh

end LichnerowiczObata
