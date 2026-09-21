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

import LeanPool.PoincareGeometry.BonnetMyers.TwoPointGaussLemma
import LeanPool.PoincareGeometry.BonnetMyers.CornerRigidity

/-!
# Uniform corner rigidity from two-point connector energy

The strong two-point endpoint equivalence supplies one smooth family of
connectors while both endpoints vary in a fixed neighbourhood.  Its energy
is an upper support for half squared distance.  Along an exact-distance
outgoing curve, the endpoint first variation therefore forces equality in
Cauchy--Schwarz and positive tangent alignment.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology RealInnerProductSpace

namespace BonnetMyersEntry.LocalGeodesicData

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [PseudoMetricSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

variable [RiemannianBundle (TangentSpace I : M → Type u)]

/-- If a right-going coordinate curve increases distance from the initial
endpoint at its full tangent speed, then it is positively aligned with the
terminal velocity of the two-point connector arriving at its base point. -/
theorem twoPointConnector_sameDirection_of_exactDistanceCurve_right
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hmetric : cov.IsMetricCompatibleTangent) (htorsion : cov.torsion = 0)
    (G : E × E → E × E) (Φ : (E × E) → ℝ → E × E)
    (R : OpenPartialHomeomorph (E × E) (E × E))
    (hG : ContDiff ℝ 1 G) (hGcompact : HasCompactSupport G)
    (hΦzero : ∀ q, Φ q 0 = q)
    (hΦcurve : ∀ q, IsIntegralCurve (Φ q) (fun _ : ℝ ↦ G))
    (hΦsmooth : ContDiff ℝ 1 (fun q ↦ Φ q 1))
    (hR : ∀ s, R s = (s.1, (Φ s 1).1))
    (hinverseSmooth : ∀ y ∈ R.target, ContDiffAt ℝ 1 R.symm y)
    (hactual : ∀ s ∈ R.source, ∀ t ∈ Icc (-2 : ℝ) 2,
      (Φ s t).1 ∈ (extChartAt I x₀).target ∧
        G (Φ s t) =
          secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ s t) ∧
        G =ᶠ[𝓝 (Φ s t)]
          (fun r ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) r))
    (hframe : ∀ s ∈ R.source, ∀ t ∈ Icc (-1 : ℝ) 1,
      ∀ j : Fin (Module.finrank ℝ E),
        smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
          𝓝 ((extChartAt I x₀).symm (Φ s t).1)]
          (trivializationAt E TM x₀).localFrame b j)
    (hedist : ∀ a c : M,
      riemannianEDist I a c = ENNReal.ofReal (dist a c))
    {p q : E} (hpq : (p, q) ∈ R.target)
    (c : ℝ → E) (ξ : E) (hc : HasDerivAt c ξ 0) (hc0 : c 0 = q)
    (hctarget : ∀ t ∈ Icc (0 : ℝ) 1, (p, c t) ∈ R.target)
    (hdistance : ∀ t ∈ Icc (0 : ℝ) 1,
      dist ((extChartAt I x₀).symm p) ((extChartAt I x₀).symm (c t)) =
        dist ((extChartAt I x₀).symm p) ((extChartAt I x₀).symm q) +
          t * ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            ξ ((extChartAt I x₀).symm q)‖)
    (hincomingDistance :
      dist ((extChartAt I x₀).symm p) ((extChartAt I x₀).symm q) =
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (Φ (R.symm (p, q)) 1).2 ((extChartAt I x₀).symm q)‖) :
    let T := coordinateFrameCombination
      (I := I) (M := M) (x₀ := x₀) b
        (Φ (R.symm (p, q)) 1).2 ((extChartAt I x₀).symm q)
    let Kξ := coordinateFrameCombination
      (I := I) (M := M) (x₀ := x₀) b ξ ((extChartAt I x₀).symm q)
    ‖Kξ‖ • T = ‖T‖ • Kξ := by
  let e : E → ℝ := twoPointConnectorEnergy
    (I := I) (M := M) x₀ b R p
  let D : E →L[ℝ] ℝ := fderiv ℝ e q
  let T : TM ((extChartAt I x₀).symm q) := coordinateFrameCombination
    (I := I) (M := M) (x₀ := x₀) b
      (Φ (R.symm (p, q)) 1).2 ((extChartAt I x₀).symm q)
  let K : E →L[ℝ] TM ((extChartAt I x₀).symm q) :=
    (IntrinsicAcceleration.coordinateFrameLinear
      (I := I) (M := M) x₀ b ((extChartAt I x₀).symm q)).toContinuousLinearMap
  dsimp only
  obtain ⟨heSmooth, heFormula⟩ :=
    twoPointConnectorEnergy_contDiffAt_and_fderiv_apply
      (I := I) (M := M) cov x₀ b hmetric htorsion G Φ R hG hGcompact
        hΦzero hΦcurve hΦsmooth hR hinverseSmooth hactual hframe hpq
  have he : HasFDerivAt e D q :=
    heSmooth.differentiableAt one_ne_zero |>.hasFDerivAt
  have hformula : D ξ = inner ℝ T (K ξ) := by
    rw [show D ξ = fderiv ℝ e q ξ by rfl, heFormula ξ]
    rfl
  have heq : e q = (1 / 2 : ℝ) * ‖T‖ ^ 2 := by
    exact twoPointConnectorEnergy_eq_half_terminal_speed_sq
      (I := I) (M := M) cov x₀ b hmetric G Φ R hG hGcompact
        hΦzero hΦcurve hR hactual hframe hpq
  have hsupport : (fun t : ℝ ↦
      (1 / 2 : ℝ) * (‖T‖ + t * ‖K ξ‖) ^ 2) ≤ᶠ[𝓝[Ici (0 : ℝ)] 0]
        (fun t ↦ e (c t)) := by
    have hlt : Iio (1 : ℝ) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (by norm_num)
    have hltWithin : Iio (1 : ℝ) ∈ 𝓝[Ici (0 : ℝ)] 0 :=
      Filter.Eventually.filter_mono inf_le_left hlt
    filter_upwards [hltWithin, self_mem_nhdsWithin] with t ht ht0
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht0, ht.le⟩
    have hbound := half_dist_sq_le_twoPointConnectorEnergy
      (I := I) (M := M) cov x₀ b hmetric G Φ R hΦzero hΦcurve hR
        hactual hframe hedist (hctarget t htI)
    rw [hdistance t htI, hincomingDistance] at hbound
    exact hbound
  have halign := sameDirection_of_energy_firstVariation_right
    e D c K q ξ T he hc hc0 hformula hsupport heq
  have hKξ : K ξ = coordinateFrameCombination
      (I := I) (M := M) (x₀ := x₀) b ξ ((extChartAt I x₀).symm q) := rfl
  simpa only [T, hKξ] using halign

/-- Chart-independent corner form.  If an outgoing smooth curve realizes the
prefix and suffix distances of an exact metric corner and remains inside the
uniform two-point target, then its initial tangent is positively aligned with
the arriving connector velocity. -/
theorem twoPointConnector_sameDirection_of_exactMetricCorner
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hmetric : cov.IsMetricCompatibleTangent) (htorsion : cov.torsion = 0)
    (G : E × E → E × E) (Φ : (E × E) → ℝ → E × E)
    (R : OpenPartialHomeomorph (E × E) (E × E))
    (hG : ContDiff ℝ 1 G) (hGcompact : HasCompactSupport G)
    (hΦzero : ∀ q, Φ q 0 = q)
    (hΦcurve : ∀ q, IsIntegralCurve (Φ q) (fun _ : ℝ ↦ G))
    (hΦsmooth : ContDiff ℝ 1 (fun q ↦ Φ q 1))
    (hR : ∀ s, R s = (s.1, (Φ s 1).1))
    (hinverseSmooth : ∀ y ∈ R.target, ContDiffAt ℝ 1 R.symm y)
    (hactual : ∀ s ∈ R.source, ∀ t ∈ Icc (-2 : ℝ) 2,
      (Φ s t).1 ∈ (extChartAt I x₀).target ∧
        G (Φ s t) =
          secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ s t) ∧
        G =ᶠ[𝓝 (Φ s t)]
          (fun r ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) r))
    (hframe : ∀ s ∈ R.source, ∀ t ∈ Icc (-1 : ℝ) 1,
      ∀ j : Fin (Module.finrank ℝ E),
        smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
          𝓝 ((extChartAt I x₀).symm (Φ s t).1)]
          (trivializationAt E TM x₀).localFrame b j)
    (hedist : ∀ a c : M,
      riemannianEDist I a c = ENNReal.ofReal (dist a c))
    {p q : E} (hpq : (p, q) ∈ R.target)
    {d : M} (β : ℝ → M) (v : TM ((extChartAt I x₀).symm q))
    (hβderiv : HasMFDerivAt (𝓘(ℝ, ℝ)) I β 0
      (CurveConnection.timeTangentMap (I := I) 0 v))
    (hβ0 : β 0 = (extChartAt I x₀).symm q)
    (hβ1 : β 1 = d)
    (hchain : dist ((extChartAt I x₀).symm p) d =
      dist ((extChartAt I x₀).symm p) ((extChartAt I x₀).symm q) +
        dist ((extChartAt I x₀).symm q) d)
    {C : ℝ} (hqd : dist ((extChartAt I x₀).symm q) d = C)
    (hCnorm : C = ‖v‖)
    (hsub : ∀ t ∈ Ioo (0 : ℝ) 1,
      dist ((extChartAt I x₀).symm q) (β t) = C * t ∧
      dist (β t) d = C * (1 - t))
    (hβsource : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ (extChartAt I x₀).source)
    (hβtarget : ∀ t ∈ Icc (0 : ℝ) 1,
      (p, extChartAt I x₀ (β t)) ∈ R.target)
    (hincomingDistance :
      dist ((extChartAt I x₀).symm p) ((extChartAt I x₀).symm q) =
        ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (Φ (R.symm (p, q)) 1).2 ((extChartAt I x₀).symm q)‖) :
    let T := coordinateFrameCombination
      (I := I) (M := M) (x₀ := x₀) b
        (Φ (R.symm (p, q)) 1).2 ((extChartAt I x₀).symm q)
    ‖v‖ • T = ‖T‖ • v := by
  dsimp only
  have hqTarget : q ∈ (extChartAt I x₀).target := by
    let s : E × E := R.symm (p, q)
    have hs : s ∈ R.source := R.map_target hpq
    have hr := R.right_inv hpq
    rw [hR] at hr
    have hsq : (Φ s 1).1 = q := congrArg Prod.snd hr
    rw [← hsq]
    exact (hactual s hs 1 (by constructor <;> norm_num)).1
  have hsourceQ : (extChartAt I x₀).symm q ∈ (extChartAt I x₀).source := by
    rw [← hβ0]
    exact hβsource 0 (by constructor <;> norm_num)
  obtain ⟨ξ, hc, hξ⟩ :=
    CurveConnection.exists_chart_hasDerivAt_coordinateFrameCombination_eq
      (I := I) (M := M) x₀ b β hβderiv
        (hβsource 0 (by constructor <;> norm_num))
  rw [hβ0] at hξ
  let c : ℝ → E := fun t ↦ extChartAt I x₀ (β t)
  have hc0 : c 0 = q := by
    dsimp only [c]
    rw [hβ0, (extChartAt I x₀).right_inv hqTarget]
  have hdistanceRaw := distance_along_exact_metric_tail hβ0 hβ1 hchain hqd hsub
  have hdistance : ∀ t ∈ Icc (0 : ℝ) 1,
      dist ((extChartAt I x₀).symm p) ((extChartAt I x₀).symm (c t)) =
        dist ((extChartAt I x₀).symm p) ((extChartAt I x₀).symm q) +
          t * ‖coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
            ξ ((extChartAt I x₀).symm q)‖ := by
    intro t ht
    have hleft : (extChartAt I x₀).symm (c t) = β t := by
      exact (extChartAt I x₀).left_inv (hβsource t ht)
    rw [hleft, hdistanceRaw t ht, hCnorm, ← hξ]
    ring
  have halign := twoPointConnector_sameDirection_of_exactDistanceCurve_right
    (I := I) (M := M) cov x₀ b hmetric htorsion G Φ R hG hGcompact
      hΦzero hΦcurve hΦsmooth hR hinverseSmooth hactual hframe hedist hpq
      c ξ (by simpa only [c] using hc) hc0
      (fun t ht ↦ hβtarget t ht) hdistance hincomingDistance
  rw [hξ] at halign
  exact halign

end BonnetMyersEntry.LocalGeodesicData
