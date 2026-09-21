/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.GlobalParallelTransport
import LeanPool.PoincareGeometry.BonnetMyers.ManifoldSineTest
import LeanPool.PoincareGeometry.BonnetMyers.Algebra

/-!
# Ricci comparison in a transported global frame

The Ricci hypothesis is a trace inequality at each tangent fibre, whereas the
index-form argument needs the curvature scalars of one coherent transverse
frame along a geodesic.  This module performs that conversion using the actual
global parallel transport equivalence.  No pointwise choice of a new frame is
silently substituted for the fields used in the variation calculation.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology RealInnerProductSpace BigOperators

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

namespace IntrinsicGeodesic.GlobalGeodesic

variable [RiemannianBundle (TangentSpace I : M → Type u)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
  {x₀ : M} {v₀ : TangentSpace I x₀}

/-- A Ricci trace lower bound becomes the corresponding lower bound for the
curvature coefficients of a fixed transported global orthonormal frame. -/
theorem global_parallelFrame_transverse_curvature_sum_lower_bound
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (R : Π x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x)
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ}
    {b : OrthonormalBasis (Fin (Module.finrank ℝ (TM (curve γ t₀)))) ℝ
      (TM (curve γ t₀))}
    (p : ∀ i, GlobalParallelField (I := I) (M := M) γ t₀ (b i))
    (horth : ∀ s, Orthonormal ℝ (fun i ↦ (p i).field s))
    {K : ℝ} (hn : 2 ≤ Module.finrank ℝ (TM (curve γ t₀)))
    (hvelocity : ∀ s, (p ⟨0, by omega⟩).field s =
      velocity (shift γ t₀) s)
    (hmetric : cov.IsMetricCompatibleTangent)
    (hunit : ‖velocity γ t₀‖ = 1)
    (hself : ∀ (x : M) (a : TM x), R x a a a = 0)
    (hRic : ∀ (x : M) (a : TM x),
      (((Module.finrank ℝ (TM x) : ℝ) - 1) * K) * inner ℝ a a ≤
        LinearMap.trace ℝ (TM x) (curvatureEndomorphism (R := R) x a))
    (s : ℝ) :
    ((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) * K ≤
      Finset.sum
        (Finset.univ.erase (⟨0, by omega⟩ :
          Fin (Module.finrank ℝ (TM (curve γ t₀)))))
        (fun i ↦ (p i).curvatureCoefficient R s) := by
  classical
  let i₀ : Fin (Module.finrank ℝ (TM (curve γ t₀))) := ⟨0, by omega⟩
  let a : TM (curve (shift γ t₀) s) := velocity (shift γ t₀) s
  let bs : OrthonormalBasis (Fin (Module.finrank ℝ (TM (curve γ t₀)))) ℝ
      (TM (curve (shift γ t₀) s)) :=
    globalParallelTransportBasis p (horth s)
  have hspeed : ‖a‖ = 1 := by
    dsimp [a]
    change ‖velocity γ (t₀ + s)‖ = 1
    calc
      ‖velocity γ (t₀ + s)‖ = ‖v₀‖ :=
        norm_velocity_eq_initial (I := I) (M := M) γ hmetric (t₀ + s)
      _ = ‖velocity γ t₀‖ :=
        (norm_velocity_eq_initial (I := I) (M := M) γ hmetric t₀).symm
      _ = 1 := hunit
  have hfirst : bs i₀ = a := by
    dsimp [bs, i₀, a]
    exact globalParallelTransportBasis_apply p (horth s) ⟨0, by omega⟩ |>.trans
      (hvelocity s)
  have hkill : curvatureEndomorphism (R := R)
      (curve (shift γ t₀) s) a (bs i₀) = 0 := by
    rw [hfirst, curvatureEndomorphism_apply]
    exact hself _ a
  have htrace : LinearMap.trace ℝ (TM (curve (shift γ t₀) s))
      (curvatureEndomorphism (R := R) (curve (shift γ t₀) s) a) =
      Finset.sum (Finset.univ.erase i₀)
        (fun i ↦ inner ℝ (bs i)
          (R (curve (shift γ t₀) s) (bs i) a a)) :=
    trace_eq_sum_erase_of_orthonormalBasis bs i₀
      (curvatureEndomorphism (R := R) (curve (shift γ t₀) s) a) hkill
  have hinner : inner ℝ a a = 1 := by
    rw [real_inner_self_eq_norm_sq, hspeed]
    norm_num
  have hRic' := hRic (curve (shift γ t₀) s) a
  rw [hinner, mul_one, htrace] at hRic'
  have hdim : Module.finrank ℝ (TM (curve (shift γ t₀) s)) =
      Module.finrank ℝ (TM (curve γ t₀)) :=
    tangent_finrank_eq (I := I) (M := M) (curve (shift γ t₀) s)
      (curve γ t₀)
  rw [hdim] at hRic'
  have hsum :
      Finset.sum (Finset.univ.erase i₀)
        (fun i ↦ inner ℝ (bs i)
          (R (curve (shift γ t₀) s) (bs i) a a)) =
      Finset.sum (Finset.univ.erase i₀)
        (fun i ↦ (p i).curvatureCoefficient R s) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [show bs i = (p i).field s by
      exact globalParallelTransportBasis_apply p (horth s) i]
    rfl
  rw [hsum] at hRic'
  have hcast : (Module.finrank ℝ (TM (curve γ t₀)) : ℝ) - 1 =
      ((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  simpa [hcast] using hRic'

/-- A unit-speed global ODE geodesic admits one two-sided transported frame
whose transverse curvature coefficients satisfy the Ricci lower bound at
every time.  The frame in this conclusion is the same global frame that will
be used for the sine test; it is not chosen afresh pointwise. -/
theorem exists_global_parallelFrame_transverse_curvature_sum_lower_bound
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (R : Π x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x)
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) (t₀ : ℝ)
    (hmetric : cov.IsMetricCompatibleTangent)
    (hunit : ‖velocity γ t₀‖ = 1)
    {K : ℝ} (hn : 2 ≤ Module.finrank ℝ (TM (curve γ t₀)))
    (hself : ∀ (x : M) (a : TM x), R x a a a = 0)
    (hRic : ∀ (x : M) (a : TM x),
      (((Module.finrank ℝ (TM x) : ℝ) - 1) * K) * inner ℝ a a ≤
        LinearMap.trace ℝ (TM x) (curvatureEndomorphism (R := R) x a)) :
    letI : Nonempty (Fin (Module.finrank ℝ (TM (curve γ t₀)))) :=
      ⟨⟨0, by omega⟩⟩
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℝ (TM (curve γ t₀)))) ℝ
          (TM (curve γ t₀)),
      b ⟨0, by omega⟩ = velocity γ t₀ ∧
      ∃ p : ∀ i, GlobalParallelField (I := I) (M := M) γ t₀ (b i),
        (∀ i s, CurveConnection.IsCovariantAccelerationAt cov
          (curve (shift γ t₀)) (p i).field s (velocity (shift γ t₀) s) 0) ∧
        (∀ s, (p ⟨0, by omega⟩).field s = velocity (shift γ t₀) s) ∧
        (∀ s, Orthonormal ℝ (fun i ↦ (p i).field s)) ∧
        (∀ i ∈ Finset.univ.erase (⟨0, by omega⟩ :
          Fin (Module.finrank ℝ (TM (curve γ t₀)))), ∀ s,
          inner ℝ ((p i).field s) (velocity (shift γ t₀) s) = 0) ∧
        (∀ s,
          ((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) * K ≤
            Finset.sum
              (Finset.univ.erase (⟨0, by omega⟩ :
                Fin (Module.finrank ℝ (TM (curve γ t₀)))))
              (fun i ↦ (p i).curvatureCoefficient R s)) := by
  classical
  obtain ⟨b, hb, p, hacc, hvelocity, horth, htransverse⟩ :=
    exists_global_adapted_parallelFrame (I := I) (M := M) γ t₀ hmetric
      hunit (by omega)
  refine ⟨b, hb, p, hacc, hvelocity, horth, htransverse, ?_⟩
  intro s
  exact global_parallelFrame_transverse_curvature_sum_lower_bound
    (I := I) (M := M) R p horth hn hvelocity hmetric hunit hself hRic s

/-- The preceding moving-frame comparison applies directly to the actual
curvature tensor of the local covariant derivative.  Its vanishing in the
geodesic direction is supplied by the proved curvature-tensor identity, not
by an extra hypothesis. -/
theorem global_parallelFrame_transverse_curvature_sum_lower_bound_curvature
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ}
    {b : OrthonormalBasis (Fin (Module.finrank ℝ (TM (curve γ t₀)))) ℝ
      (TM (curve γ t₀))}
    (p : ∀ i, GlobalParallelField (I := I) (M := M) γ t₀ (b i))
    (horth : ∀ s, Orthonormal ℝ (fun i ↦ (p i).field s))
    {K : ℝ} (hn : 2 ≤ Module.finrank ℝ (TM (curve γ t₀)))
    (hvelocity : ∀ s, (p ⟨0, by omega⟩).field s =
      velocity (shift γ t₀) s)
    (hmetric : cov.IsMetricCompatibleTangent)
    (hunit : ‖velocity γ t₀‖ = 1)
    (hRic : ∀ (x : M) (a : TM x),
      (((Module.finrank ℝ (TM x) : ℝ) - 1) * K) * inner ℝ a a ≤
        LinearMap.trace ℝ (TM x)
          (curvatureEndomorphism (R := curvature (I := I) (M := M) cov) x a))
    (s : ℝ) :
    ((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) * K ≤
      Finset.sum
        (Finset.univ.erase (⟨0, by omega⟩ :
          Fin (Module.finrank ℝ (TM (curve γ t₀)))))
        (fun i ↦ (p i).curvatureCoefficient
          (curvature (I := I) (M := M) cov) s) := by
  exact global_parallelFrame_transverse_curvature_sum_lower_bound
    (I := I) (M := M) (curvature (I := I) (M := M) cov) p horth hn
      hvelocity hmetric hunit
      (fun x a ↦ curvature_self (I := I) (M := M) cov x a) hRic s

end IntrinsicGeodesic.GlobalGeodesic

end BonnetMyersEntry
