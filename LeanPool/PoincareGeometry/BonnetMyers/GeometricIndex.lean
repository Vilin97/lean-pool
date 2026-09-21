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

import LeanPool.PoincareGeometry.BonnetMyers.GeometricComparison
import LeanPool.PoincareGeometry.BonnetMyers.CurvatureRegularity

/-!
# The summed geometric sine-index estimate

`GeometricComparison` supplies a pointwise Ricci lower bound for the
curvature coefficients of one transported frame.  This file performs the
remaining integral algebra for the actual tangent-bundle sine fields.  The
integrability premise is explicit: establishing it from the smooth curvature
tensor is a separate regularity obligation, and no second-variation
nonnegativity is asserted here.
-/

noncomputable section

open Bundle Manifold Set Filter
open MeasureTheory
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

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)] in
/-- Integrating the pointwise Ricci comparison after multiplication by the
nonnegative Dirichlet sine square.  The right hand side is already separated
into the individual transported directions, ready for the index-form sum. -/
theorem weighted_transverse_curvature_integral_lower_bound
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (R : Π x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x)
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀} {t₀ : ℝ}
    {b : OrthonormalBasis (Fin (Module.finrank ℝ (TM (curve γ t₀)))) ℝ
      (TM (curve γ t₀))}
    (p : ∀ i, GlobalParallelField (I := I) (M := M) γ t₀ (b i))
    {K L : ℝ} (hn : 2 ≤ Module.finrank ℝ (TM (curve γ t₀)))
    (hcurv : ∀ s,
      ((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) * K ≤
        Finset.sum
          (Finset.univ.erase (⟨0, by omega⟩ :
            Fin (Module.finrank ℝ (TM (curve γ t₀)))))
          (fun i ↦ (p i).curvatureCoefficient R s))
    (hL : 0 ≤ L)
    (hintegrable : ∀ i ∈ Finset.univ.erase (⟨0, by omega⟩ :
      Fin (Module.finrank ℝ (TM (curve γ t₀)))),
      IntervalIntegrable
        (fun s ↦ sineTest L s ^ 2 * (p i).curvatureCoefficient R s)
        volume 0 L) :
    ((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) * K *
        (∫ s in (0 : ℝ)..L, sineTest L s ^ 2) ≤
      Finset.sum
        (Finset.univ.erase (⟨0, by omega⟩ :
          Fin (Module.finrank ℝ (TM (curve γ t₀)))))
        (fun i ↦ ∫ s in (0 : ℝ)..L,
          sineTest L s ^ 2 * (p i).curvatureCoefficient R s) := by
  classical
  let S : Finset (Fin (Module.finrank ℝ (TM (curve γ t₀)))) :=
    Finset.univ.erase ⟨0, by omega⟩
  have hsine_continuous : Continuous (fun s : ℝ ↦ sineTest L s ^ 2) := by
    rw [continuous_iff_continuousAt]
    intro s
    exact (hasDerivAt_sineTest L s).continuousAt.pow 2
  have hsine : IntervalIntegrable (fun s : ℝ ↦ sineTest L s ^ 2)
      volume 0 L :=
    hsine_continuous.intervalIntegrable 0 L
  have hsum : IntervalIntegrable
      (fun s ↦ Finset.sum S
        (fun i ↦ sineTest L s ^ 2 * (p i).curvatureCoefficient R s))
      volume 0 L := by
    have hsum' := IntervalIntegrable.sum S (fun i hi ↦
      hintegrable i (by simpa [S] using hi))
    simpa only [Finset.sum_fn] using hsum'
  have hweighted : IntervalIntegrable
      (fun s ↦ sineTest L s ^ 2 *
        Finset.sum S (fun i ↦ (p i).curvatureCoefficient R s)) volume 0 L := by
    convert hsum using 1
    funext s
    rw [Finset.mul_sum]
  have hpointwise : ∀ s ∈ Icc (0 : ℝ) L,
      ((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) * K *
          sineTest L s ^ 2 ≤
        sineTest L s ^ 2 *
          Finset.sum S (fun i ↦ (p i).curvatureCoefficient R s) := by
    intro s hs
    calc
      ((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) * K *
          sineTest L s ^ 2 =
          sineTest L s ^ 2 *
            (((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) * K) := by
              ring
      _ ≤ sineTest L s ^ 2 *
          Finset.sum S (fun i ↦ (p i).curvatureCoefficient R s) :=
        mul_le_mul_of_nonneg_left (hcurv s) (sq_nonneg _)
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hL
    (hsine.const_mul
      (((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) * K))
    hweighted hpointwise
  have hmono' :
      ((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) * K *
          (∫ s in (0 : ℝ)..L, sineTest L s ^ 2) ≤
        ∫ s in (0 : ℝ)..L, sineTest L s ^ 2 *
          Finset.sum S (fun i ↦ (p i).curvatureCoefficient R s) := by
    simpa only [intervalIntegral.integral_const_mul] using hmono
  have hswap :
      (∫ s in (0 : ℝ)..L, sineTest L s ^ 2 *
          Finset.sum S (fun i ↦ (p i).curvatureCoefficient R s)) =
        Finset.sum S (fun i ↦ ∫ s in (0 : ℝ)..L,
          sineTest L s ^ 2 * (p i).curvatureCoefficient R s) := by
    calc
      (∫ s in (0 : ℝ)..L, sineTest L s ^ 2 *
          Finset.sum S (fun i ↦ (p i).curvatureCoefficient R s)) =
          ∫ s in (0 : ℝ)..L,
            Finset.sum S (fun i ↦ sineTest L s ^ 2 *
              (p i).curvatureCoefficient R s) := by
            apply intervalIntegral.integral_congr
            intro s hs
            change sineTest L s ^ 2 *
                Finset.sum S (fun i ↦ (p i).curvatureCoefficient R s) =
              Finset.sum S (fun i ↦ sineTest L s ^ 2 *
                (p i).curvatureCoefficient R s)
            rw [Finset.mul_sum]
      _ = Finset.sum S (fun i ↦ ∫ s in (0 : ℝ)..L,
          sineTest L s ^ 2 * (p i).curvatureCoefficient R s) :=
        intervalIntegral.integral_finsetSum (fun i hi ↦
          hintegrable i (by simpa [S] using hi))
  simpa [S] using hmono'.trans_eq hswap

/-- Summing the actual tangent-bundle sine index forms gives at most the
classical scalar sine index form multiplied by the number of transverse
directions.  This is an integral comparison only; second-variation
nonnegativity remains a separate theorem to establish from minimization. -/
theorem sum_globalIndexForm_sineTest_le
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (R : Π x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x)
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀} {t₀ : ℝ}
    {b : OrthonormalBasis (Fin (Module.finrank ℝ (TM (curve γ t₀)))) ℝ
      (TM (curve γ t₀))}
    (p : ∀ i, GlobalParallelField (I := I) (M := M) γ t₀ (b i))
    (hmetric : cov.IsMetricCompatibleTangent)
    {K L : ℝ} (hn : 2 ≤ Module.finrank ℝ (TM (curve γ t₀)))
    (hcurv : ∀ s,
      ((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) * K ≤
        Finset.sum
          (Finset.univ.erase (⟨0, by omega⟩ :
            Fin (Module.finrank ℝ (TM (curve γ t₀)))))
          (fun i ↦ (p i).curvatureCoefficient R s))
    (hL : 0 < L)
    (hintegrable : ∀ i ∈ Finset.univ.erase (⟨0, by omega⟩ :
      Fin (Module.finrank ℝ (TM (curve γ t₀)))),
      IntervalIntegrable
        (fun s ↦ sineTest L s ^ 2 * (p i).curvatureCoefficient R s)
        volume 0 L) :
    Finset.sum
      (Finset.univ.erase (⟨0, by omega⟩ :
        Fin (Module.finrank ℝ (TM (curve γ t₀)))))
      (fun i ↦ globalIndexForm R γ t₀ ((p i).sineTestField L)
        ((p i).sineTestDerivativeField L) L) ≤
      ((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) *
        sineIndexForm K L := by
  classical
  let S : Finset (Fin (Module.finrank ℝ (TM (curve γ t₀)))) :=
    Finset.univ.erase ⟨0, by omega⟩
  let D : ℝ := ∫ s in (0 : ℝ)..L, sineTestDeriv L s ^ 2
  let A : ℝ := ∫ s in (0 : ℝ)..L, sineTest L s ^ 2
  let C : Fin (Module.finrank ℝ (TM (curve γ t₀))) → ℝ := fun i ↦
    ∫ s in (0 : ℝ)..L, sineTest L s ^ 2 *
      (p i).curvatureCoefficient R s
  have hweight :
      ((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) * K * A ≤
        Finset.sum S C := by
    simpa [A, C, S] using
      weighted_transverse_curvature_integral_lower_bound
        (I := I) (M := M) R p hn hcurv hL.le hintegrable
  have hindex : ∀ i,
      globalIndexForm R γ t₀ ((p i).sineTestField L)
          ((p i).sineTestDerivativeField L) L = D - C i := by
    intro i
    simpa [D, C] using
      globalIndexForm_sineTest_eq (I := I) (M := M) R (p i) hmetric
        (b.norm_eq_one i) L
  have hcard : (S.card : ℝ) =
      ((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) := by
    simp [S]
  have hsumD : Finset.sum S (fun _i ↦ D) =
      ((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) * D := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
  change Finset.sum S (fun i ↦ globalIndexForm R γ t₀ ((p i).sineTestField L)
      ((p i).sineTestDerivativeField L) L) ≤ _
  calc
    Finset.sum S (fun i ↦ globalIndexForm R γ t₀ ((p i).sineTestField L)
        ((p i).sineTestDerivativeField L) L) =
        Finset.sum S (fun i ↦ D - C i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hindex i
    _ = Finset.sum S (fun _i ↦ D) - Finset.sum S C :=
      Finset.sum_sub_distrib (fun _i : Fin (Module.finrank ℝ (TM (curve γ t₀))) ↦ D) C
    _ = ((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) * D -
          Finset.sum S C := by rw [hsumD]
    _ ≤ ((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) * D -
          (((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) * K * A) :=
      sub_le_sub_left hweight _
    _ = ((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) *
          sineIndexForm K L := by
      simp only [sineIndexForm, D, A]
      ring

/-- For the actual curvature tensor, the regularity hypothesis in the generic
index estimate is discharged by `CurvatureRegularity`.  Thus this is the
geometric sine-index comparison with no separately assumed integrability. -/
theorem sum_globalIndexForm_sineTest_le_curvature
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀} {t₀ : ℝ}
    {b : OrthonormalBasis (Fin (Module.finrank ℝ (TM (curve γ t₀)))) ℝ
      (TM (curve γ t₀))}
    (p : ∀ i, GlobalParallelField (I := I) (M := M) γ t₀ (b i))
    (hmetric : cov.IsMetricCompatibleTangent)
    {K L : ℝ} (hn : 2 ≤ Module.finrank ℝ (TM (curve γ t₀)))
    (hcurv : ∀ s,
      ((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) * K ≤
        Finset.sum
          (Finset.univ.erase (⟨0, by omega⟩ :
            Fin (Module.finrank ℝ (TM (curve γ t₀)))))
          (fun i ↦ (p i).curvatureCoefficient
            (curvature (I := I) (M := M) cov) s))
    (hL : 0 < L) :
    Finset.sum
      (Finset.univ.erase (⟨0, by omega⟩ :
        Fin (Module.finrank ℝ (TM (curve γ t₀)))))
      (fun i ↦ globalIndexForm (curvature (I := I) (M := M) cov) γ t₀
        ((p i).sineTestField L) ((p i).sineTestDerivativeField L) L) ≤
      ((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) *
        sineIndexForm K L := by
  exact sum_globalIndexForm_sineTest_le (I := I) (M := M)
    (curvature (I := I) (M := M) cov) p hmetric hn hcurv hL
    (fun i _ ↦
      (p i).intervalIntegrable_sineTest_square_mul_curvatureCoefficient_curvature
        L 0 L)

/-- The actual tangent-bundle sine fields rule out a long unit-speed segment
once their genuine geometric index forms are known to be nonnegative.  The
only remaining premise of this theorem is precisely the second-variation
nonnegativity statement for an endpoint-minimizing smooth geodesic; neither
minimization nor a variation theorem is concealed in the proof. -/
theorem no_long_global_geodesic_of_sine_index_nonnegative
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (R : Π x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x)
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀} {t₀ : ℝ}
    {b : OrthonormalBasis (Fin (Module.finrank ℝ (TM (curve γ t₀)))) ℝ
      (TM (curve γ t₀))}
    (p : ∀ i, GlobalParallelField (I := I) (M := M) γ t₀ (b i))
    (hmetric : cov.IsMetricCompatibleTangent)
    {K L : ℝ} (hn : 2 ≤ Module.finrank ℝ (TM (curve γ t₀)))
    (hK : 0 < K) (hL : Real.pi / Real.sqrt K < L)
    (hcurv : ∀ s,
      ((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) * K ≤
        Finset.sum
          (Finset.univ.erase (⟨0, by omega⟩ :
            Fin (Module.finrank ℝ (TM (curve γ t₀)))))
          (fun i ↦ (p i).curvatureCoefficient R s))
    (hintegrable : ∀ i ∈ Finset.univ.erase (⟨0, by omega⟩ :
      Fin (Module.finrank ℝ (TM (curve γ t₀)))),
      IntervalIntegrable
        (fun s ↦ sineTest L s ^ 2 * (p i).curvatureCoefficient R s)
        volume 0 L)
    (hmin : ∀ i ∈ Finset.univ.erase (⟨0, by omega⟩ :
      Fin (Module.finrank ℝ (TM (curve γ t₀)))),
      0 ≤ globalIndexForm R γ t₀ ((p i).sineTestField L)
        ((p i).sineTestDerivativeField L) L) :
    False := by
  classical
  let S : Finset (Fin (Module.finrank ℝ (TM (curve γ t₀)))) :=
    Finset.univ.erase ⟨0, by omega⟩
  have hsum_nonneg : 0 ≤ Finset.sum S (fun i ↦
      globalIndexForm R γ t₀ ((p i).sineTestField L)
        ((p i).sineTestDerivativeField L) L) := by
    apply Finset.sum_nonneg
    intro i hi
    exact hmin i (by simpa [S] using hi)
  have hsum_le : Finset.sum S (fun i ↦
      globalIndexForm R γ t₀ ((p i).sineTestField L)
        ((p i).sineTestDerivativeField L) L) ≤
      ((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) *
        sineIndexForm K L := by
    simpa [S] using sum_globalIndexForm_sineTest_le
      (I := I) (M := M) R p hmetric hn hcurv
        (lt_trans (div_pos Real.pi_pos (Real.sqrt_pos.2 hK)) hL) hintegrable
  have hfactor_pos : 0 <
      ((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) := by
    have hnat : 1 ≤ Module.finrank ℝ (TM (curve γ t₀)) - 1 := by omega
    exact_mod_cast hnat
  have hright_neg :
      ((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) *
        sineIndexForm K L < 0 :=
    mul_neg_of_pos_of_neg hfactor_pos (sineIndexForm_negative hK hL)
  linarith

/-- The long-segment contradiction for the actual curvature tensor needs no
independent curvature-integrability premise.  Its remaining nonnegativity
premise is exactly the still-separate second-variation bridge. -/
theorem no_long_global_geodesic_of_sine_index_nonnegative_curvature
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀} {t₀ : ℝ}
    {b : OrthonormalBasis (Fin (Module.finrank ℝ (TM (curve γ t₀)))) ℝ
      (TM (curve γ t₀))}
    (p : ∀ i, GlobalParallelField (I := I) (M := M) γ t₀ (b i))
    (hmetric : cov.IsMetricCompatibleTangent)
    {K L : ℝ} (hn : 2 ≤ Module.finrank ℝ (TM (curve γ t₀)))
    (hK : 0 < K) (hL : Real.pi / Real.sqrt K < L)
    (hcurv : ∀ s,
      ((Module.finrank ℝ (TM (curve γ t₀)) - 1 : ℕ) : ℝ) * K ≤
        Finset.sum
          (Finset.univ.erase (⟨0, by omega⟩ :
            Fin (Module.finrank ℝ (TM (curve γ t₀)))))
          (fun i ↦ (p i).curvatureCoefficient
            (curvature (I := I) (M := M) cov) s))
    (hmin : ∀ i ∈ Finset.univ.erase (⟨0, by omega⟩ :
      Fin (Module.finrank ℝ (TM (curve γ t₀)))),
      0 ≤ globalIndexForm (curvature (I := I) (M := M) cov) γ t₀
        ((p i).sineTestField L) ((p i).sineTestDerivativeField L) L) :
    False := by
  exact no_long_global_geodesic_of_sine_index_nonnegative
    (I := I) (M := M) (curvature (I := I) (M := M) cov) p hmetric
    hn hK hL hcurv
    (fun i _ ↦
      (p i).intervalIntegrable_sineTest_square_mul_curvatureCoefficient_curvature
        L 0 L)
    hmin

/-- This is the full Ricci-to-index contradiction along one genuine global
geodesic.  The Ricci trace is converted to the fixed transported frame and
actual-curvature regularity supplies integrability; only the endpoint-
minimizing second-variation nonnegativity remains as an input. -/
theorem no_long_global_geodesic_of_ricci_and_sine_index_nonnegative
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀} {t₀ : ℝ}
    {b : OrthonormalBasis (Fin (Module.finrank ℝ (TM (curve γ t₀)))) ℝ
      (TM (curve γ t₀))}
    (p : ∀ i, GlobalParallelField (I := I) (M := M) γ t₀ (b i))
    (horth : ∀ s, Orthonormal ℝ (fun i ↦ (p i).field s))
    {K L : ℝ} (hn : 2 ≤ Module.finrank ℝ (TM (curve γ t₀)))
    (hvelocity : ∀ s, (p ⟨0, by omega⟩).field s =
      velocity (shift γ t₀) s)
    (hmetric : cov.IsMetricCompatibleTangent)
    (hunit : ‖velocity γ t₀‖ = 1)
    (hK : 0 < K) (hL : Real.pi / Real.sqrt K < L)
    (hRic : ∀ (x : M) (a : TM x),
      (((Module.finrank ℝ (TM x) : ℝ) - 1) * K) * inner ℝ a a ≤
        LinearMap.trace ℝ (TM x)
          (curvatureEndomorphism
            (R := curvature (I := I) (M := M) cov) x a))
    (hmin : ∀ i ∈ Finset.univ.erase (⟨0, by omega⟩ :
      Fin (Module.finrank ℝ (TM (curve γ t₀)))),
      0 ≤ globalIndexForm (curvature (I := I) (M := M) cov) γ t₀
        ((p i).sineTestField L) ((p i).sineTestDerivativeField L) L) :
    False := by
  apply no_long_global_geodesic_of_sine_index_nonnegative_curvature
    (I := I) (M := M) p hmetric hn hK hL
  · intro s
    exact global_parallelFrame_transverse_curvature_sum_lower_bound_curvature
      (I := I) (M := M) p horth hn hvelocity hmetric hunit hRic s
  · exact hmin

end IntrinsicGeodesic.GlobalGeodesic

end BonnetMyersEntry
