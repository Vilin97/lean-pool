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

public import LeanPool.PoincareGeometry.AlmostSchur.LeviCivitaRegularityTwo
public import LeanPool.PoincareGeometry.AlmostSchur.CurvatureVendor.ContractedBianchiBridge

/-! # The attributed double-contraction core for the constructed LC

All compatibility, torsion, and C² connection premises are discharged for the
constructed connection. This module does not rename the double sum as a Ricci
divergence or as the scalar-curvature differential.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff BigOperators
namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 3 E (TangentSpace I : M → Type _)]
local notation "TM" => (TangentSpace I : M → Type _)

/-- The native compatibility predicate implies the explicitly stated metric
Leibniz predicate retained by the attributed curvature core. -/
theorem tangentMetricCompatible_to_curvatureVendor
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) :
    cov.IsMetricCompatibleTangentAlmostSchur := by
  intro x σ τ hσ hτ u
  have h := CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq hm
    (FiberBundle.extend E u) hσ hτ
  simpa using h

local instance manifoldMinTwo : IsManifold I (minSmoothness ℝ 2) M :=
  IsManifold.of_le (n := ∞) (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
local instance manifoldMinThree : IsManifold I (minSmoothness ℝ 3) M :=
  IsManifold.of_le (n := ∞) (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
local instance manifoldMinFour : IsManifold I (minSmoothness ℝ 4) M :=
  IsManifold.of_le (n := ∞) (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
local instance manifoldTwoAddOne : IsManifold I ((2 : ℕ∞) + 1) M :=
  IsManifold.of_le (n := ∞) (by exact_mod_cast (le_top : (2 + 1 : ℕ∞) ≤ ⊤))
local instance manifoldThreeAddOne : IsManifold I ((3 : ℕ∞) + 1) M :=
  IsManifold.of_le (n := ∞) (by exact_mod_cast (le_top : (3 + 1 : ℕ∞) ≤ ⊤))

/-- Double contraction of the actual corrected curvature derivative of our
constructed LC, with no assumed connection regularity or geometric identities. -/
theorem leviCivita_curvatureDerivative_doubleContraction
    (x : M) {ι : Type*} [Fintype ι] (e : ι → TM x) (w : TM x) :
    let cov := leviCivitaConnection (I := I) (M := M)
    (∑ i, ∑ k, cov.curvatureCovariantDerivativeInnerAlmostSchur x w (e k) (e i) (e i) (e k)) =
      2 * ∑ i, ∑ k,
        cov.curvatureCovariantDerivativeInnerAlmostSchur x (e i) (e k) (e i) w (e k) := by
  exact CovariantDerivative.curvatureCovariantDerivativeInner_doubleContractionAlmostSchur
    (leviCivitaConnection (I := I) (M := M)) x leviCivitaConnection_torsion
    (tangentMetricCompatible_to_curvatureVendor _ leviCivitaConnection_metricCompatible) e w

end AlmostSchur
