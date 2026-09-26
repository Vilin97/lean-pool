/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Geometry.ProjectiveBoundaryFrameRank
public import LeanPool.Stafford38.Stafford38.Geometry.ArcFrameConormal
public import LeanPool.Stafford38.Stafford38.Geometry.JacobianConormalComparison


/-!
# The exact completed-chart to arc-frame adapter boundary

The completed projective certificate canonically supplies an affine
power-series arc after deleting its normalized chart coordinate.  Its
dehomogenized first jet is exactly the uniformizer member of
`residueFrameVector`.

The remaining projective residue columns cannot be interpreted as
coefficient-field derivations over the field stored in the certificate: every
`k`-derivation of `k` is zero, whereas those columns are independent.  Thus a
smaller base field and geometric residue-field derivations are genuinely new
data, not consequences of `CompletedProjectiveBoundaryChart`.

For the separate closed-tangent obligation, independent Jacobian rows from
the actual boundary ideal give the sharp annihilator-dimension formula and
therefore the finrank bound consumed by `ArcFrameConormal`.  This regularity
criterion concerns the closed point directly; no generic-rank specialization
is used.
-/

@[expose] public section

namespace Stafford38.Geometry.AsymptoticChartArcAdapter

open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.ArcFrameConormal
open Stafford38.Geometry.CanonicalAsymptoticLaurentProducer
open Stafford38.Geometry.ContinuousPowerSeriesTangentFrame
open Stafford38.Geometry.JacobianConormalComparison
open Stafford38.Geometry.ProjectiveBoundaryFrameRank
open Stafford38.GeometryRetractionSpecialization

noncomputable section

universe u v

variable {k : Type u} [Field k]

/-! ## The canonical affine arc and its first jet -/

/-- The complement of one coordinate in `Fin (m+1)` has `m` elements. -/
def chartAffineCoordinateEquiv {m : ℕ} (chart : Fin (m + 1)) :
    Fin m ≃ ChartAffineIndex (Fin (m + 1)) chart := by
  classical
  apply (Fintype.equivFinOfCardEq (α := ChartAffineIndex (Fin (m + 1)) chart) ?_).symm
  rw [Fintype.card_subtype_compl]
  simp

/-- Affine power-series coordinates obtained by deleting the normalized
projective chart coordinate.  Since that coordinate is exactly one, no
power-series division is needed. -/
def completedChartAffineArc [CharZero k]
    {m : ℕ} (hm : 0 < m) (I : Ideal (MvPolynomial (Fin m) k))
    (W : CompletedProjectiveBoundaryChart k m hm I) :
    Fin m → PowerSeries k :=
  fun i ↦ W.q ((chartAffineCoordinateEquiv W.chart i).1)

/-- The first coefficient of every projective power-series coordinate. -/
def projectiveFirstJet {ι : Type v} (q : ι → PowerSeries k) : ι → k :=
  fun i ↦ PowerSeries.coeff 1 (q i)

/-- The actual uniformizer residue vector of the affine chart arc is exactly
the dehomogenized projective first jet. -/
theorem completedChart_uniformizerResidueFrame_eq_dehomogenizedFirstJet
    [CharZero k] {m r : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k))
    (W : CompletedProjectiveBoundaryChart k m hm I)
    (D : Fin r → Derivation k k k) (i : Fin m) :
    residueFrameVector (completedChartAffineArc hm I W) D none i =
      chartDehomogenizedTangentColumn W.chart
        (residueColumn W.q) (projectiveFirstJet W.q)
        (chartAffineCoordinateEquiv W.chart i) := by
  simp [completedChartAffineArc, chartDehomogenizedTangentColumn,
    projectiveFirstJet, residueColumn, W.q_chart]

/-! ## Why the remaining columns are not a self-relative arc frame -/

/-- Every derivation of a field relative to itself is zero. -/
theorem selfDerivation_apply_eq_zero (D : Derivation k k k) (a : k) :
    D a = 0 := by
  simpa using D.map_algebraMap a

/-- Consequently every coefficient member of a `k/k` residue frame is the
zero tangent vector. -/
theorem residueFrameVector_coefficient_self_eq_zero
    {m : ℕ} (q : Fin m → PowerSeries k)
    {κ : Type v} (D : κ → Derivation k k k) (j : κ) :
    residueFrameVector q D (some j) = 0 := by
  funext i
  rw [residueFrameVector_coefficient]
  exact selfDerivation_apply_eq_zero (D j) _

/-- If the completed chart has at least one divisor-tangent column, its
independent projective residue frame cannot equal a coefficient-derivation
frame over `k/k`, even after the canonical affine-coordinate reindexing. -/
theorem completedChart_no_selfRelative_fullResidueFrameIdentification
    [CharZero k] {m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k))
    (W : CompletedProjectiveBoundaryChart k m hm I)
    (hpositive : 0 < W.tangentCount) :
    ¬ ∃ (q : Fin m → PowerSeries k)
        (D : Fin W.tangentCount → Derivation k k k),
      ∀ (j : Fin W.tangentCount) (i : Fin m),
        residueFrameVector q D (some j) i =
          chartDehomogenizedTangentColumn W.chart
            (residueColumn W.q)
            (fun a ↦ PowerSeries.constantCoeff
              (nonpositionPowerSeriesMatrix W.Z W.tau a (Sum.inl j)))
            (chartAffineCoordinateEquiv W.chart i) := by
  rintro ⟨q, D, hidentify⟩
  let j : Fin W.tangentCount := ⟨0, hpositive⟩
  have hprojective :=
    (completedBoundaryChart_residueFrame_linearIndependent hm I W).ne_zero
      (Sum.inl j)
  apply hprojective
  funext a
  let i : Fin m := (chartAffineCoordinateEquiv W.chart).symm a
  have hz := congrFun (residueFrameVector_coefficient_self_eq_zero q D j) i
  have hid := hidentify j i
  have hres : residueColumn W.q = fun i ↦ PowerSeries.constantCoeff (W.q i) := rfl
  simpa [i, hres, Equiv.apply_symm_apply] using hid.symm.trans hz

/-! ## Closed-boundary Jacobian regularity -/

/-- Independent Jacobian rows have the expected common-kernel dimension. -/
theorem finrank_jacobianTangentSpace_eq_sub_of_linearIndependent
    {n : ℕ} {ι : Type v} [Fintype ι]
    (y : Fin n → k) (equations : ι → MvPolynomial (Fin n) k)
    (hindependent :
      LinearIndependent k (fun i ↦ differentialCovector y (equations i))) :
    Module.finrank k (jacobianTangentSpace y equations) =
      n - Fintype.card ι := by
  have hspan : Module.finrank k (jacobianCovectorSpan y equations) =
      Fintype.card ι := by
    exact finrank_span_eq_card hindependent
  have hdimension :=
    Subspace.finrank_add_finrank_dualCoannihilator_eq
      (jacobianCovectorSpan y equations)
  rw [hspan, Module.finrank_pi, Fintype.card_fin] at hdimension
  rw [jacobianTangentSpace]
  omega

/-- Independent differentials of equations belonging to `I` give a sharp
upper bound on the equation-defined closed tangent space. -/
theorem zariskiTangent_finrank_le_sub_of_independentEquations
    {n : ℕ} {ι : Type v} [Fintype ι]
    (y : Fin n → k) (I : Ideal (MvPolynomial (Fin n) k))
    (equations : ι → MvPolynomial (Fin n) k)
    (hequations : ∀ i, equations i ∈ I)
    (hindependent :
      LinearIndependent k (fun i ↦ differentialCovector y (equations i))) :
    Module.finrank k (zariskiTangentSpace y I) ≤
      n - Fintype.card ι := by
  have hcovectors :
      jacobianCovectorSpan y equations ≤ equationCovectorSpan y I :=
    jacobianCovectorSpan_le_equationCovectorSpan y I equations hequations
  have htangent : zariskiTangentSpace y I ≤
      jacobianTangentSpace y equations := by
    exact Submodule.dualCoannihilator_anti hcovectors
  calc
    Module.finrank k (zariskiTangentSpace y I) ≤
        Module.finrank k (jacobianTangentSpace y equations) :=
      Submodule.finrank_mono htangent
    _ = n - Fintype.card ι :=
      finrank_jacobianTangentSpace_eq_sub_of_linearIndependent
        y equations hindependent

/-- Cardinal form matching the `ArcFrameConormal` consumer: enough
independent closed-point Jacobian equations discharge its finrank input. -/
theorem zariskiTangent_finrank_le_frameCard_of_independentEquations
    {n frameCount : ℕ} {ι : Type v} [Fintype ι]
    (y : Fin n → k) (I : Ideal (MvPolynomial (Fin n) k))
    (equations : ι → MvPolynomial (Fin n) k)
    (hequations : ∀ i, equations i ∈ I)
    (hindependent :
      LinearIndependent k (fun i ↦ differentialCovector y (equations i)))
    (hcodimension : n ≤ Fintype.card ι + frameCount) :
    Module.finrank k (zariskiTangentSpace y I) ≤ frameCount := by
  have hbound := zariskiTangent_finrank_le_sub_of_independentEquations
    y I equations hequations hindependent
  omega

/-- An annihilating arc with an independent residue frame spans the closed
tangent space once enough independent boundary Jacobian equations are
exhibited.  The finrank premise of `ArcFrameConormal` is now a conclusion. -/
theorem tangent_le_span_residueFrame_of_independentBoundaryEquations
    {K : Type u} [Field K] [Algebra k K]
    {m : ℕ} {κ : Type v} [Fintype κ]
    {ι : Type v} [Fintype ι]
    (I : Ideal (MvPolynomial (Fin m) k))
    (q : Fin m → PowerSeries K)
    (D : κ → Derivation k K K)
    (equations : ι → MvPolynomial (Fin m) K)
    (hequations : ∀ i,
      equations i ∈ I.map (MvPolynomial.map (algebraMap k K)))
    (hjacobian : LinearIndependent K (fun i ↦
      differentialCovector
        (fun a ↦ PowerSeries.constantCoeff (q a)) (equations i)))
    (hcodimension :
      m ≤ Fintype.card ι + Fintype.card (FrameIndex κ))
    (hq : ∀ f ∈ I,
      MvPolynomial.eval₂ (algebraMap k (PowerSeries K)) q f = 0)
    (hframe : LinearIndependent K (residueFrameVector q D)) :
    zariskiTangentSpace
        (fun i ↦ PowerSeries.constantCoeff (q i))
        (I.map (MvPolynomial.map (algebraMap k K))) ≤
      Submodule.span K (Set.range (residueFrameVector q D)) := by
  apply tangent_le_span_residueFrame_of_annihilatingArc I q D hq hframe
  exact zariskiTangent_finrank_le_frameCard_of_independentEquations
    _ _ equations hequations hjacobian hcodimension


end

end Stafford38.Geometry.AsymptoticChartArcAdapter
