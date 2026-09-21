/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.CanonicalSupportVanishingReduction
import LeanPool.Stafford38.Stafford38.Geometry.ProjectiveDivisorOrderGap
import LeanPool.Stafford38.Stafford38.Geometry.ProjectiveEquationFormalChart
import LeanPool.Stafford38.Stafford38.Geometry.ProjectiveTangentInclusion

/-!
# The completed-boundary consumer for the Laurent producer

This file isolates the exact local certificate consumed by the asymptotic
Laurent step.  A certificate contains

* a one-parameter completed projective chart `q`;
* a finite homogeneous family of projective equations, with their vanishing
  at `q` and containment of the target affine ideal after dehomogenization;
* divisor-tangent columns `Z` and the strict projective order-gap data;
* one fixed derivative-compatible geometric witness `tau`, `C`, `ell`; and
* the one genuinely geometric comparison still needed by the consumer:
  the Zariski tangent space is *contained* in the span built from that same
  fixed transverse column `tau`.

The main theorem below turns this certificate into the exact output required
by `CanonicalAsymptoticLaurentProducer`.  It does not assume support
vanishing, a finite affine point on the axis, tangent-space equality, or a
heuristic derivative limit.  The certificate is therefore a non-circular
consumer interface, not a disguised proof of its own existence.

What is deliberately not asserted here is the global production theorem that
constructs such a certificate from normalization and projective closure.  In
particular, a DVR with residue field `K` naturally completes to `K[[X]]`;
specializing that chart to `k[[X]]`, constructing homogeneous equations, and
proving the tangent-span inclusion are separate geometric obligations.
`CanonicalBoundaryChartProduction` records exactly that remaining obligation.
-/

namespace Stafford38.Geometry.CanonicalAsymptoticLaurentProducer

open Stafford38
open Stafford38.CanonicalSupportVanishingReduction
open Stafford38.Characteristic
open Stafford38.CharacteristicInitialIdeal
open Stafford38.Characteristic.ReducedSupportIdeal
open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.FormalDivisorLaurentConormal
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.ProjectiveDivisorOrderGap
open Stafford38.Geometry.ProjectiveEquationFormalChart
open Stafford38.Geometry.ProjectiveTangentInclusion
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.GeometrySplitTangentMatrix
open Stafford38.GeometryFormalDivisorTangent
open Stafford38.GeometryPowerSeriesTangentLimit
open Stafford38.GeometryRetractionSpecialization
open Stafford38.WeylEulerResidue
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge

noncomputable section

universe u

/-! ## The exact local certificate -/

/--
A completed one-parameter projective boundary chart for an affine ideal in
`m` variables.

The finite equation and tangent-column indices are natural numbers so that
the certificate is entirely first-order data over the pinned Lean library;
no hidden finiteness or choice of an equation family is left to an
elaboration-side typeclass.

The formal tangent data are one fixed geometric witness.  In particular,
`tangent_inclusion` refers to the stored derivative-compatible transverse
column `tau`; it does not quantify over alternative, possibly nongeometric,
split columns.  The inclusion remains intentionally one-sided: it asks for
the actual Zariski tangent space to lie in the supplied span and never assumes
equality.
-/
structure CompletedProjectiveBoundaryChart
    (k : Type u) [Field k] [CharZero k]
    (m : ℕ) (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k)) where
  /-- The number of homogeneous equations in the completed projective boundary chart. -/
  equationCount : ℕ
  /-- The number of tangent columns in the completed projective boundary chart. -/
  tangentCount : ℕ
  /-- Homogeneous Laurent-series equations vanishing on the formal boundary arc. -/
  equations : Fin equationCount →
    MvPolynomial (Fin (m + 1)) (LaurentSeries k)
  /-- The homogeneous degree of each completed-chart equation. -/
  degree : Fin equationCount → ℕ
  homogeneous : ∀ j, (equations j).IsHomogeneous (degree j)
  /-- Power-series homogeneous coordinates of the formal projective arc. -/
  q : Fin (m + 1) → PowerSeries k
  /-- The power-series tangent columns in the chosen affine projective chart. -/
  Z : Matrix (Fin (m + 1)) (Fin tangentCount) (PowerSeries k)
  /-- Rows selecting a tangent minor with nonzero determinant after taking residues. -/
  rows : Fin tangentCount ↪ Fin (m + 1)
  /-- The projective coordinate normalized to one along the arc. -/
  chart : Fin (m + 1)
  /-- The nonzero boundary coordinate whose constant coefficient vanishes. -/
  zero : Fin (m + 1)
  /-- The first fibre coordinate used for the limiting conormal direction. -/
  axis : Fin (m + 1)
  /-- The nonzero vanishing ratio relating the fibre coordinate to the boundary coordinate. -/
  ratio : PowerSeries k
  q_chart : q chart = 1
  Z_chart : ∀ j, Z chart j = 0
  q_zero_ne : q zero ≠ 0
  q_origin_ne : q 0 ≠ 0
  ratio_ne : ratio ≠ 0
  q_zero_vanish : PowerSeries.constantCoeff (q zero) = 0
  ratio_vanish : PowerSeries.constantCoeff ratio = 0
  q_axis : q axis = q zero * ratio
  Z_zero_dvd : ∀ j, q zero ∣ Z zero j
  Z_axis_dvd : ∀ j, q axis ∣ Z axis j
  selected_minor_nonzero :
    PowerSeries.constantCoeff
      (selectedMinor Z rows).det ≠ 0
  equations_vanish :
    ∀ j, MvPolynomial.eval (laurentColumn q) (equations j) = 0
  ideal_containment :
    I.map (scalarPolynomialMap
      (k := k) (K := LaurentSeries k) (Fin m)) ≤
      dehomogenizedEquationIdeal equations
  axis_is_first_fibre : axis = Fin.succ ⟨0, hm⟩
  /-- The additional column completing the formal tangent matrix. -/
  tau : Fin (m + 1) → PowerSeries k
  /-- A left inverse of the completed formal tangent matrix. -/
  C : Matrix (FormalTangentColumn (Fin tangentCount))
    (Fin (m + 1)) (PowerSeries k)
  /-- A formal annihilating covector whose residue is the specified fibre axis. -/
  ell : Fin (m + 1) → PowerSeries k
  left_inverse : C * formalTangentMatrix q Z tau = 1
  annihilation : rowMul ell (formalTangentMatrix q Z tau) = 0
  residue_axis : residueColumn ell = axisRow (k := k) axis
  tangent_inclusion :
    zariskiTangentSpace (dehomogenizedPoint (laurentColumn q))
        (I.map (scalarPolynomialMap
          (k := k) (K := LaurentSeries k) (Fin m))) ≤
      dehomogenizedTangentSpan (laurentColumn q)
        (laurentNonpositionTangentMatrix Z tau)

/-! ## Local consumer theorem -/

/--
The completed-DVR/projective certificate supplies the Laurent conormal axis.

The proof has four explicit interfaces: the projective order-gap theorem
constructs the formal annihilating row; homogeneous equation vanishing gives
the base-equation condition after dehomogenization; tangent inclusion feeds
the weaker Laurent conormal bridge; and the axis equation identifies the
regular fibre residue with the pure first momentum direction.
-/
theorem exists_conormalAxis_of_completedProjectiveBoundaryChart
    {k : Type u} [Field k] [CharZero k]
    {m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k))
    (W : CompletedProjectiveBoundaryChart k m hm I) :
    ∃ (y : Fin m → LaurentSeries k)
      (xi : Fin m → PowerSeries k),
      Sum.elim y
          (fun i ↦ algebraMap (PowerSeries k) (LaurentSeries k) (xi i)) ∈
        equationConormalLocus
          (I.map (scalarPolynomialMap
            (k := k) (K := LaurentSeries k) (Fin m))) ∧
      residueColumn xi =
        (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0) := by
  classical
  let Iext := I.map (scalarPolynomialMap
    (k := k) (K := LaurentSeries k) (Fin m))
  have hbase : ∀ f ∈ Iext,
      MvPolynomial.eval (dehomogenizedPoint (laurentColumn W.q)) f = 0 := by
    intro f hf
    exact eval_eq_zero_of_mem_dehomogenizedEquationIdeal
      W.equations W.degree W.homogeneous (laurentColumn W.q)
      (laurentColumn_ne_zero_of_ne_zero W.q W.q_origin_ne)
      W.equations_vanish f (W.ideal_containment hf)
  have htangent :
      zariskiTangentSpace (dehomogenizedPoint (laurentColumn W.q)) Iext ≤
        dehomogenizedTangentSpan (laurentColumn W.q)
          (laurentNonpositionTangentMatrix W.Z W.tau) := by
    exact W.tangent_inclusion
  have hphase :=
    laurentPhasePoint_mem_equationConormalLocus_of_zariski_le_span
      Iext W.q W.ell W.Z W.tau W.q_origin_ne W.annihilation hbase htangent
  refine ⟨dehomogenizedPoint (laurentColumn W.q),
    (fun i : Fin m ↦ W.ell i.succ), ?_, ?_⟩
  · simpa [Iext, laurentColumn] using hphase
  · calc
      residueColumn (fun i : Fin m ↦ W.ell i.succ) =
          (fun i : Fin m ↦ residueColumn W.ell i.succ) :=
        residueColumn_tail W.ell
      _ = (fun i : Fin m ↦ axisRow (k := k) W.axis i.succ) := by
        rw [W.residue_axis]
      _ = (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0) := by
        funext i
        rw [W.axis_is_first_fibre]
        by_cases hi : i = ⟨0, hm⟩
        · subst i
          simp [axisRow]
        · have hne : i.succ ≠ Fin.succ ⟨0, hm⟩ := by
            intro h
            exact hi (Fin.succ_injective m h)
          change (if i.succ = Fin.succ ⟨0, hm⟩ then 1 else 0) =
            (if i = ⟨0, hm⟩ then 1 else 0)
          rw [ite_eq_right hne, ite_eq_right hi]

/-! ## The remaining global production obligation -/

/--
The exact global theorem still needed to obtain the producer from boundary
geometry.  It asks normalization/projective-closure arguments to return the
certificate above for the canonical reduced base ideal, but it does not put
the desired support-vanishing conclusion among the certificate fields.

This is a definition rather than an axiom.  Consequently a caller must still
prove the actual completion, homogeneous-equation, and tangent-inclusion
construction; the adapter theorem above cannot discharge those obligations
by circular reasoning.
-/
def CanonicalBoundaryChartProduction : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    (n N : ℕ)
    (d : PresentedWeyl k (n + 1)),
    0 < N →
    IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d →
    Disjoint
      (orderCharacteristicSupport k
        (canonicalRightIdeal (presentedCoordinate k n) d N))
      (PrimeSpectrum.zeroLocus
        ({MvPolynomial.X (.inl (0 : Fin (n + 1)))} :
          Set (SymbolRing k (n + 1)))) →
    (orderCharacteristicSupport k
      (canonicalRightIdeal (presentedCoordinate k n) d N)).Nonempty →
    Nonempty (CompletedProjectiveBoundaryChart k (n + 1) (Nat.zero_lt_succ n)
      (reducedOrderBaseIdeal k
        (canonicalRightIdeal (presentedCoordinate k n) d N)))

/--
The exact adapter from global boundary-chart production to the canonical
Laurent producer.  All support hypotheses are used only to request a chart;
the chart-to-conormal proof itself has no support-vanishing premise.
-/
theorem canonicalAsymptoticLaurentProducer_of_boundaryChartProduction
    (hproduction : CanonicalBoundaryChartProduction.{u}) :
    CanonicalAsymptoticLaurentProducer.{u} := by
  intro k _ _ _ n N d hN hd hdisjoint hnonempty
  obtain ⟨W⟩ :=
    hproduction k n N d hN hd hdisjoint hnonempty
  obtain ⟨y, xi, hmem, haxis⟩ :=
    exists_conormalAxis_of_completedProjectiveBoundaryChart
      (k := k) (m := n + 1) (Nat.zero_lt_succ n)
      (reducedOrderBaseIdeal k
        (canonicalRightIdeal (presentedCoordinate k n) d N)) W
  exact ⟨y, xi, hmem, haxis⟩


end

end Stafford38.Geometry.CanonicalAsymptoticLaurentProducer
