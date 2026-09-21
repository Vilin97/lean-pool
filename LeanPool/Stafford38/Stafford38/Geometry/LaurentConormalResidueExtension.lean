/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Geometry.LaurentConormalDirection
import LeanPool.Stafford38.Stafford38.Geometry.ProjectiveDivisorOrderGap
import LeanPool.Stafford38.Stafford38.Geometry.ProjectiveEquationFormalChart
import LeanPool.Stafford38.Stafford38.Geometry.ProjectiveTangentInclusion

/-!
# Laurent conormal specialization over a residue-field extension

The residue field of a divisorial valuation need not be the original ground
field.  This file separates the two coefficient roles which are easy to
confuse in that situation:

* `k` is the field of coefficients of the original equations and symbol;
* `K` is the residue field of the boundary valuation, and the completed
  coordinates live in `PowerSeries K` and `LaurentSeries K`.

Ground coefficients are sent to Laurent series by the displayed composite
`k -> K -> LaurentSeries K`.  The fibre closure itself is taken over `K`.
The resulting contradiction uses only field and algebra-tower structure; in
particular it does not require `K` to be algebraically closed and does not
choose a map `K -> k`.

The final structure and consumer are a residue-extension version of the
completed-boundary local interface.  They construct no projective chart,
normalization, divisor, or tangent comparison.
-/

namespace Stafford38.Geometry.LaurentConormalResidueExtension

open Stafford38
open Stafford38.Characteristic
open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.LaurentConormalDirection
open Stafford38.Geometry.ProjectiveConormalDehomogenization
open Stafford38.Geometry.ProjectiveDivisorOrderGap
open Stafford38.Geometry.ProjectiveEquationFormalChart
open Stafford38.Geometry.ProjectiveTangentInclusion
open Stafford38.GeometryPowerSeriesTangentLimit
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.GeometryRetractionSpecialization
open Stafford38.GeometryFormalDivisorTangent
open Stafford38.GeometrySplitTangentMatrix
open Stafford38.Geometry.FormalDivisorLaurentConormal

noncomputable section

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {n : ℕ}

/-! ## The coefficient tower -/

/-- The coefficient map used by equations over the ground field after
completion at a boundary with residue field `K`. -/
def groundLaurentMap : k →+* LaurentSeries K :=
  (algebraMap K (LaurentSeries K)).comp (algebraMap k K)

/-- Ground-field polynomials evaluated in the completed residue-field
Laurent series ring. -/
def groundPolynomialMap (σ : Type*) :
    MvPolynomial σ k →+* MvPolynomial σ (LaurentSeries K) :=
  MvPolynomial.map (groundLaurentMap (k := k) (K := K))

/-- The same ground polynomial after first extending its coefficients to the
residue field. -/
def residuePolynomialMap (σ : Type*) :
    MvPolynomial σ k →+* MvPolynomial σ K :=
  MvPolynomial.map (algebraMap k K)

/-- Fibre lift after extending the ground coefficients to `K`. -/
def residueFibreLift (P : MvPolynomial (Fin n) k) :
    MvPolynomial (PhaseVar n) K :=
  fibreLift (residuePolynomialMap (k := k) (K := K) (Fin n) P)

/-- The two routes from a ground-field fibre polynomial to Laurent series
agree exactly: extend to `K` first or map directly along the composite. -/
theorem eval_residueFibreLift_eq_ground
    (P : MvPolynomial (Fin n) k)
    (q : PhaseVar n → LaurentSeries K) :
    MvPolynomial.eval₂ (algebraMap K (LaurentSeries K)) q
        (residueFibreLift (k := k) (K := K) P) =
      MvPolynomial.eval₂ (groundLaurentMap (k := k) (K := K)) q
        (fibreLift P) := by
  change MvPolynomial.eval₂ (algebraMap K (LaurentSeries K)) q
      (MvPolynomial.rename Sum.inr
        (MvPolynomial.map (algebraMap k K) P)) = _
  rw [← MvPolynomial.map_rename]
  rw [MvPolynomial.eval₂_map]
  rfl

/-- Evaluation of a ground polynomial agrees with evaluation of its
coefficient extension along the residue-field-to-Laurent map. -/
theorem eval_residuePolynomialMap_eq_ground
    (P : MvPolynomial (Fin n) k)
    (v : Fin n → LaurentSeries K) :
    MvPolynomial.eval₂ (algebraMap K (LaurentSeries K)) v
        (residuePolynomialMap (k := k) (K := K) (Fin n) P) =
    MvPolynomial.eval₂ (groundLaurentMap (k := k) (K := K)) v P := by
  change MvPolynomial.eval₂ (algebraMap K (LaurentSeries K)) v
      (MvPolynomial.map (algebraMap k K) P) = _
  rw [MvPolynomial.eval₂_map]
  rfl

/-- Fibre-only evaluation ignores the base part of a phase point, also for
the explicit ground-to-Laurent coefficient map. -/
theorem eval_ground_fibreLift
    (P : MvPolynomial (Fin n) k)
    (q : PhaseVar n → LaurentSeries K) :
    MvPolynomial.eval₂ (groundLaurentMap (k := k) (K := K)) q
        (fibreLift P) =
      MvPolynomial.eval₂ (groundLaurentMap (k := k) (K := K))
        (fun i ↦ q (Sum.inr i)) P := by
  rw [fibreLift, MvPolynomial.eval₂_rename]
  rfl

/-! ## Fibre closure over the residue field -/

/-- The projected closure of Laurent-valued phase points, with regular fibre
residue, formed over `K`.  Its base coordinates may have poles. -/
def residueExtensionFibreClosure
    (S : Set (PhaseVar n → LaurentSeries K)) : Set (Fin n → K) :=
  extensionFibreClosure (k := K) (K := LaurentSeries K) S

/-- The existing Laurent-residue theorem, instantiated over the residue field
`K`.  No algebraic-closedness hypothesis occurs. -/
theorem residue_mem_residueExtensionFibreClosure_of_laurent_generic
    (S : Set (PhaseVar n → LaurentSeries K))
    (y : Fin n → LaurentSeries K)
    (xi : Fin n → PowerSeries K)
    (hgeneric :
      Sum.elim y
          (fun i ↦ algebraMap (PowerSeries K) (LaurentSeries K) (xi i)) ∈ S) :
    residueColumn xi ∈ residueExtensionFibreClosure (K := K) S := by
  exact residue_mem_extensionFibreClosure_of_laurent_generic
    (k := K) S y xi hgeneric

/-! ## Ground-field contradiction -/

/-- The scalar-extended equation-conormal locus associated with a ground
ideal.  Its coefficients use the explicit composite `k -> K -> Laurent`. -/
def groundEquationConormalLocus
    (I : Ideal (MvPolynomial (Fin n) k)) :
    Set (PhaseVar n → LaurentSeries K) :=
  equationConormalLocus
    (I.map (groundPolynomialMap (k := k) (K := K) (Fin n)))

/-- A fibre-only ground polynomial which vanishes on the whole completed
equation-conormal locus also vanishes after extending its coefficients to
`K` and evaluating at every regular fibre residue. -/
theorem residueFibreLift_mem_extensionValuedVanishingIdeal_of_ground_vanishing
    (I : Ideal (MvPolynomial (Fin n) k))
    (P : MvPolynomial (Fin n) k)
    (hvanishes :
      ∀ q ∈ groundEquationConormalLocus (k := k) (K := K) I,
        MvPolynomial.eval₂ (groundLaurentMap (k := k) (K := K)) q
          (fibreLift P) = 0) :
    residuePolynomialMap (k := k) (K := K) (Fin n) P ∈
      extensionValuedVanishingIdeal (k := K) (K := LaurentSeries K)
        (fibreImage (groundEquationConormalLocus (k := k) (K := K) I)) := by
  rw [mem_extensionValuedVanishingIdeal_iff]
  intro q hq
  rcases hq with ⟨z, hz, rfl⟩
  rw [eval_residuePolynomialMap_eq_ground]
  rw [← eval_ground_fibreLift]
  exact hvanishes z hz

/-- Exact contradiction consumer for a residue-field-valued boundary arc.

The hypotheses deliberately use the composite coefficient map and an
`eval₂ (algebraMap k K)` axis value.  The theorem requires neither
`IsAlgClosed K` nor a retraction from `K` to `k`. -/
theorem false_of_ground_fibreOnly_symbol_one_on_residue_and_vanishing
    (I : Ideal (MvPolynomial (Fin n) k))
    (P : MvPolynomial (Fin n) k)
    (axis : Fin n → K)
    (y : Fin n → LaurentSeries K)
    (xi : Fin n → PowerSeries K)
    (hgeneric :
      Sum.elim y
          (fun i ↦ algebraMap (PowerSeries K) (LaurentSeries K) (xi i)) ∈
        groundEquationConormalLocus (k := k) (K := K) I)
    (hresidue : residueColumn xi = axis)
    (hvanishes :
      ∀ q ∈ groundEquationConormalLocus (k := k) (K := K) I,
        MvPolynomial.eval₂ (groundLaurentMap (k := k) (K := K)) q
          (fibreLift P) = 0)
    (haxis : MvPolynomial.eval₂ (algebraMap k K) axis P = 1) : False := by
  let S : Set (PhaseVar n → LaurentSeries K) :=
    groundEquationConormalLocus (k := k) (K := K) I
  have hP :
      residuePolynomialMap (k := k) (K := K) (Fin n) P ∈
        extensionValuedVanishingIdeal (k := K) (K := LaurentSeries K)
          (fibreImage S) := by
    exact residueFibreLift_mem_extensionValuedVanishingIdeal_of_ground_vanishing
      (k := k) (K := K) I P (by
        simpa [S] using hvanishes)
  have hclosure :
      residueColumn xi ∈ residueExtensionFibreClosure (K := K) S :=
    residue_mem_residueExtensionFibreClosure_of_laurent_generic
      (K := K) S y xi (by simpa [S] using hgeneric)
  have hzero :
      MvPolynomial.eval (residueColumn xi)
        (residuePolynomialMap (k := k) (K := K) (Fin n) P) = 0 :=
    hclosure _ hP
  have hzero' :
      MvPolynomial.eval₂ (algebraMap k K) (residueColumn xi) P = 0 := by
    simpa [residuePolynomialMap] using hzero
  rw [hresidue, haxis] at hzero'
  exact one_ne_zero hzero'

/-! ## Completed-boundary adapter over `K` -/

/-- A completed projective boundary chart whose residue coefficients are in
`K`, while the target affine ideal remains defined over `k`.  Its formal
tangent data are one fixed derivative-compatible geometric witness.  The
one-sided tangent inclusion uses that same stored transverse column, never an
alternative split column. -/
structure CompletedProjectiveBoundaryChartOver
    (m : ℕ) (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k)) where
  /-- The number of homogeneous equations defining the completed boundary chart. -/
  equationCount : ℕ
  /-- The number of tangent columns in the completed boundary chart. -/
  tangentCount : ℕ
  /-- Homogeneous Laurent-series equations vanishing on the formal projective arc. -/
  equations : Fin equationCount →
    MvPolynomial (Fin (m + 1)) (LaurentSeries K)
  /-- The homogeneous degree of each chart equation. -/
  degree : Fin equationCount → ℕ
  homogeneous : ∀ j, (equations j).IsHomogeneous (degree j)
  /-- Power-series homogeneous coordinates of the formal projective arc. -/
  q : Fin (m + 1) → PowerSeries K
  /-- Power-series tangent columns with zero component in the chosen projective chart. -/
  Z : Matrix (Fin (m + 1)) (Fin tangentCount) (PowerSeries K)
  /-- Rows selecting a tangent minor that remains invertible after taking residues. -/
  rows : Fin tangentCount ↪ Fin (m + 1)
  /-- The projective coordinate normalized to one along the arc. -/
  chart : Fin (m + 1)
  /-- The nonzero coordinate whose residue vanishes at the boundary. -/
  zero : Fin (m + 1)
  /-- The first fibre coordinate, expressed as the boundary coordinate times `ratio`. -/
  axis : Fin (m + 1)
  /-- A nonzero power-series coordinate ratio vanishing at the special point. -/
  ratio : PowerSeries K
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
    PowerSeries.constantCoeff (selectedMinor Z rows).det ≠ 0
  equations_vanish :
    ∀ j, MvPolynomial.eval (laurentColumn q) (equations j) = 0
  ideal_containment :
    I.map (groundPolynomialMap (k := k) (K := K) (Fin m)) ≤
      dehomogenizedEquationIdeal equations
  axis_is_first_fibre : axis = Fin.succ ⟨0, hm⟩
  /-- The additional column completing the formal tangent matrix. -/
  tau : Fin (m + 1) → PowerSeries K
  /-- A left inverse of the completed formal tangent matrix. -/
  C : Matrix (FormalTangentColumn (Fin tangentCount))
    (Fin (m + 1)) (PowerSeries K)
  /-- An annihilating covector whose residue is the specified coordinate axis. -/
  ell : Fin (m + 1) → PowerSeries K
  left_inverse : C * formalTangentMatrix q Z tau = 1
  annihilation : rowMul ell (formalTangentMatrix q Z tau) = 0
  residue_axis : residueColumn ell = axisRow (k := K) axis
  tangent_inclusion :
    zariskiTangentSpace (dehomogenizedPoint (laurentColumn q))
        (I.map (groundPolynomialMap (k := k) (K := K) (Fin m))) ≤
      dehomogenizedTangentSpan (laurentColumn q)
        (laurentNonpositionTangentMatrix Z tau)

/-- The residue-extension completed chart supplies a Laurent equation-
conormal point with pure first fibre residue. -/
theorem exists_conormalAxis_of_completedProjectiveBoundaryChartOver
    {m : ℕ} (hm : 0 < m)
    (I : Ideal (MvPolynomial (Fin m) k))
    (W : CompletedProjectiveBoundaryChartOver (k := k) (K := K) m hm I) :
    ∃ (y : Fin m → LaurentSeries K)
      (xi : Fin m → PowerSeries K),
      Sum.elim y
          (fun i ↦ algebraMap (PowerSeries K) (LaurentSeries K) (xi i)) ∈
        groundEquationConormalLocus (k := k) (K := K) I ∧
      residueColumn xi =
        (fun i : Fin m ↦ if i = ⟨0, hm⟩ then 1 else 0) := by
  classical
  let Iext := I.map (groundPolynomialMap (k := k) (K := K) (Fin m))
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
  · simpa [Iext, groundEquationConormalLocus, laurentColumn] using hphase
  · calc
      residueColumn (fun i : Fin m ↦ W.ell i.succ) =
          (fun i : Fin m ↦ residueColumn W.ell i.succ) :=
        residueColumn_tail W.ell
      _ = (fun i : Fin m ↦ axisRow (k := K) W.axis i.succ) := by
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


end

end Stafford38.Geometry.LaurentConormalResidueExtension
