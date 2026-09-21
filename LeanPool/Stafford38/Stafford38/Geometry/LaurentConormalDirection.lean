/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.LaurentSeries
import LeanPool.Stafford38.Stafford38.Geometry.RetractionSpecialization
import LeanPool.Stafford38.Stafford38.Geometry.ScalarExtensionPoints

/-!
# Laurent specialization of projected conormal directions

A Laurent-valued phase point need not specialize to a finite phase point: its
base coordinates may have poles.  Its fibre coordinates can nevertheless be
regular power series.  This file records exactly the consequence that survives:
the residue of those fibre coordinates belongs to the ground-coefficient
vanishing hull of the projected fibre image.

The construction is then specialized to the scalar-extended
`equationConormalLocus`.  The final theorem is the corresponding direct
polynomial obstruction for a ground-field symbol using only fibre variables.

No full phase-space closure, compatibility of closure with base change,
normalization chart, asymptotic-conormal producer, or Gabber theorem is proved
here.
-/

namespace Stafford38.Geometry.LaurentConormalDirection

open Stafford38.Characteristic
open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.GeometryRetractionSpecialization

noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable {n : ℕ}

/-- Forget the base coordinate of a set of phase points. -/
def fibreImage (S : Set (PhaseVar n → K)) : Set (Fin n → K) :=
  (fun q i ↦ q (Sum.inr i)) '' S

/-- The ground-field affine vanishing hull of the fibre directions of a set
of extension-valued phase points.  Both projection and extension-valued
vanishing are explicit; this is not a full phase-space closure. -/
def extensionFibreClosure (S : Set (PhaseVar n → K)) : Set (Fin n → k) :=
  MvPolynomial.zeroLocus k
    (extensionValuedVanishingIdeal (k := k) (K := K) (fibreImage S))

/-- Evaluating a ground-field polynomial on power-series coordinates and then
embedding in Laurent series is the same as evaluating directly on the
embedded Laurent coordinates. -/
theorem algebraMap_eval_powerSeries_eq_eval₂_laurent
    (P : MvPolynomial (Fin n) k) (xi : Fin n → PowerSeries k) :
    algebraMap (PowerSeries k) (LaurentSeries k)
        (MvPolynomial.eval xi (MvPolynomial.map (PowerSeries.C) P)) =
      MvPolynomial.eval₂ (algebraMap k (LaurentSeries k))
        (fun i ↦ algebraMap (PowerSeries k) (LaurentSeries k) (xi i)) P := by
  have hcoeff :
      (algebraMap (PowerSeries k) (LaurentSeries k)).comp
          (PowerSeries.C) =
        algebraMap k (LaurentSeries k) := by
    ext r
    simp [LaurentSeries.algebraMap_apply]
  rw [MvPolynomial.eval_map, MvPolynomial.eval₂_comp_left, hcoeff]
  rfl

/-- A Laurent-valued phase point whose fibre coordinates are regular power
series specializes, after forgetting its possibly singular base coordinate,
to the ground-field extension-valued vanishing hull of the projected fibre
image. -/
theorem residue_mem_extensionFibreClosure_of_laurent_generic
    (S : Set (PhaseVar n → LaurentSeries k))
    (y : Fin n → LaurentSeries k)
    (xi : Fin n → PowerSeries k)
    (hgeneric :
      Sum.elim y
          (fun i ↦ algebraMap (PowerSeries k) (LaurentSeries k) (xi i)) ∈ S) :
    residueColumn xi ∈
      extensionFibreClosure (k := k) (K := LaurentSeries k) S := by
  rw [extensionFibreClosure, MvPolynomial.mem_zeroLocus_iff]
  intro P hP
  have hzeroLaurent :
      MvPolynomial.eval₂ (algebraMap k (LaurentSeries k))
          (fun i ↦ algebraMap (PowerSeries k) (LaurentSeries k) (xi i)) P = 0 := by
    apply (mem_extensionValuedVanishingIdeal_iff
      (k := k) (K := LaurentSeries k) (fibreImage S) P).mp hP
    exact ⟨Sum.elim y
      (fun i ↦ algebraMap (PowerSeries k) (LaurentSeries k) (xi i)),
      hgeneric, rfl⟩
  have hzeroPowerSeries :
      MvPolynomial.eval xi (MvPolynomial.map (PowerSeries.C) P) = 0 := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    change algebraMap (PowerSeries k) (LaurentSeries k)
        (MvPolynomial.eval xi (MvPolynomial.map (PowerSeries.C) P)) =
      algebraMap (PowerSeries k) (LaurentSeries k) 0
    rw [map_zero, algebraMap_eval_powerSeries_eq_eval₂_laurent]
    exact hzeroLaurent
  exact residue_eval_eq_zero_of_eval_map_eq_zero P xi hzeroPowerSeries

/-- The projected Laurent-direction hull of the scalar-extended
equation-defined conormal locus. -/
def laurentEquationConormalDirectionClosure
    (I : Ideal (MvPolynomial (Fin n) k)) : Set (Fin n → k) :=
  extensionFibreClosure (k := k) (K := LaurentSeries k)
    (equationConormalLocus
      (I.map
        (scalarPolynomialMap
          (k := k) (K := LaurentSeries k) (Fin n))))

/-- Projected-direction specialization for a Laurent-valued point of the
scalar-extended equation conormal locus. -/
theorem residue_mem_laurentEquationConormalDirectionClosure
    (I : Ideal (MvPolynomial (Fin n) k))
    (y : Fin n → LaurentSeries k)
    (xi : Fin n → PowerSeries k)
    (hgeneric :
      Sum.elim y
          (fun i ↦ algebraMap (PowerSeries k) (LaurentSeries k) (xi i)) ∈
        equationConormalLocus
          (I.map
            (scalarPolynomialMap
              (k := k) (K := LaurentSeries k) (Fin n)))) :
    residueColumn xi ∈ laurentEquationConormalDirectionClosure I := by
  exact residue_mem_extensionFibreClosure_of_laurent_generic
    (S := equationConormalLocus
      (I.map
        (scalarPolynomialMap
          (k := k) (K := LaurentSeries k) (Fin n))))
    y xi hgeneric

/-- Embed a ground-field polynomial in fibre variables as a fibre-only phase
symbol. -/
def fibreLift (P : MvPolynomial (Fin n) k) : SymbolRing k n :=
  MvPolynomial.rename Sum.inr P

/-- Evaluation of a fibre-only phase symbol ignores the base coordinate. -/
theorem eval₂_fibreLift
    (P : MvPolynomial (Fin n) k)
    (y xi : Fin n → K) :
    MvPolynomial.eval₂ (algebraMap k K) (Sum.elim y xi) (fibreLift P) =
      MvPolynomial.eval₂ (algebraMap k K) xi P := by
  rw [fibreLift, MvPolynomial.eval₂_rename]
  rfl

/-- Direct projected-direction contradiction.  A fibre-only ground-field
symbol cannot both evaluate to one on the residue axis and vanish on a
Laurent generic conormal direction whose fibre coordinates have that residue.

The conormal hypothesis is used only to place the generic fibre in the
projected set; no specialization of its base coordinate is asserted. -/
theorem false_of_fibreOnly_symbol_one_on_residue_and_vanishes_on_laurentConormal
    (I : Ideal (MvPolynomial (Fin n) k))
    (P : MvPolynomial (Fin n) k)
    (axis : Fin n → k)
    (y : Fin n → LaurentSeries k)
    (xi : Fin n → PowerSeries k)
    (hgeneric :
      Sum.elim y
          (fun i ↦ algebraMap (PowerSeries k) (LaurentSeries k) (xi i)) ∈
        equationConormalLocus
          (I.map
            (scalarPolynomialMap
              (k := k) (K := LaurentSeries k) (Fin n))))
    (hresidue : residueColumn xi = axis)
    (hvanishes :
      ∀ q ∈ equationConormalLocus
          (I.map
            (scalarPolynomialMap
              (k := k) (K := LaurentSeries k) (Fin n))),
        MvPolynomial.eval₂ (algebraMap k (LaurentSeries k)) q
          (fibreLift P) = 0)
    (haxis : MvPolynomial.eval axis P = 1) : False := by
  let S : Set (PhaseVar n → LaurentSeries k) :=
    equationConormalLocus
      (I.map
        (scalarPolynomialMap
          (k := k) (K := LaurentSeries k) (Fin n)))
  have hP :
      P ∈ extensionValuedVanishingIdeal
        (k := k) (K := LaurentSeries k) (fibreImage S) := by
    rw [mem_extensionValuedVanishingIdeal_iff]
    intro v hv
    rcases hv with ⟨q, hq, rfl⟩
    rw [← eval₂_fibreLift P (fun i ↦ q (Sum.inl i))]
    have hsplit :
        Sum.elim (fun i ↦ q (Sum.inl i)) (fun i ↦ q (Sum.inr i)) = q := by
      funext i
      rcases i with i | i <;> rfl
    rw [hsplit]
    exact hvanishes q hq
  have hresidueInHull :
      residueColumn xi ∈
        extensionFibreClosure (k := k) (K := LaurentSeries k) S :=
    residue_mem_extensionFibreClosure_of_laurent_generic
      (S := S) y xi hgeneric
  rw [extensionFibreClosure, MvPolynomial.mem_zeroLocus_iff] at hresidueInHull
  have hzeroResidue := hresidueInHull P hP
  rw [hresidue, MvPolynomial.aeval_eq_eval, haxis] at hzeroResidue
  exact one_ne_zero hzeroResidue

/-! The declarations below make the scope boundary executable: projection
forgets arbitrary base coordinates, whereas membership in a full phase set
still retains them.  In particular no converse reconstructing a finite phase
specialization is available from `fibreImage`. -/

theorem fibre_mem_fibreImage_of_phase_mem
    (S : Set (PhaseVar n → K)) (q : PhaseVar n → K) (hq : q ∈ S) :
    (fun i ↦ q (Sum.inr i)) ∈ fibreImage S :=
  ⟨q, hq, rfl⟩


end

end Stafford38.Geometry.LaurentConormalDirection
