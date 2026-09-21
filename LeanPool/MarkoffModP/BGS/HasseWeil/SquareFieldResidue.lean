/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveAuxiliaryFinitePlaceCases
import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointLeadingCoefficient
import Mathlib.Tactic

/-!
# Degree-one residues over a square constant field

For a function field over a finite field `S`, a finite place of constant-field
degree one has residue field of cardinality `#S`.  If `#S = (#K)^2`, every
residue therefore satisfies the half-Frobenius square identity used by the
semilinear Stepanov restriction.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped Polynomial

noncomputable section

variable (K S : Type*) [Field K] [Fintype K]
  [Field S] [Fintype S] [DecidableEq S]
  [DecidableEq (RatFunc S)]
variable (L : Type*) [Field L] [Algebra (RatFunc S) L]
  [FiniteDimensional (RatFunc S) L]
  [Algebra.IsSeparable (RatFunc S) L]

local instance (priority := 10) squareFieldResiduePolynomialAlgebra :
    Algebra S[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc S) L).comp
    (algebraMap S[X] (RatFunc S)))

local instance squareFieldResiduePolynomialScalarTower :
    IsScalarTower S[X] (RatFunc S) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance squareFieldResidueFiniteConstantAlgebra :
    Algebra S (RatFuncFiniteIntegralClosure S L) :=
  RingHom.toAlgebra ((algebraMap S[X]
    (RatFuncFiniteIntegralClosure S L)).comp (algebraMap S S[X]))

local instance squareFieldResidueFiniteConstantTower :
    IsScalarTower S S[X] (RatFuncFiniteIntegralClosure S L) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- A degree-one finite place over a square constant field has the quadratic
half-Frobenius identity in its residue field. -/
theorem finiteExtensionFinitePlace_residue_squareFrobenius_of_degree_one
    (hcard : Fintype.card S = (Fintype.card K) ^ 2)
    (q : FiniteExtensionFinitePlace S L)
    (hdegree : finiteExtensionPlaceDegree S L (.inl q) = 1) :
    ∀ z : q.asIdeal.ResidueField,
      z ^ (Fintype.card K) ^ 2 = z := by
  letI : Finite q.asIdeal.ResidueField :=
    finiteExtensionFinitePlace_residueField_finite (K := S) (L := L) q
  letI : Fintype q.asIdeal.ResidueField := Fintype.ofFinite _
  letI : Module.Finite S q.asIdeal.ResidueField := by
    rw [Module.finite_def]
    exact ⟨Finset.univ, by simp⟩
  have hfinrank : Module.finrank S q.asIdeal.ResidueField = 1 := by
    rw [finiteExtensionFinitePlace_degree_eq_finrank_residueField S L q] at hdegree
    exact hdegree
  have hresidueCard :
      Fintype.card q.asIdeal.ResidueField = (Fintype.card K) ^ 2 := by
    calc
      Fintype.card q.asIdeal.ResidueField =
          (Fintype.card S) ^ Module.finrank S q.asIdeal.ResidueField :=
        Module.card_eq_pow_finrank
      _ = (Fintype.card K) ^ 2 := by rw [hfinrank, pow_one, hcard]
  intro z
  simpa [hresidueCard] using FiniteField.pow_card z

end

end BGS.HasseWeil
