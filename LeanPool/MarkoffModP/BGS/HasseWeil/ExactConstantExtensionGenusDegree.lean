/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionCanonicalDifferentLocalMaximality
public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionConstants
public import LeanPool.MarkoffModP.BGS.HasseWeil.RatFuncExactConstantExtension

/-!
# Genus and extension degree under exact constant extension

This file records two numerical consequences needed to compare a function
field with an exact finite extension of its constants.  First, cotrace
canonicality identifies the total finite-and-infinite trace-different degree
with the Riemann--Hurwitz expression.  Second, extending the constants from
`C` to `S` preserves the degree over the corresponding rational function
field.
-/

@[expose] public section

open scoped Polynomial TensorProduct

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier


section RiemannHurwitzDegree

variable (K : Type*) [Field K] [Finite K]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance genusDegreeFintype : Fintype K := Fintype.ofFinite K
local instance genusDegreeDecidableEq : DecidableEq K := Classical.decEq K
local instance genusDegreeRatFuncDecidableEq : DecidableEq (RatFunc K) :=
  Classical.decEq (RatFunc K)
local instance genusDegreeConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))
local instance genusDegreeConstantTower : IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance (priority := 10) genusDegreePolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))
local instance genusDegreePolynomialTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance genusDegreeConstantPolynomialTower :
    IsScalarTower K K[X] L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Cotrace canonicality gives the Riemann--Hurwitz equality for the weighted
finite and infinite trace-different degrees. -/
theorem finiteExtension_totalDifferentDegree_eq_two_finrank_add_two_genus_sub_two
    [FunctionField.IsFullConstantField K L] :
    (finiteExtensionFiniteDifferentDegree K L
        (finiteExtensionFiniteDifferentIdeal_ne_bot K L) : ℤ) +
      (infinityDifferentDegree K L : ℤ) =
        2 * (Module.finrank (RatFunc K) L : ℤ) +
          2 * (FunctionField.Chart.genus K L : ℤ) - 2 := by
  apply
    (finiteExtensionCanonicalDifferent_degree_eq_two_genus_sub_two_iff K L).mp
  rw [finiteExtensionDivisorDegree_eq_chart]
  exact FunctionField.Chart.deg_canonical K L
    (finiteExtensionCanonicalDifferent_isCanonical_of_cotrace K L)

/-- The same Riemann--Hurwitz identity stated with the intrinsic genus.  This
form no longer remembers which compatible polynomial chart was installed. -/
theorem finiteExtension_totalDifferentDegree_eq_two_finrank_add_two_genus_sub_two_intrinsic
    [FunctionField.IsFullConstantField K L] :
    (finiteExtensionFiniteDifferentDegree K L
        (finiteExtensionFiniteDifferentIdeal_ne_bot K L) : ℤ) +
      (infinityDifferentDegree K L : ℤ) =
        2 * (Module.finrank (RatFunc K) L : ℤ) +
          2 * (FunctionField.genus K L : ℤ) - 2 := by
  rw [FunctionField.genus_eq_genusChart K L]
  exact finiteExtension_totalDifferentDegree_eq_two_finrank_add_two_genus_sub_two K L

end RiemannHurwitzDegree

section RiemannHurwitzDegreeCompatibleChart

variable (K : Type*) [Field K] [Finite K]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]
  [Algebra K[X] L] [IsScalarTower K[X] (RatFunc K) L]

local instance compatibleGenusDegreeFintype : Fintype K := Fintype.ofFinite K
local instance compatibleGenusDegreeDecidableEq : DecidableEq K := Classical.decEq K
local instance compatibleGenusDegreeRatFuncDecidableEq : DecidableEq (RatFunc K) :=
  Classical.decEq (RatFunc K)
local instance compatibleGenusDegreeConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))
local instance compatibleGenusDegreeConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

variable [IsScalarTower K K[X] L]

/-- Riemann--Hurwitz for any polynomial chart whose action is compatible
with the fixed rational-function-field action.  This is the same statement
as `finiteExtension_totalDifferentDegree_eq_two_finrank_add_two_genus_sub_two`,
but it keeps an explicitly installed chart instead of replacing it by the
induced one. -/
theorem finiteExtension_totalDifferentDegree_eq_two_finrank_add_two_genus_sub_two_of_compatibleChart
    [FunctionField.IsFullConstantField K L] :
    (finiteExtensionFiniteDifferentDegree K L
        (finiteExtensionFiniteDifferentIdeal_ne_bot K L) : ℤ) +
      (infinityDifferentDegree K L : ℤ) =
        2 * (Module.finrank (RatFunc K) L : ℤ) +
          2 * (FunctionField.Chart.genus K L : ℤ) - 2 := by
  rw [← FunctionField.genus_eq_genusChart K L]
  exact
    finiteExtension_totalDifferentDegree_eq_two_finrank_add_two_genus_sub_two_intrinsic K L

end RiemannHurwitzDegreeCompatibleChart

section ExactConstantExtensionConstants

variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Finite C] [Finite S]
  [Algebra (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance exactConstantExtensionGenusConstantAlgebra : Algebra C N :=
  RingHom.toAlgebra ((algebraMap (RatFunc C) N).comp
    (algebraMap C (RatFunc C)))

/-- Exactness of the extended constants for the constant algebra induced by
the canonical `S(X)`-algebra structure on the exact constant extension. -/
theorem exactConstantExtension_extended_algebraicClosure_eq_bot
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N)) :
    let L := ExactConstantExtension C N S
    letI : Field L := exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc S) L :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : Algebra S L :=
      RingHom.toAlgebra ((algebraMap (RatFunc S) L).comp
        (algebraMap S (RatFunc S)))
    algebraicClosure S L = (⊥ : IntermediateField S L) := by
  let L := ExactConstantExtension C N S
  let : Field L := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc S) L :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let extendedConstantAlgebra : Algebra S L :=
    RingHom.toAlgebra ((algebraMap (RatFunc S) L).comp
      (algebraMap S (RatFunc S)))
  let tensorConstantAlgebra : Algebra S L :=
    Algebra.TensorProduct.leftAlgebra
  have hconstantMap (s : S) :
      (@algebraMap S L _ _ extendedConstantAlgebra) s =
        (@algebraMap S L _ _ tensorConstantAlgebra) s := by
    exact (ratFuncToExactConstantExtension C S N hExact).commutes s
  have hAlgebraicTransfer (z : L)
      (hz : @IsAlgebraic S L _ _ extendedConstantAlgebra z) :
      @IsAlgebraic S L _ _ tensorConstantAlgebra z := by
    rcases hz with ⟨p, hp, hpz⟩
    refine ⟨p, hp, ?_⟩
    have hmapEq :
        (@algebraMap S L _ _ extendedConstantAlgebra) =
          (@algebraMap S L _ _ tensorConstantAlgebra) := by
      ext s
      exact hconstantMap s
    change Polynomial.eval₂
      (@algebraMap S L _ _ extendedConstantAlgebra) z p = 0 at hpz
    change Polynomial.eval₂
      (@algebraMap S L _ _ tensorConstantAlgebra) z p = 0
    rw [← hmapEq]
    exact hpz
  have hTensorRange (z : L)
      (hz : @IsAlgebraic S L _ _ tensorConstantAlgebra z) :
      z ∈ Set.range (@algebraMap S L _ _ tensorConstantAlgebra) := by
    let : Algebra S L := tensorConstantAlgebra
    have hTensorExact : algebraicClosure S L =
        (⊥ : IntermediateField S L) :=
      exactConstantExtension_algebraicClosure_eq_bot C N S hExact
    have hzClosure : z ∈ algebraicClosure S L :=
      mem_algebraicClosure_iff.mpr hz
    have hzBot : z ∈ (⊥ : IntermediateField S L) := by
      rw [← hTensorExact]
      exact hzClosure
    exact hzBot
  let : Algebra S L := extendedConstantAlgebra
  apply eq_bot_iff.mpr
  intro z hz
  have hzExtended : @IsAlgebraic S L _ _ extendedConstantAlgebra z :=
    mem_algebraicClosure_iff.mp hz
  obtain ⟨s, hs⟩ := hTensorRange z
    (hAlgebraicTransfer z hzExtended)
  exact ⟨s, (hconstantMap s).trans hs⟩

end ExactConstantExtensionConstants

section ExactConstantExtensionDegree

variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance exactConstantExtensionDegreeConstantAlgebra : Algebra C N :=
  RingHom.toAlgebra ((algebraMap (RatFunc C) N).comp
    (algebraMap C (RatFunc C)))

/-- Exact finite extension of the constants preserves the function-field
degree: `[S ⊗_C N : S(X)] = [N : C(X)]`. -/
theorem exactConstantExtension_finrank_over_extendedRatFunc_eq
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N)) :
    let L := ExactConstantExtension C N S
    letI : Field L := exactConstantExtensionField C N S hExact
    letI : Algebra (RatFunc C) (RatFunc S) :=
      ratFuncCoefficientAlgebra C S
    letI : Algebra (RatFunc C) L :=
      exactConstantExtensionBaseAlgebra C (RatFunc C) N S
    letI : Algebra (RatFunc S) L :=
      ratFuncExactConstantExtensionAlgebra C S N hExact
    letI : SMul (RatFunc S) L := Algebra.toSMul
    letI : Module (RatFunc S) L := Algebra.toModule
    Module.finrank (RatFunc S) L = Module.finrank (RatFunc C) N := by
  let L := ExactConstantExtension C N S
  let : Field L := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc C) (RatFunc S) :=
    ratFuncCoefficientAlgebra C S
  let : Algebra (RatFunc C) L :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N S
  let : Algebra (RatFunc S) L :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : SMul (RatFunc C) (RatFunc S) := Algebra.toSMul
  let : SMul (RatFunc C) L := Algebra.toSMul
  let : SMul (RatFunc S) L := Algebra.toSMul
  let : Module (RatFunc C) (RatFunc S) := Algebra.toModule
  let : Module (RatFunc C) L := Algebra.toModule
  let : Module (RatFunc S) L := Algebra.toModule
  let : IsScalarTower (RatFunc C) (RatFunc S) L :=
    rationalBase_scalarTower C S N hExact
  let : FiniteDimensional (RatFunc S) L :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  have hdegree :
      Module.finrank (RatFunc C) (RatFunc S) *
          Module.finrank (RatFunc S) L =
        Module.finrank (RatFunc C) N * Module.finrank C S := by
    calc
      Module.finrank (RatFunc C) (RatFunc S) *
            Module.finrank (RatFunc S) L =
          Module.finrank (RatFunc C) L :=
        Module.finrank_mul_finrank (RatFunc C) (RatFunc S) L
      _ = Module.finrank (RatFunc C) N * Module.finrank C S :=
        exactConstantExtension_finrank_over_base
          C (RatFunc C) N S
  have hcancel :
      Module.finrank C S * Module.finrank (RatFunc S) L =
        Module.finrank C S * Module.finrank (RatFunc C) N := by
    simpa only [ratFuncCoefficient_finrank, mul_comm] using hdegree
  exact Nat.mul_left_cancel
    (Module.finrank_pos (R := C) (M := S)) hcancel

end ExactConstantExtensionDegree

end

end BGS.HasseWeil
