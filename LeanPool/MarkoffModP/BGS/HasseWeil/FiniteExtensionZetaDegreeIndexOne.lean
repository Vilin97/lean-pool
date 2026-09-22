/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantExtensionClosedPlaceCount
import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionConstants
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionIndexedZetaRationalityAutomatic
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionZetaDegreeExtensionIdentity
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionZetaNumeratorNoncancellation
import LeanPool.MarkoffModP.BGS.HasseWeil.FormalZetaDegreeIndexOneIndexed
import LeanPool.MarkoffModP.BGS.HasseWeil.RatFuncExactConstantExtension

/-!
# The geometric F. K. Schmidt composition

This file composes indexed zeta rationality, numerator noncancellation, the
formal constant-extension identity, and indexed rationality after exact
constant extension.  The extension is never assumed to have degree index one.

The only geometric input left explicit is the closed-place count identity for
the constant extension whose degree is the original divisor-degree index.
-/

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier
open scoped Polynomial TensorProduct

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance degreeIndexOneAutomaticConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance degreeIndexOneAutomaticConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Exact constants automatically give an indexed rational numerator which
does not vanish at `T = 1`. -/
theorem exists_finiteExtensionClosedPlaceZeta_indexed_rational_nonvanishing_of_constants
    (hconstants : algebraicClosure K L =
      (⊥ : IntermediateField K L)) :
    ∃ P : Polynomial ℂ,
      P.coeff 0 = 1 ∧ P.eval 1 ≠ 0 ∧
        HasIndexedCurveZetaRationalForm
          (formalPointCountZeta
            (finiteExtensionClosedPlaceExtensionCount K L))
          (Nat.card K) (finiteExtensionDivisorDegreeIndex K L) P := by
  obtain ⟨genus, threshold, hRiemann⟩ :=
    exists_hasFiniteExtensionUniformEventualRiemannFormula_of_constants
      K L hconstants
  exact exists_finiteExtensionClosedPlaceZeta_indexed_rational_nonvanishing
    K L genus threshold hconstants hRiemann

variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Fintype C] [Fintype S] [DecidableEq C] [DecidableEq (RatFunc C)]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance degreeIndexOneBaseConstantAlgebra : Algebra C N :=
  RingHom.toAlgebra ((algebraMap (RatFunc C) N).comp
    (algebraMap C (RatFunc C)))

local instance degreeIndexOneBaseConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The exhaustive closed-place point-count sequence of the exact constant
extension, packaged with its canonical `S(X)`-function-field structure. -/
noncomputable def exactConstantExtensionClosedPlaceExtensionCount
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N)) (r : ℕ) : ℕ := by
  let E := ExactConstantExtension C N S
  letI : Field E := exactConstantExtensionField C N S hExact
  letI : Algebra (RatFunc S) E :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  letI : SMul (RatFunc S) E := Algebra.toSMul
  letI : Module (RatFunc S) E := Algebra.toModule
  letI : FiniteDimensional (RatFunc S) E :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  letI : Algebra.IsSeparable (RatFunc S) E :=
    isSeparable_over_extendedRatFunc C S N hExact
  letI : DecidableEq S := infinityBridgeDecidableEqConstants S
  letI : DecidableEq (RatFunc S) :=
    closedPlaceRatFuncConstantsDecidableEq S
  exact finiteExtensionClosedPlaceExtensionCount S E r

omit [Fintype C] [DecidableEq C] [DecidableEq (RatFunc C)] in
/-- Replacing the former explicit `Classical.decEq` choices by the canonical
closed-place choices does not change the exact-constant-extension count. -/
theorem exactConstantExtensionClosedPlaceExtensionCount_eq_classical_decidableEq
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N)) (r : ℕ) :
    exactConstantExtensionClosedPlaceExtensionCount C S N hExact r =
      (by
        let E := ExactConstantExtension C N S
        letI : Field E := exactConstantExtensionField C N S hExact
        letI : Algebra (RatFunc S) E :=
          ratFuncExactConstantExtensionAlgebra C S N hExact
        letI : SMul (RatFunc S) E := Algebra.toSMul
        letI : Module (RatFunc S) E := Algebra.toModule
        letI : FiniteDimensional (RatFunc S) E :=
          finiteDimensional_over_extendedRatFunc C S N hExact
        letI : Algebra.IsSeparable (RatFunc S) E :=
          isSeparable_over_extendedRatFunc C S N hExact
        letI : DecidableEq S := Classical.decEq S
        letI : DecidableEq (RatFunc S) := Classical.decEq (RatFunc S)
        exact finiteExtensionClosedPlaceExtensionCount S E r) := by
  unfold exactConstantExtensionClosedPlaceExtensionCount
  congr 1

/-- Noncircular geometric F. K. Schmidt theorem.

`S/C` is required to have degree equal to the original divisor-degree index.
The sole remaining geometric relation says that the closed-place point count
after this constant extension at level `r` is the original count at level
`d*r`.  Indexed rationality of both zeta series, including the extension, is
derived internally. -/
theorem finiteExtensionDivisorDegreeIndex_eq_one_of_exactConstantExtension_closedPlaceCount
    (hExact : algebraicClosure C N =
      (⊥ : IntermediateField C N))
    (hdegree : Module.finrank C S =
      finiteExtensionDivisorDegreeIndex C N)
    (hcount : ∀ r,
      exactConstantExtensionClosedPlaceExtensionCount C S N hExact r =
        finiteExtensionClosedPlaceExtensionCount C N
          (finiteExtensionDivisorDegreeIndex C N * r)) :
    finiteExtensionDivisorDegreeIndex C N = 1 := by
  let E := ExactConstantExtension C N S
  let d := finiteExtensionDivisorDegreeIndex C N
  let : Field E := exactConstantExtensionField C N S hExact
  let : Algebra (RatFunc S) E :=
    ratFuncExactConstantExtensionAlgebra C S N hExact
  let : SMul (RatFunc S) E := Algebra.toSMul
  let : Module (RatFunc S) E := Algebra.toModule
  let : FiniteDimensional (RatFunc S) E :=
    finiteDimensional_over_extendedRatFunc C S N hExact
  let : Algebra.IsSeparable (RatFunc S) E :=
    isSeparable_over_extendedRatFunc C S N hExact
  let : DecidableEq S := infinityBridgeDecidableEqConstants S
  let : DecidableEq (RatFunc S) :=
    closedPlaceRatFuncConstantsDecidableEq S
  let extendedConstantAlgebra : Algebra S E :=
    RingHom.toAlgebra ((algebraMap (RatFunc S) E).comp
      (algebraMap S (RatFunc S)))
  let tensorConstantAlgebra : Algebra S E :=
    Algebra.TensorProduct.leftAlgebra
  have hconstantMap (s : S) :
      (@algebraMap S E _ _ extendedConstantAlgebra) s =
        (@algebraMap S E _ _ tensorConstantAlgebra) s := by
    exact (ratFuncToExactConstantExtension C S N hExact).commutes s
  have hAlgebraicTransfer (z : E)
      (hz : @IsAlgebraic S E _ _ extendedConstantAlgebra z) :
      @IsAlgebraic S E _ _ tensorConstantAlgebra z := by
    rcases hz with ⟨p, hp, hpz⟩
    refine ⟨p, hp, ?_⟩
    have hmapEq :
        (@algebraMap S E _ _ extendedConstantAlgebra) =
          (@algebraMap S E _ _ tensorConstantAlgebra) := by
      ext s
      exact hconstantMap s
    change Polynomial.eval₂
      (@algebraMap S E _ _ extendedConstantAlgebra) z p = 0 at hpz
    change Polynomial.eval₂
      (@algebraMap S E _ _ tensorConstantAlgebra) z p = 0
    rw [← hmapEq]
    exact hpz
  have hTensorRange (z : E)
      (hz : @IsAlgebraic S E _ _ tensorConstantAlgebra z) :
      z ∈ Set.range (@algebraMap S E _ _ tensorConstantAlgebra) := by
    let : Algebra S E := tensorConstantAlgebra
    have hTensorExact : algebraicClosure S E =
        (⊥ : IntermediateField S E) :=
      exactConstantExtension_algebraicClosure_eq_bot C N S hExact
    have hzClosure : z ∈ algebraicClosure S E :=
      mem_algebraicClosure_iff.mpr hz
    have hzBot : z ∈ (⊥ : IntermediateField S E) := by
      rw [← hTensorExact]
      exact hzClosure
    exact hzBot
  let : Algebra S E := extendedConstantAlgebra
  have hExtendedExact : algebraicClosure S E =
      (⊥ : IntermediateField S E) := by
    apply eq_bot_iff.mpr
    intro z hz
    have hzExtended : @IsAlgebraic S E _ _ extendedConstantAlgebra z :=
      mem_algebraicClosure_iff.mp hz
    obtain ⟨s, hs⟩ := hTensorRange z
      (hAlgebraicTransfer z hzExtended)
    exact ⟨s, (hconstantMap s).trans hs⟩
  obtain ⟨P, _, hPone, hPindexed⟩ :=
    exists_finiteExtensionClosedPlaceZeta_indexed_rational_nonvanishing_of_constants
      C N hExact
  obtain ⟨extendedP, _, hExtendedIndexed⟩ :=
    exists_finiteExtensionClosedPlaceZeta_indexed_rational_of_constants
      S E hExtendedExact
  have hcard : Nat.card S = Nat.card C ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := C) (V := S), hdegree]
  have hExtensionIdentity : HasFormalDegreeExtensionZetaIdentity
      (formalPointCountZeta
        (finiteExtensionClosedPlaceExtensionCount C N))
      (formalPointCountZeta
        (finiteExtensionClosedPlaceExtensionCount S E)) d := by
    apply finiteExtensionClosedPlaceZeta_hasDegreeExtensionIdentity C N
    intro r
    rw [← hcount r]
    rfl
  apply degreeIndex_eq_one_of_two_indexed_rationalForms_and_degreeExtension
    (formalPointCountZeta
      (finiteExtensionClosedPlaceExtensionCount C N))
    (formalPointCountZeta
      (finiteExtensionClosedPlaceExtensionCount S E))
    (Nat.card C) d (finiteExtensionDivisorDegreeIndex S E)
    P extendedP
  · rw [← Fintype.card_eq_nat_card]
    exact Fintype.one_lt_card
  · exact finiteExtensionDivisorDegreeIndex_pos C N
  · exact finiteExtensionDivisorDegreeIndex_pos S E
  · exact hPone
  · exact hPindexed
  · simpa only [hcard] using hExtendedIndexed
  · exact hExtensionIdentity

end

end BGS.HasseWeil
