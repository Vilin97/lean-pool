/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionIntermediateFrobeniusTwistHasseBound
public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionGenusDegree
public import LeanPool.MarkoffModP.BGS.HasseWeil.ExactConstantExtensionNormalClosureTower
public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionDivisibleErrorFromConstantBase
public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteFieldDivisibleExtension

/-!
# Hasse--Weil for finite separable function-field extensions

The normal closure supplies one finite enlargement of the constant field over
which the extension is geometric.  At every sufficiently divisible even
constant-field degree, a quadratic subfield and an auxiliary extension of
factorial degree put the fixed-tower Frobenius-twist estimate into a uniform
form.  Exact constant-extension splitting and the spectral argument then
transport that estimate back to the original function field.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section


section GenusBridge

variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Fintype C] [Finite S]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]
local instance : Algebra C N := bridgeBaseConstantAlgebra C N
local instance : IsScalarTower C (RatFunc C) N := IsScalarTower.of_algebraMap_eq' rfl

/-- Constant extension preserves genus for the induced rational-function-field algebra. -/
private theorem exactConstantExtension_genus_eq_for_ratFunc
    (hExact : algebraicClosure C N = (⊥ : IntermediateField C N)) :
    let E := ExactConstantExtension C N S
    let : Field E := exactConstantExtensionField C N S hExact
    let : Algebra (RatFunc S) E := ratFuncExactConstantExtensionAlgebra C S N hExact
    @FunctionField.genus S E _ _ (bridgeBaseConstantAlgebra S E) = FunctionField.genus C N := by
  intro E fieldStructure rationalAlgebra
  have hConstantAlgebra : (Algebra.TensorProduct.leftAlgebra : Algebra S E) =
      bridgeBaseConstantAlgebra S E := by
    apply Algebra.algebra_ext
    intro s
    exact (ratFuncToExactConstantExtension C S N hExact).commutes s |>.symm
  rw [← hConstantAlgebra]
  exact exactConstantExtension_genus_eq C S N hExact


end GenusBridge

variable (K F : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)] [Field F] [Algebra (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F]
  [Algebra.IsSeparable (RatFunc K) F]

local instance finiteExtensionHasseBaseConstantAlgebra : Algebra K F :=
  bridgeBaseConstantAlgebra K F

local instance finiteExtensionHasseBaseConstantTower :
    IsScalarTower K (RatFunc K) F :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance finiteExtensionHasseNormalClosureConstantFintype :
    Fintype (FunctionFieldNormalClosureConstantField K F) :=
  Fintype.ofFinite _

local instance finiteExtensionHasseNormalClosureConstantAlgebra :
    Algebra K (FunctionFieldNormalClosureConstantField K F) :=
  SubalgebraClass.toAlgebra
    (algebraicClosure K (FunctionFieldNormalClosure K F))

local instance finiteExtensionHasseNormalClosureConstantSmul :
    SMul K (FunctionFieldNormalClosureConstantField K F) :=
  Algebra.toSMul

local instance finiteExtensionHasseNormalClosureConstantModule :
    Module K (FunctionFieldNormalClosureConstantField K F) :=
  Algebra.toModule

local instance finiteExtensionHasseNormalClosureConstantFiniteDimensional :
    FiniteDimensional K (FunctionFieldNormalClosureConstantField K F) :=
  functionFieldConstantField_finiteDimensional K
    (FunctionFieldNormalClosure K F)

local instance finiteExtensionHasseNormalClosureConstantIsGalois :
    IsGalois K (FunctionFieldNormalClosureConstantField K F) :=
  functionFieldConstantField_isGalois K (FunctionFieldNormalClosure K F)

local instance finiteExtensionHasseNormalClosureConstantDecidableEq :
    DecidableEq (FunctionFieldNormalClosureConstantField K F) :=
  Classical.decEq _

local instance finiteExtensionHasseNormalClosureRatFuncDecidableEq :
    DecidableEq (RatFunc (FunctionFieldNormalClosureConstantField K F)) :=
  Classical.decEq _

local instance finiteExtensionHasseNormalClosureRatFuncSmul :
    SMul (RatFunc (FunctionFieldNormalClosureConstantField K F))
      (FunctionFieldNormalClosure K F) :=
  Algebra.toSMul

local instance finiteExtensionHasseNormalClosureRatFuncModule :
    Module (RatFunc (FunctionFieldNormalClosureConstantField K F))
      (FunctionFieldNormalClosure K F) :=
  Algebra.toModule

local instance finiteExtensionHasseNormalClosureRatFuncTorsionFree :
    Module.IsTorsionFree
      (RatFunc (FunctionFieldNormalClosureConstantField K F))
      (FunctionFieldNormalClosure K F) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  exact (algebraMap
    (RatFunc (FunctionFieldNormalClosureConstantField K F))
    (FunctionFieldNormalClosure K F)).injective

local instance finiteExtensionHasseNormalClosureFiniteDimensional :
    FiniteDimensional
      (RatFunc (FunctionFieldNormalClosureConstantField K F))
      (FunctionFieldNormalClosure K F) :=
  functionFieldNormalClosure_finiteDimensional_over_constantRatFunc K F

local instance finiteExtensionHasseNormalClosureCanonicalConstantAlgebra :
    Algebra (FunctionFieldNormalClosureConstantField K F)
      (FunctionFieldNormalClosure K F) :=
  exactConstantExtensionTowerCanonicalConstantAlgebra _ _

/-- The genus of the chosen normal closure over its full constant field. -/
noncomputable def functionFieldNormalClosureGenus : ℕ :=
  FunctionField.genus (FunctionFieldNormalClosureConstantField K F)
    (FunctionFieldNormalClosure K F)

/-- The degree of the chosen normal closure over the canonical rational
function field of its full constant field. -/
noncomputable def functionFieldNormalClosureRatFuncDegree : ℕ :=
  Module.finrank (RatFunc (FunctionFieldNormalClosureConstantField K F))
    (FunctionFieldNormalClosure K F)

/-- The Stepanov threshold attached to the chosen normal closure. -/
def functionFieldNormalClosureStepanovThreshold : ℕ :=
  (functionFieldNormalClosureGenus K F + 1) *
    (functionFieldNormalClosureGenus K F + 2)

omit [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)] in
theorem functionFieldNormalClosureRatFuncDegree_pos :
    0 < functionFieldNormalClosureRatFuncDegree K F := by
  unfold functionFieldNormalClosureRatFuncDegree
  exact Module.finrank_pos

omit [Fintype K] [DecidableEq K] [DecidableEq (RatFunc K)] in
theorem functionFieldNormalClosureStepanovThreshold_pos :
    0 < functionFieldNormalClosureStepanovThreshold K F := by
  unfold functionFieldNormalClosureStepanovThreshold
  positivity

section GenericGaloisTowerBound

variable (C M N : Type*) [Field C] [Fintype C] [DecidableEq C]
  [DecidableEq (RatFunc C)] [Field M] [Field N]
  [Algebra (RatFunc C) M] [Algebra (RatFunc C) N]
  [Algebra M N] [IsScalarTower (RatFunc C) M N]
  [FiniteDimensional (RatFunc C) M] [FiniteDimensional (RatFunc C) N]
  [FiniteDimensional M N]
  [IsGalois (RatFunc C) N] [IsGalois M N]
  [Algebra.IsSeparable (RatFunc C) M]

/-- Restrict the intermediate rational-function-field algebra to the constants. -/
local instance genericGaloisTowerConstantAlgebraM : Algebra C M :=
  exactConstantExtensionTowerCanonicalConstantAlgebra C M

/-- Restrict the top rational-function-field algebra to the constants. -/
local instance genericGaloisTowerConstantAlgebraN : Algebra C N :=
  exactConstantExtensionTowerCanonicalConstantAlgebra C N

private local instance genericGaloisTowerConstantTower : IsScalarTower C M N :=
  exactConstantExtensionTowerCanonicalConstantScalarTower C M N

private local instance genericGaloisTowerRationalConstantTowerM :
    IsScalarTower C (RatFunc C) M := IsScalarTower.of_algebraMap_eq' rfl

private local instance genericGaloisTowerRationalConstantTowerN :
    IsScalarTower C (RatFunc C) N := IsScalarTower.of_algebraMap_eq' rfl

private local instance genericGaloisTowerTopSeparable : Algebra.IsSeparable (RatFunc C) N :=
  (isGalois_iff.mp (inferInstance : IsGalois (RatFunc C) N)).1

omit [DecidableEq C] [DecidableEq (RatFunc C)] in
/-- A finite Galois function-field tower over exact finite constants satisfies the
square-field error bound after a sufficiently divisible even constant extension. -/
private theorem exactConstantExtensionClosedPlaceError_le_galoisTowerConstants
    (hExactM : algebraicClosure C M = (⊥ : IntermediateField C M))
    (hExactN : algebraicClosure C N = (⊥ : IntermediateField C N))
    (n : ℕ) (hn : 0 < n) :
    let g := FunctionField.genus C N
    let H := (g + 1) * (g + 2)
    let D := Module.finrank (RatFunc C) N
    let p := ringChar C
    let : CharP C p := ringChar.charP C
    let : Fact p.Prime := ⟨CharP.char_is_prime C p⟩
    let : NeZero (2 * (H * n)) := ⟨by positivity⟩
    let Cbig := FiniteField.Extension C p (2 * (H * n))
    let : Fintype Cbig := Fintype.ofFinite Cbig
    |(exactConstantExtensionClosedPlaceExtensionCount C Cbig M hExactM 1 : ℝ) -
        (Nat.card C : ℝ) ^ (2 * H * n) - 1| ≤
      2 * (D : ℝ) ^ 2 + 2 * (D : ℝ) ^ 3 +
        (D : ℝ) ^ 2 * (2 * g + 1) * (Nat.card C : ℝ) ^ (H * n) := by
  classical
  intro g H D p charP primeP neBig Cbig fintypeBig
  have hH : 0 < H := by positivity
  have hD : 0 < D := Module.finrank_pos
  let : NeZero (H * n) := ⟨Nat.mul_pos hH hn |>.ne'⟩
  let Ksmall := FiniteField.Extension C p (H * n)
  let : Fintype Ksmall := Fintype.ofFinite Ksmall
  let : DecidableEq Cbig := Classical.decEq Cbig
  let : DecidableEq (RatFunc Cbig) := Classical.decEq (RatFunc Cbig)
  let : Algebra C Ksmall :=
    FiniteField.instAlgebraExtension C p (H * n)
  let : Algebra C Cbig :=
    FiniteField.instAlgebraExtension C p (2 * (H * n))
  let : SMul C Ksmall := Algebra.toSMul
  let : Module C Ksmall := Algebra.toModule
  let : SMul C Cbig := Algebra.toSMul
  let : Module C Cbig := Algebra.toModule
  let : CharP Cbig p :=
    charP_of_injective_algebraMap (algebraMap C Cbig).injective p
  let : Algebra Ksmall Cbig :=
    finiteFieldExtensionAlgebraOfDvd C p (H * n) (2 * (H * n))
      ⟨2, by omega⟩
  let : SMul Ksmall Cbig := Algebra.toSMul
  let : Module Ksmall Cbig := Algebra.toModule
  let : IsScalarTower C Ksmall Cbig :=
    finiteFieldExtension_isScalarTower_of_dvd C p
      (H * n) (2 * (H * n)) ⟨2, by omega⟩
  have hcard : Fintype.card Cbig = Fintype.card Ksmall ^ 2 := by
    simpa only [Fintype.card_eq_nat_card] using
      natCard_double_finiteFieldExtension_eq_sq C p (H * n)
  have hlargeBase : H ≤ Fintype.card Ksmall := by
    simpa only [Fintype.card_eq_nat_card] using
      degree_le_natCard_finiteFieldExtension_mul C p H n hn
  let E_N := ExactConstantExtension C N Cbig
  let E_M := ExactConstantExtension C M Cbig
  let : Field E_N :=
    exactConstantExtensionField C N Cbig hExactN
  let : Field E_M :=
    exactConstantExtensionField C M Cbig hExactM
  let : Algebra (RatFunc Cbig) E_N :=
    ratFuncExactConstantExtensionAlgebra C Cbig N hExactN
  let : Algebra (RatFunc Cbig) E_M :=
    ratFuncExactConstantExtensionAlgebra C Cbig M hExactM
  let : Module (RatFunc Cbig) E_N := Algebra.toModule
  let : Module (RatFunc Cbig) E_M := Algebra.toModule
  let : FiniteDimensional (RatFunc Cbig) E_N :=
    finiteDimensional_over_extendedRatFunc C Cbig N hExactN
  let : FiniteDimensional (RatFunc Cbig) E_M :=
    finiteDimensional_over_extendedRatFunc C Cbig M hExactM
  let : Algebra.IsSeparable (RatFunc Cbig) E_N :=
    isSeparable_over_extendedRatFunc C Cbig N hExactN
  let : Algebra.IsSeparable (RatFunc Cbig) E_M :=
    isSeparable_over_extendedRatFunc C Cbig M hExactM
  let : Algebra E_M E_N :=
    exactConstantExtensionTowerRatFuncAlgebra C M N Cbig
  let : SMul (RatFunc Cbig) E_M := Algebra.toSMul
  let : SMul (RatFunc Cbig) E_N := Algebra.toSMul
  let : SMul E_M E_N := Algebra.toSMul
  let : Module E_M E_N := Algebra.toModule
  let : IsScalarTower (RatFunc Cbig) E_M E_N :=
    exactConstantExtensionTower_ratFuncScalarTower C M N Cbig hExactN
  let : Module.Finite E_M E_N :=
    exactConstantExtensionTower_finiteDimensional C M N Cbig hExactN
  let : IsGalois E_M E_N :=
    exactConstantExtensionTower_isGalois C M N Cbig hExactN
  let : Algebra (RatFunc C) (RatFunc Cbig) :=
    ratFuncCoefficientAlgebra C Cbig
  let : Algebra (RatFunc C) E_N :=
    exactConstantExtensionBaseAlgebra C (RatFunc C) N Cbig
  let : SMul (RatFunc C) (RatFunc Cbig) := Algebra.toSMul
  let : SMul (RatFunc C) E_N := Algebra.toSMul
  let : Module (RatFunc C) E_N := Algebra.toModule
  let : IsScalarTower (RatFunc C) (RatFunc Cbig) E_N :=
    rationalBase_scalarTower C Cbig N hExactN
  let : IsGalois (RatFunc C) E_N :=
    exactConstantExtension_isGalois C (RatFunc C) N Cbig hExactN
  let : IsGalois (RatFunc Cbig) E_N :=
    IsGalois.tower_top_of_isGalois (RatFunc C) (RatFunc Cbig) E_N
  have hExactEN :
      @algebraicClosure Cbig E_N _ _ (bridgeBaseConstantAlgebra Cbig E_N) =
        (⊥ : @IntermediateField Cbig E_N _ _
          (bridgeBaseConstantAlgebra Cbig E_N)) :=
    exactConstantExtension_extended_algebraicClosure_eq_bot
      C Cbig N hExactN
  have hgenusEN :
      @FunctionField.genus Cbig E_N _ _
        (bridgeBaseConstantAlgebra Cbig E_N) = g := by
    simpa only [E_N, g] using
      exactConstantExtension_genus_eq_for_ratFunc C Cbig N hExactN
  have hdegreeEN : Module.finrank (RatFunc Cbig) E_N = D :=
    exactConstantExtension_finrank_over_extendedRatFunc_eq
      C Cbig N hExactN
  have hHg : H = (g + 1) * (g + 2) := rfl
  have hlarge :
      (@FunctionField.genus Cbig E_N _ _
          (bridgeBaseConstantAlgebra Cbig E_N) + 1) *
        (@FunctionField.genus Cbig E_N _ _
          (bridgeBaseConstantAlgebra Cbig E_N) + 2) ≤
          Fintype.card Ksmall := by
    simpa only [hgenusEN, hHg] using hlargeBase
  let : NeZero D.factorial := ⟨Nat.factorial_ne_zero D⟩
  let U := FiniteField.Extension Cbig p D.factorial
  let : DecidableEq U := Classical.decEq U
  let : DecidableEq (RatFunc U) := Classical.decEq (RatFunc U)
  let : Algebra Cbig U :=
    FiniteField.instAlgebraExtension Cbig p D.factorial
  let : SMul Cbig U := Algebra.toSMul
  let : Module Cbig U := Algebra.toModule
  have hauxDegree : Module.finrank Cbig U = D.factorial := by
    simpa only [U] using FiniteField.finrank_extension Cbig p D.factorial
  have hdivBase : Nat.card (E_N ≃ₐ[RatFunc Cbig] E_N) ∣
      Module.finrank Cbig U := by
    rw [hauxDegree, IsGalois.card_aut_eq_finrank, hdegreeEN]
    exact Nat.dvd_factorial hD le_rfl
  have hdivMOriginal : Nat.card (N ≃ₐ[M] N) ∣ D.factorial :=
    natCard_aut_dvd_finrank_factorial_of_tower (RatFunc C) M N
  have hcardTower : Nat.card (E_N ≃ₐ[E_M] E_N) =
      Nat.card (N ≃ₐ[M] N) :=
    exactConstantExtensionTower_card_aut_eq C M N Cbig hExactN
  have hdivL : Nat.card (E_N ≃ₐ[E_M] E_N) ∣
      Module.finrank Cbig U := by
    rw [hauxDegree, hcardTower]
    exact hdivMOriginal
  have hfixed :=
    abs_intermediateBaseRationalPlaceError_le_squareField_of_genus
      Ksmall Cbig U E_N E_M hcard hExactEN hdivL hdivBase hlarge
  have hcount : exactConstantExtensionClosedPlaceExtensionCount C Cbig M hExactM 1 =
      finiteExtensionRationalPlaceCount Cbig E_M :=
    exactConstantExtensionClosedPlaceExtensionCount_one_eq_rationalPlaceCount
      C Cbig M hExactM
  have hcardBig : Nat.card Cbig = Nat.card C ^ (2 * H * n) := by
    simpa only [Cbig, Nat.mul_assoc] using
      FiniteField.natCard_extension C p (2 * (H * n))
  have hcardSmall : Fintype.card Ksmall = Nat.card C ^ (H * n) := by
    rw [Fintype.card_eq_nat_card,
      FiniteField.natCard_extension C p (H * n)]
  rw [← hcount, hcardBig, hdegreeEN, hgenusEN, hcardSmall] at hfixed
  push_cast at hfixed
  simpa only [mul_assoc] using hfixed

end GenericGaloisTowerBound

/-- The normal-closure constant field gives a uniform square-root-scale bound
for the packaged exact constant extensions of the original function field.

Here `H = (g + 1)(g + 2)` is the Stepanov threshold for the genus `g` of the
geometric normal closure, while `D` is its degree over the rational function
field of its full constant field. -/
theorem exactConstantExtensionClosedPlaceError_le_normalClosureConstants
    (hExact : algebraicClosure K F =
      (⊥ : IntermediateField K F)) :
    ∀ n, 0 < n →
      |(exactConstantExtensionClosedPlaceExtensionCount
          K (FunctionFieldNormalClosureConstantField K F) F hExact
            (2 * functionFieldNormalClosureStepanovThreshold K F * n) : ℝ) -
          (Nat.card (FunctionFieldNormalClosureConstantField K F) : ℝ) ^
            (2 * functionFieldNormalClosureStepanovThreshold K F * n) - 1| ≤
        2 * (functionFieldNormalClosureRatFuncDegree K F : ℝ) ^ 2 +
          2 * (functionFieldNormalClosureRatFuncDegree K F : ℝ) ^ 3 +
          (functionFieldNormalClosureRatFuncDegree K F : ℝ) ^ 2 *
            (2 * functionFieldNormalClosureGenus K F + 1) *
            (Nat.card (FunctionFieldNormalClosureConstantField K F) : ℝ) ^
              (functionFieldNormalClosureStepanovThreshold K F * n) := by
  classical
  intro n hn
  let C := FunctionFieldNormalClosureConstantField K F
  let : Fintype C :=
    finiteExtensionHasseNormalClosureConstantFintype K F
  let : DecidableEq C :=
    finiteExtensionHasseNormalClosureConstantDecidableEq K F
  let : DecidableEq (RatFunc C) :=
    finiteExtensionHasseNormalClosureRatFuncDecidableEq K F
  let N := FunctionFieldNormalClosure K F
  let M := FunctionFieldNormalClosureOriginalCompositum K F hExact
  let : Algebra (RatFunc C) M :=
    functionFieldNormalClosureOriginalCompositumConstantRatFuncAlgebra
      K F hExact
  let : SMul (RatFunc C) M := Algebra.toSMul
  let : Module (RatFunc C) M := Algebra.toModule
  let : Algebra C M :=
    exactConstantExtensionTowerCanonicalConstantAlgebra C M
  let : IsScalarTower (RatFunc C) M N :=
    functionFieldNormalClosureOriginalCompositumConstantRatFuncTower
      K F hExact
  let : FiniteDimensional (RatFunc C) M :=
    functionFieldNormalClosureOriginalCompositum_finiteDimensional_over_constantRatFunc
      K F hExact
  let : FiniteDimensional M N :=
    functionFieldNormalClosure_finiteDimensional_over_originalCompositum
      K F hExact
  let : IsGalois M N :=
    functionFieldNormalClosure_isGalois_over_originalCompositum K F hExact
  let : Algebra.IsSeparable (RatFunc C) M :=
    functionFieldNormalClosureOriginalCompositum_isSeparable_over_constantRatFunc
      K F hExact
  let normalClosureGalois : IsGalois (RatFunc C) N :=
    functionFieldNormalClosure_isGalois_over_constantRatFunc K F
  let : Algebra.IsSeparable (RatFunc C) N :=
    (isGalois_iff.mp normalClosureGalois).1
  let g := functionFieldNormalClosureGenus K F
  let H := functionFieldNormalClosureStepanovThreshold K F
  let D := functionFieldNormalClosureRatFuncDegree K F
  have hH : 0 < H := functionFieldNormalClosureStepanovThreshold_pos K F
  have hExactN : algebraicClosure C N = (⊥ : IntermediateField C N) :=
    functionFieldNormalClosureConstantField_isExact_for_constantRatFunc K F
  have hExactM : algebraicClosure C M = (⊥ : IntermediateField C M) :=
    functionFieldNormalClosureOriginalCompositumConstantField_isExact_for_constantRatFunc
      K F hExact
  let p := ringChar C
  let : CharP C p := ringChar.charP C
  let : Fact p.Prime := ⟨CharP.char_is_prime C p⟩
  let : NeZero (2 * (H * n)) := ⟨by positivity⟩
  let Cbig := FiniteField.Extension C p (2 * (H * n))
  let : Fintype Cbig := Fintype.ofFinite Cbig
  let : Algebra C Cbig := FiniteField.instAlgebraExtension C p (2 * (H * n))
  have hfixed := exactConstantExtensionClosedPlaceError_le_galoisTowerConstants
    C M N hExactM hExactN n hn
  have hcount : exactConstantExtensionClosedPlaceExtensionCount C Cbig M hExactM 1 =
      exactConstantExtensionClosedPlaceExtensionCount K C F hExact (2 * H * n) := by
    have htransport :=
      (normalClosureOriginalCompositum_rationalPlaceCount_eq_exactExtensionCount
        K F Cbig hExact).symm.trans
        (normalClosureOriginalCompositum_rationalPlaceCount_eq_originalExactExtensionCount
          K F Cbig hExact)
    convert htransport using 2
    simpa only [Cbig, Nat.mul_assoc] using
      (FiniteField.finrank_extension C p (2 * (H * n))).symm
  change |(exactConstantExtensionClosedPlaceExtensionCount C Cbig M hExactM 1 : ℝ) -
      (Nat.card C : ℝ) ^ (2 * H * n) - 1| ≤
    2 * (D : ℝ) ^ 2 + 2 * (D : ℝ) ^ 3 +
      (D : ℝ) ^ 2 * (2 * g + 1) * (Nat.card C : ℝ) ^ (H * n) at hfixed
  rw [hcount] at hfixed
  exact hfixed

/-- The closed Hasse--Weil bound for a finite separable extension of `K(X)`
with exact constant field `K`. -/
theorem finiteExtensionClosedPlaceHasseWeil
    (hExact : algebraicClosure K F =
      (⊥ : IntermediateField K F)) :
    |(finiteExtensionClosedPlaceExtensionCount K F 1 : ℝ) -
        Nat.card K - 1| ≤
      (2 * FunctionField.genus K F + 1 : ℝ) *
        Real.sqrt (Nat.card K) := by
  classical
  let C := FunctionFieldNormalClosureConstantField K F
  let : Fintype C :=
    finiteExtensionHasseNormalClosureConstantFintype K F
  let : DecidableEq C :=
    finiteExtensionHasseNormalClosureConstantDecidableEq K F
  let : DecidableEq (RatFunc C) :=
    finiteExtensionHasseNormalClosureRatFuncDecidableEq K F
  let g := functionFieldNormalClosureGenus K F
  let H := functionFieldNormalClosureStepanovThreshold K F
  let D := functionFieldNormalClosureRatFuncDegree K F
  let A : ℝ := 2 * (D : ℝ) ^ 2 + 2 * (D : ℝ) ^ 3
  let B : ℝ := (D : ℝ) ^ 2 * (2 * g + 1)
  have hH : 0 < H := functionFieldNormalClosureStepanovThreshold_pos K F
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hbound : ∀ n, 0 < n →
      |(exactConstantExtensionClosedPlaceExtensionCount
          K C F hExact (2 * H * n) : ℝ) -
          (Nat.card C : ℝ) ^ (2 * H * n) - 1| ≤
        A + B * (Nat.card C : ℝ) ^ (H * n) := by
    intro n hn
    have h := exactConstantExtensionClosedPlaceError_le_normalClosureConstants
      K F hExact n hn
    simpa only [C, g, H, D, A, B] using h
  exact finiteExtensionClosedPlaceHasseBound_of_constantBase_bound
    K C F (FunctionField.genus K F) hExact le_rfl H hH A B hA hbound

end

end BGS.HasseWeil
