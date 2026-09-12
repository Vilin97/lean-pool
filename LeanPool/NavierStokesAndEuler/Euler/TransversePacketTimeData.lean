/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketData
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import Mathlib.Analysis.Calculus.ContDiff.Operations
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothLimit
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPathJets
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
public import LeanPool.NavierStokesAndEuler.Euler.SourceNormalCoefficient
import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketPotentialMultiplier
public import LeanPool.NavierStokesAndEuler.Euler.TransverseGramInverse

/-! Time identities derived from the source deformation data, including the actual inverse and
normal paths. -/

section

/-! The actual time coefficient of the vector potential, with uniform factorial bounds. -/

section

/-! The vector-potential multiplier is a fixed linear contraction of the normal functional. -/

@[expose] public section

noncomputable section

namespace EulerPacketCrossProduct

open EulerSmoothLimit EulerTransverseGramInverse InnerProductSpace

/-- Normal vector, given by `(ContinuousLinearMap.apply ℝ Space (1 : ℝ)).comp (realAdjoint (U :=
Space) (E := ℝ))`. -/
def normalVector : (Space →L[ℝ] ℝ) →L[ℝ] Space :=
  (ContinuousLinearMap.apply ℝ Space (1 : ℝ)).comp (realAdjoint (U := Space) (E := ℝ))

@[simp] theorem normalVector_apply (N : Space →L[ℝ] ℝ) : normalVector N = N.adjoint 1 := rfl

/-- Normal potential map, given by `-(crossOperator.comp normalVector)`. -/
def normalPotentialMap : (Space →L[ℝ] ℝ) →L[ℝ] (Space →L[ℝ] Space) :=
  -(crossOperator.comp normalVector)

@[simp] theorem normalPotentialMap_apply (N : Space →L[ℝ] ℝ) :
    normalPotentialMap N = -crossLeft (N.adjoint 1) := rfl

theorem normalPotentialMap_norm : ‖normalPotentialMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro N
  simp only [normalPotentialMap_apply, norm_neg, one_mul]
  apply (crossLeft_norm_le (N.adjoint 1)).trans
  simpa only [norm_one, mul_one, LinearIsometryEquiv.norm_map] using N.adjoint.le_opNorm 1

theorem normalVector_eq (m : Space) (N : Space →L[ℝ] ℝ)
    (hN : ∀ v, N v = ⟪m, v⟫_ℝ / (‖m‖ ^ 2)) : N.adjoint 1 = ((‖m‖^2)⁻¹) • m := by
  apply ext_inner_right ℝ
  intro v
  rw [N.adjoint_inner_left, real_inner_smul_left]
  rw [Real.inner_apply, one_mul, hN, div_eq_mul_inv, mul_comm]

/-- No additional inverse or derivative estimate is needed after constructing the normal functional.
-/
theorem normalPotentialMap_eq (m : Space) (N : Space →L[ℝ] ℝ)
    (hN : ∀ v, N v = ⟪m, v⟫_ℝ / (‖m‖ ^ 2)) : normalPotentialMap N = potentialMultiplier m := by
  change -(crossOperator (N.adjoint 1)) = potentialMultiplier m
  rw [normalVector_eq m N hN, map_smul, crossOperator_apply]
  apply ContinuousLinearMap.ext
  intro v
  change -(((‖m‖^2)⁻¹) • crossLeft m v) = (-((‖m‖^2)⁻¹)) • crossLeft m v
  exact (neg_smul _ _).symm

end EulerPacketCrossProduct

end
end

end

section

/-! The literal vector-potential multiplier inherits the source normal coefficient bounds. -/

@[expose] public section

noncomputable section

namespace EulerSourcePotentialCoefficient

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerPacketCrossProduct
  EulerSourceNormalCoefficient EulerSourceForwardCoefficient EulerTimeLpGramGevrey EulerGevrey
open scoped BoundedContinuousFunction ContDiff

/-- Normal field: an abbreviation for `Space →ᵇ (Space →L[ℝ] ℝ)`. -/
abbrev NormalField := Space →ᵇ (Space →L[ℝ] ℝ)
/-- Potential field: an abbreviation for `Space →ᵇ (Space →L[ℝ] Space)`. -/
abbrev PotentialField := Space →ᵇ (Space →L[ℝ] Space)

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Cache the standard `NormedAddCommGroup NormalField` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialCoefficient1 : NormedAddCommGroup NormalField := inferInstance
/-- Cache the standard `NormedSpace ℝ NormalField` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialCoefficient2 : NormedSpace ℝ NormalField := inferInstance
/-- Cache the standard `NormedAddCommGroup PotentialField` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialCoefficient3 : NormedAddCommGroup PotentialField := inferInstance
/-- Cache the standard `NormedSpace ℝ PotentialField` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialCoefficient4 : NormedSpace ℝ PotentialField := inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,NormalField)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialCoefficient5 : NormedAddCommGroup C(K,NormalField) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,NormalField)` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialCoefficient6 : NormedSpace ℝ C(K,NormalField) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,PotentialField)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialCoefficient7 : NormedAddCommGroup C(K,PotentialField) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,PotentialField)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialCoefficient8 : NormedSpace ℝ C(K,PotentialField) := inferInstance

/-- Potential path map, given by `(normalPotentialMap.compLeftContinuousBounded
Space).compLeftContinuous ℝ K`. -/
def potentialPathMap : C(K,NormalField) →L[ℝ] C(K,PotentialField) :=
  (normalPotentialMap.compLeftContinuousBounded Space).compLeftContinuous ℝ K

omit [CompactSpace K] in
@[simp] theorem potentialPathMap_apply (N : C(K, NormalField)) (t : K) (x : Space) :
    potentialPathMap N t x = normalPotentialMap (N t x) := rfl

theorem potentialPathMap_norm : ‖potentialPathMap (K := K)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro N
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg N)).mpr
  intro t
  apply (BoundedContinuousFunction.norm_le (norm_nonneg N)).mpr
  intro x
  change ‖normalPotentialMap (N t x)‖ ≤ ‖N‖
  exact (normalPotentialMap.le_of_opNorm_le normalPotentialMap_norm (N t x)).trans
    (by simpa only [one_mul] using ((N t).norm_coe_le_norm x).trans (N.norm_coe_le_norm t))

variable (m : SmoothCoefficientPath K Space) (c : ℝ) (hc : 0 < c)
  (hm : ∀ t x, c ≤ ‖m.field t x‖ ^ 2)

/-- Potential coefficient, given by `potentialPathMap (normalFunctional m c hc hm)`. -/
def potentialCoefficient : C(K,PotentialField) :=
  potentialPathMap (normalFunctional m c hc hm)

theorem potentialCoefficient_apply (t : K) (x : Space) :
    potentialCoefficient m c hc hm t x = potentialMultiplier (m.field t x) :=
  normalPotentialMap_eq (m.field t x) (normalFunctional m c hc hm t x)
    (normalFunctional_apply m c hc hm t x)

theorem potentialCoefficient_translated (a : Space) :
    translateCoefficientPath (potentialCoefficient m c hc hm) a =
      potentialPathMap (translateCoefficientPath (normalFunctional m c hc hm) a) := by
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro x
  rfl

theorem potentialCoefficient_translation_contDiff :
    ContDiff ℝ ∞ (translateCoefficientPath (potentialCoefficient m c hc hm)) := by
  have he : translateCoefficientPath (potentialCoefficient m c hc hm) =
      fun a => potentialPathMap (translateCoefficientPath (normalFunctional m c hc hm) a) :=
    funext (potentialCoefficient_translated m c hc hm)
  rw [he]
  exact potentialPathMap.contDiff.comp (normalFunctional_translation_contDiff m c hc hm)

/-- The source coefficient passes through a linear contraction, with no radius or shift change. -/
theorem potentialCoefficient_translation_bound (Rc C Ri : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hRi : 2 * gramCost c C 1 * (Rc + 1) ≤ Ri)
    (hbm : ∀ n t x, ‖iteratedFDeriv ℝ n (m.field t : Space → Space) x‖ ≤ C * majorant Rc 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (potentialCoefficient m c hc hm)) a‖ ≤
      (3*Ri*C)*majorant (4*Ri) 0 n := by
  have he : translateCoefficientPath (potentialCoefficient m c hc hm) =
      fun a => potentialPathMap (translateCoefficientPath (normalFunctional m c hc hm) a) :=
    funext (potentialCoefficient_translated m c hc hm)
  rw [he]
  have h := (potentialPathMap (K := K)).norm_iteratedFDeriv_comp_left
    ((normalFunctional_translation_contDiff m c hc hm).contDiffAt (x := a)) (n := n) (by simp)
  exact h.trans ((mul_le_mul_of_nonneg_right (potentialPathMap_norm (K := K)) (norm_nonneg _)).trans
    (by
        simpa only [one_mul] using normalFunctional_translation_bound m c hc hm Rc C Ri hRc hC hRi
            hbm n a))

end EulerSourcePotentialCoefficient

end
end

end

section

/-! An inverse-free polynomial formula for the actual normal multiplier's time derivative. -/

@[expose] public section

noncomputable section

namespace EulerPacketCrossProduct

open ContinuousLinearMap InnerProductSpace EulerSmoothLimit

/-- Differentiate the normal functional using only itself and the normal's derivative column. -/
def normalTimeMap (N : Space →L[ℝ] ℝ) (Q₁ : ℝ →L[ℝ] Space) : Space →L[ℝ] ℝ :=
  (N.comp N.adjoint).comp Q₁.adjoint - (2 : ℝ) • (N.comp Q₁).comp N

theorem normalTimeMap_apply (m mt : Space) (N : Space →L[ℝ] ℝ) (hm : m ≠ 0)
    (hN : ∀ v, N v = ⟪m, v⟫_ℝ / ‖m‖ ^ 2) (v : Space) :
    normalTimeMap N (toSpanSingleton ℝ mt) v =
      ⟪mt,v⟫_ℝ / ‖m‖^2 - (2*⟪m,mt⟫_ℝ/(‖m‖^2)^2)*⟪m,v⟫_ℝ := by
  have hd : ‖m‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hm)
  have hNm : N m = 1 := by rw [hN, real_inner_self_eq_norm_sq, div_self hd]
  have hAdj (s : ℝ) : N.adjoint s = s • (((‖m‖^2)⁻¹) • m) := by
    calc
      N.adjoint s = N.adjoint (s • (1 : ℝ)) := by simp
      _ = s • N.adjoint 1 := map_smul N.adjoint s 1
      _ = _ := by rw [normalVector_eq m N hN]
  simp only [normalTimeMap, sub_apply, smul_apply, comp_apply, adjoint_toSpanSingleton,
    innerSL_apply_apply, toSpanSingleton_apply]
  rw [hAdj, map_smul, map_smul, hNm, map_smul, hN mt, hN v]
  simp only [smul_eq_mul, mul_one]
  field_simp

theorem normalTimeMap_vector (m mt : Space) (N : Space →L[ℝ] ℝ) (hm : m ≠ 0)
    (hN : ∀ v, N v = ⟪m, v⟫_ℝ / ‖m‖ ^ 2) :
    (normalTimeMap N (toSpanSingleton ℝ mt)).adjoint 1 =
      ((‖m‖^2)⁻¹) • mt - (2*⟪m,mt⟫_ℝ/(‖m‖^2)^2) • m := by
  apply ext_inner_right ℝ
  intro v
  rw [adjoint_inner_left, Real.inner_apply, one_mul, normalTimeMap_apply m mt N hm hN]
  simp only [inner_sub_left, real_inner_smul_left, div_eq_mul_inv]
  ring

/-- This polynomial coefficient is exactly the derivative of −cross(m)/|m|². -/
theorem normalTimeMap_potential (m mt : Space) (N : Space →L[ℝ] ℝ) (hm : m ≠ 0)
    (hN : ∀ v, N v = ⟪m, v⟫_ℝ / ‖m‖ ^ 2) :
    normalPotentialMap (normalTimeMap N (toSpanSingleton ℝ mt)) =
      potentialMultiplierDerivative m mt := by
  change -crossOperator ((normalTimeMap N (toSpanSingleton ℝ mt)).adjoint 1) = _
  rw [normalTimeMap_vector m mt N hm hN, map_sub, map_smul, map_smul, neg_sub]
  rfl

end EulerPacketCrossProduct

end
end

end

@[expose] public section

noncomputable section

namespace EulerSourcePotentialCoefficient

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanCoefficients
  EulerPacketCrossProduct EulerSourceNormalCoefficient EulerBoundedFieldCalculus
  EulerOperatorGevreyCalculus EulerGevrey EulerTimeLpGramGevrey EulerVolterraConvolution
open scoped BoundedContinuousFunction ContDiff

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] ℝ)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient1 : NormedAddCommGroup (Space →L[ℝ] ℝ) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] ℝ)` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialTimeCoefficient2 : NormedSpace ℝ (Space →L[ℝ] ℝ) := inferInstance
/-- Cache the standard `NormedAddCommGroup (ℝ →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient3 : NormedAddCommGroup (ℝ →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (ℝ →L[ℝ] Space)` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialTimeCoefficient4 : NormedSpace ℝ (ℝ →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup NormalField` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialTimeCoefficient5 : NormedAddCommGroup NormalField := inferInstance
/-- Cache the standard `NormedSpace ℝ NormalField` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialTimeCoefficient6 : NormedSpace ℝ NormalField := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ ℝ →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instSourcePotentialTimeCoefficient7 : NormedAddCommGroup (Space →ᵇ ℝ →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ ℝ →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient8 : NormedSpace ℝ (Space →ᵇ ℝ →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (ℝ →L[ℝ] ℝ)` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialTimeCoefficient9 : NormedAddCommGroup (ℝ →L[ℝ] ℝ) := inferInstance
/-- Cache the standard `NormedSpace ℝ (ℝ →L[ℝ] ℝ)` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialTimeCoefficient10 : NormedSpace ℝ (ℝ →L[ℝ] ℝ) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ ℝ →L[ℝ] ℝ)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient11 : NormedAddCommGroup (Space →ᵇ ℝ →L[ℝ] ℝ) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ ℝ →L[ℝ] ℝ)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient12 : NormedSpace ℝ (Space →ᵇ ℝ →L[ℝ] ℝ) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,NormalField)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient13 : NormedAddCommGroup C(K,NormalField) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,NormalField)` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialTimeCoefficient14 : NormedSpace ℝ C(K,NormalField) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,Space →ᵇ ℝ →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instSourcePotentialTimeCoefficient15 : NormedAddCommGroup C(K,Space →ᵇ ℝ →L[ℝ]
    Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,Space →ᵇ ℝ →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient16 : NormedSpace ℝ C(K,Space →ᵇ ℝ →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,Space →ᵇ ℝ →L[ℝ] ℝ)` instance to shorten
typeclass synthesis. -/
local instance instSourcePotentialTimeCoefficient17 : NormedAddCommGroup C(K,Space →ᵇ ℝ →L[ℝ] ℝ) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,Space →ᵇ ℝ →L[ℝ] ℝ)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient18 : NormedSpace ℝ C(K,Space →ᵇ ℝ →L[ℝ] ℝ) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient19 : NormedAddCommGroup (Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient20 : NormedSpace ℝ (Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup PotentialField` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient21 : NormedAddCommGroup PotentialField :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ PotentialField` instance to shorten typeclass synthesis. -/
local instance instSourcePotentialTimeCoefficient22 : NormedSpace ℝ PotentialField := inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,PotentialField)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient23 : NormedAddCommGroup C(K,PotentialField) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,PotentialField)` instance to shorten typeclass
synthesis. -/
local instance instSourcePotentialTimeCoefficient24 : NormedSpace ℝ C(K,PotentialField) :=
    inferInstance

/-- Time normal path, constructed using `pathCompositionMap`. -/
def timeNormalPath (N : C(K, NormalField)) (Q₁ : C(K, Space →ᵇ ℝ →L[ℝ] Space)) : C(K,NormalField) :=
  pathCompositionMap (pathCompositionMap N (pathAdjointMap N)) (pathAdjointMap Q₁) -
    (2 : ℝ) • pathCompositionMap (pathCompositionMap N Q₁) N

theorem timeNormalPath_apply (N : C(K, NormalField)) (Q₁ : C(K, Space →ᵇ ℝ →L[ℝ] Space))
    (t : K) (y : Space) : timeNormalPath N Q₁ t y = normalTimeMap (N t y) (Q₁ t y) := rfl

theorem timeNormalPath_translation (N : C(K, NormalField)) (Q₁ : C(K, Space →ᵇ ℝ →L[ℝ] Space))
    (a : Space) : translateCoefficientPath (timeNormalPath N Q₁) a =
      timeNormalPath (translateCoefficientPath N a) (translateCoefficientPath Q₁ a) := by
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro y
  rfl

section Families

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (N : X → C(K, NormalField)) (Q₁ : X → C(K, Space →ᵇ ℝ →L[ℝ] Space))
  (hN : ContDiff ℝ ∞ N) (hQ₁ : ContDiff ℝ ∞ Q₁)

include hN hQ₁ in
theorem timeNormalPath_contDiff : ContDiff ℝ ∞ (fun a => timeNormalPath (N a) (Q₁ a)) := by
  have hNa := (pathAdjointMap (α := Space) (K := K) (U := Space) (E := ℝ)).contDiff.comp hN
  have hQa := (pathAdjointMap (α := Space) (K := K) (U := ℝ) (E := Space)).contDiff.comp hQ₁
  have hNN := pathComposition_contDiff N (fun x => pathAdjointMap (N x)) hN hNa
  have hNQ := pathComposition_contDiff N Q₁ hN hQ₁
  have hA := pathComposition_contDiff
    (fun x => pathCompositionMap (N x) (pathAdjointMap (N x)))
    (fun x => pathAdjointMap (Q₁ x)) hNN hQa
  have hB := pathComposition_contDiff (fun x => pathCompositionMap (N x) (Q₁ x)) N hNQ hN
  exact hA.sub (hB.const_smul 2)

include hN hQ₁ in
theorem timeNormalPath_bound (R C D : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbN : ∀ n a, ‖iteratedFDeriv ℝ n N a‖ ≤ C * majorant R 0 n)
    (hbQ₁ : ∀ n a, ‖iteratedFDeriv ℝ n Q₁ a‖ ≤ D * majorant R 0 n)
    (n : ℕ) (a : X) :
    ‖iteratedFDeriv ℝ n (fun x => timeNormalPath (N x) (Q₁ x)) a‖ ≤
      (27*C^2*D)*majorant R 0 n := by
  let A : X → C(K,NormalField) := fun x =>
    pathCompositionMap (E := ℝ) (F := ℝ) (U := Space)
      (pathCompositionMap (E := Space) (F := ℝ) (U := ℝ)
        (N x) (pathAdjointMap (U := Space) (E := ℝ) (N x)))
      (pathAdjointMap (U := ℝ) (E := Space) (Q₁ x))
  let B : X → C(K,NormalField) := fun x =>
    pathCompositionMap (E := ℝ) (F := ℝ) (U := Space)
      (pathCompositionMap (E := Space) (F := ℝ) (U := ℝ) (N x) (Q₁ x)) (N x)
  have hNa := (pathAdjointMap (α := Space) (K := K) (U := Space) (E := ℝ)).contDiff.comp hN
  have hQa := (pathAdjointMap (α := Space) (K := K) (U := ℝ) (E := Space)).contDiff.comp hQ₁
  have hNN := pathComposition_contDiff N (fun x => pathAdjointMap (N x)) hN hNa
  have hNQ := pathComposition_contDiff N Q₁ hN hQ₁
  have hA : ContDiff ℝ ∞ A := pathComposition_contDiff _ _ hNN hQa
  have hB : ContDiff ℝ ∞ B := pathComposition_contDiff _ _ hNQ hN
  have hbNa := contraction_bound (pathAdjointMap (α := Space) (K := K) (U := Space) (E := ℝ))
    pathAdjointMap_norm N hN R C hR hC 0 hbN
  have hbQa := contraction_bound (pathAdjointMap (α := Space) (K := K) (U := ℝ) (E := Space))
    pathAdjointMap_norm Q₁ hQ₁ R D hR hD 0 hbQ₁
  have hbNN := pathComposition_bound N (fun x => pathAdjointMap (N x)) hN hNa
    R C C hR hC hC 0 0 hbN hbNa
  have hbNQ := pathComposition_bound N Q₁ hN hQ₁ R C D hR hC hD 0 0 hbN hbQ₁
  have hbA : ∀ j x, ‖iteratedFDeriv ℝ j A x‖ ≤ (3*(3*C*C)*D)*majorant R 0 j :=
    pathComposition_bound _ _ hNN hQa R (3*C*C) D hR (by positivity) hD 0 0 hbNN hbQa
  have hbB : ∀ j x, ‖iteratedFDeriv ℝ j B x‖ ≤ (3*(3*C*D)*C)*majorant R 0 j :=
    pathComposition_bound _ _ hNQ hN R (3*C*D) C hR (by positivity) hC 0 0 hbNQ hbN
  have hb₂B (j : ℕ) (x : X) :
      ‖iteratedFDeriv ℝ j (fun y => (2 : ℝ) • B y) x‖ ≤
        (2*(3*(3*C*D)*C))*majorant R 0 j := by
    rw [iteratedFDeriv_const_smul_apply' (hB.contDiffAt.of_le (by simp)), norm_smul]
    norm_num only [Real.norm_ofNat]
    exact (mul_le_mul_of_nonneg_left (hbB j x) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  have h := sub_bound A (fun y => (2 : ℝ) • B y) hA (hB.const_smul 2)
    R (3*(3*C*C)*D) (2*(3*(3*C*D)*C)) 0 hbA hb₂B n a
  exact h.trans_eq (by ring)

end Families

variable (m m₁ : SmoothCoefficientPath K Space) (c : ℝ) (hc : 0 < c)
  (hm : ∀ t y, c ≤ ‖m.field t y‖ ^ 2)

/-- Potential time coefficient, given by `potentialPathMap (timeNormalPath (normalFunctional m c
hc hm) (normalColumn m₁).field)`. -/
def potentialTimeCoefficient : C(K,PotentialField) :=
  potentialPathMap (timeNormalPath (normalFunctional m c hc hm) (normalColumn m₁).field)

theorem potentialTimeCoefficient_apply (t : K) (y : Space) :
    potentialTimeCoefficient m m₁ c hc hm t y =
      potentialMultiplierDerivative (m.field t y) (m₁.field t y) := by
  have hn : m.field t y ≠ 0 := by
    intro hz
    have h := hm t y
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
    linarith
  exact normalTimeMap_potential (m.field t y) (m₁.field t y)
    (normalFunctional m c hc hm t y) hn (normalFunctional_apply m c hc hm t y)

theorem potentialTimeCoefficient_translation :
    translateCoefficientPath (potentialTimeCoefficient m m₁ c hc hm) =
      fun a => potentialPathMap (timeNormalPath
        (translateCoefficientPath (normalFunctional m c hc hm) a)
        (translateCoefficientPath (normalColumn m₁).field a)) := by
  funext a
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro y
  rfl

theorem potentialTimeCoefficient_translation_contDiff :
    ContDiff ℝ ∞ (translateCoefficientPath (potentialTimeCoefficient m m₁ c hc hm)) := by
  rw [potentialTimeCoefficient_translation]
  have h := timeNormalPath_contDiff _ _
    (normalFunctional_translation_contDiff m c hc hm) (normalColumn m₁).translation_contDiff
  exact (potentialPathMap (K := K)).contDiff.comp h

/-- The derivative coefficient is polynomial in the already constructed normal functional. -/
theorem potentialTimeCoefficient_translation_bound (R C D : ℝ)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbN : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath (normalFunctional m c hc hm)) a‖ ≤
      C * majorant R 0 n)
    (hbm₁ : ∀ n t y, ‖iteratedFDeriv ℝ n (m₁.field t : Space → Space) y‖ ≤ D * majorant R 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (potentialTimeCoefficient m m₁ c hc hm)) a‖ ≤
      (27*C^2*D)*majorant R 0 n := by
  have hQ (j : ℕ) (x : Space) :
      ‖iteratedFDeriv ℝ j (translateCoefficientPath (normalColumn m₁).field) x‖ ≤ D*majorant R 0 j
          := by
    apply (normalColumn m₁).norm_iteratedFDeriv_translation_le j (D*majorant R 0 j)
      (mul_nonneg hD (majorant_nonneg R hR 0 j))
    intro t y
    exact SmoothCoefficientPath.map_derivative_bound
      (ContinuousLinearMap.toSpanSingletonLIE ℝ Space).toLinearIsometry.toContinuousLinearMap
      (ContinuousLinearMap.toSpanSingletonLIE ℝ
          Space).toLinearIsometry.norm_toContinuousLinearMap_le
      m₁ j (D*majorant R 0 j) (hbm₁ j) t y
  rw [potentialTimeCoefficient_translation]
  exact contraction_bound (potentialPathMap (K := K)) potentialPathMap_norm _
    (timeNormalPath_contDiff _ _ (normalFunctional_translation_contDiff m c hc hm)
      (normalColumn m₁).translation_contDiff) R (27*C^2*D) hR (by positivity) 0
    (timeNormalPath_bound _ _ (normalFunctional_translation_contDiff m c hc hm)
      (normalColumn m₁).translation_contDiff R C D hR hC hD hbN hQ) n a

end EulerSourcePotentialCoefficient

end
end

end

section

/-! The potential time coefficient from an actual continuous, translation-smooth normal derivative
path. -/

@[expose] public section

noncomputable section

namespace EulerSourcePotentialCoefficient

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerSourceNormalCoefficient
  EulerPacketCrossProduct EulerOperatorGevreyCalculus EulerGevrey EulerVolterraConvolution
open scoped ContDiff BoundedContinuousFunction

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Column path, given by `mapCoefficientPath (ContinuousLinearMap.toSpanSingletonLIE ℝ
Space).toLinearIsometry.toContinuousLinearMap`. -/
def columnPath : C(K,Space →ᵇ Space) →L[ℝ] C(K,Space →ᵇ ℝ →L[ℝ] Space) :=
  mapCoefficientPath (ContinuousLinearMap.toSpanSingletonLIE ℝ
      Space).toLinearIsometry.toContinuousLinearMap

theorem columnPath_norm : ‖columnPath (K := K)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg A)).mpr
  intro t
  apply (BoundedContinuousFunction.norm_le (norm_nonneg A)).mpr
  intro y
  change ‖(ContinuousLinearMap.toSpanSingletonLIE ℝ Space) (A t y)‖ ≤ ‖A‖
  rw [LinearIsometryEquiv.norm_map]
  exact ((A t).norm_coe_le_norm y).trans (A.norm_coe_le_norm t)

omit [CompactSpace K] in
theorem columnPath_translation (A : C(K, Space →ᵇ Space)) (a : Space) :
    translateCoefficientPath (columnPath A) a = columnPath (translateCoefficientPath A a) := by
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro y
  rfl

section Coefficient

variable (m : SmoothCoefficientPath K Space) (m₁ : C(K, Space →ᵇ Space))
  (c : ℝ) (hc : 0 < c) (hm : ∀ t y, c ≤ ‖m.field t y‖ ^ 2)

/-- Potential time path, given by `potentialPathMap (timeNormalPath (normalFunctional m c hc hm)
(columnPath m₁))`. -/
def potentialTimePath : C(K,PotentialField) :=
  potentialPathMap (timeNormalPath (normalFunctional m c hc hm) (columnPath m₁))

theorem potentialTimePath_apply (t : K) (y : Space) :
    potentialTimePath m m₁ c hc hm t y = potentialMultiplierDerivative (m.field t y) (m₁ t y) := by
  have hn : m.field t y ≠ 0 := by
    intro hz
    have h := hm t y
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
    linarith
  exact normalTimeMap_potential (m.field t y) (m₁ t y)
    (normalFunctional m c hc hm t y) hn (normalFunctional_apply m c hc hm t y)

theorem potentialTimePath_translation :
    translateCoefficientPath (potentialTimePath m m₁ c hc hm) = fun a =>
      potentialPathMap (timeNormalPath (translateCoefficientPath (normalFunctional m c hc hm) a)
        (columnPath (translateCoefficientPath m₁ a))) := by
  funext a
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro y
  rfl

theorem potentialTimePath_orbit (h₁ : ContDiff ℝ ∞ (translateCoefficientPath m₁)) :
    ContDiff ℝ ∞ (translateCoefficientPath (potentialTimePath m m₁ c hc hm)) := by
  rw [potentialTimePath_translation]
  have hcol := (columnPath (K := K)).contDiff.comp h₁
  have h := timeNormalPath_contDiff _ _ (normalFunctional_translation_contDiff m c hc hm) hcol
  exact (potentialPathMap (K := K)).contDiff.comp h

theorem potentialTimePath_bound (h₁ : ContDiff ℝ ∞ (translateCoefficientPath m₁))
    (R C D : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbN : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath (normalFunctional m c hc hm)) a‖ ≤
      C * majorant R 0 n)
    (hb₁ : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath m₁) a‖ ≤ D * majorant R 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (potentialTimePath m m₁ c hc hm)) a‖ ≤
      (27*C^2*D)*majorant R 0 n := by
  rw [potentialTimePath_translation]
  have hcol := (columnPath (K := K)).contDiff.comp h₁
  have hbcol := contraction_bound (columnPath (K := K)) columnPath_norm
    (translateCoefficientPath m₁) h₁ R D hR hD 0 hb₁
  have h := timeNormalPath_contDiff _ _ (normalFunctional_translation_contDiff m c hc hm) hcol
  exact contraction_bound (potentialPathMap (K := K)) potentialPathMap_norm _ h
    R (27*C^2*D) hR (by positivity) 0
    (timeNormalPath_bound _ _ (normalFunctional_translation_contDiff m c hc hm)
      hcol R C D hR hC hD hbN hbcol) n a

end Coefficient

section Time

variable (T : ℝ) (hT : 0 ≤ T) (m : SmoothCoefficientPath (Icc (0 : ℝ) T) Space)
  (m₁ : C(Icc (0 : ℝ) T, Space →ᵇ Space))
  (c : ℝ) (hc : 0 < c) (hm : ∀ t y, c ≤ ‖m.field t y‖ ^ 2)
  (hmt : ∀ t ∈ Icc (0 : ℝ) T, ∀ y : Space,
    HasDerivWithinAt (fun r => extendPath T hT m.field r y)
      (extendPath T hT m₁ t y) (Icc (0 : ℝ) T) t)

include hmt in
theorem potentialTimePath_hasDerivWithinAt (t : Icc (0 : ℝ) T) (y : Space) :
    HasDerivWithinAt (fun r => extendPath T hT (potentialCoefficient m c hc hm) r y)
      (potentialTimePath m m₁ c hc hm t y) (Icc (0 : ℝ) T) t := by
  have hn : extendPath T hT m.field t y ≠ 0 := by
    change m.field (projIcc 0 T hT t) y ≠ 0
    rw [projIcc_of_mem hT t.property]
    intro hz
    have h := hm t y
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
    linarith
  have h := potentialMultiplier_hasDerivWithinAt (Icc (0 : ℝ) T) t
    (fun r => extendPath T hT m.field r y) (extendPath T hT m₁ t y) (hmt t t.property y) hn
  convert h using 1 <;> try rfl
  · funext r
    exact potentialCoefficient_apply m c hc hm (projIcc 0 T hT r) y
  · rw [potentialTimePath_apply]
    change potentialMultiplierDerivative (m.field t y) (m₁ t y) =
      potentialMultiplierDerivative (m.field (projIcc 0 T hT t) y) (m₁ (projIcc 0 T hT t) y)
    rw [projIcc_of_mem hT t.property]

end Time
end EulerSourcePotentialCoefficient

end
end

end

section

/-! Genuine time derivatives of the inverse deformation and its transported normal. -/

@[expose] public section

noncomputable section

namespace EulerDeformationTime

open Set ContinuousLinearMap EulerSmoothLimit

/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instDeformationTimeInverse1 : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instDeformationTimeInverse2 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance

/-- Inverse unit, bundling `val`, `inv`, `val_inv`, `inv_val`. -/
def inverseUnit (F G : Space →L[ℝ] Space)
    (hFG : F.comp G = ContinuousLinearMap.id ℝ Space)
    (hGF : G.comp F = ContinuousLinearMap.id ℝ Space) : (Space →L[ℝ] Space)ˣ where
  val := F
  inv := G
  val_inv := hFG
  inv_val := hGF

theorem inverse_hasDerivWithinAt (s : Set ℝ) (t : ℝ) (ht : t ∈ s)
    (F G : ℝ → Space →L[ℝ] Space) (F₁ : Space →L[ℝ] Space)
    (hFG : ∀ r ∈ s, (F r).comp (G r) = ContinuousLinearMap.id ℝ Space)
    (hGF : ∀ r ∈ s, (G r).comp (F r) = ContinuousLinearMap.id ℝ Space)
    (hF : HasDerivWithinAt F F₁ s t) :
    HasDerivWithinAt G (-((G t).comp (F₁.comp (G t)))) s t := by
  have h := (hasFDerivAt_ringInverse (𝕜 := ℝ)
    (inverseUnit (F t) (G t) (hFG t ht) (hGF t ht))).comp_hasDerivWithinAt t hF
  change HasDerivWithinAt (fun r => Ring.inverse (F r)) (-((G t).comp (F₁.comp (G t)))) s t at h
  apply h.congr_of_mem _ ht
  intro r hr
  exact (Ring.inverse_unit (inverseUnit (F r) (G r) (hFG r hr) (hGF r hr))).symm

/-- F_t=MF implies (F⁻¹)_t=−F⁻¹M on the same closed time set. -/
theorem inverse_strain_hasDerivWithinAt (s : Set ℝ) (t : ℝ) (ht : t ∈ s)
    (F G : ℝ → Space →L[ℝ] Space) (M : Space →L[ℝ] Space)
    (hFG : ∀ r ∈ s, (F r).comp (G r) = ContinuousLinearMap.id ℝ Space)
    (hGF : ∀ r ∈ s, (G r).comp (F r) = ContinuousLinearMap.id ℝ Space)
    (hF : HasDerivWithinAt F (M.comp (F t)) s t) :
    HasDerivWithinAt G (-((G t).comp M)) s t := by
  have h := inverse_hasDerivWithinAt s t ht F G (M.comp (F t)) hFG hGF hF
  rwa [ContinuousLinearMap.comp_assoc M (F t) (G t), hFG t ht, ContinuousLinearMap.comp_id] at h

/-- Adjoint vector as an element of `(Space →L[ℝ] Space) →L[ℝ] Space`. -/
def adjointVector (m₀ : Space) : (Space →L[ℝ] Space) →L[ℝ] Space :=
  (ContinuousLinearMap.apply ℝ Space m₀).comp
    (ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
      : (Space →L[ℝ] Space) →L[ℝ] (Space →L[ℝ] Space))

/-- The actual transported normal satisfies m_t=−M* m. -/
theorem normal_hasDerivWithinAt (s : Set ℝ) (t : ℝ) (ht : t ∈ s)
    (F G : ℝ → Space →L[ℝ] Space) (M : Space →L[ℝ] Space) (m₀ : Space)
    (hFG : ∀ r ∈ s, (F r).comp (G r) = ContinuousLinearMap.id ℝ Space)
    (hGF : ∀ r ∈ s, (G r).comp (F r) = ContinuousLinearMap.id ℝ Space)
    (hF : HasDerivWithinAt F (M.comp (F t)) s t) :
    HasDerivWithinAt (fun r => (G r).adjoint m₀) (-(M.adjoint ((G t).adjoint m₀))) s t := by
  have h := (adjointVector m₀).hasFDerivAt.comp_hasDerivWithinAt t
    (inverse_strain_hasDerivWithinAt s t ht F G M hFG hGF hF)
  convert h using 1 <;> try rfl
  change -(M.adjoint ((G t).adjoint m₀)) = (-((G t).comp M)).adjoint m₀
  simp only [map_neg, adjoint_comp, neg_apply, comp_apply]

end EulerDeformationTime

end
end

end

@[expose] public section

noncomputable section

namespace EulerTransversePacketProvider.Data

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerTransverseBoundedFrame EulerBoundedFieldCalculus EulerOperatorGevreyCalculus
  EulerGevrey EulerSourcePotentialCoefficient EulerVolterraConvolution
open scoped ContDiff BoundedContinuousFunction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] (D : Data U)

/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketTimeData1 : NormedAddCommGroup (Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketTimeData2 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instTransversePacketTimeData3 : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instTransversePacketTimeData4 : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) D.T,Space →ᵇ Space →L[ℝ] Space)`
instance to shorten typeclass synthesis. -/
local instance instTransversePacketTimeData5 : NormedAddCommGroup C(Icc (0 : ℝ) D.T,Space →ᵇ Space
    →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) D.T,Space →ᵇ Space →L[ℝ] Space)` instance to
shorten typeclass synthesis. -/
local instance instTransversePacketTimeData6 : NormedSpace ℝ C(Icc (0 : ℝ) D.T,Space →ᵇ Space →L[ℝ]
    Space) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketTimeData7 : NormedAddCommGroup (Space →ᵇ Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space)` instance to shorten typeclass synthesis. -/
local instance instTransversePacketTimeData8 : NormedSpace ℝ (Space →ᵇ Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) D.T,Space →ᵇ Space)` instance to
shorten typeclass synthesis. -/
local instance instTransversePacketTimeData9 : NormedAddCommGroup C(Icc (0 : ℝ) D.T,Space →ᵇ Space)
    := inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) D.T,Space →ᵇ Space)` instance to shorten
typeclass synthesis. -/
local instance instTransversePacketTimeData10 : NormedSpace ℝ C(Icc (0 : ℝ) D.T,Space →ᵇ Space) :=
    inferInstance

/-- The derivative of the inverse is constructed from the original fields. -/
def inverseDerivative : C(Icc (0 : ℝ) D.T,Space →ᵇ Space →L[ℝ] Space) :=
  -pathCompositionMap D.FInv.field D.M.field

/-- The derivative of the transported normal is the fixed adjoint-vector map of that path. -/
def normalDerivative : C(Icc (0 : ℝ) D.T,Space →ᵇ Space) :=
  mapCoefficientPath (normalMap D.m₀) D.inverseDerivative

@[simp] theorem inverseDerivative_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    D.inverseDerivative t x = -((D.FInv.field t x).comp (D.M.field t x)) := rfl

@[simp] theorem normalDerivative_apply (t : Icc (0 : ℝ) D.T) (x : Space) :
    D.normalDerivative t x = -((D.M.field t x).adjoint (D.normal.field t x)) := by
  change (-((D.FInv.field t x).comp (D.M.field t x))).adjoint D.m₀ =
    -((D.M.field t x).adjoint ((D.FInv.field t x).adjoint D.m₀))
  simp only [map_neg, adjoint_comp, neg_apply, comp_apply]

/-- No differentiability of F⁻¹ is assumed: it follows from the actual inverse identities and
F_t=MF. -/
theorem inverse_hasDerivWithinAt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D.T) (x : Space) :
    HasDerivWithinAt (fun r => extendPath D.T D.T_pos.le D.FInv.field r x)
      (extendPath D.T D.T_pos.le D.inverseDerivative t x) (Icc (0 : ℝ) D.T) t := by
  have hFG (r : ℝ) (_hr : r ∈ Icc (0 : ℝ) D.T) :
      (extendPath D.T D.T_pos.le D.F.field r x).comp
        (extendPath D.T D.T_pos.le D.FInv.field r x) = ContinuousLinearMap.id ℝ Space := by
    apply ContinuousLinearMap.ext
    intro v
    exact D.inverse_right (projIcc 0 D.T D.T_pos.le r) x v
  have hGF (r : ℝ) (_hr : r ∈ Icc (0 : ℝ) D.T) :
      (extendPath D.T D.T_pos.le D.FInv.field r x).comp
        (extendPath D.T D.T_pos.le D.F.field r x) = ContinuousLinearMap.id ℝ Space := by
    apply ContinuousLinearMap.ext
    intro v
    exact D.inverse_left (projIcc 0 D.T D.T_pos.le r) x v
  have hF₁ : extendPath D.T D.T_pos.le D.F₁.field t x =
      (extendPath D.T D.T_pos.le D.M.field t x).comp
        (extendPath D.T D.T_pos.le D.F.field t x) := by
    apply ContinuousLinearMap.ext
    intro v
    exact D.strain_equation (projIcc 0 D.T D.T_pos.le t) x v
  have hF := D.frame_time t ht x
  rw [hF₁] at hF
  exact EulerDeformationTime.inverse_strain_hasDerivWithinAt (Icc (0 : ℝ) D.T) t ht
    (fun r => extendPath D.T D.T_pos.le D.F.field r x)
    (fun r => extendPath D.T D.T_pos.le D.FInv.field r x)
    (extendPath D.T D.T_pos.le D.M.field t x) hFG hGF hF

theorem normal_hasDerivWithinAt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D.T) (x : Space) :
    HasDerivWithinAt (fun r => extendPath D.T D.T_pos.le D.normal.field r x)
      (extendPath D.T D.T_pos.le D.normalDerivative t x) (Icc (0 : ℝ) D.T) t := by
  exact (normalMap D.m₀).hasFDerivAt.comp_hasDerivWithinAt t
    (D.inverse_hasDerivWithinAt t ht x)

theorem inverseDerivative_translation :
    translateCoefficientPath D.inverseDerivative = fun a =>
      -pathCompositionMap (translateCoefficientPath D.FInv.field a)
        (translateCoefficientPath D.M.field a) := by
  funext a
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro x
  rfl

theorem normalDerivative_translation :
    translateCoefficientPath D.normalDerivative = fun a =>
      mapCoefficientPath (normalMap D.m₀) (translateCoefficientPath D.inverseDerivative a) := by
  funext a
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro x
  rfl

theorem inverseDerivative_orbit : ContDiff ℝ ∞ (translateCoefficientPath D.inverseDerivative) := by
  rw [D.inverseDerivative_translation]
  exact (pathComposition_contDiff _ _ D.FInv.translation_contDiff D.M.translation_contDiff).neg

theorem normalDerivative_orbit : ContDiff ℝ ∞ (translateCoefficientPath D.normalDerivative) := by
  rw [D.normalDerivative_translation]
  exact (mapCoefficientPath (K := Icc (0 : ℝ) D.T) (normalMap D.m₀)).contDiff.comp
    D.inverseDerivative_orbit

theorem normalPathMap_norm :
    ‖mapCoefficientPath (K := Icc (0 : ℝ) D.T) (normalMap D.m₀)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg A)).mpr
  intro t
  apply (BoundedContinuousFunction.norm_le (norm_nonneg A)).mpr
  intro x
  change ‖normalMap D.m₀ (A t x)‖ ≤ ‖A‖
  calc
    _ ≤ ‖normalMap D.m₀‖ * ‖A t x‖ := (normalMap D.m₀).le_opNorm _
    _ ≤ 1 * ‖A t x‖ := mul_le_mul_of_nonneg_right (normalMap_norm D.m₀ D.m₀_unit) (norm_nonneg _)
    _ ≤ ‖A‖ := by simpa only [one_mul] using ((A t).norm_coe_le_norm x).trans (A.norm_coe_le_norm t)

theorem inverseDerivative_bound (R CI CM : ℝ) (hR : 0 ≤ R) (hCI : 0 ≤ CI) (hCM : 0 ≤ CM)
    (hI : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.FInv.field) a‖ ≤ CI * majorant R 0
        n)
    (hM : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.M.field) a‖ ≤ CM * majorant R 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath D.inverseDerivative) a‖ ≤ (3*CI*CM)*majorant R 0
        n := by
  rw [D.inverseDerivative_translation]
  exact neg_bound _ R (3*CI*CM) 0
    (pathComposition_bound _ _ D.FInv.translation_contDiff D.M.translation_contDiff
      R CI CM hR hCI hCM 0 0 hI hM) n a

theorem normalDerivative_bound (R CI CM : ℝ) (hR : 0 ≤ R) (hCI : 0 ≤ CI) (hCM : 0 ≤ CM)
    (hI : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.FInv.field) a‖ ≤ CI * majorant R 0
        n)
    (hM : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath D.M.field) a‖ ≤ CM * majorant R 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath D.normalDerivative) a‖ ≤ (3*CI*CM)*majorant R 0 n
        := by
  rw [D.normalDerivative_translation]
  exact contraction_bound (mapCoefficientPath (K := Icc (0 : ℝ) D.T) (normalMap D.m₀))
    D.normalPathMap_norm _ D.inverseDerivative_orbit R (3*CI*CM) hR (by positivity) 0
    (D.inverseDerivative_bound R CI CM hR hCI hCM hI hM) n a

/-- The actual time coefficient for the periodic-potential multiplier. -/
def potentialDerivative : C(Icc (0 : ℝ) D.T,PotentialField) :=
  potentialTimePath D.normal D.normalDerivative D.normalLower D.normalLower_pos D.normal_lower

theorem potentialDerivative_orbit : ContDiff ℝ ∞ (translateCoefficientPath D.potentialDerivative) :=
  potentialTimePath_orbit D.normal D.normalDerivative D.normalLower D.normalLower_pos D.normal_lower
    D.normalDerivative_orbit

theorem potential_hasDerivWithinAt (t : Icc (0 : ℝ) D.T) (x : Space) :
    HasDerivWithinAt (fun r => extendPath D.T D.T_pos.le
      (potentialCoefficient D.normal D.normalLower D.normalLower_pos D.normal_lower) r x)
      (D.potentialDerivative t x) (Icc (0 : ℝ) D.T) t := by
  convert potentialTimePath_hasDerivWithinAt D.T D.T_pos.le D.normal D.normalDerivative
    D.normalLower D.normalLower_pos D.normal_lower D.normal_hasDerivWithinAt t x using 1
  dsimp only [potentialDerivative]

end EulerTransversePacketProvider.Data
