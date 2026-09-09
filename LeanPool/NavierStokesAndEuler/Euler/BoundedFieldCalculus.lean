/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathCalculus
public import LeanPool.NavierStokesAndEuler.Euler.TransverseGramInverse
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Actual bounded-field bilinear and adjoint calculus

Pointwise application/composition are bounded bilinear maps in the genuine
uniform field norm, including on a noncompact spatial domain. Lifting these
maps to compact time paths preserves their norm bounds. These are the
coefficient maps used to construct the actual source forward generator.
-/

@[expose] public section


noncomputable section

namespace EulerBoundedFieldCalculus

open ContinuousLinearMap EulerTransverseGramInverse EulerOperatorGevreyCalculus EulerGevrey
open scoped BoundedContinuousFunction ContDiff

variable {α : Type*} [TopologicalSpace α]

section Bilinear

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Cache the standard `NormedAddCommGroup (F →L[ℝ] G)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus1 : NormedAddCommGroup (F →L[ℝ] G) := inferInstance
/-- Cache the standard `NormedSpace ℝ (F →L[ℝ] G)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus2 : NormedSpace ℝ (F →L[ℝ] G) := inferInstance
/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] F →L[ℝ] G)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus3 : NormedAddCommGroup (E →L[ℝ] F →L[ℝ] G) := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] F →L[ℝ] G)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus4 : NormedSpace ℝ (E →L[ℝ] F →L[ℝ] G) := inferInstance
/-- Cache the standard `NormedAddCommGroup (α →ᵇ E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus5 : NormedAddCommGroup (α →ᵇ E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (α →ᵇ E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus6 : NormedSpace ℝ (α →ᵇ E) := inferInstance
/-- Cache the standard `NormedAddCommGroup (α →ᵇ F)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus7 : NormedAddCommGroup (α →ᵇ F) := inferInstance
/-- Cache the standard `NormedSpace ℝ (α →ᵇ F)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus8 : NormedSpace ℝ (α →ᵇ F) := inferInstance
/-- Cache the standard `NormedAddCommGroup (α →ᵇ G)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus9 : NormedAddCommGroup (α →ᵇ G) := inferInstance
/-- Cache the standard `NormedSpace ℝ (α →ᵇ G)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus10 : NormedSpace ℝ (α →ᵇ G) := inferInstance

/-- The literal pointwise bounded bilinear field. -/
def bilinearValue (B : E →L[ℝ] F →L[ℝ] G) (f : α →ᵇ E) (g : α →ᵇ F) : α →ᵇ G :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => B (f x) (g x))
    ((B.continuous.comp f.continuous).clm_apply g.continuous) (‖B‖*‖f‖*‖g‖)
    (fun x => (B.le_opNorm₂ (f x) (g x)).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg B))
        (g.norm_coe_le_norm x) (norm_nonneg _) (mul_nonneg (norm_nonneg B) (norm_nonneg f))))

@[simp] theorem bilinearValue_apply (B : E →L[ℝ] F →L[ℝ] G) (f : α →ᵇ E) (g : α →ᵇ F) (x : α) :
    bilinearValue B f g x = B (f x) (g x) := rfl

theorem bilinearValue_norm (B : E →L[ℝ] F →L[ℝ] G) (f : α →ᵇ E) (g : α →ᵇ F) :
    ‖bilinearValue B f g‖ ≤ ‖B‖*‖f‖*‖g‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by positivity) _

/-- Bilinearity is proved on the actual coefficient functions. -/
def bilinearLinear (B : E →L[ℝ] F →L[ℝ] G) : (α →ᵇ E) →ₗ[ℝ] (α →ᵇ F) →ₗ[ℝ] (α →ᵇ G) where
  toFun f :=
    { toFun := bilinearValue B f
      map_add' g h := by
        apply BoundedContinuousFunction.ext
        intro x
        exact map_add (B (f x)) (g x) (h x)
      map_smul' r g := by
        apply BoundedContinuousFunction.ext
        intro x
        exact map_smul (B (f x)) r (g x) }
  map_add' f g := by
    apply LinearMap.ext
    intro h
    apply BoundedContinuousFunction.ext
    intro x
    exact congrArg (fun L : F →L[ℝ] G => L (h x)) (map_add B (f x) (g x))
  map_smul' r f := by
    apply LinearMap.ext
    intro h
    apply BoundedContinuousFunction.ext
    intro x
    exact congrArg (fun L : F →L[ℝ] G => L (h x)) (map_smul B r (f x))

/-- The actual bilinear map on bounded continuous fields. -/
def bilinearMap (B : E →L[ℝ] F →L[ℝ] G) : (α →ᵇ E) →L[ℝ] (α →ᵇ F) →L[ℝ] (α →ᵇ G) :=
  (bilinearLinear B).mkContinuous₂ ‖B‖ (bilinearValue_norm B)

@[simp] theorem bilinearMap_apply (B : E →L[ℝ] F →L[ℝ] G) (f : α →ᵇ E) (g : α →ᵇ F) (x : α) :
    bilinearMap B f g x = B (f x) (g x) := rfl

theorem bilinearMap_norm (B : E →L[ℝ] F →L[ℝ] G) : ‖bilinearMap (α := α) B‖ ≤ ‖B‖ :=
  (bilinearLinear B).mkContinuous₂_norm_le (norm_nonneg B) (bilinearValue_norm B)

/-- Pointwise postcomposition preserves the coefficient map's norm bound. -/
theorem postcomposition_norm (L : E →L[ℝ] F) : ‖L.compLeftContinuousBounded α‖ ≤ ‖L‖ := by
  apply opNorm_le_bound _ (norm_nonneg L)
  intro f
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg L) (norm_nonneg f))).2
  intro x
  exact (L.le_opNorm (f x)).trans (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg L))

end Bilinear

section Composition

variable {U E F : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Cache the standard `NormedAddCommGroup (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus11 : NormedAddCommGroup (U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus12 : NormedSpace ℝ (U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus13 : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus14 : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
/-- Cache the standard `NormedAddCommGroup (U →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus15 : NormedAddCommGroup (U →L[ℝ] F) := inferInstance
/-- Cache the standard `NormedSpace ℝ (U →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus16 : NormedSpace ℝ (U →L[ℝ] F) := inferInstance
/-- Cache the standard `NormedAddCommGroup (α →ᵇ U →L[ℝ] E)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus17 : NormedAddCommGroup (α →ᵇ U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (α →ᵇ U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus18 : NormedSpace ℝ (α →ᵇ U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedAddCommGroup (α →ᵇ E →L[ℝ] F)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus19 : NormedAddCommGroup (α →ᵇ E →L[ℝ] F) := inferInstance
/-- Cache the standard `NormedSpace ℝ (α →ᵇ E →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus20 : NormedSpace ℝ (α →ᵇ E →L[ℝ] F) := inferInstance
/-- Cache the standard `NormedAddCommGroup (α →ᵇ U →L[ℝ] F)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus21 : NormedAddCommGroup (α →ᵇ U →L[ℝ] F) := inferInstance
/-- Cache the standard `NormedSpace ℝ (α →ᵇ U →L[ℝ] F)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus22 : NormedSpace ℝ (α →ᵇ U →L[ℝ] F) := inferInstance
/-- Cache the standard `NormedAddCommGroup ((α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ U →L[ℝ] F))` instance
to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus23 : NormedAddCommGroup ((α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ U
    →L[ℝ] F)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ ((α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ U →L[ℝ] F))` instance to
shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus24 : NormedSpace ℝ ((α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ U →L[ℝ] F))
    := inferInstance

/-- The literal composition of two bounded operator fields. -/
def compositionMap : (α →ᵇ E →L[ℝ] F) →L[ℝ] (α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ U →L[ℝ] F) :=
  bilinearMap (compL ℝ U E F)

theorem compositionMap_norm : ‖compositionMap (α := α) (U := U) (E := E) (F := F)‖ ≤ 1 :=
  (bilinearMap_norm (compL ℝ U E F)).trans (norm_compL_le ℝ U E F)

@[simp] theorem compositionMap_apply (A : α →ᵇ E →L[ℝ] F) (B : α →ᵇ U →L[ℝ] E) (x : α) :
    compositionMap A B x = (A x).comp (B x) := rfl

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Cache the standard `NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus25 : NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] E)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus26 : NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] E)) := inferInstance
/-- Cache the standard `NormedAddCommGroup (C(K,α →ᵇ E →L[ℝ] F))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus27 : NormedAddCommGroup (C(K,α →ᵇ E →L[ℝ] F)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,α →ᵇ E →L[ℝ] F))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus28 : NormedSpace ℝ (C(K,α →ᵇ E →L[ℝ] F)) := inferInstance
/-- Cache the standard `NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] F))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus29 : NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] F)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] F))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus30 : NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] F)) := inferInstance
/-- Cache the standard `NormedAddCommGroup (C(K,(α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ U →L[ℝ] F)))`
instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus31 : NormedAddCommGroup (C(K,(α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ U
    →L[ℝ] F))) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,(α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ U →L[ℝ] F)))` instance
to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus32 : NormedSpace ℝ (C(K,(α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ U →L[ℝ]
    F))) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] E) →L[ℝ] C(K,α →ᵇ U →L[ℝ] F))`
instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus33 : NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] E) →L[ℝ] C(K,α →ᵇ
    U →L[ℝ] F)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] E) →L[ℝ] C(K,α →ᵇ U →L[ℝ] F))` instance
to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus34 : NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] E) →L[ℝ] C(K,α →ᵇ U
    →L[ℝ] F)) :=
    inferInstance

/-- Pointwise spatial composition, uniformly along a compact time path. -/
def pathCompositionMap : C(K,α →ᵇ E →L[ℝ] F) →L[ℝ]
    C(K,α →ᵇ U →L[ℝ] E) →L[ℝ] C(K,α →ᵇ U →L[ℝ] F) :=
  (EulerContinuousPathCalculus.coefficientMap (K := K)
    (E := α →ᵇ U →L[ℝ] E) (F := α →ᵇ U →L[ℝ] F)).comp
    ((compositionMap (α := α) (U := U) (E := E) (F := F)).compLeftContinuous ℝ K)

@[simp] theorem pathCompositionMap_apply (A : C(K, α →ᵇ E →L[ℝ] F))
    (B : C(K, α →ᵇ U →L[ℝ] E)) (t : K) (x : α) :
    pathCompositionMap A B t x = (A t x).comp (B t x) := rfl

theorem pathCompositionMap_norm : ‖pathCompositionMap (α := α) (K := K) (U := U) (E := E) (F := F)‖
    ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply opNorm_le_bound _ (norm_nonneg A)
  intro B
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg B))).2
  intro t
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg A) (norm_nonneg B))).2
  intro x
  exact (opNorm_comp_le (A t x) (B t x)).trans
    (mul_le_mul (((A t).norm_coe_le_norm x).trans (A.norm_coe_le_norm t))
      (((B t).norm_coe_le_norm x).trans (B.norm_coe_le_norm t)) (norm_nonneg _) (norm_nonneg A))

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Genuine smoothness of pointwise field composition in the uniform time-space norm. -/
theorem pathComposition_contDiff (A : P → C(K, α →ᵇ E →L[ℝ] F))
    (B : P → C(K, α →ᵇ U →L[ℝ] E)) {n : ℕ∞ω} (hA : ContDiff ℝ n A) (hB : ContDiff ℝ n B) :
    ContDiff ℝ n (fun y => pathCompositionMap (A y) (B y)) :=
  ((ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n)
    (E := C(K,α →ᵇ E →L[ℝ] F))
    (F := C(K,α →ᵇ U →L[ℝ] E) →L[ℝ] C(K,α →ᵇ U →L[ℝ] F))
    (pathCompositionMap (α := α) (K := K) (U := U) (E := E) (F := F))).comp hA).clm_apply hB

/-- The actual field product has the same factorial convolution bound. -/
theorem pathComposition_bound (A : P → C(K, α →ᵇ E →L[ℝ] F))
    (B : P → C(K, α →ᵇ U →L[ℝ] E)) (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    (R C D : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D) (c d : ℕ)
    (hbA : ∀ n x, ‖iteratedFDeriv ℝ n A x‖ ≤ C * majorant R c n)
    (hbB : ∀ n x, ‖iteratedFDeriv ℝ n B x‖ ≤ D * majorant R d n) (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => pathCompositionMap (A y) (B y)) x‖ ≤ (3*C*D)*majorant R (c+d) n :=
  bilinear_bound (pathCompositionMap (α := α) (K := K) (U := U) (E := E) (F := F))
    (pathCompositionMap_norm (α := α) (K := K) (U := U) (E := E) (F := F))
    A B hA hB R C D hR hC hD c d hbA hbB n x

end Composition

section Adjoint

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Cache the standard `NormedAddCommGroup (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus35 : NormedAddCommGroup (U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus36 : NormedSpace ℝ (U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus37 : NormedAddCommGroup (E →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus38 : NormedSpace ℝ (E →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedAddCommGroup (α →ᵇ U →L[ℝ] E)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus39 : NormedAddCommGroup (α →ᵇ U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (α →ᵇ U →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus40 : NormedSpace ℝ (α →ᵇ U →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedAddCommGroup (α →ᵇ E →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus41 : NormedAddCommGroup (α →ᵇ E →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedSpace ℝ (α →ᵇ E →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus42 : NormedSpace ℝ (α →ᵇ E →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedAddCommGroup ((α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ E →L[ℝ] U))` instance
to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus43 : NormedAddCommGroup ((α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ E
    →L[ℝ] U)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ ((α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ E →L[ℝ] U))` instance to
shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus44 : NormedSpace ℝ ((α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ E →L[ℝ] U))
    := inferInstance

/-- The actual adjoint of every bounded coefficient operator. -/
def adjointMap : (α →ᵇ U →L[ℝ] E) →L[ℝ] (α →ᵇ E →L[ℝ] U) :=
  (realAdjoint (U := U) (E := E)).compLeftContinuousBounded α

@[simp] theorem adjointMap_apply (A : α →ᵇ U →L[ℝ] E) (x : α) : adjointMap A x = (A x).adjoint :=
    rfl

theorem adjointMap_norm : ‖adjointMap (α := α) (U := U) (E := E)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply (BoundedContinuousFunction.norm_le (norm_nonneg A)).2
  intro x
  change ‖(A x).adjoint‖ ≤ ‖A‖
  rw [LinearIsometryEquiv.norm_map]
  exact A.norm_coe_le_norm x

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Cache the standard `NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus45 : NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] E)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] E))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus46 : NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] E)) := inferInstance
/-- Cache the standard `NormedAddCommGroup (C(K,α →ᵇ E →L[ℝ] U))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus47 : NormedAddCommGroup (C(K,α →ᵇ E →L[ℝ] U)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,α →ᵇ E →L[ℝ] U))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldCalculus48 : NormedSpace ℝ (C(K,α →ᵇ E →L[ℝ] U)) := inferInstance
/-- Cache the standard `NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] E) →L[ℝ] C(K,α →ᵇ E →L[ℝ] U))`
instance to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus49 : NormedAddCommGroup (C(K,α →ᵇ U →L[ℝ] E) →L[ℝ] C(K,α →ᵇ
    E →L[ℝ] U)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] E) →L[ℝ] C(K,α →ᵇ E →L[ℝ] U))` instance
to shorten typeclass synthesis. -/
local instance instBoundedFieldCalculus50 : NormedSpace ℝ (C(K,α →ᵇ U →L[ℝ] E) →L[ℝ] C(K,α →ᵇ E
    →L[ℝ] U)) :=
    inferInstance

/-- The bounded adjoint map on entire coefficient paths. -/
def pathAdjointMap : C(K,α →ᵇ U →L[ℝ] E) →L[ℝ] C(K,α →ᵇ E →L[ℝ] U) :=
  (adjointMap (α := α) (U := U) (E := E)).compLeftContinuous ℝ K

omit [CompactSpace K] in
@[simp] theorem pathAdjointMap_apply (A : C(K, α →ᵇ U →L[ℝ] E)) (t : K) (x : α) :
    pathAdjointMap A t x = (A t x).adjoint := rfl

theorem pathAdjointMap_norm : ‖pathAdjointMap (α := α) (K := K) (U := U) (E := E)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg A)).2
  intro t
  apply (BoundedContinuousFunction.norm_le (norm_nonneg A)).2
  intro x
  change ‖(A t x).adjoint‖ ≤ ‖A‖
  rw [LinearIsometryEquiv.norm_map]
  exact ((A t).norm_coe_le_norm x).trans (A.norm_coe_le_norm t)

end Adjoint

end EulerBoundedFieldCalculus
