/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import LeanPool.NavierStokesAndEuler.Euler.BoundedFieldCalculus
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeField

/-! Composition with identity plus a bounded smooth displacement preserves
the actual continuous-time bounded spatial jets. The finite Faà di Bruno
formula is evaluated in the sup norm, with no extra time derivative. -/

section

/-! Pullback of a bounded field by identity plus a bounded displacement.
Uniform spatial Lipschitz control proves continuity in the genuine sup norm. -/

@[expose] public section

noncomputable section

open scoped BoundedContinuousFunction ContDiff NNReal

namespace EulerBoundedFieldPullback

variable {E V : Type*} [NormedAddCommGroup E] [NormedAddCommGroup V]

/-- Pullback, constructed using `BoundedContinuousFunction.ofNormedAddCommGroup`. -/
def pullback (A : E →ᵇ V) (d : E →ᵇ E) : E →ᵇ V :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => A (x+d x))
    (A.continuous.comp (continuous_id.add d.continuous)) ‖A‖
    (fun x => A.norm_coe_le_norm (x+d x))

@[simp] theorem pullback_apply (A : E →ᵇ V) (d : E →ᵇ E) (x : E) :
    pullback A d x = A (x+d x) := rfl

theorem pullback_norm (A : E →ᵇ V) (d : E →ᵇ E) :
    ‖pullback A d‖ ≤ ‖A‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (norm_nonneg A) _

theorem pullback_sub_norm (A B : E →ᵇ V) (d e : E →ᵇ E)
    (L : ℝ≥0) (hL : LipschitzWith L A) :
    ‖pullback A d - pullback B e‖ ≤ ‖A-B‖ + L * ‖d-e‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).2
  intro x
  change ‖A (x+d x)-B (x+e x)‖ ≤ _
  calc
    _ ≤ ‖A (x+d x)-A (x+e x)‖ + ‖A (x+e x)-B (x+e x)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ L*‖d-e‖ + ‖A-B‖ := by
      apply add_le_add
      · have hh := hL.dist_le_mul (x+d x) (x+e x)
        rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub] at hh
        exact hh.trans (mul_le_mul_of_nonneg_left ((d-e).norm_coe_le_norm x) L.coe_nonneg)
      · exact (A-B).norm_coe_le_norm (x+e x)
    _ = _ := add_comm _ _

variable {K : Type*} [TopologicalSpace K]

theorem continuous_pullback (A : C(K, E →ᵇ V)) (d : C(K, E →ᵇ E))
    (L : ℝ≥0) (hL : ∀ t, LipschitzWith L (A t)) :
    Continuous (fun t => pullback (A t) (d t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun s => norm_nonneg _)
    (fun s => pullback_sub_norm (A s) (A t) (d s) (d t) L (hL s))
  have hzero : Filter.Tendsto
      (fun s => ‖A s-A t‖ + (L : ℝ)*‖d s-d t‖) (nhds t) (nhds 0) := by
    have hc : Continuous (fun s => ‖A s-A t‖ + (L : ℝ)*‖d s-d t‖) :=
      ((A.continuous.sub continuous_const).norm).add
        (continuous_const.mul ((d.continuous.sub continuous_const).norm))
    simpa only [sub_self, norm_zero, mul_zero, add_zero] using hc.tendsto t
  exact hzero

/-- Path pullback, given by `⟨fun t => pullback (A t) (d t), continuous_pullback A d L hL⟩`. -/
def pathPullback (A : C(K, E →ᵇ V)) (d : C(K, E →ᵇ E))
    (L : ℝ≥0) (hL : ∀ t, LipschitzWith L (A t)) : C(K,E →ᵇ V) :=
  ⟨fun t => pullback (A t) (d t), continuous_pullback A d L hL⟩

@[simp] theorem pathPullback_apply (A : C(K, E →ᵇ V)) (d : C(K, E →ᵇ E))
    (L : ℝ≥0) (hL : ∀ t, LipschitzWith L (A t)) (t : K) (x : E) :
    pathPullback A d L hL t x = A t (x+d t x) := rfl

end EulerBoundedFieldPullback

namespace SmoothTimeField

universe u

variable {K E V : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldPullback1 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] V) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldPullback2 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] V) := inferInstance
/-- Cache the standard `NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldPullback3 (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instBoundedFieldPullback4 (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance

theorem jet_lipschitz (A : SmoothTimeField K E V) (n : ℕ) (t : K) :
    LipschitzWith ‖A.jet (n+1)‖₊ (A.jet n t) := by
  have he : (A.jet n t : E → E [×n]→L[ℝ] V) =
      iteratedFDeriv ℝ n (A.field t : E → V) := funext (A.jet_eq n t)
  rw [he]
  apply lipschitzWith_of_nnnorm_fderiv_le
    (((A.smooth t).iteratedFDeriv_right (m := ∞) (by simp)).differentiable (by simp))
  intro x
  change ‖fderiv ℝ (iteratedFDeriv ℝ n (A.field t : E → V)) x‖ ≤ ‖A.jet (n+1)‖
  rw [norm_fderiv_iteratedFDeriv, ← A.jet_eq]
  exact ((A.jet (n+1) t).norm_coe_le_norm x).trans ((A.jet (n+1)).norm_coe_le_norm t)

end SmoothTimeField

end
end

end

section

/-! A continuous multilinear operation acts on genuine bounded fields in
the uniform norm. This includes the finite Faà di Bruno operations. -/

@[expose] public section

noncomputable section

open scoped BigOperators BoundedContinuousFunction

namespace EulerBoundedFieldCalculus

variable {α ι : Type*} [TopologicalSpace α] [Fintype ι]
  {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Cache the standard `NormedAddCommGroup (α →ᵇ V i)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldMultilinear1 (i : ι) : NormedAddCommGroup (α →ᵇ V i) := inferInstance
/-- Cache the standard `NormedSpace ℝ (α →ᵇ V i)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldMultilinear2 (i : ι) : NormedSpace ℝ (α →ᵇ V i) := inferInstance
/-- Cache the standard `NormedAddCommGroup (α →ᵇ W)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldMultilinear3 : NormedAddCommGroup (α →ᵇ W) := inferInstance
/-- Cache the standard `NormedSpace ℝ (α →ᵇ W)` instance to shorten typeclass synthesis. -/
local instance instBoundedFieldMultilinear4 : NormedSpace ℝ (α →ᵇ W) := inferInstance

/-- Multilinear value, constructed using `BoundedContinuousFunction.ofNormedAddCommGroup`. -/
def multilinearValue (L : ContinuousMultilinearMap ℝ V W)
    (f : ∀ i, α →ᵇ V i) : α →ᵇ W :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => L (fun i => f i x))
    (L.cont.comp (continuous_pi (fun i => (f i).continuous)))
    (‖L‖ * ∏ i, ‖f i‖) (fun x => (L.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          (fun i _ => (f i).norm_coe_le_norm x)) (norm_nonneg L)))

@[simp] theorem multilinearValue_apply (L : ContinuousMultilinearMap ℝ V W)
    (f : ∀ i, α →ᵇ V i) (x : α) :
    multilinearValue L f x = L (fun i => f i x) := rfl

theorem multilinearValue_norm (L : ContinuousMultilinearMap ℝ V W)
    (f : ∀ i, α →ᵇ V i) :
    ‖multilinearValue L f‖ ≤ ‖L‖ * ∏ i, ‖f i‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
    (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun _ _ => norm_nonneg _))) _

/-- Multilinear algebra as an element of `MultilinearMap ℝ (fun i => α →ᵇ V i) (α →ᵇ W)`. -/
def multilinearAlgebra (L : ContinuousMultilinearMap ℝ V W) :
    MultilinearMap ℝ (fun i => α →ᵇ V i) (α →ᵇ W) := by
  classical
  refine MultilinearMap.mk' (multilinearValue L) ?_ ?_
  · intro f i a b
    apply BoundedContinuousFunction.ext
    intro x
    change L (fun j => Function.update f i (a+b) j x) =
      L (fun j => Function.update f i a j x) + L (fun j => Function.update f i b j x)
    have he (c : α →ᵇ V i) :
        (fun j => Function.update f i c j x) =
          Function.update (fun j => f j x) i (c x) := by
      funext j
      by_cases hj : j = i
      · subst j; simp
      · simp [hj]
    simp only [he, BoundedContinuousFunction.add_apply]
    exact L.map_update_add _ _ _ _
  · intro f i r a
    apply BoundedContinuousFunction.ext
    intro x
    change L (fun j => Function.update f i (r • a) j x) =
      r • L (fun j => Function.update f i a j x)
    have he (c : α →ᵇ V i) :
        (fun j => Function.update f i c j x) =
          Function.update (fun j => f j x) i (c x) := by
      funext j
      by_cases hj : j = i
      · subst j; simp
      · simp [hj]
    simp only [he, BoundedContinuousFunction.smul_apply]
    exact L.map_update_smul _ _ _ _

/-- Multilinear map, given by `(multilinearAlgebra L).mkContinuous ‖L‖ (multilinearValue_norm
L)`. -/
def multilinearMap (L : ContinuousMultilinearMap ℝ V W) :
    ContinuousMultilinearMap ℝ (fun i => α →ᵇ V i) (α →ᵇ W) :=
  (multilinearAlgebra L).mkContinuous ‖L‖ (multilinearValue_norm L)

@[simp] theorem multilinearMap_apply (L : ContinuousMultilinearMap ℝ V W)
    (f : ∀ i, α →ᵇ V i) (x : α) :
    multilinearMap L f x = L (fun i => f i x) := rfl

theorem multilinearMap_norm (L : ContinuousMultilinearMap ℝ V W) :
    ‖multilinearMap (α := α) L‖ ≤ ‖L‖ :=
  (multilinearAlgebra L).mkContinuous_norm_le (norm_nonneg L) (multilinearValue_norm L)

end EulerBoundedFieldCalculus

end
end

end

@[expose] public section

noncomputable section

open scoped ContDiff BoundedContinuousFunction BigOperators NNReal

universe u

namespace SmoothTimeField

open EulerBoundedFieldPullback EulerBoundedFieldCalculus

variable {K E V : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Cache the standard `NormedAddCommGroup (E [×n]→L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeFieldComposition1 (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] V) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (E [×n]→L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instSmoothTimeFieldComposition2 (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] V) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeFieldComposition3 (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V))
    := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V))` instance to shorten typeclass
synthesis. -/
local instance instSmoothTimeFieldComposition4 (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V)) :=
    inferInstance

theorem field_lipschitz (A : SmoothTimeField K E V) (t : K) :
    LipschitzWith ‖A.jet 1‖₊ (A.field t) := by
  apply lipschitzWith_of_nnnorm_fderiv_le ((A.smooth t).differentiable (by simp))
  intro x
  change ‖fderiv ℝ (A.field t : E → V) x‖ ≤ ‖A.jet 1‖
  rw [← norm_iteratedFDeriv_one, ← A.jet_eq]
  exact ((A.jet 1 t).norm_coe_le_norm x).trans ((A.jet 1).norm_coe_le_norm t)

omit [TopologicalSpace K] [CompactSpace K] [NormedAddCommGroup V] [NormedSpace ℝ V] in
theorem positive_identity_jet (n : ℕ) (hn : 0 < n) (x : E) :
    iteratedFDeriv ℝ n (id : E → E) 0 = iteratedFDeriv ℝ n (id : E → E) x := by
  have hid : fderiv ℝ (id : E → E) = fun _ : E => ContinuousLinearMap.id ℝ E :=
    funext (fun _ => fderiv_id)
  cases n with
  | zero => omega
  | succ n =>
    simp only [Nat.succ_eq_add_one, iteratedFDeriv_succ_eq_comp_right, hid, Function.comp_apply]
    cases n with
    | zero => rfl
    | succ n => simp only [iteratedFDeriv_succ_const, Pi.zero_apply]

/-- Displaced jet, given by `ContinuousMap.const K (BoundedContinuousFunction.const E
(iteratedFDeriv ℝ n (id : E → E) 0)) + D.jet n`. -/
def displacedJet (D : SmoothTimeField K E E) (n : ℕ) :
    C(K,E →ᵇ (E [×n]→L[ℝ] E)) :=
  ContinuousMap.const K (BoundedContinuousFunction.const E
    (iteratedFDeriv ℝ n (id : E → E) 0)) + D.jet n

theorem displacedJet_apply (D : SmoothTimeField K E E) (n : ℕ) (hn : 0 < n)
    (t : K) (x : E) :
    displacedJet D n t x = iteratedFDeriv ℝ n (fun y => y+D.field t y) x := by
  change iteratedFDeriv ℝ n (id : E → E) 0 + D.jet n t x = _
  rw [positive_identity_jet n hn x, D.jet_eq]
  exact (iteratedFDeriv_add_apply contDiffAt_id ((D.smooth t).contDiffAt.of_le (by simp))).symm

/-- Pulled jet, given by `pathPullback (A.jet n) D.field ‖A.jet (n+1)‖₊ (A.jet_lipschitz n)`. -/
def pulledJet (A : SmoothTimeField K E V) (D : SmoothTimeField K E E) (n : ℕ) :
    C(K,E →ᵇ (E [×n]→L[ℝ] V)) :=
  pathPullback (A.jet n) D.field ‖A.jet (n+1)‖₊ (A.jet_lipschitz n)

@[simp] theorem pulledJet_apply (A : SmoothTimeField K E V) (D : SmoothTimeField K E E)
    (n : ℕ) (t : K) (x : E) :
    pulledJet A D n t x = iteratedFDeriv ℝ n (A.field t : E → V) (x+D.field t x) := by
  change A.jet n t (x+D.field t x) = _
  exact A.jet_eq n t _

/-- Partition jet as an element of `C(K,E →ᵇ (E [×n]→L[ℝ] V))`. -/
def partitionJet (A : SmoothTimeField K E V) (D : SmoothTimeField K E E)
    {n : ℕ} (c : OrderedFinpartition n) : C(K,E →ᵇ (E [×n]→L[ℝ] V)) := by
  let L := (c.compAlongOrderedFinpartitionL ℝ E E V).flipMultilinear
  let M := multilinearMap (α := E) L
  let J : C(K,E →ᵇ ((E [×c.length]→L[ℝ] V) →L[ℝ] (E [×n]→L[ℝ] V))) :=
    ⟨fun t => M (fun i => displacedJet D (c.partSize i) t),
      M.cont.comp (continuous_pi (fun i => (displacedJet D (c.partSize i)).continuous))⟩
  let O := pulledJet A D c.length
  let B := bilinearMap (α := E) (ContinuousLinearMap.id ℝ
    ((E [×c.length]→L[ℝ] V) →L[ℝ] (E [×n]→L[ℝ] V)))
  exact ⟨fun t => B (J t) (O t), (B.continuous.comp J.continuous).clm_apply O.continuous⟩

theorem partitionJet_apply (A : SmoothTimeField K E V) (D : SmoothTimeField K E E)
    {n : ℕ} (c : OrderedFinpartition n) (t : K) (x : E) :
    partitionJet A D c t x = c.compAlongOrderedFinpartition
      (iteratedFDeriv ℝ c.length (A.field t : E → V) (x+D.field t x))
      (fun i => iteratedFDeriv ℝ (c.partSize i) (fun y => y+D.field t y) x) := by
  change c.compAlongOrderedFinpartition (pulledJet A D c.length t x)
    (fun i => displacedJet D (c.partSize i) t x) = _
  rw [pulledJet_apply]
  congr 1
  funext i
  exact displacedJet_apply D (c.partSize i) (c.partSize_pos i) t x

/-- Comp displacement, bundling `field`, `smooth`, `jet`, `jet_eq` and the required
compatibility proofs. -/
def compDisplacement (A : SmoothTimeField K E V) (D : SmoothTimeField K E E) :
    SmoothTimeField K E V where
  field := pathPullback A.field D.field ‖A.jet 1‖₊ A.field_lipschitz
  smooth t := (A.smooth t).comp (contDiff_id.add (D.smooth t))
  jet n := ∑ c : OrderedFinpartition n, partitionJet A D c
  jet_eq n t x := by
    change (∑ c : OrderedFinpartition n, partitionJet A D c) t x =
      iteratedFDeriv ℝ n ((A.field t : E → V) ∘ (fun y => y+D.field t y)) x
    have hinner : ContDiff ℝ ∞ (fun y : E => y+D.field t y) :=
      contDiff_id.add (D.smooth t)
    rw [iteratedFDeriv_comp (i := n) (f := fun y : E => y+D.field t y)
      (g := (A.field t : E → V)) (A.smooth t).contDiffAt hinner.contDiffAt (by simp)]
    simp only [ContinuousMap.sum_apply, BoundedContinuousFunction.sum_apply,
      FormalMultilinearSeries.taylorComp, FormalMultilinearSeries.compAlongOrderedFinpartition]
    apply Finset.sum_congr rfl
    intro c _
    exact partitionJet_apply A D c t x

@[simp] theorem compDisplacement_apply (A : SmoothTimeField K E V) (D : SmoothTimeField K E E)
    (t : K) (x : E) :
    (A.compDisplacement D).field t x = A.field t (x+D.field t x) := rfl

end SmoothTimeField
