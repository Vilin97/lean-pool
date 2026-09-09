/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import LeanPool.NavierStokesAndEuler.Euler.BoundedFieldPullback
public import LeanPool.NavierStokesAndEuler.Euler.BoundedFieldMultilinear
public import LeanPool.NavierStokesAndEuler.Euler.BoundedFieldCalculus
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.MeanValue

/-! Composition with identity plus a bounded smooth displacement preserves
the actual continuous-time bounded spatial jets. The finite Faà di Bruno
formula is evaluated in the sup norm, with no extra time derivative. -/

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
