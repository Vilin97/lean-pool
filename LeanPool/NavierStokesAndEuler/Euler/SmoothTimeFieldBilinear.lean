/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldLinear
public import LeanPool.NavierStokesAndEuler.Euler.BoundedFieldCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section

/-! Constants and bounded bilinear operations on actual smooth bounded
coefficient paths, with the spatial product rule at every order. -/

noncomputable section


open scoped ContDiff BoundedContinuousFunction

universe u

namespace SmoothTimeField

open EulerBoundedFieldCalculus

variable {K E : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [CompactSpace K] [NormedSpace ℝ E] in
@[simp] theorem mapPath_apply {V W : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : V →L[ℝ] W) (A : C(K,E →ᵇ V)) (t : K) (x : E) :
    mapPath L A t x = L (A t x) := rfl

section Constant

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

def boundConstant (v : V) : SmoothTimeField K E V where
  field := ContinuousMap.const K (BoundedContinuousFunction.const E v)
  smooth _ := contDiff_const
  jet n := ContinuousMap.const K (BoundedContinuousFunction.const E
    (iteratedFDeriv ℝ n (fun _ : E => v) 0))
  jet_eq n _ x := by
    change iteratedFDeriv ℝ n (fun _ : E => v) 0 = iteratedFDeriv ℝ n (fun _ : E => v) x
    cases n with
    | zero => rfl
    | succ n => simp only [iteratedFDeriv_succ_const, Pi.zero_apply]

@[simp] theorem constant_apply (v : V) (t : K) (x : E) :
    (boundConstant (K := K) (E := E) v).field t x = v := rfl

end Constant

variable {V W Z : Type u}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

private local instance (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] Z) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] Z) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] Z)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] Z)) := inferInstance
private local instance : NormedAddCommGroup (E →L[ℝ] Z) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] Z) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] (E →L[ℝ] Z)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] (E →L[ℝ] Z)) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] (E →L[ℝ] Z))) :=
  inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] (E →L[ℝ] Z))) := inferInstance

def bilinearPath (B : V →L[ℝ] W →L[ℝ] Z)
    (A : SmoothTimeField K E V) (C : SmoothTimeField K E W) : C(K,E →ᵇ Z) :=
  ⟨fun t => bilinearMap B (A.field t) (C.field t),
    ((bilinearMap (α := E) B).continuous.comp A.field.continuous).clm_apply C.field.continuous⟩

@[simp] theorem bilinearPath_apply (B : V →L[ℝ] W →L[ℝ] Z)
    (A : SmoothTimeField K E V) (C : SmoothTimeField K E W) (t : K) (x : E) :
    bilinearPath B A C t x = B (A.field t x) (C.field t x) := rfl

def uncurryRightPath (n : ℕ) (J : C(K,E →ᵇ (E [×n]→L[ℝ] (E →L[ℝ] Z)))) :
    C(K,E →ᵇ (E [×(n+1)]→L[ℝ] Z)) :=
  mapPath (continuousMultilinearCurryRightEquiv' ℝ n E
    Z).symm.toContinuousLinearEquiv.toContinuousLinearMap J

omit [CompactSpace K] in
@[simp] theorem uncurryRightPath_apply (n : ℕ)
    (J : C(K,E →ᵇ (E [×n]→L[ℝ] (E →L[ℝ] Z)))) (t : K) (x : E) :
    uncurryRightPath n J t x = (continuousMultilinearCurryRightEquiv' ℝ n E Z).symm (J t x) := rfl

theorem exists_bilinear_jet (B : V →L[ℝ] W →L[ℝ] Z)
    (A : SmoothTimeField K E V) (C : SmoothTimeField K E W) (n : ℕ) :
    ∃ J : C(K,E →ᵇ (E [×n]→L[ℝ] Z)), ∀ t x,
      J t x = iteratedFDeriv ℝ n (fun y => B (A.field t y) (C.field t y)) x := by
  induction n generalizing V W Z with
  | zero =>
    refine ⟨mapPath (continuousMultilinearCurryFin0 ℝ E
      Z).symm.toContinuousLinearEquiv.toContinuousLinearMap
      (bilinearPath B A C), ?_⟩
    intro t x
    rfl
  | succ n ih =>
    obtain ⟨J₁,hJ₁⟩ := ih (V := V) (W := E →L[ℝ] W) (Z := E →L[ℝ] Z)
      (B.precompR E) A C.derivative
    obtain ⟨J₂,hJ₂⟩ := ih (V := E →L[ℝ] V) (W := W) (Z := E →L[ℝ] Z)
      (B.precompL E) A.derivative C
    refine ⟨uncurryRightPath n (J₁+J₂), ?_⟩
    intro t x
    rw [uncurryRightPath_apply, ContinuousMap.add_apply, BoundedContinuousFunction.add_apply]
    rw [hJ₁, hJ₂, iteratedFDeriv_succ_eq_comp_right]
    apply congrArg (continuousMultilinearCurryRightEquiv' ℝ n E Z).symm
    have hd : fderiv ℝ (fun y => B (A.field t y) (C.field t y)) =
        fun y => B.precompR E (A.field t y) (C.derivative.field t y)+
          B.precompL E (A.derivative.field t y) (C.field t y) := by
      funext y
      rw [B.fderiv_of_bilinear ((A.smooth t).differentiable (by simp) y)
        ((C.smooth t).differentiable (by simp) y)]
      simp only [derivative, derivativeField_eq]
    rw [hd]
    exact (fun_iteratedFDeriv_add_apply
      ((((B.precompR E).contDiff.comp (A.smooth t)).clm_apply (C.derivative.smooth
        t)).contDiffAt.of_le (by simp))
      ((((B.precompL E).contDiff.comp (A.derivative.smooth t)).clm_apply (C.smooth
        t)).contDiffAt.of_le (by simp))).symm

def bilinear (B : V →L[ℝ] W →L[ℝ] Z)
    (A : SmoothTimeField K E V) (C : SmoothTimeField K E W) : SmoothTimeField K E Z where
  field := bilinearPath B A C
  smooth t := (B.contDiff.comp (A.smooth t)).clm_apply (C.smooth t)
  jet n := (exists_bilinear_jet B A C n).choose
  jet_eq n := (exists_bilinear_jet B A C n).choose_spec

@[simp] theorem bilinear_apply (B : V →L[ℝ] W →L[ℝ] Z)
    (A : SmoothTimeField K E V) (C : SmoothTimeField K E W) (t : K) (x : E) :
    (bilinear B A C).field t x = B (A.field t x) (C.field t x) := rfl

end SmoothTimeField
