/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FinitePathTensorIntegral

@[expose] public section

/-! An actual smooth family of time paths carries the differentiated time
equation at every spatial order. This is proved by the bounded Bochner
integral identity, rather than assumed commutation of derivatives. -/

noncomputable section


open scoped ContDiff

namespace EulerSmoothPathTimeJets

open Set EulerContinuousTimeIntegral EulerVolterraConvolution EulerFinitePathTensor

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (T : ℝ) (hT : 0 ≤ T) (f q : E → C(Icc (0 : ℝ) T,V))
  (hf : ContDiff ℝ ∞ f) (hq : ContDiff ℝ ∞ q)

def jetFamily (n : ℕ) (x : E) : C(Icc (0 : ℝ) T,E [×n]→L[ℝ] V) :=
  tensorPathMap n (iteratedFDeriv ℝ n f x)

include hf in
theorem jetFamily_contDiff (n : ℕ) : ContDiff ℝ ∞ (jetFamily T f n) := by
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := E [×n]→L[ℝ] C(Icc (0 : ℝ) T,V))
    (F := C(Icc (0 : ℝ) T,E [×n]→L[ℝ] V)) (tensorPathMap n)).comp
    (hf.iteratedFDeriv_right (by simp))

include hf in
theorem jetFamily_apply (n : ℕ) (x : E) (t : Icc (0 : ℝ) T) :
    jetFamily T f n x t = iteratedFDeriv ℝ n (fun y => f y t) x :=
  tensorPath_iteratedFDeriv f hf n x t

variable (hd : ∀ x (t : Icc (0 : ℝ) T),
  HasDerivWithinAt (extendPath T hT (f x)) (q x t) (Icc (0 : ℝ) T) t)

include hf hq hd in
theorem jetFamily_integral (n : ℕ) (x : E) :
    jetFamily T f n x =
      (ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T))
        ((ContinuousMap.evalCLM ℝ (⟨0,le_rfl,hT⟩ : Icc (0 : ℝ) T)).compContinuousMultilinearMap
          (iteratedFDeriv ℝ n f x)) + integral T hT (jetFamily T q n x) := by
  let K : C(Icc (0 : ℝ) T,V) →L[ℝ] C(Icc (0 : ℝ) T,V) :=
    (ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)).comp
      (ContinuousMap.evalCLM ℝ ⟨0,le_rfl,hT⟩)
  let J : C(Icc (0 : ℝ) T,V) →L[ℝ] C(Icc (0 : ℝ) T,V) := integral T hT
  have hfun : f = (K ∘ f) + (J ∘ q) := by
    funext y
    apply ContinuousMap.ext
    intro t
    have h := eq_initial_add_integral T hT (q y) (extendPath T hT (f y)) (hd y) t
    change f y t = f y ⟨0,le_rfl,hT⟩ + integral T hT (q y) t
    simpa only [extendPath, projIcc_of_mem hT t.property,
      projIcc_of_mem hT ⟨le_rfl,hT⟩] using h
  have hKf : ContDiff ℝ ∞ (K ∘ f) := K.contDiff.comp hf
  have hJq : ContDiff ℝ ∞ (J ∘ q) := J.contDiff.comp hq
  have hD := congrArg (fun g : E → C(Icc (0 : ℝ) T,V) => iteratedFDeriv ℝ n g x) hfun
  have hs := iteratedFDeriv_add_apply (i := n) (x := x)
    (hKf.contDiffAt.of_le (by simp)) (hJq.contDiffAt.of_le (by simp))
  have hK := K.iteratedFDeriv_comp_left (x := x) hf.contDiffAt (by simp : (n : ℕ∞) ≤ ∞)
  have hJ := J.iteratedFDeriv_comp_left (x := x) hq.contDiffAt (by simp : (n : ℕ∞) ≤ ∞)
  have hjets := hD.trans (hs.trans (congrArg₂ (fun A B : E [×n]→L[ℝ] C(Icc (0 : ℝ) T,V) => A+B) hK
    hJ))
  have hp := congrArg (tensorPathMap n) hjets
  rw [map_add] at hp
  have hKi : tensorPathMap n (K.compContinuousMultilinearMap (iteratedFDeriv ℝ n f x)) =
      (ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T))
        ((ContinuousMap.evalCLM ℝ (⟨0,le_rfl,hT⟩ : Icc (0 : ℝ) T)).compContinuousMultilinearMap
          (iteratedFDeriv ℝ n f x)) :=
    tensorPath_const (E := E) (V := V) (K := Icc (0 : ℝ) T) n
      ((ContinuousMap.evalCLM ℝ (⟨0,le_rfl,hT⟩ : Icc (0 : ℝ) T)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ n f x))
  exact hp.trans (congrArg₂ (fun a b : C(Icc (0 : ℝ) T,E [×n]→L[ℝ] V) => a+b)
    hKi (tensorPath_integral T hT n _))

include hf hq hd in
theorem jetFamily_hasDerivWithinAt (n : ℕ) (x : E) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (jetFamily T f n x))
      (jetFamily T q n x t) (Icc (0 : ℝ) T) t := by
  have he := jetFamily_integral T hT f q hf hq hd n x
  have hfun := congrArg (fun p : C(Icc (0 : ℝ) T,E [×n]→L[ℝ] V) => extendPath T hT p) he
  rw [hfun]
  exact (integral_hasDerivWithinAt T hT (jetFamily T q n x) t).const_add _

end EulerSmoothPathTimeJets
