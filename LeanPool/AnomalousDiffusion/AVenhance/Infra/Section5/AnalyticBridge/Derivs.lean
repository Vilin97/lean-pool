/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsZ2Periodic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Seminorm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.FourierDecay

/-! # Derivative bookkeeping for the `L²_x → L¹` analyticity bridge

Identities relating iterated Fréchet derivatives of the coordinate derivative `∂_v f`, and of
the `L²`-test functions `y ↦ Dⁿf(y)(w)`, to higher-order iterated derivatives of `f`.  The
extra directions are always placed outermost (`Fin.cons`) or innermost (`Fin.snoc`), so no
symmetry of mixed partials is needed.
-/

@[expose] public section

noncomputable section

open scoped ContDiff
open Homogenization

namespace AVenhance.Infra.Section5.AnalyticBridge

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `n`-th derivative of the directional derivative `∂_v f` is the `(n+1)`-st derivative of
`f` with `v` appended as the innermost direction. -/
theorem iteratedFDeriv_fderiv_apply_snoc {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) (v : E)
    (w : Fin n → E) (x : E) :
    iteratedFDeriv ℝ n (fun y => fderiv ℝ f y v) x w =
      iteratedFDeriv ℝ (n + 1) f x (Fin.snoc w v) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (m := ∞) (by simp)
  have h1 : (fun y => fderiv ℝ f y v) = (ContinuousLinearMap.apply ℝ ℝ v) ∘ (fderiv ℝ f) := rfl
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_left _ hd.contDiffAt (by exact_mod_cast le_top),
    iteratedFDeriv_succ_apply_right]
  simp

/-- The derivative of `y ↦ Dᵐf(y)(w)` in direction `v` puts `v` outermost. -/
theorem fderiv_iteratedFDeriv_apply_cons {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (m : ℕ) (v : E)
    (w : Fin m → E) (x : E) :
    fderiv ℝ (fun y => iteratedFDeriv ℝ m f y w) x v =
      iteratedFDeriv ℝ (m + 1) f x (Fin.cons v w) := by
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ m f) x :=
    (hf.differentiable_iteratedFDeriv (m := m) (by exact_mod_cast WithTop.coe_lt_top _)) x
  have := hdiff.iteratedFDeriv_succ_apply_left' (m := Fin.cons v w)
  simpa using this.symm

/-- The `L²`-test functions `y ↦ Dᵐf(y)(w)` are smooth. -/
theorem contDiff_iteratedFDeriv_apply {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (m : ℕ)
    (w : Fin m → E) : ContDiff ℝ ∞ (fun y => iteratedFDeriv ℝ m f y w) := by
  have h := hf.iteratedFDeriv_right (i := m) (m := ∞) (by simp)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => E) ℝ w).contDiff.comp h

/-- Two derivatives of `y ↦ Dᵐf(y)(w)` in the same direction `v`. -/
theorem iteratedFDeriv_two_iteratedFDeriv_apply {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (m : ℕ)
    (w : Fin m → E) (v : E) (x : E) :
    iteratedFDeriv ℝ 2 (fun y => iteratedFDeriv ℝ m f y w) x (fun _ => v) =
      iteratedFDeriv ℝ (m + 2) f x (Fin.cons v (Fin.cons v w)) := by
  have hu := contDiff_iteratedFDeriv_apply hf m w
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 (fun y => iteratedFDeriv ℝ m f y w)) x :=
    (hu.differentiable_iteratedFDeriv (m := 1) (by exact_mod_cast WithTop.coe_lt_top _)) x
  have h2 := hdiff.iteratedFDeriv_succ_apply_left' (m := fun _ : Fin 2 => v)
  have h3 : (fun y => iteratedFDeriv ℝ 1 (fun y => iteratedFDeriv ℝ m f y w) y
      (Fin.tail fun _ : Fin 2 => v)) =
      fun y => iteratedFDeriv ℝ (m + 1) f y (Fin.cons v w) := by
    funext y
    have : (Fin.tail fun _ : Fin 2 => v) = fun _ : Fin 1 => v := rfl
    rw [this, iteratedFDeriv_one_apply]
    exact fderiv_iteratedFDeriv_apply_cons hf m v w y
  rw [h3] at h2
  have h4 := fderiv_iteratedFDeriv_apply_cons hf (m + 1) v (Fin.cons v w) x
  exact h2.trans h4

/-- Periodicity passes to the `L²`-test functions `y ↦ Dᵐf(y)(w)`. -/
theorem isZ2Periodic_iteratedFDeriv_apply {f : Vec 2 → ℝ} (hp : IsZ2Periodic f) (m : ℕ)
    (w : Fin m → Vec 2) : IsZ2Periodic (fun y => iteratedFDeriv ℝ m f y w) := by
  intro n x
  have hf : (fun z => f (z + latticeShift n)) = f := funext fun z => hp n z
  have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f) m (latticeShift n) x
  rw [hf] at h
  simp only [h]

end Generic

section Coordinate

variable {d : ℕ}

/-- The coordinate-list partial `orderedPartial` is the iterated Fréchet derivative evaluated on
coordinate basis vectors of `Vec d`. -/
theorem orderedPartial_eq_iteratedFDeriv {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ)
    (x : Vec d) (I : Fin n → Fin d) :
    AVenhance.FaaDiBruno.orderedPartial n f x I =
      iteratedFDeriv ℝ n f x (fun j => basisVec (I j)) := by
  have hl : ContDiff ℝ ∞ f := hf
  unfold AVenhance.FaaDiBruno.orderedPartial AVenhance.FaaDiBruno.liftVecOne
  have h : iteratedFDeriv ℝ n (f ∘ ⇑(AVenhance.FaaDiBruno.vecOneEquiv d))
      (WithLp.toLp 1 x) =
      (iteratedFDeriv ℝ n f (AVenhance.FaaDiBruno.vecOneEquiv d (WithLp.toLp 1
          x))).compContinuousLinearMap
        fun _ => (AVenhance.FaaDiBruno.vecOneEquiv d : AVenhance.FaaDiBruno.VecOne d →L[ℝ] Vec d) :=
    ContinuousLinearMap.iteratedFDeriv_comp_right
      (AVenhance.FaaDiBruno.vecOneEquiv d : AVenhance.FaaDiBruno.VecOne d →L[ℝ] Vec d) hl
      (WithLp.toLp 1 x) (i := n) (by exact_mod_cast le_top)
  rw [h]
  simp [AVenhance.FaaDiBruno.vecOneEquiv, PiLp.coe_continuousLinearEquiv,
    AVenhance.FaaDiBruno.coordinateVectorOne, basisVec]

/-- The complexified coordinate derivative of a real smooth function. -/
theorem coordDeriv_ofReal_apply {f : Vec d → ℝ} {x : Vec d} (hf : DifferentiableAt ℝ f x) (i : Fin
    d) :
    AVenhance.Infra.Torus.coordDeriv i (fun y => (f y : ℂ)) x =
      ((fderiv ℝ f x (basisVec i) : ℝ) : ℂ) := by
  change fderiv ℝ (Complex.ofRealCLM ∘ f) x (basisVec i) = _
  rw [fderiv_comp x Complex.ofRealCLM.differentiableAt hf]
  simp

/-- `∂_i^n` of the complexification is the complexification of the iterated derivative on the
constant coordinate list. -/
theorem coordDerivIter_ofReal {F : Vec d → ℝ} (hF : ContDiff ℝ ∞ F) (i : Fin d) (n : ℕ) :
    AVenhance.Infra.Ergodic.coordDerivIter i n (fun x => (F x : ℂ)) =
      fun x => ((iteratedFDeriv ℝ n F x (fun _ => basisVec i) : ℝ) : ℂ) := by
  induction n with
  | zero =>
      funext x
      simp [AVenhance.Infra.Ergodic.coordDerivIter]
  | succ n ih =>
      funext x
      have hdiff : DifferentiableAt ℝ (fun y => iteratedFDeriv ℝ n F y (fun _ => basisVec i)) x :=
        ((contDiff_iteratedFDeriv_apply hF n (fun _ => basisVec i)).differentiable
          (by simp)) x
      simp only [AVenhance.Infra.Ergodic.coordDerivIter, ih]
      rw [coordDeriv_ofReal_apply hdiff, fderiv_iteratedFDeriv_apply_cons hF n _ _ x]
      have hc : (Fin.cons (basisVec i) (fun _ : Fin n => basisVec i) : Fin (n + 1) → Vec d) =
          fun _ => basisVec i := by
        funext j
        refine Fin.cases ?_ (fun j => ?_) j <;> simp
      rw [hc]

/-- Norm of the complexified iterated coordinate derivative. -/
theorem norm_coordDerivIter_ofReal {F : Vec d → ℝ} (hF : ContDiff ℝ ∞ F) (i : Fin d) (n : ℕ)
    (x : Vec d) :
    ‖AVenhance.Infra.Ergodic.coordDerivIter i n (fun x => (F x : ℂ)) x‖ =
      ‖AVenhance.FaaDiBruno.orderedPartial n F x (fun _ => i)‖ := by
  rw [coordDerivIter_ofReal hF, orderedPartial_eq_iteratedFDeriv hF]
  simp

end Coordinate

end AVenhance.Infra.Section5.AnalyticBridge

end
