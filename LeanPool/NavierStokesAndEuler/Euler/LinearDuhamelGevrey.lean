/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelWeighted
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathCalculus
import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelParameter
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.RCLike.Basic

/-!
# Actual all-order profile estimates for the forward initial value problem

Qualitative smoothness comes from the actual fixed-space Volterra inverse.
Quantitative differentiation instead freezes the evolution and uses its
profile-normalized Green operator, whose norm is bounded by `C*T` directly.
The profile's extrema never enter the factorial radius or amplitude.
-/

section

/-!
# Differentiating a genuine frozen-evolution identity

This calculus lemma applies to actual bounded initial-data and Green operators.
The coefficient difference vanishes at the base point, so the resulting
binomial recurrence contains only lower solution derivatives on the right.
-/

@[expose] public section

noncomputable section

namespace EulerFrozenEvolutionGevrey

open ContinuousLinearMap Finset
open scoped ContDiff

variable {P E X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The triangular recurrence is derived from actual Fréchet derivatives of
the frozen equation; it is not an assumed sequence estimate. -/
theorem derivative_recurrence
    (B : P → X →L[ℝ] X) (u f : P → X) (a : P → E)
    (hB : ContDiff ℝ ∞ B) (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f) (ha : ContDiff ℝ ∞ a)
    (x : P) (H : E →L[ℝ] X) (K : X →L[ℝ] X)
    (heq : ∀ y, u y = H (a y) + K (f y + (B y - B x) (u y))) (n : ℕ) :
    ‖iteratedFDeriv ℝ n u x‖ ≤ ‖H‖*‖iteratedFDeriv ℝ n a x‖ + ‖K‖*
      (‖iteratedFDeriv ℝ n f x‖ + ∑ j ∈ range n,
        (n.choose (j+1) : ℝ) * ‖iteratedFDeriv ℝ (j+1) B x‖ *
          ‖iteratedFDeriv ℝ (n-(j+1)) u x‖) := by
  let C : P → X →L[ℝ] X := fun y => B y-B x
  let p : P → X := fun y => C y (u y)
  let q : P → X := f+p
  have hC : ContDiff ℝ ∞ C := hB.sub contDiff_const
  have hp : ContDiff ℝ ∞ p := hC.clm_apply hu
  have hq : ContDiff ℝ ∞ q := hf.add hp
  have hfreeze : u = (H ∘ a) + (K ∘ q) := funext heq
  have hzero : ‖iteratedFDeriv ℝ 0 C x‖ = 0 := by
    rw [norm_iteratedFDeriv_zero]
    simp [C]
  have hpositive (j : ℕ) : iteratedFDeriv ℝ (j+1) C x = iteratedFDeriv ℝ (j+1) B x := by
    change iteratedFDeriv ℝ (j+1) (B - fun _ => B x) x = _
    rw [iteratedFDeriv_sub_apply (hB.contDiffAt.of_le (by simp)) contDiffAt_const]
    simp only [iteratedFDeriv_succ_const, Pi.zero_apply, sub_zero]
  have hprod := norm_iteratedFDeriv_clm_apply hC hu x (n := n) (by simp)
  rw [sum_range_succ'] at hprod
  simp only [hzero, mul_zero, zero_mul, add_zero, hpositive] at hprod
  have hqnorm : ‖iteratedFDeriv ℝ n q x‖ ≤
      ‖iteratedFDeriv ℝ n f x‖ + ‖iteratedFDeriv ℝ n p x‖ := by
    change ‖iteratedFDeriv ℝ n (f+p) x‖ ≤ _
    rw [iteratedFDeriv_add_apply (hf.contDiffAt.of_le (by simp)) (hp.contDiffAt.of_le (by simp))]
    exact norm_add_le _ _
  have hH := H.norm_iteratedFDeriv_comp_left (x := x) ha.contDiffAt (n := n) (by simp)
  have hK := K.norm_iteratedFDeriv_comp_left (x := x) hq.contDiffAt (n := n) (by simp)
  have hsum : ‖iteratedFDeriv ℝ n u x‖ ≤
      ‖iteratedFDeriv ℝ n (H ∘ a) x‖ + ‖iteratedFDeriv ℝ n (K ∘ q) x‖ := by
    conv_lhs => rw [hfreeze]
    rw [iteratedFDeriv_add_apply ((H.contDiff.comp ha).contDiffAt.of_le (by simp))
      ((K.contDiff.comp hq).contDiffAt.of_le (by simp))]
    exact norm_add_le _ _
  exact hsum.trans (add_le_add hH (hK.trans (mul_le_mul_of_nonneg_left
    (hqnorm.trans (add_le_add le_rfl hprod)) (norm_nonneg K))))

end EulerFrozenEvolutionGevrey

end
end

end

@[expose] public section

noncomputable section

namespace EulerLinearDuhamel

open Set Finset ContinuousLinearMap EulerContinuousTimeIntegral EulerContinuousTimeWeight
  EulerContinuousPathCalculus EulerGevrey
open scoped ContDiff

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (T : ℝ) (hT : 0 ≤ T) (B : P → C(Icc (0 : ℝ) T, E →L[ℝ] E))
  (U : ∀ x, Evolution T hT (B x))
  (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
  (f : P → C(Icc (0 : ℝ) T, E)) (a₀ : P → E)

/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instLinearDuhamelGevrey1 : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instLinearDuhamelGevrey2 : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,E)` instance to shorten typeclass
synthesis. -/
local instance instLinearDuhamelGevrey3 : NormedAddCommGroup C(Icc (0 : ℝ) T,E) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,E)` instance to shorten typeclass
synthesis. -/
local instance instLinearDuhamelGevrey4 : NormedSpace ℝ C(Icc (0 : ℝ) T,E) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,E →L[ℝ] E)` instance to shorten
typeclass synthesis. -/
local instance instLinearDuhamelGevrey5 : NormedAddCommGroup C(Icc (0 : ℝ) T,E →L[ℝ] E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,E →L[ℝ] E)` instance to shorten typeclass
synthesis. -/
local instance instLinearDuhamelGevrey6 : NormedSpace ℝ C(Icc (0 : ℝ) T,E →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedAddCommGroup (C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E))`
instance to shorten typeclass synthesis. -/
local instance instLinearDuhamelGevrey7 : NormedAddCommGroup (C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 :
    ℝ) T,E)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E))` instance to
shorten typeclass synthesis. -/
local instance instLinearDuhamelGevrey8 : NormedSpace ℝ (C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ)
    T,E)) :=
    inferInstance

/-- Normalization by a fixed profile preserves actual parameter regularity. -/
theorem weightedSolution_contDiff {n : ℕ∞ω} (hB : ContDiff ℝ n B)
    (hf : ContDiff ℝ n f) (ha₀ : ContDiff ℝ n a₀) :
    ContDiff ℝ n (fun x => (U x).weightedSolution g hg (f x) (a₀ x)) := by
  have hw : ContDiff ℝ n (fun x => weight g (f x)) := by
    change ContDiff ℝ n ((weight (E := E) g) ∘ f)
    exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n)
      (E := C(Icc (0 : ℝ) T,E)) (F := C(Icc (0 : ℝ) T,E)) (weight g)).comp hf
  have hs := solution_contDiff T hT B U (fun x => weight g (f x)) a₀ hB hw ha₀
  change ContDiff ℝ n ((normalize (E := E) g hg) ∘
    (fun x => (U x).solution (weight g (f x)) (a₀ x)))
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n)
    (E := C(Icc (0 : ℝ) T,E)) (F := C(Icc (0 : ℝ) T,E)) (normalize g hg)).comp hs

/-- The exact differentiated ODE yields a triangular estimate in the fixed
profile norm, with the same homogeneous and Green operators at every order. -/
theorem weightedSolution_derivative_recurrence
    (hB : ContDiff ℝ ∞ B) (hf : ContDiff ℝ ∞ f) (ha₀ : ContDiff ℝ ∞ a₀)
    (hg₀ : g ⟨0, le_rfl, hT⟩ = 1) (C : ℝ) (hC : 0 ≤ C)
    (hU : ∀ x (t s : Icc (0 : ℝ) T), s ≤ t → ‖(U x).propagator t s‖ ≤ C * g t / g s)
    (x : P) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => (U y).weightedSolution g hg (f y) (a₀ y)) x‖ ≤
      C*‖iteratedFDeriv ℝ n a₀ x‖ + (C*T) *
        (‖iteratedFDeriv ℝ n f x‖ + ∑ j ∈ range n,
          (n.choose (j+1) : ℝ) * ‖iteratedFDeriv ℝ (j+1) (fun y => multiplier (B y)) x‖ *
            ‖iteratedFDeriv ℝ (n-(j+1))
              (fun y => (U y).weightedSolution g hg (f y) (a₀ y)) x‖) := by
  let u := fun y => (U y).weightedSolution g hg (f y) (a₀ y)
  have hu := weightedSolution_contDiff T hT B U g hg f a₀ hB hf ha₀
  have hfreeze : ∀ y, u y = (U x).weightedInitial g hg (a₀ y) +
      (U x).weightedForcing g hg (f y + (multiplier (B y)-multiplier (B x)) (u y)) := by
    intro y
    have hd : multiplier (B y-B x) = multiplier (B y)-multiplier (B x) := by
      ext p t
      rfl
    simpa only [hd] using (U x).weighted_frozen_solution g hg (U y) (f y) (a₀ y)
  have hr := EulerFrozenEvolutionGevrey.derivative_recurrence
    (fun y => multiplier (B y)) u f a₀ (contDiff_multiplier B hB) hu hf ha₀ x
    ((U x).weightedInitial g hg) ((U x).weightedForcing g hg) hfreeze n
  exact hr.trans (add_le_add
    (mul_le_mul_of_nonneg_right ((U x).weightedInitial_norm g hg hg₀ C hC (hU x)) (norm_nonneg _))
    (mul_le_mul_of_nonneg_right ((U x).weightedForcing_norm g hg hg₀ C hC (hU x)) (by positivity)))

/-- The fixed polynomial amplitude controlling the differentiated forward solve. -/
def forwardCost (T C A D CB : ℝ) : ℝ := 1 + C*A + C*T*(D+CB)

/-- The actual forward solve loses one factorial shift. Its radius condition
contains only the propagator, coefficient and data amplitudes, and time length. -/
theorem weightedSolution_gevrey
    (hB : ContDiff ℝ ∞ B) (hf : ContDiff ℝ ∞ f) (ha₀ : ContDiff ℝ ∞ a₀)
    (hg₀ : g ⟨0, le_rfl, hT⟩ = 1)
    (C A D CB Rc R : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D) (hCB : 0 ≤ CB)
    (hRc : 0 ≤ Rc) (hR : 2 * forwardCost T C A D CB * (Rc + 1) ≤ R)
    (hU : ∀ x (t s : Icc (0 : ℝ) T), s ≤ t → ‖(U x).propagator t s‖ ≤ C * g t / g s)
    (hcoeff : ∀ j x, ‖iteratedFDeriv ℝ (j + 1) B x‖ ≤ CB * (Rc ^ (j + 1) * ((j + 1).factorial : ℝ)
        ^ 2))
    (d : ℕ) (hforce : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ D * majorant R d n)
    (hinitial : ∀ n x, ‖iteratedFDeriv ℝ n a₀ x‖ ≤ A * majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => (U y).weightedSolution g hg (f y) (a₀ y)) x‖ ≤
      majorant R (d+1) n := by
  let u := fun y => (U y).weightedSolution g hg (f y) (a₀ y)
  let M := forwardCost T C A D CB
  have hCT : 0 ≤ C*T := mul_nonneg hC hT
  have hM : 1 ≤ M := by
    dsimp [M,forwardCost]
    linarith [mul_nonneg hC hA, mul_nonneg hCT (add_nonneg hD hCB)]
  have hR0 : 0 ≤ R := le_trans
    (mul_nonneg (mul_nonneg (by norm_num) (le_trans zero_le_one hM)) (by linarith)) hR
  have htop : C*A + C*T*D ≤ M := by
    dsimp [M,forwardCost]
    linarith [mul_nonneg hCT hCB]
  have hcoef : C*T*CB ≤ M := by
    dsimp [M,forwardCost]
    linarith [mul_nonneg hC hA, mul_nonneg hCT hD]
  apply triangular_inverse_majorant M Rc R hM hRc hR d
    (fun k => majorant R d k) (fun k => ‖iteratedFDeriv ℝ k u x‖) (fun _ => le_rfl) _ n
  intro k
  let S : ℝ := ∑ j ∈ range k, (k.choose (j+1) : ℝ) * Rc^(j+1) *
    ((j+1).factorial : ℝ)^2 * ‖iteratedFDeriv ℝ (k-(j+1)) u x‖
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hmajor : 0 ≤ majorant R d k := majorant_nonneg R hR0 d k
  have hcoeffOp (j : ℕ) :
      ‖iteratedFDeriv ℝ (j+1) (fun y => multiplier (B y)) x‖ ≤
        CB*(Rc^(j+1)*((j+1).factorial : ℝ)^2) := by
    have hl := ContinuousLinearMap.norm_iteratedFDeriv_comp_left
      (𝕜 := ℝ) (E := P) (F := C(Icc (0 : ℝ) T,E →L[ℝ] E))
      (G := C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E))
      (coefficientMap (K := Icc (0 : ℝ) T) (E := E) (F := E))
      (x := x) hB.contDiffAt (n := j+1) (by simp)
    exact hl.trans ((mul_le_mul_of_nonneg_right coefficientMap_norm (norm_nonneg _)).trans
      (by simpa only [one_mul] using hcoeff j x))
  have hsum : (∑ j ∈ range k, (k.choose (j+1) : ℝ) *
      ‖iteratedFDeriv ℝ (j+1) (fun y => multiplier (B y)) x‖ *
      ‖iteratedFDeriv ℝ (k-(j+1)) u x‖) ≤ CB*S := by
    dsimp [S]
    rw [mul_sum]
    apply sum_le_sum
    intro j _
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hcoeffOp j) (by positivity : (0 : ℝ) ≤ k.choose (j+1)))
      (norm_nonneg (iteratedFDeriv ℝ (k-(j+1)) u x))
    convert hh using 1
    ring
  have hr := weightedSolution_derivative_recurrence T hT B U g hg f a₀ hB hf ha₀ hg₀ C hC hU x k
  have hb : ‖iteratedFDeriv ℝ k u x‖ ≤ C*(A*majorant R d k) + (C*T)*(D*majorant R d k+CB*S) :=
    hr.trans (add_le_add (mul_le_mul_of_nonneg_left (hinitial k x) hC)
      (mul_le_mul_of_nonneg_left (add_le_add (hforce k x) hsum) hCT))
  change ‖iteratedFDeriv ℝ k u x‖ ≤ M*(majorant R d k+S)
  apply hb.trans
  calc
    _ = (C*A+C*T*D)*majorant R d k+(C*T*CB)*S := by ring
    _ ≤ M*majorant R d k+M*S := add_le_add
      (mul_le_mul_of_nonneg_right htop hmajor) (mul_le_mul_of_nonneg_right hcoef hS)
    _ = _ := by ring

end EulerLinearDuhamel
