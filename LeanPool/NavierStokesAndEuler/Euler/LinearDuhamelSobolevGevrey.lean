/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevInverse
import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelGevrey
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevGevrey
import Mathlib.Algebra.Order.Star.Real
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevBlocks
import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathCalculus
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear
import Mathlib.Analysis.Calculus.ContDiff.Operations
public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelWeighted
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# The forward estimate in actual fixed-Sobolev external-word blocks

The normalized Duhamel solution satisfies the constructed frozen equation.
Its inverse at the base point is literally Id. Applying the finite base-order
inverse estimate and then the external-word recurrence gives one factorial
shift at the same input/output radius. Every constant is a fixed polynomial
in the coefficient, data, propagator and time-length constants when q is fixed.
-/

section

/-!
# Quantitative bounds for the actual frozen forward equation

The frozen coefficient has a polynomial tensor multiplier bound derived
from the original coefficient and the H3 Green bound. Its fixed-Sobolev
forcing block is bounded directly by the original initial/forcing blocks.
No profile extremum, inverse amplitude, or raw weighted primitive is used.
-/

section

/-!
# A frozen bounded-operator equation for the actual forward solve

At a chosen parameter x, Duhamel gives an exact equation with coefficient
Id minus the fixed Green operator applied to the coefficient difference.
Its coefficient at x is exactly Id. Thus the fixed-Sobolev inverse estimate
can use the identity inverse; it never requires a norm for a profile-weighted
raw time primitive.
-/

@[expose] public section

noncomputable section

namespace EulerLinearDuhamel

open Set ContinuousLinearMap EulerContinuousTimeIntegral EulerContinuousTimeWeight
  EulerContinuousPathCalculus
open scoped ContDiff

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (T : ℝ) (hT : 0 ≤ T) (B : P → C(Icc (0 : ℝ) T, E →L[ℝ] E))
  (U : ∀ x, Evolution T hT (B x))
  (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)

/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instLinearDuhamelFrozenOperator1 : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instLinearDuhamelFrozenOperator2 : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,E)` instance to shorten typeclass
synthesis. -/
local instance instLinearDuhamelFrozenOperator3 : NormedAddCommGroup C(Icc (0 : ℝ) T,E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,E)` instance to shorten typeclass
synthesis. -/
local instance instLinearDuhamelFrozenOperator4 : NormedSpace ℝ C(Icc (0 : ℝ) T,E) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,E →L[ℝ] E)` instance to shorten
typeclass synthesis. -/
local instance instLinearDuhamelFrozenOperator5 : NormedAddCommGroup C(Icc (0 : ℝ) T,E →L[ℝ] E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,E →L[ℝ] E)` instance to shorten typeclass
synthesis. -/
local instance instLinearDuhamelFrozenOperator6 : NormedSpace ℝ C(Icc (0 : ℝ) T,E →L[ℝ] E) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E))`
instance to shorten typeclass synthesis. -/
local instance instLinearDuhamelFrozenOperator7 : NormedAddCommGroup (C(Icc (0 : ℝ) T,E) →L[ℝ]
    C(Icc (0 : ℝ) T,E)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E))` instance to
shorten typeclass synthesis. -/
local instance instLinearDuhamelFrozenOperator8 : NormedSpace ℝ (C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0
    : ℝ) T,E)) :=
    inferInstance

/-- The exact frozen coefficient, using the actual weighted Green operator. -/
def frozenOperator (x y : P) : C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E) :=
  ContinuousLinearMap.id ℝ _ - ((U x).weightedForcing g hg).comp (multiplier (B y)-multiplier (B x))

/-- The exact transformed data under the fixed homogeneous and Green operators. -/
def frozenForcing (f : P → C(Icc (0 : ℝ) T, E)) (a₀ : P → E) (x y : P) : C(Icc (0 : ℝ) T,E) :=
  (U x).weightedInitial g hg (a₀ y)+(U x).weightedForcing g hg (f y)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The frozen coefficient at its base parameter is the identity. -/
theorem frozenOperator_self (x : P) :
    frozenOperator T hT B U g hg x x = ContinuousLinearMap.id ℝ _ := by
  simp only [frozenOperator, sub_self, comp_zero, sub_zero]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The actual normalized Duhamel solution satisfies this bounded-operator equation. -/
theorem frozenOperator_equation (f : P → C(Icc (0 : ℝ) T, E)) (a₀ : P → E) (x y : P) :
    frozenOperator T hT B U g hg x y ((U y).weightedSolution g hg (f y) (a₀ y)) =
      frozenForcing T hT B U g hg f a₀ x y := by
  have hd : multiplier (B y-B x) = multiplier (B y)-multiplier (B x) := by
    ext p t
    rfl
  have h := (U x).weighted_frozen_solution g hg (U y) (f y) (a₀ y)
  rw [hd, map_add] at h
  change (U y).weightedSolution g hg (f y) (a₀ y) -
      (U x).weightedForcing g hg ((multiplier (B y)-multiplier (B x))
        ((U y).weightedSolution g hg (f y) (a₀ y))) = _
  exact sub_eq_iff_eq_add.mpr (by simpa only [frozenForcing, add_assoc] using h)

/-- The frozen coefficient is genuinely smooth in the translated coefficients. -/
theorem frozenOperator_contDiff (hB : ContDiff ℝ ∞ B) (x : P) :
    ContDiff ℝ ∞ (frozenOperator T hT B U g hg x) :=
  contDiff_const.sub (contDiff_const.clm_comp ((contDiff_multiplier B hB).sub contDiff_const))

/-- The transformed data retain the actual parameter smoothness of the original data. -/
theorem frozenForcing_contDiff (f : P → C(Icc (0 : ℝ) T, E)) (a₀ : P → E)
    (hf : ContDiff ℝ ∞ f) (ha₀ : ContDiff ℝ ∞ a₀) (x : P) :
    ContDiff ℝ ∞ (frozenForcing T hT B U g hg f a₀ x) :=
  (((U x).weightedInitial g hg).contDiff.comp ha₀).add
    (((U x).weightedForcing g hg).contDiff.comp hf)

end EulerLinearDuhamel

end
end

end

@[expose] public section

noncomputable section

namespace EulerLinearDuhamel

open Set ContinuousLinearMap EulerContinuousTimeIntegral EulerContinuousTimeWeight
  EulerContinuousPathCalculus EulerOperatorGevreyCalculus EulerGevrey EulerParameterWordGevrey
open scoped ContDiff

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (T : ℝ) (hT : 0 ≤ T) (B : P → C(Icc (0 : ℝ) T, E →L[ℝ] E))
  (U : ∀ x, Evolution T hT (B x))
  (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)

/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instLinearDuhamelFrozenGevrey1 : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instLinearDuhamelFrozenGevrey2 : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,E)` instance to shorten typeclass
synthesis. -/
local instance instLinearDuhamelFrozenGevrey3 : NormedAddCommGroup C(Icc (0 : ℝ) T,E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,E)` instance to shorten typeclass
synthesis. -/
local instance instLinearDuhamelFrozenGevrey4 : NormedSpace ℝ C(Icc (0 : ℝ) T,E) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,E →L[ℝ] E)` instance to shorten
typeclass synthesis. -/
local instance instLinearDuhamelFrozenGevrey5 : NormedAddCommGroup C(Icc (0 : ℝ) T,E →L[ℝ] E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,E →L[ℝ] E)` instance to shorten typeclass
synthesis. -/
local instance instLinearDuhamelFrozenGevrey6 : NormedSpace ℝ C(Icc (0 : ℝ) T,E →L[ℝ] E) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E))`
instance to shorten typeclass synthesis. -/
local instance instLinearDuhamelFrozenGevrey7 : NormedAddCommGroup (C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc
    (0 : ℝ) T,E)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E))` instance to
shorten typeclass synthesis. -/
local instance instLinearDuhamelFrozenGevrey8 : NormedSpace ℝ (C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 :
    ℝ) T,E)) :=
    inferInstance

/-- The frozen coefficient amplitude is polynomial in the original coefficient and H3 constant. -/
def frozenAmplitude (T C CB : ℝ) : ℝ := 1+2*C*T*CB

/-- Actual derivatives of the frozen coefficient have the stated polynomial bound. -/
theorem frozenOperator_bound (hB : ContDiff ℝ ∞ B)
    (hg₀ : g ⟨0, le_rfl, hT⟩ = 1) (C CB Rc : ℝ) (hC : 0 ≤ C) (hCB : 0 ≤ CB) (hRc : 0 ≤ Rc)
    (hBb : ∀ n y, ‖iteratedFDeriv ℝ n B y‖ ≤ CB * majorant Rc 0 n)
    (x : P) (hU : ∀ t s : Icc (0 : ℝ) T, s ≤ t → ‖(U x).propagator t s‖ ≤ C*g t/g s)
    (n : ℕ) (y : P) :
    ‖iteratedFDeriv ℝ n (frozenOperator T hT B U g hg x) y‖ ≤
      frozenAmplitude T C CB*majorant Rc 0 n := by
  let K := (U x).weightedForcing g hg
  let D := (fun z => multiplier (B z))-fun _ => multiplier (B x)
  have hM := contDiff_multiplier B hB
  have hD : ContDiff ℝ ∞ D := hM.sub contDiff_const
  have hMb := multiplier_bound B hB Rc CB hRc hCB 0 hBb
  have hMx : ‖multiplier (B x)‖ ≤ CB := by
    simpa only [norm_iteratedFDeriv_zero, majorant, Nat.add_zero, pow_zero,
      Nat.factorial_zero, Nat.cast_one, one_pow, mul_one] using hMb 0 x
  have hDb := sub_bound (fun z => multiplier (B z)) (fun _ : P => multiplier (B x))
    hM contDiff_const Rc CB CB 0 hMb (const_bound (multiplier (B x)) Rc CB hRc hMx)
  have hKb : ‖K‖ ≤ C*T := (U x).weightedForcing_norm g hg hg₀ C hC hU
  have hKD (j : ℕ) (z : P) : ‖iteratedFDeriv ℝ j (fun w => K.comp (D w)) z‖ ≤
      (2*C*T*CB)*majorant Rc 0 j := by
    have h := clm_comp_const_left_bound K D hD Rc (CB+CB) hRc (by positivity) 0 hDb j z
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (majorant_nonneg Rc hRc 0 j)
    calc
      ‖K‖*(CB+CB) ≤ (C*T)*(CB+CB) := mul_le_mul_of_nonneg_right hKb (by positivity)
      _ = 2*C*T*CB := by ring
  have h := sub_bound (fun _ : P => ContinuousLinearMap.id ℝ C(Icc (0 : ℝ) T,E))
    (fun z => K.comp (D z)) contDiff_const (contDiff_const.clm_comp hD)
    Rc 1 (2*C*T*CB) 0
    (const_bound (ContinuousLinearMap.id ℝ C(Icc (0 : ℝ) T,E)) Rc 1 hRc norm_id_le) hKD n y
  exact h

/-- The transformed right side preserves the original fixed-Sobolev external radius. -/
theorem frozenForcing_block_bound {ι : Type*} [Fintype ι] (directions : ι → P) (q : ℕ)
    (f : P → C(Icc (0 : ℝ) T, E)) (a₀ : P → E)
    (hf : ContDiff ℝ ∞ f) (ha₀ : ContDiff ℝ ∞ a₀)
    (hg₀ : g ⟨0, le_rfl, hT⟩ = 1) (C A D R : ℝ) (hC : 0 ≤ C)
    (x : P) (hU : ∀ t s : Icc (0 : ℝ) T, s ≤ t → ‖(U x).propagator t s‖ ≤ C*g t/g s)
    (d : ℕ) (hfa : ∀ n, block directions q f n x ≤ D*majorant R d n)
    (haa : ∀ n, block directions q a₀ n x ≤ A*majorant R d n) (n : ℕ) :
    block directions q (frozenForcing T hT B U g hg f a₀ x) n x ≤
      (C*A+C*T*D)*majorant R d n := by
  let H := (U x).weightedInitial g hg
  let K := (U x).weightedForcing g hg
  have hH := block_comp_clm_le directions q H a₀ ha₀ n x
  have hK := block_comp_clm_le directions q K f hf n x
  have hs := block_add_le directions q (H ∘ a₀) (K ∘ f)
    (H.contDiff.comp ha₀) (K.contDiff.comp hf) n x
  apply hs.trans
  calc
    _ ≤ C*(A*majorant R d n)+(C*T)*(D*majorant R d n) := add_le_add
      (hH.trans (mul_le_mul ((U x).weightedInitial_norm g hg hg₀ C hC hU)
        (haa n) (block_nonneg directions q a₀ n x) hC))
      (hK.trans (mul_le_mul ((U x).weightedForcing_norm g hg hg₀ C hC hU)
        (hfa n) (block_nonneg directions q f n x) (mul_nonneg hC hT)))
    _ = _ := by ring

end EulerLinearDuhamel

end
end

end

section

/-!
# The fixed-Sobolev inverse estimate needs bounds only at its base point

In particular a frozen Duhamel equation has identity as its base operator.
The actual equation and smoothness hold as functions; every quantitative
hypothesis, including invertibility, is needed only at the evaluation point.
-/

@[expose] public section

noncomputable section

namespace EulerParameterWordGevrey

open ContinuousLinearMap Finset EulerJetProductBounds EulerGevrey
open scoped ContDiff

variable {P E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem block_inverse_gevrey_at (directions : ι → P) (q : ℕ)
    (A : P → E →L[ℝ] E) (u f : P → E)
    (hA : ContDiff ℝ ∞ A) (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (heq : ∀ y, A y (u y) = f y)
    (x : P) (inverse : E →L[ℝ] E) (hleft : ∀ v, inverse (A x v) = v)
    (I B C D M Rc R : ℝ) (_hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hM : 1 ≤ M) (hMC : sobolevInverseCost I B q * C ≤ M)
    (hMD : sobolevInverseCost I B q * D ≤ M)
    (hRc : 0 ≤ Rc) (hR : 2 * M * (Rc + 1) ≤ R)
    (hinv : ‖inverse‖ ≤ I) (hbase : baseSize directions q A x ≤ B)
    (hcoeff : ∀ j, coefficientBlock directions q A (j + 1) x ≤ C * (Rc ^ (j + 1) * ((j +
        1).factorial : ℝ) ^ 2))
    (d : ℕ) (hforce : ∀ n, block directions q f n x ≤ D * majorant R d n)
    (n : ℕ) : block directions q u n x ≤ majorant R (d+1) n := by
  have hR0 : 0 ≤ R := by nlinarith
  have hI : 0 ≤ I := (norm_nonneg inverse).trans hinv
  have hB : 0 ≤ B := (baseSize_nonneg directions q A x).trans hbase
  have hcost := sobolevInverseCost_nonneg I B hI hB q
  apply triangular_inverse_majorant M Rc R hM hRc hR d
    (fun k => majorant R d k) (fun k => block directions q u k x) (fun _ => le_rfl) _ n
  intro k
  let S : ℝ := ∑ j ∈ range k, (k.choose (j+1) : ℝ)*Rc^(j+1) *
    ((j+1).factorial : ℝ)^2*block directions q u (k-(j+1)) x
  have hS : 0 ≤ S := sum_nonneg (fun j _ => mul_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hRc _)) (sq_nonneg _))
    (block_nonneg directions q u _ x))
  have hsum : (∑ j ∈ range k, (k.choose (j+1) : ℝ)*coefficientBlock directions q A (j+1) x *
      block directions q u (k-(j+1)) x) ≤ C*S := by
    dsimp only [S]
    rw [mul_sum]
    apply sum_le_sum
    intro j _
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hcoeff j) (Nat.cast_nonneg (k.choose (j+1))))
      (block_nonneg directions q u (k-(j+1)) x)
    convert h using 1
    ring
  have hrec := block_inverse_recurrence directions q A u f hA hu hf heq x
    inverse hleft I B hinv hbase k
  have hb : block directions q u k x ≤ sobolevInverseCost I B q*(D*majorant R d k+C*S) :=
    hrec.trans (mul_le_mul_of_nonneg_left (add_le_add (hforce k) hsum) hcost)
  have h₁ := mul_le_mul_of_nonneg_right hMC hS
  have h₂ := mul_le_mul_of_nonneg_right hMD (majorant_nonneg R hR0 d k)
  change block directions q u k x ≤ M*(majorant R d k+S)
  linarith

end EulerParameterWordGevrey

end
end

end

@[expose] public section

noncomputable section

namespace EulerLinearDuhamel

open Set ContinuousLinearMap EulerContinuousTimeIntegral EulerContinuousTimeWeight
  EulerGevrey EulerParameterWordGevrey
open scoped ContDiff

/-- The once-enlarged coefficient amplitude for the frozen equation at fixed base order. -/
def forwardSobolevAmplitude (ι : Type*) [Fintype ι] (q : ℕ) (T C CB Rc : ℝ) : ℝ :=
  sobolevCoefficientAmplitude ι q Rc (frozenAmplitude T C CB)

/-- A fixed polynomial cost for the source's forward Hq external-word estimate. -/
def forwardSobolevCost (ι : Type*) [Fintype ι] (q : ℕ) (T C A D CB Rc : ℝ) : ℝ :=
  1+sobolevInverseCost 1 (forwardSobolevAmplitude ι q T C CB Rc) q *
    (forwardSobolevAmplitude ι q T C CB Rc+C*A+C*T*D)

variable {P E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Fintype ι]
  (directions : ι → P) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (T : ℝ) (hT : 0 ≤ T) (B : P → C(Icc (0 : ℝ) T, E →L[ℝ] E))
  (U : ∀ x, Evolution T hT (B x))
  (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
  (f : P → C(Icc (0 : ℝ) T, E)) (a₀ : P → E)

/-- Cache the standard `NormedAddCommGroup (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instLinearDuhamelSobolevGevrey1 : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedSpace ℝ (E →L[ℝ] E)` instance to shorten typeclass synthesis. -/
local instance instLinearDuhamelSobolevGevrey2 : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,E)` instance to shorten typeclass
synthesis. -/
local instance instLinearDuhamelSobolevGevrey3 : NormedAddCommGroup C(Icc (0 : ℝ) T,E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,E)` instance to shorten typeclass
synthesis. -/
local instance instLinearDuhamelSobolevGevrey4 : NormedSpace ℝ C(Icc (0 : ℝ) T,E) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,E →L[ℝ] E)` instance to shorten
typeclass synthesis. -/
local instance instLinearDuhamelSobolevGevrey5 : NormedAddCommGroup C(Icc (0 : ℝ) T,E →L[ℝ] E) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,E →L[ℝ] E)` instance to shorten typeclass
synthesis. -/
local instance instLinearDuhamelSobolevGevrey6 : NormedSpace ℝ C(Icc (0 : ℝ) T,E →L[ℝ] E) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E))`
instance to shorten typeclass synthesis. -/
local instance instLinearDuhamelSobolevGevrey7 : NormedAddCommGroup (C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc
    (0 : ℝ) T,E)) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E))` instance to
shorten typeclass synthesis. -/
local instance instLinearDuhamelSobolevGevrey8 : NormedSpace ℝ (C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 :
    ℝ) T,E)) :=
    inferInstance

include hd in
/-- The actual fixed-Hq block of the forward solution gains just one shift,
with an unchanged radius and with H3 used only at the base parameter. -/
theorem weightedSolution_block_gevrey_at
    (hB : ContDiff ℝ ∞ B) (hf : ContDiff ℝ ∞ f) (ha₀ : ContDiff ℝ ∞ a₀)
    (hg₀ : g ⟨0, le_rfl, hT⟩ = 1)
    (C A D CB Rc R : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D) (hCB : 0 ≤ CB)
    (hRc : 0 ≤ Rc)
    (hR : 2 * forwardSobolevCost ι q T C A D CB Rc * (sobolevCoefficientRadius ι Rc + 1) ≤ R)
    (hBb : ∀ n y, ‖iteratedFDeriv ℝ n B y‖ ≤ CB * majorant Rc 0 n)
    (x : P) (hU : ∀ t s : Icc (0 : ℝ) T, s ≤ t → ‖(U x).propagator t s‖ ≤ C*g t/g s)
    (d : ℕ) (hforce : ∀ n, block directions q f n x ≤ D*majorant R d n)
    (hinitial : ∀ n, block directions q a₀ n x ≤ A*majorant R d n)
    (n : ℕ) :
    block directions q (fun y => (U y).weightedSolution g hg (f y) (a₀ y)) n x ≤
      majorant R (d+1) n := by
  let Aₓ := frozenOperator T hT B U g hg x
  let Fₓ := frozenForcing T hT B U g hg f a₀ x
  let u := fun y => (U y).weightedSolution g hg (f y) (a₀ y)
  let CF := forwardSobolevAmplitude ι q T C CB Rc
  let DF := C*A+C*T*D
  let M := forwardSobolevCost ι q T C A D CB Rc
  have hfrozen : 0 ≤ frozenAmplitude T C CB := by unfold frozenAmplitude; positivity
  have hCF : 0 ≤ CF := sobolevCoefficientAmplitude_nonneg q Rc (frozenAmplitude T C CB) hRc hfrozen
  have hDF : 0 ≤ DF := by dsimp [DF]; positivity
  have hcost : 0 ≤ sobolevInverseCost 1 CF q := sobolevInverseCost_nonneg 1 CF zero_le_one hCF q
  have hMeq : M = 1+sobolevInverseCost 1 CF q*(CF+DF) := by
    dsimp only [M, forwardSobolevCost, CF, DF]
    ring
  have hM : 1 ≤ M := by
    rw [hMeq]
    exact le_add_of_nonneg_right (mul_nonneg hcost (add_nonneg hCF hDF))
  have hMC : sobolevInverseCost 1 CF q*CF ≤ M := by
    rw [hMeq]
    linarith [mul_nonneg hcost hDF]
  have hMD : sobolevInverseCost 1 CF q*DF ≤ M := by
    rw [hMeq]
    linarith [mul_nonneg hcost hCF]
  have hAₓ : ContDiff ℝ ∞ Aₓ := frozenOperator_contDiff T hT B U g hg hB x
  have hFₓ : ContDiff ℝ ∞ Fₓ := frozenForcing_contDiff T hT B U g hg f a₀ hf ha₀ x
  have hu : ContDiff ℝ ∞ u := weightedSolution_contDiff T hT B U g hg f a₀ hB hf ha₀
  have hAb : ∀ j y, ‖iteratedFDeriv ℝ j Aₓ y‖ ≤ frozenAmplitude T C CB*majorant Rc 0 j :=
    frozenOperator_bound T hT B U g hg hB hg₀ C CB Rc hC hCB hRc hBb x hU
  have hbase : baseSize directions q Aₓ x ≤ CF :=
    baseSize_of_tensor_bound directions hd q Aₓ hAₓ Rc (frozenAmplitude T C CB) hRc hfrozen hAb x
  have hcoeff (j : ℕ) : coefficientBlock directions q Aₓ (j+1) x ≤
      CF*(sobolevCoefficientRadius ι Rc^(j+1)*((j+1).factorial : ℝ)^2) := by
    simpa only [majorant, Nat.add_zero, CF, forwardSobolevAmplitude] using
        coefficientBlock_of_tensor_bound directions hd q Aₓ hAₓ
      Rc (frozenAmplitude T C CB) hRc hfrozen hAb (j+1) x
  have hFb : ∀ j, block directions q Fₓ j x ≤ DF*majorant R d j :=
    frozenForcing_block_bound T hT B U g hg directions q f a₀ hf ha₀ hg₀ C A D R hC x hU d hforce
        hinitial
  exact block_inverse_gevrey_at directions q Aₓ u Fₓ hAₓ hu hFₓ
    (frozenOperator_equation T hT B U g hg f a₀ x) x
    (ContinuousLinearMap.id ℝ C(Icc (0 : ℝ) T,E))
    (fun v => by change Aₓ x v = v; rw [show Aₓ x = ContinuousLinearMap.id ℝ _ from
      frozenOperator_self T hT B U g hg x]; rfl)
    1 CF CF DF M (sobolevCoefficientRadius ι Rc) R hCF hDF hM hMC hMD
    (sobolevCoefficientRadius_nonneg Rc hRc) hR norm_id_le hbase hcoeff d hFb n

end EulerLinearDuhamel
