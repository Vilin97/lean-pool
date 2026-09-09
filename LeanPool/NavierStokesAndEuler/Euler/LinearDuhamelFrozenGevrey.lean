/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelFrozenOperator
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevBlocks
import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathCalculus
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Quantitative bounds for the actual frozen forward equation

The frozen coefficient has a polynomial tensor multiplier bound derived
from the original coefficient and the H3 Green bound. Its fixed-Sobolev
forcing block is bounded directly by the original initial/forcing blocks.
No profile extremum, inverse amplitude, or raw weighted primitive is used.
-/

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
