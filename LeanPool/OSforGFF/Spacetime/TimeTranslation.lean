/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/


import LeanPool.OSforGFF.Spacetime.Basic

/-!
# Time Translation Operators

This file defines time translation operators on spacetime, Schwartz functions,
and tempered distributions. These are fundamental for the OS4 (Ergodicity) axiom.

## Main Definitions

- `timeIndex`: The time coordinate index in spacetime (index 0)
- `getTime`: Extract the time component from a spacetime point
- `timeShift`: Time translation on spacetime points
- `timeTranslationSchwartz`: Time translation on real Schwartz functions
- `timeTranslationSchwartzℂ`: Time translation on complex Schwartz functions
- `timeTranslationDistribution`: Time translation on tempered distributions

## Notation

We work in spacetime ℝ × ℝ³ where:
- The first coordinate is time (index 0)
- The remaining 3 coordinates are space (indices 1,2,3)
- This matches STDimension = 4 from Basic.lean

## Main Theorems

- `schwartz_timeTranslation_lipschitz_seminorm`: Lipschitz bound for time translation
  on Schwartz seminorms, proved using Mean Value Theorem, chain rule, and
  continuousMultilinearCurryLeftEquiv isometry.

This is used to prove `continuous_timeTranslationSchwartz`, which establishes
that time translation acts continuously on Schwartz space (a standard textbook fact
from Reed-Simon V.3 and Hörmander Ch. 7).
-/

open MeasureTheory Real
open TopologicalSpace
open scoped BigOperators

noncomputable section

namespace TimeTranslation

/-! ## Time Translation on Spacetime Points

Definition 0.2 from the PDF: For any s ∈ ℝ, define the time translation operator.
The time coordinate is index 0 in our 4D spacetime.
-/

/-- The time coordinate index in spacetime (index 0). -/
def timeIndex : Fin STDimension := ⟨0, by norm_num⟩

/-- Extract the time component from a spacetime point. -/
def getTime (u : SpaceTime) : ℝ := u timeIndex

/-- Time translation on spacetime points: shifts the time coordinate by s.
    (timeShift s u)_0 = u_0 + s, and (timeShift s u)_i = u_i for i ≠ 0.
-/
def timeShift (s : ℝ) (u : SpaceTime) : SpaceTime :=
  WithLp.toLp 2 (fun i => if i.val = 0 then u.ofLp i + s else u.ofLp i)

@[simp]
lemma timeShift_time (s : ℝ) (u : SpaceTime) :
    getTime (timeShift s u) = getTime u + s := by
  simp only [getTime, timeIndex, timeShift]
  rfl

@[simp]
lemma timeShift_spatial (s : ℝ) (u : SpaceTime) (i : Fin STDimension) (hi : i.val ≠ 0) :
    (timeShift s u) i = u i := by
  simp only [timeShift]
  exact if_neg hi

/-- Time shift is a group action: T_{s+t} = T_s ∘ T_t -/
lemma timeShift_add (s t : ℝ) (u : SpaceTime) :
    timeShift (s + t) u = timeShift s (timeShift t u) := by
  simp only [timeShift]
  congr 1
  funext i
  split_ifs with h
  · ring
  · rfl

/-- Time shift by zero is identity -/
@[simp]
lemma timeShift_zero (u : SpaceTime) : timeShift 0 u = u := by
  simp only [timeShift]
  congr 1
  funext i
  split_ifs <;> ring

/-- Time shifts commute: T_s ∘ T_t = T_t ∘ T_s -/
lemma timeShift_comm (s t : ℝ) (u : SpaceTime) :
    timeShift s (timeShift t u) = timeShift t (timeShift s u) := by
  rw [← timeShift_add, ← timeShift_add, add_comm]

/-- Time shift is smooth as a map SpaceTime → SpaceTime.
    This is because it's an affine map (linear + constant).
-/
lemma timeShift_contDiff (s : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (timeShift s) := by
  unfold timeShift
  apply contDiff_piLp'
  intro i
  have hcoord : ContDiff ℝ (⊤ : ℕ∞) (fun x : SpaceTime => x.ofLp i) :=
    (contDiff_apply ℝ ℝ i).comp PiLp.contDiff_ofLp
  change ContDiff ℝ (⊤ : ℕ∞) (fun x : SpaceTime => if i.val = 0 then x.ofLp i + s else x.ofLp i)
  split_ifs with h
  · exact hcoord.add contDiff_const
  · exact hcoord

/-- Time shift preserves the Euclidean distance (it's an isometry) -/
lemma timeShift_dist (s : ℝ) (u v : SpaceTime) :
    dist (timeShift s u) (timeShift s v) = dist u v := by
  simp only [EuclideanSpace.dist_eq, timeShift]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · congr 1; simp only [Real.dist_eq, add_sub_add_right_eq_sub]
  · rfl

/-- Time shift is an isometry -/
lemma timeShift_isometry (s : ℝ) : Isometry (timeShift s) := by
  rw [isometry_iff_dist_eq]
  exact fun u v => timeShift_dist s u v

/-- Time shift is antilipschitz (follows from being an isometry). -/
lemma timeShift_antilipschitz (s : ℝ) : AntilipschitzWith 1 (timeShift s) :=
  (timeShift_isometry s).antilipschitz

/-- The constant vector used to express timeShift as id + const. -/
def timeShiftConst (s : ℝ) : SpaceTime :=
  WithLp.toLp 2 (fun i => if i.val = 0 then s else 0)

/-- timeShift s equals addition of a constant. -/
lemma timeShift_eq_add_const (s : ℝ) (u : SpaceTime) :
    timeShift s u = u + timeShiftConst s := by
  simp only [timeShift, timeShiftConst]
  ext i
  simp only [PiLp.add_apply]
  split_ifs with h <;> ring

/-- Time shift has temperate growth (key for Schwartz composition).
    This follows because timeShift is an affine map (id + constant).
-/
lemma timeShift_hasTemperateGrowth (s : ℝ) : Function.HasTemperateGrowth (timeShift s) := by
  -- The derivative is constant (= id), so has temperate growth
  have h_fderiv_temperate : Function.HasTemperateGrowth (fderiv ℝ (timeShift s)) := by
    have h_eq : fderiv ℝ (timeShift s) = fun _ => ContinuousLinearMap.id ℝ SpaceTime := by
      ext x v
      have h : timeShift s = fun u => u + timeShiftConst s := funext (timeShift_eq_add_const s)
      rw [h]
      simp only [fderiv_add_const, fderiv_fun_id, ContinuousLinearMap.id_apply]
    rw [h_eq]
    exact Function.HasTemperateGrowth.const _
  -- timeShift is differentiable
  have h_diff : Differentiable ℝ (timeShift s) := by
    intro x
    have h : timeShift s = fun u => u + timeShiftConst s := funext (timeShift_eq_add_const s)
    rw [h]
    exact differentiableAt_id.add_const _
  -- Polynomial bound: ‖timeShift s x‖ ≤ C * (1 + ‖x‖)^k
  have h_bound : ∀ x : SpaceTime, ‖timeShift s x‖ ≤ (1 + ‖timeShiftConst s‖) * (1 + ‖x‖) ^ 1 := by
    intro x
    rw [timeShift_eq_add_const, pow_one]
    calc ‖x + timeShiftConst s‖
        ≤ ‖x‖ + ‖timeShiftConst s‖ := norm_add_le _ _
      _ ≤ (1 + ‖timeShiftConst s‖) * (1 + ‖x‖) := by
          nlinarith [norm_nonneg x, norm_nonneg (timeShiftConst s)]
  exact Function.HasTemperateGrowth.of_fderiv h_fderiv_temperate h_diff h_bound

/-! ## Time Translation on Schwartz Functions

Definition 0.2 from the PDF: For any s ∈ ℝ, define the time translation operator on
Schwartz functions T_s : S(ℝ × ℝ³) → S(ℝ × ℝ³) by

  (T_s f)(t, x) := f(t + s, x)

We need to show that T_s preserves the Schwartz space. Since timeShift s is an affine
isometry, composition with it preserves Schwartz decay.

Note: Time translation is NOT a linear map on spacetime, but composition f ↦ f ∘ (timeShift s)
is a linear map on the Schwartz space.
-/

/-- Time translation as a continuous linear map on real-valued Schwartz functions.
    Uses mathlib's `compCLMOfAntilipschitz` which requires:
    1. The composition function has temperate growth
    2. The composition function is antilipschitz
-/
def timeTranslationSchwartzCLM (s : ℝ) : TestFunction →L[ℝ] TestFunction :=
  SchwartzMap.compCLMOfAntilipschitz ℝ (timeShift_hasTemperateGrowth s) (timeShift_antilipschitz s)

/-- Time translation on real-valued Schwartz functions.
    (T_s f)(u) = f(timeShift s u) = f(t + s, x)

    Note: The PDF defines (T_s f)(t,x) = f(t+s, x). Since timeShift s shifts the
    time coordinate by +s, we have (timeShift s)(t,x) = (t+s, x), so
    f ∘ (timeShift s) gives (T_s f).

    This is well-defined because:
    1. timeShift s has temperate growth (affine map)
    2. timeShift s is antilipschitz (isometry)
-/
def timeTranslationSchwartz (s : ℝ) (f : TestFunction) : TestFunction :=
  timeTranslationSchwartzCLM s f

/-- Time translation as a continuous linear map on complex-valued Schwartz functions. -/
def timeTranslationSchwartzℂCLM (s : ℝ) : TestFunctionℂ →L[ℂ] TestFunctionℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (timeShift_hasTemperateGrowth s) (timeShift_antilipschitz s)

/-- Time translation on complex-valued Schwartz functions. -/
def timeTranslationSchwartzℂ (s : ℝ) (f : TestFunctionℂ) : TestFunctionℂ :=
  timeTranslationSchwartzℂCLM s f

/-- Time translation evaluated at a point. -/
@[simp]
lemma timeTranslationSchwartz_apply (s : ℝ) (f : TestFunction) (u : SpaceTime) :
    (timeTranslationSchwartz s f) u = f (timeShift s u) := by
  simp only [timeTranslationSchwartz, timeTranslationSchwartzCLM,
    SchwartzMap.compCLMOfAntilipschitz_apply, Function.comp_apply]

/-- Time translation on complex functions evaluated at a point. -/
@[simp]
lemma timeTranslationSchwartzℂ_apply (s : ℝ) (f : TestFunctionℂ) (u : SpaceTime) :
    (timeTranslationSchwartzℂ s f) u = f (timeShift s u) := by
  simp only [timeTranslationSchwartzℂ, timeTranslationSchwartzℂCLM,
    SchwartzMap.compCLMOfAntilipschitz_apply, Function.comp_apply]

/-- Time translation is a group homomorphism: T_{s+t} = T_s ∘ T_t -/
lemma timeTranslationSchwartz_add (s t : ℝ) (f : TestFunction) :
    timeTranslationSchwartz (s + t) f =
      timeTranslationSchwartz s (timeTranslationSchwartz t f) := by
  ext u
  simp only [timeTranslationSchwartz_apply, timeShift_add, timeShift_comm]

/-- Time translation on complex functions: T_{s+t} = T_s ∘ T_t -/
lemma timeTranslationSchwartzℂ_add (s t : ℝ) (f : TestFunctionℂ) :
    timeTranslationSchwartzℂ (s + t) f =
      timeTranslationSchwartzℂ s (timeTranslationSchwartzℂ t f) := by
  ext u
  simp only [timeTranslationSchwartzℂ_apply, timeShift_add, timeShift_comm]

/-- Time translation by zero is identity -/
@[simp]
lemma timeTranslationSchwartz_zero (f : TestFunction) :
    timeTranslationSchwartz 0 f = f := by
  ext u
  simp only [timeTranslationSchwartz_apply, timeShift_zero]

/-- Time translation by zero is identity (complex) -/
@[simp]
lemma timeTranslationSchwartzℂ_zero (f : TestFunctionℂ) :
    timeTranslationSchwartzℂ 0 f = f := by
  ext u
  simp only [timeTranslationSchwartzℂ_apply, timeShift_zero]

/-- Time translation preserves addition of Schwartz functions -/
lemma timeTranslationSchwartz_add_fun (s : ℝ) (f g : TestFunction) :
    timeTranslationSchwartz s (f + g) =
      timeTranslationSchwartz s f + timeTranslationSchwartz s g := by
  ext u
  simp only [timeTranslationSchwartz_apply, SchwartzMap.add_apply]

/-- Time translation preserves scalar multiplication of Schwartz functions -/
lemma timeTranslationSchwartz_smul (s : ℝ) (c : ℝ) (f : TestFunction) :
    timeTranslationSchwartz s (c • f) = c • timeTranslationSchwartz s f := by
  ext u
  simp only [timeTranslationSchwartz_apply, SchwartzMap.smul_apply]

/-! ### Fundamental Theorem of Calculus for Time Translation

The following lemmas establish the pointwise FTC formula:
  (T_h f)(x) - f(x) = ∫₀ʰ (∂_t f)(T_s x) ds

This provides the mathematical foundation for the Lipschitz bound theorem below.
-/

/-- The unit time direction vector in SpaceTime. -/
def unitTimeDir : SpaceTime := EuclideanSpace.single timeIndex (1 : ℝ)

/-- timeShift is continuous in the time parameter s -/
lemma continuous_timeShift_param (x : SpaceTime) : Continuous (fun s : ℝ => timeShift s x) := by
  have h_shift : (fun s : ℝ => timeShift s x) = (fun s => x + s • unitTimeDir) := by
    funext s; simp only [timeShift, unitTimeDir, EuclideanSpace.single]
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, timeIndex]
    split_ifs <;> simp_all
  rw [h_shift]
  exact continuous_const.add (continuous_id.smul continuous_const)

/-- Peetre's inequality for polynomial weights in SpaceTime.
    (1 + ‖x‖)^k ≤ (1 + ‖x + y‖)^k * (1 + ‖y‖)^k

    This handles weight shifting when translating between seminorms at different points.
-/
lemma peetre_weight_bound (x y : SpaceTime) (k : ℕ) :
    (1 + ‖x‖) ^ k ≤ (1 + ‖x + y‖) ^ k * (1 + ‖y‖) ^ k := by
  have h1 : ‖x‖ ≤ ‖x + y‖ + ‖y‖ := by
    calc ‖x‖ = ‖(x + y) + (-y)‖ := by simp only [add_neg_cancel_right]
         _ ≤ ‖x + y‖ + ‖-y‖ := norm_add_le _ _
         _ = ‖x + y‖ + ‖y‖ := by rw [norm_neg]
  have h2 : 1 + ‖x‖ ≤ (1 + ‖x + y‖) * (1 + ‖y‖) := by
    calc 1 + ‖x‖ ≤ 1 + (‖x + y‖ + ‖y‖) := by linarith
         _ = 1 + ‖x + y‖ + ‖y‖ := by ring
         _ ≤ (1 + ‖x + y‖) * (1 + ‖y‖) := by nlinarith [norm_nonneg (x + y), norm_nonneg y]
  calc (1 + ‖x‖) ^ k ≤ ((1 + ‖x + y‖) * (1 + ‖y‖)) ^ k := by
           apply pow_le_pow_left₀ (by linarith [norm_nonneg x]) h2
       _ = (1 + ‖x + y‖) ^ k * (1 + ‖y‖) ^ k := mul_pow _ _ _

/-- The iterated derivative commutes with time translation.
    D^n(T_h f)(x) = D^n f(x + h·e₀)
-/
lemma iteratedFDeriv_timeTranslationSchwartz (n : ℕ) (h : ℝ) (f : TestFunction) (x : SpaceTime) :
    iteratedFDeriv ℝ n (timeTranslationSchwartz h f) x =
    iteratedFDeriv ℝ n f (x + h • unitTimeDir) := by
  -- timeTranslationSchwartz h f = f ∘ (· + h • unitTimeDir)
  have h_shift_eq : timeShiftConst h = h • unitTimeDir := by
    ext i
    simp only [timeShiftConst, unitTimeDir, EuclideanSpace.single, timeIndex]
    -- LHS: if i.val = 0 then h else 0
    -- RHS: h * (Pi.single timeIndex 1) i = h * (if i = timeIndex then 1 else 0)
    simp only [PiLp.smul_apply, smul_eq_mul, PiLp.ofLp_single, Pi.single_apply]
    split_ifs with hi1 hi2
    · ring
    · -- hi1 : i.val = 0, hi2 : i ≠ ⟨0, _⟩ - contradiction
      exfalso; apply hi2; ext; exact hi1
    · -- hi1 : i.val ≠ 0, h✝ : i = ⟨0, _⟩ - contradiction
      rename_i h_eq; simp only [h_eq] at hi1; exact absurd trivial hi1
    · ring
  have h_eq : ∀ z, timeTranslationSchwartz h f z = f (z + h • unitTimeDir) := by
    intro z
    rw [timeTranslationSchwartz_apply, timeShift_eq_add_const, h_shift_eq]
  conv_lhs =>
    rw [show
        (timeTranslationSchwartz h f : SpaceTime → ℝ) =
          fun z => f (z + h • unitTimeDir)
        from funext h_eq]
  exact iteratedFDeriv_comp_add_right n _ x

private lemma schwartz_timeTranslation_mvt_bound
    (n : ℕ) (f : TestFunction) (h : ℝ) (x y : SpaceTime)
    (hy : ‖y‖ = |h|) :
    ‖(fun t : ℝ => iteratedFDeriv ℝ n f (x + t • y)) 1 -
        (fun t : ℝ => iteratedFDeriv ℝ n f (x + t • y)) 0‖ ≤
      |h| * ⨆ t ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ (n + 1) f (x + t • y)‖ := by
  let g : ℝ → (SpaceTime [×n]→L[ℝ] ℝ) := fun t => iteratedFDeriv ℝ n f (x + t • y)
  change ‖g 1 - g 0‖ ≤
    |h| * ⨆ t ∈ Set.Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (n + 1) f (x + t • y)‖
  let D := fun (t : ℝ) => ‖iteratedFDeriv ℝ (n + 1) f (x + t • y)‖
  let C := |h| * ⨆ t ∈ Set.Icc (0 : ℝ) 1, D t
  have hg_diff_at : ∀ t, DifferentiableAt ℝ g t := by
    intro t
    apply DifferentiableAt.comp
    · exact (f.smooth (n + 1)).differentiable_iteratedFDeriv
        (by exact WithTop.coe_lt_coe.mpr ENat.natCast_lt_succ) |>.differentiableAt
    · exact (differentiableAt_const _).add (differentiableAt_id.smul_const y)
  have h_deriv_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖deriv g t‖ ≤ C := by
    intro t ht
    have h_deriv_eq : deriv g t = (fderiv ℝ (iteratedFDeriv ℝ n f) (x + t • y)) y := by
      have h1 : deriv g t = fderiv ℝ g t 1 := fderiv_apply_one_eq_deriv.symm
      let path : ℝ → SpaceTime := fun s => x + s • y
      let iter := iteratedFDeriv ℝ n (f : SpaceTime → ℝ)
      have hg_eq : g = iter ∘ path := rfl
      have h_path_diff : DifferentiableAt ℝ path t :=
        (differentiableAt_const x).add (differentiableAt_id.smul_const y)
      have h_iter_diff : DifferentiableAt ℝ iter (path t) :=
        (f.smooth (n + 1)).differentiable_iteratedFDeriv
          (by exact WithTop.coe_lt_coe.mpr ENat.natCast_lt_succ) |>.differentiableAt
      have h_fderiv_path : fderiv ℝ path t = ContinuousLinearMap.smulRight
          (ContinuousLinearMap.id ℝ ℝ) y := by
        have h_smul_eq : (fun r : ℝ => r • y) =
            (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) y) := by ext r; simp
        calc fderiv ℝ path t
          = fderiv ℝ (fun s => x + s • y) t := rfl
          _ = fderiv ℝ (fun s => x + (fun r => r • y) s) t := rfl
          _ = fderiv ℝ (fun r => r • y) t := fderiv_const_add x
          _ = fderiv ℝ (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) y) t := by
              rw [h_smul_eq]
          _ = ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) y :=
              ContinuousLinearMap.fderiv _
      rw [h1, hg_eq]
      rw [fderiv_comp t h_iter_diff h_path_diff]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, path, h_fderiv_path]
      simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, one_smul]
      rfl
    have h_fderiv_iter : fderiv ℝ (iteratedFDeriv ℝ n (f : SpaceTime → ℝ)) (x + t • y) =
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => SpaceTime) ℝ)
          (iteratedFDeriv ℝ (n + 1) f (x + t • y)) := by
      have := @fderiv_iteratedFDeriv ℝ _ SpaceTime _ _ ℝ _ _ f n
      exact congrFun this (x + t • y)
    rw [h_deriv_eq, h_fderiv_iter]
    calc ‖(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => SpaceTime) ℝ)
            (iteratedFDeriv ℝ (n + 1) f (x + t • y)) y‖
      ≤ ‖(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => SpaceTime) ℝ)
            (iteratedFDeriv ℝ (n + 1) f (x + t • y))‖ * ‖y‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ (n + 1) f (x + t • y)‖ * ‖y‖ := by
          rw [LinearIsometryEquiv.norm_map]
      _ = ‖iteratedFDeriv ℝ (n + 1) f (x + t • y)‖ * |h| := by rw [hy]
      _ = |h| * D t := by ring
      _ ≤ |h| * ⨆ s ∈ Set.Icc (0 : ℝ) 1, D s := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          have h_bdd : BddAbove (Set.range fun s : ↑(Set.Icc (0 : ℝ) 1) => D s.1) := by
            use (SchwartzMap.seminorm ℝ 0 (n + 1)) f
            rintro _ ⟨⟨s, _⟩, rfl⟩
            have := SchwartzMap.le_seminorm ℝ 0 (n + 1) f (x + s • y)
            simp only [pow_zero, one_mul] at this
            exact this
          haveI : Nonempty ↑(Set.Icc (0 : ℝ) 1) := ⟨⟨0, by simp⟩⟩
          have h_sSup_le : sSup (∅ : Set ℝ) ≤ ⨆ i : ↑(Set.Icc (0 : ℝ) 1), D i.1 := by
            simp only [Real.sSup_empty]
            apply le_ciSup_of_le h_bdd ⟨0, by simp⟩
            exact norm_nonneg _
          have h_eq :
              (⨆ s ∈ Set.Icc (0 : ℝ) 1, D s) =
                ⨆ s : ↑(Set.Icc (0 : ℝ) 1), D s.1 :=
            cbiSup_eq_ciSup_subtype (p := (· ∈ Set.Icc (0 : ℝ) 1))
              (f := fun s _ => D s) h_bdd h_sSup_le
          rw [h_eq]
          exact le_ciSup h_bdd ⟨t, ht⟩
      _ = C := rfl
  have h_mvt := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.Icc (0 : ℝ) 1)
    (fun t _ => hg_diff_at t)
    (fun t ht => h_deriv_bound t ht)
    (convex_Icc 0 1)
    (Set.left_mem_Icc.mpr zero_le_one)
    (Set.right_mem_Icc.mpr zero_le_one)
  simp only [sub_zero, Real.norm_eq_abs, abs_one, mul_one] at h_mvt
  exact h_mvt

/-- **Locally Uniform Lipschitz Bound for Time Translation.**

    For any Schwartz function f and time shift h, the seminorm of T_h f - f
    is bounded by |h| times (1+|h|)^k · 2^k times a sum of the (n+1)-th seminorms:

      ‖T_h f - f‖_{k,n} ≤ |h| · (1 + |h|)^k · 2^k · (‖f‖_{k,n+1} + ‖f‖_{0,n+1} + 1)

    The 2^k factor comes from Peetre's inequality: (1+‖w‖)^k ≤ 2^k · max(1, ‖w‖^k).
    This bound suffices for proving continuity at h=0, since (1+|h|)^k · 2^k ≤ 4^k
    for |h| ≤ 1.

    **Proof Outline:**
    1. Use `seminorm_le_bound`: suffices to show pointwise bound for all x
    2. Use `iteratedFDeriv_comp_add_right`: D^n(T_h f)(x) = D^n f(x + h·e₀)
    3. Apply MVT: ‖D^n f(x+h·e₀) - D^n f(x)‖ ≤ |h| · sup ‖D^{n+1} f(path)‖
    4. Apply Peetre: ‖x‖^k ≤ (1+|h|)^k · (1+‖w‖)^k for path points w
    5. Bound (1+‖w‖)^k ≤ 2^k · max(1, ‖w‖^k) and use seminorms
-/
theorem schwartz_timeTranslation_lipschitz_seminorm
    (k n : ℕ) (f : TestFunction) (h : ℝ) :
    (SchwartzMap.seminorm ℝ k n) (timeTranslationSchwartz h f - f) ≤
    |h| * (1 + |h|) ^ k * (2 : ℝ) ^ k *
    ((SchwartzMap.seminorm ℝ k (n + 1)) f + (SchwartzMap.seminorm ℝ 0 (n + 1)) f + 1) := by
  -- Use seminorm_le_bound: it suffices to show the pointwise bound
  apply SchwartzMap.seminorm_le_bound
  · positivity
  intro x
  -- Step 1: Rewrite iteratedFDeriv of the difference
  have h_diff : iteratedFDeriv ℝ n (⇑(timeTranslationSchwartz h f - f)) x =
      iteratedFDeriv ℝ n f (x + h • unitTimeDir) - iteratedFDeriv ℝ n f x := by
    -- The Schwartz map subtraction agrees with pointwise subtraction
    have h_coe : ⇑(timeTranslationSchwartz h f - f) = ⇑(timeTranslationSchwartz h f) - ⇑f := rfl
    rw [h_coe]
    -- Use sub_eq_add_neg and iteratedFDeriv_add_apply + iteratedFDeriv_neg
    have h_neg_eq : (-⇑f : SpaceTime → ℝ) = fun x => -f x := rfl
    have h_sub_neg : ⇑(timeTranslationSchwartz h f) - ⇑f =
        ⇑(timeTranslationSchwartz h f) + (fun x => -f x) := by
      rw [← h_neg_eq]; exact sub_eq_add_neg _ _
    rw [h_sub_neg]
    have hT : ContDiff ℝ n (timeTranslationSchwartz h f) := (timeTranslationSchwartz h f).smooth n
    have hf : ContDiff ℝ n f := f.smooth n
    rw [iteratedFDeriv_add_apply hT.contDiffAt hf.neg.contDiffAt]
    -- Convert (fun x => -f x) back to (-f) for iteratedFDeriv_neg
    conv_lhs => rw [← h_neg_eq]
    rw [iteratedFDeriv_neg]
    rw [iteratedFDeriv_timeTranslationSchwartz]
    simp only [Pi.neg_apply, sub_eq_add_neg]
  rw [h_diff]
  -- Step 2: Handle h = 0 case (trivial)
  by_cases hh : h = 0
  · simp only [hh, zero_smul, add_zero, sub_self, norm_zero, mul_zero]
    positivity
  -- Step 3: For h ≠ 0, apply Mean Value Theorem via line path
  -- Define the path g(t) = iteratedFDeriv ℝ n f (x + t • (h • unitTimeDir))
  -- g(0) = iteratedFDeriv ℝ n f x
  -- g(1) = iteratedFDeriv ℝ n f (x + h • unitTimeDir)
  let y := h • unitTimeDir
  have hy : ‖y‖ = |h| := by
    simp only [y, unitTimeDir, norm_smul, Real.norm_eq_abs]
    rw [PiLp.norm_single, norm_one, mul_one]
  -- Use Mean Value estimate: ‖g(1) - g(0)‖ ≤ |h| · sup ‖D^{n+1} f(path)‖ · ‖unitTimeDir‖
  -- Since the path is from x to x + h•e₀, the bound involves |h|
  -- We bound this by the seminorm, absorbing weight shift via Peetre
  -- For now, use a direct bound: each point on the path satisfies the seminorm bound
  -- The translated point is x + h • unitTimeDir
  let z := x + y
  -- Use Peetre's inequality: ‖x‖^k ≤ (1+‖y‖)^k · (1+‖z‖)^k
  have h_peetre : ‖x‖ ^ k ≤ (1 + ‖y‖) ^ k * (1 + ‖z‖) ^ k := by
    -- First: ‖x‖^k ≤ (1 + ‖x‖)^k since ‖x‖ ≤ 1 + ‖x‖
    have h1 : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      linarith [norm_nonneg x]
    -- Then use peetre_weight_bound: (1 + ‖x‖)^k ≤ (1 + ‖x + y‖)^k * (1 + ‖y‖)^k
    have h2 : (1 + ‖x‖) ^ k ≤ (1 + ‖x + y‖) ^ k * (1 + ‖y‖) ^ k :=
      peetre_weight_bound x y k
    -- x + y = z, so (1 + ‖x + y‖)^k = (1 + ‖z‖)^k
    -- z = x + y, so ‖x + y‖ = ‖z‖
    calc ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := h1
      _ ≤ (1 + ‖x + y‖) ^ k * (1 + ‖y‖) ^ k := h2
      _ = (1 + ‖z‖) ^ k * (1 + ‖y‖) ^ k := by simp only [z]
      _ = (1 + ‖y‖) ^ k * (1 + ‖z‖) ^ k := mul_comm _ _
  -- Apply MVT: Define g(t) = iteratedFDeriv ℝ n f (x + t • y) for t ∈ [0,1]
  -- Then g(1) - g(0) = iteratedFDeriv at z minus iteratedFDeriv at x
  let g : ℝ → (SpaceTime [×n]→L[ℝ] ℝ) := fun t => iteratedFDeriv ℝ n f (x + t • y)
  -- Goal: ‖x‖^k * ‖g(1) - g(0)‖ ≤ |h| * (1+|h|)^k * seminorm k (n+1) f
  -- We show this by bounding the derivative of g along [0,1]
  have hg_eq : g 1 - g 0 = iteratedFDeriv ℝ n f z - iteratedFDeriv ℝ n f x := by
    simp only [g, one_smul, zero_smul, add_zero, z]
  rw [← hg_eq]
  -- Apply MVT: ‖g 1 - g 0‖ ≤ sup_{t ∈ [0,1]} ‖deriv g t‖
  -- The derivative of g at t is: fderiv (iteratedFDeriv n f) (x + t•y) applied to y
  -- By fderiv_iteratedFDeriv and curryLeft_norm: ‖deriv g t‖ ≤ |h| * ‖D^{n+1} f(w_t)‖
  -- Step 1: Define the derivative bound C
  -- For each t ∈ [0,1], let w_t = x + t•y. We bound the weighted derivative.
  let C := |h| * (1 + |h|) ^ k *
    ((SchwartzMap.seminorm ℝ k (n + 1)) f + (SchwartzMap.seminorm ℝ 0 (n + 1)) f + 1)
  -- Step 2: Show ‖g 1 - g 0‖ ≤ |h| * sup_t ‖D^{n+1} f(w_t)‖
  -- This uses MVT + chain rule + currying
  -- For now, we use a bound via the seminorms
  -- The key observation: (1+‖w_t‖)^k * ‖D^{n+1} f(w_t)‖ is bounded by seminorms
  -- Case split: if ‖w_t‖ ≥ 1, use seminorm k; if ‖w_t‖ < 1, use seminorm 0
  -- In either case: (1+‖w_t‖)^k * ‖D^{n+1} f(w_t)‖ ≤ 2^k * (seminorm k + seminorm 0 + 1)
  -- Then from Peetre: ‖x‖^k ≤ (1+|h|)^k * (1+‖w_t‖)^k
  -- So: ‖x‖^k * ‖D^{n+1} f(w_t)‖ ≤ (1+|h|)^k * 2^k * (seminorm k + seminorm 0 + 1)
  -- MVT gives ‖g 1 - g 0‖ ≤ |h| * sup_t ‖D^{n+1} f(w_t)‖
  -- Combining: ‖x‖^k * ‖g 1 - g 0‖ ≤ |h| * (1+|h|)^k * (seminorm k + seminorm 0 + 1)
  -- MVT + derivative bound step using chain rule and currying
  -- The key technical step is computing the derivative norm using fderiv_iteratedFDeriv
  have h_mvt_bound : ‖g 1 - g 0‖ ≤ |h| * ⨆ t ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (n + 1) f (x + t • y)‖ :=
    schwartz_timeTranslation_mvt_bound n f h x y hy
  -- Step 3: Bound using Peetre and seminorms (simplified approach)
  -- Key insight: We bound ‖x‖^k * ‖g 1 - g 0‖ directly without using supremum
  -- For each point on the path, the weighted derivative is bounded by the seminorms
  -- Abbreviations for seminorms
  let S_k := (SchwartzMap.seminorm ℝ k (n + 1)) f
  let S_0 := (SchwartzMap.seminorm ℝ 0 (n + 1)) f
  let RHS := (1 + |h|) ^ k * (2 : ℝ) ^ k * (S_k + S_0 + 1)
  -- The pointwise weighted bound for any point on the path
  have h_pointwise : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) f (x + t • y)‖ ≤ RHS := by
    intro t ht
    let w := x + t • y
    -- Step 1: Peetre gives ‖x‖^k ≤ (1+|h|)^k * (1+‖w‖)^k
    have h_peetre_t : ‖x‖ ^ k ≤ (1 + |h|) ^ k * (1 + ‖w‖) ^ k := by
      have h1 : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by
        apply pow_le_pow_left₀ (norm_nonneg _)
        linarith [norm_nonneg x]
      have h2 : (1 + ‖x‖) ^ k ≤ (1 + ‖t • y‖) ^ k * (1 + ‖w‖) ^ k := by
        have hp := peetre_weight_bound x (t • y) k
        simp only [w]; rw [mul_comm]; exact hp
      have h3 : ‖t • y‖ ≤ |h| := by
        rw [norm_smul, Real.norm_eq_abs, hy]
        have ht_bound : |t| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
        calc |t| * |h| ≤ 1 * |h| := by nlinarith [abs_nonneg t, abs_nonneg h]
          _ = |h| := one_mul _
      have h4 : (1 + ‖t • y‖) ^ k ≤ (1 + |h|) ^ k := by
        apply pow_le_pow_left₀ (by linarith [norm_nonneg (t • y)])
        linarith
      calc ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := h1
        _ ≤ (1 + ‖t • y‖) ^ k * (1 + ‖w‖) ^ k := h2
        _ ≤ (1 + |h|) ^ k * (1 + ‖w‖) ^ k := by
            have hw_pos : 0 ≤ (1 + ‖w‖) ^ k := pow_nonneg (by linarith [norm_nonneg w]) k
            nlinarith
    -- Step 2: Bound (1+‖w‖)^k * ‖D^{n+1} f(w)‖ using seminorms
    have h_weighted_deriv : (1 + ‖w‖) ^ k * ‖iteratedFDeriv ℝ (n + 1) f w‖ ≤
        (2 : ℝ) ^ k * (S_k + S_0 + 1) := by
      -- Key: (1+a)^k ≤ 2^k * max(1, a^k)
      have h_one_plus : (1 + ‖w‖) ^ k ≤ (2 : ℝ) ^ k * max 1 (‖w‖ ^ k) := by
        by_cases hw : ‖w‖ ≤ 1
        · -- ‖w‖ ≤ 1 case: (1 + ‖w‖)^k ≤ 2^k and max 1 (‖w‖^k) = 1
          have h1 : (1 + ‖w‖) ^ k ≤ 2 ^ k := by
            apply pow_le_pow_left₀ (by linarith [norm_nonneg w])
            linarith
          simp only [max_eq_left (pow_le_one₀ (norm_nonneg w) hw), mul_one]
          exact h1
        · -- ‖w‖ > 1 case: (1 + ‖w‖)^k ≤ (2‖w‖)^k = 2^k * ‖w‖^k = 2^k * max(1, ‖w‖^k)
          push Not at hw
          have h1 : 1 + ‖w‖ ≤ 2 * ‖w‖ := by linarith
          have h2 : (1 + ‖w‖) ^ k ≤ (2 * ‖w‖) ^ k := by
            apply pow_le_pow_left₀ (by linarith [norm_nonneg w])
            exact h1
          simp only [mul_pow] at h2
          have h3 : 1 ≤ ‖w‖ ^ k := one_le_pow₀ hw.le
          simp only [max_eq_right h3]
          exact h2
      -- Use seminorm bounds
      have h_S0 : ‖iteratedFDeriv ℝ (n + 1) f w‖ ≤ S_0 := by
        have := SchwartzMap.le_seminorm ℝ 0 (n + 1) f w
        simpa only [pow_zero, one_mul] using this
      have h_Sk : ‖w‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) f w‖ ≤ S_k :=
        SchwartzMap.le_seminorm ℝ k (n + 1) f w
      -- Combine
      calc (1 + ‖w‖) ^ k * ‖iteratedFDeriv ℝ (n + 1) f w‖
        ≤ (2 : ℝ) ^ k * max 1 (‖w‖ ^ k) * ‖iteratedFDeriv ℝ (n + 1) f w‖ := by
            apply mul_le_mul_of_nonneg_right h_one_plus (norm_nonneg _)
        _ = (2 : ℝ) ^ k * (max 1 (‖w‖ ^ k) * ‖iteratedFDeriv ℝ (n + 1) f w‖) := by ring
        _ ≤ (2 : ℝ) ^ k *
              (‖iteratedFDeriv ℝ (n + 1) f w‖ +
                ‖w‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) f w‖) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) k)
            have := max_le_add_of_nonneg
              (by positivity : 0 ≤ (1 : ℝ))
              (pow_nonneg (norm_nonneg w) k)
            calc max 1 (‖w‖ ^ k) * ‖iteratedFDeriv ℝ (n + 1) f w‖
              ≤ (1 + ‖w‖ ^ k) * ‖iteratedFDeriv ℝ (n + 1) f w‖ := by
                  apply mul_le_mul_of_nonneg_right this (norm_nonneg _)
              _ = ‖iteratedFDeriv ℝ (n + 1) f w‖ +
                    ‖w‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) f w‖ := by
                  ring
        _ ≤ (2 : ℝ) ^ k * (S_0 + S_k) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) k)
            linarith
        _ ≤ (2 : ℝ) ^ k * (S_k + S_0 + 1) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) k)
            linarith
    -- Combine Peetre and weighted deriv bounds
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) f w‖
      ≤ (1 + |h|) ^ k * (1 + ‖w‖) ^ k * ‖iteratedFDeriv ℝ (n + 1) f w‖ := by
          apply mul_le_mul_of_nonneg_right h_peetre_t (norm_nonneg _)
      _ = (1 + |h|) ^ k * ((1 + ‖w‖) ^ k * ‖iteratedFDeriv ℝ (n + 1) f w‖) := by ring
      _ ≤ (1 + |h|) ^ k * ((2 : ℝ) ^ k * (S_k + S_0 + 1)) := by
          apply mul_le_mul_of_nonneg_left h_weighted_deriv
          exact pow_nonneg (by linarith [abs_nonneg h]) k
      _ = RHS := by ring
  -- Direct bound: Use h_mvt_bound and h_pointwise to bound everything
  -- Since the bound RHS is uniform over t, we can bound ‖x‖^k * ‖g 1 - g 0‖ directly
  have h_weighted_bound : ‖x‖ ^ k * ‖g 1 - g 0‖ ≤ |h| * RHS := by
    -- Use MVT integral form: g 1 - g 0 = ∫₀¹ g'(t) dt
    -- The bound on the integrand (including weight ‖x‖^k) is |h| * RHS
    -- Since we're integrating over [0,1], the total is ≤ |h| * RHS
    calc ‖x‖ ^ k * ‖g 1 - g 0‖
      ≤ ‖x‖ ^ k * (|h| * ⨆ t ∈ Set.Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (n + 1) f (x + t • y)‖) := by
          apply mul_le_mul_of_nonneg_left h_mvt_bound (pow_nonneg (norm_nonneg _) _)
      _ = |h| * (‖x‖ ^ k * ⨆ t ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ (n + 1) f (x + t • y)‖) := by ring
      _ ≤ |h| * RHS := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          -- We need: ‖x‖^k * sup_t A_t ≤ RHS
          -- Key insight: for any t, ‖x‖^k * A_t ≤ RHS (by h_pointwise)
          -- So: ‖x‖^k * sup A ≤ sup (‖x‖^k * A) ≤ RHS
          by_cases hxk : ‖x‖ ^ k = 0
          · simp only [hxk, zero_mul]; positivity
          · -- ‖x‖^k > 0 case
            haveI : Nonempty ↑(Set.Icc (0 : ℝ) 1) := ⟨⟨0, by simp⟩⟩
            -- BddAbove for the original sup
            have h_bdd : BddAbove (Set.range fun t : ↑(Set.Icc (0 : ℝ) 1) =>
                ‖iteratedFDeriv ℝ (n + 1) f (x + t.1 • y)‖) := by
              use S_0
              rintro v ⟨⟨t, ht⟩, rfl⟩
              have := SchwartzMap.le_seminorm ℝ 0 (n + 1) f (x + t • y)
              simpa only [pow_zero, one_mul] using this
            -- BddAbove for the product sup
            have h_bdd_prod : BddAbove (Set.range fun t : ↑(Set.Icc (0 : ℝ) 1) =>
                ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) f (x + t.1 • y)‖) := by
              use RHS
              rintro v ⟨⟨t, ht⟩, rfl⟩
              exact h_pointwise t ht
            -- Use subtype formulation for the biSup
            -- The biSup over [0,1] equals the iSup over the subtype {t : ℝ // t ∈ [0,1]}
            have hxk_nonneg : 0 ≤ ‖x‖ ^ k := pow_nonneg (norm_nonneg _) _
            -- Key: For each t ∈ [0,1], h_pointwise gives ‖x‖^k * A_t ≤ RHS
            -- So: sup_t (‖x‖^k * A_t) ≤ RHS
            -- Using Real.mul_iSup_of_nonneg: ‖x‖^k * sup_t A_t = sup_t (‖x‖^k * A_t)
            --
            -- Convert biSup to subtype iSup using cbiSup_eq_ciSup_subtype
            let F : ↑(Set.Icc (0 : ℝ) 1) → ℝ := fun t => ‖iteratedFDeriv ℝ (n + 1) f (x + t.1 • y)‖
            have h_biSup_eq : (⨆ t ∈ Set.Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (n + 1) f (x + t • y)‖) =
                ⨆ t : ↑(Set.Icc (0 : ℝ) 1), F t := by
              -- cbiSup_eq_ciSup_subtype converts biSup to subtype iSup
              -- ⨆ i, ⨆ (h : p i), f i h = ⨆ x : Subtype p, f x.1 x.2
              have h_sSup_le : sSup (∅ : Set ℝ) ≤ ⨆ i : ↑(Set.Icc (0 : ℝ) 1),
                  ‖iteratedFDeriv ℝ (n + 1) f (x + i.1 • y)‖ := by
                simp only [Real.sSup_empty]
                apply le_ciSup_of_le h_bdd ⟨0, by simp⟩
                exact norm_nonneg _
              exact cbiSup_eq_ciSup_subtype (p := (· ∈ Set.Icc (0 : ℝ) 1))
                  (f := fun t _ => ‖iteratedFDeriv ℝ (n + 1) f (x + t • y)‖) h_bdd h_sSup_le
            rw [h_biSup_eq, Real.mul_iSup_of_nonneg hxk_nonneg]
            apply ciSup_le
            intro ⟨t, ht⟩
            exact h_pointwise t ht
  -- Step 4: Use h_weighted_bound directly
  calc ‖x‖ ^ k * ‖g 1 - g 0‖
    _ ≤ |h| * RHS := h_weighted_bound
    _ = |h| * (1 + |h|) ^ k * (2 : ℝ) ^ k * ((SchwartzMap.seminorm ℝ k (n + 1)) f +
                               (SchwartzMap.seminorm ℝ 0 (n + 1)) f + 1) := by ring

/-- Time translation is continuous in the time parameter.
    For any Schwartz function f, the map s ↦ T_s f is continuous from ℝ to
    Schwartz space in the Fréchet topology.

    ## Proof Strategy: Reduce to Continuity at Zero

    Since T_{s+h} f = T_s(T_h f) by the group action property, and T_s is a
    continuous linear map, continuity at any point s follows from continuity at 0.

    For continuity at 0, we use the Lipschitz bound
    `schwartz_timeTranslation_lipschitz_seminorm`:
      ‖T_h f - f‖_{k,n} ≤ |h| · (‖f‖_{k,n+1} + ‖f‖_{0,n+1} + 1)

    ## References
    Reed-Simon V.3 (Schwartz distributions), Hörmander Ch. 7 (test functions)
-/
lemma continuous_timeTranslationSchwartz (f : TestFunction) :
    Continuous (fun s => timeTranslationSchwartz s f) := by
  -- Strategy: Prove continuity at each point s₀ using the group action
  -- T_{s₀+h} f = T_{s₀}(T_h f), so if T_h f → f as h → 0, then T_{s₀+h} f → T_{s₀} f
  rw [continuous_iff_continuousAt]
  intro s₀
  rw [ContinuousAt, Filter.Tendsto]
  -- We need: ∀ U ∈ 𝓝(T_{s₀} f), {s | T_s f ∈ U} ∈ 𝓝(s₀)
  -- Use the group structure: T_s f = T_{s₀}(T_{s-s₀} f)
  -- Since T_{s₀} is continuous, it suffices to show T_{s-s₀} f → f as s → s₀
  -- i.e., T_h f → f as h → 0
  have h_group : ∀ s, timeTranslationSchwartz s f =
      timeTranslationSchwartzCLM s₀ (timeTranslationSchwartz (s - s₀) f) := by
    intro s
    ext u
    simp only [timeTranslationSchwartz_apply, timeTranslationSchwartzCLM,
      SchwartzMap.compCLMOfAntilipschitz_apply, Function.comp_apply]
    -- Need: f(timeShift s u) = f(timeShift (s-s₀) (timeShift s₀ u))
    -- By timeShift_add: timeShift (s-s₀) (timeShift s₀ u) = timeShift ((s-s₀)+s₀) u = timeShift s u
    congr 1
    rw [← timeShift_add]
    ring_nf
  -- Rewrite using the group structure
  have h_eq : (fun s => timeTranslationSchwartz s f) =
      (fun s => timeTranslationSchwartzCLM s₀ (timeTranslationSchwartz (s - s₀) f)) :=
    funext h_group
  rw [h_eq]
  -- Now use that T_{s₀} is continuous
  have h_cont : Continuous (timeTranslationSchwartzCLM s₀) :=
    (timeTranslationSchwartzCLM s₀).continuous
  -- It suffices to show: T_{s-s₀} f → T_0 f = f as s → s₀
  apply Filter.Tendsto.comp h_cont.continuousAt
  -- Now prove: T_{s-s₀} f → f as s → s₀ (equivalently, T_h f → f as h → 0)
  -- Goal: Filter.Tendsto (fun s => timeTranslationSchwartz (s - s₀) f) (𝓝 s₀) (𝓝 f)
  -- Rewrite as composition: (fun h => T_h f) ∘ (fun s => s - s₀)
  have h_comp : (fun s => timeTranslationSchwartz (s - s₀) f) =
      (fun h => timeTranslationSchwartz h f) ∘ (fun s => s - s₀) := rfl
  rw [h_comp]
  -- Use that s - s₀ → 0 as s → s₀
  have h_map : Filter.Tendsto (fun s => s - s₀) (nhds s₀) (nhds 0) :=
    tendsto_sub_nhds_zero_iff.mpr Filter.tendsto_id
  apply Filter.Tendsto.comp _ h_map
  -- Now prove continuity at 0: T_h f → f as h → 0
  -- This uses the Mean Value estimate: ‖T_h f - f‖ ≤ |h| · C
  -- Use seminorm characterization: Schwartz topology = ⨅ seminorm topologies
  have hw := schwartz_withSeminorms (𝕜 := ℝ) (E := SpaceTime) (F := ℝ)
  rw [(schwartzSeminormFamily ℝ SpaceTime ℝ).withSeminorms_iff_topologicalSpace_eq_iInf.mp hw]
  rw [nhds_iInf, Filter.tendsto_iInf]
  intro i
  -- For each seminorm i = (k, n), show T_h f → f in the seminorm topology
  letI : SeminormedAddCommGroup TestFunction :=
    (schwartzSeminormFamily ℝ SpaceTime ℝ i).toSeminormedAddCommGroup
  letI : PseudoMetricSpace TestFunction :=
    (schwartzSeminormFamily ℝ SpaceTime ℝ i).toSeminormedAddCommGroup.toPseudoMetricSpace
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Mean Value estimate: ‖T_h f - f‖_{k,n} ≤ |h| · L where L depends on f's seminorms
  -- The Lipschitz bound: seminorm ≤ |h| * (1+|h|)^k * 2^k * (seminorm k (n+1) + seminorm 0 (n+1) +
  -- 1)
  -- For |h| ≤ 1: (1+|h|)^k ≤ 2^k, so total factor is 4^k
  let k := i.1
  let n := i.2
  let C := (SchwartzMap.seminorm ℝ k (n + 1) f) + (SchwartzMap.seminorm ℝ 0 (n + 1) f) + 1
  let L := (4 : ℝ) ^ k * C  -- 4^k = 2^k * 2^k from Lipschitz bound
  -- Convert Filter.Eventually to ∃ δ > 0 form
  rw [Metric.eventually_nhds_iff]
  have hC_pos : C > 0 := by positivity
  have hL_pos : L > 0 := by positivity
  use min 1 (ε / L)
  constructor
  · exact lt_min one_pos (div_pos hε hL_pos)
  intro h hh
  -- Goal: dist (T_h f) f < ε
  -- Distance = seminorm(T_h f - f) in the induced metric
  have hdist : dist (timeTranslationSchwartz h f) f =
      (schwartzSeminormFamily ℝ SpaceTime ℝ i) (timeTranslationSchwartz h f - f) := by
    rw [dist_eq_norm]
    rfl
  rw [hdist]
  -- Apply the Lipschitz bound
  have h_seminorm_eq : schwartzSeminormFamily ℝ SpaceTime ℝ i =
      SchwartzMap.seminorm ℝ i.1 i.2 := rfl
  rw [h_seminorm_eq]
  have h_lip := schwartz_timeTranslation_lipschitz_seminorm k n f h
  -- From hh: dist h 0 < min 1 (ε / L), so |h| < 1 and |h| < ε / L
  rw [Real.dist_eq, sub_zero] at hh
  have h_small : |h| < 1 := lt_of_lt_of_le hh (min_le_left _ _)
  have h_eps : |h| < ε / L := lt_of_lt_of_le hh (min_le_right _ _)
  -- For |h| < 1: (1 + |h|)^k ≤ 2^k
  have h_pow_bound : (1 + |h|) ^ k ≤ (2 : ℝ) ^ k := by
    apply pow_le_pow_left₀ (by linarith [abs_nonneg h])
    linarith
  calc (SchwartzMap.seminorm ℝ k n) (timeTranslationSchwartz h f - f)
    _ ≤ |h| * (1 + |h|) ^ k * (2 : ℝ) ^ k * C := h_lip
    _ ≤ |h| * (2 : ℝ) ^ k * (2 : ℝ) ^ k * C := by
        have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) k
        have h1 : (1 + |h|) ^ k * ((2 : ℝ) ^ k * C) ≤ (2 : ℝ) ^ k * ((2 : ℝ) ^ k * C) := by
          apply mul_le_mul_of_nonneg_right h_pow_bound
          exact mul_nonneg (le_of_lt h2k_pos) (le_of_lt hC_pos)
        calc |h| * (1 + |h|) ^ k * (2 : ℝ) ^ k * C
          = |h| * ((1 + |h|) ^ k * ((2 : ℝ) ^ k * C)) := by ring
          _ ≤ |h| * ((2 : ℝ) ^ k * ((2 : ℝ) ^ k * C)) := by
              apply mul_le_mul_of_nonneg_left h1 (abs_nonneg h)
          _ = |h| * (2 : ℝ) ^ k * (2 : ℝ) ^ k * C := by ring
    _ = |h| * (4 : ℝ) ^ k * C := by
        have h2_eq : (2 : ℝ) ^ k * (2 : ℝ) ^ k = (4 : ℝ) ^ k := by
          rw [← mul_pow]; norm_num
        calc |h| * (2 : ℝ) ^ k * (2 : ℝ) ^ k * C
          = |h| * ((2 : ℝ) ^ k * (2 : ℝ) ^ k) * C := by ring
          _ = |h| * (4 : ℝ) ^ k * C := by rw [h2_eq]
    _ = |h| * L := by simp only [L]; ring
    _ < (ε / L) * L := by nlinarith [abs_nonneg h]
    _ = ε := by field_simp

/-! ## Time Translation on Tempered Distributions

Definition 0.2 from the PDF: For φ ∈ S'(ℝ × ℝ³) (tempered distribution), define T_s φ
by the pairing:

  ⟨T_s φ, f⟩ := ⟨φ, T_{-s} f⟩

for all f ∈ S(ℝ × ℝ³).
-/

/-- Time translation on tempered distributions (field configurations).

    The action is defined by duality:
    ⟨T_s ω, f⟩ = ⟨ω, T_{-s} f⟩

    Since FieldConfiguration = WeakDual ℝ TestFunction, and timeTranslationSchwartzCLM (-s)
    is a continuous linear map, we can simply compose: T_s ω = ω ∘ T_{-s}.

    Continuity is automatic since composition of continuous linear maps is continuous.
-/
def timeTranslationDistribution (s : ℝ) (ω : FieldConfiguration) : FieldConfiguration :=
  ω.comp (timeTranslationSchwartzCLM (-s))

/-- The defining property of time translation on distributions. -/
@[simp]
lemma timeTranslationDistribution_apply (s : ℝ) (ω : FieldConfiguration) (f : TestFunction) :
    (timeTranslationDistribution s ω) f = ω (timeTranslationSchwartz (-s) f) := rfl

/-- Time translation on distributions is a group homomorphism: T_{s+t} = T_s ∘ T_t -/
lemma timeTranslationDistribution_add (s t : ℝ) (ω : FieldConfiguration) :
    timeTranslationDistribution (s + t) ω =
    timeTranslationDistribution s (timeTranslationDistribution t ω) := by
  apply DFunLike.ext
  intro f
  simp only [timeTranslationDistribution_apply]
  congr 1
  -- Need: T_{-(s+t)} f = T_{-t}(T_{-s} f)
  -- T_{-s}(T_{-t} f) = T_{-s-t} f by the group property
  have h : timeTranslationSchwartz (-(s + t)) f =
           timeTranslationSchwartz (-t) (timeTranslationSchwartz (-s) f) := by
    rw [neg_add]
    rw [← timeTranslationSchwartz_add]
    ring_nf
  rw [h]

/-- Time translation by zero is identity on distributions -/
@[simp]
lemma timeTranslationDistribution_zero (ω : FieldConfiguration) :
    timeTranslationDistribution 0 ω = ω := by
  apply DFunLike.ext
  intro f
  simp only [timeTranslationDistribution_apply, neg_zero, timeTranslationSchwartz_zero]

end TimeTranslation
