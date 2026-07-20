/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Parametric Calculus

General-purpose lemmas for iterated Fréchet derivatives and parametric integrals,
not yet available in Mathlib. Used as building blocks in the SchwartzNuclear proofs.

## Main results

- `norm_iteratedFDeriv_iteratedFDeriv` — **Currying isometry**: composing two levels of
  iterated derivatives preserves norms.
- `contDiff_schwartz_parametric_integral` — **Leibniz integral rule (C^∞)**: if a Schwartz
  function is integrated against another Schwartz function along a smooth parametric embedding,
  the result is C^∞ and derivatives commute with the integral.
-/

open MeasureTheory SchwartzMap
open scoped ContDiff

/-! ### Helper: currying isometry with NormedAddCommGroup instances

The `continuousMultilinearCurryLeftEquiv` is parameterized by `SeminormedAddCommGroup`
instances, while `LinearIsometryEquiv.norm_iteratedFDeriv_comp_left` requires
`NormedAddCommGroup`. We rebuild the isometry with explicit `NormedAddCommGroup`
instances to resolve this diamond.
-/

private noncomputable def curryLeftLIE {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) :=
  let L := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F).symm
  @LinearIsometryEquiv.mk ℝ ℝ _ _ (RingHom.id ℝ) (RingHom.id ℝ) _ _
    (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F)
    (ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => E) F)
    NormedAddCommGroup.toSeminormedAddCommGroup
    NormedAddCommGroup.toSeminormedAddCommGroup
    NormedSpace.toModule NormedSpace.toModule
    L.toLinearEquiv L.norm_map'

private lemma curryLeftLIE_coe_eq {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) :
    ⇑(curryLeftLIE (E := E) (F := F) k) =
    ⇑(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F).symm := rfl

/-- **Textbook: Currying isometry for iterated Fréchet derivatives.**

`‖iteratedFDeriv n (iteratedFDeriv l' f) z‖ = ‖iteratedFDeriv (n + l') f z‖`

Proof by induction on `l'`. The key difficulty is a typeclass diamond: the
`SeminormedAddCommGroup` instances on `ContinuousMultilinearMap` and `ContinuousLinearMap`
differ from those derived from `NormedAddCommGroup`, preventing direct use of
`LinearIsometryEquiv.norm_iteratedFDeriv_comp_left`. We resolve this by rebuilding the
currying isometry with explicit `NormedAddCommGroup` instances via `curryLeftLIE`.
-/
lemma norm_iteratedFDeriv_iteratedFDeriv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (n l' : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ n (iteratedFDeriv ℝ l' f) z‖ =
      ‖iteratedFDeriv ℝ (n + l') f z‖ := by
  revert n
  induction l' with
  | zero =>
    intro n
    simp only [Nat.add_zero]
    rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.norm_iteratedFDeriv_comp_left f z n
  | succ k ih =>
    intro n
    rw [iteratedFDeriv_succ_eq_comp_left (f := f) (n := k)]
    rw [show ⇑(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F).symm =
      ⇑(curryLeftLIE (E := E) (F := F) k) from (curryLeftLIE_coe_eq k).symm]
    rw [(curryLeftLIE k).norm_iteratedFDeriv_comp_left, norm_iteratedFDeriv_fderiv, ih (n + 1)]
    conv_lhs => rw [show n + 1 + k = n + (k + 1) from by omega]

/-! ### Leibniz integral rule for Schwartz integrands

The proof uses a "double induction" on `I n y := ∫ t, D^n_y[Φ_t(t)](y)`:
1. `I_diff`: each `I n` is differentiable with `fderiv = (curryLeftLIE n).symm ∘ I(n+1)`
2. `I_contDiff`: `ContDiff m (I n)` by induction on `m`, shifting `n`
3. `h_iter`: `iteratedFDeriv m Φ = I m` by induction on `m`

The `hι_meas` hypothesis provides measurability of the parametric iterated
derivatives `t ↦ D^m_y[f(ι(·,t))](y)`. In all applications (e.g., `ι = euclideanSnoc`),
this follows from joint smoothness of `ι` via `Continuous.aestronglyMeasurable`.
-/

/-- **Leibniz integral rule (C^∞, Schwartz integrand).**

Given a Schwartz function `f` on `E`, a Schwartz function `g` on `ℝ`, and
a parametric embedding `ι : H → ℝ → E`, if:
- for each `t`, `y ↦ ι(y,t)` is C^∞,
- for each `m`, `t ↦ D^m_y[f(ι(·,t))](y)` is ae-strongly-measurable, and
- for each derivative order `m`, `‖D^m_y[f(ι(·,t))](y)‖` is uniformly bounded,

then `y ↦ ∫_t f(ι(y,t)) · g(t) dt` is C^∞ and `D^m` commutes with `∫`.

**Reference**: Folland, "Real Analysis", Theorem 2.27 (iterated version).
-/
lemma contDiff_schwartz_parametric_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : SchwartzMap E ℝ) (g : SchwartzMap ℝ ℝ)
    (ι : H → ℝ → E)
    (hι_smooth : ∀ t, ContDiff ℝ ∞ (ι · t))
    (hι_meas : ∀ (m : ℕ) (y : H), AEStronglyMeasurable
      (fun t => iteratedFDeriv ℝ m (fun y' => f (ι y' t)) y) volume)
    (hι_bound : ∀ m : ℕ, ∃ C : ℝ, ∀ y t,
      ‖iteratedFDeriv ℝ m (fun y' => f (ι y' t)) y‖ ≤ C) :
    ContDiff ℝ ∞ (fun y => ∫ t, f (ι y t) * g t) ∧
    ∀ (m : ℕ) (y : H),
      iteratedFDeriv ℝ m (fun y' => ∫ t, f (ι y' t) * g t) y =
      ∫ t, iteratedFDeriv ℝ m (fun y' => f (ι y' t) * g t) y := by
  -- Abbreviations
  set Φ_t : ℝ → H → ℝ := fun t y => f (ι y t) * g t with hΦ_t_def
  set Φ : H → ℝ := fun y => ∫ t, Φ_t t y with hΦ_def
  -- Each inner function y ↦ f(ι(y,t)) is C^∞
  have inner_smooth : ∀ t, ContDiff ℝ ∞ (fun y => f (ι y t)) :=
    fun t => (f.smooth ⊤).comp (hι_smooth t)
  -- Each integrand y ↦ Φ_t(t,y) is C^∞ in y
  have Φ_t_smooth : ∀ t, ContDiff ℝ ∞ (Φ_t t) := by
    intro t; exact (inner_smooth t).mul contDiff_const
  -- Factorization: iteratedFDeriv m (Φ_t t) y = g t • iteratedFDeriv m (f ∘ ι · t) y
  have hΦ_t_deriv : ∀ (m : ℕ) (y : H) (t : ℝ),
      iteratedFDeriv ℝ m (Φ_t t) y =
      g t • iteratedFDeriv ℝ m (fun y' => f (ι y' t)) y := by
    intro m y t
    have h_eq : Φ_t t = fun y' => g t • f (ι y' t) := by ext y'; simp [Φ_t, mul_comm, smul_eq_mul]
    rw [h_eq]
    exact iteratedFDeriv_const_smul_apply'
      ((inner_smooth t).of_le (by exact_mod_cast le_top) |>.contDiffAt)
  -- Integrand bound: ‖iteratedFDeriv m (Φ_t t) y‖ ≤ C * ‖g t‖
  have h_bound : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y t,
      ‖iteratedFDeriv ℝ m (Φ_t t) y‖ ≤ C * ‖g t‖ := by
    intro m
    obtain ⟨C, hC⟩ := hι_bound m
    refine ⟨max C 0, le_max_right _ _, fun y t => ?_⟩
    rw [hΦ_t_deriv, norm_smul (α := ℝ)]
    calc ‖g t‖ * ‖iteratedFDeriv ℝ m (fun y ↦ f (ι y t)) y‖
        ≤ ‖g t‖ * max C 0 :=
          mul_le_mul_of_nonneg_left
            (le_trans (hC y t) (le_max_left C 0)) (norm_nonneg _)
      _ = max C 0 * ‖g t‖ := mul_comm _ _
  -- g is integrable
  have g_integrable : Integrable (fun t => g t) := g.integrable
  -- Measurability of integrands at each derivative order
  have Φ_t_meas : ∀ (m : ℕ) (y : H),
      AEStronglyMeasurable (fun t => iteratedFDeriv ℝ m (Φ_t t) y) volume := by
    intro m y
    simp_rw [hΦ_t_deriv m y]
    exact g.continuous.aestronglyMeasurable.smul (hι_meas m y)
  -- Raw integrability of Φ_t t y as a function of t (ℝ-valued)
  have Φ_t_raw_integrable : ∀ (y : H), Integrable (fun t => Φ_t t y) volume := by
    intro y
    obtain ⟨C, hC_pos, hC⟩ := h_bound 0
    have hC' : ∀ y t, ‖Φ_t t y‖ ≤ C * ‖g t‖ := fun y t => by
      simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
        LinearIsometryEquiv.norm_map] using hC y t
    exact (g_integrable.norm.const_mul C).mono
      (by -- measurability of Φ_t · y
        have h := Φ_t_meas 0 y
        simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def] at h
        exact ((continuousMultilinearCurryFin0 ℝ H ℝ).symm.isometry.isEmbedding
          |>.aestronglyMeasurable_comp_iff).mp h)
      (Filter.Eventually.of_forall fun t => le_trans (hC' y t)
        (le_of_eq (Real.norm_of_nonneg (mul_nonneg hC_pos (norm_nonneg _))).symm))
  -- Integrability of iteratedFDeriv m (Φ_t ·) y as a function of t (CML-valued)
  have Φ_t_integrable : ∀ (m : ℕ) (y : H),
      Integrable (fun t => iteratedFDeriv ℝ m (Φ_t t) y) volume := by
    intro m y
    obtain ⟨C, hC_pos, hC⟩ := h_bound m
    exact (g_integrable.norm.const_mul C).mono (Φ_t_meas m y)
      (Filter.Eventually.of_forall fun t => le_trans (hC y t)
        (le_of_eq (Real.norm_of_nonneg (mul_nonneg hC_pos (norm_nonneg _))).symm))
  -- Define I n y := ∫ t, iteratedFDeriv n (Φ_t t) y
  set I : (n : ℕ) → H → ContinuousMultilinearMap ℝ (fun _ : Fin n => H) ℝ :=
    fun n y => ∫ t, iteratedFDeriv ℝ n (Φ_t t) y with hI_def
  -- Step 1: HasFDerivAt (I n) at each point
  -- fderiv(iteratedFDeriv n (Φ_t t)) y = (curryLeftLIE n).symm (iteratedFDeriv (n+1) (Φ_t t) y)
  -- so hasFDerivAt_integral gives HasFDerivAt (I n) ((curryLeftLIE n).symm (I (n+1) y)) y
  have I_diff : ∀ (n : ℕ) (y : H),
      HasFDerivAt (I n) ((curryLeftLIE (E := H) (F := ℝ)
        n).symm.toContinuousLinearEquiv.toContinuousLinearMap
        (I (n + 1) y)) y := by
    intro n y₀
    set L := (curryLeftLIE (E := H) (F := ℝ) n).symm.toContinuousLinearEquiv
    -- Each y ↦ iteratedFDeriv n (Φ_t t) y is differentiable (Φ_t t is C^∞)
    have h_cdiff : ∀ t, ContDiff ℝ (↑(n + 1) : ℕ∞) (Φ_t t) :=
      fun t => (Φ_t_smooth t).of_le (by exact_mod_cast le_top)
    have h_differentiable : ∀ t, Differentiable ℝ (fun y => iteratedFDeriv ℝ n (Φ_t t) y) :=
      fun t => (h_cdiff t).differentiable_iteratedFDeriv (by
        apply WithTop.coe_lt_coe.mpr
        apply WithTop.coe_lt_coe.mpr
        omega)
    -- The fderiv of iteratedFDeriv n equals L applied to iteratedFDeriv (n+1)
    -- From iteratedFDeriv_succ_eq_comp_left and curryLeftLIE_coe_eq
    have h_fderiv_eq : ∀ t y, fderiv ℝ (fun y' => iteratedFDeriv ℝ n (Φ_t t) y') y =
        L.toContinuousLinearMap (iteratedFDeriv ℝ (n + 1) (Φ_t t) y) := by
      intro t y
      have h1 := congrFun (iteratedFDeriv_succ_eq_comp_left (𝕜 := ℝ) (f := Φ_t t) (n := n)) y
      -- h1 : iteratedFDeriv (n+1) (Φ_t t) y = curryLeftEquiv.symm (fderiv (iteratedFDeriv n (Φ_t
      -- t)) y)
      rw [Function.comp_def] at h1
      -- curryLeftEquiv.symm = curryLeftLIE n as functions (by curryLeftLIE_coe_eq)
      -- So iteratedFDeriv (n+1) y = curryLeftLIE n (fderiv(iteratedFDeriv n) y)
      -- Apply (curryLeftLIE n).symm = L to both sides
      change fderiv ℝ (fun y' => iteratedFDeriv ℝ n (Φ_t t) y') y =
        (curryLeftLIE (E := H) (F := ℝ) n).symm (iteratedFDeriv ℝ (n + 1) (Φ_t t) y)
      rw [← curryLeftLIE_coe_eq] at h1
      rw [h1, (curryLeftLIE (E := H) (F := ℝ) n).symm_apply_apply]
    -- HasFDerivAt for each integrand
    have h_hasFDerivAt : ∀ t y, HasFDerivAt (fun y' => iteratedFDeriv ℝ n (Φ_t t) y')
        (L.toContinuousLinearMap (iteratedFDeriv ℝ (n + 1) (Φ_t t) y)) y := by
      intro t y
      rw [← h_fderiv_eq]
      exact (h_differentiable t y).hasFDerivAt
    -- Bound on the derivative norm: ‖L (iteratedFDeriv (n+1) ...)‖ = ‖iteratedFDeriv (n+1) ...‖ ≤ C
    -- * ‖g t‖
    obtain ⟨C, hC_pos, hC_bound⟩ := h_bound (n + 1)
    -- Apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    have h_result : HasFDerivAt (fun y => ∫ t, iteratedFDeriv ℝ n (Φ_t t) y)
        (∫ t, L.toContinuousLinearMap (iteratedFDeriv ℝ (n + 1) (Φ_t t) y₀)) y₀ :=
      hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F' := fun y t => L.toContinuousLinearMap (iteratedFDeriv ℝ (n + 1) (Φ_t t) y))
        (s := Set.univ) Filter.univ_mem
        (Filter.Eventually.of_forall fun x => Φ_t_meas n x)
        (Φ_t_integrable n y₀)
        (L.toContinuousLinearMap.continuous.comp_aestronglyMeasurable (Φ_t_meas (n + 1) y₀))
        (Filter.Eventually.of_forall fun t => fun y _ => by
          change ‖(curryLeftLIE (E := H) (F := ℝ) n).symm
            (iteratedFDeriv ℝ (n + 1) (Φ_t t) y)‖ ≤ C * ‖g t‖
          rw [(curryLeftLIE (E := H) (F := ℝ) n).symm.norm_map]
          exact hC_bound y t)
        (g_integrable.norm.const_mul C)
        (Filter.Eventually.of_forall fun t => fun y _ => h_hasFDerivAt t y)
    -- Commute L with the integral to get L (I (n+1) y₀)
    rw [show (∫ t, L.toContinuousLinearMap (iteratedFDeriv ℝ (n + 1) (Φ_t t) y₀)) =
      L.toContinuousLinearMap (I (n + 1) y₀) from
        L.toContinuousLinearMap.integral_comp_comm (Φ_t_integrable (n + 1) y₀)] at h_result
    exact h_result
  -- Step 2: ContDiff m (I n) for all m, n — by induction on m, shifting n
  have I_contDiff : ∀ (m : ℕ) (n : ℕ), ContDiff ℝ (m : ℕ∞) (I n) := by
    intro m
    induction m with
    | zero =>
      intro n
      have h_diff : Differentiable ℝ (I n) := fun y => (I_diff n y).differentiableAt
      exact contDiff_zero.mpr h_diff.continuous
    | succ m ih =>
      intro n
      change ContDiff ℝ ((↑↑m : WithTop ℕ∞) + 1) (I n)
      rw [contDiff_succ_iff_fderiv]
      refine ⟨fun y => (I_diff n y).differentiableAt, ?_, ?_⟩
      · -- Analyticity: vacuous since (m : ℕ∞) ≠ ω
        intro h; exact absurd h WithTop.coe_ne_top
      · -- ContDiff m (fderiv (I n))
        have h_fderiv_eq : fderiv ℝ (I n) =
            fun y => (curryLeftLIE (E := H) (F := ℝ)
              n).symm.toContinuousLinearEquiv.toContinuousLinearMap
              (I (n + 1) y) :=
          funext fun y => (I_diff n y).fderiv
        rw [h_fderiv_eq]
        exact ((curryLeftLIE n).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff).comp
          (ih (n + 1))
  -- Step 3: iteratedFDeriv m Φ = I m — by induction on m
  have h_iter : ∀ (m : ℕ) (y : H), iteratedFDeriv ℝ m Φ y = I m y := by
    intro m
    induction m with
    | zero =>
      intro y
      -- iteratedFDeriv 0 Φ y = (curry0).symm (Φ y)
      -- I 0 y = ∫ t, (curry0).symm (Φ_t t y)
      -- These are equal because (curry0).symm commutes with the integral
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def, hI_def]
      change (continuousMultilinearCurryFin0 ℝ H ℝ).symm (Φ y) =
        ∫ t, (continuousMultilinearCurryFin0 ℝ H ℝ).symm (Φ_t t y)
      set L0 := (continuousMultilinearCurryFin0 ℝ H ℝ).symm.toContinuousLinearEquiv
      exact (L0.toContinuousLinearMap.integral_comp_comm (Φ_t_raw_integrable y)).symm
    | succ m ih =>
      intro y
      -- iteratedFDeriv (m+1) Φ y = (curryLeftLIE m) (fderiv (iteratedFDeriv m Φ) y)
      -- By IH: iteratedFDeriv m Φ = I m, so fderiv (iteratedFDeriv m Φ) = fderiv (I m)
      -- By I_diff: fderiv (I m) y = (curryLeftLIE m).symm (I (m+1) y)
      -- So curryLeftLIE m applied to that gives I (m+1) y
      have h_succ : iteratedFDeriv ℝ (m + 1) Φ y =
          (curryLeftLIE (E := H) (F := ℝ) m) (fderiv ℝ (iteratedFDeriv ℝ m Φ) y) := by
        have := congrFun (iteratedFDeriv_succ_eq_comp_left (𝕜 := ℝ) (f := Φ) (n := m)) y
        rw [Function.comp_def] at this
        rw [this, ← curryLeftLIE_coe_eq]
      rw [h_succ]
      -- Replace iteratedFDeriv m Φ by I m using IH
      have h_eq_fun : iteratedFDeriv ℝ m Φ = I m := funext ih
      rw [h_eq_fun]
      -- Use fderiv from I_diff
      rw [(I_diff m y).fderiv]
      -- curryLeftLIE m applied to (curryLeftLIE m).symm gives identity
      exact (curryLeftLIE m).apply_symm_apply (I (m + 1) y)
  -- Assembly
  refine ⟨?_, fun m y => h_iter m y⟩
  -- ContDiff ∞ Φ: derive from I_contDiff via the I 0 representation
  -- Φ = curry0 ∘ I 0 since I 0 y = curry0.symm (Φ y) by h_iter 0
  have h_Φ_eq : Φ = (continuousMultilinearCurryFin0 ℝ H ℝ) ∘ I 0 := by
    ext y
    simp only [Function.comp_def]
    have h := h_iter 0 y
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def] at h
    -- h : curry0.symm (Φ y) = I 0 y
    -- Goal: Φ y = curry0 (I 0 y)
    rw [← h]
    exact ((continuousMultilinearCurryFin0 ℝ H ℝ).apply_symm_apply (Φ y)).symm
  rw [h_Φ_eq]
  exact contDiff_infty.mpr fun m =>
    ((continuousMultilinearCurryFin0 ℝ H ℝ).contDiff).comp (I_contDiff m 0)
