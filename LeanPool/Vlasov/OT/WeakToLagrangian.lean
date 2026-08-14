/-
Copyright (c) 2026 Joseph K. Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph K. Miller
-/
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Convolution
import LeanPool.Vlasov.OT.CharacteristicFlow

/-!
# Weak ⟹ Lagrangian: every weak Vlasov solution is transported by its characteristic flow

(tex: thm:weak-lagrangian)

The forward direction — a Lagrangian solution is weak — is immediate
(`IsLagrangianVlasovSolution.1`; the substantive pushforward-solves-weak content is
`vlasovSolutionViaPushforward_isVlasovSolutionOn`, `CharacteristicFlow.lean`).  This file builds
the **converse**: under the strengthened assumption `AssW2` (`W ∈ C²`, see `Basic.lean`), every
**weak** Vlasov solution on a window `[0,T]` is **Lagrangian** — i.e. it is the pushforward of its
initial datum under the characteristic flow it generates.  This is the superposition /
probabilistic-representation principle for the phase-space continuity equation
`∂_t f + div_{(x,v)}(b_f · f) = 0` with the Lipschitz field
`b_f(t,x,v) = (v, −(∇W ∗ ρ_t)(x))`, `ρ_t = spatialMarginal (f t)`.

It upgrades the project's uniqueness from "unique *Lagrangian* solution" to "unique *weak* (PDE)
solution".  The marquee `vlasovWellPosedness` / `dobrushin` are untouched and stay at `AssW`.

## Strategy (three ingredients)

Freeze the field at `ρ^f_t := spatialMarginal (f t)` (the field
`vlasovVectorField gradW ρ t z = (z.2, −(∇W ∗ ρ_t)(z.1))` is already parametric in `ρ`).  Let
`g_t := (Φ_t)_# (f 0)` be the pushforward along the flow `Φ` of this *frozen* field.  Then `f`
and `g` solve the **same linear** continuity equation with the same datum, so `f = g`, and `g` is
Lagrangian by construction.

1. **Flow existence for the frozen `ρ^f`** — reuse `exists_vlasov_characteristicFlow_global_smallT`.
2. **Pushforward solves the frozen linear weak eq** — reuse the *generic* helpers SC.1–SC.4
   (`vlasov_traj_chain_rule` etc., stated over an arbitrary `ρ`) at `ρ := ρ^f`, bypassing the
   self-consistent wrapper `vlasovSolutionViaPushforward_isVlasovSolutionOn`.
3. **Linear continuity-equation uniqueness `f = g`** — the crux (absent from Mathlib).  Dual
   transported test function `ψ_s(z) := φ(Φ_{s→T}(z))`: `s ↦ ∫ ψ_s dμ_s` is constant (the
   `∂_sψ + ⟨b,∇ψ⟩ = 0` cancellation), so `∫φ dμ_T = ∫ψ_0 dμ_0`, equal for `f` and `g` (shared
   `μ_0`); ranging over `φ` gives `f T = g T`.

## Decomposition roadmap (sub-lemmas added per build-layer)

Setup layer (C1):
* #1 `vlasov_frozenField_pushforward_isWeakSolOn` — `g` solves the frozen linear weak eq on
  `Ioo 0 T`; recompose SC.1 + SC.2 at `ρ := ρ^f`.
* #2 `exists_frozenField_charFlow_On` — instantiate `exists_vlasov_characteristicFlow_global_smallT`
  at `ρ := ρ^f`, discharging the integrability / continuity / moment hypotheses.

Final-step layer (C2, crux-independent):
* #7 `transportedIntegral_const_On` — zero derivative on `Ioo` + `ContinuousOn` on `Icc` ⟹ const.
* #9 `measure_eq_of_forall_Cc_integral_eq` — `∫φ dμ = ∫φ dν` for all `C_c^∞ φ` ⟹ `μ = ν`, via
  smooth approximation + `ext_of_forall_integral_eq_of_IsFiniteMeasure` (cf. `Wasserstein.lean`).

Crux layer (C3):
* #3 `charFlow_hasFDerivAt_in_initialPoint` — **the variational equation**: `z ↦ Φ_{s→T}(z)` is C¹
  (`HasFDerivAt`), derivative solving `M' = (D_z b)·M`.  Sub-steps: 3.1 variational-ODE existence /
  uniqueness, 3.2 joint `(t,z)` continuity, 3.3 difference-quotient `o(‖h‖)` via Gronwall (the
  heart), 3.4 assemble `HasFDerivAt` → C¹.  Needs `AssW2.gradContDiff`.
* #4 `weakSolOn_test_C1c_of_Cinftyc` — extend `IsVlasovSolutionOn`'s test class from `C_c^∞` to
  `C¹_c` (mollification + DCT), since `ψ_s = φ∘Φ_{s→T}` is only `C¹_c` with a C¹ flow.
* #5 `transportedTestFunction_props` — `ψ_s` is `C¹`, compactly supported, with
  `∂_sψ_s + ⟨b,∇ψ_s⟩ = 0`.
* #6 `transportedIntegral_hasDerivWithinAt_zero` — `s ↦ ∫ ψ_s dμ_s` has zero derivative on
  `Ioo 0 T` for both `μ = f` and `μ = g`.

Assembly (C4):
* #8 `finalTime_integral_eq_of_weak` — combine #7 for `f` and `g` ⟹ `∫φ df_T = ∫φ dg_T` ∀ `C_c^∞ φ`.
* #10 the top theorem below — package `g`'s flow witness + `f = g` into
  `IsLagrangianVlasovSolutionOn`.

Universal (non-`_On`) form via window-gluing is a deferred follow-on (C5).
-/

namespace Vlasov

open MeasureTheory

variable {d : ℕ} [NeZero d]

/-! ## Linear (external-field) weak Vlasov solutions

The self-consistent weak predicate `IsVlasovSolutionOn` drives the convolution field by the
solution's *own* spatial marginal.  For the superposition argument we need the **linear**
version, where the field is driven by an *external* (frozen) measure curve `ρ` — both the given
weak solution `f` (with `ρ := spatialMarginal ∘ f`) and the pushforward `g` along the
frozen-field flow solve the *same* `IsLinearVlasovSolutionOn gradW ρ · T`, and uniqueness for it
(the crux, C3) forces `f = g`. -/

/-- Linear weak Vlasov evolution on `Ioo 0 T` for a test function `φ`, with the convolution field
driven by an **external** measure curve `ρ` (frozen), not the solution's own spatial marginal.
The self-consistent `WeakEvolutionEqOn gradW μ φ … (fun _ => 0) T` is the special case
`ρ = spatialMarginal ∘ μ` (modulo the `+ 0` remainder term). -/
def LinearWeakEvolutionEqOn
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (μ : ℝ → Measure (PhaseSpace d))
    (φ : PhaseSpace d → ℝ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (T : ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) T,
    HasDerivAt (fun s => ∫ z, φ z ∂μ s)
      (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
              @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (ρ t) z.1)
                (gradVφ z))
        ∂μ t) t

/-- A measure curve `μ` solves the **linear** Vlasov equation on `[0,T]` driven by the external
field `ρ`: the distributional identity `LinearWeakEvolutionEqOn` holds for every `C_c^∞` test
function.  Mirror of `IsVlasovSolutionOn` with the field externalized. -/
def IsLinearVlasovSolutionOn
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (μ : ℝ → Measure (PhaseSpace d)) (T : ℝ) : Prop :=
  ∀ (φ : PhaseSpace d → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∀ (gradXφ gradVφ : PhaseSpace d → PhysSpace d),
      (∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1) →
      (∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2) →
      LinearWeakEvolutionEqOn gradW ρ μ φ gradXφ gradVφ T

omit [NeZero d] in
/-- A self-consistent weak solution is a linear solution driven by its **own** spatial marginal.
The two differ only by `WeakEvolutionEqOn`'s `+ (fun _ => 0) t = + 0` remainder. -/
lemma IsVlasovSolutionOn.toLinearSelf
    {gradW : PhysSpace d → PhysSpace d} {f : ℝ → Measure (PhaseSpace d)} {T : ℝ}
    (h : IsVlasovSolutionOn gradW f T) :
    IsLinearVlasovSolutionOn gradW (fun t => spatialMarginal (f t)) f T := by
  intro φ hφ hφc gradXφ gradVφ hgradXφ hgradVφ t ht
  simpa using h φ hφ hφc gradXφ gradVφ hgradXφ hgradVφ t ht

omit [NeZero d] in
/-- **C1 #1 — pushforward solves the frozen linear weak equation.**

For a characteristic flow `(charX, charV)` solving the ODE with an **external** field `ρ` on
`Ioo 0 T`, the pushforward `g := (charX t, charV t)_# f₀` solves the linear Vlasov equation
driven by that same `ρ`.  Proof: the generic SC.1–SC.3 machinery (change of variables +
chain rule + differentiation-under-the-integral, all parametric in `ρ`) recomposed at this `ρ`,
with SC.4's push-back inlined as `integral_map` (SC.4's packaged form hard-codes the
self-consistent marginal).  This is `vlasovSolutionViaPushforward_isVlasovSolutionOn` with `ρ`
left free — the `_hself` self-consistency hypothesis is unused. -/
theorem vlasov_frozenField_pushforward_isLinearVlasovSolutionOn
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_fm : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (hflow_on : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_Ico : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z)) (Set.Ici s) s)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ s ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(ρ s) ≤ M_ρ)
    (h_y_int : ∀ s ∈ Set.Icc (0 : ℝ) T, Integrable (fun y : PhysSpace d => ‖y‖) (ρ s))
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (h_flow_meas : ∀ s, AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀)
    (hgradW_cont : Continuous gradW)
    (hconv_cont : ∀ s, Continuous (fun x => convolveFunctionMeasure gradW (ρ s) x)) :
    IsLinearVlasovSolutionOn gradW ρ (vlasovSolutionViaPushforward charX charV f₀) T := by
  intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ t ht
  have hφ_cont : Continuous φ := hφ_smooth.continuous
  have hφ_aesm_general : ∀ μ : Measure (PhaseSpace d), AEStronglyMeasurable φ μ :=
    fun μ => hφ_cont.aestronglyMeasurable
  -- SC.1: ∫ φ d(pushforward s) = ∫ (φ ∘ flow_s) df₀.
  have h_compose : ∀ s, ∫ z, φ z ∂(vlasovSolutionViaPushforward charX charV f₀ s) =
      ∫ z, φ (charX s z, charV s z) ∂f₀ := fun s =>
    vlasov_pushforward_integral_eq_compose charX charV f₀ s (h_flow_meas s) φ (hφ_aesm_general _)
  -- SC.2 `_at`: pointwise chain rule at every z, at this t.
  have h_pointwise : ∀ z, HasDerivAt (fun s => φ (charX s z, charV s z))
      (@inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
       - @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ t) (charX t z))
          (gradVφ (charX t z, charV t z))) t := by
    intro z
    have hX_at := hflow_on.2.1 t ht z (Set.mem_univ z)
    have hV_at := hflow_on.2.2 t ht z (Set.mem_univ z)
    exact vlasov_traj_chain_rule_at gradW ρ charX charV φ hφ_smooth
      gradXφ gradVφ hgradXφ hgradVφ t z hX_at hV_at
  -- SC.3: differentiation under the integral via the DiffUnderIntegralData bundle.
  have h_diff_data : DiffUnderIntegralData gradW ρ charX charV f₀ φ gradXφ gradVφ t := by
    obtain ⟨nhd, bound, hnhd, h_lipsch, h_bound_int⟩ :=
      vlasov_trajectory_lipschitz_bound_on gradW L hL ρ charX charV f₀
        hf₀_fm φ hφ_smooth hφ_compact hT hflow_on h_init h_cont_Icc h_deriv_Ico
        hgradW_cont hconv_cont t ht M_ρ hM_ρ_nn hM_ρ h_y_int h_int
    refine ⟨nhd, bound, hnhd, ?_, ?_, ?_, h_lipsch, h_bound_int⟩
    · exact vlasov_compose_flow_aestronglymeas charX charV f₀ φ hφ_cont h_flow_meas t
    · exact vlasov_compose_flow_integrable_at charX charV f₀ φ hφ_cont hφ_compact t (h_flow_meas t)
    · exact vlasov_pointwise_deriv_aestronglymeas gradW ρ charX charV f₀
        φ hφ_smooth gradXφ gradVφ hgradXφ hgradVφ hconv_cont t (h_flow_meas t)
  have h_under_integral :=
    vlasov_pushforward_hasDerivAt_under_integral gradW ρ charX charV f₀
      φ gradXφ gradVφ t h_pointwise h_diff_data
  -- SC.4 (inlined; the packaged form hard-codes the self-consistent marginal): AE-strong-meas
  -- of the dot-product integrand, then push back through `integral_map`.
  have h_integrand_aesm : AEStronglyMeasurable
      (fun y : PhaseSpace d =>
        @inner ℝ (PhysSpace d) _ y.2 (gradXφ y)
        - @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (ρ t) y.1) (gradVφ y))
      (vlasovSolutionViaPushforward charX charV f₀ t) := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.sub
    · apply Continuous.inner continuous_snd
      have hfderiv_X : ∀ z : PhaseSpace d,
          fderiv ℝ (fun x => φ (x, z.2)) z.1 =
          (fderiv ℝ φ z).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) :=
        fun z => by
          have h1 : HasFDerivAt φ (fderiv ℝ φ z) z :=
            (hφ_smooth.differentiable (by simp) z).hasFDerivAt
          have h2 : HasFDerivAt (fun x : PhysSpace d => (x, z.2))
              (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) z.1 :=
            hasFDerivAt_prodMk_left z.1 z.2
          exact (h1.comp z.1 h2).fderiv
      have heqX : gradXφ = fun z => gradient (fun x => φ (x, z.2)) z.1 := funext hgradXφ
      simp_rw [heqX, gradient, hfderiv_X]
      exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
        ((ContinuousLinearMap.isBoundedLinearMap_comp_right
          (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d))).continuous.comp
          (hφ_smooth.continuous_fderiv (by simp)))
    · apply Continuous.inner
      · exact (hconv_cont t).comp continuous_fst
      · have hfderiv_V : ∀ z : PhaseSpace d,
            fderiv ℝ (fun v => φ (z.1, v)) z.2 =
            (fderiv ℝ φ z).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) :=
          fun z => by
            have h1 : HasFDerivAt φ (fderiv ℝ φ z) z :=
              (hφ_smooth.differentiable (by simp) z).hasFDerivAt
            have h2 : HasFDerivAt (fun v : PhysSpace d => (z.1, v))
                (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) z.2 :=
              hasFDerivAt_prodMk_right z.1 z.2
            exact (h1.comp z.2 h2).fderiv
        have heqV : gradVφ = fun z => gradient (fun v => φ (z.1, v)) z.2 := funext hgradVφ
        simp_rw [heqV, gradient, hfderiv_V]
        exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
          ((ContinuousLinearMap.isBoundedLinearMap_comp_right
            (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d))).continuous.comp
            (hφ_smooth.continuous_fderiv (by simp)))
  -- Assemble: rewrite LHS via SC.1; push the derivative integral back through `integral_map`.
  have hLHS : (fun s => ∫ z, φ z ∂(vlasovSolutionViaPushforward charX charV f₀ s)) =
              (fun s => ∫ z, φ (charX s z, charV s z) ∂f₀) := funext h_compose
  have h_map_eq :
      ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z)
            - @inner ℝ (PhysSpace d) _ (convolveFunctionMeasure gradW (ρ t) z.1) (gradVφ z))
        ∂(vlasovSolutionViaPushforward charX charV f₀ t)
      = ∫ z, (@inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
            - @inner ℝ (PhysSpace d) _ (convolveFunctionMeasure gradW (ρ t) (charX t z))
                (gradVφ (charX t z, charV t z)))
        ∂f₀ := by
    unfold vlasovSolutionViaPushforward at h_integrand_aesm ⊢
    exact integral_map (h_flow_meas t) h_integrand_aesm
  rw [hLHS, h_map_eq]
  exact h_under_integral

omit [NeZero d] in
/-- **C1 #2 — characteristic flow for a frozen field from window data (L11 clamp).**

Build the characteristic flow for the *given* external curve `ρ` on `Ioo 0 T` (with boundary
regularity), from probability/moment/integrability/continuity data on the window `[0,T]` only.
`exists_vlasov_characteristicFlow_global_smallT` demands *universal*-in-`t` instances; we clamp
`t ↦ ρ (max 0 (min t T))` into the window (L11), apply the universal producer to the clamped
curve, and transfer on `[0,T]` where the clamp is the identity. -/
theorem exists_frozenField_charFlow_On
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d) (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    (T : ℝ) (hT : 0 < T) (hTL_PL : LocalSmallnessPLBuffer L T)
    (hρ_prob : ∀ t ∈ Set.Icc (0 : ℝ) T, IsProbabilityMeasure (ρ t))
    (h_int : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x : PhysSpace d),
      Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      ContinuousOn (fun t => convolveFunctionMeasure gradW (ρ t) x) (Set.Icc (0 : ℝ) T))
    (h_y_int : ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun y : PhysSpace d => ‖y‖) (ρ t))
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(ρ t) ≤ M_ρ) :
    ∃ charX charV : ℝ → PhaseSpace d → PhysSpace d,
      IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ ∧
      (∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z) ∧
      (∀ z : PhaseSpace d,
        ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T)) ∧
      (∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
          (vlasovVectorField gradW ρ s (charX s z, charV s z)) (Set.Ici s) s) := by
  classical
  -- L11 clamp: `clampT t ∈ [0,T]` for every `t`, and `clampT t = t` on `[0,T]`.
  set clampT : ℝ → ℝ := fun t => max 0 (min t T) with hclampT_def
  have hclampT_mem : ∀ t, clampT t ∈ Set.Icc (0 : ℝ) T := by
    intro t
    simp only [hclampT_def, Set.mem_Icc]
    exact ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩
  have hclampT_id : ∀ t ∈ Set.Icc (0 : ℝ) T, clampT t = t := by
    intro t ht
    simp only [hclampT_def, min_eq_left ht.2, max_eq_right ht.1]
  have hclampT_cont : Continuous clampT := by
    simp only [hclampT_def]
    exact continuous_const.max (continuous_id.min continuous_const)
  -- Clamped curve `ρ' := ρ ∘ clampT`, which satisfies the universal hypotheses.
  set ρ' : ℝ → Measure (PhysSpace d) := fun t => ρ (clampT t) with hρ'_def
  have hρ'_prob : ∀ t, IsProbabilityMeasure (ρ' t) :=
    fun t => hρ_prob (clampT t) (hclampT_mem t)
  have h_int' : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ' t) :=
    fun t x => h_int (clampT t) (hclampT_mem t) x
  have h_y_int' : ∀ t, Integrable (fun y : PhysSpace d => ‖y‖) (ρ' t) :=
    fun t => h_y_int (clampT t) (hclampT_mem t)
  have hM_ρ' : ∀ t, ∫ y, ‖y‖ ∂(ρ' t) ≤ M_ρ := fun t => hM_ρ (clampT t) (hclampT_mem t)
  have hρ'_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ' t) x) :=
    fun x => (hρ_cont x).comp_continuous hclampT_cont (fun t => hclampT_mem t)
  -- Apply the universal producer to `ρ'`.
  obtain ⟨charX, charV, hflow', h_bdry'⟩ :=
    exists_vlasov_characteristicFlow_global_smallT W gradW hgradW L hL ρ'
      h_int' hρ'_cont h_y_int' M_ρ hM_ρ_nn hM_ρ' T hT.le hTL_PL
  -- On `Ioo`/`Icc 0 T`, `clampT = id` so `ρ' = ρ`: transfer the flow back to `ρ`.
  refine ⟨charX, charV, ⟨hflow'.1, hflow'.2.1, ?_⟩, ?_, ?_, ?_⟩
  · -- velocity ODE for `ρ` on `Ioo 0 T`
    intro t ht z hz
    have h := hflow'.2.2 t ht z hz
    have hρeq : ρ' t = ρ t := by
      simp only [hρ'_def, hclampT_id t (Set.Ioo_subset_Icc_self ht)]
    rwa [hρeq] at h
  · -- initial condition
    intro z
    have h := hflow'.1 z (Set.mem_univ z)
    exact Prod.ext h.1 h.2
  · -- `ContinuousOn` on `Icc 0 T` from the producer's boundary derivatives
    intro z t ht
    obtain ⟨hX, hV⟩ := h_bdry' z t ht
    exact (hX.prodMk hV).continuousWithinAt
  · -- `h_deriv_Ico` (Ici-joint) from the producer's `Icc`-component derivatives
    intro z s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) T := Set.Ico_subset_Icc_self hs
    obtain ⟨hX, hV⟩ := h_bdry' z s hsIcc
    have hρeq : ρ' s = ρ s := by simp only [hρ'_def, hclampT_id s hsIcc]
    have hpair : HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (charV s z, -(convolveFunctionMeasure gradW (ρ' s) (charX s z)))
        (Set.Icc 0 T) s := hX.prodMk hV
    rw [hρeq] at hpair
    -- convert the set `Icc 0 T` to `Ici s` (local subset near `s`, since `s < T`)
    have hmem : Set.Iic ((s + T) / 2) ∈ nhds s := Iic_mem_nhds (by linarith [hs.2])
    have hsub : Set.Ici s ∩ Set.Iic ((s + T) / 2) ⊆ Set.Icc 0 T := by
      rintro u ⟨hu1, hu2⟩
      exact ⟨le_trans hs.1 hu1, le_trans hu2 (by linarith [hs.2])⟩
    exact (hasDerivWithinAt_inter hmem).mp (hpair.mono hsub)

/-! ## Final-step layer (crux-independent): constancy + measure extensionality -/

/-- **C2 #7 — constancy from a vanishing derivative.**

If a real function is continuous on `[0,T]` and has zero derivative throughout the open
interval, its endpoint values agree.  This is the dual argument's payoff step: `s ↦ ∫ ψ_s dμ_s`
is constant, so its value at `T` (= `∫ φ dμ_T`) equals its value at `0` (= `∫ ψ_0 dμ_0`). Mean
value theorem (`exists_hasDerivAt_eq_slope`). -/
lemma transportedIntegral_const_On {h : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hcont : ContinuousOn h (Set.Icc 0 T))
    (hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) T, HasDerivAt h 0 s) :
    h 0 = h T := by
  obtain ⟨c, _hc, hc'⟩ :=
    exists_hasDerivAt_eq_slope h (fun _ => 0) hT hcont (fun s hs => hderiv s hs)
  have hc0 : (0 : ℝ) = (h T - h 0) / (T - 0) := hc'
  rcases div_eq_zero_iff.mp hc0.symm with h1 | h2
  · exact (sub_eq_zero.mp h1).symm
  · exact absurd h2 (ne_of_gt (by linarith : (0 : ℝ) < T - 0))

omit [NeZero d] in
/-- **C2 #9 — `C_c^∞` test functions determine a finite measure.**

If `∫ φ dμ = ∫ φ dν` for every smooth compactly-supported `φ`, then `μ = ν` (finite measures on
phase space).  The dual argument yields equality of integrals against the `IsVlasovSolution` test
class `C_c^∞`; this closes the bridge's final step `f T = g T`.  Route: extend `C_c^∞ →`
bounded-continuous (smooth approximation), then the in-house bounded-continuous extensionality
`ext_of_forall_integral_eq_of_IsFiniteMeasure` (cf. `Wasserstein.lean`). -/
lemma measure_eq_of_forall_Cc_integral_eq {μ ν : Measure (PhaseSpace d)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ φ : PhaseSpace d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ z, φ z ∂μ = ∫ z, φ z ∂ν) :
    μ = ν := by
  -- Haar instance on the ambient volume via the product reduction.
  have hHaar : (volume : Measure (PhaseSpace d)).IsAddHaarMeasure := by
    rw [show (volume : Measure (PhaseSpace d)) = (volume : Measure (PhysSpace d)).prod volume from
      Measure.volume_eq_prod _ _]
    infer_instance
  have hvolReg : (volume : Measure (PhaseSpace d)).Regular := inferInstance
  have hμreg : μ.Regular := inferInstance
  have hνreg : ν.Regular := inferInstance
  -- Reduce `μ = ν` to equality of integrals against continuous compactly-supported `g`.
  refine MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported (fun g => ?_)
  set gf : PhaseSpace d → ℝ := ⇑g with hgf
  have hg_cont : Continuous gf := map_continuous g
  have hg_cs : HasCompactSupport gf := CompactlySupportedContinuousMap.hasCompactSupport g
  -- Uniform sup bound on `g`.
  obtain ⟨C, hC⟩ := hg_cont.bounded_above_of_compact_support hg_cs
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  -- A mollifier family `φ n` with outer radius `2/(n+2) → 0`.
  set φ : ℕ → ContDiffBump (0 : PhaseSpace d) :=
    fun n => ⟨1 / (n + 2), 2 / (n + 2), by positivity, by
      rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num⟩ with hφ
  have hrout : ∀ n, (φ n).rOut = 2 / (n + 2) := fun n => rfl
  have hrout_tendsto : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0) := by
    simp only [hrout]
    apply Filter.Tendsto.div_atTop (tendsto_const_nhds)
    exact Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  -- The mollified functions.
  set gn : ℕ → PhaseSpace d → ℝ :=
    fun n => convolution ((φ n).normed volume) gf (ContinuousLinearMap.lsmul ℝ ℝ) volume with hgn
  -- Each `gn n` is `C^∞` with compact support, hence covered by the hypothesis `h`.
  have hgn_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (gn n) := fun n =>
    ((φ n).hasCompactSupport_normed).contDiff_convolution_left _
      (φ n).contDiff_normed (hg_cont.locallyIntegrable)
  have hgn_cs : ∀ n, HasCompactSupport (gn n) := fun n =>
    HasCompactSupport.convolution _ (φ n).hasCompactSupport_normed hg_cs
  have hgn_eq : ∀ n, ∫ z, gn n z ∂μ = ∫ z, gn n z ∂ν := fun n =>
    h (gn n) (hgn_smooth n) (hgn_cs n)
  -- Pointwise convergence `gn n → gf` (continuous `g`, shrinking bumps).
  have hgn_lim : ∀ x, Filter.Tendsto (fun n => gn n x) Filter.atTop (nhds (gf x)) := fun x =>
    ContDiffBump.convolution_tendsto_right_of_continuous hrout_tendsto hg_cont x
  -- Uniform bound `‖gn n x‖ ≤ C` (averaging keeps the sup bound).
  have hgn_bound : ∀ n, ∀ x, ‖gn n x‖ ≤ C := by
    intro n x
    rw [hgn]
    simp only
    rw [convolution_lsmul]
    calc ‖∫ t, (φ n).normed volume t • gf (x - t) ∂volume‖
        ≤ ∫ t, ‖(φ n).normed volume t • gf (x - t)‖ ∂volume := norm_integral_le_integral_norm _
      _ ≤ ∫ t, (φ n).normed volume t * C ∂volume := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun t => norm_nonneg _)
          · exact ((φ n).integrable_normed).mul_const C
          · refine Filter.Eventually.of_forall (fun t => ?_)
            simp only
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ((φ n).nonneg_normed t)]
            exact mul_le_mul_of_nonneg_left (hC _) ((φ n).nonneg_normed t)
      _ = C := by rw [integral_mul_const, (φ n).integral_normed, one_mul]
  -- DCT: `∫ gn n dμ → ∫ gf dμ` and likewise for `ν`.
  have hconv_μ : Filter.Tendsto (fun n => ∫ z, gn n z ∂μ) Filter.atTop (nhds (∫ z, gf z ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => C)
    · exact fun n => (hgn_smooth n).continuous.aestronglyMeasurable
    · exact integrable_const C
    · exact fun n => Filter.Eventually.of_forall (fun x => hgn_bound n x)
    · exact Filter.Eventually.of_forall hgn_lim
  have hconv_ν : Filter.Tendsto (fun n => ∫ z, gn n z ∂ν) Filter.atTop (nhds (∫ z, gf z ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => C)
    · exact fun n => (hgn_smooth n).continuous.aestronglyMeasurable
    · exact integrable_const C
    · exact fun n => Filter.Eventually.of_forall (fun x => hgn_bound n x)
    · exact Filter.Eventually.of_forall hgn_lim
  -- The two limits coincide because the prelimit sequences are equal.
  have hμν : Filter.Tendsto (fun n => ∫ z, gn n z ∂μ) Filter.atTop (nhds (∫ z, gf z ∂ν)) := by
    simpa only [hgn_eq] using hconv_ν
  exact tendsto_nhds_unique hconv_μ hμν

omit [NeZero d] in
/-- Convenience extractor: under `[AssW2 W]`, a gradient field `gradW= ∇W` is `C¹`.

`AssW2.gradContDiff` gives `ContDiff ℝ 1 (fun x => fderiv ℝ W x)`; composing with the (smooth,
linear) Riesz isometry `gradient W x = (toDual ℝ _).symm (fderiv ℝ W x)` and rewriting by `hgradW`
yields `ContDiff ℝ 1 gradW`. -/
lemma assW2_contDiff_gradW (W : PhysSpace d → ℝ) [AssW2 W]
    (gradW : PhysSpace d → PhysSpace d) (hgradW : ∀ x, gradW x = gradient W x) :
    ContDiff ℝ 1 gradW := by
  have heq : gradW =
      fun x => (InnerProductSpace.toDual ℝ (PhysSpace d)).symm (fderiv ℝ W x) := by
    funext x; rw [hgradW]; rfl
  rw [heq]
  have hriesz : ContDiff ℝ 1 fun u => (InnerProductSpace.toDual ℝ (PhysSpace d)).symm u :=
    (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.toContinuousLinearEquiv.contDiff
  exact hriesz.comp ‹AssW2 W›.gradContDiff

/-! ## Crux layer (C3): the variational equation and the dual-transport assembly

The two interfaces below were the load-bearing pieces of the bridge — both now proven and
axiom-clean.  `#3` was the genuine research gap (C¹ dependence of an ODE flow on its initial point
— absent from Mathlib), closed via route (b) (difference-quotient + Gronwall); `#8` is the
bridge-specific dual-transported-test-function assembly that consumes it.  `#10` (the public
theorem) composes the reuse layer (`exists_frozenField_charFlow_On`, #2) with `#8`.

The dual-argument *internals* `#4`/`#5`/`#6` (test-class enlargement `C_c^∞ → C¹_c`, the
transported test function `ψ_s = φ ∘ Φ_{s→t}` and its transport identity, and the zero-derivative
of `s ↦ ∫ ψ_s dμ_s`) are realized against the two-time-flow representation `Φ_{s→t} = Φ_t ∘ Φ_s⁻¹`
and proven below (`weakEvolution_test_C1c_On`, `transportedTest_transport_identity`,
`transportedIntegral_hasDerivAt_zero`). -/

omit [NeZero d] in
/-- **C3 F1 — the convolution force field is `C¹` in space (Fréchet derivative under the
integral).**  For `gradW ∈ C¹` (and `L`-Lipschitz, a probability measure `ρ` with the kernel
integrable), `x ↦ ∫ y, gradW (x − y) ∂ρ` is Fréchet-differentiable with derivative
`∫ y, fderiv ℝ gradW (x₀ − y) ∂ρ`.  This is the field-regularity foundation of the variational
equation (#3): it makes `D_z (vlasovVectorField …)` exist and continuous, so the variational ODE
`M' = (D_z b)·M` has continuous coefficients.

Differentiation under the integral sign (`hasFDerivAt_integral_of_dominated_loc_of_lip`): the
per-fibre map `x ↦ gradW (x − y)` is `L`-Lipschitz (a uniform, integrable bound against a
probability measure) and differentiable, so the parametric integral differentiates with derivative
the integral of the fibrewise derivatives. -/
theorem convolveFunctionMeasure_hasFDerivAt
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : Measure (PhysSpace d)) [IsProbabilityMeasure ρ]
    (h_int : ∀ x : PhysSpace d, Integrable (fun y => gradW (x - y)) ρ)
    (x₀ : PhysSpace d) :
    HasFDerivAt (fun x => convolveFunctionMeasure gradW ρ x)
      (∫ y, fderiv ℝ gradW (x₀ - y) ∂ρ) x₀ := by
  have hdiff : Differentiable ℝ gradW := hgradW_C1.differentiable one_ne_zero
  have hfderiv_cont : Continuous (fun z => fderiv ℝ gradW z) :=
    hgradW_C1.continuous_fderiv one_ne_zero
  have key := hasFDerivAt_integral_of_dominated_loc_of_lip
    (μ := ρ) (s := (Set.univ : Set (PhysSpace d))) (x₀ := x₀)
    (F := fun x y => gradW (x - y))
    (F' := fun y => fderiv ℝ gradW (x₀ - y))
    (bound := fun _ => (L : ℝ))
    (Filter.univ_mem)
    (Filter.Eventually.of_forall fun x =>
      (hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (h_int x₀)
    ((hfderiv_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun a => ?_)
    (integrable_const _)
    (Filter.Eventually.of_forall fun a => ?_)
  · have h2 := key.2
    simpa only [convolveFunctionMeasure] using h2
  · -- h_lip: `fun x => gradW (x - a)` is `L`-Lipschitz, hence `LipschitzOnWith (nnabs L)` on univ
    have hLip : LipschitzWith L (fun x : PhysSpace d => gradW (x - a)) := by
      refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
      have hd : dist (x - a) (y - a) = dist x y := by
        rw [dist_eq_norm, dist_eq_norm]; congr 1; abel
      calc dist (gradW (x - a)) (gradW (y - a))
          ≤ (L : ℝ) * dist (x - a) (y - a) := hL.dist_le_mul _ _
        _ = (L : ℝ) * dist x y := by rw [hd]
    rw [Real.nnabs_coe L]
    exact hLip.lipschitzOnWith
  · -- h_diff: `HasFDerivAt (fun x => gradW (x - a)) (fderiv ℝ gradW (x₀ - a)) x₀`
    have h1 : HasFDerivAt gradW (fderiv ℝ gradW (x₀ - a)) (x₀ - a) :=
      (hdiff (x₀ - a)).hasFDerivAt
    have h2 : HasFDerivAt (fun x : PhysSpace d => x - a)
        (ContinuousLinearMap.id ℝ (PhysSpace d)) x₀ :=
      (hasFDerivAt_id x₀).sub_const a
    have hc := h1.comp x₀ h2
    simpa [Function.comp_def] using hc

omit [NeZero d] in
/-- **C3 F2 — the Vlasov field is `C¹` in the phase-space variable, with the block Jacobian.**
At fixed time `t`, `vlasovVectorField gradW ρ t = fun (x,v) ↦ (v, −conv(x))` is
Fréchet-differentiable in `z = (x,v)` with derivative the block continuous-linear map
`δ ↦ (δ.2, −(D_x conv)(δ.1))`, where `D_x conv = ∫ y, fderiv ℝ gradW (z.1 − y) ∂(ρ t)` (F1).
This is the coefficient `A(t) := D_z b(t, Φ_t z)` of the variational ODE `M' = A(t)·M`. -/
theorem vlasovVectorField_hasFDerivAt_in_z
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (t : ℝ) (z : PhaseSpace d) :
    HasFDerivAt (vlasovVectorField gradW ρ t)
      ((ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d)).prod
        (-((∫ y, fderiv ℝ gradW (z.1 - y) ∂(ρ t)).comp
            (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d))))) z := by
  have hconv : HasFDerivAt (fun x => convolveFunctionMeasure gradW (ρ t) x)
      (∫ y, fderiv ℝ gradW (z.1 - y) ∂(ρ t)) z.1 :=
    convolveFunctionMeasure_hasFDerivAt gradW hgradW_C1 L hL (ρ t) (h_int t) z.1
  have hfst : HasFDerivAt (fun w : PhaseSpace d => w.1)
      (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d)) z :=
    (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d)).hasFDerivAt
  have h1 : HasFDerivAt (fun w : PhaseSpace d => w.2)
      (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d)) z :=
    (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d)).hasFDerivAt
  have h2 : HasFDerivAt (fun w : PhaseSpace d => convolveFunctionMeasure gradW (ρ t) w.1)
      ((∫ y, fderiv ℝ gradW (z.1 - y) ∂(ρ t)).comp
        (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d))) z :=
    hconv.comp z hfst
  have hprod := h1.prodMk h2.neg
  exact hprod

omit [NeZero d] in
/-- **C3 F1c — the convolution derivative is continuous in space.**  `x ↦ ∫ y, fderiv ℝ gradW
(x − y) ∂ρ` (the Fréchet derivative of the convolution field, F1) is continuous, by dominated
convergence: the integrand is continuous in `x` and bounded by `‖fderiv gradW‖ ≤ L` (a constant,
integrable against the probability measure `ρ`).  Continuity of the variational coefficient
`A(t)` in its spatial argument — half of the `t`-continuity of `A` (the other half is the
measure-curve regularity `t ↦ ρ t`, supplied at the V1c ODE-existence step). -/
theorem convolveFunctionMeasure_fderiv_continuous
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : Measure (PhysSpace d)) [IsProbabilityMeasure ρ] :
    Continuous (fun x => ∫ y, fderiv ℝ gradW (x - y) ∂ρ) := by
  have hfderiv_cont : Continuous (fun z => fderiv ℝ gradW z) :=
    hgradW_C1.continuous_fderiv one_ne_zero
  refine continuous_of_dominated
    (F := fun x y => fderiv ℝ gradW (x - y)) (bound := fun _ => (L : ℝ)) ?_ ?_ ?_ ?_
  · intro x
    exact (hfderiv_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall (fun y => norm_fderiv_le_of_lipschitz (𝕜 := ℝ) hL)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun y =>
      hfderiv_cont.comp (continuous_id.sub continuous_const))

/-- Picard iterates for the linear IVP `x' = 𝒜(t)x`, `x(0)=x₀` (the V1c engine):
`I₀ ≡ x₀`, `I_{n+1}(t) = ∫₀ᵗ 𝒜(s)(Iₙ(s)) ds`. -/
noncomputable def picardIter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (x₀ : E) : ℕ → ℝ → E
  | 0, _ => x₀
  | (n + 1), t => ∫ s in (0 : ℝ)..t, 𝒜 s (picardIter 𝒜 x₀ n s)

@[simp] lemma picardIter_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (x₀ : E) (t : ℝ) : picardIter 𝒜 x₀ 0 t = x₀ := rfl

lemma picardIter_succ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (x₀ : E) (n : ℕ) (t : ℝ) :
    picardIter 𝒜 x₀ (n + 1) t = ∫ s in (0 : ℝ)..t, 𝒜 s (picardIter 𝒜 x₀ n s) := rfl

/-- **C3 V1c-engine — the Picard iterates are continuous and satisfy the geometric
`(Kt)ⁿ/n!`-bound on `[0,T]`.**  Proved by simultaneous induction (continuity feeds
integrability, which feeds the next bound).  This `Σ (KT)ⁿ/n! = e^{KT}`-summable bound is the
convergence driver for the V1c fixed point. -/
lemma picardIter_continuousOn_and_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (x₀ : E)
    (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (hcont𝒜 : ContinuousOn 𝒜 (Set.Icc 0 T))
    (hbound𝒜 : ∀ t ∈ Set.Icc 0 T, ‖𝒜 t‖ ≤ K) :
    ∀ n, ContinuousOn (picardIter 𝒜 x₀ n) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, ‖picardIter 𝒜 x₀ n t‖ ≤ (K * t) ^ n / n.factorial * ‖x₀‖ := by
  intro n
  induction n with
  | zero =>
    refine ⟨continuousOn_const, fun t ht => ?_⟩
    simp
  | succ n ih =>
    obtain ⟨ih_cont, ih_bd⟩ := ih
    have hg_cont : ContinuousOn (fun s => 𝒜 s (picardIter 𝒜 x₀ n s)) (Set.Icc 0 T) :=
      hcont𝒜.clm_apply ih_cont
    have hg_int : IntegrableOn (fun s => 𝒜 s (picardIter 𝒜 x₀ n s)) (Set.Icc 0 T) :=
      hg_cont.integrableOn_Icc
    refine ⟨?_, ?_⟩
    · have hcp := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := T) (μ := volume)
        (f := fun s => 𝒜 s (picardIter 𝒜 x₀ n s)) (by rw [Set.uIcc_of_le hT]; exact hg_int)
      rw [Set.uIcc_of_le hT] at hcp
      exact hcp
    · intro t ht
      have ht0 : (0 : ℝ) ≤ t := ht.1
      have htT : t ≤ T := ht.2
      have h_ptwise : ∀ s ∈ Set.Icc (0 : ℝ) t,
          ‖𝒜 s (picardIter 𝒜 x₀ n s)‖ ≤ K * (K * s) ^ n / n.factorial * ‖x₀‖ := by
        intro s hs
        have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, le_trans hs.2 htT⟩
        calc ‖𝒜 s (picardIter 𝒜 x₀ n s)‖
            ≤ ‖𝒜 s‖ * ‖picardIter 𝒜 x₀ n s‖ := (𝒜 s).le_opNorm _
          _ ≤ K * ((K * s) ^ n / n.factorial * ‖x₀‖) :=
              mul_le_mul (hbound𝒜 s hsT) (ih_bd s hsT) (norm_nonneg _) hK
          _ = K * (K * s) ^ n / n.factorial * ‖x₀‖ := by ring
      have hRHS_int : IntervalIntegrable
          (fun s => K * (K * s) ^ n / n.factorial * ‖x₀‖) volume 0 t :=
        (Continuous.intervalIntegrable (by fun_prop) 0 t)
      have hLHS_int : IntervalIntegrable
          (fun s => ‖𝒜 s (picardIter 𝒜 x₀ n s)‖) volume 0 t := by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le ht0]
        exact (hg_cont.mono (Set.Icc_subset_Icc_right htT)).norm
      calc ‖picardIter 𝒜 x₀ (n + 1) t‖
          = ‖∫ s in (0 : ℝ)..t, 𝒜 s (picardIter 𝒜 x₀ n s)‖ := by rw [picardIter_succ]
        _ ≤ ∫ s in (0 : ℝ)..t, ‖𝒜 s (picardIter 𝒜 x₀ n s)‖ :=
            intervalIntegral.norm_integral_le_integral_norm ht0
        _ ≤ ∫ s in (0 : ℝ)..t, K * (K * s) ^ n / n.factorial * ‖x₀‖ :=
            intervalIntegral.integral_mono_on ht0 hLHS_int hRHS_int h_ptwise
        _ = (K * t) ^ (n + 1) / (n + 1).factorial * ‖x₀‖ := by
            have hpow : ∀ s : ℝ, K * (K * s) ^ n / n.factorial * ‖x₀‖
                = (K ^ (n + 1) * ‖x₀‖ / n.factorial) * s ^ n := by
              intro s; rw [mul_pow]; ring
            simp_rw [hpow]
            rw [intervalIntegral.integral_const_mul, integral_pow]
            rw [Nat.factorial_succ]
            push_cast
            rw [mul_pow]
            field_simp
            ring

/-- **C3 V1c-conv — the Dyson sum `M := ∑ₙ Iₙ` is continuous on `[0,T]`.**  Weierstrass M-test:
the terms are dominated by the summable majorant `(KT)ⁿ/n!·‖x₀‖`, so the series converges
uniformly; the uniform limit of the continuous partial sums is continuous.  (`M` is the candidate
solution: `M = x₀ + ∫₀ᵗ 𝒜(s)(M s) ds`, proved next.) -/
lemma picardSum_continuousOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (x₀ : E) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (hcont𝒜 : ContinuousOn 𝒜 (Set.Icc 0 T)) (hbound𝒜 : ∀ t ∈ Set.Icc 0 T, ‖𝒜 t‖ ≤ K) :
    ContinuousOn (fun t => ∑' n, picardIter 𝒜 x₀ n t) (Set.Icc 0 T) := by
  have hcb := picardIter_continuousOn_and_bound 𝒜 x₀ T hT K hK hcont𝒜 hbound𝒜
  have hbd : ∀ (n : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
      ‖picardIter 𝒜 x₀ n t‖ ≤ (K * T) ^ n / n.factorial * ‖x₀‖ := by
    intro n t ht
    refine le_trans ((hcb n).2 t ht) ?_
    have hKt : 0 ≤ K * t := mul_nonneg hK ht.1
    have hle : K * t ≤ K * T := mul_le_mul_of_nonneg_left ht.2 hK
    gcongr
  have hsum : Summable (fun n => (K * T) ^ n / n.factorial * ‖x₀‖) :=
    (Real.summable_pow_div_factorial (K * T)).mul_right ‖x₀‖
  have hunif : TendstoUniformlyOn
      (fun (u : Finset ℕ) (t : ℝ) => ∑ n ∈ u, picardIter 𝒜 x₀ n t)
      (fun t => ∑' n, picardIter 𝒜 x₀ n t) Filter.atTop (Set.Icc 0 T) :=
    tendstoUniformlyOn_tsum hsum hbd
  refine hunif.continuousOn ?_
  exact (Filter.Eventually.of_forall
    (fun u => continuousOn_finsetSum u (fun n _ => (hcb n).1))).frequently

/-- **C3 V2-core — the Dyson sum is continuous in a PARAMETER (the V2 ingredient).**  If the
coefficient family `𝒜 : Z → ℝ → (E →L E)` is jointly continuous in `(z, s)` (globally) and
uniformly `K`-bounded on `[0,T]` (with `x₀` constant in `z`), then `z ↦ ∑ₙ Iₙ(z)(t)` is continuous
for each fixed `t ∈ [0,T]`.  This is the parameter analogue of `picardSum_continuousOn`: each
iterate `z ↦ Iₙ(z)(t)` is continuous (joint `(z,s)`-continuity, by induction through the parametric
primitive `continuous_parametric_primitive_of_continuous`), and the M-test majorant `(KT)ⁿ/n!·‖x₀‖`
is **`z`-independent**, so the uniform-in-`z` limit of continuous maps is continuous.  This is what
makes the variational fundamental matrix `z ↦ M z t` continuous (V2) — the property the abstract
`exists_fundamentalMatrix` + `choose` cannot supply (the `choose`'d witness is an arbitrary
fiberwise section; see lesson L14). -/
lemma picardSum_continuous_param
    {Z E : Type*} [TopologicalSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (𝒜 : Z → ℝ → (E →L[ℝ] E)) (x₀ : E) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (h𝒜_cont : Continuous (fun p : Z × ℝ => 𝒜 p.1 p.2))
    (h𝒜_bound : ∀ z, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖𝒜 z s‖ ≤ K)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Continuous (fun z => ∑' n, picardIter (𝒜 z) x₀ n t) := by
  -- (1) joint continuity of each Picard iterate on `Z × ℝ`.
  have hiter_cont : ∀ n, Continuous (fun p : Z × ℝ => picardIter (𝒜 p.1) x₀ n p.2) := by
    intro n
    induction n with
    | zero =>
      simp only [picardIter_zero]
      exact continuous_const
    | succ n ih =>
      have hg : Continuous (Function.uncurry fun z v => 𝒜 z v (picardIter (𝒜 z) x₀ n v)) :=
        h𝒜_cont.clm_apply ih
      have hpp := intervalIntegral.continuous_parametric_primitive_of_continuous
        (μ := volume) (a₀ := (0 : ℝ)) hg
      simp only [picardIter_succ]
      exact hpp
  -- (2) per-`z` slice continuity + the `z`-independent M-test bound.
  have h𝒜cont_z : ∀ z, ContinuousOn (𝒜 z) (Set.Icc (0 : ℝ) T) := fun z =>
    (h𝒜_cont.comp (continuous_const.prodMk continuous_id)).continuousOn
  have hbd : ∀ (n : ℕ) (z : Z), z ∈ (Set.univ : Set Z) →
      ‖picardIter (𝒜 z) x₀ n t‖ ≤ (K * T) ^ n / n.factorial * ‖x₀‖ := by
    intro n z _
    have hb := (picardIter_continuousOn_and_bound (𝒜 z) x₀ T hT K hK (h𝒜cont_z z)
      (h𝒜_bound z) n).2 t ht
    refine le_trans hb ?_
    have hKt : (0 : ℝ) ≤ K * t := mul_nonneg hK ht.1
    have hle : K * t ≤ K * T := mul_le_mul_of_nonneg_left ht.2 hK
    gcongr
  have hsum : Summable (fun n => (K * T) ^ n / n.factorial * ‖x₀‖) :=
    (Real.summable_pow_div_factorial (K * T)).mul_right ‖x₀‖
  have hsummands_cont : ∀ n, Continuous (fun z => picardIter (𝒜 z) x₀ n t) := fun n =>
    (hiter_cont n).comp (continuous_id.prodMk continuous_const)
  have hunif : TendstoUniformlyOn
      (fun (u : Finset ℕ) (z : Z) => ∑ n ∈ u, picardIter (𝒜 z) x₀ n t)
      (fun z => ∑' n, picardIter (𝒜 z) x₀ n t) Filter.atTop (Set.univ : Set Z) :=
    tendstoUniformlyOn_tsum hsum hbd
  rw [← continuousOn_univ]
  refine hunif.continuousOn ?_
  exact (Filter.Eventually.of_forall
    (fun u => continuousOn_finsetSum u (fun n _ => (hsummands_cont n).continuousOn))).frequently

/-- Window version of `picardSum_continuous_param`: only joint continuity ON `[0,T]` is needed.
The coefficient is clamped into `[0,T]` (`projIcc`, L11) so the global parametric-primitive lemma
applies, then transferred back by agreement of the iterates on `[0,T]` (they only integrate over
`[0,t] ⊆ [0,T]`).  This is the form the variational coefficient `A(s,z) = D_z b(s, Φ_s z)` needs —
it is jointly continuous only on the window `[0,T]` (the flow `Φ_s z` is). -/
lemma picardSum_continuous_param_Icc
    {Z E : Type*} [TopologicalSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (𝒜 : Z → ℝ → (E →L[ℝ] E)) (x₀ : E) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (h𝒜_contOn : ContinuousOn (fun p : Z × ℝ => 𝒜 p.1 p.2) (Set.univ ×ˢ Set.Icc (0 : ℝ) T))
    (h𝒜_bound : ∀ z, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖𝒜 z s‖ ≤ K)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Continuous (fun z => ∑' n, picardIter (𝒜 z) x₀ n t) := by
  set cl : ℝ → ℝ := fun s => ↑(Set.projIcc 0 T hT s) with hcl
  have hcl_cont : Continuous cl := continuous_subtype_val.comp continuous_projIcc
  have hcl_mem : ∀ s, cl s ∈ Set.Icc (0 : ℝ) T := fun s => (Set.projIcc 0 T hT s).2
  have hcl_eq : ∀ s ∈ Set.Icc (0 : ℝ) T, cl s = s := by
    intro s hs; change (↑(Set.projIcc 0 T hT s) : ℝ) = s; rw [Set.projIcc_of_mem hT hs]
  set 𝒜c : Z → ℝ → (E →L[ℝ] E) := fun z s => 𝒜 z (cl s) with h𝒜c
  have h𝒜c_cont : Continuous (fun p : Z × ℝ => 𝒜c p.1 p.2) := by
    have hmap : Continuous (fun p : Z × ℝ => ((p.1, cl p.2) : Z × ℝ)) :=
      continuous_fst.prodMk (hcl_cont.comp continuous_snd)
    have hmem : ∀ p : Z × ℝ, ((p.1, cl p.2) : Z × ℝ) ∈ Set.univ ×ˢ Set.Icc (0 : ℝ) T :=
      fun p => ⟨Set.mem_univ _, hcl_mem p.2⟩
    exact h𝒜_contOn.comp_continuous hmap hmem
  have h𝒜c_bound : ∀ z, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖𝒜c z s‖ ≤ K :=
    fun z s _ => h𝒜_bound z (cl s) (hcl_mem s)
  have hagree : ∀ (n : ℕ) (z : Z), ∀ s ∈ Set.Icc (0 : ℝ) T,
      picardIter (𝒜c z) x₀ n s = picardIter (𝒜 z) x₀ n s := by
    intro n
    induction n with
    | zero => intro z s _; simp
    | succ n ih =>
      intro z s hs
      simp only [picardIter_succ]
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      have huIcc : u ∈ Set.Icc (0 : ℝ) T := by
        rw [Set.uIcc_of_le hs.1] at hu; exact ⟨hu.1, le_trans hu.2 hs.2⟩
      have e1 : 𝒜c z u = 𝒜 z u := by simp only [h𝒜c, hcl_eq u huIcc]
      rw [e1, ih z u huIcc]
  have key := picardSum_continuous_param 𝒜c x₀ T hT K hK h𝒜c_cont h𝒜c_bound t ht
  have heq : (fun z => ∑' n, picardIter (𝒜c z) x₀ n t)
      = (fun z => ∑' n, picardIter (𝒜 z) x₀ n t) := by
    funext z; congr 1; funext n; exact hagree n z t ht
  rwa [heq] at key

/-- **C3 V1c-rec — finite Picard recurrence.**  The `(N+1)`-th partial Dyson sum equals
`x₀ + ∫₀ᵗ 𝒜(s)(Sₙ(s)) ds`, where `Sₙ = ∑_{n<N} Iₙ`.  Only finite-sum swaps
(`integral_finsetSum`, `map_sum`); no infinite interchange.  Passing `N → ∞` against the
uniform convergence (`picardSum_continuousOn`'s M-test) yields the integral equation for `M`. -/
lemma picardSum_finset_recurrence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (x₀ : E) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (hcont𝒜 : ContinuousOn 𝒜 (Set.Icc 0 T)) (hbound𝒜 : ∀ t ∈ Set.Icc 0 T, ‖𝒜 t‖ ≤ K)
    (N : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∑ n ∈ Finset.range (N + 1), picardIter 𝒜 x₀ n t
      = x₀ + ∫ s in (0 : ℝ)..t, 𝒜 s (∑ n ∈ Finset.range N, picardIter 𝒜 x₀ n s) := by
  have hcb := picardIter_continuousOn_and_bound 𝒜 x₀ T hT K hK hcont𝒜 hbound𝒜
  have hint : ∀ n, IntervalIntegrable
      (fun s => 𝒜 s (picardIter 𝒜 x₀ n s)) volume 0 t := by
    intro n
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ht.1]
    exact (hcont𝒜.clm_apply (hcb n).1).mono (Set.Icc_subset_Icc_right ht.2)
  rw [Finset.sum_range_succ', picardIter_zero]
  simp only [picardIter_succ]
  rw [add_comm]
  congr 1
  rw [← intervalIntegral.integral_finsetSum (fun i _ => hint i)]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  exact (map_sum (𝒜 s) (fun i => picardIter 𝒜 x₀ i s) (Finset.range N)).symm

/-- **C3 V1c-inteq — the Dyson sum solves the integral equation.**
`M(t) = x₀ + ∫₀ᵗ 𝒜(s)(M s) ds` on `[0,T]`, where `M = ∑'ₙ Iₙ`.  Pass `N → ∞` in the finite
recurrence: LHS → `M t` (partial sums of the summable series); RHS via DCT (the terms
`𝒜(s)(S_N s) → 𝒜(s)(M s)` pointwise, dominated by the constant `K·∑'ₙ (KT)ⁿ/n!·‖x₀‖`). -/
lemma picardSum_solves_integralEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (x₀ : E) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (hcont𝒜 : ContinuousOn 𝒜 (Set.Icc 0 T)) (hbound𝒜 : ∀ t ∈ Set.Icc 0 T, ‖𝒜 t‖ ≤ K)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∑' n, picardIter 𝒜 x₀ n t)
      = x₀ + ∫ s in (0 : ℝ)..t, 𝒜 s (∑' n, picardIter 𝒜 x₀ n s) := by
  have hcb := picardIter_continuousOn_and_bound 𝒜 x₀ T hT K hK hcont𝒜 hbound𝒜
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have htT : t ≤ T := ht.2
  have hmaj : ∀ n, ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖picardIter 𝒜 x₀ n s‖ ≤ (K * T) ^ n / n.factorial * ‖x₀‖ := by
    intro n s hs
    refine le_trans ((hcb n).2 s hs) ?_
    have hKs : 0 ≤ K * s := mul_nonneg hK hs.1
    have hle : K * s ≤ K * T := mul_le_mul_of_nonneg_left hs.2 hK
    gcongr
  have hmaj_summable : Summable (fun n => (K * T) ^ n / n.factorial * ‖x₀‖) :=
    (Real.summable_pow_div_factorial (K * T)).mul_right ‖x₀‖
  have hsummable : ∀ s ∈ Set.Icc (0 : ℝ) T, Summable (fun n => picardIter 𝒜 x₀ n s) := by
    intro s hs
    exact (hmaj_summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hmaj n s hs)).of_norm
  set C : ℝ := ∑' n, (K * T) ^ n / n.factorial * ‖x₀‖ with hC
  have hSbound : ∀ N, ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖∑ n ∈ Finset.range N, picardIter 𝒜 x₀ n s‖ ≤ C := by
    intro N s hs
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun n _ => hmaj n s hs)) ?_
    exact hmaj_summable.sum_le_tsum _ (fun n _ => by positivity)
  set M : ℝ → E := fun u => ∑' n, picardIter 𝒜 x₀ n u with hM
  have hLHS : Filter.Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), picardIter 𝒜 x₀ n t)
      Filter.atTop (nhds (M t)) :=
    ((hsummable t ht).hasSum.tendsto_sum_nat).comp (Filter.tendsto_add_atTop_nat 1)
  have hRHS_int : Filter.Tendsto
      (fun N => ∫ s in Set.Ioc (0 : ℝ) t, 𝒜 s (∑ n ∈ Finset.range N, picardIter 𝒜 x₀ n s))
      Filter.atTop (nhds (∫ s in Set.Ioc (0 : ℝ) t, 𝒜 s (M s))) := by
    apply MeasureTheory.tendsto_integral_of_dominated_convergence (bound := fun _ => K * C)
    · intro N
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
      exact (hcont𝒜.clm_apply (continuousOn_finsetSum _ (fun n _ => (hcb n).1))).mono
        (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_right htT))
    · exact integrableOn_const (hs := measure_Ioc_lt_top.ne)
    · intro N
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => ?_)
      have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨le_of_lt hs.1, le_trans hs.2 htT⟩
      calc ‖𝒜 s (∑ n ∈ Finset.range N, picardIter 𝒜 x₀ n s)‖
          ≤ ‖𝒜 s‖ * ‖∑ n ∈ Finset.range N, picardIter 𝒜 x₀ n s‖ := (𝒜 s).le_opNorm _
        _ ≤ K * C := mul_le_mul (hbound𝒜 s hsT) (hSbound N s hsT) (norm_nonneg _) hK
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun s hs => ?_)
      have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨le_of_lt hs.1, le_trans hs.2 htT⟩
      exact ((𝒜 s).continuous.tendsto (M s)).comp ((hsummable s hsT).hasSum.tendsto_sum_nat)
  rw [intervalIntegral.integral_of_le ht0]
  have hrec' : ∀ N, ∑ n ∈ Finset.range (N + 1), picardIter 𝒜 x₀ n t
      = x₀ + ∫ s in Set.Ioc (0 : ℝ) t, 𝒜 s (∑ n ∈ Finset.range N, picardIter 𝒜 x₀ n s) := by
    intro N
    rw [picardSum_finset_recurrence 𝒜 x₀ T hT K hK hcont𝒜 hbound𝒜 N t ht,
      intervalIntegral.integral_of_le ht0]
  exact tendsto_nhds_unique hLHS ((hRHS_int.const_add x₀).congr (fun N => (hrec' N).symm))

/-- **C3 V1c — existence for a linear ODE with continuous coefficients on a compact interval**
(the fundamental solution of the variational equation; a Mathlib gap).

For a continuous family of bounded linear maps `𝒜 : ℝ → (E →L[ℝ] E)` on a Banach space `E`, the
linear IVP `x' = 𝒜(t) x`, `x(0) = x₀` has a solution on `[0,T]`.  Generic and reusable
(promotable to `Mathlib/Analysis/ODE/`); instantiated for the variational equation with
`E := PhaseSpace d →L[ℝ] PhaseSpace d`, `𝒜(t) := (·).comp-by A(t)` (left composition), `x₀ := id`
to produce the fundamental matrix `M(t)`, where `A(t) = vlasovVectorField_hasFDerivAt_in_z`'s
block CLM evaluated along the flow.

**Why not Mathlib's `IsPicardLindelof`**: that needs a *globally bounded* field
(`norm_le : ‖f t x‖ ≤ L`); the linear field `x ↦ 𝒜(t) x` is unbounded, and confining to a ball
makes the Picard window-condition `K·e^{KT}·T ≤ e^{KT}−1` fail for a single window (⇒ tiling).

**Proof plan (integral-operator contraction, no tiling)**: on the Banach space
`C([0,T]; E)` the Picard operator `𝒯[M](t) := x₀ + ∫_0^t 𝒜(s) (M s) ds` is `K·T`-Lipschitz
(`K := sup_{[0,T]} ‖𝒜‖`, finite by continuity on the compact `[0,T]`), and its `n`-th iterate is
`(K·T)^n/n!`-Lipschitz (induction on the Bochner-integral bound), which is `< 1` for large `n`;
so `𝒯` has a unique fixed point by the iterated-contraction Banach theorem
(`ContractingWith` + `exists_fixedPoint`, `Mathlib/Topology/MetricSpace/Contracting.lean`).
Differentiating the fixed-point integral equation (FTC, `HasDerivWithinAt` of `t ↦ ∫_0^t …`)
recovers `x' = 𝒜(t) x`; `x(0) = x₀` from the lower integral limit. -/
theorem exists_linearODE_solution_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (𝒜 : ℝ → (E →L[ℝ] E)) (T : ℝ) (hT : 0 ≤ T)
    (h𝒜 : ContinuousOn 𝒜 (Set.Icc 0 T)) (x₀ : E) :
    ∃ M : ℝ → E, M 0 = x₀ ∧ ContinuousOn M (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt M (𝒜 t (M t)) (Set.Icc 0 T) t := by
  obtain ⟨K, hbK⟩ := isCompact_Icc.exists_bound_of_continuousOn h𝒜
  have hK'0 : 0 ≤ max K 0 := le_max_right _ _
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖𝒜 t‖ ≤ max K 0 :=
    fun t ht => le_trans (hbK t ht) (le_max_left _ _)
  set M : ℝ → E := fun u => ∑' n, picardIter 𝒜 x₀ n u with hM
  have hMcont : ContinuousOn M (Set.Icc 0 T) :=
    picardSum_continuousOn 𝒜 x₀ T hT (max K 0) hK'0 h𝒜 hbound
  have hMeq : ∀ t ∈ Set.Icc (0 : ℝ) T, M t = x₀ + ∫ s in (0 : ℝ)..t, 𝒜 s (M s) :=
    fun t ht => picardSum_solves_integralEq 𝒜 x₀ T hT (max K 0) hK'0 h𝒜 hbound t ht
  have hg_cont : ContinuousOn (fun s => 𝒜 s (M s)) (Set.Icc 0 T) := h𝒜.clm_apply hMcont
  refine ⟨M, ?_, hMcont, fun t ht => ?_⟩
  · rw [hMeq 0 ⟨le_refl 0, hT⟩, intervalIntegral.integral_same, add_zero]
  · have : Fact (t ∈ Set.Icc (0 : ℝ) T) := ⟨ht⟩
    have hg_int : IntervalIntegrable (fun s => 𝒜 s (M s)) volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le ht.1]
      exact hg_cont.mono (Set.Icc_subset_Icc_right ht.2)
    have hg_meas : StronglyMeasurableAtFilter (fun s => 𝒜 s (M s)) (nhdsWithin t (Set.Icc 0 T)) :=
      ⟨Set.Icc 0 T, self_mem_nhdsWithin, hg_cont.aestronglyMeasurable measurableSet_Icc⟩
    have hFTC : HasDerivWithinAt (fun u => ∫ s in (0 : ℝ)..u, 𝒜 s (M s)) (𝒜 t (M t))
        (Set.Icc 0 T) t :=
      intervalIntegral.integral_hasDerivWithinAt_right hg_int hg_meas (hg_cont t ht)
    exact (hFTC.const_add x₀).congr (fun y hy => hMeq y hy) (hMeq t ht)

/-- **C3 V1c→matrix — the fundamental matrix of a linear ODE.**  Specialising
`exists_linearODE_solution_Icc` to the operator space `E := F →L[ℝ] F` with `𝒜(s) := A(s) ∘ (·)`
(left composition) and `x₀ := id` gives the fundamental solution `M' = A(t)∘M`, `M(0) = id`.
This `M(t)` is the candidate `Dflow t z` of the variational equation (#3), once `A` is the Vlasov
field Jacobian `A(s) = D_z b(s, Φ_s z)` along the flow (F2). -/
lemma exists_fundamentalMatrix
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : ℝ → (F →L[ℝ] F)) (T : ℝ) (hT : 0 ≤ T) (hA : ContinuousOn A (Set.Icc 0 T)) :
    ∃ M : ℝ → (F →L[ℝ] F), M 0 = ContinuousLinearMap.id ℝ F ∧ ContinuousOn M (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt M ((A t).comp (M t)) (Set.Icc 0 T) t := by
  obtain ⟨M, hM0, hMcont, hMderiv⟩ := exists_linearODE_solution_Icc
    (fun s => ContinuousLinearMap.compL ℝ F F F (A s)) T hT
    ((ContinuousLinearMap.compL ℝ F F F).continuous.comp_continuousOn hA)
    (ContinuousLinearMap.id ℝ F)
  refine ⟨M, hM0, hMcont, fun t ht => ?_⟩
  simpa [ContinuousLinearMap.compL_apply] using hMderiv t ht

omit [NeZero d] in
/-- **C3 A-cont — the variational coefficient `A(s,z) = D_z b(s, Φ_s z)` is continuous in `s`.**
`A(s,z)` is the F2 block CLM `(snd).prod(−(∫ fderiv gradW (charX s z − y) ∂ρ_s) ∘ fst)`; its only
`s`-varying part is the convolution-derivative integral, continuous via `hρD_cont` composed with
the flow.  The block CLM is reassembled with `inl∘snd + inr∘(·)` (Mathlib has no `clm_prod`
continuity combinator).  This `ContinuousOn` is the coefficient input to `exists_fundamentalMatrix`
that produces the fundamental matrix `M_t(z) = Dflow t z` for `#3`. -/
lemma vlasovVariationalCoeff_continuousOn
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d) (T : ℝ) (z : PhaseSpace d)
    (hcontIcc : ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d)))) :
    ContinuousOn (fun s => (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d)).prod
      (-((∫ y, fderiv ℝ gradW (charX s z - y) ∂(ρ s)).comp
          (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d))))) (Set.Icc 0 T) := by
  have hX : ContinuousOn (fun s => charX s z) (Set.Icc (0 : ℝ) T) :=
    continuous_fst.comp_continuousOn hcontIcc
  have hpair : ContinuousOn (fun s => ((s, charX s z) : ℝ × PhysSpace d)) (Set.Icc (0 : ℝ) T) :=
    continuousOn_id.prodMk hX
  have hmaps : Set.MapsTo (fun s => ((s, charX s z) : ℝ × PhysSpace d))
      (Set.Icc (0 : ℝ) T) (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))) :=
    fun s hs => ⟨hs, Set.mem_univ _⟩
  have hD : ContinuousOn (fun s => ∫ y, fderiv ℝ gradW (charX s z - y) ∂(ρ s)) (Set.Icc 0 T) :=
    hρD_cont.comp hpair hmaps
  have hDcomp : ContinuousOn (fun s => -((∫ y, fderiv ℝ gradW (charX s z - y) ∂(ρ s)).comp
      (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d)))) (Set.Icc 0 T) :=
    (hD.clm_comp continuousOn_const).neg
  have heq : (fun s => (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d)).prod
        (-((∫ y, fderiv ℝ gradW (charX s z - y) ∂(ρ s)).comp
            (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d)))))
      = (fun s => (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)).comp
            (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d))
          + (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)).comp
            (-((∫ y, fderiv ℝ gradW (charX s z - y) ∂(ρ s)).comp
                (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d))))) := by
    funext s; ext x <;> simp
  rw [heq]
  exact continuousOn_const.add (continuousOn_const.clm_comp hDcomp)

/-- **C3 D1 (Jacobian).**  The phase-space Jacobian `A(s, p) = D_w b(s, p)` of the frozen Vlasov
field at the base point `p`: the block continuous-linear map `δ ↦ (δ.2, −(D_x conv ρ_s)(p.1)·δ.1)`,
where `D_x conv ρ_s (p.1) = ∫ y, fderiv ℝ gradW (p.1 − y) ∂ρ_s` (F1).  This is the coefficient of
the linear variational ODE `M' = A(s, Φ_s z)·M`; `vlasovVectorField_hasFDerivAt_in_z` (F2) says it
is the Fréchet derivative of `vlasovVectorField gradW ρ s` at `p.2`. -/
noncomputable def vlasovFieldJacobian (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d)) (p : ℝ × PhaseSpace d) : PhaseSpace d →L[ℝ] PhaseSpace d :=
  (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d)).prod
    (-((∫ y, fderiv ℝ gradW (p.2.1 - y) ∂(ρ p.1)).comp
        (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d))))

omit [NeZero d] in
/-- **C3 D1a — the uniform-over-compact first-order Taylor remainder of the Vlasov field.**

For a fixed initial point `z`, the first-order remainder of the frozen field `b(s,·)` at the moving
base point `Φ_s z := (charX s z, charV s z)`,
`R(s,w) = b(s,w) − b(s,Φ_s z) − A(s,Φ_s z)·(w − Φ_s z)`, is `o(‖w − Φ_s z‖)` **uniformly in
`s ∈ [0,T]`**: for every `η > 0` there is a single `δ > 0` (independent of `s`) with
`‖R(s,w)‖ ≤ η·‖w − Φ_s z‖` whenever `‖w − Φ_s z‖ ≤ δ`.

This uniformity is the load-bearing analytic core of D1 (the variational-equation difference
quotient): it is what lets Grönwall bound `Φ_t(z+h) − Φ_t(z) − M_t(z)·h` by `o(‖h‖)` *uniformly
along the trajectory*.  Proof: the flow image `{Φ_s z : s ∈ [0,T]}` is compact (continuous image of
`[0,T]`), `A = D_w b` is jointly `(s,w)`-continuous (from `hρD_cont`), so `A` is **uniformly**
continuous on the compact tube `Γ = {(s, Φ_s z + e) : s ∈ [0,T], ‖e‖ ≤ 1}` (Heine–Cantor); the
mean-value inequality on `closedBall (Φ_s z) δ` then converts the modulus into the remainder
bound. -/
lemma vlasovField_taylorRemainder_uniform
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d) (T : ℝ) (z : PhaseSpace d)
    (hcontIcc : ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d)))) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ w : PhaseSpace d,
      ‖w - (charX s z, charV s z)‖ ≤ δ →
      ‖vlasovVectorField gradW ρ s w - vlasovVectorField gradW ρ s (charX s z, charV s z)
        - (vlasovFieldJacobian gradW ρ (s, (charX s z, charV s z))) (w - (charX s z, charV s z))‖
        ≤ η * ‖w - (charX s z, charV s z)‖ := by
  set Φ : ℝ → PhaseSpace d := fun s => (charX s z, charV s z) with hΦ
  -- F2: the field is differentiable in the phase variable with derivative `vlasovFieldJacobian`.
  have hF2 : ∀ s (w : PhaseSpace d),
      HasFDerivAt (vlasovVectorField gradW ρ s) (vlasovFieldJacobian gradW ρ (s, w)) w :=
    fun s w => vlasovVectorField_hasFDerivAt_in_z gradW hgradW_C1 L hL ρ h_int s w
  -- Joint continuity of the Jacobian on `Icc 0 T ×ˢ Set.univ` (from `hρD_cont`).
  have hg_cont : Continuous (fun p : ℝ × PhaseSpace d => ((p.1, p.2.1) : ℝ × PhysSpace d)) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have hmaps : Set.MapsTo (fun p : ℝ × PhaseSpace d => ((p.1, p.2.1) : ℝ × PhysSpace d))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhaseSpace d)))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))) :=
    fun p hp => ⟨hp.1, Set.mem_univ _⟩
  have hD2 : ContinuousOn
      (fun p : ℝ × PhaseSpace d => ∫ y, fderiv ℝ gradW (p.2.1 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ Set.univ) :=
    hρD_cont.comp hg_cont.continuousOn hmaps
  have hDcomp : ContinuousOn
      (fun p : ℝ × PhaseSpace d => -((∫ y, fderiv ℝ gradW (p.2.1 - y) ∂(ρ p.1)).comp
        (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d)))) (Set.Icc 0 T ×ˢ Set.univ) :=
    (hD2.clm_comp continuousOn_const).neg
  have heq : (fun p : ℝ × PhaseSpace d => vlasovFieldJacobian gradW ρ p) = fun p =>
        (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)).comp
          (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d))
        + (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)).comp
          (-((∫ y, fderiv ℝ gradW (p.2.1 - y) ∂(ρ p.1)).comp
              (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d)))) := by
    funext p; ext x <;> simp [vlasovFieldJacobian]
  have hAj_cont : ContinuousOn (fun p : ℝ × PhaseSpace d => vlasovFieldJacobian gradW ρ p)
      (Set.Icc 0 T ×ˢ Set.univ) := by
    rw [heq]; exact continuousOn_const.add (continuousOn_const.clm_comp hDcomp)
  -- The compact tube `Γ = {(s, Φ s + e) : s ∈ [0,T], ‖e‖ ≤ 1}`.
  set ball1 : Set (PhaseSpace d) := Metric.closedBall 0 1 with hball1
  have hmap : ContinuousOn (fun q : ℝ × PhaseSpace d => ((q.1, Φ q.1 + q.2) : ℝ × PhaseSpace d))
      (Set.Icc 0 T ×ˢ ball1) :=
    continuousOn_fst.prodMk
      ((hcontIcc.comp continuousOn_fst (fun q hq => hq.1)).add continuousOn_snd)
  set Γ : Set (ℝ × PhaseSpace d) :=
    (fun q : ℝ × PhaseSpace d => ((q.1, Φ q.1 + q.2) : ℝ × PhaseSpace d)) '' (Set.Icc 0 T ×ˢ ball1)
    with hΓ
  have hΓcompact : IsCompact Γ :=
    (isCompact_Icc.prod (isCompact_closedBall 0 1)).image_of_continuousOn hmap
  have hΓsub : Γ ⊆ Set.Icc 0 T ×ˢ Set.univ := by
    rintro _ ⟨q, hq, rfl⟩; exact ⟨hq.1, Set.mem_univ _⟩
  have hUC : UniformContinuousOn (fun p => vlasovFieldJacobian gradW ρ p) Γ :=
    hΓcompact.uniformContinuousOn_of_continuous (hAj_cont.mono hΓsub)
  have hmemΓ : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ e : PhaseSpace d, ‖e‖ ≤ 1 →
      ((s, Φ s + e) : ℝ × PhaseSpace d) ∈ Γ := by
    intro s hs e he
    exact ⟨(s, e), ⟨hs, by simpa [hball1, Metric.mem_closedBall, dist_eq_norm] using he⟩, rfl⟩
  -- Extract the uniform-continuity modulus.
  intro η hη
  obtain ⟨δ₀, hδ₀, H⟩ := Metric.uniformContinuousOn_iff_le.mp hUC η hη
  refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, ?_⟩
  intro s hs w hw
  -- Mean value on the convex ball `C = closedBall (Φ s) (min δ₀ 1)`.
  set C : Set (PhaseSpace d) := Metric.closedBall (Φ s) (min δ₀ 1) with hC
  have hΦmem : Φ s ∈ C := Metric.mem_closedBall_self (le_min hδ₀.le zero_le_one)
  have hwmem : w ∈ C := by
    rw [hC, Metric.mem_closedBall, dist_eq_norm]; exact hw
  -- The fderiv bound on `C` from uniform continuity.
  have hbound : ∀ w' ∈ C,
      ‖vlasovFieldJacobian gradW ρ (s, w') - vlasovFieldJacobian gradW ρ (s, Φ s)‖ ≤ η := by
    intro w' hw'
    have hw'norm : ‖w' - Φ s‖ ≤ min δ₀ 1 := by
      rw [← dist_eq_norm]; rw [hC, Metric.mem_closedBall] at hw'; exact hw'
    have hw'le1 : ‖w' - Φ s‖ ≤ 1 := hw'norm.trans (min_le_right _ _)
    have hmem1 : ((s, w') : ℝ × PhaseSpace d) ∈ Γ := by
      have := hmemΓ s hs (w' - Φ s) hw'le1
      rwa [add_sub_cancel] at this
    have hmem2 : ((s, Φ s) : ℝ × PhaseSpace d) ∈ Γ := by
      have := hmemΓ s hs 0 (by simp)
      rwa [add_zero] at this
    have hdist : dist ((s, w') : ℝ × PhaseSpace d) (s, Φ s) ≤ δ₀ := by
      rw [Prod.dist_eq]
      simp only [dist_self, max_le_iff]
      refine ⟨hδ₀.le, ?_⟩
      rw [dist_eq_norm]; exact hw'norm.trans (min_le_left _ _)
    have := H _ hmem1 _ hmem2 hdist
    rwa [dist_eq_norm] at this
  -- Apply the mean value inequality to `g u = b(s,u) − A(s,Φ s)·u`.
  have hg : ∀ w' ∈ C, HasFDerivWithinAt
      (fun u => vlasovVectorField gradW ρ s u - vlasovFieldJacobian gradW ρ (s, Φ s) u)
      (vlasovFieldJacobian gradW ρ (s, w') - vlasovFieldJacobian gradW ρ (s, Φ s)) C w' := by
    intro w' _
    have h1 := hF2 s w'
    have h2 : HasFDerivAt (fun u => vlasovFieldJacobian gradW ρ (s, Φ s) u)
        (vlasovFieldJacobian gradW ρ (s, Φ s)) w' :=
      (vlasovFieldJacobian gradW ρ (s, Φ s)).hasFDerivAt
    exact (h1.sub h2).hasFDerivWithinAt
  have hmv := (convex_closedBall (Φ s) (min δ₀ 1)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hg hbound hΦmem hwmem
  -- Rewrite `g w − g (Φ s)` as the remainder.
  have hReq : (vlasovVectorField gradW ρ s w - vlasovFieldJacobian gradW ρ (s, Φ s) w)
        - (vlasovVectorField gradW ρ s (Φ s) - vlasovFieldJacobian gradW ρ (s, Φ s) (Φ s))
      = vlasovVectorField gradW ρ s w - vlasovVectorField gradW ρ s (Φ s)
        - vlasovFieldJacobian gradW ρ (s, Φ s) (w - Φ s) := by
    rw [map_sub]; abel
  simpa only [hReq] using hmv

omit [NeZero d] in
/-- **C3 (shared) — joint continuity of the Jacobian** on `Icc 0 T ×ˢuniv` (used by V2's
`hA_contOn`).  The block CLM `vlasovFieldJacobian` is reassembled `inl∘snd + inr∘(·)` and its
varying part is continuous via `hρD_cont`. -/
lemma vlasovFieldJacobian_continuousOn
    (gradW : PhysSpace d → PhysSpace d) (ρ : ℝ → Measure (PhysSpace d)) (T : ℝ)
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d)))) :
    ContinuousOn (fun p : ℝ × PhaseSpace d => vlasovFieldJacobian gradW ρ p)
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhaseSpace d))) := by
  have hg_cont : Continuous (fun p : ℝ × PhaseSpace d => ((p.1, p.2.1) : ℝ × PhysSpace d)) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have hmaps : Set.MapsTo (fun p : ℝ × PhaseSpace d => ((p.1, p.2.1) : ℝ × PhysSpace d))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhaseSpace d)))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))) :=
    fun p hp => ⟨hp.1, Set.mem_univ _⟩
  have hD2 : ContinuousOn
      (fun p : ℝ × PhaseSpace d => ∫ y, fderiv ℝ gradW (p.2.1 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ Set.univ) :=
    hρD_cont.comp hg_cont.continuousOn hmaps
  have hDcomp : ContinuousOn
      (fun p : ℝ × PhaseSpace d => -((∫ y, fderiv ℝ gradW (p.2.1 - y) ∂(ρ p.1)).comp
        (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d)))) (Set.Icc 0 T ×ˢ Set.univ) :=
    (hD2.clm_comp continuousOn_const).neg
  have heq : (fun p : ℝ × PhaseSpace d => vlasovFieldJacobian gradW ρ p) = fun p =>
        (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)).comp
          (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d))
        + (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)).comp
          (-((∫ y, fderiv ℝ gradW (p.2.1 - y) ∂(ρ p.1)).comp
              (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d)))) := by
    funext p; ext x <;> simp [vlasovFieldJacobian]
  rw [heq]; exact continuousOn_const.add (continuousOn_const.clm_comp hDcomp)

/-- **C3 (shared) — Lipschitz-in-parameter + ContinuousOn-in-time ⇒ jointly ContinuousOn.**
A generic upgrade: if `G z ·` is `ContinuousOn (Icc 0 T)` for each `z` and `z ↦ G z s` is
`C`-Lipschitz uniformly over `s ∈ [0,T]`, then `(z,s) ↦ G z s` is jointly continuous on
`univ ×ˢ Icc 0 T`.  Used to derive flow joint continuity `(z,s) ↦ Φ_s z` from
`charFlow_lipschitzInZ_via_gronwall_Ioo` (Lipschitz-in-`z`) + per-`z` continuity in `s`. -/
lemma continuousOn_prod_of_lipschitz_continuousOn
    {Z E : Type*} [PseudoMetricSpace Z] [PseudoMetricSpace E]
    (G : Z → ℝ → E) (T C : ℝ)
    (hlip : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z₁ z₂, dist (G z₁ s) (G z₂ s) ≤ C * dist z₁ z₂)
    (hcont : ∀ z, ContinuousOn (fun s => G z s) (Set.Icc (0 : ℝ) T)) :
    ContinuousOn (fun p : Z × ℝ => G p.1 p.2) (Set.univ ×ˢ Set.Icc (0 : ℝ) T) := by
  rw [Metric.continuousOn_iff]
  rintro ⟨z₀, s₀⟩ ⟨_, hs₀⟩ ε hε
  obtain ⟨δ₁, hδ₁, hcs⟩ :=
    (Metric.continuousWithinAt_iff).mp (hcont z₀ s₀ hs₀) (ε/2) (by positivity)
  have hC1 : (0 : ℝ) < |C| + 1 := by positivity
  refine ⟨min δ₁ (ε / (2 * (|C| + 1))), by positivity, ?_⟩
  rintro ⟨z, s⟩ ⟨_, hs⟩ hd
  rw [Prod.dist_eq, max_lt_iff] at hd
  obtain ⟨hdz, hds⟩ := hd
  have hterm1 : dist (G z s) (G z₀ s) < ε/2 := by
    calc dist (G z s) (G z₀ s)
        ≤ C * dist z z₀ := hlip s hs z z₀
      _ ≤ (|C| + 1) * dist z z₀ :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) dist_nonneg
      _ < (|C| + 1) * (ε / (2 * (|C| + 1))) :=
          mul_lt_mul_of_pos_left (lt_of_lt_of_le hdz (min_le_right _ _)) hC1
      _ = ε/2 := by field_simp
  have hterm2 : dist (G z₀ s) (G z₀ s₀) < ε/2 :=
    hcs hs (lt_of_lt_of_le hds (min_le_left _ _))
  calc dist (G z s) (G z₀ s₀)
      ≤ dist (G z s) (G z₀ s) + dist (G z₀ s) (G z₀ s₀) := dist_triangle _ _ _
    _ < ε/2 + ε/2 := add_lt_add hterm1 hterm2
    _ = ε := by ring

/-- **C3 V2 — the explicit fundamental matrix** (Route A, lesson L14): the canonical Dyson-series
solution of `M' = A(t)·M`, `M 0 = id`, as a *function* (not a `choose`-d witness), so its
parameter-regularity is accessible. -/
noncomputable def fundamentalMatrix {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ℝ → (F →L[ℝ] F)) : ℝ → (F →L[ℝ] F) :=
  fun t => ∑' n, picardIter (fun s => ContinuousLinearMap.compL ℝ F F F (A s))
    (ContinuousLinearMap.id ℝ F) n t

/-- `fundamentalMatrix A` solves the fundamental-matrix IVP on `[0,T]` (the non-existential form of
`exists_fundamentalMatrix`; same proof through the picardSum lemmas). -/
lemma fundamentalMatrix_spec {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : ℝ → (F →L[ℝ] F)) (T : ℝ) (hT : 0 ≤ T) (hA : ContinuousOn A (Set.Icc 0 T)) :
    fundamentalMatrix A 0 = ContinuousLinearMap.id ℝ F ∧
      ContinuousOn (fundamentalMatrix A) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (fundamentalMatrix A)
        ((A t).comp (fundamentalMatrix A t)) (Set.Icc 0 T) t := by
  have h𝒜cont : ContinuousOn (fun s => ContinuousLinearMap.compL ℝ F F F (A s)) (Set.Icc 0 T) :=
    (ContinuousLinearMap.compL ℝ F F F).continuous.comp_continuousOn hA
  obtain ⟨KA, hKA⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hA
  have hK'0 : (0 : ℝ) ≤ max KA 0 := le_max_right _ _
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖ContinuousLinearMap.compL ℝ F F F (A t)‖ ≤ max KA 0 := by
    intro t ht
    have h1 : ‖ContinuousLinearMap.compL ℝ F F F (A t)‖ ≤ ‖A t‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun g => ?_)
      rw [ContinuousLinearMap.compL_apply]; exact (A t).opNorm_comp_le g
    exact le_trans (le_trans h1 (hKA t ht)) (le_max_left KA 0)
  have hMcont : ContinuousOn (fundamentalMatrix A) (Set.Icc 0 T) :=
    picardSum_continuousOn (fun s => ContinuousLinearMap.compL ℝ F F F (A s))
      (ContinuousLinearMap.id ℝ F) T hT (max KA 0) hK'0 h𝒜cont hbound
  have hMeq : ∀ t ∈ Set.Icc (0 : ℝ) T, fundamentalMatrix A t = ContinuousLinearMap.id ℝ F
      + ∫ s in (0 : ℝ)..t, ContinuousLinearMap.compL ℝ F F F (A s) (fundamentalMatrix A s) :=
    fun t ht => picardSum_solves_integralEq (fun s => ContinuousLinearMap.compL ℝ F F F (A s))
      (ContinuousLinearMap.id ℝ F) T hT (max KA 0) hK'0 h𝒜cont hbound t ht
  have hg_cont : ContinuousOn
      (fun s => ContinuousLinearMap.compL ℝ F F F (A s) (fundamentalMatrix A s)) (Set.Icc 0 T) :=
    h𝒜cont.clm_apply hMcont
  refine ⟨?_, hMcont, fun t ht => ?_⟩
  · rw [hMeq 0 ⟨le_refl 0, hT⟩, intervalIntegral.integral_same, add_zero]
  · have : Fact (t ∈ Set.Icc (0 : ℝ) T) := ⟨ht⟩
    have hg_int : IntervalIntegrable
        (fun s => ContinuousLinearMap.compL ℝ F F F (A s) (fundamentalMatrix A s)) volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le ht.1]; exact hg_cont.mono (Set.Icc_subset_Icc_right ht.2)
    have hg_meas : StronglyMeasurableAtFilter
        (fun s => ContinuousLinearMap.compL ℝ F F F (A s) (fundamentalMatrix A s))
        (nhdsWithin t (Set.Icc 0 T)) :=
      ⟨Set.Icc 0 T, self_mem_nhdsWithin, hg_cont.aestronglyMeasurable measurableSet_Icc⟩
    have hFTC : HasDerivWithinAt
        (fun u => ∫ s in (0 : ℝ)..u,
          ContinuousLinearMap.compL ℝ F F F (A s) (fundamentalMatrix A s))
        (ContinuousLinearMap.compL ℝ F F F (A t) (fundamentalMatrix A t)) (Set.Icc 0 T) t :=
      intervalIntegral.integral_hasDerivWithinAt_right hg_int hg_meas (hg_cont t ht)
    have hHD := (hFTC.const_add (ContinuousLinearMap.id ℝ F)).congr
      (fun y hy => hMeq y hy) (hMeq t ht)
    rwa [ContinuousLinearMap.compL_apply] at hHD

/-- **C3 V2 — the fundamental matrix is continuous in a PARAMETER** (closes V2 via Route A).
Specialises `picardSum_continuous_param_Icc` to `𝒜 := compL∘A`, `x₀ := id`; the `compL` factor is
`1`-bounded so the `K`-bound transfers from `A`. -/
lemma fundamentalMatrix_continuous_param
    {Z F : Type*} [TopologicalSpace Z] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : Z → ℝ → (F →L[ℝ] F)) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (hA_contOn : ContinuousOn (fun p : Z × ℝ => A p.1 p.2) (Set.univ ×ˢ Set.Icc (0 : ℝ) T))
    (hA_bound : ∀ z, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖A z s‖ ≤ K)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Continuous (fun z => fundamentalMatrix (A z) t) := by
  have h𝒜_contOn : ContinuousOn
      (fun p : Z × ℝ => ContinuousLinearMap.compL ℝ F F F (A p.1 p.2))
      (Set.univ ×ˢ Set.Icc (0 : ℝ) T) :=
    (ContinuousLinearMap.compL ℝ F F F).continuous.comp_continuousOn hA_contOn
  have h𝒜_bound : ∀ z, ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖ContinuousLinearMap.compL ℝ F F F (A z s)‖ ≤ K := by
    intro z s hs
    refine le_trans ?_ (hA_bound z s hs)
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun g => ?_)
    rw [ContinuousLinearMap.compL_apply]
    exact (A z s).opNorm_comp_le g
  exact picardSum_continuous_param_Icc (fun z s => ContinuousLinearMap.compL ℝ F F F (A z s))
    (ContinuousLinearMap.id ℝ F) T hT K hK h𝒜_contOn h𝒜_bound t ht

/-- **Step 3 (i) — joint `(z,s)` continuity of the Dyson sum** (global-hypothesis form).
Mirror of `picardSum_continuous_param`, concluding JOINT `ContinuousOn` on `univ ×ˢ Icc 0 T`
instead of per-`t` continuity in `z`.  The proof reuses the same joint iterate continuity
(`hiter_cont` on `Z × ℝ`) and the same `(z,s)`-independent M-test majorant `(KT)ⁿ/n!·‖x₀‖`; only
the final `tendstoUniformlyOn` ranges over `univ ×ˢ Icc 0 T`.  Used to make the variational
fundamental matrix `(z,s) ↦ M z s` jointly continuous (the partial-derivative continuity the
two-time-flow joint `C¹`-ness needs). -/
lemma picardSum_continuous_param_joint
    {Z E : Type*} [TopologicalSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (𝒜 : Z → ℝ → (E →L[ℝ] E)) (x₀ : E) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (h𝒜_cont : Continuous (fun p : Z × ℝ => 𝒜 p.1 p.2))
    (h𝒜_bound : ∀ z, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖𝒜 z s‖ ≤ K) :
    ContinuousOn (fun p : Z × ℝ => ∑' n, picardIter (𝒜 p.1) x₀ n p.2)
      (Set.univ ×ˢ Set.Icc (0 : ℝ) T) := by
  have hiter_cont : ∀ n, Continuous (fun p : Z × ℝ => picardIter (𝒜 p.1) x₀ n p.2) := by
    intro n
    induction n with
    | zero =>
      simp only [picardIter_zero]
      exact continuous_const
    | succ n ih =>
      have hg : Continuous (Function.uncurry fun z v => 𝒜 z v (picardIter (𝒜 z) x₀ n v)) :=
        h𝒜_cont.clm_apply ih
      have hpp := intervalIntegral.continuous_parametric_primitive_of_continuous
        (μ := volume) (a₀ := (0 : ℝ)) hg
      simp only [picardIter_succ]
      exact hpp
  have h𝒜cont_z : ∀ z, ContinuousOn (𝒜 z) (Set.Icc (0 : ℝ) T) := fun z =>
    (h𝒜_cont.comp (continuous_const.prodMk continuous_id)).continuousOn
  have hbd : ∀ (n : ℕ) (p : Z × ℝ), p ∈ Set.univ ×ˢ Set.Icc (0 : ℝ) T →
      ‖picardIter (𝒜 p.1) x₀ n p.2‖ ≤ (K * T) ^ n / n.factorial * ‖x₀‖ := by
    intro n p hp
    have hps : p.2 ∈ Set.Icc (0 : ℝ) T := hp.2
    have hb := (picardIter_continuousOn_and_bound (𝒜 p.1) x₀ T hT K hK (h𝒜cont_z p.1)
      (h𝒜_bound p.1) n).2 p.2 hps
    refine le_trans hb ?_
    have hKt : (0 : ℝ) ≤ K * p.2 := mul_nonneg hK hps.1
    have hle : K * p.2 ≤ K * T := mul_le_mul_of_nonneg_left hps.2 hK
    gcongr
  have hsum : Summable (fun n => (K * T) ^ n / n.factorial * ‖x₀‖) :=
    (Real.summable_pow_div_factorial (K * T)).mul_right ‖x₀‖
  have hunif : TendstoUniformlyOn
      (fun (u : Finset ℕ) (p : Z × ℝ) => ∑ n ∈ u, picardIter (𝒜 p.1) x₀ n p.2)
      (fun p => ∑' n, picardIter (𝒜 p.1) x₀ n p.2) Filter.atTop
      (Set.univ ×ˢ Set.Icc (0 : ℝ) T) :=
    tendstoUniformlyOn_tsum hsum hbd
  refine hunif.continuousOn ?_
  exact (Filter.Eventually.of_forall
    (fun u => continuousOn_finsetSum u (fun n _ => (hiter_cont n).continuousOn))).frequently

/-- **Step 3 (i) — joint `(z,s)` continuity of the Dyson sum** (window / `ContinuousOn`-hypothesis
form).  Mirror of `picardSum_continuous_param_Icc`: clamp `s` into `[0,T]` (`projIcc`, L11) so the
global form applies, then transfer back by iterate-agreement on `[0,T]`. -/
lemma picardSum_continuous_param_Icc_joint
    {Z E : Type*} [TopologicalSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (𝒜 : Z → ℝ → (E →L[ℝ] E)) (x₀ : E) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (h𝒜_contOn : ContinuousOn (fun p : Z × ℝ => 𝒜 p.1 p.2) (Set.univ ×ˢ Set.Icc (0 : ℝ) T))
    (h𝒜_bound : ∀ z, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖𝒜 z s‖ ≤ K) :
    ContinuousOn (fun p : Z × ℝ => ∑' n, picardIter (𝒜 p.1) x₀ n p.2)
      (Set.univ ×ˢ Set.Icc (0 : ℝ) T) := by
  set cl : ℝ → ℝ := fun s => ↑(Set.projIcc 0 T hT s) with hcl
  have hcl_cont : Continuous cl := continuous_subtype_val.comp continuous_projIcc
  have hcl_mem : ∀ s, cl s ∈ Set.Icc (0 : ℝ) T := fun s => (Set.projIcc 0 T hT s).2
  have hcl_eq : ∀ s ∈ Set.Icc (0 : ℝ) T, cl s = s := by
    intro s hs; change (↑(Set.projIcc 0 T hT s) : ℝ) = s; rw [Set.projIcc_of_mem hT hs]
  set 𝒜c : Z → ℝ → (E →L[ℝ] E) := fun z s => 𝒜 z (cl s) with h𝒜c
  have h𝒜c_cont : Continuous (fun p : Z × ℝ => 𝒜c p.1 p.2) := by
    have hmap : Continuous (fun p : Z × ℝ => ((p.1, cl p.2) : Z × ℝ)) :=
      continuous_fst.prodMk (hcl_cont.comp continuous_snd)
    have hmem : ∀ p : Z × ℝ, ((p.1, cl p.2) : Z × ℝ) ∈ Set.univ ×ˢ Set.Icc (0 : ℝ) T :=
      fun p => ⟨Set.mem_univ _, hcl_mem p.2⟩
    exact h𝒜_contOn.comp_continuous hmap hmem
  have h𝒜c_bound : ∀ z, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖𝒜c z s‖ ≤ K :=
    fun z s _ => h𝒜_bound z (cl s) (hcl_mem s)
  have hagree : ∀ (n : ℕ) (z : Z), ∀ s ∈ Set.Icc (0 : ℝ) T,
      picardIter (𝒜c z) x₀ n s = picardIter (𝒜 z) x₀ n s := by
    intro n
    induction n with
    | zero => intro z s _; simp
    | succ n ih =>
      intro z s hs
      simp only [picardIter_succ]
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      have huIcc : u ∈ Set.Icc (0 : ℝ) T := by
        rw [Set.uIcc_of_le hs.1] at hu; exact ⟨hu.1, le_trans hu.2 hs.2⟩
      have e1 : 𝒜c z u = 𝒜 z u := by simp only [h𝒜c, hcl_eq u huIcc]
      rw [e1, ih z u huIcc]
  have key := picardSum_continuous_param_joint 𝒜c x₀ T hT K hK h𝒜c_cont h𝒜c_bound
  refine key.congr ?_
  rintro ⟨z, s⟩ ⟨_, hs⟩
  simp only
  congr 1; funext n; exact (hagree n z s hs).symm

/-- **Step 3 (i) — the fundamental matrix is jointly `(z,s)`-continuous.**  Joint companion of
`fundamentalMatrix_continuous_param`; specialises `picardSum_continuous_param_Icc_joint` to
`𝒜 := compL∘A`, `x₀ := id`.  This is the partial-`z`-derivative continuity input to the joint
`C¹`-ness of the forward flow `(s,z) ↦ Φ_s z` (Step 3 (iii)). -/
lemma fundamentalMatrix_continuous_param_joint
    {Z F : Type*} [TopologicalSpace Z] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : Z → ℝ → (F →L[ℝ] F)) (T : ℝ) (hT : 0 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (hA_contOn : ContinuousOn (fun p : Z × ℝ => A p.1 p.2) (Set.univ ×ˢ Set.Icc (0 : ℝ) T))
    (hA_bound : ∀ z, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖A z s‖ ≤ K) :
    ContinuousOn (fun p : Z × ℝ => fundamentalMatrix (A p.1) p.2)
      (Set.univ ×ˢ Set.Icc (0 : ℝ) T) := by
  have h𝒜_contOn : ContinuousOn
      (fun p : Z × ℝ => ContinuousLinearMap.compL ℝ F F F (A p.1 p.2))
      (Set.univ ×ˢ Set.Icc (0 : ℝ) T) :=
    (ContinuousLinearMap.compL ℝ F F F).continuous.comp_continuousOn hA_contOn
  have h𝒜_bound : ∀ z, ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖ContinuousLinearMap.compL ℝ F F F (A z s)‖ ≤ K := by
    intro z s hs
    refine le_trans ?_ (hA_bound z s hs)
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun g => ?_)
    rw [ContinuousLinearMap.compL_apply]
    exact (A z s).opNorm_comp_le g
  exact picardSum_continuous_param_Icc_joint
    (fun z s => ContinuousLinearMap.compL ℝ F F F (A z s))
    (ContinuousLinearMap.id ℝ F) T hT K hK h𝒜_contOn h𝒜_bound

section CharFlowDeriv
open Filter Topology

/-- Generic Grönwall difference-quotient bound (open-interval ODE + `s₀→0⁺` limit).  Two curves
`uh, mh` that approximately solve the same linear ODE `w' = vlin·w` on `Ioo 0 T` from the same datum
(`uh 0 = mh 0`), with `mh` exact and `uh`'s defect uniformly `≤ εf`, satisfy
`dist (uh t) (mh t) ≤ gronwallBound 0 K εf t`.  `vlin` is abstract (kept opaque to avoid unfolding
the heavy `vlasovFieldJacobian` integral in the Grönwall application). -/
lemma gronwall_diffQuotient_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (vlin : ℝ → (E →L[ℝ] E)) (K : NNReal) (hvlin_lip : ∀ s, LipschitzWith K (vlin s))
    (uh mh Fuh : ℝ → E) (εf : ℝ) (T t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (huh_cont : ContinuousOn uh (Set.Icc 0 T)) (hmh_cont : ContinuousOn mh (Set.Icc 0 T))
    (huh_deriv : ∀ s ∈ Set.Ioo (0 : ℝ) T, HasDerivAt uh (Fuh s) s)
    (hmh_deriv : ∀ s ∈ Set.Ioo (0 : ℝ) T, HasDerivAt mh ((vlin s) (mh s)) s)
    (hdefect : ∀ s ∈ Set.Ioo (0 : ℝ) T, dist (Fuh s) (vlin s (uh s)) ≤ εf)
    (h0 : uh 0 = mh 0) :
    dist (uh t) (mh t) ≤ gronwallBound 0 (K:ℝ) εf t := by
  have hbound_s0 : ∀ s₀ ∈ Set.Ioo (0 : ℝ) t,
      dist (uh t) (mh t) ≤ gronwallBound (dist (uh s₀) (mh s₀)) (K:ℝ) εf (t - s₀) := by
    intro s₀ hs₀
    have hIco_sub : Set.Ico s₀ t ⊆ Set.Ioo 0 T := fun s hs =>
      ⟨lt_of_lt_of_le hs₀.1 hs.1, hs.2.trans ht.2⟩
    have hIcc_sub : Set.Icc s₀ t ⊆ Set.Icc 0 T := fun s hs =>
      ⟨le_trans hs₀.1.le hs.1, le_trans hs.2 ht.2.le⟩
    have key := dist_le_of_approx_trajectories_ODE (K := K)
      (εf := εf) (εg := 0) (δ := dist (uh s₀) (mh s₀))
      hvlin_lip (huh_cont.mono hIcc_sub)
      (fun s hs => (huh_deriv s (hIco_sub hs)).hasDerivWithinAt)
      (fun s hs => hdefect s (hIco_sub hs))
      (hmh_cont.mono hIcc_sub)
      (fun s hs => (hmh_deriv s (hIco_sub hs)).hasDerivWithinAt)
      (fun s _ => le_of_eq (dist_self _)) (le_refl _)
    have hkey := key t ⟨hs₀.2.le, le_refl t⟩
    simpa only [add_zero] using hkey
  have : (𝓝[Set.Ioo 0 t] (0 : ℝ)).NeBot := left_nhdsWithin_Ioo_neBot ht.1
  have hT0 : (0 : ℝ) ≤ T := le_trans ht.1.le ht.2.le
  have hsub_Icc : Set.Ioo (0 : ℝ) t ⊆ Set.Icc 0 T := fun s hs => ⟨hs.1.le, le_trans hs.2.le ht.2.le⟩
  have htend_uh : Tendsto uh (𝓝[Set.Ioo 0 t] 0) (𝓝 (uh 0)) :=
    (huh_cont 0 ⟨le_refl 0, hT0⟩).tendsto.mono_left (nhdsWithin_mono 0 hsub_Icc)
  have htend_mh : Tendsto mh (𝓝[Set.Ioo 0 t] 0) (𝓝 (mh 0)) :=
    (hmh_cont 0 ⟨le_refl 0, hT0⟩).tendsto.mono_left (nhdsWithin_mono 0 hsub_Icc)
  have htend_δ : Tendsto (fun s₀ => dist (uh s₀) (mh s₀)) (𝓝[Set.Ioo 0 t] 0) (𝓝 0) := by
    have := htend_uh.dist htend_mh
    rwa [h0, dist_self] at this
  have htend_x : Tendsto (fun s₀ : ℝ => t - s₀) (𝓝[Set.Ioo 0 t] 0) (𝓝 t) := by
    have h0' : Tendsto (fun s₀ : ℝ => t - s₀) (𝓝 0) (𝓝 (t - 0)) :=
      (continuous_const.sub continuous_id).tendsto 0
    rw [sub_zero] at h0'; exact h0'.mono_left nhdsWithin_le_nhds
  have hgb_cont : Continuous (fun p : ℝ × ℝ => gronwallBound p.1 (K:ℝ) εf p.2) := by
    by_cases hK : (K:ℝ) = 0
    · simp only [hK, gronwallBound_K0]; fun_prop
    · have heq : (fun p : ℝ × ℝ => gronwallBound p.1 (K:ℝ) εf p.2)
          = fun p => p.1 * Real.exp ((K:ℝ) * p.2) + εf / (K:ℝ) * (Real.exp ((K:ℝ) * p.2) - 1) := by
        funext p; rw [gronwallBound_of_K_ne_0 hK]
      rw [heq]; fun_prop
  have htend_gb : Tendsto (fun s₀ => gronwallBound (dist (uh s₀) (mh s₀)) (K:ℝ) εf (t - s₀))
      (𝓝[Set.Ioo 0 t] 0) (𝓝 (gronwallBound 0 (K:ℝ) εf t)) :=
    (hgb_cont.tendsto (0, t)).comp (htend_δ.prodMk_nhds htend_x)
  exact ge_of_tendsto htend_gb (eventually_nhdsWithin_of_forall (fun s₀ hs₀ => hbound_s0 s₀ hs₀))

omit [NeZero d] in
/-- **C3 D1 — the difference-quotient heart of the variational equation.**

Given the fundamental matrix `Mz` of the linear variational ODE `M' = A(s, Φ_s z)·M`, `M 0 = id`
(coefficient `A = vlasovFieldJacobian`), the time-`t` flow map `w ↦ (charX t w, charV t w)` is
Fréchet-differentiable **at the fixed point `z`** with derivative exactly `Mz t`.

This is the load-bearing difference-quotient estimate `Φ_t(z+h) − Φ_t(z) − Mz t·h = o(‖h‖)`.
The matrix is threaded as an explicit hypothesis (rather than `choose`-d) so the proof can use its
ODE/continuity data directly.

**Proof plan (route b — Grönwall on the linearisation remainder).**  Reduce via
`hasFDerivAt_iff_isLittleO_nhds_zero` + `Asymptotics.isLittleO_iff` to: `∀ c>0, ∀ᶠ h, ‖Φ_t(z+h) −
Φ_t(z) − Mz t·h‖ ≤ c‖h‖`.  For fixed small `h`, the two curves `u_h(s) := Φ_s(z+h) − Φ_s(z)`
(approximate) and `m_h(s) := Mz s·h` (exact) both solve `w' = A(s, Φ_s z)·w` from the same datum
`h` (`Φ_0 = id`, `Mz 0 = id`):
* `m_h` is exact — its defect is `0` (its derivative `(A·Mz)(s)·h = A(s)·m_h(s)` by `hMzderiv` +
  `HasDerivWithinAt.clm_apply`).
* `u_h`'s defect is the Taylor remainder `R(s, Φ_s(z+h))`, bounded by `η·‖u_h(s)‖` (D1a,
  `vlasovField_taylorRemainder_uniform`) once `‖u_h(s)‖ ≤ δ(η)`, which holds with
  `‖u_h(s)‖ ≤ exp(K T)·‖h‖` (flow Lipschitz-in-`z`, `charFlow_lipschitzInZ_via_gronwall_Ioo`) for
  `‖h‖` small.  So `εf = η·exp(K T)·‖h‖`, uniform in `s`.
The frozen field's two-sided ODE holds only on `Ioo 0 T`, so apply
`dist_le_of_approx_trajectories_ODE` on `[s₀, t]` (`s₀ ∈ Ioo 0 t`) and take `s₀ → 0⁺` (the initial
defect `dist(u_h s₀, m_h s₀) → 0` by continuity), giving `‖u_h t − m_h t‖ ≤ gronwallBound 0 K εf t =
εf·(exp(K t)−1)/K`.  Since `η` is arbitrary this is `o(‖h‖)`.  `K := max 1 L` is the uniform field
Lipschitz constant; `‖A(s,·)‖ ≤ K` via `norm_fderiv_le_of_lipschitz`.  (`hcontIcc` is universal in
the initial point because the `s₀→0⁺` limit needs continuity of `Φ_·(z+h)`, M2.) -/
theorem charFlow_hasFDerivAt_of_fundamentalMatrix
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 < T)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (z : PhaseSpace d)
    (hcontIcc : ∀ z' : PhaseSpace d,
      ContinuousOn (fun s => (charX s z', charV s z')) (Set.Icc (0 : ℝ) T))
    (Mz : ℝ → (PhaseSpace d →L[ℝ] PhaseSpace d))
    (hMz0 : Mz 0 = ContinuousLinearMap.id ℝ (PhaseSpace d))
    (hMzcont : ContinuousOn Mz (Set.Icc 0 T))
    (hMzderiv : ∀ s ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt Mz
        ((vlasovFieldJacobian gradW ρ (s, (charX s z, charV s z))).comp (Mz s))
        (Set.Icc 0 T) s) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, HasFDerivAt (fun w => (charX t w, charV t w)) (Mz t) z := by
  intro t ht
  set Kr : ℝ := ((max 1 L : NNReal) : ℝ) with hKr
  have hKr1 : (1:ℝ) ≤ Kr := by rw [hKr]; exact_mod_cast le_max_left 1 L
  have hKrpos : (0 : ℝ) < Kr := lt_of_lt_of_le one_pos hKr1
  set Φ : ℝ → PhaseSpace d := fun s => (charX s z, charV s z) with hΦ
  have hF2 : ∀ s (w : PhaseSpace d),
      HasFDerivAt (vlasovVectorField gradW ρ s) (vlasovFieldJacobian gradW ρ (s, w)) w :=
    fun s w => vlasovVectorField_hasFDerivAt_in_z gradW hgradW_C1 L hL ρ h_int s w
  have hVF_lip : ∀ s, LipschitzWith (max 1 L) (vlasovVectorField gradW ρ s) := fun s =>
    vlasovVectorField_lipschitzWith gradW L hL ρ h_int s
  set vlin : ℝ → (PhaseSpace d →L[ℝ] PhaseSpace d) := fun s => vlasovFieldJacobian gradW ρ (s, Φ s)
    with hvlin
  have hvlin_norm : ∀ s, ‖vlin s‖ ≤ Kr := by
    intro s
    change ‖vlasovFieldJacobian gradW ρ (s, Φ s)‖ ≤ Kr
    rw [← (hF2 s (Φ s)).fderiv]
    exact norm_fderiv_le_of_lipschitz ℝ (hVF_lip s)
  have hvlin_lip : ∀ s, LipschitzWith (max 1 L) (vlin s) := by
    intro s
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    calc ‖vlin s (x - y)‖ ≤ ‖vlin s‖ * ‖x - y‖ := (vlin s).le_opNorm _
      _ ≤ Kr * ‖x - y‖ := by gcongr; exact hvlin_norm s
  clear_value vlin
  have h_init : ∀ z' : PhaseSpace d, (charX 0 z', charV 0 z') = z' := fun z' =>
    Prod.ext_iff.mpr ⟨(hflow.1 z' (Set.mem_univ z')).1, (hflow.1 z' (Set.mem_univ z')).2⟩
  have h_derivAt : ∀ z', ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun s => (charX s z', charV s z'))
        (vlasovVectorField gradW ρ s (charX s z', charV s z')) s := fun z' s hs =>
    HasDerivAt.prodMk (hflow.2.1 s hs z' (Set.mem_univ z')) (hflow.2.2 s hs z' (Set.mem_univ z'))
  have hgron := charFlow_lipschitzInZ_via_gronwall_Ioo gradW L hL ρ h_int charX charV T hT.le
    h_init hcontIcc (fun z' s hs => (h_derivAt z' s hs).hasDerivWithinAt)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  set Cexp : ℝ := Real.exp (Kr * T) with hCexp
  have hCexp_pos : 0 < Cexp := Real.exp_pos _
  set Cgron : ℝ := (Real.exp (Kr * t) - 1) / Kr with hCgron
  have hCgron_nonneg : 0 ≤ Cgron := by
    rw [hCgron]; apply div_nonneg _ hKrpos.le
    simp only [sub_nonneg]; exact Real.one_le_exp (mul_nonneg hKrpos.le ht.1.le)
  set G : ℝ := Cexp * Cgron with hG
  have hG_nonneg : 0 ≤ G := mul_nonneg hCexp_pos.le hCgron_nonneg
  set η : ℝ := c / (G + 1) with hη
  have hη_pos : 0 < η := by rw [hη]; positivity
  obtain ⟨δη, hδη_pos, hδη⟩ := vlasovField_taylorRemainder_uniform gradW hgradW_C1 L hL ρ h_int
    charX charV T z (hcontIcc z) hρD_cont η hη_pos
  refine Metric.eventually_nhds_iff.mpr
    ⟨δη / (Cexp + 1), div_pos hδη_pos (by linarith [hCexp_pos]), ?_⟩
  intro h hh
  rw [dist_zero_right] at hh
  have hCexph : Cexp * ‖h‖ ≤ δη := by
    have hle : ‖h‖ * (Cexp + 1) ≤ δη := by rw [← le_div_iff₀ (by linarith [hCexp_pos])]; exact hh.le
    nlinarith [norm_nonneg h, hCexp_pos, hle]
  set uh : ℝ → PhaseSpace d := fun s => (charX s (z + h), charV s (z + h)) - (charX s z, charV s z)
    with huh
  set mh : ℝ → PhaseSpace d := fun s => (Mz s) h with hmh
  set εf : ℝ := η * Cexp * ‖h‖ with hεf
  have huh_cont : ContinuousOn uh (Set.Icc 0 T) := (hcontIcc (z + h)).sub (hcontIcc z)
  have hmh_cont : ContinuousOn mh (Set.Icc 0 T) := hMzcont.clm_apply continuousOn_const
  have huh_bound : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖uh s‖ ≤ Cexp * ‖h‖ := by
    intro s hs
    change ‖(charX s (z + h), charV s (z + h)) - (charX s z, charV s z)‖ ≤ Cexp * ‖h‖
    rw [← dist_eq_norm]
    calc dist ((charX s (z + h), charV s (z + h)) : PhaseSpace d) (charX s z, charV s z)
        ≤ dist (z + h) z * Real.exp (Kr * (s - 0)) := hgron s hs (z + h) z
      _ = ‖h‖ * Real.exp (Kr * s) := by rw [dist_eq_norm, add_sub_cancel_left, sub_zero]
      _ ≤ ‖h‖ * Cexp := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg h)
          rw [hCexp]; exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 hKrpos.le)
      _ = Cexp * ‖h‖ := mul_comm _ _
  have huh_derivAt : ∀ s ∈ Set.Ioo (0 : ℝ) T, HasDerivAt uh
      (vlasovVectorField gradW ρ s (charX s (z + h), charV s (z + h))
        - vlasovVectorField gradW ρ s (charX s z, charV s z)) s := fun s hs =>
    (h_derivAt (z + h) s hs).sub (h_derivAt z s hs)
  have hmh_derivAt : ∀ s ∈ Set.Ioo (0 : ℝ) T, HasDerivAt mh ((vlin s) (mh s)) s := by
    intro s hs
    have hMz_at : HasDerivAt Mz ((vlin s).comp (Mz s)) s := by
      simp only [hvlin]
      exact (hMzderiv s (Set.Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
    have hck := hMz_at.clm_apply (hasDerivAt_const s h)
    simpa only [ContinuousLinearMap.comp_apply, map_zero, add_zero] using hck
  have hdefect : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      dist (vlasovVectorField gradW ρ s (charX s (z + h), charV s (z + h))
        - vlasovVectorField gradW ρ s (charX s z, charV s z)) (vlin s (uh s)) ≤ εf := by
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) T := Set.Ioo_subset_Icc_self hs
    have huhs_le : ‖uh s‖ ≤ δη := le_trans (huh_bound s hsIcc) hCexph
    have hR := hδη s hsIcc (charX s (z + h), charV s (z + h)) huhs_le
    rw [dist_eq_norm]; simp only [hvlin]
    calc ‖vlasovVectorField gradW ρ s (charX s (z + h), charV s (z + h))
            - vlasovVectorField gradW ρ s (charX s z, charV s z)
            - vlasovFieldJacobian gradW ρ (s, Φ s) (uh s)‖
        ≤ η * ‖uh s‖ := hR
      _ ≤ η * (Cexp * ‖h‖) := mul_le_mul_of_nonneg_left (huh_bound s hsIcc) hη_pos.le
      _ = εf := by rw [hεf]; ring
  have huh0 : uh 0 = h := by
    change (charX 0 (z + h), charV 0 (z + h)) - (charX 0 z, charV 0 z) = h
    rw [h_init (z + h), h_init z, add_sub_cancel_left]
  have hmh0 : mh 0 = h := by change (Mz 0) h = h; rw [hMz0]; rfl
  have hlim : dist (uh t) (mh t) ≤ gronwallBound 0 Kr εf t := by
    have := gronwall_diffQuotient_bound vlin (max 1 L) hvlin_lip uh mh
      (fun s => vlasovVectorField gradW ρ s (charX s (z + h), charV s (z + h))
        - vlasovVectorField gradW ρ s (charX s z, charV s z)) εf T t ht
      huh_cont hmh_cont huh_derivAt hmh_derivAt hdefect (huh0.trans hmh0.symm)
    rwa [← hKr] at this
  have hgb_val : gronwallBound 0 Kr εf t = εf * Cgron := by
    rw [gronwallBound_of_K_ne_0 hKrpos.ne']; simp only [zero_mul, zero_add]; rw [hCgron]; ring
  have hηG : η * G ≤ c := by
    rw [hη]; rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith [hG_nonneg] : (0 : ℝ) < G + 1)]
    nlinarith [hG_nonneg, hc.le]
  change ‖(charX t (z + h), charV t (z + h)) - (charX t z, charV t z) - (Mz t) h‖ ≤ c * ‖h‖
  rw [show (charX t (z + h), charV t (z + h)) - (charX t z, charV t z) - (Mz t) h
      = uh t - mh t from rfl, ← dist_eq_norm]
  calc dist (uh t) (mh t)
      ≤ gronwallBound 0 Kr εf t := hlim
    _ = εf * Cgron := hgb_val
    _ = η * G * ‖h‖ := by rw [hεf, hG]; ring
    _ ≤ c * ‖h‖ := mul_le_mul_of_nonneg_right hηG (norm_nonneg h)

end CharFlowDeriv

omit [NeZero d] in
/-- **C3 #3 — the variational equation (`HasFDerivAt` of the flow in its initial point).**

For the frozen field `b(t,·) = vlasovVectorField gradW ρ t` with `gradW ∈ C¹` (supplied by the
consumer via `assW2_contDiff_gradW`), the time-`t` characteristic map
`z ↦ (charX t z, charV t z)` is Fréchet-differentiable in the initial point `z`, with a derivative
`Dflow t z` that is continuous in `z` (so the flow map is `C¹` in `z`).  The derivative solves the
linear matrix variational ODE `M' = (D_z b(t, Φ_t z)) · M`, `M_0 = id`.

**This was the load-bearing research gap** — Mathlib has no C¹-dependence-of-an-ODE-flow-on-its-
initial-condition lemma — now proven (axiom-clean) via route (b)
(`charFlow_lipschitzInZ_via_gronwall_Ioo`, `CharacteristicFlow.lean`, is the Lipschitz-in-`z`
scaffold; Mathlib Gronwall + the vendored `IsPicardLindelof` confinement are the analytic inputs):
3.1 existence/uniqueness of the continuous matrix solution `M_t(z)` of the variational ODE
(`fundamentalMatrix`); 3.2 joint `(t,z)` continuity of `M` (`fundamentalMatrix_continuous_param`);
3.3 the difference-quotient estimate `Φ_t(z+h) − Φ_t(z) − M_t(z)·h = o(‖h‖)` uniformly on compacts
(Gronwall on the linearization remainder, using `gradW ∈ C¹`,
`charFlow_hasFDerivAt_of_fundamentalMatrix`); 3.4 assembled into `HasFDerivAt`.

The `HasFDerivAt`/continuity *conclusion* is route-independent, so this interface is stable; the
universal-`t` probability instance + force-integrability `h_int` are the field-regularity inputs
the proof consumes (the window-only application clamps, L11, at the grind).

**`hρD_cont` (joint continuity of the convolution-derivative field).**  This is the regularity that
makes the variational coefficient `A(s,z) = D_z b(s, Φ_s z)` continuous in `s` — its only non-flow
varying part is `D_x conv(ρ_s)(x) = ∫ fderiv gradW (x − y) ∂ρ_s`, evaluated at the *moving* point
`Φ_s z`, so per-`x` continuity is not enough; joint `(s,x)`-continuity is needed.  Note the
asymmetry with the *field*: `∫ gradW(x−y) dρ_s` gets joint continuity for free (per-`x` continuity
+ uniform Lipschitz-in-`x`, `convolveFunctionMeasure_lipschitz_in_x`), but the *derivative* field is
NOT uniformly Lipschitz in `x` (that needs `W ∈ C³`; `AssW2` gives only `C²`), so its joint
continuity must be supplied.

**Option-B note (running — eventual extension).**  `hρD_cont` is, in the complete theory, NOT a new
assumption: it is *derivable* from **narrow continuity of `s ↦ ρ_s`** (since `fderiv gradW` is
bounded continuous, `‖·‖ ≤ L`), which is in turn derivable from `IsVlasovSolutionOn` + tightness
(the uniform moment bound) via the standard **"`C_c^∞`-continuity + tight ⟹ narrow-continuity"**
upgrade — a self-contained measure-theory lemma not yet in the codebase.  We thread it as a
hypothesis (Option A) to unblock the variational-equation grind; folding it into a derived fact
(so the bridge assumes only the weak solution + moments) is the **Option-B extension**, tracked as
a follow-up. -/
theorem charFlow_hasFDerivAt_in_initialPoint
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 < T)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (hcontIcc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T)) :
    ∃ Dflow : ℝ → PhaseSpace d → (PhaseSpace d →L[ℝ] PhaseSpace d),
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ z : PhaseSpace d,
        HasFDerivAt (fun w => (charX t w, charV t w)) (Dflow t z) z) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, Continuous (Dflow t)) := by
  -- **Reduction (Route A — explicit fundamental matrix, lesson L14).**  `M z := fundamentalMatrix
  -- (A z)` with `A z s := vlasovFieldJacobian gradW ρ (s, Φ_s z)`; its ODE/continuity
  -- data come from
  -- `fundamentalMatrix_spec` (feeds D1), and `z ↦ M z t` continuity (V2) from
  -- `fundamentalMatrix_continuous_param` — the parameter-regularity an existential
  -- `choose` could not
  -- supply.  `Dflow t z := fundamentalMatrix (A z) t`.
  set A : PhaseSpace d → ℝ → (PhaseSpace d →L[ℝ] PhaseSpace d) :=
    fun z s => vlasovFieldJacobian gradW ρ (s, (charX s z, charV s z)) with hA_def
  have hAcont : ∀ z : PhaseSpace d, ContinuousOn (A z) (Set.Icc 0 T) := fun z =>
    vlasovVariationalCoeff_continuousOn gradW ρ charX charV T z (hcontIcc z) hρD_cont
  refine ⟨fun t z => fundamentalMatrix (A z) t, ?_, ?_⟩
  · -- **D1** — `charFlow_hasFDerivAt_of_fundamentalMatrix` fed by `fundamentalMatrix_spec`.
    intro t ht z
    obtain ⟨h0, hcont, hderiv⟩ := fundamentalMatrix_spec (A z) T hT.le (hAcont z)
    exact charFlow_hasFDerivAt_of_fundamentalMatrix gradW hgradW_C1 L hL ρ charX charV T hT hflow
      h_int hρD_cont z hcontIcc (fundamentalMatrix (A z)) h0 hcont hderiv t ht
  · -- **V2** — `fundamentalMatrix_continuous_param`: flow joint continuity ⇒ `A` jointly continuous
    -- ⇒ `z ↦ M z t` continuous.
    intro t ht
    -- Flow joint continuity `(z,s) ↦ Φ_s z` on `univ ×ˢ Icc 0 T` (Grönwall Lipschitz-in-`z` from
    -- `hflow` + per-`z` continuity in `s`).
    have h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z := fun z =>
      Prod.ext_iff.mpr ⟨(hflow.1 z (Set.mem_univ z)).1, (hflow.1 z (Set.mem_univ z)).2⟩
    have h_deriv : ∀ z, ∀ s ∈ Set.Ioo (0 : ℝ) T,
        HasDerivWithinAt (fun s => (charX s z, charV s z))
          (vlasovVectorField gradW ρ s (charX s z, charV s z)) (Set.Ici s) s := fun z s hs =>
      (HasDerivAt.prodMk (hflow.2.1 s hs z (Set.mem_univ z))
        (hflow.2.2 s hs z (Set.mem_univ z))).hasDerivWithinAt
    have hgron := charFlow_lipschitzInZ_via_gronwall_Ioo gradW L hL ρ h_int charX charV T hT.le
      h_init hcontIcc h_deriv
    have hflowjoint : ContinuousOn
        (fun p : PhaseSpace d × ℝ => (charX p.2 p.1, charV p.2 p.1)) (Set.univ ×ˢ Set.Icc 0 T) := by
      refine continuousOn_prod_of_lipschitz_continuousOn (fun z s => (charX s z, charV s z)) T
        (Real.exp (((max 1 L : NNReal) : ℝ) * T)) (fun s hs z₁ z₂ => ?_) hcontIcc
      calc dist ((charX s z₁, charV s z₁) : PhaseSpace d) (charX s z₂, charV s z₂)
          ≤ dist z₁ z₂ * Real.exp (((max 1 L : NNReal) : ℝ) * (s - 0)) := hgron s hs z₁ z₂
        _ = Real.exp (((max 1 L : NNReal) : ℝ) * (s - 0)) * dist z₁ z₂ := by ring
        _ ≤ Real.exp (((max 1 L : NNReal) : ℝ) * T) * dist z₁ z₂ := by
            refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) dist_nonneg
            have hsT : s - 0 ≤ T := by simp only [sub_zero]; exact hs.2
            exact mul_le_mul_of_nonneg_left hsT (by positivity)
    -- `A` jointly continuous (Jacobian along the flow) and uniformly bounded by `max 1 L`.
    have hg : ContinuousOn
        (fun p : PhaseSpace d × ℝ => ((p.2, (charX p.2 p.1, charV p.2 p.1)) : ℝ × PhaseSpace d))
        (Set.univ ×ˢ Set.Icc 0 T) := continuousOn_snd.prodMk hflowjoint
    have hmapsg : Set.MapsTo
        (fun p : PhaseSpace d × ℝ => ((p.2, (charX p.2 p.1, charV p.2 p.1)) : ℝ × PhaseSpace d))
        (Set.univ ×ˢ Set.Icc 0 T) (Set.Icc 0 T ×ˢ Set.univ) := fun p hp => ⟨hp.2, Set.mem_univ _⟩
    have hA_contOn : ContinuousOn (fun p : PhaseSpace d × ℝ => A p.1 p.2)
        (Set.univ ×ˢ Set.Icc 0 T) :=
      (vlasovFieldJacobian_continuousOn gradW ρ T hρD_cont).comp hg hmapsg
    have hA_bound : ∀ z, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖A z s‖ ≤ ((max 1 L : NNReal) : ℝ) := by
      intro z s _
      have heq : A z s = fderiv ℝ (vlasovVectorField gradW ρ s) (charX s z, charV s z) := by
        simp only [hA_def]
        exact (vlasovVectorField_hasFDerivAt_in_z gradW hgradW_C1 L hL ρ h_int s
          (charX s z, charV s z)).fderiv.symm
      rw [heq]
      exact norm_fderiv_le_of_lipschitz ℝ (vlasovVectorField_lipschitzWith gradW L hL ρ h_int s)
    exact fundamentalMatrix_continuous_param A T hT.le ((max 1 L : NNReal) : ℝ) (by positivity)
      hA_contOn hA_bound t (Set.Ioo_subset_Icc_self ht)

open Filter Topology in
omit [NeZero d] in
/-- **Step 1 (dual core) — lower Grönwall / anti-Lipschitz bound on the characteristic flow.**
For `t ∈ (0,T)`, the flow `Φ_t : z ↦ (charX t z, charV t z)` satisfies
`dist z₁ z₂ ≤ dist (Φ_t z₁) (Φ_t z₂) · exp(K t)` (K = max 1 L), i.e. `Φ_t` is `AntilipschitzWith`.
This is the keystone of the two-time-flow inverse construction (Step 2): bi-Lipschitz makes `Φ_t`
injective with closed range and `M_t = DΦ_t` invertible (no Liouville needed).

Proof: time-reverse the two trajectories on each `[s₀,t] ⊆ (0,T)` (so they solve
`w' = −b_{s₀+t−r}(w)`, still K-Lipschitz) and apply the existing forward
`dist_le_of_trajectories_ODE`; take `s₀→0⁺`.  `h_deriv2` is the two-sided `HasDerivAt` on the open
interval, supplied by `IsCharacteristicFlowOn`. -/
theorem charFlow_antilipschitzInZ_via_gronwall_Ioo
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ)
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z, ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv2 : ∀ z, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z)) s) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
      dist z₁ z₂ ≤
        dist ((charX t z₁, charV t z₁) : PhaseSpace d) (charX t z₂, charV t z₂)
          * Real.exp (((max 1 L : NNReal) : ℝ) * (t - 0)) := by
  intro t ht z₁ z₂
  set K : NNReal := max 1 L with hK_def
  have h_vf_lip : ∀ s, LipschitzWith K (vlasovVectorField gradW ρ s) := fun s =>
    vlasovVectorField_lipschitzWith gradW L hL ρ h_int s
  set F : ℝ → PhaseSpace d := fun s => (charX s z₁, charV s z₁) with hF_def
  set G : ℝ → PhaseSpace d := fun s => (charX s z₂, charV s z₂) with hG_def
  -- Per-`s₀` antilipschitz bound on `[s₀, t]`.
  have h_perS0 : ∀ s₀ ∈ Set.Ioo (0 : ℝ) t,
      dist (F s₀) (G s₀) ≤ dist (F t) (G t) * Real.exp ((K : ℝ) * (t - s₀)) := by
    intro s₀ hs₀
    have hsub_Ioo : Set.Icc s₀ t ⊆ Set.Ioo (0 : ℝ) T := fun r hr =>
      ⟨lt_of_lt_of_le hs₀.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
    have hsub_Icc : Set.Icc s₀ t ⊆ Set.Icc (0 : ℝ) T := fun r hr =>
      ⟨le_of_lt (lt_of_lt_of_le hs₀.1 hr.1), le_of_lt (lt_of_le_of_lt hr.2 ht.2)⟩
    have hrefl_mem : ∀ r ∈ Set.Icc s₀ t, s₀ + t - r ∈ Set.Icc s₀ t := by
      intro r hr; exact ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have hrefl_cont : ContinuousOn (fun r : ℝ => s₀ + t - r) (Set.Icc s₀ t) :=
      (continuous_const.sub continuous_id).continuousOn
    set vr : ℝ → PhaseSpace d → PhaseSpace d :=
      fun r w => -(vlasovVectorField gradW ρ (s₀ + t - r) w) with hvr_def
    have hvr_lip : ∀ r, LipschitzWith K (vr r) := fun r => (h_vf_lip (s₀ + t - r)).neg
    have hFr_cont : ContinuousOn (fun r => F (s₀ + t - r)) (Set.Icc s₀ t) :=
      (h_cont_Icc z₁).comp hrefl_cont (fun r hr => hsub_Icc (hrefl_mem r hr))
    have hGr_cont : ContinuousOn (fun r => G (s₀ + t - r)) (Set.Icc s₀ t) :=
      (h_cont_Icc z₂).comp hrefl_cont (fun r hr => hsub_Icc (hrefl_mem r hr))
    have hFr' : ∀ r ∈ Set.Ico s₀ t,
        HasDerivWithinAt (fun r => F (s₀ + t - r)) (vr r (F (s₀ + t - r))) (Set.Ici r) r := by
      intro r hr
      have hrIoo : s₀ + t - r ∈ Set.Ioo (0 : ℝ) T :=
        hsub_Ioo ⟨by linarith [hr.2], by linarith [hr.1]⟩
      have hlin : HasDerivAt (fun r : ℝ => s₀ + t - r) (-1) r := by
        simpa using (hasDerivAt_id r).const_sub (s₀ + t)
      have key : HasDerivAt (fun r => F (s₀ + t - r))
          ((-1 : ℝ) • vlasovVectorField gradW ρ (s₀ + t - r) (F (s₀ + t - r))) r :=
        HasDerivAt.scomp_of_eq r (h_deriv2 z₁ (s₀ + t - r) hrIoo) hlin rfl
      simp only [neg_one_smul] at key
      exact key.hasDerivWithinAt
    have hGr' : ∀ r ∈ Set.Ico s₀ t,
        HasDerivWithinAt (fun r => G (s₀ + t - r)) (vr r (G (s₀ + t - r))) (Set.Ici r) r := by
      intro r hr
      have hrIoo : s₀ + t - r ∈ Set.Ioo (0 : ℝ) T :=
        hsub_Ioo ⟨by linarith [hr.2], by linarith [hr.1]⟩
      have hlin : HasDerivAt (fun r : ℝ => s₀ + t - r) (-1) r := by
        simpa using (hasDerivAt_id r).const_sub (s₀ + t)
      have key : HasDerivAt (fun r => G (s₀ + t - r))
          ((-1 : ℝ) • vlasovVectorField gradW ρ (s₀ + t - r) (G (s₀ + t - r))) r :=
        HasDerivAt.scomp_of_eq r (h_deriv2 z₂ (s₀ + t - r) hrIoo) hlin rfl
      simp only [neg_one_smul] at key
      exact key.hasDerivWithinAt
    have hgron := dist_le_of_trajectories_ODE hvr_lip hFr_cont hFr' hGr_cont hGr'
      (le_refl (dist (F (s₀ + t - s₀)) (G (s₀ + t - s₀)))) t ⟨hs₀.2.le, le_refl t⟩
    simp only [show s₀ + t - t = s₀ from by ring, show s₀ + t - s₀ = t from by ring] at hgron
    exact hgron
  -- `s₀ → 0⁺` limit.
  have hfilt : (nhdsWithin (0 : ℝ) (Set.Ioo 0 t)).NeBot := left_nhdsWithin_Ioo_neBot ht.1
  have hIoo_sub_Icc : Set.Ioo (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun s hs =>
    ⟨hs.1.le, le_of_lt (lt_trans hs.2 ht.2)⟩
  have h_tendsto_F : Tendsto F (nhdsWithin (0 : ℝ) (Set.Ioo 0 t)) (nhds z₁) := by
    have hcw : ContinuousWithinAt F (Set.Icc (0 : ℝ) T) 0 :=
      (h_cont_Icc z₁) 0 ⟨le_refl 0, le_of_lt (lt_trans ht.1 ht.2)⟩
    have h0 : Tendsto F (nhdsWithin (0 : ℝ) (Set.Icc 0 T)) (nhds (F 0)) := hcw
    rw [show F 0 = z₁ from h_init z₁] at h0
    exact h0.mono_left (nhdsWithin_mono 0 hIoo_sub_Icc)
  have h_tendsto_G : Tendsto G (nhdsWithin (0 : ℝ) (Set.Ioo 0 t)) (nhds z₂) := by
    have hcw : ContinuousWithinAt G (Set.Icc (0 : ℝ) T) 0 :=
      (h_cont_Icc z₂) 0 ⟨le_refl 0, le_of_lt (lt_trans ht.1 ht.2)⟩
    have h0 : Tendsto G (nhdsWithin (0 : ℝ) (Set.Icc 0 T)) (nhds (G 0)) := hcw
    rw [show G 0 = z₂ from h_init z₂] at h0
    exact h0.mono_left (nhdsWithin_mono 0 hIoo_sub_Icc)
  have h_tendsto_lhs : Tendsto (fun s₀ => dist (F s₀) (G s₀))
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 t)) (nhds (dist z₁ z₂)) :=
    h_tendsto_F.dist h_tendsto_G
  have h_tendsto_rhs : Tendsto (fun s₀ => dist (F t) (G t) * Real.exp ((K : ℝ) * (t - s₀)))
      (nhdsWithin (0 : ℝ) (Set.Ioo 0 t))
      (nhds (dist (F t) (G t) * Real.exp ((K : ℝ) * (t - 0)))) := by
    have hcont : Continuous (fun s₀ : ℝ => dist (F t) (G t) * Real.exp ((K : ℝ) * (t - s₀))) := by
      fun_prop
    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto h_tendsto_lhs h_tendsto_rhs
    (eventually_nhdsWithin_of_forall h_perS0)

section Step2Inverse
open Filter Topology

/-- **Step 2a (dual core, generic) — antilipschitz map ⇒ antilipschitz derivative.**
If `f` is antilipschitz and Fréchet-differentiable at `x`, its derivative `f'` is antilipschitz
(hence injective) with the same constant.  `f' u` is the limit of slopes `n•(f(x+n⁻¹•u)−f x)`, each
of norm `≥ ‖u‖/C` by antilipschitz; pass to the limit.  (Mathlib lacks this producer.) -/
theorem antilipschitzWith_fderiv_of_antilipschitz
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {f' : E →L[ℝ] F} {x : E} {C : NNReal}
    (hf : AntilipschitzWith C f) (hf' : HasFDerivAt f f' x) :
    AntilipschitzWith C f' := by
  refine AntilipschitzWith.of_le_mul_dist (fun v w => ?_)
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  set u := v - w with hu
  have hc : Tendsto (fun n : ℕ => ‖((n : ℝ))‖) atTop atTop := by
    simpa [Real.norm_natCast] using tendsto_natCast_atTop_atTop (R := ℝ)
  have hlim := hf'.lim u hc
  have hbd : ∀ᶠ n : ℕ in atTop,
      ‖u‖ ≤ (C : ℝ) * ‖(n : ℝ) • (f (x + ((n : ℝ))⁻¹ • u) - f x)‖ := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hd := hf.le_mul_dist (x + ((n : ℝ))⁻¹ • u) x
    rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_inv,
      Real.norm_natCast] at hd
    rw [norm_smul, Real.norm_natCast]
    calc ‖u‖ = (n : ℝ) * ((n : ℝ)⁻¹ * ‖u‖) := by
              rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hn0), one_mul]
      _ ≤ (n : ℝ) * ((C : ℝ) * ‖f (x + ((n : ℝ))⁻¹ • u) - f x‖) :=
              mul_le_mul_of_nonneg_left hd (le_of_lt hn0)
      _ = (C : ℝ) * ((n : ℝ) * ‖f (x + ((n : ℝ))⁻¹ • u) - f x‖) := by ring
  have hlim2 : Tendsto (fun n : ℕ => (C : ℝ) * ‖(n : ℝ) • (f (x + ((n : ℝ))⁻¹ • u) - f x)‖)
      atTop (𝓝 ((C : ℝ) * ‖f' u‖)) := hlim.norm.const_mul (C : ℝ)
  exact ge_of_tendsto hlim2 hbd

/-- **Step 2 (dual core, generic) — global `C¹` inverse of an antilipschitz `C¹` self-map.**
If `Φ : E → E` (finite-dim) is `C¹` (derivative `M z` at `z`), antilipschitz, and Lipschitz, then
each `M z` is invertible, `Φ` is bijective, and the global inverse `Ψ` is Lipschitz with
`HasFDerivAt Ψ (M (Ψ w))⁻¹ w`.  No Liouville/Hadamard: open range
(`isOpenMap_of_hasStrictFDerivAt_equiv`) + closed range (`AntilipschitzWith.isClosed_range`) ⇒
clopen ⇒ surjective; inverse derivative from `HasStrictFDerivAt.to_local_left_inverse`. -/
theorem exists_global_c1_inverse_of_antilipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Φ : E → E} {M : E → (E →L[ℝ] E)} {Ca Cl : NNReal}
    (hderiv : ∀ z, HasFDerivAt Φ (M z) z)
    (hM_cont : Continuous M)
    (hanti : AntilipschitzWith Ca Φ)
    (hlip : LipschitzWith Cl Φ) :
    ∃ (Ψ : E → E) (e : E → E ≃L[ℝ] E),
      (∀ z, ((e z : E →L[ℝ] E)) = M z) ∧
      Function.LeftInverse Ψ Φ ∧ Function.RightInverse Ψ Φ ∧
      LipschitzWith Ca Ψ ∧
      (∀ w, HasFDerivAt Ψ ((e (Ψ w)).symm : E →L[ℝ] E) w) := by
  classical
  have hMz_anti : ∀ z, AntilipschitzWith Ca (M z) := fun z =>
    antilipschitzWith_fderiv_of_antilipschitz hanti (hderiv z)
  have hker : ∀ z, LinearMap.ker (M z : E →ₗ[ℝ] E) = ⊥ := fun z =>
    LinearMap.ker_eq_bot.mpr (hMz_anti z).injective
  have hsurj_lin : ∀ z, LinearMap.range (M z : E →ₗ[ℝ] E) = ⊤ := fun z =>
    LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp (hMz_anti z).injective)
  set e : ∀ z, E ≃L[ℝ] E := fun z =>
    ContinuousLinearEquiv.ofBijective (M z) (hker z) (hsurj_lin z) with he_def
  have he_coe : ∀ z, ((e z : E →L[ℝ] E)) = M z := fun _ => rfl
  have hC1 : ContDiff ℝ 1 Φ := contDiff_one_iff_hasFDerivAt.mpr ⟨M, hM_cont, hderiv⟩
  have hstrict : ∀ z, HasStrictFDerivAt Φ ((e z : E →L[ℝ] E)) z := fun z => by
    rw [he_coe z]; exact hC1.contDiffAt.hasStrictFDerivAt' (hderiv z) (by norm_num)
  have hopen : IsOpenMap Φ := isOpenMap_of_hasStrictFDerivAt_equiv hstrict
  have hrange_open : IsOpen (Set.range Φ) := hopen.isOpen_range
  have hrange_closed : IsClosed (Set.range Φ) := hanti.isClosed_range hlip.uniformContinuous
  have hrange_univ : Set.range Φ = Set.univ :=
    IsClopen.eq_univ ⟨hrange_closed, hrange_open⟩ ⟨Φ 0, Set.mem_range_self 0⟩
  have hsurj : Function.Surjective Φ := Set.range_eq_univ.mp hrange_univ
  have hinj : Function.Injective Φ := hanti.injective
  set Ψ : E → E := Function.invFun Φ with hΨ_def
  have hLeft : Function.LeftInverse Ψ Φ := Function.leftInverse_invFun hinj
  have hRight : Function.RightInverse Ψ Φ := Function.rightInverse_invFun hsurj
  have hΨ_lip : LipschitzWith Ca Ψ := by
    refine LipschitzWith.of_dist_le_mul (fun w₁ w₂ => ?_)
    have h := hanti.le_mul_dist (Ψ w₁) (Ψ w₂)
    rwa [hRight w₁, hRight w₂] at h
  have hΨ_deriv : ∀ w, HasFDerivAt Ψ ((e (Ψ w)).symm : E →L[ℝ] E) w := by
    intro w
    have hz : Φ (Ψ w) = w := hRight w
    have hev : ∀ᶠ x in 𝓝 (Ψ w), Ψ (Φ x) = x := Filter.Eventually.of_forall hLeft
    have hsymm := (hstrict (Ψ w)).to_local_left_inverse hev
    rw [hz] at hsymm
    exact hsymm.hasFDerivAt
  exact ⟨Ψ, e, he_coe, hLeft, hRight, hΨ_lip, hΨ_deriv⟩

end Step2Inverse

omit [NeZero d] in
/-- **Step 2 (dual core) — the characteristic flow `Φ_t` is a `C¹` diffeomorphism on `(0,T)`.**
Instantiates the generic global-inverse machinery at `Φ_t := (charX t, charV t)`: its derivative
`e z` (= `#3`'s `Dflow t z`) is invertible, `Φ_t` is bijective, and the inverse `Ψ` is continuous
with `HasFDerivAt Ψ (e (Ψ w))⁻¹ w`.  `hanti` comes from Step 1
(`charFlow_antilipschitzInZ_via_gronwall_Ioo`), `hlip` from the existing upper Grönwall bound
(`charFlow_lipschitzInZ_via_gronwall_Ioo`), the derivative family from `#3`. -/
theorem exists_charFlow_inverse_On
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 < T)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (hcontIcc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T,
      ∃ (Ψ : PhaseSpace d → PhaseSpace d)
        (e : PhaseSpace d → (PhaseSpace d ≃L[ℝ] PhaseSpace d)),
        (∀ z, HasFDerivAt (fun w => (charX t w, charV t w))
          ((e z : PhaseSpace d →L[ℝ] PhaseSpace d)) z) ∧
        Function.LeftInverse Ψ (fun z => (charX t z, charV t z)) ∧
        Function.RightInverse Ψ (fun z => (charX t z, charV t z)) ∧
        Continuous Ψ ∧
        (∀ w, HasFDerivAt Ψ ((e (Ψ w)).symm : PhaseSpace d →L[ℝ] PhaseSpace d) w) := by
  have h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z := fun z =>
    Prod.ext_iff.mpr (hflow.1 z (Set.mem_univ z))
  have h_deriv2 : ∀ z, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z)) s := fun z s hs =>
    HasDerivAt.prodMk (hflow.2.1 s hs z (Set.mem_univ z)) (hflow.2.2 s hs z (Set.mem_univ z))
  have h_deriv_Ioo : ∀ z, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z)) (Set.Ici s) s := fun z s hs =>
    (h_deriv2 z s hs).hasDerivWithinAt
  obtain ⟨Dflow, hDeriv, hCont⟩ := charFlow_hasFDerivAt_in_initialPoint gradW hgradW_C1 L hL ρ
    charX charV T hT hflow h_int hρD_cont hcontIcc
  intro t ht
  set K : ℝ := ((max 1 L : NNReal) : ℝ) with hK
  have hCcoe : (((Real.exp (K * t)).toNNReal : NNReal) : ℝ) = Real.exp (K * t) :=
    Real.coe_toNNReal _ (le_of_lt (Real.exp_pos _))
  have hderiv : ∀ z, HasFDerivAt (fun z => (charX t z, charV t z)) (Dflow t z) z := fun z =>
    hDeriv t ht z
  have hM_cont : Continuous (Dflow t) := hCont t ht
  have hanti : AntilipschitzWith (Real.exp (K * t)).toNNReal
      (fun z => (charX t z, charV t z)) := by
    refine AntilipschitzWith.of_le_mul_dist (fun z₁ z₂ => ?_)
    have h1 := charFlow_antilipschitzInZ_via_gronwall_Ioo gradW L hL ρ h_int charX charV T
      h_init hcontIcc h_deriv2 t ht z₁ z₂
    rw [sub_zero] at h1
    rw [hCcoe, mul_comm]
    exact h1
  have hlip : LipschitzWith (Real.exp (K * t)).toNNReal
      (fun z => (charX t z, charV t z)) := by
    refine LipschitzWith.of_dist_le_mul (fun z₁ z₂ => ?_)
    have h1 := charFlow_lipschitzInZ_via_gronwall_Ioo gradW L hL ρ h_int charX charV T hT.le
      h_init hcontIcc h_deriv_Ioo t (Set.Ioo_subset_Icc_self ht) z₁ z₂
    rw [sub_zero] at h1
    rw [hCcoe, mul_comm]
    exact h1
  obtain ⟨Ψ, e, he_coe, hLeft, hRight, hΨlip, hΨderiv⟩ :=
    exists_global_c1_inverse_of_antilipschitz hderiv hM_cont hanti hlip
  refine ⟨Ψ, e, ?_, hLeft, hRight, hΨlip.continuous, hΨderiv⟩
  intro z; rw [he_coe z]; exact hderiv z

section Step3Joint
open Filter Topology Asymptotics

/-- **Step 3 gating lemma (generic) — joint `C¹` from continuous partial derivatives** on a
`ℝ × E` domain (Mathlib-absent).  A partial `s`-derivative `Ds p` at every point (`Ds` continuous)
plus a partial `z`-derivative `Dz₀` at the base point ⇒ `f` is Fréchet-differentiable at `(s₀,z₀)`
with total derivative `(h,k) ↦ h•Ds(s₀,z₀) + Dz₀ k`.  Proof: split the increment into an
`s`-part (FTC `∫₀ʰ Ds(s₀+u,z₀+k)du ≈ h•Ds₀` by continuity of `Ds`) and a `z`-part
(`= Dz₀ k + o(k)`).
This is the keystone for the joint `(s,w)` regularity of the two-time flow `Φ_{s→t}`: the flow's
partials are `M_s z` (jointly continuous, V2) in `z` and `b_s(Φ_s z)` in `s`.

**PR-ABLE (Mathlib upstream candidate).**  This is a general real-analysis result with no Vlasov
content — "a function on `ℝ × E` with a continuous partial derivative in the `ℝ` factor and a
Fréchet partial derivative in the `E` factor is Fréchet-differentiable" — filling a genuine gap in
`Mathlib/Analysis/Calculus`.  Generalisation worth doing before a PR: replace the `ℝ` factor by an
arbitrary first factor with an analogous "integrate the partial along segments" hypothesis, and
weaken `Continuous Ds` to `ContinuousAt Ds` at the base point (the proof only uses a neighbourhood
of `(s₀,z₀)`). -/
theorem hasFDerivAt_of_continuous_partials
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℝ × E → F} {Ds : ℝ × E → F} {Dz₀ : E →L[ℝ] F} (s₀ : ℝ) (z₀ : E)
    (hDs : ∀ p : ℝ × E, HasDerivAt (fun s => f (s, p.2)) (Ds p) p.1)
    (hDs_cont : Continuous Ds)
    (hDz₀ : HasFDerivAt (fun z => f (s₀, z)) Dz₀ z₀) :
    HasFDerivAt f
      ((ContinuousLinearMap.fst ℝ ℝ E).smulRight (Ds (s₀, z₀))
        + Dz₀.comp (ContinuousLinearMap.snd ℝ ℝ E)) (s₀, z₀) := by
  set Ds₀ : F := Ds (s₀, z₀) with hDs₀
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro ε hε
  have hBz : ∀ᶠ k in 𝓝 (0 : E),
      ‖f (s₀, z₀ + k) - f (s₀, z₀) - Dz₀ k‖ ≤ (ε / 2) * ‖k‖ := by
    have hz := hDz₀
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff] at hz
    exact hz (half_pos hε)
  have hBz' : ∀ᶠ p : ℝ × E in 𝓝 0,
      ‖f (s₀, z₀ + p.2) - f (s₀, z₀) - Dz₀ p.2‖ ≤ (ε / 2) * ‖p.2‖ :=
    (continuous_snd.tendsto (0 : ℝ × E)).eventually hBz
  have hball : ∀ᶠ q in 𝓝 ((s₀, z₀) : ℝ × E), ‖Ds q - Ds₀‖ ≤ ε / 2 := by
    have hc : Tendsto Ds (𝓝 (s₀, z₀)) (𝓝 Ds₀) := hDs_cont.continuousAt
    have hsub : Tendsto (fun q => Ds q - Ds₀) (𝓝 (s₀, z₀)) (𝓝 (Ds₀ - Ds₀)) :=
      hc.sub tendsto_const_nhds
    rw [sub_self] at hsub
    have h0 : Tendsto (fun q => ‖Ds q - Ds₀‖) (𝓝 (s₀, z₀)) (𝓝 0) := by
      simpa using hsub.norm
    exact h0.eventually (Iic_mem_nhds (half_pos hε))
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hball
  have hAs : ∀ᶠ p : ℝ × E in 𝓝 0,
      ‖f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀‖ ≤ (ε / 2) * ‖p‖ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ × E) hδpos] with p hp
    rw [mem_ball_zero_iff] at hp
    have hcont_u : Continuous (fun u => Ds (u, z₀ + p.2)) :=
      hDs_cont.comp (continuous_id.prodMk continuous_const)
    have hg_deriv : ∀ u : ℝ, HasDerivAt (fun s => f (s, z₀ + p.2)) (Ds (u, z₀ + p.2)) u :=
      fun u => hDs (u, z₀ + p.2)
    have hftc : ∫ u in s₀..(s₀ + p.1), Ds (u, z₀ + p.2)
        = f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hg_deriv u)
        (hcont_u.intervalIntegrable _ _)]
    have hbound_u : ∀ u ∈ Set.uIoc s₀ (s₀ + p.1), ‖Ds (u, z₀ + p.2) - Ds₀‖ ≤ ε / 2 := by
      intro u hu
      refine @hδ (u, z₀ + p.2) ?_
      have hple : |p.1| ≤ ‖p‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le p
      have hp1 : |u - s₀| ≤ ‖p‖ := by
        rcases Set.mem_uIcc.mp (Set.uIoc_subset_uIcc hu) with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ u - s₀)]
          rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ p.1)] at hple; linarith
        · rw [abs_of_nonpos (by linarith : u - s₀ ≤ 0)]
          rw [abs_of_nonpos (by linarith : p.1 ≤ 0)] at hple; linarith
      have hp2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
      rw [Prod.dist_eq]
      simp only [dist_eq_norm, add_sub_cancel_left, Real.norm_eq_abs]
      exact lt_of_le_of_lt (max_le hp1 hp2) hp
    have hA_eq : f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀
        = ∫ u in s₀..(s₀ + p.1), (Ds (u, z₀ + p.2) - Ds₀) := by
      rw [intervalIntegral.integral_sub (hcont_u.intervalIntegrable _ _)
          (intervalIntegrable_const), hftc, intervalIntegral.integral_const,
          add_sub_cancel_left]
    rw [hA_eq]
    calc ‖∫ u in s₀..(s₀ + p.1), (Ds (u, z₀ + p.2) - Ds₀)‖
        ≤ (ε / 2) * |(s₀ + p.1) - s₀| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbound_u
      _ = (ε / 2) * ‖p.1‖ := by rw [add_sub_cancel_left, Real.norm_eq_abs]
      _ ≤ (ε / 2) * ‖p‖ := mul_le_mul_of_nonneg_left (norm_fst_le p) (by positivity)
  filter_upwards [hAs, hBz'] with p hAp hBp
  have hdecomp :
      f ((s₀, z₀) + p) - f (s₀, z₀)
        - ((ContinuousLinearMap.fst ℝ ℝ E).smulRight Ds₀
            + Dz₀.comp (ContinuousLinearMap.snd ℝ ℝ E)) p
      = (f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀)
        + (f (s₀, z₀ + p.2) - f (s₀, z₀) - Dz₀ p.2) := by
    rw [show ((s₀, z₀) + p : ℝ × E) = (s₀ + p.1, z₀ + p.2) from rfl]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd']
    abel
  rw [hdecomp]
  calc ‖(f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀)
          + (f (s₀, z₀ + p.2) - f (s₀, z₀) - Dz₀ p.2)‖
      ≤ ‖f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀‖
        + ‖f (s₀, z₀ + p.2) - f (s₀, z₀) - Dz₀ p.2‖ := norm_add_le _ _
    _ ≤ (ε / 2) * ‖p‖ + (ε / 2) * ‖p‖ :=
        add_le_add hAp (le_trans hBp (mul_le_mul_of_nonneg_left (norm_snd_le p) (by positivity)))
    _ = ε * ‖p‖ := by ring

/-- **Step 3 gating lemma (LOCAL / open-set form)** — joint `HasFDerivAt` from continuous partial
derivatives on an open set `U ⊆ ℝ × E`.  The open-set generalisation of
`hasFDerivAt_of_continuous_partials` (which is the `U := univ` special case) that the PR-note above
flagged: the `s`-partial is required only on `U`, and `Ds` only `ContinuousOn U`.  This is the form
the Vlasov flow needs — its partials exist and are continuous only on the open window
`Ioo 0 T ×ˢ univ`.  Proof = the global proof + ball-in-`U` bookkeeping (`B((s₀,z₀),r) ⊆ U`; the FTC
segment points `(u, z₀+p.2)`, `u ∈ uIcc s₀ (s₀+p.1)`, lie within `‖p‖ < min δ (r/2)` of `(s₀,z₀)`,
hence in `U` and within the continuity radius `δ`).

NOTE (consolidation TODO): the global `hasFDerivAt_of_continuous_partials` above is the `univ`
special case of this; a follow-up cleanup should rewrite it as the one-line corollary
`hasFDerivAt_of_continuous_partials_open isOpen_univ (Set.mem_univ _) (fun p _ => hDs p)
hDs_cont.continuousOn hDz₀` to drop the duplicated proof.  **PR-ABLE** (the more
general statement). -/
theorem hasFDerivAt_of_continuous_partials_open
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℝ × E → F} {Ds : ℝ × E → F} {Dz₀ : E →L[ℝ] F}
    {U : Set (ℝ × E)} (hU : IsOpen U) {s₀ : ℝ} {z₀ : E} (hmem : (s₀, z₀) ∈ U)
    (hDs : ∀ p ∈ U, HasDerivAt (fun s => f (s, p.2)) (Ds p) p.1)
    (hDs_cont : ContinuousOn Ds U)
    (hDz₀ : HasFDerivAt (fun z => f (s₀, z)) Dz₀ z₀) :
    HasFDerivAt f
      ((ContinuousLinearMap.fst ℝ ℝ E).smulRight (Ds (s₀, z₀))
        + Dz₀.comp (ContinuousLinearMap.snd ℝ ℝ E)) (s₀, z₀) := by
  set Ds₀ : F := Ds (s₀, z₀) with hDs₀
  obtain ⟨r, hrpos, hrU⟩ := Metric.isOpen_iff.mp hU (s₀, z₀) hmem
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro ε hε
  have hBz : ∀ᶠ k in 𝓝 (0 : E),
      ‖f (s₀, z₀ + k) - f (s₀, z₀) - Dz₀ k‖ ≤ (ε / 2) * ‖k‖ := by
    have hz := hDz₀
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff] at hz
    exact hz (half_pos hε)
  have hBz' : ∀ᶠ p : ℝ × E in 𝓝 0,
      ‖f (s₀, z₀ + p.2) - f (s₀, z₀) - Dz₀ p.2‖ ≤ (ε / 2) * ‖p.2‖ :=
    (continuous_snd.tendsto (0 : ℝ × E)).eventually hBz
  have hball : ∀ᶠ q in 𝓝 ((s₀, z₀) : ℝ × E), ‖Ds q - Ds₀‖ ≤ ε / 2 := by
    have hc : Tendsto Ds (𝓝 (s₀, z₀)) (𝓝 Ds₀) := hDs_cont.continuousAt (hU.mem_nhds hmem)
    have hsub : Tendsto (fun q => Ds q - Ds₀) (𝓝 (s₀, z₀)) (𝓝 (Ds₀ - Ds₀)) :=
      hc.sub tendsto_const_nhds
    rw [sub_self] at hsub
    have h0 : Tendsto (fun q => ‖Ds q - Ds₀‖) (𝓝 (s₀, z₀)) (𝓝 0) := by
      simpa using hsub.norm
    exact h0.eventually (Iic_mem_nhds (half_pos hε))
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hball
  set ρr : ℝ := min δ (r / 2) with hρr
  have hρrpos : 0 < ρr := lt_min hδpos (by positivity)
  have hAs : ∀ᶠ p : ℝ × E in 𝓝 0,
      ‖f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀‖ ≤ (ε / 2) * ‖p‖ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ × E) hρrpos] with p hp
    rw [mem_ball_zero_iff] at hp
    have hdist : ∀ u ∈ Set.uIcc s₀ (s₀ + p.1),
        dist ((u, z₀ + p.2) : ℝ × E) (s₀, z₀) ≤ ‖p‖ := by
      intro u hu
      have hple : |p.1| ≤ ‖p‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le p
      have hp1 : |u - s₀| ≤ ‖p‖ := by
        rcases Set.mem_uIcc.mp hu with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ u - s₀)]
          rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ p.1)] at hple; linarith
        · rw [abs_of_nonpos (by linarith : u - s₀ ≤ 0)]
          rw [abs_of_nonpos (by linarith : p.1 ≤ 0)] at hple; linarith
      have hp2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
      rw [Prod.dist_eq]
      refine max_le ?_ ?_
      · rw [dist_eq_norm]; simpa [Real.norm_eq_abs] using hp1
      · rw [dist_eq_norm, add_sub_cancel_left]; exact hp2
    have hmemU : ∀ u ∈ Set.uIcc s₀ (s₀ + p.1), ((u, z₀ + p.2) : ℝ × E) ∈ U := by
      intro u hu
      apply hrU
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (hdist u hu)
        (lt_of_lt_of_le hp (le_trans (min_le_right _ _) (by linarith)))
    have hcont_u : ContinuousOn (fun u => Ds (u, z₀ + p.2)) (Set.uIcc s₀ (s₀ + p.1)) := by
      refine hDs_cont.comp (continuous_id.prodMk continuous_const).continuousOn ?_
      exact fun u hu => hmemU u hu
    have hg_deriv : ∀ u ∈ Set.uIcc s₀ (s₀ + p.1),
        HasDerivAt (fun s => f (s, z₀ + p.2)) (Ds (u, z₀ + p.2)) u :=
      fun u hu => hDs (u, z₀ + p.2) (hmemU u hu)
    have hftc : ∫ u in s₀..(s₀ + p.1), Ds (u, z₀ + p.2)
        = f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu => hg_deriv u hu)
        (hcont_u.intervalIntegrable)]
    have hbound_u : ∀ u ∈ Set.uIoc s₀ (s₀ + p.1), ‖Ds (u, z₀ + p.2) - Ds₀‖ ≤ ε / 2 := by
      intro u hu
      refine @hδ (u, z₀ + p.2) ?_
      have hmem' := hdist u (Set.uIoc_subset_uIcc hu)
      exact lt_of_le_of_lt hmem' (lt_of_lt_of_le hp (min_le_left _ _))
    have hA_eq : f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀
        = ∫ u in s₀..(s₀ + p.1), (Ds (u, z₀ + p.2) - Ds₀) := by
      rw [intervalIntegral.integral_sub (hcont_u.intervalIntegrable)
          (intervalIntegrable_const), hftc, intervalIntegral.integral_const,
          add_sub_cancel_left]
    rw [hA_eq]
    calc ‖∫ u in s₀..(s₀ + p.1), (Ds (u, z₀ + p.2) - Ds₀)‖
        ≤ (ε / 2) * |(s₀ + p.1) - s₀| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbound_u
      _ = (ε / 2) * ‖p.1‖ := by rw [add_sub_cancel_left, Real.norm_eq_abs]
      _ ≤ (ε / 2) * ‖p‖ := mul_le_mul_of_nonneg_left (norm_fst_le p) (by positivity)
  filter_upwards [hAs, hBz'] with p hAp hBp
  have hdecomp :
      f ((s₀, z₀) + p) - f (s₀, z₀)
        - ((ContinuousLinearMap.fst ℝ ℝ E).smulRight Ds₀
            + Dz₀.comp (ContinuousLinearMap.snd ℝ ℝ E)) p
      = (f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀)
        + (f (s₀, z₀ + p.2) - f (s₀, z₀) - Dz₀ p.2) := by
    rw [show ((s₀, z₀) + p : ℝ × E) = (s₀ + p.1, z₀ + p.2) from rfl]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_snd']
    abel
  rw [hdecomp]
  calc ‖(f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀)
          + (f (s₀, z₀ + p.2) - f (s₀, z₀) - Dz₀ p.2)‖
      ≤ ‖f (s₀ + p.1, z₀ + p.2) - f (s₀, z₀ + p.2) - p.1 • Ds₀‖
        + ‖f (s₀, z₀ + p.2) - f (s₀, z₀) - Dz₀ p.2‖ := norm_add_le _ _
    _ ≤ (ε / 2) * ‖p‖ + (ε / 2) * ‖p‖ :=
        add_le_add hAp (le_trans hBp (mul_le_mul_of_nonneg_left (norm_snd_le p) (by positivity)))
    _ = ε * ‖p‖ := by ring

end Step3Joint

omit [NeZero d] in
/-- **Step 3 — the forward flow `(s,z) ↦ Φ_s z` is jointly continuous** on `Icc 0 T ×ˢ univ`
(`(s,z)`-order).  Gronwall Lipschitz-in-`z` (uniform over `[0,T]`) + per-`z` continuity-in-`s`, via
the generic `continuousOn_prod_of_lipschitz_continuousOn`, then a prod-order swap.  Extracted from
`#3`'s V2-branch pattern so the joint `C¹`-ness (Step 3 (iii)) can reuse it directly. -/
lemma charFlow_continuousOn_joint
    (gradW : PhysSpace d → PhysSpace d) (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d) (T : ℝ) (hT : 0 ≤ T)
    (hinit : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (hcontIcc : ∀ z, ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (hderiv : ∀ z, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s => (charX s z, charV s z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z)) (Set.Ici s) s) :
    ContinuousOn (fun p : ℝ × PhaseSpace d => (charX p.1 p.2, charV p.1 p.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := by
  have hgron := charFlow_lipschitzInZ_via_gronwall_Ioo gradW L hL ρ h_int charX charV T hT
    hinit hcontIcc hderiv
  have hjoint_zs : ContinuousOn (fun p : PhaseSpace d × ℝ => (charX p.2 p.1, charV p.2 p.1))
      (Set.univ ×ˢ Set.Icc (0 : ℝ) T) := by
    refine continuousOn_prod_of_lipschitz_continuousOn (fun z s => (charX s z, charV s z)) T
      (Real.exp (((max 1 L : NNReal) : ℝ) * T)) (fun s hs z₁ z₂ => ?_) hcontIcc
    calc dist ((charX s z₁, charV s z₁) : PhaseSpace d) (charX s z₂, charV s z₂)
        ≤ dist z₁ z₂ * Real.exp (((max 1 L : NNReal) : ℝ) * (s - 0)) := hgron s hs z₁ z₂
      _ = Real.exp (((max 1 L : NNReal) : ℝ) * (s - 0)) * dist z₁ z₂ := by ring
      _ ≤ Real.exp (((max 1 L : NNReal) : ℝ) * T) * dist z₁ z₂ := by
          refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) dist_nonneg
          have hsT : s - 0 ≤ T := by simp only [sub_zero]; exact hs.2
          exact mul_le_mul_of_nonneg_left hsT (by positivity)
  have hswap : ContinuousOn (fun p : ℝ × PhaseSpace d => ((p.2, p.1) : PhaseSpace d × ℝ))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := (continuous_snd.prodMk continuous_fst).continuousOn
  have hmaps : Set.MapsTo (fun p : ℝ × PhaseSpace d => ((p.2, p.1) : PhaseSpace d × ℝ))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) (Set.univ ×ˢ Set.Icc (0 : ℝ) T) :=
    fun p hp => ⟨Set.mem_univ _, hp.1⟩
  exact hjoint_zs.comp hswap hmaps

omit [NeZero d] in
/-- **Step 3 (ii) — the field along the flow `(s,z) ↦ b_s(Φ_s z)` is jointly continuous** on
`Icc 0 T ×ˢ univ`.  First component `charV` from flow joint continuity; second component
`-(∇W ∗ ρ_s)(charX s z)` from `(s,x) ↦ (∇W∗ρ_s)(x)` jointly continuous (equi-Lipschitz-in-`x` from
`convolveFunctionMeasure_lipschitz_in_x` + continuous-in-`s` from `hf_cont`) composed with the flow.
This is the partial-`s`-derivative continuity input to the joint `C¹`-ness (Step 3 (iii)). -/
lemma vlasovField_along_flow_continuousOn
    (gradW : PhysSpace d → PhysSpace d) (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (hf_cont : ∀ x, Continuous (fun s => convolveFunctionMeasure gradW (ρ s) x))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d) (T : ℝ)
    (hflowjoint : ContinuousOn (fun p : ℝ × PhaseSpace d => (charX p.1 p.2, charV p.1 p.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ)) :
    ContinuousOn (fun p : ℝ × PhaseSpace d =>
        vlasovVectorField gradW ρ p.1 (charX p.1 p.2, charV p.1 p.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := by
  have hcomp1 : ContinuousOn (fun p : ℝ × PhaseSpace d => charV p.1 p.2)
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := continuous_snd.comp_continuousOn hflowjoint
  have hcharX : ContinuousOn (fun p : ℝ × PhaseSpace d => charX p.1 p.2)
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := continuous_fst.comp_continuousOn hflowjoint
  have hconv_joint : ContinuousOn
      (fun p : PhysSpace d × ℝ => convolveFunctionMeasure gradW (ρ p.2) p.1)
      (Set.univ ×ˢ Set.Icc (0 : ℝ) T) :=
    continuousOn_prod_of_lipschitz_continuousOn
      (fun (x : PhysSpace d) (s : ℝ) => convolveFunctionMeasure gradW (ρ s) x) T (L:ℝ)
      (fun s _ x₁ x₂ =>
        (convolveFunctionMeasure_lipschitz_in_x gradW L hL (ρ s) (h_int s)).dist_le_mul x₁ x₂)
      (fun x => (hf_cont x).continuousOn)
  have hg2 : ContinuousOn (fun p : ℝ × PhaseSpace d => ((charX p.1 p.2, p.1) : PhysSpace d × ℝ))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := hcharX.prodMk continuousOn_fst
  have hg2maps : Set.MapsTo (fun p : ℝ × PhaseSpace d => ((charX p.1 p.2, p.1) : PhysSpace d × ℝ))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) (Set.univ ×ˢ Set.Icc (0 : ℝ) T) :=
    fun p hp => ⟨Set.mem_univ _, hp.1⟩
  have hconv_along : ContinuousOn
      (fun p : ℝ × PhaseSpace d => convolveFunctionMeasure gradW (ρ p.1) (charX p.1 p.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) := hconv_joint.comp hg2 hg2maps
  have heq : (fun p : ℝ × PhaseSpace d =>
        vlasovVectorField gradW ρ p.1 (charX p.1 p.2, charV p.1 p.2))
      = fun p => ((charV p.1 p.2),
          -(convolveFunctionMeasure gradW (ρ p.1) (charX p.1 p.2))) := by
    funext p; rfl
  rw [heq]
  exact hcomp1.prodMk hconv_along.neg

omit [NeZero d] in
/-- **Step 3 (iii) — the forward flow `(s,z) ↦ Φ_s z` is jointly `C¹`** on `U := Ioo 0 T ×ˢ univ`:
Fréchet-differentiable at every point with a jointly-continuous total derivative `DΦ`.  Built by
composing the open-set gating theorem (`hasFDerivAt_of_continuous_partials_open`) — fed the
`s`-partial `b_s(Φ_s z)` (flow ODE, jointly continuous by item (ii)) and the `z`-partial `M_s z`
(the fundamental matrix, via D1c, jointly continuous by item (i)).  Per L14 the matrix is rebuilt
concretely (`fundamentalMatrix (A z) s`), NOT routed through `#3`'s existential.

The field `bfun` and matrix `Mfun` are made opaque locals (`clear_value`, the D1c lesson) so the
gating unification stays syntactic and never unfolds the `vlasovVectorField`/`vlasovFieldJacobian`
integrals — the per-point derivative facts are established in terms of them *before* clearing.
`A` is kept transparent through the D1c call (whose coefficient is
`vlasovFieldJacobian`) and cleared
only afterwards (before the projection-reduction defeqs).  No `maxHeartbeats` bump needed. -/
theorem charFlow_hasFDerivAt_joint
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 < T)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (hf_cont : ∀ x, Continuous (fun s => convolveFunctionMeasure gradW (ρ s) x))
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (hcontIcc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T)) :
    ∃ DΦ : ℝ × PhaseSpace d → (ℝ × PhaseSpace d →L[ℝ] PhaseSpace d),
      (∀ p ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d)),
        HasFDerivAt (fun q : ℝ × PhaseSpace d => (charX q.1 q.2, charV q.1 q.2)) (DΦ p) p) ∧
      ContinuousOn DΦ (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := by
  set A : PhaseSpace d → ℝ → (PhaseSpace d →L[ℝ] PhaseSpace d) :=
    fun z s => vlasovFieldJacobian gradW ρ (s, (charX s z, charV s z)) with hA_def
  have hAcont : ∀ z, ContinuousOn (A z) (Set.Icc 0 T) := fun z =>
    vlasovVariationalCoeff_continuousOn gradW ρ charX charV T z (hcontIcc z) hρD_cont
  have h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z := fun z =>
    Prod.ext_iff.mpr ⟨(hflow.1 z (Set.mem_univ z)).1, (hflow.1 z (Set.mem_univ z)).2⟩
  have h_deriv : ∀ z, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s => (charX s z, charV s z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z)) (Set.Ici s) s := fun z s hs =>
    (HasDerivAt.prodMk (hflow.2.1 s hs z (Set.mem_univ z))
      (hflow.2.2 s hs z (Set.mem_univ z))).hasDerivWithinAt
  have hflowjoint_sz : ContinuousOn (fun q : ℝ × PhaseSpace d => (charX q.1 q.2, charV q.1 q.2))
      (Set.Icc 0 T ×ˢ Set.univ) :=
    charFlow_continuousOn_joint gradW L hL ρ h_int charX charV T hT.le h_init hcontIcc h_deriv
  -- field as an opaque local
  set bfun : ℝ × PhaseSpace d → PhaseSpace d :=
    fun q => vlasovVectorField gradW ρ q.1 (charX q.1 q.2, charV q.1 q.2) with hbfun_def
  have hb_cont : ContinuousOn bfun (Set.Icc 0 T ×ˢ Set.univ) :=
    vlasovField_along_flow_continuousOn gradW L hL ρ h_int hf_cont charX charV T hflowjoint_sz
  -- `A` jointly continuous + bounded ⇒ `M` jointly continuous (item (i))
  have hflowjoint_zs : ContinuousOn (fun p : PhaseSpace d × ℝ => (charX p.2 p.1, charV p.2 p.1))
      (Set.univ ×ˢ Set.Icc 0 T) := by
    have hswap : ContinuousOn (fun p : PhaseSpace d × ℝ => ((p.2, p.1) : ℝ × PhaseSpace d))
        (Set.univ ×ˢ Set.Icc 0 T) := (continuous_snd.prodMk continuous_fst).continuousOn
    have hmaps : Set.MapsTo (fun p : PhaseSpace d × ℝ => ((p.2, p.1) : ℝ × PhaseSpace d))
        (Set.univ ×ˢ Set.Icc 0 T) (Set.Icc 0 T ×ˢ Set.univ) := fun p hp => ⟨hp.2, Set.mem_univ _⟩
    exact hflowjoint_sz.comp hswap hmaps
  have hg : ContinuousOn
      (fun p : PhaseSpace d × ℝ => ((p.2, (charX p.2 p.1, charV p.2 p.1)) : ℝ × PhaseSpace d))
      (Set.univ ×ˢ Set.Icc 0 T) := continuousOn_snd.prodMk hflowjoint_zs
  have hmapsg : Set.MapsTo
      (fun p : PhaseSpace d × ℝ => ((p.2, (charX p.2 p.1, charV p.2 p.1)) : ℝ × PhaseSpace d))
      (Set.univ ×ˢ Set.Icc 0 T) (Set.Icc 0 T ×ˢ Set.univ) := fun p hp => ⟨hp.2, Set.mem_univ _⟩
  have hA_contOn : ContinuousOn (fun p : PhaseSpace d × ℝ => A p.1 p.2) (Set.univ ×ˢ Set.Icc 0 T) :=
    (vlasovFieldJacobian_continuousOn gradW ρ T hρD_cont).comp hg hmapsg
  have hA_bound : ∀ z, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖A z s‖ ≤ ((max 1 L : NNReal) : ℝ) := by
    intro z s _
    have heq : A z s = fderiv ℝ (vlasovVectorField gradW ρ s) (charX s z, charV s z) := by
      simp only [hA_def]
      exact (vlasovVectorField_hasFDerivAt_in_z gradW hgradW_C1 L hL ρ h_int s
        (charX s z, charV s z)).fderiv.symm
    rw [heq]
    exact norm_fderiv_le_of_lipschitz ℝ (vlasovVectorField_lipschitzWith gradW L hL ρ h_int s)
  have hM_zs : ContinuousOn (fun p : PhaseSpace d × ℝ => fundamentalMatrix (A p.1) p.2)
      (Set.univ ×ˢ Set.Icc 0 T) :=
    fundamentalMatrix_continuous_param_joint A T hT.le ((max 1 L : NNReal) : ℝ) (by positivity)
      hA_contOn hA_bound
  have hU_open : IsOpen (Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d))) :=
    isOpen_Ioo.prod isOpen_univ
  have hU_sub : Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d)) ⊆ Set.Icc 0 T ×ˢ Set.univ :=
    Set.prod_mono Set.Ioo_subset_Icc_self (subset_refl _)
  -- matrix as a local (kept transparent for the D1c call, which needs `A`'s coefficient)
  set Mfun : ℝ × PhaseSpace d → (PhaseSpace d →L[ℝ] PhaseSpace d) :=
    fun p => fundamentalMatrix (A p.2) p.1 with hMfun_def
  -- z-partial at base via D1c — needs `A` TRANSPARENT (its coefficient is `vlasovFieldJacobian`).
  have hDz_all : ∀ s₀ ∈ Set.Ioo (0 : ℝ) T, ∀ z₀ : PhaseSpace d,
      HasFDerivAt (fun z => (charX s₀ z, charV s₀ z)) (Mfun (s₀, z₀)) z₀ := by
    intro s₀ hs₀ z₀
    obtain ⟨h0, hMcont, hMderiv⟩ := fundamentalMatrix_spec (A z₀) T hT.le (hAcont z₀)
    exact charFlow_hasFDerivAt_of_fundamentalMatrix gradW hgradW_C1 L hL ρ charX charV T hT hflow
      h_int hρD_cont z₀ hcontIcc (fundamentalMatrix (A z₀)) h0 hMcont hMderiv s₀ hs₀
  have hDs_all : ∀ p ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d)),
      HasDerivAt (fun s => ((charX s p.2, charV s p.2) : PhaseSpace d)) (bfun p) p.1 := by
    intro p hp'
    exact HasDerivAt.prodMk (hflow.2.1 p.1 hp'.1 p.2 (Set.mem_univ _))
      (hflow.2.2 p.1 hp'.1 p.2 (Set.mem_univ _))
  -- NOW make `A`/field/matrix opaque so the projection-reduction defeqs below never unfold the
  -- heavy `vlasovFieldJacobian`/`vlasovVectorField` integrals (D1c lesson).
  clear_value A bfun Mfun
  have hM_sz : ContinuousOn Mfun (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := by
    rw [hMfun_def]
    have hswap : ContinuousOn (fun p : ℝ × PhaseSpace d => ((p.2, p.1) : PhaseSpace d × ℝ))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := (continuous_snd.prodMk continuous_fst).continuousOn
    have hmaps : Set.MapsTo (fun p : ℝ × PhaseSpace d => ((p.2, p.1) : PhaseSpace d × ℝ))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) (Set.univ ×ˢ Set.Icc 0 T) :=
      fun p hp => ⟨Set.mem_univ _, Set.Ioo_subset_Icc_self hp.1⟩
    exact hM_zs.comp hswap hmaps
  refine ⟨fun p => (ContinuousLinearMap.fst ℝ ℝ (PhaseSpace d)).smulRight (bfun p)
      + (Mfun p).comp (ContinuousLinearMap.snd ℝ ℝ (PhaseSpace d)), ?_, ?_⟩
  · rintro ⟨s₀, z₀⟩ hp
    obtain ⟨hs₀, _⟩ := hp
    exact hasFDerivAt_of_continuous_partials_open
      (f := fun q : ℝ × PhaseSpace d => (charX q.1 q.2, charV q.1 q.2)) (Ds := bfun)
      hU_open ⟨hs₀, Set.mem_univ _⟩ hDs_all (hb_cont.mono hU_sub) (hDz_all s₀ hs₀ z₀)
  · have hT1 : ContinuousOn (fun p : ℝ × PhaseSpace d =>
        (ContinuousLinearMap.fst ℝ ℝ (PhaseSpace d)).smulRight (bfun p))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := by
      have hc : Continuous (fun v : PhaseSpace d =>
          (ContinuousLinearMap.fst ℝ ℝ (PhaseSpace d)).smulRight v) :=
        (ContinuousLinearMap.smulRightL ℝ (ℝ × PhaseSpace d) (PhaseSpace d)
          (ContinuousLinearMap.fst ℝ ℝ (PhaseSpace d))).continuous
      exact hc.comp_continuousOn (hb_cont.mono hU_sub)
    have hT2 : ContinuousOn (fun p : ℝ × PhaseSpace d =>
        (Mfun p).comp (ContinuousLinearMap.snd ℝ ℝ (PhaseSpace d)))
        (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := hM_sz.clm_comp continuousOn_const
    exact hT1.add hT2

omit [NeZero d] in
/-- **Step 3 (iv-A) — the forward flow `(s,z) ↦ Φ_s z` is `ContDiffAt ℝ 1`** at each point of the
open window (the chart-IFT input for item (iv)).  Lifts item (iii)'s `HasFDerivAt`-everywhere +
`ContinuousOn`-derivative to `ContDiffAt` via `contDiffAt_succ_iff_hasFDerivAt`. -/
lemma charFlow_contDiffAt_joint
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 < T)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (hf_cont : ∀ x, Continuous (fun s => convolveFunctionMeasure gradW (ρ s) x))
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (hcontIcc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T)) :
    ∀ p ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d)),
      ContDiffAt ℝ 1 (fun q : ℝ × PhaseSpace d => (charX q.1 q.2, charV q.1 q.2)) p := by
  obtain ⟨DΦ, hFDeriv, hDΦ_cont⟩ :=
    charFlow_hasFDerivAt_joint gradW hgradW_C1 L hL ρ charX charV T hT
    hflow h_int hf_cont hρD_cont hcontIcc
  have hU_open : IsOpen (Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d))) :=
    isOpen_Ioo.prod isOpen_univ
  intro p hp
  have hmain : ContDiffAt ℝ ((0:ℕ) + 1)
      (fun q : ℝ × PhaseSpace d => (charX q.1 q.2, charV q.1 q.2)) p := by
    rw [contDiffAt_succ_iff_hasFDerivAt]
    refine ⟨DΦ, ⟨Set.Ioo (0 : ℝ) T ×ˢ Set.univ, hU_open.mem_nhds hp, fun y hy => hFDeriv y hy⟩, ?_⟩
    exact contDiffAt_zero.mpr ⟨Set.Ioo (0 : ℝ) T ×ˢ Set.univ, hU_open.mem_nhds hp, hDΦ_cont⟩
  simpa using hmain

open Filter Topology in
omit [NeZero d] in
/-- **Step 3 (iv) — the per-slice inverse `Ψ_s := Φ_s⁻¹` is jointly `C¹`** on `Ioo 0 T ×ˢ univ`,
the keystone of the two-time flow `Φ_{s→t} = Φ_t ∘ Φ_s⁻¹`.

**PROVEN (axiom-clean)** via the space-time chart inverse-function theorem — see the proof plan
below, realized exactly as scouted: `charFlow_contDiffAt_joint` (iv-A) for the chart `ContDiffAt`,
the block-triangular `≃L` (invertibility from Step 2's `e z₀` via `HasFDerivAt.unique` +
`ofBijective`), `ContDiffAt.to_localInverse`, and the global patch via `localInverse_unique` (the
global per-slice inverse is a local left inverse of the chart, by injectivity on the window).

Per slice `s ∈ Ioo 0 T`, Step 2 (`exists_charFlow_inverse_On`) already gives the inverse `Ψ_s` and
its invertible derivative family `e` (`= M_s z`, `#3`/D1c); here we upgrade to JOINT `(s,w)`
regularity via the space-time chart.

**Proof plan (atoms scouted + verified, 2026-06-16):**
1. **Forward chart `Ξ : (s,z) ↦ (s, Φ_s z)` is `ContDiffAt ℝ 1` at each
   `(s₀,z₀) ∈ Ioo 0 T ×ˢ univ`.**
   `Φ := (charX·, charV·)` is jointly `C¹` (`charFlow_hasFDerivAt_joint`, item (iii) — `∃ DΦ`,
   `HasFDerivAt`-everywhere + `ContinuousOn DΦ`); lift to `ContDiffAt ℝ 1 Φ` via
   `contDiffAt_succ_iff_hasFDerivAt` (`Mathlib/.../ContDiff/Defs.lean:994`, `n := 0`: feed `DΦ`, the
   open nbhd `U ∈ 𝓝`, `HasFDerivAt`-on-`U`, and `ContDiffAt 0 DΦ` from `contDiffAt_zero` +
   `ContinuousOn DΦ U`).  `Ξ = (fst, Φ)` so `ContDiffAt ℝ 1 Ξ` via `ContDiffAt.prod` with
   `contDiffAt_fst`.
2. **`DΞ(s₀,z₀)` is an invertible `≃L`.**  Block-lower-triangular `(h,k) ↦ (h, h•b + M·k)` with
   `b := b_{s₀}(Φ_{s₀}z₀)`, `M := M_{s₀}z₀` invertible (Step 2's `e₀ z₀`).  Build the `ℝ×E ≃L ℝ×E`
   via `ContinuousLinearEquiv.ofBijective` (inject: `(h,k)↦0 ⇒ h=0`, then `M k=0 ⇒ k=0`; finite-dim
   `LinearMap.injective_iff_surjective`).  `HasStrictFDerivAt Ξ (this ≃L) (s₀,z₀)` via
   `ContDiffAt.hasStrictFDerivAt'`.
3. **Local `C¹` inverse + patch.**  `ContDiffAt.to_localInverse`
   (`Mathlib/.../InverseFunctionTheorem/ContDiff.lean:66`) ⇒ `Ξ.localInverse` is `ContDiffAt ℝ 1` at
   `Ξ(s₀,z₀) = (s₀, Φ_{s₀}z₀)`.  The global `(s,w)↦(s, Ψ_s w)` agrees with
   `Ξ.localInverse` on a nbhd
   (both left-inverses; `Ξ` injective on `Ioo 0 T ×ˢ univ` since `s` is preserved + each `Φ_s`
   injective per Step 2) ⇒ `ContDiffAt.congr` ⇒ `(s,w)↦(s,Ψ_s w)` is `ContDiffAt ℝ 1` at each point
   ⇒ `ContDiffOn ℝ 1` (projecting off the `s` component, `ContDiffAt.snd`).
4. **Bijectivity** is the per-slice `LeftInverse`/`RightInverse` from `exists_charFlow_inverse_On`,
   packaged into the `s`-indexed `Ψ`.
The two-time flow `Φ_{s→t} = Φ_t ∘ Ψ_s` is then jointly `C¹` by composing with `Φ_t` (`C¹` in its
argument, `#3`), and the dual core's transport identity differentiates it. -/
theorem charFlow_inverse_contDiffOn_joint
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 < T)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (hf_cont : ∀ x, Continuous (fun s => convolveFunctionMeasure gradW (ρ s) x))
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (hcontIcc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T)) :
    ∃ Ψ : ℝ → PhaseSpace d → PhaseSpace d,
      (∀ s ∈ Set.Ioo (0 : ℝ) T,
        Function.LeftInverse (Ψ s) (fun z => (charX s z, charV s z))) ∧
      (∀ s ∈ Set.Ioo (0 : ℝ) T,
        Function.RightInverse (Ψ s) (fun z => (charX s z, charV s z))) ∧
      ContDiffOn ℝ 1 (fun p : ℝ × PhaseSpace d => Ψ p.1 p.2) (Set.Ioo 0 T ×ˢ Set.univ) := by
  classical
  obtain ⟨DΦ, hFDeriv, -⟩ := charFlow_hasFDerivAt_joint gradW hgradW_C1 L hL ρ charX charV T hT
    hflow h_int hf_cont hρD_cont hcontIcc
  have hΦ_cda := charFlow_contDiffAt_joint gradW hgradW_C1 L hL ρ charX charV T hT
    hflow h_int hf_cont hρD_cont hcontIcc
  have hstep2 := exists_charFlow_inverse_On gradW hgradW_C1 L hL ρ charX charV T hT
    hflow h_int hρD_cont hcontIcc
  have hbij : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      Function.Bijective (fun z => ((charX s z, charV s z) : PhaseSpace d)) := by
    intro s hs
    obtain ⟨Ψ', e, _, hL', hR', _, _⟩ := hstep2 s hs
    exact ⟨hL'.injective, hR'.surjective⟩
  set Ψ : ℝ → PhaseSpace d → PhaseSpace d :=
    fun s => Function.invFun (fun z => (charX s z, charV s z)) with hΨ_def
  have hLeft : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      Function.LeftInverse (Ψ s) (fun z => (charX s z, charV s z)) :=
    fun s hs => Function.leftInverse_invFun (hbij s hs).1
  have hRight : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      Function.RightInverse (Ψ s) (fun z => (charX s z, charV s z)) :=
    fun s hs => Function.rightInverse_invFun (hbij s hs).2
  refine ⟨Ψ, hLeft, hRight, ?_⟩
  set Ξ : ℝ × PhaseSpace d → ℝ × PhaseSpace d :=
    fun x => (x.1, (charX x.1 x.2, charV x.1 x.2)) with hΞ_def
  intro pt hpt
  obtain ⟨hs₀, -⟩ := hpt
  obtain ⟨Ψ', e, he_deriv, -, -, -, -⟩ := hstep2 pt.1 hs₀
  set z₀ : PhaseSpace d := Ψ pt.1 pt.2 with hz₀_def
  have hΦz₀ : (charX pt.1 z₀, charV pt.1 z₀) = pt.2 := hRight pt.1 hs₀ pt.2
  have hΞ_cda : ContDiffAt ℝ 1 Ξ (pt.1, z₀) :=
    contDiffAt_fst.prodMk (hΦ_cda (pt.1, z₀) ⟨hs₀, Set.mem_univ _⟩)
  set DΞ : (ℝ × PhaseSpace d) →L[ℝ] (ℝ × PhaseSpace d) :=
    (ContinuousLinearMap.fst ℝ ℝ (PhaseSpace d)).prod (DΦ (pt.1, z₀)) with hDΞ_def
  have hΞ_hd : HasFDerivAt Ξ DΞ (pt.1, z₀) :=
    (hasFDerivAt_fst).prodMk (hFDeriv (pt.1, z₀) ⟨hs₀, Set.mem_univ _⟩)
  have hincl : HasFDerivAt (fun z : PhaseSpace d => ((pt.1, z) : ℝ × PhaseSpace d))
      ((0 : PhaseSpace d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (PhaseSpace d))) z₀ :=
    (hasFDerivAt_const (pt.1 : ℝ) z₀).prodMk (hasFDerivAt_id z₀)
  have hslice : HasFDerivAt (fun z => (charX pt.1 z, charV pt.1 z))
      ((DΦ (pt.1, z₀)).comp
        ((0 : PhaseSpace d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (PhaseSpace d)))) z₀ :=
    (hFDeriv (pt.1, z₀) ⟨hs₀, Set.mem_univ _⟩).comp z₀ hincl
  have hcomp_eq : (DΦ (pt.1, z₀)).comp
      ((0 : PhaseSpace d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (PhaseSpace d)))
      = (e z₀ : PhaseSpace d →L[ℝ] PhaseSpace d) :=
    hslice.unique (he_deriv z₀)
  have hslice_app : ∀ k : PhaseSpace d,
      DΦ (pt.1, z₀) ((0 : ℝ), k) = (e z₀ : PhaseSpace d →L[ℝ] PhaseSpace d) k := by
    intro k
    have h1 : ((0 : PhaseSpace d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (PhaseSpace d))) k
        = ((0 : ℝ), k) := by simp
    rw [← h1, ← ContinuousLinearMap.comp_apply, hcomp_eq]
  have hker : LinearMap.ker (DΞ : (ℝ × PhaseSpace d) →ₗ[ℝ] (ℝ × PhaseSpace d)) = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr (fun x hx => ?_)
    have hxapp : (x.1, DΦ (pt.1, z₀) x) = ((0 : ℝ), (0 : PhaseSpace d)) := by
      have : DΞ x = ((0 : ℝ), (0 : PhaseSpace d)) := hx
      simpa [hDΞ_def, ContinuousLinearMap.prod_apply] using this
    have hx1 : x.1 = 0 := (Prod.ext_iff.mp hxapp).1
    have hx2 : DΦ (pt.1, z₀) x = 0 := (Prod.ext_iff.mp hxapp).2
    have hxz : x = ((0 : ℝ), x.2) := Prod.ext hx1 rfl
    have hez : (e z₀ : PhaseSpace d →L[ℝ] PhaseSpace d) x.2 = 0 := by
      rw [← hslice_app x.2, ← hxz]; exact hx2
    have : x.2 = 0 := by
      have hinj := (e z₀).injective
      have : (e z₀) x.2 = (e z₀) 0 := by rw [map_zero]; exact_mod_cast hez
      exact hinj this
    exact Prod.ext hx1 this
  have hrange : LinearMap.range (DΞ : (ℝ × PhaseSpace d) →ₗ[ℝ] (ℝ × PhaseSpace d)) = ⊤ :=
    LinearMap.range_eq_top.mpr
      (LinearMap.injective_iff_surjective.mp (LinearMap.ker_eq_bot.mp hker))
  set eΞ : (ℝ × PhaseSpace d) ≃L[ℝ] (ℝ × PhaseSpace d) :=
    ContinuousLinearEquiv.ofBijective DΞ hker hrange with heΞ_def
  have hΞ_hd' : HasFDerivAt Ξ (eΞ : (ℝ × PhaseSpace d) →L[ℝ] (ℝ × PhaseSpace d)) (pt.1, z₀) :=
    hΞ_hd
  have hlocinv : ContDiffAt ℝ 1 (hΞ_cda.localInverse hΞ_hd' one_ne_zero) (Ξ (pt.1, z₀)) :=
    hΞ_cda.to_localInverse hΞ_hd' one_ne_zero
  have hstrict := hΞ_cda.hasStrictFDerivAt' hΞ_hd' (one_ne_zero)
  have hloc : ∀ᶠ x in 𝓝 ((pt.1, z₀) : ℝ × PhaseSpace d),
      ((fun y : ℝ × PhaseSpace d => ((y.1, Ψ y.1 y.2) : ℝ × PhaseSpace d)) (Ξ x)) = x := by
    have hIoo : ∀ᶠ x in 𝓝 ((pt.1, z₀) : ℝ × PhaseSpace d), x.1 ∈ Set.Ioo (0 : ℝ) T :=
      continuous_fst.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds hs₀)
    filter_upwards [hIoo] with x hx
    have hL2 : Ψ x.1 (charX x.1 x.2, charV x.1 x.2) = x.2 := hLeft x.1 hx x.2
    simp only [hΞ_def]
    rw [hL2]
  have huniq : ∀ᶠ y in 𝓝 (Ξ (pt.1, z₀)),
      ((y.1, Ψ y.1 y.2) : ℝ × PhaseSpace d) = (hΞ_cda.localInverse hΞ_hd' one_ne_zero) y :=
    hstrict.localInverse_unique hloc
  have hΞeq : Ξ (pt.1, z₀) = (pt.1, pt.2) := by rw [hΞ_def]; exact Prod.ext rfl hΦz₀
  have hG_cda : ContDiffAt ℝ 1
      (fun y : ℝ × PhaseSpace d => ((y.1, Ψ y.1 y.2) : ℝ × PhaseSpace d)) (pt.1, pt.2) := by
    rw [← hΞeq]
    exact hlocinv.congr_of_eventuallyEq huniq
  have hpt_eq : pt = (pt.1, pt.2) := rfl
  rw [hpt_eq]
  exact (hG_cda.snd).contDiffWithinAt

/-! ### Step 4 — the transported test function and the transport identity

The dual core's `s ↦ ∫ ψ_s d(f s)` argument rests on the backward-transported test
`ψ_s := φ ∘ Φ_{s→t}` where `Φ_{s→t} = Φ_t ∘ Φ_s⁻¹` is the two-time flow (Step 3 gave it jointly
`C¹`).  Two deliverables, both taking the *outputs* of Step 3 (the inverse `Ψ` + the `C¹` terminal
map `Φ_t`) as hypotheses rather than re-deriving them from the flow-construction data: -/

omit [NeZero d] in
/-- **Step 4 (4a) — the two-time flow `Φ_{s→t} = Φ_t ∘ Φ_s⁻¹` is jointly `C¹`** on
`Ioo 0 T ×ˢ univ`.

The two-time flow `(s,w) ↦ (charX t (Ψ_s w), charV t (Ψ_s w))` is the composition of the terminal
map `Φ_t = (charX t ·, charV t ·)` (`C¹` in its argument — `hΦt_C1`, from Step 2 / item (iii) at the
fixed time `t`) with the jointly-`C¹` inverse family `(s,w) ↦ Ψ_s w` (`hΨ_C1`, item (iv)).  Proof:
`ContDiff.comp_contDiffOn`. -/
theorem twoTimeFlow_contDiffOn_joint
    (charX charV : ℝ → PhaseSpace d → PhysSpace d) (T t : ℝ)
    (Ψ : ℝ → PhaseSpace d → PhaseSpace d)
    (hΨ_C1 : ContDiffOn ℝ 1 (fun p : ℝ × PhaseSpace d => Ψ p.1 p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hΦt_C1 : ContDiff ℝ 1 (fun z : PhaseSpace d => (charX t z, charV t z))) :
    ContDiffOn ℝ 1
      (fun p : ℝ × PhaseSpace d => ((charX t (Ψ p.1 p.2), charV t (Ψ p.1 p.2)) : PhaseSpace d))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) :=
  hΦt_C1.comp_contDiffOn hΨ_C1

omit [NeZero d] in
/-- **Step 4 (4b) — the transport identity `∂_s ψ_s + Dψ_s · b_s = 0`.**

For the backward-transported test `ψ_s(w) := φ(Φ_t(Ψ_s w)) = φ(Φ_{s→t} w)`, the partial
`s`-derivative cancels the spatial directional derivative along the field:
`∂_s ψ_s(w) = -(Dψ_s(w))(b_s(w))`, where `b_s = vlasovVectorField gradW ρ s` and
`Dψ_s(w) = fderiv ℝ (ψ s) w`.  This is the dual of `vlasov_traj_chain_rule` (the pushforward
direction) and the engine that makes `s ↦ ∫ ψ_s d(f s)` constant in Step 6.

Proof:
* `ψ` is jointly `C¹` on `Ioo 0 T ×ˢ univ` (4a + `φ` smooth), so `HasFDerivAt (uncurry ψ) Dψ (s,w)`
  at the interior point `(s,w)`, with `Dψ` the joint Fréchet derivative.
* Constancy curve: set `z₀ := Ψ_s w`, so `w = Φ_s z₀` (`hΨ_right`).  The composite
  `s' ↦ ψ_{s'}(Φ_{s'} z₀) = φ(Φ_t(Ψ_{s'}(Φ_{s'} z₀))) = φ(Φ_t z₀)` is **constant** in `s'`
  (`hΨ_left`: `Ψ_{s'} ∘ Φ_{s'} = id`), hence has zero `s'`-derivative.
* The curve `c(s') := (s', Φ_{s'} z₀)` has `HasDerivAt c (1, b_s w) s` (`hflow_ode` + `id`), with
  `c(s) = (s, w)`.  Chain rule: `0 = Dψ(s,w)(1, b_s w) = Dψ(s,w)(1,0) + Dψ(s,w)(0, b_s w)`.
* `Dψ(s,w)(1,0) = ∂_s ψ_s(w)` (compose `uncurry ψ` with `s' ↦ (s', w)`) and
  `Dψ(s,w)(0,k) = (fderiv ℝ (ψ s) w) k` (compose with `w' ↦ (s, w')`).  Surjectivity (`hΨ_right`)
  covers every `w`.  Rearrange to the claimed `HasDerivAt`. -/
theorem transportedTest_transport_identity
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d) (T t : ℝ)
    (φ : PhaseSpace d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (Ψ : ℝ → PhaseSpace d → PhaseSpace d)
    (hΨ_left : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      Function.LeftInverse (Ψ s) (fun z => (charX s z, charV s z)))
    (hΨ_right : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      Function.RightInverse (Ψ s) (fun z => (charX s z, charV s z)))
    (hΨ_C1 : ContDiffOn ℝ 1 (fun p : ℝ × PhaseSpace d => Ψ p.1 p.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hΦt_C1 : ContDiff ℝ 1 (fun z : PhaseSpace d => (charX t z, charV t z)))
    (hflow_ode : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z)) s)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) T) (w : PhaseSpace d) :
    HasDerivAt (fun s' => φ (charX t (Ψ s' w), charV t (Ψ s' w)))
      (-(fderiv ℝ (fun w' : PhaseSpace d => φ (charX t (Ψ s w'), charV t (Ψ s w'))) w
          (vlasovVectorField gradW ρ s w))) s := by
  classical
  -- uncurried two-time flow and transported test
  set G2 : ℝ × PhaseSpace d → PhaseSpace d :=
    fun p => (charX t (Ψ p.1 p.2), charV t (Ψ p.1 p.2)) with hG2_def
  set g : ℝ × PhaseSpace d → ℝ := fun p => φ (G2 p) with hg_def
  have hopen : IsOpen (Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d))) :=
    isOpen_Ioo.prod isOpen_univ
  have hmem : ((s, w) : ℝ × PhaseSpace d) ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d)) :=
    ⟨hs, Set.mem_univ _⟩
  -- right-inverse identity: Φ_s (Ψ_s w) = w
  have hw : (charX s (Ψ s w), charV s (Ψ s w)) = w := hΨ_right s hs w
  -- g is jointly C¹, hence HasFDerivAt at the interior point (s,w)
  have hG2_cd : ContDiffOn ℝ 1 G2 (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) :=
    twoTimeFlow_contDiffOn_joint charX charV T t Ψ hΨ_C1 hΦt_C1
  have hG2_diff : DifferentiableAt ℝ G2 (s, w) :=
    hG2_cd.differentiableOn_one.differentiableAt (hopen.mem_nhds hmem)
  have hφ_diff : DifferentiableAt ℝ φ (G2 (s, w)) := hφ.differentiable (by simp) _
  have hg_fderiv : HasFDerivAt g (fderiv ℝ g (s, w)) (s, w) :=
    (hφ_diff.comp (s, w) hG2_diff).hasFDerivAt
  set G := fderiv ℝ g (s, w) with hG_def
  -- (A) spatial slice w' ↦ g (s, w') : fderiv = G ∘ inr
  have hslice_fderiv : HasFDerivAt (fun w' : PhaseSpace d => g (s, w'))
      (G.comp (ContinuousLinearMap.inr ℝ ℝ (PhaseSpace d))) w := by
    have := hg_fderiv.comp w (hasFDerivAt_prodMk_right s w)
    simpa only [Function.comp_def] using this
  -- (B) ∂_s slice s' ↦ g (s', w) : HasDerivAt with value G (1, 0)
  have hscurve : HasDerivAt (fun s' => ((s', w) : ℝ × PhaseSpace d))
      ((1 : ℝ), (0 : PhaseSpace d)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s w)
  have hs_slice : HasDerivAt (fun s' => g (s', w)) (G ((1 : ℝ), (0 : PhaseSpace d))) s := by
    have := hg_fderiv.comp_hasDerivAt s hscurve
    simpa only [Function.comp_def] using this
  -- (C) constancy curve c(s') = (s', Φ_{s'} (Ψ_s w)); chain rule gives G(1, b)
  have hccurve : HasDerivAt
      (fun s' => ((s', (charX s' (Ψ s w), charV s' (Ψ s w))) : ℝ × PhaseSpace d))
      ((1 : ℝ), vlasovVectorField gradW ρ s (charX s (Ψ s w), charV s (Ψ s w))) s :=
    (hasDerivAt_id s).prodMk (hflow_ode (Ψ s w) s hs)
  have hcs : ((s, (charX s (Ψ s w), charV s (Ψ s w))) : ℝ × PhaseSpace d) = (s, w) := by rw [hw]
  have hgc : HasDerivAt (fun s' => g (s', (charX s' (Ψ s w), charV s' (Ψ s w))))
      (G ((1 : ℝ), vlasovVectorField gradW ρ s (charX s (Ψ s w), charV s (Ψ s w)))) s := by
    have hF := hg_fderiv
    rw [← hcs] at hF
    have := hF.comp_hasDerivAt s hccurve
    simpa only [Function.comp_def] using this
  -- (D) the composite is eventually constant near s, so its derivative is 0
  have hconst : (fun s' => g (s', (charX s' (Ψ s w), charV s' (Ψ s w)))) =ᶠ[nhds s]
      (fun _ => φ (charX t (Ψ s w), charV t (Ψ s w))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with s' hs'
    simp only [hg_def, hG2_def]
    rw [hΨ_left s' hs' (Ψ s w)]
  have hgc0 : HasDerivAt (fun s' => g (s', (charX s' (Ψ s w), charV s' (Ψ s w)))) 0 s :=
    (hasDerivAt_const s (φ (charX t (Ψ s w), charV t (Ψ s w)))).congr_of_eventuallyEq hconst
  -- (E) uniqueness: G (1, b) = 0
  have hGzero : G ((1 : ℝ), vlasovVectorField gradW ρ s (charX s (Ψ s w), charV s (Ψ s w))) = 0 :=
    hgc.unique hgc0
  -- (F) split G(1,b) = G(1,0) + G(0,b); identify G(0,b) with the target fderiv applied to b
  have hsplit : ((1 : ℝ), vlasovVectorField gradW ρ s (charX s (Ψ s w), charV s (Ψ s w)))
      = ((1 : ℝ), (0 : PhaseSpace d))
        + ((0 : ℝ), vlasovVectorField gradW ρ s (charX s (Ψ s w), charV s (Ψ s w))) := by
    ext <;> simp
  have hb_eq : vlasovVectorField gradW ρ s (charX s (Ψ s w), charV s (Ψ s w))
      = vlasovVectorField gradW ρ s w := by rw [hw]
  have hG0b : G ((0 : ℝ), vlasovVectorField gradW ρ s (charX s (Ψ s w), charV s (Ψ s w)))
      = (fderiv ℝ (fun w' : PhaseSpace d => φ (charX t (Ψ s w'), charV t (Ψ s w'))) w)
          (vlasovVectorField gradW ρ s w) := by
    have hfd : fderiv ℝ (fun w' : PhaseSpace d => g (s, w')) w
        = G.comp (ContinuousLinearMap.inr ℝ ℝ (PhaseSpace d)) := hslice_fderiv.fderiv
    have hfun : (fun w' : PhaseSpace d => g (s, w'))
        = (fun w' : PhaseSpace d => φ (charX t (Ψ s w'), charV t (Ψ s w'))) := rfl
    rw [hfun] at hfd
    rw [hfd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hb_eq]
  -- (G) G(1,0) = -(target fderiv)(b)
  have hval : G ((1 : ℝ), (0 : PhaseSpace d))
      = -(fderiv ℝ (fun w' : PhaseSpace d => φ (charX t (Ψ s w'), charV t (Ψ s w'))) w)
          (vlasovVectorField gradW ρ s w) := by
    have hsum : G ((1 : ℝ), (0 : PhaseSpace d))
        + G ((0 : ℝ), vlasovVectorField gradW ρ s (charX s (Ψ s w), charV s (Ψ s w))) = 0 := by
      rw [← map_add, ← hsplit]; exact hGzero
    rw [hG0b] at hsum
    linarith [hsum]
  -- (H) conclude
  have hgoalfun : (fun s' => φ (charX t (Ψ s' w), charV t (Ψ s' w)))
      = (fun s' => g (s', w)) := rfl
  rw [hgoalfun, ← hval]
  exact hs_slice


open Filter Topology Metric in
open scoped Convolution in
omit [NeZero d] in
/-- Helper 1 — uniform mollification of a continuous, compactly-supported function.
The mollified family `ρ_n ⋆ g` converges to `g` **uniformly** (not just pointwise), the
load-bearing analytic input the `C¹_c` test-class enlargement (#4) needs.  Proof: uniform
continuity of `g` (compact support) gives a single `δ`; once `rOut_n < δ`, the pointwise bump
estimate `dist_normed_convolution_le` fires at *every* base point simultaneously. -/
theorem mollifier_tendstoUniformly {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : PhaseSpace d → E) (hg_cont : Continuous g) (hg_cs : HasCompactSupport g)
    (φ : ℕ → ContDiffBump (0 : PhaseSpace d))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) :
    TendstoUniformly
      (fun n x => ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) g atTop := by
  have hHaar : (volume : Measure (PhaseSpace d)).IsAddHaarMeasure := by
    rw [show (volume : Measure (PhaseSpace d)) = (volume : Measure (PhysSpace d)).prod volume from
      Measure.volume_eq_prod _ _]
    infer_instance
  have hg_uc : UniformContinuous g := hg_cs.uniformContinuous_of_continuous hg_cont
  rw [Metric.uniformContinuous_iff] at hg_uc
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδ_prop⟩ := hg_uc (ε / 2) (by positivity)
  have hev : ∀ᶠ n in atTop, (φ n).rOut < δ := hφ.eventually (Iio_mem_nhds hδ)
  filter_upwards [hev] with n hn
  intro x₀
  rw [dist_comm]
  have hball : ∀ x ∈ ball x₀ (φ n).rOut, dist (g x) (g x₀) ≤ ε / 2 := by
    intro x hx
    exact le_of_lt (hδ_prop (lt_trans (mem_ball.mp hx) hn))
  have hbump := ContDiffBump.dist_normed_convolution_le (μ := volume) (φ := φ n) (g := g)
    hg_cont.aestronglyMeasurable hball
  exact lt_of_le_of_lt hbump (half_lt_self hε)

open Filter Topology Metric in
open scoped Convolution in
omit [NeZero d] in
/-- Helper 2 — the mollified Fréchet derivative converges uniformly.
`fderiv (ρ_n ⋆ χ) = ρ_n ⋆ (fderiv χ)` (convolution commutes onto the `C¹` factor via
`HasCompactSupport.hasFDerivAt_convolution_right`, with `precompR` reconciled to `lsmul` on the
operator codomain), and the right-hand side converges uniformly to `fderiv χ` by Helper 1 applied
to the continuous, compactly-supported `fderiv χ`. -/
theorem mollifiedFDeriv_tendstoUniformly
    (χ : PhaseSpace d → ℝ) (hχ_C1 : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (φ : ℕ → ContDiffBump (0 : PhaseSpace d))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) :
    TendstoUniformly
      (fun n z => fderiv ℝ ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] χ) z)
      (fderiv ℝ χ) atTop := by
  have hHaar : (volume : Measure (PhaseSpace d)).IsAddHaarMeasure := by
    rw [show (volume : Measure (PhaseSpace d)) = (volume : Measure (PhysSpace d)).prod volume from
      Measure.volume_eq_prod _ _]
    infer_instance
  have hdf_cont : Continuous (fderiv ℝ χ) := hχ_C1.continuous_fderiv one_ne_zero
  have hdf_cs : HasCompactSupport (fderiv ℝ χ) := hχc.fderiv ℝ
  -- the `precompR` bilinear map coincides with `lsmul` on the operator codomain
  have hbridge : (ContinuousLinearMap.lsmul ℝ ℝ).precompR (PhaseSpace d)
      = (ContinuousLinearMap.lsmul ℝ ℝ :
          ℝ →L[ℝ] (PhaseSpace d →L[ℝ] ℝ) →L[ℝ] (PhaseSpace d →L[ℝ] ℝ)) := by
    refine ContinuousLinearMap.ext fun u => ?_
    refine ContinuousLinearMap.ext fun v => ?_
    refine ContinuousLinearMap.ext fun x => ?_
    simp [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.lsmul_apply]
  have hfd : ∀ n, (fun z => fderiv ℝ
        ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] χ) z)
      = (fun z => ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fderiv ℝ χ) z) := by
    intro n
    funext z
    rw [(hχc.hasFDerivAt_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ)
      ((φ n).continuous_normed.locallyIntegrable) hχ_C1 z).fderiv, hbridge]
  have hgoal_eq :
      (fun n z => fderiv ℝ ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] χ) z)
      = (fun n z =>
          ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fderiv ℝ χ) z) := by
    funext n; exact hfd n
  rw [hgoal_eq]
  exact mollifier_tendstoUniformly (fderiv ℝ χ) hdf_cont hdf_cs φ hφ

-- ── Helpers for `weakEvolution_test_C1c_On`, extracted from its proof body (the
--    mathematical content is unchanged; each piece is generic in the test function). ──

omit [NeZero d] in
/-- Norm bound for the dual-composed difference of two Fréchet derivatives. -/
lemma toDualSymm_comp_sub_norm_le (ψ ϕ : PhaseSpace d → ℝ)
    (z : PhaseSpace d) (e : PhysSpace d →L[ℝ] PhaseSpace d) :
    ‖(InnerProductSpace.toDual ℝ (PhysSpace d)).symm ((fderiv ℝ ψ z).comp e)
      - (InnerProductSpace.toDual ℝ (PhysSpace d)).symm ((fderiv ℝ ϕ z).comp e)‖
    ≤ ‖fderiv ℝ ψ z - fderiv ℝ ϕ z‖ * ‖e‖ := by
  rw [← map_sub, LinearIsometryEquiv.norm_map, ← ContinuousLinearMap.sub_comp]
  exact ContinuousLinearMap.opNorm_comp_le _ _

omit [NeZero d] in
/-- Chain rule: the Fréchet derivative of an `x`-slice is the composition with `inl`. -/
lemma fderiv_slice_fst (ψ : PhaseSpace d → ℝ) (hψ : Differentiable ℝ ψ) (z : PhaseSpace d) :
    fderiv ℝ (fun x => ψ (x, z.2)) z.1
      = (fderiv ℝ ψ z).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) := by
  have h2 : HasFDerivAt (fun x : PhysSpace d => (x, z.2))
      (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) z.1 :=
    hasFDerivAt_prodMk_left z.1 z.2
  exact ((hψ z).hasFDerivAt.comp z.1 h2).fderiv

omit [NeZero d] in
/-- Chain rule: the Fréchet derivative of a `v`-slice is the composition with `inr`. -/
lemma fderiv_slice_snd (ψ : PhaseSpace d → ℝ) (hψ : Differentiable ℝ ψ) (z : PhaseSpace d) :
    fderiv ℝ (fun v => ψ (z.1, v)) z.2
      = (fderiv ℝ ψ z).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) := by
  have h2 : HasFDerivAt (fun v : PhysSpace d => (z.1, v))
      (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) z.2 :=
    hasFDerivAt_prodMk_right z.1 z.2
  exact ((hψ z).hasFDerivAt.comp z.2 h2).fderiv

omit [NeZero d] in
/-- Continuity of the first-slot partial-gradient field of a `C¹` test function. -/
lemma continuous_gradientSlice_fst (ψ : PhaseSpace d → ℝ) (g : PhaseSpace d → PhysSpace d)
    (hψ : Differentiable ℝ ψ) (hψ' : Continuous (fderiv ℝ ψ))
    (hg : ∀ z, g z = gradient (fun x => ψ (x, z.2)) z.1) : Continuous g := by
  have heq : g = fun z => (InnerProductSpace.toDual ℝ (PhysSpace d)).symm
      ((fderiv ℝ ψ z).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d))) := by
    funext z; rw [hg z]; simp only [gradient]; rw [fderiv_slice_fst ψ hψ z]
  rw [heq]
  exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
    (hψ'.clm_comp continuous_const)

omit [NeZero d] in
/-- Continuity of the second-slot partial-gradient field of a `C¹` test function. -/
lemma continuous_gradientSlice_snd (ψ : PhaseSpace d → ℝ) (g : PhaseSpace d → PhysSpace d)
    (hψ : Differentiable ℝ ψ) (hψ' : Continuous (fderiv ℝ ψ))
    (hg : ∀ z, g z = gradient (fun v => ψ (z.1, v)) z.2) : Continuous g := by
  have heq : g = fun z => (InnerProductSpace.toDual ℝ (PhysSpace d)).symm
      ((fderiv ℝ ψ z).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d))) := by
    funext z; rw [hg z]; simp only [gradient]; rw [fderiv_slice_snd ψ hψ z]
  rw [heq]
  exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
    (hψ'.clm_comp continuous_const)

omit [NeZero d] in
/-- Compact support of the first-slot partial-gradient field. -/
lemma hasCompactSupport_gradientSlice_fst (ψ : PhaseSpace d → ℝ)
    (g : PhaseSpace d → PhysSpace d) (hψ : Differentiable ℝ ψ) (hψcs : HasCompactSupport ψ)
    (hg : ∀ z, g z = gradient (fun x => ψ (x, z.2)) z.1) : HasCompactSupport g := by
  apply HasCompactSupport.intro hψcs
  intro z hz
  have hf0 : fderiv ℝ ψ z = 0 := fderiv_of_notMem_tsupport ℝ hz
  rw [hg z]; simp only [gradient]; rw [fderiv_slice_fst ψ hψ z, hf0]; simp

omit [NeZero d] in
/-- Compact support of the second-slot partial-gradient field. -/
lemma hasCompactSupport_gradientSlice_snd (ψ : PhaseSpace d → ℝ)
    (g : PhaseSpace d → PhysSpace d) (hψ : Differentiable ℝ ψ) (hψcs : HasCompactSupport ψ)
    (hg : ∀ z, g z = gradient (fun v => ψ (z.1, v)) z.2) : HasCompactSupport g := by
  apply HasCompactSupport.intro hψcs
  intro z hz
  have hf0 : fderiv ℝ ψ z = 0 := fderiv_of_notMem_tsupport ℝ hz
  rw [hg z]; simp only [gradient]; rw [fderiv_slice_snd ψ hψ z, hf0]; simp

omit [NeZero d] in
/-- First-slot partial gradients of two tests differ by at most the full
Fréchet-derivative difference. -/
lemma gradientSlice_fst_sub_norm_le (ψ ϕ : PhaseSpace d → ℝ)
    (hψ : Differentiable ℝ ψ) (hϕ : Differentiable ℝ ϕ)
    (gψ gϕ : PhaseSpace d → PhysSpace d)
    (hgψ : ∀ z, gψ z = gradient (fun x => ψ (x, z.2)) z.1)
    (hgϕ : ∀ z, gϕ z = gradient (fun x => ϕ (x, z.2)) z.1) (z : PhaseSpace d) :
    ‖gψ z - gϕ z‖ ≤ ‖fderiv ℝ ψ z - fderiv ℝ ϕ z‖ := by
  have e1 : gψ z = (InnerProductSpace.toDual ℝ (PhysSpace d)).symm
      ((fderiv ℝ ψ z).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d))) := by
    rw [hgψ z]; simp only [gradient]; rw [fderiv_slice_fst ψ hψ z]
  have e2 : gϕ z = (InnerProductSpace.toDual ℝ (PhysSpace d)).symm
      ((fderiv ℝ ϕ z).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d))) := by
    rw [hgϕ z]; simp only [gradient]; rw [fderiv_slice_fst ϕ hϕ z]
  rw [e1, e2]
  refine le_trans (toDualSymm_comp_sub_norm_le ψ ϕ z _) ?_
  calc ‖fderiv ℝ ψ z - fderiv ℝ ϕ z‖ * ‖ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)‖
      ≤ ‖fderiv ℝ ψ z - fderiv ℝ ϕ z‖ * 1 := by
        gcongr; exact ContinuousLinearMap.norm_inl_le_one ℝ (PhysSpace d) (PhysSpace d)
    _ = ‖fderiv ℝ ψ z - fderiv ℝ ϕ z‖ := mul_one _

omit [NeZero d] in
/-- Second-slot partial gradients of two tests differ by at most the full
Fréchet-derivative difference. -/
lemma gradientSlice_snd_sub_norm_le (ψ ϕ : PhaseSpace d → ℝ)
    (hψ : Differentiable ℝ ψ) (hϕ : Differentiable ℝ ϕ)
    (gψ gϕ : PhaseSpace d → PhysSpace d)
    (hgψ : ∀ z, gψ z = gradient (fun v => ψ (z.1, v)) z.2)
    (hgϕ : ∀ z, gϕ z = gradient (fun v => ϕ (z.1, v)) z.2) (z : PhaseSpace d) :
    ‖gψ z - gϕ z‖ ≤ ‖fderiv ℝ ψ z - fderiv ℝ ϕ z‖ := by
  have e1 : gψ z = (InnerProductSpace.toDual ℝ (PhysSpace d)).symm
      ((fderiv ℝ ψ z).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d))) := by
    rw [hgψ z]; simp only [gradient]; rw [fderiv_slice_snd ψ hψ z]
  have e2 : gϕ z = (InnerProductSpace.toDual ℝ (PhysSpace d)).symm
      ((fderiv ℝ ϕ z).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d))) := by
    rw [hgϕ z]; simp only [gradient]; rw [fderiv_slice_snd ϕ hϕ z]
  rw [e1, e2]
  refine le_trans (toDualSymm_comp_sub_norm_le ψ ϕ z _) ?_
  calc ‖fderiv ℝ ψ z - fderiv ℝ ϕ z‖ * ‖ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)‖
      ≤ ‖fderiv ℝ ψ z - fderiv ℝ ϕ z‖ * 1 := by
        gcongr; exact ContinuousLinearMap.norm_inr_le_one ℝ (PhysSpace d) (PhysSpace d)
    _ = ‖fderiv ℝ ψ z - fderiv ℝ ϕ z‖ := mul_one _

omit [NeZero d] in
/-- Integrability of the weak-evolution integrand against a probability measure:
continuous with compact support (both gradient slots), continuous field. -/
lemma inner_integrand_integrable
    (μ : Measure (PhaseSpace d)) [IsProbabilityMeasure μ]
    (fld : PhysSpace d → PhysSpace d) (hfld : Continuous fld)
    (gX gV : PhaseSpace d → PhysSpace d)
    (hgXc : Continuous gX) (hgVc : Continuous gV)
    (hgXcs : HasCompactSupport gX) (hgVcs : HasCompactSupport gV) :
    Integrable (fun z => @inner ℝ (PhysSpace d) _ z.2 (gX z)
      - @inner ℝ (PhysSpace d) _ (fld z.1) (gV z)) μ := by
  have hcont : Continuous (fun z => @inner ℝ (PhysSpace d) _ z.2 (gX z)
      - @inner ℝ (PhysSpace d) _ (fld z.1) (gV z)) :=
    (continuous_snd.inner hgXc).sub ((hfld.comp continuous_fst).inner hgVc)
  have hcs : HasCompactSupport (fun z => @inner ℝ (PhysSpace d) _ z.2 (gX z)
      - @inner ℝ (PhysSpace d) _ (fld z.1) (gV z)) := by
    apply HasCompactSupport.intro (IsCompact.union hgXcs hgVcs)
    intro z hz
    simp only [Set.mem_union, not_or] at hz
    rw [image_eq_zero_of_notMem_tsupport hz.1, image_eq_zero_of_notMem_tsupport hz.2]
    simp
  exact hcont.integrable_of_hasCompactSupport hcs

omit [NeZero d] in
/-- Pointwise bound on the difference of two weak-evolution integrands: on the
common support `K` it is `(R_K + B) * δ` (norm bound `R_K` on `K`, field bound `B`
on `K`, gradient-slot distance `δ`); off `K` both integrands agree. -/
lemma inner_integrand_sub_norm_le
    (K : Set (PhaseSpace d)) (R_K : ℝ) (hR_K_nn : 0 ≤ R_K) (hR_K : ∀ z ∈ K, ‖z‖ ≤ R_K)
    (fld : PhysSpace d → PhysSpace d) (B : ℝ) (hB_nn : 0 ≤ B)
    (hfld_K : ∀ z ∈ K, ‖fld (Prod.fst z)‖ ≤ B)
    (gX gV gX' gV' : PhaseSpace d → PhysSpace d) (δ : ℝ) (hδ_nn : 0 ≤ δ)
    (hXd : ∀ z, ‖gX' z - gX z‖ ≤ δ) (hVd : ∀ z, ‖gV' z - gV z‖ ≤ δ)
    (hXoff : ∀ z ∉ K, gX' z = gX z) (hVoff : ∀ z ∉ K, gV' z = gV z)
    (z : PhaseSpace d) :
    ‖(@inner ℝ (PhysSpace d) _ z.2 (gX z) - @inner ℝ (PhysSpace d) _ (fld z.1) (gV z))
      - (@inner ℝ (PhysSpace d) _ z.2 (gX' z)
          - @inner ℝ (PhysSpace d) _ (fld z.1) (gV' z))‖
    ≤ (R_K + B) * δ := by
  by_cases hzK : z ∈ K
  · have hrw : (@inner ℝ (PhysSpace d) _ z.2 (gX z)
          - @inner ℝ (PhysSpace d) _ (fld z.1) (gV z))
        - (@inner ℝ (PhysSpace d) _ z.2 (gX' z)
          - @inner ℝ (PhysSpace d) _ (fld z.1) (gV' z))
        = @inner ℝ (PhysSpace d) _ z.2 (gX z - gX' z)
          - @inner ℝ (PhysSpace d) _ (fld z.1) (gV z - gV' z) := by
      rw [inner_sub_right, inner_sub_right]; ring
    rw [Real.norm_eq_abs, hrw]
    have hb1 : |@inner ℝ (PhysSpace d) _ z.2 (gX z - gX' z)| ≤ R_K * δ := by
      refine le_trans (abs_real_inner_le_norm _ _) ?_
      have hz2 : ‖z.2‖ ≤ R_K := le_trans (norm_snd_le z) (hR_K z hzK)
      rw [norm_sub_rev (gX z)]
      exact mul_le_mul hz2 (hXd z) (norm_nonneg _) hR_K_nn
    have hb2 : |@inner ℝ (PhysSpace d) _ (fld z.1) (gV z - gV' z)| ≤ B * δ := by
      refine le_trans (abs_real_inner_le_norm _ _) ?_
      rw [norm_sub_rev (gV z)]
      exact mul_le_mul (hfld_K z hzK) (hVd z) (norm_nonneg _) hB_nn
    calc |@inner ℝ (PhysSpace d) _ z.2 (gX z - gX' z)
            - @inner ℝ (PhysSpace d) _ (fld z.1) (gV z - gV' z)|
        ≤ |@inner ℝ (PhysSpace d) _ z.2 (gX z - gX' z)|
          + |@inner ℝ (PhysSpace d) _ (fld z.1) (gV z - gV' z)| := abs_sub _ _
      _ ≤ R_K * δ + B * δ := by linarith
      _ = (R_K + B) * δ := by ring
  · rw [hXoff z hzK, hVoff z hzK]
    simp only [sub_self, norm_zero]
    positivity

omit [NeZero d] in
/-- On the window, the frozen convolution field over the spatial marginal is
integrable (in force form), linearly bounded, and continuous — packaged for
consumers that quantify over the window. -/
lemma convolveField_window_setup
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (M_ρ : ℝ)
    (hM_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M_ρ)
    (ε₀ : ℝ) (hε₀_def : ε₀ = ‖gradW 0‖ + (L : ℝ) * M_ρ) :
    ∀ σ ∈ Set.Icc (0 : ℝ) T,
      (Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal (f σ)))
      ∧ (∀ x : PhysSpace d, Integrable (fun y => gradW (x - y)) (spatialMarginal (f σ)))
      ∧ (∀ x : PhysSpace d,
          ‖convolveFunctionMeasure gradW (spatialMarginal (f σ)) x‖ ≤ ε₀ + (L:ℝ) * ‖x‖)
      ∧ Continuous (fun x => convolveFunctionMeasure gradW (spatialMarginal (f σ)) x) := by
  intro σ hσ
  have : IsProbabilityMeasure (f σ) := (hf_mom σ hσ).1
  have hprob_m : IsProbabilityMeasure (spatialMarginal (f σ)) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  -- ‖·‖ integrable wrt the spatial marginal (from the finite first moment of f σ)
  have h_y_int : Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal (f σ)) := by
    unfold spatialMarginal
    rw [integrable_map_measure (continuous_norm.measurable).aestronglyMeasurable
      measurable_fst.aemeasurable]
    refine Integrable.mono' (hf_mom σ hσ).2
      ((continuous_norm.comp continuous_fst).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => ?_)
    change |‖z.1‖| ≤ ‖z‖
    rw [abs_of_nonneg (norm_nonneg _)]; exact norm_fst_le z
  -- force-integrability (Lipschitz growth + finite moment)
  have h_int : ∀ x : PhysSpace d,
      Integrable (fun y => gradW (x - y)) (spatialMarginal (f σ)) := by
    intro x
    have h_aesm : AEStronglyMeasurable (fun y : PhysSpace d => gradW (x - y))
        (spatialMarginal (f σ)) :=
      (hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    have h_dom : ∀ y : PhysSpace d,
        ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + (L:ℝ) * ‖x‖ + (L:ℝ) * ‖y‖ := by
      intro y
      have hd := hL.dist_le_mul (x - y) 0
      simp only [dist_eq_norm, sub_zero] at hd
      have h_tri : ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x - y) - gradW 0‖ := by
        have := norm_add_le (gradW (x - y) - gradW 0) (gradW 0)
        simp only [sub_add_cancel] at this; linarith
      have h_sub_le : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
      have h_mul := mul_le_mul_of_nonneg_left h_sub_le L.coe_nonneg
      linarith
    have h_dom_int : Integrable
        (fun y : PhysSpace d => ‖gradW 0‖ + (L:ℝ) * ‖x‖ + (L:ℝ) * ‖y‖)
        (spatialMarginal (f σ)) := by
      have h_eq : (fun y : PhysSpace d => ‖gradW 0‖ + (L:ℝ) * ‖x‖ + (L:ℝ) * ‖y‖)
          = fun y => (‖gradW 0‖ + (L:ℝ) * ‖x‖) + (L:ℝ) * ‖y‖ := by funext y; ring
      rw [h_eq]; exact (integrable_const _).add (h_y_int.const_mul _)
    exact Integrable.mono' h_dom_int h_aesm (Filter.Eventually.of_forall h_dom)
  -- field bound (CharFlow idiom)
  have hbound : ∀ x : PhysSpace d,
      ‖convolveFunctionMeasure gradW (spatialMarginal (f σ)) x‖ ≤ ε₀ + (L:ℝ) * ‖x‖ := by
    intro x
    unfold convolveFunctionMeasure
    have h_sub_int : Integrable (fun y => ‖x - y‖) (spatialMarginal (f σ)) :=
      Integrable.mono' ((integrable_const ‖x‖).add h_y_int)
        ((aestronglyMeasurable_const (b := x)).sub aestronglyMeasurable_id |>.norm)
        (Filter.Eventually.of_forall fun y => by
          simp only [Real.norm_of_nonneg (norm_nonneg _)]; exact norm_sub_le x y)
    have h_bnd_int : Integrable (fun y => ‖gradW 0‖ + (L:ℝ) * ‖x - y‖) (spatialMarginal (f σ)) :=
      (integrable_const _).add (h_sub_int.const_mul _)
    have h_pt : ∀ y, ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + (L:ℝ) * ‖x - y‖ := by
      intro y
      have hd := hL.dist_le_mul (x - y) 0
      simp only [dist_eq_norm, sub_zero] at hd
      have h_tri : ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x - y) - gradW 0‖ := by
        have := norm_add_le (gradW (x - y) - gradW 0) (gradW 0)
        simp only [sub_add_cancel] at this; linarith
      linarith
    calc ‖∫ y, gradW (x - y) ∂(spatialMarginal (f σ))‖
        ≤ ∫ y, ‖gradW (x - y)‖ ∂(spatialMarginal (f σ)) := norm_integral_le_integral_norm _
      _ ≤ ∫ y, (‖gradW 0‖ + (L:ℝ) * ‖x - y‖) ∂(spatialMarginal (f σ)) :=
          integral_mono (h_int x).norm h_bnd_int (fun y => h_pt y)
      _ = ‖gradW 0‖ + (L:ℝ) * ∫ y, ‖x - y‖ ∂(spatialMarginal (f σ)) := by
          rw [integral_add (integrable_const _) (h_sub_int.const_mul _)]
          simp [integral_const, measureReal_def, measure_univ, integral_const_mul]
      _ ≤ ε₀ + (L:ℝ) * ‖x‖ := by
          have h_int_le : ∫ y, ‖x - y‖ ∂(spatialMarginal (f σ)) ≤ ‖x‖ + M_ρ := by
            calc ∫ y, ‖x - y‖ ∂(spatialMarginal (f σ))
                ≤ ∫ y, (‖x‖ + ‖y‖) ∂(spatialMarginal (f σ)) :=
                  integral_mono h_sub_int ((integrable_const _).add h_y_int)
                    (fun y => norm_sub_le x y)
              _ = ‖x‖ + ∫ y, ‖y‖ ∂(spatialMarginal (f σ)) := by
                  rw [integral_add (integrable_const _) h_y_int]
                  simp [integral_const, measureReal_def, measure_univ]
              _ ≤ ‖x‖ + M_ρ := by linarith [hM_ρ σ hσ]
          simp only [hε₀_def]
          linarith [mul_le_mul_of_nonneg_left h_int_le (NNReal.coe_nonneg L)]
  -- field continuity from the Lipschitz-in-x lemma
  have hcont : Continuous (fun x => convolveFunctionMeasure gradW (spatialMarginal (f σ)) x) :=
    (convolveFunctionMeasure_lipschitz_in_x gradW L hL (spatialMarginal (f σ)) h_int).continuous
  exact ⟨h_y_int, h_int, hbound, hcont⟩

omit [NeZero d] in
open Filter Topology Metric in
/-- Uniform convergence of integrands implies convergence of the integrals against
a probability measure (every term integrable). -/
lemma integral_tendsto_of_tendstoUniformly
    (μ : Measure (PhaseSpace d)) [IsProbabilityMeasure μ]
    (g : ℕ → PhaseSpace d → ℝ) (g₀ : PhaseSpace d → ℝ)
    (hUnif : TendstoUniformly g g₀ atTop)
    (hg₀_int : Integrable g₀ μ) (hg_int : ∀ n, Integrable (g n) μ) :
    Tendsto (fun n => ∫ z, g n z ∂μ) atTop (𝓝 (∫ z, g₀ z ∂μ)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (Metric.tendstoUniformly_iff.mp hUnif (ε/2) (by positivity))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  have hpt : ∀ z, |g n z - g₀ z| ≤ ε/2 := by
    intro z
    have h := hN n hn z
    rw [Real.dist_eq, abs_sub_comm] at h
    exact le_of_lt h
  calc |∫ z, g n z ∂μ - ∫ z, g₀ z ∂μ|
      = |∫ z, (g n z - g₀ z) ∂μ| := by rw [integral_sub (hg_int n) hg₀_int]
    _ ≤ ∫ z, |g n z - g₀ z| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _z, (ε/2) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _)
          (integrable_const _) (Eventually.of_forall hpt)
    _ = ε/2 := by simp
    _ < ε := half_lt_self hε

-- #4 (Step 5 interface): the weak evolution equation extended to C¹_c test functions.
open Filter Topology Metric in
open scoped Convolution Pointwise in
omit [NeZero d] in
theorem weakEvolution_test_C1c_On
    (gradW : PhysSpace d → PhysSpace d)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ)
    (hf_weak : IsVlasovSolutionOn gradW f T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    -- B2 enrichment (mollification proof): the velocity-term needs a uniform-in-σ bound on the
    -- frozen field `‖∇W∗ρ_σ‖` over the fixed compact support of the test, supplied by the
    -- Lipschitz growth of `gradW` (`hL`) and the uniform first-moment bound `hM_ρ`.
    (L : NNReal) (hL : LipschitzWith L gradW)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M_ρ)
    (χ : PhaseSpace d → ℝ) (hχ_C1 : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (gradXχ gradVχ : PhaseSpace d → PhysSpace d)
    (hgradXχ : ∀ z, gradXχ z = gradient (fun x => χ (x, z.2)) z.1)
    (hgradVχ : ∀ z, gradVχ z = gradient (fun v => χ (z.1, v)) z.2)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun σ => ∫ z, χ z ∂(f σ))
      (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXχ z)
             - @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (spatialMarginal (f s)) z.1)
                (gradVχ z)) ∂(f s)) s := by
  classical
  have hHaar : (volume : Measure (PhaseSpace d)).IsAddHaarMeasure := by
    rw [show (volume : Measure (PhaseSpace d)) = (volume : Measure (PhysSpace d)).prod volume from
      Measure.volume_eq_prod _ _]
    infer_instance
  have hvolReg : (volume : Measure (PhaseSpace d)).Regular := inferInstance
  -- mollifier family (shrinking bumps); copy of #9's
  set φ : ℕ → ContDiffBump (0 : PhaseSpace d) :=
    fun n => ⟨1 / (n + 2), 2 / (n + 2), by positivity, by
      rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num⟩ with hφ_def
  have hrout : ∀ n, (φ n).rOut = 2 / (n + 2) := fun n => rfl
  have hrout_tendsto : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    simp only [hrout]
    apply Filter.Tendsto.div_atTop (tendsto_const_nhds)
    exact Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  -- mollified test functions
  set χn : ℕ → PhaseSpace d → ℝ :=
    fun n => (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] χ with hχn_def
  have hχn_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (χn n) := fun n =>
    ((φ n).hasCompactSupport_normed).contDiff_convolution_left _
      (φ n).contDiff_normed hχ_C1.continuous.locallyIntegrable
  have hχn_cs : ∀ n, HasCompactSupport (χn n) := fun n =>
    HasCompactSupport.convolution _ (φ n).hasCompactSupport_normed hχc
  -- genuine partial gradients of χ_n
  set gXn : ℕ → PhaseSpace d → PhysSpace d :=
    fun n z => gradient (fun x => χn n (x, z.2)) z.1 with hgXn_def
  set gVn : ℕ → PhaseSpace d → PhysSpace d :=
    fun n z => gradient (fun v => χn n (z.1, v)) z.2 with hgVn_def
  -- D_n: the C^∞ weak-evolution derivative, from hf_weak applied to χ_n
  have hDn : ∀ n, ∀ σ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt (fun σ' => ∫ z, χn n z ∂(f σ'))
      (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gXn n z)
             - @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (spatialMarginal (f σ)) z.1)
                (gVn n z)) ∂(f σ)) σ := by
    intro n σ hσ
    have h := hf_weak (χn n) (hχn_smooth n) (hχn_cs n) (gXn n) (gVn n)
      (fun z => rfl) (fun z => rfl) σ hσ
    simpa using h
  -- pointwise convergence (0th order): ∫ χ_n d(f σ) → ∫ χ d(f σ)
  have hfg : ∀ σ ∈ Set.Ioo (0 : ℝ) T, Tendsto (fun n => ∫ z, χn n z ∂(f σ)) atTop
      (𝓝 (∫ z, χ z ∂(f σ))) := by
    intro σ hσ
    have : IsProbabilityMeasure (f σ) := (hf_mom σ (Set.Ioo_subset_Icc_self hσ)).1
    exact integral_tendsto_of_tendstoUniformly (f σ) χn χ
      (mollifier_tendstoUniformly χ hχ_C1.continuous hχc φ hrout_tendsto)
      (hχ_C1.continuous.integrable_of_hasCompactSupport hχc)
      (fun n => (hχn_smooth n).continuous.integrable_of_hasCompactSupport (hχn_cs n))
  -- uniform-in-σ convergence of the derivatives (the term bound)
  -- Helper 2: uniform fderiv convergence
  have hH2 := mollifiedFDeriv_tendstoUniformly χ hχ_C1 hχc φ hrout_tendsto
  -- fixed compact K containing all supports
  set K : Set (PhaseSpace d) := tsupport χ + Metric.closedBall (0 : PhaseSpace d) 1 with hK_def
  have hK_compact : IsCompact K := IsCompact.add hχc (isCompact_closedBall 0 1)
  obtain ⟨R0, hR0⟩ := (hK_compact.image continuous_norm).bddAbove
  set R_K := max R0 0 with hRK_def
  have hR_K_nn : (0 : ℝ) ≤ R_K := le_max_right _ _
  have hR_K : ∀ z ∈ K, ‖z‖ ≤ R_K := fun z hz => le_trans (hR0 ⟨z, hz, rfl⟩) (le_max_left _ _)
  -- tsupport χ ⊆ K, and fderiv χ vanishes off K
  have htsuppχ_K : tsupport χ ⊆ K := by
    intro z hz
    rw [hK_def]
    exact (add_zero z) ▸ Set.add_mem_add hz (by simp : (0:PhaseSpace d) ∈ Metric.closedBall 0 1)
  have hsuppχ : ∀ z ∉ K, fderiv ℝ χ z = 0 := by
    intro z hz
    exact fderiv_of_notMem_tsupport ℝ (fun h => hz (htsuppχ_K h))
  -- tsupport (χn n) ⊆ K, and fderiv (χn n) vanishes off K
  have htsuppχn_K : ∀ n, tsupport (χn n) ⊆ K := by
    intro n
    have h1 : Function.support (χn n)
        ⊆ Function.support ((φ n).normed volume) + Function.support χ :=
      support_convolution_subset _
    have h2 : Function.support ((φ n).normed volume) ⊆ Metric.closedBall 0 1 := by
      rw [(φ n).support_normed_eq]
      refine Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall ?_)
      rw [hrout n]; rw [div_le_one (by positivity)]; norm_num
    have h4 : Function.support (χn n) ⊆ K := by
      refine h1.trans ?_
      rw [hK_def, add_comm (tsupport χ)]
      exact Set.add_subset_add h2 (subset_tsupport χ)
    exact (closure_minimal h4 hK_compact.isClosed)
  have hsuppχn : ∀ n, ∀ z ∉ K, fderiv ℝ (χn n) z = 0 := by
    intro n z hz
    exact fderiv_of_notMem_tsupport ℝ (fun h => hz (htsuppχn_K n h))
  -- partial-gradient projection bounds (X and V), off Helper 2's fderiv difference
  -- field: integrability, bound, continuity — all on the window
  set ε₀ : ℝ := ‖gradW 0‖ + (L : ℝ) * M_ρ with hε₀_def
  have hε₀_nn : 0 ≤ ε₀ := by positivity
  have hfield_setup := convolveField_window_setup gradW L hL f T hf_mom M_ρ hM_ρ ε₀ hε₀_def
  -- THE ESTIMATE
  -- continuity of the four partial gradients (off the uniform fderiv)
  have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hχdiff : Differentiable ℝ χ := hχ_C1.differentiable one_ne_zero
  have hχ'cont : Continuous (fderiv ℝ χ) := hχ_C1.continuous_fderiv one_ne_zero
  have hgXχc : Continuous gradXχ :=
    continuous_gradientSlice_fst χ gradXχ hχdiff hχ'cont hgradXχ
  have hgVχc : Continuous gradVχ :=
    continuous_gradientSlice_snd χ gradVχ hχdiff hχ'cont hgradVχ
  have hgXnc : ∀ n, Continuous (gXn n) := fun n => continuous_gradientSlice_fst (χn n) (gXn n)
    ((hχn_smooth n).differentiable htop) ((hχn_smooth n).continuous_fderiv htop)
    (fun z => by rw [hgXn_def])
  have hgVnc : ∀ n, Continuous (gVn n) := fun n => continuous_gradientSlice_snd (χn n) (gVn n)
    ((hχn_smooth n).differentiable htop) ((hχn_smooth n).continuous_fderiv htop)
    (fun z => by rw [hgVn_def])
  -- compact support of the four partial gradients (vanish off the test's support)
  have hgXχcs : HasCompactSupport gradXχ :=
    hasCompactSupport_gradientSlice_fst χ gradXχ hχdiff hχc hgradXχ
  have hgVχcs : HasCompactSupport gradVχ :=
    hasCompactSupport_gradientSlice_snd χ gradVχ hχdiff hχc hgradVχ
  have hgXncs : ∀ n, HasCompactSupport (gXn n) := fun n =>
    hasCompactSupport_gradientSlice_fst (χn n) (gXn n)
      ((hχn_smooth n).differentiable htop) (hχn_cs n) (fun z => by rw [hgXn_def])
  have hgVncs : ∀ n, HasCompactSupport (gVn n) := fun n =>
    hasCompactSupport_gradientSlice_snd (χn n) (gVn n)
      ((hχn_smooth n).differentiable htop) (hχn_cs n) (fun z => by rw [hgVn_def])
  -- THE ESTIMATE
  have hf'unif : TendstoUniformlyOn
      (fun n σ => ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gXn n z)
             - @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (spatialMarginal (f σ)) z.1) (gVn n z)) ∂(f σ))
      (fun σ => ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXχ z)
             - @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (spatialMarginal (f σ)) z.1) (gradVχ z)) ∂(f σ))
      atTop (Set.Ioo 0 T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set C : ℝ := R_K + (ε₀ + (L:ℝ) * R_K) with hC_def
    have hC_nn : (0 : ℝ) ≤ C := by rw [hC_def]; positivity
    rw [Metric.tendstoUniformly_iff] at hH2
    filter_upwards [hH2 (ε/(C+1)) (by positivity)] with n hn
    intro σ hσ
    have hσ' : σ ∈ Set.Icc (0 : ℝ) T := Set.Ioo_subset_Icc_self hσ
    have : IsProbabilityMeasure (f σ) := (hf_mom σ hσ').1
    obtain ⟨_, _, hbnd, hfc⟩ := hfield_setup σ hσ'
    -- L15: make the field opaque so defeq never unfolds its Bochner integral
    set fldσ : PhysSpace d → PhysSpace d := convolveFunctionMeasure gradW (spatialMarginal (f σ))
      with hfldσ_def
    clear_value fldσ
    -- projection bounds for this n
    have hXp : ∀ z, ‖gXn n z - gradXχ z‖ ≤ ‖fderiv ℝ (χn n) z - fderiv ℝ χ z‖ :=
      fun z => gradientSlice_fst_sub_norm_le (χn n) χ
        ((hχn_smooth n).differentiable htop) hχdiff (gXn n) gradXχ
        (fun z => by rw [hgXn_def]) hgradXχ z
    have hVp : ∀ z, ‖gVn n z - gradVχ z‖ ≤ ‖fderiv ℝ (χn n) z - fderiv ℝ χ z‖ :=
      fun z => gradientSlice_snd_sub_norm_le (χn n) χ
        ((hχn_smooth n).differentiable htop) hχdiff (gVn n) gradVχ
        (fun z => by rw [hgVn_def]) hgradVχ z
    -- uniform fderiv bound at this n (uses χn = the convolution defeq, before clearing)
    have hfd_le : ∀ z, ‖fderiv ℝ (χn n) z - fderiv ℝ χ z‖ ≤ ε/(C+1) := by
      intro z
      have h := hn z
      rw [dist_eq_norm, norm_sub_rev] at h
      exact le_of_lt h
    -- L15: with the projection + fderiv bounds proven, make the heavy convolution defs opaque so
    -- the integrand-difference manipulations never unfold their Bochner integrals
    clear_value gXn gVn χn
    -- off K both gradient pairs agree (fderivs vanish there)
    have hXoff : ∀ z ∉ K, gXn n z = gradXχ z := by
      intro z hzK
      have hfd0 : fderiv ℝ (χn n) z = 0 := hsuppχn n z hzK
      have hfd0' : fderiv ℝ χ z = 0 := hsuppχ z hzK
      have := hXp z; rw [hfd0, hfd0', sub_self, norm_zero] at this
      exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
    have hVoff : ∀ z ∉ K, gVn n z = gradVχ z := by
      intro z hzK
      have hfd0 : fderiv ℝ (χn n) z = 0 := hsuppχn n z hzK
      have hfd0' : fderiv ℝ χ z = 0 := hsuppχ z hzK
      have := hVp z; rw [hfd0, hfd0', sub_self, norm_zero] at this
      exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
    -- field bound on K
    have hfld_K : ∀ z ∈ K, ‖fldσ (Prod.fst z)‖ ≤ ε₀ + (L:ℝ) * R_K := by
      intro z hzK
      refine le_trans (hbnd z.1) ?_
      have : ‖z.1‖ ≤ R_K := le_trans (norm_fst_le z) (hR_K z hzK)
      gcongr
    -- pointwise bound on the integrand difference
    have hpt : ∀ z, ‖(@inner ℝ (PhysSpace d) _ z.2 (gradXχ z)
          - @inner ℝ (PhysSpace d) _ (fldσ z.1)
              (gradVχ z))
        - (@inner ℝ (PhysSpace d) _ z.2 (gXn n z)
          - @inner ℝ (PhysSpace d) _ (fldσ z.1)
              (gVn n z))‖ ≤ C * (ε/(C+1)) := by
      intro z
      have h := inner_integrand_sub_norm_le K R_K hR_K_nn hR_K fldσ
        (ε₀ + (L:ℝ) * R_K) (by positivity) hfld_K
        gradXχ gradVχ (gXn n) (gVn n) (ε/(C+1)) (by positivity)
        (fun z => le_trans (hXp z) (hfd_le z)) (fun z => le_trans (hVp z) (hfd_le z))
        hXoff hVoff z
      refine le_trans h (le_of_eq ?_)
      rw [hC_def]
    -- integrability of both integrands (continuous + compact support in K)
    have hGd_int := inner_integrand_integrable (f σ) fldσ hfc gradXχ gradVχ
      hgXχc hgVχc hgXχcs hgVχcs
    have hGnd_int := inner_integrand_integrable (f σ) fldσ hfc (gXn n) (gVn n)
      (hgXnc n) (hgVnc n) (hgXncs n) (hgVncs n)
    -- assemble
    rw [Real.dist_eq, ← integral_sub hGd_int hGnd_int]
    calc |∫ z, ((@inner ℝ (PhysSpace d) _ z.2 (gradXχ z)
            - @inner ℝ (PhysSpace d) _ (fldσ z.1)
                (gradVχ z))
          - (@inner ℝ (PhysSpace d) _ z.2 (gXn n z)
            - @inner ℝ (PhysSpace d) _ (fldσ z.1)
                (gVn n z))) ∂(f σ)|
        ≤ ∫ z, C * (ε/(C+1)) ∂(f σ) := by
          refine le_trans (abs_integral_le_integral_abs) ?_
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall fun z => ?_)
          have := hpt z; rwa [Real.norm_eq_abs] at this
      _ = C * (ε/(C+1)) := by simp
      _ < ε := by
          have h1 : (0 : ℝ) < C + 1 := by positivity
          rw [← mul_div_assoc, div_lt_iff₀ h1]
          nlinarith [hε, hC_nn]
  -- assemble via the uniform-limit-of-derivatives theorem
  exact hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hf'unif (Eventually.of_forall hDn) hfg hs

-- NC (consumption form): integral of a jointly-continuous, uniformly-compactly-supported
-- family against the weak-solution measure curve is continuous in time.
omit [NeZero d] in
theorem vlasovSolutionOn_integral_continuousOn
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hf_narrow : ∀ (g : PhaseSpace d → ℝ), Continuous g → HasCompactSupport g →
      ContinuousOn (fun s => ∫ z, g z ∂(f s)) (Set.Icc 0 T))
    (G : ℝ → PhaseSpace d → ℝ)
    (hG_cont : Continuous (fun p : ℝ × PhaseSpace d => G p.1 p.2))
    (K : Set (PhaseSpace d)) (hK : IsCompact K)
    (hG_supp : ∀ s, ∀ z ∉ K, G s z = 0) :
    ContinuousOn (fun s => ∫ z, G s z ∂(f s)) (Set.Icc (0 : ℝ) T) := by
  -- Each slice G a is continuous, supported in K, hence integrable wrt the probability f b.
  have hGs_cont : ∀ a : ℝ, Continuous (fun z => G a z) := fun a =>
    hG_cont.comp (Continuous.prodMk_right a)
  have hGs_cs : ∀ a : ℝ, HasCompactSupport (fun z => G a z) := by
    intro a
    have hsub : tsupport (fun z => G a z) ⊆ K :=
      closure_minimal (fun z hz => by by_contra hzK; exact hz (hG_supp a z hzK)) hK.isClosed
    exact IsCompact.of_isClosed_subset hK (isClosed_tsupport _) hsub
  have hGint : ∀ (a b : ℝ), b ∈ Set.Icc (0 : ℝ) T → Integrable (fun z => G a z) (f b) := by
    intro a b hb
    have := (hf_mom b hb).1
    exact (hGs_cont a).integrable_of_hasCompactSupport (hGs_cs a)
  -- Uniform continuity of the uncurried G on the compact Icc 0 T ×ˢ K.
  have hC : IsCompact (Set.Icc (0 : ℝ) T ×ˢ K) := isCompact_Icc.prod hK
  have hG_uc : UniformContinuousOn (fun p : ℝ × PhaseSpace d => G p.1 p.2)
      (Set.Icc (0 : ℝ) T ×ˢ K) :=
    hC.uniformContinuousOn_of_continuous hG_cont.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hG_uc
  -- Main ε–δ.
  rw [Metric.continuousOn_iff]
  intro s₀ hs₀ ε hε
  obtain ⟨δ₁, hδ₁, hδ₁_prop⟩ := hG_uc (ε/2) (by positivity)
  -- term2: narrow continuity of f tested against the frozen g := G s₀.
  have hterm2 : ContinuousWithinAt (fun s => ∫ z, G s₀ z ∂(f s)) (Set.Icc 0 T) s₀ :=
    (hf_narrow (fun z => G s₀ z) (hGs_cont s₀) (hGs_cs s₀)) s₀ hs₀
  rw [Metric.continuousWithinAt_iff] at hterm2
  obtain ⟨δ₂, hδ₂, hδ₂_prop⟩ := hterm2 (ε/2) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s hs hsd => ?_⟩
  have hp_s : IsProbabilityMeasure (f s) := (hf_mom s hs).1
  have hsd1 : dist s s₀ < δ₁ := lt_of_lt_of_le hsd (min_le_left _ _)
  have hsd2 : dist s s₀ < δ₂ := lt_of_lt_of_le hsd (min_le_right _ _)
  -- pointwise: |G s z - G s₀ z| ≤ ε/2 (uniform continuity on K; both zero off K)
  have hpoint : ∀ z, |G s z - G s₀ z| ≤ ε/2 := by
    intro z
    by_cases hzK : z ∈ K
    · have hp : ((s, z) : ℝ × PhaseSpace d) ∈ Set.Icc (0 : ℝ) T ×ˢ K := ⟨hs, hzK⟩
      have hq : ((s₀, z) : ℝ × PhaseSpace d) ∈ Set.Icc (0 : ℝ) T ×ˢ K := ⟨hs₀, hzK⟩
      have hdpq : dist ((s, z) : ℝ × PhaseSpace d) (s₀, z) < δ₁ := by
        rw [Prod.dist_eq]
        exact max_lt hsd1 (by rw [dist_self]; exact hδ₁)
      have hlt := hδ₁_prop _ hp _ hq hdpq
      rw [Real.dist_eq] at hlt
      exact le_of_lt hlt
    · rw [hG_supp s z hzK, hG_supp s₀ z hzK, sub_zero, abs_zero]; positivity
  -- split the s-integral
  have key : ∫ z, G s z ∂(f s) - ∫ z, G s₀ z ∂(f s)
      = ∫ z, (G s z - G s₀ z) ∂(f s) :=
    (integral_sub (hGint s s hs) (hGint s₀ s hs)).symm
  have hfirst : dist (∫ z, G s z ∂(f s)) (∫ z, G s₀ z ∂(f s)) ≤ ε/2 := by
    rw [Real.dist_eq, key]
    calc |∫ z, (G s z - G s₀ z) ∂(f s)|
        ≤ ∫ z, |G s z - G s₀ z| ∂(f s) := by
            have h := norm_integral_le_integral_norm (μ := f s) (fun z => G s z - G s₀ z)
            simpa only [Real.norm_eq_abs] using h
      _ ≤ ∫ _z, (ε/2) ∂(f s) :=
            integral_mono (((hGint s s hs).sub (hGint s₀ s hs)).abs)
              (integrable_const _) hpoint
      _ = ε/2 := by simp
  have hsecond : dist (∫ z, G s₀ z ∂(f s)) (∫ z, G s₀ z ∂(f s₀)) < ε/2 :=
    hδ₂_prop hs hsd2
  calc dist (∫ z, G s z ∂(f s)) (∫ z, G s₀ z ∂(f s₀))
      ≤ dist (∫ z, G s z ∂(f s)) (∫ z, G s₀ z ∂(f s))
        + dist (∫ z, G s₀ z ∂(f s)) (∫ z, G s₀ z ∂(f s₀)) := dist_triangle _ _ _
    _ < ε/2 + ε/2 := add_lt_add_of_le_of_lt hfirst hsecond
    _ = ε := by ring

-- ── Helpers for `transportedIntegral_hasDerivAt_zero`, extracted from its proof body. ──

omit [NeZero d] in
/-- Per-`z` phase-space ODE of a characteristic flow on the open window, in
`vlasovVectorField` form. -/
lemma charFlow_ode_of_isCharacteristicFlowOn
    (gradW : PhysSpace d → PhysSpace d) (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d) (T : ℝ)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ) :
    ∀ z : PhaseSpace d, ∀ s' ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun s'' => (charX s'' z, charV s'' z))
        (vlasovVectorField gradW ρ s' (charX s' z, charV s' z)) s' := by
  intro z s' hs'
  have hX := hflow.2.1 s' hs' z (Set.mem_univ z)
  have hV := hflow.2.2 s' hs' z (Set.mem_univ z)
  simpa [vlasovVectorField] using hX.prodMk hV

omit [NeZero d] in
/-- A Fréchet derivative applied to a phase-space vector decomposes as inner
products against the two partial-gradient slices. -/
lemma fderiv_apply_eq_inner_gradientSlices (θ : PhaseSpace d → ℝ) (z : PhaseSpace d)
    (hθ : DifferentiableAt ℝ θ z) (p q : PhysSpace d) :
    (fderiv ℝ θ z) ((p, q) : PhaseSpace d)
      = @inner ℝ (PhysSpace d) _ p (gradient (fun x => θ (x, z.2)) z.1)
        + @inner ℝ (PhysSpace d) _ q (gradient (fun v => θ (z.1, v)) z.2) := by
  have hin_X : HasFDerivAt (fun x : PhysSpace d => ((x, z.2) : PhaseSpace d))
      (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) z.1 :=
    hasFDerivAt_prodMk_left z.1 z.2
  have hin_V : HasFDerivAt (fun v : PhysSpace d => ((z.1, v) : PhaseSpace d))
      (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) z.2 :=
    hasFDerivAt_prodMk_right z.1 z.2
  have hX_fd : HasFDerivAt (fun x => θ (x, z.2))
      ((fderiv ℝ θ z).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d))) z.1 := by
    have h := (hθ.hasFDerivAt).comp z.1 hin_X
    simpa only [Function.comp_def] using h
  have hV_fd : HasFDerivAt (fun v => θ (z.1, v))
      ((fderiv ℝ θ z).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d))) z.2 := by
    have h := (hθ.hasFDerivAt).comp z.2 hin_V
    simpa only [Function.comp_def] using h
  have hdecomp : (fderiv ℝ θ z) ((p, q) : PhaseSpace d)
      = (fderiv ℝ θ z) (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d) p)
        + (fderiv ℝ θ z) (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d) q) := by
    rw [ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, ← map_add]
    congr 1
    ext <;> simp
  have hX_inner : (fderiv ℝ θ z) (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d) p)
      = @inner ℝ (PhysSpace d) _ p (gradient (fun x => θ (x, z.2)) z.1) := by
    have hstep : (fderiv ℝ θ z) (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d) p)
        = fderiv ℝ (fun x => θ (x, z.2)) z.1 p := by rw [hX_fd.fderiv]; rfl
    rw [hstep, ← inner_gradient_left, real_inner_comm]
  have hV_inner : (fderiv ℝ θ z) (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d) q)
      = @inner ℝ (PhysSpace d) _ q (gradient (fun v => θ (z.1, v)) z.2) := by
    have hstep : (fderiv ℝ θ z) (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d) q)
        = fderiv ℝ (fun v => θ (z.1, v)) z.2 q := by rw [hV_fd.fderiv]; rfl
    rw [hstep, ← inner_gradient_left, real_inner_comm]
  rw [hdecomp, hX_inner, hV_inner]

/-- FTC bound on the linearization remainder of a real function: if `F` has
derivative `D r` along the segment and `D` stays within `ε` of `D s` there,
then `|F σ − F s − (σ−s)·D s| ≤ ε·|σ−s|`. -/
lemma abs_linearization_remainder_le (F D : ℝ → ℝ) (s σ ε : ℝ)
    (hderiv : ∀ r ∈ Set.uIcc s σ, HasDerivAt F (D r) r)
    (hD_cont : ContinuousOn D (Set.uIcc s σ))
    (hD_close : ∀ r ∈ Set.uIoc s σ, |D r - D s| ≤ ε) :
    |F σ - F s - (σ - s) * D s| ≤ ε * |σ - s| := by
  have hD_ii : IntervalIntegrable D MeasureTheory.volume s σ := hD_cont.intervalIntegrable
  have hFTC1 : ∫ r in s..σ, D r = F σ - F s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r hr => hderiv r hr) hD_ii
  have hFTC2 : ∫ _r in s..σ, D s = (σ - s) * D s := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  have hdiff : F σ - F s - (σ - s) * D s = ∫ r in s..σ, (D r - D s) := by
    rw [intervalIntegral.integral_sub hD_ii intervalIntegrable_const, hFTC1, hFTC2]
  rw [hdiff]
  have hbnd : ∀ r ∈ Set.uIoc s σ, ‖D r - D s‖ ≤ ε := fun r hr => by
    rw [Real.norm_eq_abs]; exact hD_close r hr
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
  rwa [Real.norm_eq_abs] at hle

omit [NeZero d] in
open Filter Topology Asymptotics in
/-- The transported-integral difference `σ ↦ ∫ ψ_σ d(f σ) − ∫ ψ_s d(f σ)` has
derivative `−Vb = ∫ D d(f s)` at `s`, from a uniform linearization of `r ↦ ψ_r`
(term `T1`) and narrow continuity of `σ ↦ ∫ D d(f σ)` (term `T2`). -/
lemma hasDerivAt_integral_sub_of_uniform_linearization
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (ψ : ℝ → PhaseSpace d → ℝ) (D : PhaseSpace d → ℝ) (s a b : ℝ)
    (hs_ab : s ∈ Set.Ioo a b)
    (hab_sub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T)
    (hψr_int : ∀ r ∈ Set.Icc a b, ∀ σ ∈ Set.Icc (0 : ℝ) T, Integrable (ψ r) (f σ))
    (hD_int : ∀ σ ∈ Set.Icc (0 : ℝ) T, Integrable D (f σ))
    (hunif : ∀ ε > 0, ∀ᶠ σ in 𝓝 s, ∀ z, |ψ σ z - ψ s z - (σ - s) * D z| ≤ ε * |σ - s|)
    (hnarrow : ContinuousWithinAt (fun σ => ∫ z, D z ∂(f σ)) (Set.Icc 0 T) s)
    (hsIoo : s ∈ Set.Ioo (0 : ℝ) T)
    (Vb : ℝ) (hVb : Vb = -∫ z, D z ∂(f s)) :
    HasDerivAt (fun σ => (∫ z, ψ σ z ∂(f σ)) - ∫ z, ψ s z ∂(f σ)) (-Vb) s := by
  rw [hasDerivAt_iff_isLittleO]
  have hT1 : (fun σ => ∫ z, (ψ σ z - ψ s z - (σ - s) * D z) ∂(f σ))
      =o[𝓝 s] (fun σ => σ - s) := by
    rw [isLittleO_iff]
    intro ε hε
    filter_upwards [hunif ε hε, isOpen_Ioo.mem_nhds hs_ab] with σ hunif_σ hσab
    have hσIcc : σ ∈ Set.Icc (0 : ℝ) T :=
      ⟨(hab_sub ⟨le_of_lt hσab.1, le_of_lt hσab.2⟩).1.le,
        (hab_sub ⟨le_of_lt hσab.1, le_of_lt hσab.2⟩).2.le⟩
    have hσab' : σ ∈ Set.Icc a b := ⟨le_of_lt hσab.1, le_of_lt hσab.2⟩
    have := (hf_mom σ hσIcc).1
    have hint : Integrable (fun z => ψ σ z - ψ s z - (σ - s) * D z) (f σ) :=
      ((hψr_int σ hσab' σ hσIcc).sub (hψr_int s
        ⟨le_of_lt hs_ab.1, le_of_lt hs_ab.2⟩ σ hσIcc)).sub ((hD_int σ hσIcc).const_mul _)
    calc ‖∫ z, (ψ σ z - ψ s z - (σ - s) * D z) ∂(f σ)‖
        ≤ ∫ z, ‖ψ σ z - ψ s z - (σ - s) * D z‖ ∂(f σ) := norm_integral_le_integral_norm _
      _ ≤ ∫ _z, ε * |σ - s| ∂(f σ) :=
          integral_mono hint.norm (integrable_const _)
            (fun z => by simpa only [Real.norm_eq_abs] using hunif_σ z)
      _ = ε * |σ - s| := by simp
      _ = ε * ‖σ - s‖ := by rw [Real.norm_eq_abs]
  have hE : Tendsto (fun σ => (∫ z, D z ∂(f σ)) - ∫ z, D z ∂(f s)) (𝓝 s) (𝓝 0) := by
    have hcont := hnarrow.continuousAt (Icc_mem_nhds hsIoo.1 hsIoo.2)
    have h2 : Tendsto (fun σ => (∫ z, D z ∂(f σ)) - ∫ z, D z ∂(f s)) (𝓝 s)
        (𝓝 ((∫ z, D z ∂(f s)) - ∫ z, D z ∂(f s))) := hcont.tendsto.sub tendsto_const_nhds
    rwa [sub_self] at h2
  have hT2 : (fun σ => (σ - s) * ((∫ z, D z ∂(f σ)) - ∫ z, D z ∂(f s)))
      =o[𝓝 s] (fun σ => σ - s) := by
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp hE ε hε] with σ hσ
    have hEσ : ‖(∫ z, D z ∂(f σ)) - ∫ z, D z ∂(f s)‖ ≤ ε := by
      rw [Real.norm_eq_abs]; rw [Real.dist_eq, sub_zero] at hσ; exact le_of_lt hσ
    calc ‖(σ - s) * ((∫ z, D z ∂(f σ)) - ∫ z, D z ∂(f s))‖
        = ‖σ - s‖ * ‖(∫ z, D z ∂(f σ)) - ∫ z, D z ∂(f s)‖ := norm_mul _ _
      _ ≤ ‖σ - s‖ * ε := by gcongr
      _ = ε * ‖σ - s‖ := by ring
  refine (hT1.add hT2).congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [isOpen_Ioo.mem_nhds hs_ab] with σ hσab
  have hσIcc : σ ∈ Set.Icc (0 : ℝ) T :=
    ⟨(hab_sub ⟨le_of_lt hσab.1, le_of_lt hσab.2⟩).1.le,
      (hab_sub ⟨le_of_lt hσab.1, le_of_lt hσab.2⟩).2.le⟩
  have hσab' : σ ∈ Set.Icc a b := ⟨le_of_lt hσab.1, le_of_lt hσab.2⟩
  have := (hf_mom σ hσIcc).1
  have hi1 : Integrable (ψ σ) (f σ) := hψr_int σ hσab' σ hσIcc
  have hi2 : Integrable (ψ s) (f σ) := hψr_int s ⟨le_of_lt hs_ab.1, le_of_lt hs_ab.2⟩ σ hσIcc
  have hi3 : Integrable D (f σ) := hD_int σ hσIcc
  have hia : Integrable (fun z => ψ σ z - ψ s z) (f σ) := hi1.sub hi2
  have hib : Integrable (fun z => (σ - s) * D z) (f σ) := hi3.const_mul _
  have hL1 : ∫ z, (ψ σ z - ψ s z - (σ - s) * D z) ∂(f σ)
      = (∫ z, ψ σ z ∂(f σ)) - (∫ z, ψ s z ∂(f σ)) - (σ - s) * ∫ z, D z ∂(f σ) := by
    rw [integral_sub hia hib, integral_sub hi1 hi2, integral_const_mul]
  rw [hL1, hVb]
  simp only [smul_eq_mul]
  ring

open Filter Topology Asymptotics in
omit [NeZero d] in
/-- **#6a (Step 6, the diagonal chain rule) — `s ↦ ∫ ψ_s d(f s)` has zero `σ`-derivative.**

The analytic heart of the dual core: for the backward-transported test
`ψ_σ(w) := φ(Φ_t(Ψ_σ w))`, the diagonal map `I(σ) := ∫ ψ_σ d(f σ)` (both the integrand *and* the
measure move with `σ`) has `HasDerivAt I 0` on `Ioo 0 t`.  The two `σ`-dependencies cancel.

Strategy (the measure `f` is a bare weak solution, so there is no joint Fréchet structure to lean
on — the two partials are combined by hand):
* Split `I = Bint + q` with `Bint σ := ∫ ψ_s d(f σ)` (integrand frozen at `s`) and
  `q σ := ∫ (ψ_σ − ψ_s) d(f σ)`.
* `HasDerivAt Bint Vb s` via the `C¹_c`-extended weak equation `weakEvolution_test_C1c_On` (#4)
  tested against the fixed `C¹_c` function `ψ_s` (this is why #4 had to land first).
* `HasDerivAt q (−Vb) s` via the little-o definition: writing
  `DQ_r z := ∂_r ψ_r(z)`, the remainder splits as `T1 + T2` where
  `T1 = ∫ (ψ_σ − ψ_s − (σ−s)·DQ_s) d(f σ)` is `o(σ−s)` by **uniform differentiability of `r ↦ ψ_r`
  over a fixed compact `K`** (FTC + Heine–Cantor; `K` is the flow image of `[a,b] × Ψ_t(tsupport φ)`
  — this is what `hflowjoint` is for: bounding the *moving* support of `ψ_r`), and
  `T2 = (σ−s)·(∫ DQ_s d(f σ) − ∫ DQ_s d(f s))` is `o(σ−s)` by narrow continuity (`hf_narrow`).
* The cancellation `Vb = −∫ DQ_s d(f s)` comes from the Step-4 transport identity
  (`transportedTest_transport_identity`, giving `DQ_s = −(fderiv ψ_s)·b_s`) composed with the
  gradient↔fderiv partial decomposition (matching #4's RHS). -/
theorem transportedIntegral_hasDerivAt_zero
    (gradW : PhysSpace d → PhysSpace d)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ)
    (hf_weak : IsVlasovSolutionOn gradW f T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hf_narrow : ∀ (g : PhaseSpace d → ℝ), Continuous g → HasCompactSupport g →
      ContinuousOn (fun s => ∫ z, g z ∂(f s)) (Set.Icc 0 T))
    -- B2 enrichment: threaded through to `weakEvolution_test_C1c_On` (#4), whose mollification
    -- proof needs the uniform field bound (`hL` + `hM_ρ`).
    (L : NNReal) (hL : LipschitzWith L gradW)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M_ρ)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow : IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f t)) charX charV
      (Set.Ioo 0 T) Set.univ)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (φ : PhaseSpace d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (Ψ : ℝ → PhaseSpace d → PhaseSpace d)
    (hΨ_left : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      Function.LeftInverse (Ψ s) (fun z => (charX s z, charV s z)))
    (hΨ_right : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      Function.RightInverse (Ψ s) (fun z => (charX s z, charV s z)))
    (hΨ_C1 : ContDiffOn ℝ 1 (fun p : ℝ × PhaseSpace d => Ψ p.1 p.2)
      (Set.Ioo 0 T ×ˢ Set.univ))
    (hΦt_C1 : ContDiff ℝ 1 (fun z : PhaseSpace d => (charX t z, charV t z)))
    -- B2 enrichment: joint flow continuity gives a fixed compact containing tsupport(ψ_r) for all
    -- `r` near `s` (the moving support of the transported test), needed for the uniform
    -- differentiability over a fixed compact in the little-o argument.
    (hflowjoint : ContinuousOn (fun p : ℝ × PhaseSpace d => (charX p.1 p.2, charV p.1 p.2))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhaseSpace d))))
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) t) :
    HasDerivAt (fun σ => ∫ z, φ (charX t (Ψ σ z), charV t (Ψ σ z)) ∂(f σ)) 0 s := by
  classical
  have hsIoo : s ∈ Set.Ioo (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 ht.2⟩
  have hopen : IsOpen (Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d))) :=
    isOpen_Ioo.prod isOpen_univ
  -- the uncurried two-time test g and its slice ψ
  set g : ℝ × PhaseSpace d → ℝ :=
    fun p => φ (charX t (Ψ p.1 p.2), charV t (Ψ p.1 p.2)) with hg_def
  set ψ : ℝ → PhaseSpace d → ℝ :=
    fun r w => φ (charX t (Ψ r w), charV t (Ψ r w)) with hψ_def
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hg_cd : ContDiffOn ℝ 1 g (Set.Ioo 0 T ×ˢ Set.univ) :=
    hφ1.comp_contDiffOn (twoTimeFlow_contDiffOn_joint charX charV T t Ψ hΨ_C1 hΦt_C1)
  ---------------------------------------------------------------------------
  -- closed neighbourhood [a,b] ⊂ Ioo 0 T of s
  obtain ⟨a, b, hab_lt, hs_ab, hab_sub⟩ :
      ∃ a b, a < b ∧ s ∈ Set.Ioo a b ∧ Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T := by
    refine ⟨s/2, (s+T)/2, by linarith [hsIoo.1, hsIoo.2],
      ⟨by linarith [hsIoo.1], by linarith [hsIoo.2]⟩, fun r hr => ⟨?_, ?_⟩⟩
    · linarith [hsIoo.1, hr.1]
    · linarith [hsIoo.2, hr.2]
  ---------------------------------------------------------------------------
  -- Ψ_t continuous, support set C, fixed compact K
  have hΨt_cont : Continuous (fun w : PhaseSpace d => Ψ t w) := by
    have hc : Continuous (fun w : PhaseSpace d => ((t, w) : ℝ × PhaseSpace d)) :=
      continuous_const.prodMk continuous_id
    exact hΨ_C1.continuousOn.comp_continuous hc (fun w => ⟨ht, Set.mem_univ _⟩)
  set C : Set (PhaseSpace d) := (fun w => Ψ t w) '' (tsupport φ) with hC_def
  have hC_compact : IsCompact C := hφc.image hΨt_cont
  set K : Set (PhaseSpace d) :=
    (fun p : ℝ × PhaseSpace d => (charX p.1 p.2, charV p.1 p.2)) '' (Set.Icc a b ×ˢ C) with hK_def
  have hsub_abC : Set.Icc a b ×ˢ C ⊆ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d)) :=
    fun p hp => ⟨⟨(hab_sub hp.1).1.le, (hab_sub hp.1).2.le⟩, Set.mem_univ _⟩
  have hK_compact : IsCompact K :=
    (isCompact_Icc.prod hC_compact).image_of_continuousOn (hflowjoint.mono hsub_abC)
  -- support confinement: ψ r z ≠ 0 ⟹ z ∈ K  (for r ∈ [a,b])
  have hsupp : ∀ r ∈ Set.Icc a b, ∀ z, ψ r z ≠ 0 → z ∈ K := by
    intro r hr z hz
    have hrIoo : r ∈ Set.Ioo 0 T := hab_sub hr
    have hmem : (charX t (Ψ r z), charV t (Ψ r z)) ∈ tsupport φ :=
      subset_tsupport _ (by simpa [Function.mem_support] using hz)
    have hΨrz_C : Ψ r z ∈ C := ⟨(charX t (Ψ r z), charV t (Ψ r z)), hmem, hΨ_left t ht (Ψ r z)⟩
    exact ⟨(r, Ψ r z), ⟨hr, hΨrz_C⟩, hΨ_right r hrIoo z⟩
  ---------------------------------------------------------------------------
  -- the r-directional derivative DQ of ψ, and its properties
  set DQ : ℝ → PhaseSpace d → ℝ :=
    fun r z => fderiv ℝ g (r, z) ((1:ℝ), (0:PhaseSpace d)) with hDQ_def
  have hg_hasfderiv : ∀ p ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d)),
      HasFDerivAt g (fderiv ℝ g p) p := fun p hp =>
    (hg_cd.differentiableOn_one.differentiableAt (hopen.mem_nhds hp)).hasFDerivAt
  have hψ_deriv : ∀ r ∈ Set.Ioo (0 : ℝ) T, ∀ z, HasDerivAt (fun r' => ψ r' z) (DQ r z) r := by
    intro r hr z
    have hcurve : HasDerivAt (fun r' => ((r', z) : ℝ × PhaseSpace d)) ((1:ℝ), (0:PhaseSpace d)) r :=
      (hasDerivAt_id r).prodMk (hasDerivAt_const r z)
    have := (hg_hasfderiv (r, z) ⟨hr, Set.mem_univ _⟩).comp_hasDerivAt r hcurve
    simpa only [Function.comp_def] using this
  -- DQ continuous on the open window, hence uniformly continuous on Icc a b ×ˢ K
  have hDQ_contOn : ContinuousOn (fun p : ℝ × PhaseSpace d => DQ p.1 p.2)
      (Set.Ioo 0 T ×ˢ Set.univ) := by
    have hfd := hg_cd.continuousOn_fderiv_of_isOpen hopen le_rfl
    have heval : Continuous
        (fun M : (ℝ × PhaseSpace d) →L[ℝ] ℝ => M ((1:ℝ), (0:PhaseSpace d))) :=
      (ContinuousLinearMap.apply ℝ ℝ ((1:ℝ), (0:PhaseSpace d))).continuous
    exact heval.comp_continuousOn hfd
  have hDQ_uc : UniformContinuousOn (fun p : ℝ × PhaseSpace d => DQ p.1 p.2)
      (Set.Icc a b ×ˢ K) :=
    (isCompact_Icc.prod hK_compact).uniformContinuousOn_of_continuous
      (hDQ_contOn.mono (fun p hp => ⟨hab_sub hp.1, Set.mem_univ _⟩))
  rw [Metric.uniformContinuousOn_iff] at hDQ_uc
  -- DQ s vanishes off K
  have hDQ_zero : ∀ z ∉ K, DQ s z = 0 := by
    intro z hzK
    have h0 : HasDerivAt (fun r' => ψ r' z) 0 s := by
      have hconst : (fun r' => ψ r' z) =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hs_ab] with r' hr'
        by_contra h
        exact hzK (hsupp r' ⟨le_of_lt hr'.1, le_of_lt hr'.2⟩ z h)
      exact (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hconst
    exact (hψ_deriv s hsIoo z).unique h0
  ---------------------------------------------------------------------------
  -- continuity / integrability bookkeeping
  have hψr_cont : ∀ r ∈ Set.Ioo (0 : ℝ) T, Continuous (ψ r) := fun r hr =>
    hg_cd.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun w => ⟨hr, Set.mem_univ _⟩)
  have hψr_cs : ∀ r ∈ Set.Icc a b, HasCompactSupport (ψ r) := by
    intro r hr
    apply hK_compact.of_isClosed_subset (isClosed_tsupport _)
    exact closure_minimal (fun z hz => hsupp r hr z (Function.mem_support.mp hz))
      hK_compact.isClosed
  have hψr_int : ∀ r ∈ Set.Icc a b, ∀ σ ∈ Set.Icc (0 : ℝ) T, Integrable (ψ r) (f σ) := by
    intro r hr σ hσ
    have := (hf_mom σ hσ).1
    exact (hψr_cont r (hab_sub hr)).integrable_of_hasCompactSupport (hψr_cs r hr)
  have hDQs_cont : Continuous (DQ s) :=
    hDQ_contOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun z => ⟨hsIoo, Set.mem_univ _⟩)
  have hDQs_cs : HasCompactSupport (DQ s) := by
    apply hK_compact.of_isClosed_subset (isClosed_tsupport _)
    refine closure_minimal (fun z hz => ?_) hK_compact.isClosed
    by_contra hzK
    exact (Function.mem_support.mp hz) (hDQ_zero z hzK)
  have hDQs_int : ∀ σ ∈ Set.Icc (0 : ℝ) T, Integrable (DQ s) (f σ) := by
    intro σ hσ
    have := (hf_mom σ hσ).1
    exact hDQs_cont.integrable_of_hasCompactSupport hDQs_cs
  have hnarrow : ContinuousWithinAt (fun σ => ∫ z, DQ s z ∂(f σ)) (Set.Icc 0 T) s :=
    (hf_narrow (DQ s) hDQs_cont hDQs_cs) s ⟨hsIoo.1.le, hsIoo.2.le⟩
  ---------------------------------------------------------------------------
  -- the two-sided ODE on Ioo (feeds 4b)
  have hflow_ode := charFlow_ode_of_isCharacteristicFlowOn gradW
    (fun τ => spatialMarginal (f τ)) charX charV T hflow
  ---------------------------------------------------------------------------
  -- the #4 derivative of the fixed-integrand integral  Bint σ = ∫ ψ_s d(f σ)
  set gXψs : PhaseSpace d → PhysSpace d := fun z => gradient (fun x => ψ s (x, z.2)) z.1
    with hgX_def
  set gVψs : PhaseSpace d → PhysSpace d := fun z => gradient (fun v => ψ s (z.1, v)) z.2
    with hgV_def
  set field_s : PhysSpace d → PhysSpace d :=
    fun x => convolveFunctionMeasure gradW (spatialMarginal (f s)) x with hfield_def
  have hψs_C1 : ContDiff ℝ 1 (ψ s) := by
    rw [contDiff_iff_contDiffAt]
    intro w
    exact (hg_cd.contDiffAt (hopen.mem_nhds ⟨hsIoo, Set.mem_univ _⟩)).comp w
      (contDiffAt_const.prodMk contDiffAt_id)
  have hψs_cs : HasCompactSupport (ψ s) := hψr_cs s ⟨le_of_lt hs_ab.1, le_of_lt hs_ab.2⟩
  set Vb : ℝ := ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gXψs z)
      - @inner ℝ (PhysSpace d) _ (field_s z.1) (gVψs z)) ∂(f s) with hVb_def
  have hBint : HasDerivAt (fun σ => ∫ z, ψ s z ∂(f σ)) Vb s :=
    weakEvolution_test_C1c_On gradW f T hf_weak hf_mom L hL M_ρ hM_ρ_nn hM_ρ
      (ψ s) hψs_C1 hψs_cs gXψs gVψs (fun z => rfl) (fun z => rfl) s hsIoo
  ---------------------------------------------------------------------------
  -- the cancellation identity  Vb = - ∫ DQ_s d(f s)
  have hpt : ∀ z, DQ s z = -(@inner ℝ (PhysSpace d) _ z.2 (gXψs z)
      - @inner ℝ (PhysSpace d) _ (field_s z.1) (gVψs z)) := by
    intro z
    have h4b := transportedTest_transport_identity gradW (fun τ => spatialMarginal (f τ))
      charX charV T t φ hφ Ψ hΨ_left hΨ_right hΨ_C1 hΦt_C1 hflow_ode s hsIoo z
    have huniq : DQ s z
        = -(fderiv ℝ (fun w' : PhaseSpace d => φ (charX t (Ψ s w'), charV t (Ψ s w'))) z)
            (vlasovVectorField gradW (fun τ => spatialMarginal (f τ)) s z) :=
      (hψ_deriv s hsIoo z).unique h4b
    rw [huniq]
    congr 1
    -- bridge:  (fderiv (ψ s) z)(b_s z) = ⟪z.2, gXψs z⟫ - ⟪field_s z.1, gVψs z⟫
    have hb : vlasovVectorField gradW (fun τ => spatialMarginal (f τ)) s z
        = ((z.2 : PhysSpace d), (-field_s z.1 : PhysSpace d)) := rfl
    rw [hb]
    have hdiffφ : DifferentiableAt ℝ (ψ s) z := hψs_C1.differentiable (by norm_num) z
    rw [fderiv_apply_eq_inner_gradientSlices (ψ s) z hdiffφ z.2 (-field_s z.1)]
    simp only [hgX_def, hgV_def]
    rw [inner_neg_left]
    ring
  have hcancel : Vb = - ∫ z, DQ s z ∂(f s) := by
    have heq : ∫ z, DQ s z ∂(f s) = ∫ z, -(@inner ℝ (PhysSpace d) _ z.2 (gXψs z)
        - @inner ℝ (PhysSpace d) _ (field_s z.1) (gVψs z)) ∂(f s) :=
      integral_congr_ae (Eventually.of_forall hpt)
    rw [heq, integral_neg, ← hVb_def, neg_neg]
  ---------------------------------------------------------------------------
  -- uniform differentiability of ψ in r over K, near s
  have hunif : ∀ ε > 0, ∀ᶠ σ in 𝓝 s,
      ∀ z, |ψ σ z - ψ s z - (σ - s) * DQ s z| ≤ ε * |σ - s| := by
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := hDQ_uc ε hε
    filter_upwards [Metric.ball_mem_nhds s hδpos, isOpen_Ioo.mem_nhds hs_ab] with σ hσδ hσab
    rw [Metric.mem_ball] at hσδ
    intro z
    have hσab' : σ ∈ Set.Icc a b := ⟨le_of_lt hσab.1, le_of_lt hσab.2⟩
    have hs_ab' : s ∈ Set.Icc a b := ⟨le_of_lt hs_ab.1, le_of_lt hs_ab.2⟩
    have hseg : Set.uIcc s σ ⊆ Set.Ioo (0 : ℝ) T := fun r hr =>
      hab_sub (Set.uIcc_subset_Icc hs_ab' hσab' hr)
    by_cases hzK : z ∈ K
    · -- FTC route via `abs_linearization_remainder_le`; the ε-closeness of `DQ · z`
      -- along the segment comes from uniform continuity on `[a,b] × K`.
      have hD_close : ∀ r ∈ Set.uIoc s σ, |DQ r z - DQ s z| ≤ ε := by
        intro r hr
        have hr_uIcc : r ∈ Set.uIcc s σ := Set.uIoc_subset_uIcc hr
        have hrab : r ∈ Set.Icc a b := Set.uIcc_subset_Icc hs_ab' hσab' hr_uIcc
        have habs : |r - s| ≤ |σ - s| := by
          rcases le_total s σ with hsσ | hσs
          · rw [Set.uIcc_of_le hsσ] at hr_uIcc
            rw [abs_of_nonneg (by linarith [hr_uIcc.1] : (0 : ℝ) ≤ r - s),
                abs_of_nonneg (by linarith : (0 : ℝ) ≤ σ - s)]
            linarith [hr_uIcc.2]
          · rw [Set.uIcc_of_ge hσs] at hr_uIcc
            rw [abs_of_nonpos (by linarith [hr_uIcc.2] : r - s ≤ 0),
                abs_of_nonpos (by linarith : σ - s ≤ 0)]
            linarith [hr_uIcc.1]
        have hdist : dist ((r, z) : ℝ × PhaseSpace d) (s, z) < δ := by
          rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq]
          calc |r - s| ≤ |σ - s| := habs
            _ = dist σ s := (Real.dist_eq σ s).symm
            _ < δ := hσδ
        have hlt := hδ (r, z) ⟨hrab, hzK⟩ (s, z) ⟨hs_ab', hzK⟩ hdist
        rw [Real.dist_eq] at hlt
        exact le_of_lt hlt
      have hmapsTo : Set.MapsTo (fun r => ((r, z) : ℝ × PhaseSpace d)) (Set.uIcc s σ)
          (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := fun r hr => ⟨hseg hr, Set.mem_univ _⟩
      exact abs_linearization_remainder_le (fun r => ψ r z) (fun r => DQ r z) s σ ε
        (fun r hr => hψ_deriv r (hseg hr) z)
        (hDQ_contOn.comp (continuous_id.prodMk continuous_const).continuousOn hmapsTo)
        hD_close
    · have hψσ : ψ σ z = 0 := by
        by_contra h
        exact hzK (hsupp σ ⟨le_of_lt hσab.1, le_of_lt hσab.2⟩ z h)
      have hψs0 : ψ s z = 0 := by
        by_contra h
        exact hzK (hsupp s ⟨le_of_lt hs_ab.1, le_of_lt hs_ab.2⟩ z h)
      rw [hψσ, hψs0, hDQ_zero z hzK]
      simp only [sub_zero, mul_zero, abs_zero]
      positivity
  ---------------------------------------------------------------------------
  -- the q-derivative  q σ = ∫ ψ_σ d(f σ) - ∫ ψ_s d(f σ)  has derivative  -Vb
  have hq : HasDerivAt (fun σ => (∫ z, ψ σ z ∂(f σ)) - ∫ z, ψ s z ∂(f σ)) (-Vb) s :=
    hasDerivAt_integral_sub_of_uniform_linearization f T hf_mom ψ (DQ s) s a b
      hs_ab hab_sub hψr_int hDQs_int hunif hnarrow hsIoo Vb hcancel
  ---------------------------------------------------------------------------
  -- assemble the diagonal
  have hfinal : HasDerivAt (fun σ => ∫ z, ψ σ z ∂(f σ)) (-Vb + Vb) s := by
    refine (hq.add hBint).congr_of_eventuallyEq (Eventually.of_forall fun σ => ?_)
    simp only [Pi.add_apply]; ring
  rw [neg_add_cancel] at hfinal
  exact hfinal

-- #6b: the transported integral (with the s=0 endpoint patched to the RHS value) is
-- continuous on the closed interval [0,t].
open Filter Topology in
omit [NeZero d] in
theorem transportedIntegral_continuousOn
    (gradW : PhysSpace d → PhysSpace d)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hf_narrow : ∀ (g : PhaseSpace d → ℝ), Continuous g → HasCompactSupport g →
      ContinuousOn (fun s => ∫ z, g z ∂(f s)) (Set.Icc 0 T))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow : IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f t)) charX charV
      (Set.Ioo 0 T) Set.univ)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (φ : PhaseSpace d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (Ψ : ℝ → PhaseSpace d → PhaseSpace d)
    (hΨ_left : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      Function.LeftInverse (Ψ s) (fun z => (charX s z, charV s z)))
    (hΨ_right : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      Function.RightInverse (Ψ s) (fun z => (charX s z, charV s z)))
    (hΨ_C1 : ContDiffOn ℝ 1 (fun p : ℝ × PhaseSpace d => Ψ p.1 p.2)
      (Set.Ioo 0 T ×ˢ Set.univ))
    (hΦt_C1 : ContDiff ℝ 1 (fun z : PhaseSpace d => (charX t z, charV t z)))
    (L : NNReal)
    (hflowjoint : ContinuousOn (fun p : ℝ × PhaseSpace d => (charX p.1 p.2, charV p.1 p.2))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhaseSpace d))))
    (hanti : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
      dist z₁ z₂ ≤ dist ((charX s z₁, charV s z₁) : PhaseSpace d) (charX s z₂, charV s z₂)
        * Real.exp (((max 1 L : NNReal) : ℝ) * s)) :
    ContinuousOn (fun s => if s = 0 then ∫ z, φ (charX t z, charV t z) ∂(f 0)
        else ∫ z, φ (charX t (Ψ s z), charV t (Ψ s z)) ∂(f s)) (Set.Icc (0 : ℝ) t) := by
  classical
  have hT0 : (0 : ℝ) < T := lt_trans ht.1 ht.2
  -- the terminal map and the transported integrand g = φ ∘ Φ_t
  have hΦt_cont : Continuous (fun z : PhaseSpace d => (charX t z, charV t z)) := hΦt_C1.continuous
  set g : PhaseSpace d → ℝ := fun z => φ (charX t z, charV t z) with hg_def
  have hg_cont : Continuous g := hφ.continuous.comp hΦt_cont
  -- Ψ_t continuous (t-slice of the joint C¹ inverse) and the support set S := Ψ_t '' (tsupport φ)
  have htIoo : t ∈ Set.Ioo (0 : ℝ) T := ht
  have hΨt_cont : Continuous (fun z => Ψ t z) := by
    have hcont_on : ContinuousOn (fun p : ℝ × PhaseSpace d => Ψ p.1 p.2)
        (Set.Ioo 0 T ×ˢ Set.univ) := hΨ_C1.continuousOn
    have : Continuous (fun z : PhaseSpace d => (t, z)) := continuous_const.prodMk continuous_id
    refine (hcont_on.comp_continuous this (fun z => ?_))
    exact ⟨ht, Set.mem_univ _⟩
  set S : Set (PhaseSpace d) := (fun z => Ψ t z) '' (tsupport φ) with hS_def
  have hS_compact : IsCompact S := hφc.image hΨt_cont
  -- g is supported in S, hence has compact support
  have hg_supp_S : ∀ z ∉ S, g z = 0 := by
    intro z hz
    by_contra hgz
    -- g z ≠ 0 ⟹ (charX t z, charV t z) ∈ support φ ⊆ tsupport φ ⟹ z = Ψ_t(Φ_t z) ∈ S
    have hφne : φ (charX t z, charV t z) ≠ 0 := hgz
    have hmem : (charX t z, charV t z) ∈ tsupport φ :=
      subset_tsupport _ (by simpa [Function.mem_support] using hφne)
    have hzeq : Ψ t (charX t z, charV t z) = z := hΨ_left t ht z
    exact hz ⟨(charX t z, charV t z), hmem, hzeq⟩
  have hg_csupp : HasCompactSupport g := by
    have hsub : tsupport g ⊆ S :=
      closure_minimal (fun z hz => by
        by_contra hzS; exact hz (hg_supp_S z hzS)) hS_compact.isClosed
    exact hS_compact.of_isClosed_subset (isClosed_tsupport _) hsub
  have hg_unif : UniformContinuous g := hg_csupp.uniformContinuous_of_continuous hg_cont
  -- the initial condition Φ_0 = id (from hflow.1)
  have hinit : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z := fun z =>
    Prod.ext (hflow.1 z (Set.mem_univ z)).1 (hflow.1 z (Set.mem_univ z)).2
  -- clamp u : ℝ → ℝ into [0,t]
  set u : ℝ → ℝ := fun s => max 0 (min s t) with hu_def
  have hu_cont : Continuous u := continuous_const.max (continuous_id.min continuous_const)
  have hu0 : u 0 = 0 := by simp [hu_def, min_eq_left ht.1.le]
  have hu_lb : ∀ s, 0 ≤ u s := fun s => le_max_left _ _
  have hu_ub : ∀ s, u s ≤ T := fun s =>
    max_le hT0.le (le_trans (min_le_right _ _) ht.2.le)
  have hu_pos_of_pos : ∀ s, 0 < s → u s = min s t := by
    intro s hs
    have : 0 ≤ min s t := le_min hs.le ht.1.le
    simp [hu_def, max_eq_right this]
  -- the globally-continuous, uniformly-compactly-supported integrand G'
  set G' : ℝ → PhaseSpace d → ℝ := fun s z => if s ≤ 0 then g z else g (Ψ (min s t) z) with hG'_def
  -- (A) joint flow tendsto used at the s=0 seam: (p ↦ Φ_{u p.1} p.2) → z₀
  have hΦu_tendsto : ∀ z₀ : PhaseSpace d,
      Tendsto (fun p : ℝ × PhaseSpace d => (charX (u p.1) p.2, charV (u p.1) p.2))
        (𝓝 (0, z₀)) (𝓝 z₀) := by
    intro z₀
    have hcwa : ContinuousWithinAt (fun q : ℝ × PhaseSpace d => (charX q.1 q.2, charV q.1 q.2))
        (Set.Icc 0 T ×ˢ Set.univ) (0, z₀) :=
      hflowjoint (0, z₀) ⟨⟨le_refl 0, hT0.le⟩, Set.mem_univ _⟩
    have hval : (charX 0 z₀, charV 0 z₀) = z₀ := hinit z₀
    have hinner : Tendsto (fun p : ℝ × PhaseSpace d => (u p.1, p.2))
        (𝓝 (0, z₀)) (𝓝[Set.Icc 0 T ×ˢ Set.univ] (0, z₀)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall (fun p => ⟨⟨hu_lb p.1, hu_ub p.1⟩, Set.mem_univ _⟩)⟩
      have hc : Continuous (fun p : ℝ × PhaseSpace d => (u p.1, p.2)) :=
        (hu_cont.comp continuous_fst).prodMk continuous_snd
      exact hc.tendsto' (0, z₀) (0, z₀) (by simp [hu0])
    have hcomp := (hval ▸ hcwa.tendsto).comp hinner
    simpa [Function.comp_def] using hcomp
  -- (B) G' is globally continuous
  have hG'_cont : Continuous (fun p : ℝ × PhaseSpace d => G' p.1 p.2) := by
    rw [continuous_iff_continuousAt]
    rintro ⟨s₀, z₀⟩
    rcases lt_trichotomy s₀ 0 with hs₀ | hs₀ | hs₀
    · -- s₀ < 0: locally G' = g ∘ snd
      have heq : (fun p : ℝ × PhaseSpace d => G' p.1 p.2) =ᶠ[𝓝 (s₀, z₀)]
          (fun p => g p.2) := by
        have hmem : {p : ℝ × PhaseSpace d | p.1 < 0} ∈ 𝓝 (s₀, z₀) :=
          (isOpen_lt continuous_fst continuous_const).mem_nhds hs₀
        filter_upwards [hmem] with p hp
        simp only [hG'_def, ite_eq_left hp.le]
      exact (hg_cont.comp continuous_snd).continuousAt.congr heq.symm
    · -- s₀ = 0: the confinement seam
      subst hs₀
      rw [ContinuousAt]
      have hval0 : G' (0 : ℝ) z₀ = g z₀ := by simp [hG'_def]
      change Tendsto (fun p : ℝ × PhaseSpace d => G' p.1 p.2) (𝓝 ((0 : ℝ), z₀)) (𝓝 (G' 0 z₀))
      rw [hval0, Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuous_iff.mp hg_unif ε hε
      -- eventually: dist(p.2, z₀) < δ/2  and  exp(K u p.1)·dist(p.2, Φ_{u p.1} p.2) < δ/2
      have hKpos : (0 : ℝ) < δ/2 := by positivity
      have hfact1 : ∀ᶠ p : ℝ × PhaseSpace d in 𝓝 (0, z₀), dist p.2 z₀ < δ/2 := by
        have : Tendsto (fun p : ℝ × PhaseSpace d => p.2) (𝓝 (0, z₀)) (𝓝 z₀) :=
          continuous_snd.continuousAt
        exact (Metric.tendsto_nhds.mp this) (δ/2) hKpos
      have hfact2 : ∀ᶠ p : ℝ × PhaseSpace d in 𝓝 (0, z₀),
          Real.exp (((max 1 L : NNReal) : ℝ) * u p.1) *
            dist p.2 (charX (u p.1) p.2, charV (u p.1) p.2)
            < δ/2 := by
        have hd : Tendsto (fun p : ℝ × PhaseSpace d =>
            Real.exp (((max 1 L : NNReal) : ℝ) * u p.1)
              * dist p.2 (charX (u p.1) p.2, charV (u p.1) p.2)) (𝓝 (0, z₀)) (𝓝 0) := by
          have hexp : Tendsto (fun p : ℝ × PhaseSpace d =>
              Real.exp (((max 1 L : NNReal) : ℝ) * u p.1)) (𝓝 (0, z₀))
              (𝓝 (Real.exp (((max 1 L : NNReal) : ℝ) * u 0))) :=
            ((Real.continuous_exp.comp (continuous_const.mul (hu_cont.comp continuous_fst))))
              |>.continuousAt.tendsto
          have hdist : Tendsto (fun p : ℝ × PhaseSpace d =>
              dist p.2 (charX (u p.1) p.2, charV (u p.1) p.2)) (𝓝 (0, z₀)) (𝓝 0) := by
            have h2 : Tendsto (fun p : ℝ × PhaseSpace d => p.2) (𝓝 (0, z₀)) (𝓝 z₀) :=
              continuous_snd.continuousAt
            have := (h2.dist (hΦu_tendsto z₀))
            simpa using this
          have := hexp.mul hdist
          simpa [hu0] using this
        filter_upwards [(Metric.tendsto_nhds.mp hd) (δ/2) hKpos] with p hp
        rwa [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hp
      filter_upwards [hfact1, hfact2] with p hp1 hp2
      by_cases hps : p.1 ≤ 0
      · -- branch g p.2
        simp only [hG'_def, ite_eq_left hps]
        exact hδg (lt_of_lt_of_le hp1 (by linarith))
      · -- branch g (Ψ (min p.1 t) p.2)
        rw [not_le] at hps
        have humin : u p.1 = min p.1 t := hu_pos_of_pos p.1 hps
        have hminIoo : min p.1 t ∈ Set.Ioo (0 : ℝ) T :=
          ⟨lt_min hps ht.1, lt_of_le_of_lt (min_le_right _ _) ht.2⟩
        simp only [hG'_def, ite_eq_right (not_le.mpr hps)]
        apply hδg
        -- dist (Ψ (min p.1 t) p.2) z₀ < δ
        have hright : (charX (min p.1 t) (Ψ (min p.1 t) p.2),
            charV (min p.1 t) (Ψ (min p.1 t) p.2)) = p.2 := hΨ_right (min p.1 t) hminIoo p.2
        have hbound : dist (Ψ (min p.1 t) p.2) p.2
            ≤ dist p.2 (charX (u p.1) p.2, charV (u p.1) p.2)
              * Real.exp (((max 1 L : NNReal) : ℝ) * (min p.1 t)) := by
          have hkey := hanti (min p.1 t) hminIoo (Ψ (min p.1 t) p.2) p.2
          rw [hright] at hkey
          rw [humin]
          exact hkey
        calc dist (Ψ (min p.1 t) p.2) z₀
            ≤ dist (Ψ (min p.1 t) p.2) p.2 + dist p.2 z₀ := dist_triangle _ _ _
          _ < δ/2 + δ/2 := by
              refine add_lt_add_of_le_of_lt ?_ hp1
              refine le_of_lt (lt_of_le_of_lt hbound ?_)
              rw [humin] at hp2 ⊢
              rw [mul_comm] at hp2
              exact hp2
          _ = δ := by ring
    · -- s₀ > 0: locally G' = g (Ψ (min · t) ·)
      have heq : (fun p : ℝ × PhaseSpace d => G' p.1 p.2) =ᶠ[𝓝 (s₀, z₀)]
          (fun p => g (Ψ (min p.1 t) p.2)) := by
        have hmem : {p : ℝ × PhaseSpace d | 0 < p.1} ∈ 𝓝 (s₀, z₀) :=
          (isOpen_lt continuous_const continuous_fst).mem_nhds hs₀
        filter_upwards [hmem] with p hp
        simp only [hG'_def, ite_eq_right (not_le.mpr hp)]
      refine ContinuousAt.congr ?_ heq.symm
      -- continuity of g (Ψ (min p.1 t) p.2) at (s₀, z₀), s₀ > 0
      have hmin_s₀ : min s₀ t ∈ Set.Ioo (0 : ℝ) T :=
        ⟨lt_min hs₀ ht.1, lt_of_le_of_lt (min_le_right _ _) ht.2⟩
      have hΨcont_at : ContinuousAt (fun p : ℝ × PhaseSpace d => Ψ (min p.1 t) p.2) (s₀, z₀) := by
        have hcont_on : ContinuousOn (fun p : ℝ × PhaseSpace d => Ψ p.1 p.2)
            (Set.Ioo 0 T ×ˢ Set.univ) := hΨ_C1.continuousOn
        have hmapcont : Continuous (fun p : ℝ × PhaseSpace d => (min p.1 t, p.2)) :=
          ((continuous_fst.min continuous_const)).prodMk continuous_snd
        have hopen : Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set (PhaseSpace d)) ∈
            𝓝 ((min s₀ t, z₀) : ℝ × PhaseSpace d) :=
          (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hmin_s₀, Set.mem_univ _⟩
        have hca : ContinuousAt (fun p : ℝ × PhaseSpace d => Ψ p.1 p.2) (min s₀ t, z₀) :=
          hcont_on.continuousAt hopen
        exact hca.comp_of_eq hmapcont.continuousAt rfl
      exact hg_cont.continuousAt.comp hΨcont_at
  -- (C) the fixed compact K_total containing all supports of G'
  set Ktot : Set (PhaseSpace d) :=
    (fun q : ℝ × PhaseSpace d ↦ (charX q.1 q.2, charV q.1 q.2)) '' (Set.Icc 0 t ×ˢ S) with hKtot_def
  have hKtot_compact : IsCompact Ktot :=
    (isCompact_Icc.prod hS_compact).image_of_continuousOn
      (hflowjoint.mono (Set.prod_mono (Set.Icc_subset_Icc_right ht.2.le) (Set.subset_univ S)))
  have hS_sub_Ktot : S ⊆ Ktot := by
    intro p hp
    refine ⟨(0, p), ⟨⟨le_refl 0, ht.1.le⟩, hp⟩, ?_⟩
    simp [hinit p]
  have hG'_supp : ∀ s, ∀ z ∉ Ktot, G' s z = 0 := by
    intro s z hz
    simp only [hG'_def]
    split_ifs with hs
    · -- s ≤ 0: G' = g z; z ∉ Ktot ⟹ z ∉ S ⟹ g z = 0
      exact hg_supp_S z (fun hzS => hz (hS_sub_Ktot hzS))
    · -- s > 0: G' = g (Ψ (min s t) z); nonzero ⟹ Ψ(min s t) z ∈ S ⟹ z ∈ Ktot
      by_contra hgz
      rw [not_le] at hs
      have hminIoo : min s t ∈ Set.Ioo (0 : ℝ) T :=
        ⟨lt_min hs ht.1, lt_of_le_of_lt (min_le_right _ _) ht.2⟩
      have hΨz_S : Ψ (min s t) z ∈ S := by
        by_contra hΨz
        exact hgz (hg_supp_S _ hΨz)
      have hright : (charX (min s t) (Ψ (min s t) z), charV (min s t) (Ψ (min s t) z)) = z :=
        hΨ_right (min s t) hminIoo z
      exact hz ⟨(min s t, Ψ (min s t) z),
        ⟨⟨(lt_min hs ht.1).le, min_le_right _ _⟩, hΨz_S⟩, hright⟩
  -- (D) apply NC and transfer to I on Icc 0 t
  have hNC := vlasovSolutionOn_integral_continuousOn f T hf_mom hf_narrow G'
    hG'_cont Ktot hKtot_compact hG'_supp
  refine (hNC.mono (Set.Icc_subset_Icc_right ht.2.le)).congr ?_
  intro s hs
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · -- s = 0
    subst h0
    simp only [ite_true]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hG'_def, ite_eq_left (le_refl (0 : ℝ)), hg_def]
  · -- s > 0
    have hsne : s ≠ 0 := ne_of_gt h0
    have hsle : s ≤ t := hs.2
    simp only [ite_eq_right hsne, hG'_def, ite_eq_right (not_le.mpr h0), min_eq_left hsle, hg_def]

-- dualCore_main: the dual core for 0 < t ≤ T (subsumes the t = T terminal via the same
-- if-patched constancy argument).  Obtains Ψ from item (iv), assembles #6a + #6b +
-- transportedIntegral_const_On + the endpoint identities.
omit [NeZero d] in
theorem dualCore_main
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ)
    (hf_weak : IsVlasovSolutionOn gradW f T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hf_narrow : ∀ (g : PhaseSpace d → ℝ), Continuous g → HasCompactSupport g →
      ContinuousOn (fun s => ∫ z, g z ∂(f s)) (Set.Icc 0 T))
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M_ρ)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow : IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f t)) charX charV
      (Set.Ioo 0 T) Set.univ)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (φ : PhaseSpace d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (Ψ : ℝ → PhaseSpace d → PhaseSpace d)
    (hΨ_left : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      Function.LeftInverse (Ψ s) (fun z => (charX s z, charV s z)))
    (hΨ_right : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      Function.RightInverse (Ψ s) (fun z => (charX s z, charV s z)))
    (hΨ_C1 : ContDiffOn ℝ 1 (fun p : ℝ × PhaseSpace d => Ψ p.1 p.2)
      (Set.Ioo 0 T ×ˢ Set.univ))
    (hΦt_C1 : ContDiff ℝ 1 (fun z : PhaseSpace d => (charX t z, charV t z)))
    (hflowjoint : ContinuousOn (fun p : ℝ × PhaseSpace d => (charX p.1 p.2, charV p.1 p.2))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhaseSpace d))))
    (hanti : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
      dist z₁ z₂ ≤ dist ((charX s z₁, charV s z₁) : PhaseSpace d) (charX s z₂, charV s z₂)
        * Real.exp (((max 1 L : NNReal) : ℝ) * s)) :
    ∫ z, φ z ∂(f t) = ∫ z, φ (charX t z, charV t z) ∂(f 0) := by
  -- the if-patched transported integral
  set I : ℝ → ℝ := fun s => if s = 0 then ∫ z, φ (charX t z, charV t z) ∂(f 0)
      else ∫ z, φ (charX t (Ψ s z), charV t (Ψ s z)) ∂(f s) with hI_def
  -- endpoint values
  have hI0 : I 0 = ∫ z, φ (charX t z, charV t z) ∂(f 0) := by simp [hI_def]
  have htne : t ≠ 0 := ne_of_gt ht.1
  have hIt : I t = ∫ z, φ z ∂(f t) := by
    simp only [hI_def, ite_eq_right htne]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    change φ (charX t (Ψ t z), charV t (Ψ t z)) = φ z
    have hri : (charX t (Ψ t z), charV t (Ψ t z)) = z := hΨ_right t ht z
    rw [hri]
  -- zero derivative on Ioo 0 t (the un-patched form agrees with I near interior s)
  have hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) t, HasDerivAt I 0 s := by
    intro s hs
    have hbase := transportedIntegral_hasDerivAt_zero gradW f T hf_weak hf_mom hf_narrow
      L hL M_ρ hM_ρ_nn hM_ρ charX charV
      hflow t ht φ hφ hφc Ψ hΨ_left hΨ_right hΨ_C1 hΦt_C1 hflowjoint s hs
    refine hbase.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hs] with s' hs' using by
      simp only [hI_def, ite_eq_right (ne_of_gt hs'.1)]
  -- continuity on Icc 0 t
  have hcont : ContinuousOn I (Set.Icc (0 : ℝ) t) :=
    transportedIntegral_continuousOn gradW f T hf_mom hf_narrow charX charV hflow t ht
      φ hφ hφc Ψ hΨ_left hΨ_right hΨ_C1 hΦt_C1 L hflowjoint hanti
  -- constancy: I 0 = I t
  have hconst : I 0 = I t := transportedIntegral_const_On ht.1 hcont hderiv
  rw [hI0, hIt] at hconst
  exact hconst.symm

-- frozenFlow_inverse_On: the item-(iv) discharge — produces the jointly-C¹ inverse Ψ + the
-- four facts dualCore_main consumes, from the raw dual core hypotheses (L11 clamp for the
-- universal probability instance, h_int from hL + moments, etc.).
omit [NeZero d] in
theorem frozenFlow_inverse_On
    (W : PhysSpace d → ℝ) [AssW2 W]
    (gradW : PhysSpace d → PhysSpace d) (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ) (hT : 0 < T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hf_cont : ∀ x, Continuous
      (fun t => convolveFunctionMeasure gradW (spatialMarginal (f t)) x))
    (hf_cont_deriv : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(spatialMarginal (f p.1)))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow : IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f t)) charX charV
      (Set.Ioo 0 T) Set.univ)
    (hcontIcc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ∃ Ψ : ℝ → PhaseSpace d → PhaseSpace d,
      (∀ s ∈ Set.Ioo (0 : ℝ) T,
        Function.LeftInverse (Ψ s) (fun z => (charX s z, charV s z))) ∧
      (∀ s ∈ Set.Ioo (0 : ℝ) T,
        Function.RightInverse (Ψ s) (fun z => (charX s z, charV s z))) ∧
      ContDiffOn ℝ 1 (fun p : ℝ × PhaseSpace d => Ψ p.1 p.2) (Set.Ioo 0 T ×ˢ Set.univ) ∧
      ContDiff ℝ 1 (fun z : PhaseSpace d => (charX t z, charV t z)) ∧
      ContinuousOn (fun p : ℝ × PhaseSpace d => (charX p.1 p.2, charV p.1 p.2))
        (Set.Icc 0 T ×ˢ (Set.univ : Set (PhaseSpace d))) ∧
      (∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
        dist z₁ z₂ ≤ dist ((charX s z₁, charV s z₁) : PhaseSpace d) (charX s z₂, charV s z₂)
          * Real.exp (((max 1 L : NNReal) : ℝ) * s)) := by
  classical
  have hgradW_C1 : ContDiff ℝ 1 gradW := assW2_contDiff_gradW W gradW hgradW
  -- window force-integrability from finite moment + Lipschitz (h_int_helper template)
  have h_int_win : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (spatialMarginal (f s)) := by
    intro s hs x_pt
    have : IsProbabilityMeasure (f s) := (hf_mom s hs).1
    have : IsProbabilityMeasure (spatialMarginal (f s)) :=
      Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    have h_aesm : AEStronglyMeasurable (fun y : PhysSpace d => gradW (x_pt - y))
        (spatialMarginal (f s)) :=
      (hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    have h_y_int : Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal (f s)) := by
      unfold spatialMarginal
      rw [integrable_map_measure
        (by exact (continuous_norm.measurable).aestronglyMeasurable)
        measurable_fst.aemeasurable]
      refine Integrable.mono' (hf_mom s hs).2
        ((continuous_norm.comp continuous_fst).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun z => ?_)
      change |‖z.1‖| ≤ ‖z‖
      rw [abs_of_nonneg (norm_nonneg _)]; exact norm_fst_le z
    have h_dom : ∀ y : PhysSpace d, ‖gradW (x_pt - y)‖ ≤
        ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖ := by
      intro y
      have hd := hL.dist_le_mul (x_pt - y) 0
      simp only [dist_eq_norm, sub_zero] at hd
      have h_tri : ‖gradW (x_pt - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x_pt - y) - gradW 0‖ := by
        have := norm_add_le (gradW (x_pt - y) - gradW 0) (gradW 0)
        simp only [sub_add_cancel] at this; linarith
      have h_sub_le : ‖x_pt - y‖ ≤ ‖x_pt‖ + ‖y‖ := norm_sub_le x_pt y
      have h_mul := mul_le_mul_of_nonneg_left h_sub_le L.coe_nonneg
      linarith
    have h_dom_int : Integrable
        (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖)
        (spatialMarginal (f s)) := by
      have h_norm : Integrable (fun y : PhysSpace d => (L : ℝ) * ‖y‖)
          (spatialMarginal (f s)) := h_y_int.const_mul (L : ℝ)
      have h_eq : (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖) =
                  fun y => (‖gradW 0‖ + (L : ℝ) * ‖x_pt‖) + (L : ℝ) * ‖y‖ := by
        funext y; ring
      rw [h_eq]; exact (integrable_const _).add h_norm
    exact h_dom_int.mono' h_aesm (Filter.Eventually.of_forall fun y => h_dom y)
  -- L11 clamp into [0,T]
  set clampT : ℝ → ℝ := fun s => max 0 (min s T) with hclampT_def
  have hclampT_mem : ∀ s, clampT s ∈ Set.Icc (0 : ℝ) T := by
    intro s; simp only [hclampT_def, Set.mem_Icc]
    exact ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩
  have hclampT_id : ∀ s ∈ Set.Icc (0 : ℝ) T, clampT s = s := by
    intro s hs; simp only [hclampT_def, min_eq_left hs.2, max_eq_right hs.1]
  have hclampT_cont : Continuous clampT := by
    simp only [hclampT_def]; exact continuous_const.max (continuous_id.min continuous_const)
  set ρ' : ℝ → Measure (PhysSpace d) := fun s => spatialMarginal (f (clampT s)) with hρ'_def
  have hρ'_prob : ∀ s, IsProbabilityMeasure (ρ' s) := by
    intro s
    have : IsProbabilityMeasure (f (clampT s)) := (hf_mom (clampT s) (hclampT_mem s)).1
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have h_int' : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ' s) :=
    fun s x => h_int_win (clampT s) (hclampT_mem s) x
  have hf_cont' : ∀ x, Continuous (fun s => convolveFunctionMeasure gradW (ρ' s) x) :=
    fun x => (hf_cont x).comp hclampT_cont
  have hρD_cont' : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ' p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))) := by
    refine hf_cont_deriv.congr (fun p hp => ?_)
    simp only [hρ'_def, hclampT_id p.1 hp.1]
  have hflow' : IsCharacteristicFlowOn gradW ρ' charX charV (Set.Ioo 0 T) Set.univ := by
    refine ⟨hflow.1, hflow.2.1, fun s hs z hz => ?_⟩
    have h := hflow.2.2 s hs z hz
    have hρeq : ρ' s = spatialMarginal (f s) := by
      simp only [hρ'_def, hclampT_id s (Set.Ioo_subset_Icc_self hs)]
    rw [hρeq]; exact h
  -- the per-slice inverse + joint C¹ (Step 3 item iv), ρ-free conclusion
  obtain ⟨Ψ, hLeft, hRight, hC1⟩ := charFlow_inverse_contDiffOn_joint gradW hgradW_C1 L hL ρ'
    charX charV T hT hflow' h_int' hf_cont' hρD_cont' hcontIcc
  -- hΦt_C1: the t-slice ContDiff from joint ContDiffAt
  have hcdaj := charFlow_contDiffAt_joint gradW hgradW_C1 L hL ρ' charX charV T hT
    hflow' h_int' hf_cont' hρD_cont' hcontIcc
  have hΦt_C1 : ContDiff ℝ 1 (fun z : PhaseSpace d => (charX t z, charV t z)) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    have hjoint : ContDiffAt ℝ 1
        (fun q : ℝ × PhaseSpace d => (charX q.1 q.2, charV q.1 q.2)) (t, z) :=
      hcdaj (t, z) ⟨ht, Set.mem_univ _⟩
    have hinner : ContDiffAt ℝ 1 (fun z' : PhaseSpace d => ((t : ℝ), z')) z :=
      (contDiffAt_const).prodMk contDiffAt_id
    exact hjoint.comp z hinner
  -- joint flow continuity + antilipschitz (enrichment for #6b's s=0 endpoint)
  have hinit : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z := fun z =>
    Prod.ext (hflow'.1 z (Set.mem_univ z)).1 (hflow'.1 z (Set.mem_univ z)).2
  have h_deriv2 : ∀ z, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ' s (charX s z, charV s z)) s :=
    fun z s hs => (hflow'.2.1 s hs z (Set.mem_univ z)).prodMk (hflow'.2.2 s hs z (Set.mem_univ z))
  have hflowjoint : ContinuousOn (fun p : ℝ × PhaseSpace d => (charX p.1 p.2, charV p.1 p.2))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhaseSpace d))) :=
    charFlow_continuousOn_joint gradW L hL ρ' h_int' charX charV T hT.le hinit hcontIcc
      (fun z s hs => (h_deriv2 z s hs).hasDerivWithinAt)
  have hanti : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
      dist z₁ z₂ ≤ dist ((charX s z₁, charV s z₁) : PhaseSpace d) (charX s z₂, charV s z₂)
        * Real.exp (((max 1 L : NNReal) : ℝ) * s) := by
    intro s hs z₁ z₂
    have := charFlow_antilipschitzInZ_via_gronwall_Ioo gradW L hL ρ' h_int' charX charV T
      hinit hcontIcc h_deriv2 s hs z₁ z₂
    simpa using this
  exact ⟨Ψ, hLeft, hRight, hC1, hΦt_C1, hflowjoint, hanti⟩

-- dualCore_terminal: the t = T endpoint, by a t → T⁻ limit of the Ioo dual core `hIoo`.
-- LHS continuity at T via narrow continuity (hf_narrow); RHS via filter-DCT against the fixed
-- measure f 0 (joint flow continuity for measurability + per-z continuity for the pointwise limit).
open Filter Topology in
omit [NeZero d] in
theorem dualCore_terminal
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ) (hT : 0 < T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hf_narrow : ∀ (g : PhaseSpace d → ℝ), Continuous g → HasCompactSupport g →
      ContinuousOn (fun s => ∫ z, g z ∂(f s)) (Set.Icc 0 T))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hcontIcc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (hflowjoint : ContinuousOn (fun p : ℝ × PhaseSpace d => (charX p.1 p.2, charV p.1 p.2))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhaseSpace d))))
    (φ : PhaseSpace d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hIoo : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      ∫ z, φ z ∂(f t) = ∫ z, φ (charX t z, charV t z) ∂(f 0)) :
    ∫ z, φ z ∂(f T) = ∫ z, φ (charX T z, charV T z) ∂(f 0) := by
  classical
  have : IsProbabilityMeasure (f 0) := (hf_mom 0 ⟨le_refl 0, hT.le⟩).1
  -- the limit filter, nonempty since T is a left limit point of Ioo 0 T
  have hl_neBot : (𝓝[Set.Ioo (0 : ℝ) T] T).NeBot := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    rw [closure_Ioo (ne_of_lt hT)]
    exact ⟨hT.le, le_refl T⟩
  -- (1) LHS continuity at T (narrow continuity of f against φ)
  have hClaim1 : Tendsto (fun t => ∫ z, φ z ∂(f t)) (𝓝[Set.Ioo (0 : ℝ) T] T)
      (𝓝 (∫ z, φ z ∂(f T))) := by
    have hcwa : ContinuousWithinAt (fun s => ∫ z, φ z ∂(f s)) (Set.Icc 0 T) T :=
      (hf_narrow φ hφ.continuous hφc) T ⟨hT.le, le_refl T⟩
    exact hcwa.tendsto.mono_left (nhdsWithin_mono T Set.Ioo_subset_Icc_self)
  -- (2) RHS continuity at T against the fixed measure f 0 (filter DCT)
  obtain ⟨C, hC⟩ : ∃ C, ∀ z, ‖φ z‖ ≤ C := by
    obtain ⟨C, hC⟩ := (hφ.continuous.norm).bddAbove_range_of_hasCompactSupport hφc.norm
    exact ⟨C, fun z => hC ⟨z, rfl⟩⟩
  have hClaim2 : Tendsto (fun t => ∫ z, φ (charX t z, charV t z) ∂(f 0))
      (𝓝[Set.Ioo (0 : ℝ) T] T) (𝓝 (∫ z, φ (charX T z, charV T z) ∂(f 0))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => C) ?_ ?_ ?_ ?_
    · -- AEStronglyMeasurable eventually
      filter_upwards [self_mem_nhdsWithin] with t ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) T := Set.Ioo_subset_Icc_self ht
      have hslice : Continuous (fun z => (charX t z, charV t z)) :=
        hflowjoint.comp_continuous (continuous_const.prodMk continuous_id)
          (fun z => ⟨htIcc, Set.mem_univ _⟩)
      exact (hφ.continuous.comp hslice).aestronglyMeasurable
    · exact Eventually.of_forall (fun t => Eventually.of_forall (fun z => hC _))
    · exact integrable_const C
    · refine Eventually.of_forall (fun z => ?_)
      have hzcwa : ContinuousWithinAt (fun s => (charX s z, charV s z)) (Set.Icc 0 T) T :=
        (hcontIcc z) T ⟨hT.le, le_refl T⟩
      have hcomp : ContinuousWithinAt (fun s => φ (charX s z, charV s z)) (Set.Icc 0 T) T :=
        hφ.continuous.continuousAt.comp_continuousWithinAt hzcwa
      exact hcomp.tendsto.mono_left (nhdsWithin_mono T Set.Ioo_subset_Icc_self)
  -- (3) the two limits agree via hIoo, so the targets are equal
  have hEqOn : (fun t => ∫ z, φ z ∂(f t)) =ᶠ[𝓝[Set.Ioo (0 : ℝ) T] T]
      (fun t => ∫ z, φ (charX t z, charV t z) ∂(f 0)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht using hIoo t ht
  exact tendsto_nhds_unique (hClaim1.congr' hEqOn) hClaim2

omit [NeZero d] in
/-- **C3 #8 (dual-transport core) — `∫ φ d(f t) = ∫ φ∘Φ_t d(f 0)` for every `C_c^∞` test.**

The dual transported-test-function argument showing the weak solution `f` transports along its
frozen-field characteristics.  Fix a terminal `t ∈ [0,T]` and a `C_c^∞` test `φ`.  Let `Φ_{s→t}`
be the two-time flow (forward from time `s` to time `t` along the frozen-field characteristics)
and `ψ_s := φ ∘ Φ_{s→t}` the backward-transported test (so `ψ_t = φ` and `ψ_0 = φ ∘ Φ_t`).  Then:
**Proven, axiom-clean** (this body composes the six leaves below).  The two-time flow
`Φ_{s→t} = Φ_t ∘ Φ_s⁻¹` is jointly `C¹` (Steps 1–4, proven: `charFlow_inverse_contDiffOn_joint` +
`transportedTest_transport_identity`).  The constancy of `I(s) := ∫ ψ_s d(f s)` on `[0,t]` is
assembled by `dualCore_main` (sorry-free): the `if`-patched `I` (the left endpoint `s = 0`, where
item-(iv) `Ψ_s` is junk, is set directly to `∫ φ∘Φ_t d(f 0)`), endpoint identities
`I 0 = ∫ φ∘Φ_t d(f 0)` and `I t = ∫ φ d(f t)` (via the right-inverse `Ψ_t`), then
`transportedIntegral_const_On` (#7).  `t = 0` is trivial (`Φ_0 = id`); `t = T` goes through
`dualCore_terminal` (a `t → T⁻` limit).

The constancy rests on six leaves (all proven, axiom-clean):
* **`weakEvolution_test_C1c_On`** (#4 = **Step 5**) — the linear weak equation extended from the
  `C_c^∞` test class to `C¹_c` (so it can be tested against the only-`C¹` `ψ_r`).
* **`vlasovSolutionOn_integral_continuousOn`** (NC) — `s ↦ ∫ G s · d(f s)` is continuous for a
  jointly-continuous, uniformly-compactly-supported family `G` (narrow continuity of the weak
  solution, consumption form; derivable from the weak eq + moments).
* **`transportedIntegral_hasDerivAt_zero`** (#6a) — `HasDerivAt I 0` on `Ioo 0 t`, the diagonal
  chain rule: `∂_σ` via #4 + `∂_r` via differentiation-under-the-integral against `f s` + the
  transport-identity cancellation; assembles via the Step-3 continuous-partials gating theorem.
* **`transportedIntegral_continuousOn`** (#6b) — `ContinuousOn I (Icc 0 t)`, via NC + Step-4 joint
  continuity (the `s → 0⁺` endpoint is the load-bearing case).
* **`frozenFlow_inverse_On`** — the item-(iv) discharge producing `Ψ` + its four facts (L11 clamp
  for the universal probability instance).
* **`dualCore_terminal`** — the `t = T` endpoint.

The pushforward side is `integral_map` by definition, so the dual argument is needed only for `f`
(the plan's `#1` pushforward-solves-linear lemma is not on this path). -/
theorem weak_eq_frozenField_pushforward_dualCore
    (W : PhysSpace d → ℝ) [AssW2 W]
    (gradW : PhysSpace d → PhysSpace d) (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ) (hT : 0 < T)
    (hf_weak : IsVlasovSolutionOn gradW f T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hf_narrow : ∀ (g : PhaseSpace d → ℝ), Continuous g → HasCompactSupport g →
      ContinuousOn (fun s => ∫ z, g z ∂(f s)) (Set.Icc 0 T))
    (hf_cont : ∀ x, Continuous
      (fun t => convolveFunctionMeasure gradW (spatialMarginal (f t)) x))
    (hf_cont_deriv : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(spatialMarginal (f p.1)))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M_ρ)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow : IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f t)) charX charV
      (Set.Ioo 0 T) Set.univ)
    (hinit : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (hcontIcc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ : PhaseSpace d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ z, φ z ∂(f t) = ∫ z, φ (charX t z, charV t z) ∂(f 0) := by
  intro t ht φ hφ hφc
  -- the Ioo dual core (this φ): frozenFlow inverse + dualCore_main per interior point
  have hIoo : ∀ τ ∈ Set.Ioo (0 : ℝ) T,
      ∫ z, φ z ∂(f τ) = ∫ z, φ (charX τ z, charV τ z) ∂(f 0) := by
    intro τ hτ
    obtain ⟨Ψ, hl, hr, hc, hΦ, hfj, ha⟩ := frozenFlow_inverse_On W gradW hgradW L hL f T hT hf_mom
      hf_cont hf_cont_deriv charX charV hflow hcontIcc τ hτ
    exact dualCore_main gradW L hL f T hf_weak hf_mom hf_narrow
      M_ρ hM_ρ_nn hM_ρ charX charV hflow τ hτ φ hφ hφc
      Ψ hl hr hc hΦ hfj ha
  -- joint flow continuity (τ-independent; extract from one interior frozenFlow call)
  have hflowjoint : ContinuousOn (fun p : ℝ × PhaseSpace d => (charX p.1 p.2, charV p.1 p.2))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhaseSpace d))) := by
    obtain ⟨_, _, _, _, _, hfj, _⟩ := frozenFlow_inverse_On W gradW hgradW L hL f T hT hf_mom
      hf_cont hf_cont_deriv charX charV hflow hcontIcc (T/2) ⟨by linarith, by linarith⟩
    exact hfj
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · -- t = 0 : trivial, `Φ_0 = id` (hinit)
    rw [← h0]
    simp only [hinit]
  · rcases eq_or_lt_of_le ht.2 with hTe | hlt
    · -- t = T : terminal endpoint via the `t → T⁻` limit
      rw [hTe]
      exact dualCore_terminal f T hT hf_mom hf_narrow charX charV hcontIcc hflowjoint φ hφ hφc hIoo
    · -- t ∈ Ioo 0 T
      exact hIoo t ⟨h0, hlt⟩

omit [NeZero d] in
/-- **C3 #8 — the weak solution equals its frozen-field pushforward on the window.**

`f t = (Φ_t)_# (f 0)` on `[0,T]`.  Skeleton: `measure_eq_of_forall_Cc_integral_eq` (#9) reduces
this to per-`C_c^∞`-test integral equality, and `integral_map` turns the pushforward side into
`∫ φ∘Φ_t d(f 0)` — leaving exactly the dual-transport core
`weak_eq_frozenField_pushforward_dualCore`.  Flow measurability on the window (needed by
`integral_map` and the probability-measure instances) comes from an L11 clamp of `ρ^f` into
`[0,T]` + `charFlow_measurable_via_gronwall_Ioo`. -/
theorem weak_eq_frozenField_pushforward_On
    (W : PhysSpace d → ℝ) [AssW2 W]
    (gradW : PhysSpace d → PhysSpace d) (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ) (hT : 0 < T)
    (hf_weak : IsVlasovSolutionOn gradW f T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hf_narrow : ∀ (g : PhaseSpace d → ℝ), Continuous g → HasCompactSupport g →
      ContinuousOn (fun s => ∫ z, g z ∂(f s)) (Set.Icc 0 T))
    (hf_cont : ∀ x, Continuous
      (fun t => convolveFunctionMeasure gradW (spatialMarginal (f t)) x))
    (hf_cont_deriv : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(spatialMarginal (f p.1)))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M_ρ)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow : IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f t)) charX charV
      (Set.Ioo 0 T) Set.univ)
    (hinit : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (hcontIcc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (hderivIco : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW (fun t => spatialMarginal (f t)) s (charX s z, charV s z))
        (Set.Ici s) s) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      f t = Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) (f 0) := by
  classical
  -- L11 clamp `ρ^f := spatialMarginal ∘ f` into the window so the universal-instance
  -- measurability lemma `charFlow_measurable_via_gronwall_Ioo` applies.
  set clampT : ℝ → ℝ := fun t => max 0 (min t T) with hclampT_def
  have hclampT_mem : ∀ t, clampT t ∈ Set.Icc (0 : ℝ) T := by
    intro t; simp only [hclampT_def, Set.mem_Icc]
    exact ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩
  have hclampT_id : ∀ t ∈ Set.Icc (0 : ℝ) T, clampT t = t := by
    intro t ht; simp only [hclampT_def, min_eq_left ht.2, max_eq_right ht.1]
  -- Windowed first-moment integrability for `ρ^f`.
  have h_y_int : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal (f t)) := by
    intro t ht
    have : IsProbabilityMeasure (f t) := (hf_mom t ht).1
    unfold spatialMarginal
    rw [integrable_map_measure
        (by exact (continuous_norm.measurable).aestronglyMeasurable)
        measurable_fst.aemeasurable]
    refine Integrable.mono' (hf_mom t ht).2
      ((continuous_norm.comp continuous_fst).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => ?_)
    change |‖z.1‖| ≤ ‖z‖
    rw [abs_of_nonneg (norm_nonneg _)]; exact norm_fst_le z
  -- Windowed force integrability for `ρ^f`.
  have h_int_window : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (spatialMarginal (f t)) := by
    intro t ht x_pt
    have : IsProbabilityMeasure (f t) := (hf_mom t ht).1
    have : IsProbabilityMeasure (spatialMarginal (f t)) :=
      Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    have h_aesm : AEStronglyMeasurable (fun y : PhysSpace d => gradW (x_pt - y))
        (spatialMarginal (f t)) :=
      (hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    have h_dom : ∀ y : PhysSpace d, ‖gradW (x_pt - y)‖ ≤
        ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖ := by
      intro y
      have hd := hL.dist_le_mul (x_pt - y) 0
      simp only [dist_eq_norm, sub_zero] at hd
      have h_tri : ‖gradW (x_pt - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x_pt - y) - gradW 0‖ := by
        have := norm_add_le (gradW (x_pt - y) - gradW 0) (gradW 0)
        simp only [sub_add_cancel] at this; linarith
      have h_sub_le : ‖x_pt - y‖ ≤ ‖x_pt‖ + ‖y‖ := norm_sub_le x_pt y
      have h_mul := mul_le_mul_of_nonneg_left h_sub_le L.coe_nonneg
      linarith
    have h_dom_int : Integrable
        (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖)
        (spatialMarginal (f t)) := by
      have h_norm : Integrable (fun y : PhysSpace d => (L : ℝ) * ‖y‖)
          (spatialMarginal (f t)) := (h_y_int t ht).const_mul (L : ℝ)
      have h_eq : (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖) =
                  fun y => (‖gradW 0‖ + (L : ℝ) * ‖x_pt‖) + (L : ℝ) * ‖y‖ := by
        funext y; ring
      rw [h_eq]; exact (integrable_const _).add h_norm
    exact h_dom_int.mono' h_aesm (Filter.Eventually.of_forall fun y => h_dom y)
  -- Clamped curve `ρ'` with the universal probability instance + force integrability.
  set ρ' : ℝ → Measure (PhysSpace d) := fun t => spatialMarginal (f (clampT t)) with hρ'_def
  have hρ'_prob : ∀ t, IsProbabilityMeasure (ρ' t) := by
    intro t
    have : IsProbabilityMeasure (f (clampT t)) := (hf_mom (clampT t) (hclampT_mem t)).1
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have h_int' : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ' t) :=
    fun t x => h_int_window (clampT t) (hclampT_mem t) x
  -- `ρ'`-flavoured velocity ODE on `Ioo 0 T` (clamp = id there, so the field is unchanged).
  have h_deriv_Ioo' : ∀ z, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ' s (charX s z, charV s z)) (Set.Ici s) s := by
    intro z s hs
    have h := hderivIco z s (Set.Ioo_subset_Ico_self hs)
    have hρeq : ρ' s = spatialMarginal (f s) := by
      simp only [hρ'_def, hclampT_id s (Set.Ioo_subset_Icc_self hs)]
    have hfield : vlasovVectorField gradW ρ' s (charX s z, charV s z)
        = vlasovVectorField gradW (fun t => spatialMarginal (f t)) s (charX s z, charV s z) := by
      simp only [vlasovVectorField, hρeq]
    rw [hfield]; exact h
  -- Flow measurability on the window.
  have hΦ_meas : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Measurable (fun z : PhaseSpace d => (charX t z, charV t z)) :=
    charFlow_measurable_via_gronwall_Ioo gradW L hL ρ' h_int' charX charV T hT.le
      hinit hcontIcc h_deriv_Ioo'
  -- Main reduction: `#9` + `integral_map` ⟹ the dual-transport core.
  intro t ht
  have hft_prob : IsProbabilityMeasure (f t) := (hf_mom t ht).1
  have hf0_prob : IsProbabilityMeasure (f 0) := (hf_mom 0 ⟨le_refl 0, hT.le⟩).1
  have hΦt_aem : AEMeasurable (fun z : PhaseSpace d => (charX t z, charV t z)) (f 0) :=
    (hΦ_meas t ht).aemeasurable
  have hmap_prob :
      IsProbabilityMeasure (Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) (f 0)) :=
    Measure.isProbabilityMeasure_map hΦt_aem
  refine measure_eq_of_forall_Cc_integral_eq (fun φ hφ hφc => ?_)
  rw [integral_map hΦt_aem hφ.continuous.aestronglyMeasurable]
  exact weak_eq_frozenField_pushforward_dualCore W gradW hgradW L hL f T hT hf_weak hf_mom hf_narrow
    hf_cont hf_cont_deriv M_ρ hM_ρ_nn hM_ρ charX charV hflow hinit hcontIcc t ht φ hφ hφc

omit [NeZero d] in
/-- **Weak ⟹ Lagrangian on `[0,T]`** (tex: thm:weak-lagrangian).

Under `AssW2` (`W ∈ C²`) and a per-window smallness, every weak Vlasov solution on `[0,T]` with
finite first moments (and the ρ-regularity the frozen-field flow construction needs) is the
pushforward of its initial datum under the characteristic flow it generates — i.e. it is
Lagrangian.  This is the localized, forward-window form matching `vlasovWellPosedness`'s
architecture; the universal form is obtained by window-gluing (deferred).

Hypotheses mirror what `exists_vlasov_characteristicFlow_global_smallT` consumes for the frozen
curve `ρ^f := fun t => spatialMarginal (f t)`.

`hf_cont_deriv` (joint continuity of the convolution-*derivative* field
`∫ fderiv gradW (x−y) ∂ρ^f_s`) is the regularity threaded down to the variational equation (`#3`);
like `hf_cont` it is *assumed* at the bridge boundary (**Option A**).  In the complete theory it is
derivable from `hf_weak` + `hf_mom` (tightness) via a narrow-continuity upgrade — the **Option-B**
extension that would let the bridge assume only the weak solution + moments; see `#3`'s docstring.

Proof (complete, axiom-clean; built over C1–C4 per the roadmap above):
freeze the field at `ρ^f`, build its flow `Φ` (#2) and the pushforward `g := (Φ_t)_# (f 0)` which
solves the frozen linear weak eq (#1); show `f = g` by the dual-transported-test-function
uniqueness (#3–#9, the variational-equation crux); conclude `f` is Lagrangian (#10). -/
theorem weak_isLagrangianVlasovSolutionOn
    (W : PhysSpace d → ℝ) [AssW2 W]
    (gradW : PhysSpace d → PhysSpace d) (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ) (hT : 0 < T)
    (hf_weak : IsVlasovSolutionOn gradW f T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hf_narrow : ∀ (g : PhaseSpace d → ℝ), Continuous g → HasCompactSupport g →
      ContinuousOn (fun s => ∫ z, g z ∂(f s)) (Set.Icc 0 T))
    (hf_cont : ∀ x, Continuous
      (fun t => convolveFunctionMeasure gradW (spatialMarginal (f t)) x))
    (hf_cont_deriv : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(spatialMarginal (f p.1)))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))))
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M_ρ)
    (hTL_PL : LocalSmallnessPLBuffer L T) :
    IsLagrangianVlasovSolutionOn gradW f T := by
  classical
  -- Frozen field `ρ^f := spatialMarginal ∘ f`: discharge the flow-construction hypotheses of #2.
  have hρ_prob : ∀ t ∈ Set.Icc (0 : ℝ) T, IsProbabilityMeasure (spatialMarginal (f t)) := by
    intro t ht
    have : IsProbabilityMeasure (f t) := (hf_mom t ht).1
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have h_y_int : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal (f t)) := by
    intro t ht
    have : IsProbabilityMeasure (f t) := (hf_mom t ht).1
    unfold spatialMarginal
    rw [integrable_map_measure
        (by exact (continuous_norm.measurable).aestronglyMeasurable)
        measurable_fst.aemeasurable]
    refine Integrable.mono' (hf_mom t ht).2
      ((continuous_norm.comp continuous_fst).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => ?_)
    change |‖z.1‖| ≤ ‖z‖
    rw [abs_of_nonneg (norm_nonneg _)]; exact norm_fst_le z
  have h_int : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (spatialMarginal (f t)) := by
    intro t ht x_pt
    have : IsProbabilityMeasure (f t) := (hf_mom t ht).1
    have : IsProbabilityMeasure (spatialMarginal (f t)) :=
      Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    have h_aesm : AEStronglyMeasurable (fun y : PhysSpace d => gradW (x_pt - y))
        (spatialMarginal (f t)) :=
      (hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    have h_dom : ∀ y : PhysSpace d, ‖gradW (x_pt - y)‖ ≤
        ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖ := by
      intro y
      have hd := hL.dist_le_mul (x_pt - y) 0
      simp only [dist_eq_norm, sub_zero] at hd
      have h_tri : ‖gradW (x_pt - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x_pt - y) - gradW 0‖ := by
        have := norm_add_le (gradW (x_pt - y) - gradW 0) (gradW 0)
        simp only [sub_add_cancel] at this; linarith
      have h_sub_le : ‖x_pt - y‖ ≤ ‖x_pt‖ + ‖y‖ := norm_sub_le x_pt y
      have h_mul := mul_le_mul_of_nonneg_left h_sub_le L.coe_nonneg
      linarith
    have h_dom_int : Integrable
        (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖)
        (spatialMarginal (f t)) := by
      have h_norm : Integrable (fun y : PhysSpace d => (L : ℝ) * ‖y‖)
          (spatialMarginal (f t)) := (h_y_int t ht).const_mul (L : ℝ)
      have h_eq : (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖x_pt‖ + (L : ℝ) * ‖y‖) =
                  fun y => (‖gradW 0‖ + (L : ℝ) * ‖x_pt‖) + (L : ℝ) * ‖y‖ := by
        funext y; ring
      rw [h_eq]; exact (integrable_const _).add h_norm
    exact h_dom_int.mono' h_aesm (Filter.Eventually.of_forall fun y => h_dom y)
  have hρ_cont : ∀ x : PhysSpace d,
      ContinuousOn (fun t => convolveFunctionMeasure gradW (spatialMarginal (f t)) x)
        (Set.Icc (0 : ℝ) T) :=
    fun x => (hf_cont x).continuousOn
  -- #2: build the frozen-field characteristic flow on the window.
  obtain ⟨charX, charV, hflow, hinit, hcontIcc, hderivIco⟩ :=
    exists_frozenField_charFlow_On W gradW hgradW L hL (fun t => spatialMarginal (f t))
      T hT hTL_PL hρ_prob h_int hρ_cont h_y_int M_ρ hM_ρ_nn hM_ρ
  -- #8: `f` equals its frozen-field pushforward on the window (the dual-argument crux).
  have hpush : ∀ t ∈ Set.Icc (0 : ℝ) T,
      f t = Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) (f 0) :=
    weak_eq_frozenField_pushforward_On W gradW hgradW L hL f T hT hf_weak hf_mom hf_narrow hf_cont
      hf_cont_deriv M_ρ hM_ρ_nn hM_ρ charX charV hflow hinit hcontIcc hderivIco
  -- Assemble the localized Lagrangian witness.
  refine ⟨hf_weak, charX, charV, hflow, hpush, ?_, hcontIcc⟩
  -- AEMeasurability of the flow at each window time, from the pushforward identity: a
  -- non-measurable map would force `Measure.map _ (f 0) = 0 ≠ f s` (the latter a probability).
  intro s hs
  have hfs_prob : IsProbabilityMeasure (f s) := (hf_mom s hs).1
  by_contra hcon
  have h0 : f s = 0 := by
    rw [hpush s hs]; exact Measure.map_of_not_aemeasurable hcon
  have hone : (f s) Set.univ = 1 := measure_univ
  rw [h0] at hone
  simp at hone

end Vlasov
