/-
Copyright (c) 2026 Joseph K. Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph K. Miller
-/
import LeanPool.Vlasov.OT.CharacteristicFlow

/-!
# Well-posedness ladder for the Vlasov equation + Dobrushin stability

This file builds on the characteristic-flow infrastructure of
`LeanPool/Vlasov/OT/CharacteristicFlow.lean` and carries the theorem ladder of the
development:

* §9 local existence and uniqueness (`vlasovWellPosedness_local` and its
  Picard / final-assembly sub-helpers);
* the fixed-`T_0` continuation tower — the one-window glue step
  `vlasovWellPosedness_glue` (with its `vlasovGlue_*` helper family),
  `exists_localSmallness_window`, and the forward iteration to arbitrary
  `T_target`;
* per-window uniqueness over `IsLagrangianVlasovSolutionOn` and the
  universal-in-`t` bridge to `IsLagrangianVlasovSolution`;
* the §10 marquee results: `vlasovWellPosedness` (forward-in-time existence),
  `vlasovWellPosedness_uniqueness`, `dobrushin` (W₁ stability, proved by
  coupling the two flows and a Grönwall estimate), and the mean-field limit;
* the wiring layer `dobrushin_on` / `dobrushin_forward` /
  `vlasovWellPosedness_stability`: the window and forward-global stability
  forms with the explicit uniform constant `C = 2 · max 1 L`, whose
  hypotheses are exactly the clauses `vlasovWellPosedness` emits.

See `formalize/DESIGN.md` (in the source repository) for the overall design.
-/

namespace Vlasov

open MeasureTheory ENNReal

/-! ## §9  Theorem (Existence and uniqueness for Vlasov)   (tex: thm:vlasov-wp) -/
-- The proof composes directly with the characteristic-flow infrastructure
-- developed in `LeanPool/Vlasov/OT/CharacteristicFlow.lean`: `exists_vlasov_characteristicFlow`,
-- `flow_distance_growth_bound`, and
-- `vlasovSolutionViaPushforward_isLagrangianVlasovSolution`.  The
-- `HasFiniteFirstMoment` predicate remains in `Basic.lean`.

/-- **Project-internal: AEMeasurability of the Vlasov characteristic flow's
joint map** `z ↦ (charX s z, charV s z)` on the window `Icc 0 T`.

The window-restricted statement (`Icc 0 T`) is exactly what is needed: the
Vlasov flow satisfies `HasDerivAt` only on `Ioo 0 T` (off-window it is
uncontrolled `Classical.choose` data), and the sole consumer applies this
only at `clampToIcc T s ∈ Icc 0 T`.  On the window the joint flow's
measurability follows from `charFlow_measurable_via_gronwall` (genuine
`Measurable`, via the boundary bundle through
`characteristicFlow_boundary_regularity`).

**In-project consumer**: `vlasovWellPosedness_local_picard_fixedPointFlow`'s
AEMeasurable conjunct, applied at clamp times `clampToIcc T s ∈ Icc 0 T`. -/
private lemma picardCharFlow_aemeasurable
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    {T : ℝ} (hT : 0 ≤ T)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (hbdry : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV s z)
          (-(convolveFunctionMeasure gradW (ρ t) (charX t z))) (Set.Icc 0 T) t)
    (μ : Measure (PhaseSpace d)) :
    ∀ s ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) μ := by
  intro s hs
  obtain ⟨h_init, h_cont, h_deriv⟩ :=
    characteristicFlow_boundary_regularity gradW ρ charX charV T hT hflow hbdry
  exact (charFlow_measurable_via_gronwall gradW L hL ρ h_int charX charV T hT
    h_init h_cont h_deriv s hs).aemeasurable

/-- **Contraction-input helper**: from a flow's exposed facts (`IsCharacteristicFlowOn`
on `Ioo` + the boundary bundle on `Icc` — the `Phi_step_envelope` output shape)
against a curve `ν`, derive the six per-`z` regularity facts that
`Phi_supW1_contraction` consumes.  Chains `characteristicFlow_boundary_regularity`
(→ init/cont/deriv, the last three EXACT), `charFlow_measurable_via_gronwall`
(→ AEMeasurable), and `flow_distance_growth_bound_on` (→ growth bound, integrated
to the two integrability facts). -/
private lemma envelopeStep_contractionInputs {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d) (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_f₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 ≤ T) {m : ℝ → ℝ}
    (ν : VlasovMeasureCurve d T m)
    (Mbar : ℝ) (hMbar_nn : 0 ≤ Mbar)
    (hM_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(ν.extend t) ≤ Mbar)
    (cX cV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow : IsCharacteristicFlowOn gradW ν.extend cX cV (Set.Ioo 0 T) Set.univ)
    (hbdry : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => cX s z) (cV t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => cV s z)
          (-(convolveFunctionMeasure gradW (ν.extend t) (cX t z))) (Set.Icc 0 T) t)
    (h_int_ext : ∀ t (x : PhysSpace d),
        Integrable (fun y => gradW (x - y)) (ν.extend t)) :
    (∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (fun z : PhaseSpace d => cX t z) f₀) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun z : PhaseSpace d => ‖cX t z‖) f₀) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖) (Measure.map (fun z => cX t z) f₀)) ∧
    (∀ z : PhaseSpace d, (cX 0 z, cV 0 z) = z) ∧
    (∀ z : PhaseSpace d,
      ContinuousOn (fun s => (cX s z, cV s z)) (Set.Icc (0 : ℝ) T)) ∧
    (∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (cX s' z, cV s' z))
        (vlasovVectorField gradW (ν.extend) s (cX s z, cV s z))
        (Set.Ici s) s) := by
  have : ∀ t, IsProbabilityMeasure (ν.extend t) := VlasovMeasureCurve.extend_isProb ν
  obtain ⟨h_init, h_cont, h_deriv⟩ :=
    characteristicFlow_boundary_regularity gradW ν.extend cX cV T hT hflow hbdry
  have h_meas : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => cX t z) f₀ := by
    have h_meas_Icc := charFlow_measurable_via_gronwall gradW L hL ν.extend h_int_ext
      cX cV T hT h_init h_cont h_deriv
    exact fun t ht => (measurable_fst.comp (h_meas_Icc t ht)).aemeasurable
  obtain ⟨C_T, hC_T_nn, h_growth⟩ :=
    flow_distance_growth_bound_on gradW L hL ν.extend cX cV T hT
      h_init h_cont h_deriv Mbar hMbar_nn hM_ρ
      (fun t _ => VlasovMeasureCurve.extend_yIntegrable hT ν t) h_int_ext
  have h_int_charX : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun z : PhaseSpace d => ‖cX t z‖) f₀ := by
    intro t ht
    have h_dom_int : Integrable (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) f₀ := by
      have h1 : Integrable (fun z : PhaseSpace d => C_T * ‖z‖) f₀ := h_f₀_int.const_mul C_T
      have h2 : Integrable (fun _ : PhaseSpace d => C_T) f₀ := integrable_const _
      have h_eq : (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) = fun z => C_T * ‖z‖ + C_T := by
        funext z; ring
      rw [h_eq]; exact h1.add h2
    refine h_dom_int.mono' (h_meas t ht).norm.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact le_trans (norm_fst_le (cX t z, cV t z)) (h_growth t ht z)
  have h_yint_Phi : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖) (Measure.map (fun z => cX t z) f₀) := by
    intro t ht
    rw [integrable_map_measure continuous_norm.aestronglyMeasurable (h_meas t ht)]
    exact h_int_charX t ht
  exact ⟨h_meas, h_int_charX, h_yint_Phi, h_init, h_cont, h_deriv⟩

/-- Lipschitz growth of the force plus a first moment of the measure make the
shifted force integrable.  The workhorse integrability fact behind every
`convolveFunctionMeasure` estimate. -/
lemma integrable_gradW_shift
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (μ : Measure (PhysSpace d)) [MeasureTheory.IsFiniteMeasure μ]
    (h_yint : Integrable (fun y : PhysSpace d => ‖y‖) μ)
    (xp : PhysSpace d) :
    Integrable (fun y => gradW (xp - y)) μ := by
  have h_aesm : AEStronglyMeasurable (fun y : PhysSpace d => gradW (xp - y)) μ :=
    (hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have h_dom : ∀ y : PhysSpace d, ‖gradW (xp - y)‖ ≤
      ‖gradW 0‖ + (L : ℝ) * ‖xp‖ + (L : ℝ) * ‖y‖ := by
    intro y
    have hd := hL.dist_le_mul (xp - y) 0
    simp only [dist_eq_norm, sub_zero] at hd
    have h_tri : ‖gradW (xp - y)‖ ≤ ‖gradW 0‖ + ‖gradW (xp - y) - gradW 0‖ := by
      have := norm_add_le (gradW (xp - y) - gradW 0) (gradW 0)
      simp only [sub_add_cancel] at this; linarith
    have h_sub_le : ‖xp - y‖ ≤ ‖xp‖ + ‖y‖ := norm_sub_le xp y
    have h_mul := mul_le_mul_of_nonneg_left h_sub_le L.coe_nonneg
    linarith
  have h_dom_int : Integrable
      (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖xp‖ + (L : ℝ) * ‖y‖) μ := by
    have h_eq : (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖xp‖ + (L : ℝ) * ‖y‖) =
                fun y => (‖gradW 0‖ + (L : ℝ) * ‖xp‖) + (L : ℝ) * ‖y‖ := by funext y; ring
    rw [h_eq]; exact (integrable_const _).add (h_yint.const_mul _)
  exact h_dom_int.mono' h_aesm (Filter.Eventually.of_forall fun y => h_dom y)

/-- `LocalSmallnessContraction L T` IS the Grönwall contraction factor
`gronwallBound 0 (max 1 L) L T < 1`, after unfolding both definitions. -/
lemma LocalSmallnessContraction.gronwallBound_lt_one
    {L : NNReal} {T : ℝ} (hTL_con : LocalSmallnessContraction L T) :
    gronwallBound 0 ((max 1 L : NNReal) : ℝ) (L : ℝ) T < 1 := by
  have hK_pos : (0 : ℝ) < ((max 1 L : NNReal) : ℝ) := by
    have : (1 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by
      rw [NNReal.coe_max, NNReal.coe_one]; exact le_max_left _ _
    linarith
  have hK_ne : ((max 1 L : NNReal) : ℝ) ≠ 0 := ne_of_gt hK_pos
  rw [gronwallBound_of_K_ne_0 hK_ne]
  simp only [zero_mul, zero_add]
  have h_eq : (L : ℝ) / ((max 1 L : NNReal) : ℝ) *
      (Real.exp (((max 1 L : NNReal) : ℝ) * T) - 1) =
      (L : ℝ) * (Real.exp ((max 1 (L : ℝ)) * T) - 1) / (max 1 (L : ℝ)) := by
    rw [NNReal.coe_max, NNReal.coe_one]
    ring
  rw [h_eq]
  exact hTL_con

/-- The Picard sequence of the local fixed-point construction, with its exposed
per-step flows and the geometric contraction bound.  Extracted from
`vlasovWellPosedness_local_picard_fixedPointFlow`; the parameters `q` (the
contraction factor) and `D₀` (the initial `W₁`-input bound) are threaded with
their defining equations so the parent's `let`-definitions supply `rfl`. -/
private lemma vlasovWellPosedness_local_picard_sequence
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (hTL_PL : LocalSmallnessPLBuffer L T)
    (m : ℝ → ℝ) (hm_mono : MonotoneOn m (Set.Icc 0 T))
    (hm_nn : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ m t)
    (hm_inv : ∀ t ∈ Set.Icc (0 : ℝ) T,
      gronwallBound (∫ z, ‖z‖ ∂f₀) (1 + (L : ℝ)) (‖gradW 0‖ + (L : ℝ) * m t) t ≤ m t)
    (hMbar_nn : 0 ≤ m T) (hMbar_mono : ∀ t ∈ Set.Icc (0 : ℝ) T, m t ≤ m T)
    (hμ₀_prob : IsProbabilityMeasure (spatialMarginal f₀))
    (hμ₀_int : Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal f₀))
    (hμ₀_le_m : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal f₀) ≤ m t)
    (q : ℝ) (hq_nn : 0 ≤ q)
    (hq_def : q = gronwallBound 0 ((max 1 L : NNReal) : ℝ) (L : ℝ) T)
    (D₀ : ℝ) (hD₀_nn : 0 ≤ D₀) (hD₀_def : D₀ = 2 * (m T)) :
    ∃ (x : ℕ → VlasovMeasureCurve d T m)
      (charXs charVs : ℕ → ℝ → PhaseSpace d → PhysSpace d),
      (∀ k, supW1On (Set.Icc 0 T) (x k).ρ (x (k + 1)).ρ ≤
            ENNReal.ofReal (q ^ k * D₀)) ∧
      (∀ k,
        IsCharacteristicFlowOn gradW (x k).extend (charXs k) (charVs k)
          (Set.Ioo 0 T) Set.univ ∧
        (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
          HasDerivWithinAt (fun s => charXs k s z) (charVs k t z) (Set.Icc 0 T) t ∧
          HasDerivWithinAt (fun s => charVs k s z)
            (-(convolveFunctionMeasure gradW ((x k).extend t) (charXs k t z)))
            (Set.Icc 0 T) t) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) T,
          (x (k + 1)).ρ t
            = Measure.map (fun z : PhaseSpace d => charXs k t z) f₀)) := by
  have h_int_ext_gen : ∀ (ν : VlasovMeasureCurve d T m) (t : ℝ) (xp : PhysSpace d),
      Integrable (fun y => gradW (xp - y)) (ν.extend t) := fun ν t xp =>
    integrable_gradW_shift gradW L hL (ν.extend t)
      (VlasovMeasureCurve.extend_yIntegrable hT.le ν t) xp
  have step : ∀ (ν : VlasovMeasureCurve d T m),
      ∃ (σ : VlasovMeasureCurve d T m) (cX cV : ℝ → PhaseSpace d → PhysSpace d),
        (∀ t ∈ Set.Icc (0 : ℝ) T, σ.ρ t = Measure.map (fun z => cX t z) f₀) ∧
        IsCharacteristicFlowOn gradW ν.extend cX cV (Set.Ioo 0 T) Set.univ ∧
        (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
          HasDerivWithinAt (fun s => cX s z) (cV t z) (Set.Icc 0 T) t ∧
          HasDerivWithinAt (fun s => cV s z)
            (-(convolveFunctionMeasure gradW (ν.extend t) (cX t z))) (Set.Icc 0 T) t) := by
    intro ν
    obtain ⟨cX, cV, hflow, hbdry, σ, hσ⟩ :=
      Phi_step_envelope W gradW hgradW L hL f₀ hf₀_int hT.le m hm_mono hm_nn hm_inv hTL_PL
        ν (h_int_ext_gen ν)
    exact ⟨σ, cX, cV, hσ, hflow, hbdry⟩
  have hμ₀_prob_inst : IsProbabilityMeasure (spatialMarginal f₀) := hμ₀_prob
  let base : VlasovMeasureCurve d T m := constantCurve (spatialMarginal f₀) hμ₀_int hμ₀_le_m
  let x : ℕ → VlasovMeasureCurve d T m :=
    fun n => Nat.rec base (fun _ ν => Classical.choose (step ν)) n
  let charXs : ℕ → ℝ → PhaseSpace d → PhysSpace d :=
    fun k => Classical.choose (Classical.choose_spec (step (x k)))
  let charVs : ℕ → ℝ → PhaseSpace d → PhysSpace d :=
    fun k => Classical.choose (Classical.choose_spec (Classical.choose_spec (step (x k))))
  have hx_succ : ∀ k, x (k + 1) = Classical.choose (step (x k)) := fun _ => rfl
  have hspec : ∀ k,
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        (Classical.choose (step (x k))).ρ t = Measure.map (fun z => charXs k t z) f₀) ∧
      IsCharacteristicFlowOn gradW (x k).extend (charXs k) (charVs k)
        (Set.Ioo 0 T) Set.univ ∧
      (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => charXs k s z) (charVs k t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charVs k s z)
          (-(convolveFunctionMeasure gradW ((x k).extend t) (charXs k t z)))
          (Set.Icc 0 T) t) :=
    fun k => Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec (step (x k))))
  have h_flow : ∀ k,
      IsCharacteristicFlowOn gradW (x k).extend (charXs k) (charVs k)
        (Set.Ioo 0 T) Set.univ ∧
      (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => charXs k s z) (charVs k t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charVs k s z)
          (-(convolveFunctionMeasure gradW ((x k).extend t) (charXs k t z)))
          (Set.Icc 0 T) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        (x (k + 1)).ρ t = Measure.map (fun z : PhaseSpace d => charXs k t z) f₀) := by
    intro k
    obtain ⟨hpush, hcf, hbd⟩ := hspec k
    refine ⟨hcf, hbd, fun t ht => ?_⟩
    rw [hx_succ k]; exact hpush t ht
  have hCI : ∀ k,
      (∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (fun z : PhaseSpace d => charXs k t z) f₀) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun z : PhaseSpace d => ‖charXs k t z‖) f₀) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        Integrable (fun y : PhysSpace d => ‖y‖) (Measure.map (fun z => charXs k t z) f₀)) ∧
      (∀ z : PhaseSpace d, (charXs k 0 z, charVs k 0 z) = z) ∧
      (∀ z : PhaseSpace d,
        ContinuousOn (fun s => (charXs k s z, charVs k s z)) (Set.Icc (0 : ℝ) T)) ∧
      (∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (fun s' => (charXs k s' z, charVs k s' z))
          (vlasovVectorField gradW ((x k).extend) s (charXs k s z, charVs k s z))
          (Set.Ici s) s) :=
    fun k => envelopeStep_contractionInputs gradW L hL f₀ hf₀_int hT.le (x k) (m T) hMbar_nn
      (fun t _ => le_trans (VlasovMeasureCurve.extend_hasMoment hT.le (x k) t)
        (hMbar_mono (clampToIcc T t) (clampToIcc_mem hT.le t)))
      (charXs k) (charVs k) (h_flow k).1 (h_flow k).2.1 (h_int_ext_gen (x k))
  have hK_ne : ((max 1 L : NNReal) : ℝ) ≠ 0 := by
    have h1 : (1:ℝ) ≤ ((max 1 L : NNReal):ℝ) := by
      rw [NNReal.coe_max, NNReal.coe_one]; exact le_max_left _ _
    linarith
  have hq_scale : ∀ D : ℝ,
      gronwallBound 0 ((max 1 L : NNReal):ℝ) ((L:ℝ)*D) T = D * q := by
    intro D
    rw [hq_def, gronwallBound_of_K_ne_0 hK_ne, gronwallBound_of_K_ne_0 hK_ne]; ring
  have hPext : ∀ (ν : VlasovMeasureCurve d T m) (t : ℝ),
      IsProbabilityMeasure (ν.extend t) :=
    fun ν => VlasovMeasureCurve.extend_isProb ν
  have h_contract : ∀ k, supW1On (Set.Icc 0 T) (x k).ρ (x (k + 1)).ρ ≤
      ENNReal.ofReal (q ^ k * D₀) := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, one_mul]
      rw [hD₀_def]
      exact supW1On_le_two_moment_of_VlasovMeasureCurve (m T) hMbar_mono (x 0) (x 1)
    | succ k ih =>
      set D : ℝ := q ^ k * D₀ with hD_def
      have hD_nn : 0 ≤ D := mul_nonneg (pow_nonneg hq_nn k) hD₀_nn
      have he : ∀ (ν : VlasovMeasureCurve d T m) s, s ∈ Set.Icc (0 : ℝ) T → ν.extend s = ν.ρ s := by
        intro ν s hs
        unfold VlasovMeasureCurve.extend clampToIcc; congr 1
        rw [min_eq_left hs.2, max_eq_right hs.1]
      have h_W1_fin : ∀ s ∈ Set.Icc (0 : ℝ) T,
          wasserstein1 ((x k).extend s) ((x (k+1)).extend s) ≠ ⊤ := by
        intro s hs
        rw [he (x k) s hs, he (x (k+1)) s hs]
        have := (x k).isProb s; have := (x (k+1)).isProb s
        exact wasserstein1_ne_top_of_finite_moment _ _
          ((x k).yIntegrable s hs) ((x (k+1)).yIntegrable s hs)
      have h_W1_bound : ∀ s ∈ Set.Icc (0 : ℝ) T,
          (wasserstein1 ((x k).extend s) ((x (k+1)).extend s)).toReal ≤ D := by
        intro s hs
        rw [he (x k) s hs, he (x (k+1)) s hs]
        have h_le : wasserstein1 ((x k).ρ s) ((x (k+1)).ρ s)
            ≤ ENNReal.ofReal D :=
          le_trans (wasserstein1_le_supW1On _ _ _ s hs) ih
        have h_ne : wasserstein1 ((x k).ρ s) ((x (k+1)).ρ s) ≠ ⊤ := by
          have := (x k).isProb s; have := (x (k+1)).isProb s
          exact wasserstein1_ne_top_of_finite_moment _ _
            ((x k).yIntegrable s hs) ((x (k+1)).yIntegrable s hs)
        calc (wasserstein1 ((x k).ρ s) ((x (k+1)).ρ s)).toReal
            ≤ (ENNReal.ofReal D).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_le
          _ = D := ENNReal.toReal_ofReal hD_nn
      have h_contr := @Phi_supW1_contraction d gradW L hL ((x k).extend) ((x (k+1)).extend)
        (hPext (x k)) (hPext (x (k+1)))
        (h_int_ext_gen (x k)) (h_int_ext_gen (x (k+1))) T hT.le D hD_nn h_W1_fin h_W1_bound
        (charXs k) (charVs k) (charXs (k+1)) (charVs (k+1)) f₀ _
        (hCI k).1 (hCI (k+1)).1 (hCI k).2.1 (hCI (k+1)).2.1
        (hCI k).2.2.1 (hCI (k+1)).2.2.1 (hCI k).2.2.2.1 (hCI (k+1)).2.2.2.1
        (hCI k).2.2.2.2.1 (hCI (k+1)).2.2.2.2.1 (hCI k).2.2.2.2.2 (hCI (k+1)).2.2.2.2.2
      rw [hq_scale D] at h_contr
      have h_supW1_eq : supW1On (Set.Icc 0 T) (x (k+1)).ρ (x (k+1+1)).ρ
          = supW1On (Set.Icc 0 T)
              (fun t => Measure.map (fun z => charXs k t z) f₀)
              (fun t => Measure.map (fun z => charXs (k+1) t z) f₀) := by
        unfold supW1On
        exact iSup_congr fun t => iSup_congr fun ht => by
          rw [(h_flow k).2.2 t ht, (h_flow (k+1)).2.2 t ht]
      have hDq : D * q = q ^ (k + 1) * D₀ := by rw [hD_def, pow_succ]; ring
      rw [hDq] at h_contr
      have h_ne_top : supW1On (Set.Icc 0 T)
          (fun t => Measure.map (fun z => charXs k t z) f₀)
          (fun t => Measure.map (fun z => charXs (k+1) t z) f₀) ≠ ⊤ := by
        rw [← h_supW1_eq]
        exact supW1On_ne_top_of_VlasovMeasureCurve (m T) hMbar_mono (x (k+1)) (x (k+1+1))
      have h_pow_nn : 0 ≤ q ^ (k + 1) * D₀ := mul_nonneg (pow_nonneg hq_nn _) hD₀_nn
      rw [h_supW1_eq]
      rw [← ENNReal.toReal_le_toReal h_ne_top ENNReal.ofReal_ne_top,
          ENNReal.toReal_ofReal h_pow_nn]
      exact h_contr
  exact ⟨x, charXs, charVs, h_contract, h_flow⟩

/-- Pointwise contraction of the Picard step between an iterate and the limit
curve: the pushforwards under the two flows are `D·q`-close whenever the curves
are uniformly `D`-close in `W₁`.  Wraps `Phi_pointwise_contraction` +
`gronwallBound` monotonicity for a single curve pair. -/
private lemma picardLimit_flow_pointwise_contraction
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (m : ℝ → ℝ) (hMbar_nn : 0 ≤ m T)
    (hMbar_mono : ∀ t ∈ Set.Icc (0 : ℝ) T, m t ≤ m T)
    (ν ρl : VlasovMeasureCurve d T m)
    (cX cV charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow_ν : IsCharacteristicFlowOn gradW ν.extend cX cV (Set.Ioo 0 T) Set.univ)
    (hbdry_ν : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => cX s z) (cV t z) (Set.Icc 0 T) t ∧
      HasDerivWithinAt (fun s => cV s z)
        (-(convolveFunctionMeasure gradW (ν.extend t) (cX t z))) (Set.Icc 0 T) t)
    (hflow_l : IsCharacteristicFlowOn gradW ρl.extend charX charV (Set.Ioo 0 T) Set.univ)
    (hbdry_l : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
      HasDerivWithinAt (fun s => charV s z)
        (-(convolveFunctionMeasure gradW (ρl.extend t) (charX t z))) (Set.Icc 0 T) t)
    (D : ℝ) (hD_nn : 0 ≤ D)
    (h_W1_fin : ∀ s ∈ Set.Icc (0 : ℝ) T, wasserstein1 (ν.extend s) (ρl.extend s) ≠ ⊤)
    (h_W1_bound : ∀ s ∈ Set.Icc (0 : ℝ) T,
      (wasserstein1 (ν.extend s) (ρl.extend s)).toReal ≤ D)
    (q : ℝ) (hq_def : q = gronwallBound 0 ((max 1 L : NNReal) : ℝ) (L : ℝ) T) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      (wasserstein1 (Measure.map (fun z => cX t z) f₀)
                    (Measure.map (fun z => charX t z) f₀)).toReal ≤ D * q := by
  have hK_ge1 : (1 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by
    rw [NNReal.coe_max, NNReal.coe_one]; exact le_max_left _ _
  have hK_ne : ((max 1 L : NNReal) : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hK_pos : (0 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by linarith
  have hMm : ∀ (μ : VlasovMeasureCurve d T m), ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫ y, ‖y‖ ∂(μ.extend t) ≤ m T :=
    fun μ t _ => le_trans (VlasovMeasureCurve.extend_hasMoment hT.le μ t)
      (hMbar_mono (clampToIcc T t) (clampToIcc_mem hT.le t))
  have h_int_ν : ∀ t (xp : PhysSpace d),
      Integrable (fun y => gradW (xp - y)) (ν.extend t) := fun t xp =>
    integrable_gradW_shift gradW L hL (ν.extend t)
      (VlasovMeasureCurve.extend_yIntegrable hT.le ν t) xp
  have h_int_l : ∀ t (xp : PhysSpace d),
      Integrable (fun y => gradW (xp - y)) (ρl.extend t) := fun t xp =>
    integrable_gradW_shift gradW L hL (ρl.extend t)
      (VlasovMeasureCurve.extend_yIntegrable hT.le ρl t) xp
  have hCI_ν := envelopeStep_contractionInputs gradW L hL f₀ hf₀_int hT.le ν
    (m T) hMbar_nn (hMm ν) cX cV hflow_ν hbdry_ν h_int_ν
  have hCI_l := envelopeStep_contractionInputs gradW L hL f₀ hf₀_int hT.le ρl
    (m T) hMbar_nn (hMm ρl) charX charV hflow_l hbdry_l h_int_l
  have hq_scale : gronwallBound 0 ((max 1 L : NNReal) : ℝ) ((L:ℝ) * D) T = D * q := by
    rw [hq_def, gronwallBound_of_K_ne_0 hK_ne, gronwallBound_of_K_ne_0 hK_ne]; ring
  intro t ht
  have hpt := @Phi_pointwise_contraction d gradW L hL (ν.extend) (ρl.extend)
    (VlasovMeasureCurve.extend_isProb ν) (VlasovMeasureCurve.extend_isProb ρl)
    h_int_ν h_int_l T hT.le D hD_nn h_W1_fin h_W1_bound
    cX cV charX charV f₀ _
    hCI_ν.1 hCI_l.1 hCI_ν.2.1 hCI_l.2.1
    hCI_ν.2.2.2.1 hCI_l.2.2.2.1 hCI_ν.2.2.2.2.1 hCI_l.2.2.2.2.1
    hCI_ν.2.2.2.2.2 hCI_l.2.2.2.2.2 t ht
  have h_mono : gronwallBound 0 ((max 1 L : NNReal) : ℝ) ((L:ℝ) * D) t
      ≤ gronwallBound 0 ((max 1 L : NNReal) : ℝ) ((L:ℝ) * D) T :=
    gronwallBound_mono (le_refl 0) (mul_nonneg L.coe_nonneg hD_nn) hK_pos ht.2
  rw [hq_scale] at h_mono
  exact le_trans hpt h_mono

/-- The Picard fixed-point equation at the limit: if the iterates converge to the
limit curve in `W₁` and each step's pushforward is `Dₙ·q`-close to the limit
flow's pushforward with `Dₙ·q → 0`, the limit curve equals the limit flow's
pushforward.  Triangle through the iterates + the `W₁` separation lemma. -/
private lemma picardLimit_fixed_point_eq
    {d : ℕ} [NeZero d]
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    {T : ℝ}
    (m : ℝ → ℝ) (x : ℕ → VlasovMeasureCurve d T m) (ρl : VlasovMeasureCurve d T m)
    (charXs : ℕ → ℝ → PhaseSpace d → PhysSpace d)
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (h_push : ∀ n, ∀ t ∈ Set.Icc (0 : ℝ) T,
      (x (n + 1)).ρ t = Measure.map (fun z : PhaseSpace d => charXs n t z) f₀)
    (h_tendsto : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Filter.Tendsto (fun n => wasserstein1 ((x n).ρ t) (ρl.ρ t)) Filter.atTop (nhds 0))
    (h_aem_n : ∀ n, ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => charXs n t z) f₀)
    (h_aem_lim : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => charX t z) f₀)
    (h_mom_n : ∀ n, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖) (Measure.map (fun z => charXs n t z) f₀))
    (h_mom_lim : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖) (Measure.map (fun z => charX t z) f₀))
    (Dn : ℕ → ℝ) (q : ℝ)
    (hDnq_tendsto : Filter.Tendsto (fun n => Dn n * q) Filter.atTop (nhds 0))
    (h_term2 : ∀ n t, t ∈ Set.Icc (0 : ℝ) T →
      (wasserstein1 (Measure.map (fun z => charXs n t z) f₀)
                    (Measure.map (fun z => charX t z) f₀)).toReal ≤ Dn n * q) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ρl.ρ t = Measure.map (fun z => charX t z) f₀ := by
  intro t ht
  have hP1 : IsProbabilityMeasure (ρl.ρ t) := ρl.isProb t
  have hP2 : IsProbabilityMeasure (Measure.map (fun z => charX t z) f₀) :=
    Measure.isProbabilityMeasure_map (h_aem_lim t ht)
  refine (wasserstein1_eq_zero_iff_measure_eq (ρl.ρ t)
    (Measure.map (fun z => charX t z) f₀)).mp ?_
  have h_le_seq : ∀ n, wasserstein1 (ρl.ρ t) (Measure.map (fun z => charX t z) f₀)
      ≤ wasserstein1 ((x (n+1)).ρ t) (ρl.ρ t) + ENNReal.ofReal (Dn n * q) := by
    intro n
    have h_mid : (x (n+1)).ρ t = Measure.map (fun z => charXs n t z) f₀ := h_push n t ht
    calc wasserstein1 (ρl.ρ t) (Measure.map (fun z => charX t z) f₀)
        ≤ wasserstein1 (ρl.ρ t) ((x (n+1)).ρ t)
            + wasserstein1 ((x (n+1)).ρ t) (Measure.map (fun z => charX t z) f₀) :=
          wasserstein1_triangle _ _ _
      _ = wasserstein1 ((x (n+1)).ρ t) (ρl.ρ t)
            + wasserstein1 ((x (n+1)).ρ t) (Measure.map (fun z => charX t z) f₀) := by
          rw [wasserstein1_comm (ρl.ρ t) ((x (n+1)).ρ t)]
      _ ≤ wasserstein1 ((x (n+1)).ρ t) (ρl.ρ t) + ENNReal.ofReal (Dn n * q) := by
          gcongr
          rw [h_mid]
          have h_fin : wasserstein1 (Measure.map (fun z => charXs n t z) f₀)
              (Measure.map (fun z => charX t z) f₀) ≠ ⊤ := by
            have : IsProbabilityMeasure (Measure.map (fun z => charXs n t z) f₀) :=
              Measure.isProbabilityMeasure_map (h_aem_n n t ht)
            exact wasserstein1_ne_top_of_finite_moment _ _
              (h_mom_n n t ht) (h_mom_lim t ht)
          rw [← ENNReal.ofReal_toReal h_fin]
          exact ENNReal.ofReal_le_ofReal (h_term2 n t ht)
  have hA : Filter.Tendsto (fun n => wasserstein1 ((x (n+1)).ρ t) (ρl.ρ t))
      Filter.atTop (nhds 0) :=
    (h_tendsto t ht).comp (Filter.tendsto_add_atTop_nat 1)
  have hB : Filter.Tendsto (fun n => ENNReal.ofReal (Dn n * q)) Filter.atTop (nhds 0) := by
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hDnq_tendsto
    simpa [Function.comp_def] using this
  have h_seq : Filter.Tendsto
      (fun n => wasserstein1 ((x (n+1)).ρ t) (ρl.ρ t) + ENNReal.ofReal (Dn n * q))
      Filter.atTop (nhds 0) := by
    have := hA.add hB
    simpa using this
  exact le_antisymm (ge_of_tendsto' h_seq h_le_seq) (zero_le)

/-- Bundle the self-consistent Picard-limit flow, CLAMPED to the window, into the
seven-conjunct conclusion of `vlasovWellPosedness_local_picard_fixedPointFlow`.
The raw flow is controlled only on `[0, T]`; clamping (`clampToIcc`) makes every
universal-in-`s` conjunct reduce to the window, where the clamp is the identity. -/
private lemma picardFlow_clamp_bundle
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    {T : ℝ} (hT : 0 < T)
    (m : ℝ → ℝ) (hMbar_nn : 0 ≤ m T)
    (hMbar_mono : ∀ t ∈ Set.Icc (0 : ℝ) T, m t ≤ m T)
    (ρ_lim : VlasovMeasureCurve d T m)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow_on_ρlim : IsCharacteristicFlowOn gradW ρ_lim.extend charX charV
      (Set.Ioo 0 T) Set.univ)
    (h_boundary_ρlim : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
      HasDerivWithinAt (fun s => charV s z)
        (-(convolveFunctionMeasure gradW (ρ_lim.extend t) (charX t z))) (Set.Icc 0 T) t)
    (h_int_ρ_lim : ∀ t (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (ρ_lim.extend t))
    (h_self_consist : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ρ_lim.extend t =
      spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) :
    ∃ (charX' charV' : ℝ → PhaseSpace d → PhysSpace d) (M_ρ : ℝ), 0 ≤ M_ρ ∧
      IsCharacteristicFlowOn gradW
        (fun t => spatialMarginal (vlasovSolutionViaPushforward charX' charV' f₀ t))
        charX' charV' (Set.Ioo 0 T) Set.univ ∧
      (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => charX' s z) (charV' t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV' s z)
          (-(convolveFunctionMeasure gradW
              (spatialMarginal (vlasovSolutionViaPushforward charX' charV' f₀ t))
              (charX' t z)))
          (Set.Icc 0 T) t) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) T,
        ∫ y, ‖y‖ ∂(spatialMarginal (vlasovSolutionViaPushforward charX' charV' f₀ s)) ≤ M_ρ) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) T,
        Integrable (fun y : PhysSpace d => ‖y‖)
          (spatialMarginal (vlasovSolutionViaPushforward charX' charV' f₀ s))) ∧
      (∀ s, Continuous (fun x =>
        convolveFunctionMeasure gradW
          (spatialMarginal (vlasovSolutionViaPushforward charX' charV' f₀ s)) x)) ∧
      (∀ s, AEMeasurable (fun z : PhaseSpace d => (charX' s z, charV' s z)) f₀) ∧
      (∀ s (x : PhysSpace d),
        Integrable (fun y => gradW (x - y))
          (spatialMarginal (vlasovSolutionViaPushforward charX' charV' f₀ s))) := by
  have hclamp_id : ∀ s ∈ Set.Icc (0 : ℝ) T, clampToIcc T s = s := fun s hs => by
    unfold clampToIcc; rw [min_eq_left hs.2, max_eq_right hs.1]
  have hclamp0 : clampToIcc T 0 = 0 := hclamp_id 0 ⟨le_refl 0, hT.le⟩
  have h_rho_clamp : ∀ s : ℝ,
      spatialMarginal (vlasovSolutionViaPushforward
        (fun s' z => charX (clampToIcc T s') z)
        (fun s' z => charV (clampToIcc T s') z) f₀ s) =
      ρ_lim.extend (clampToIcc T s) := by
    intro s
    have h1 : spatialMarginal (vlasovSolutionViaPushforward
        (fun s' z => charX (clampToIcc T s') z)
        (fun s' z => charV (clampToIcc T s') z) f₀ s) =
        spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ (clampToIcc T s)) :=
      rfl
    rw [h1, ← h_self_consist (clampToIcc T s) (clampToIcc_mem hT.le s)]
  refine ⟨fun s z => charX (clampToIcc T s) z, fun s z => charV (clampToIcc T s) z,
    m T, hMbar_nn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun z _hz => ?_, fun t ht z _hz => ?_, fun t ht z _hz => ?_⟩
    · change charX (clampToIcc T 0) z = z.1 ∧ charV (clampToIcc T 0) z = z.2
      rw [hclamp0]; exact hflow_on_ρlim.1 z (Set.mem_univ z)
    · have hEv : (fun s => charX (clampToIcc T s) z) =ᶠ[nhds t]
          (fun s => charX s z) := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
        rw [hclamp_id s (Set.Ioo_subset_Icc_self hs)]
      change HasDerivAt (fun s => charX (clampToIcc T s) z) (charV (clampToIcc T t) z) t
      rw [hclamp_id t (Set.Ioo_subset_Icc_self ht)]
      exact (hflow_on_ρlim.2.1 t ht z (Set.mem_univ z)).congr_of_eventuallyEq hEv
    · have hEv : (fun s => charV (clampToIcc T s) z) =ᶠ[nhds t]
          (fun s => charV s z) := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
        rw [hclamp_id s (Set.Ioo_subset_Icc_self hs)]
      change HasDerivAt (fun s => charV (clampToIcc T s) z)
        (-(convolveFunctionMeasure gradW
            (spatialMarginal (vlasovSolutionViaPushforward
              (fun s' z' => charX (clampToIcc T s') z')
              (fun s' z' => charV (clampToIcc T s') z') f₀ t))
            (charX (clampToIcc T t) z))) t
      rw [h_rho_clamp t, hclamp_id t (Set.Ioo_subset_Icc_self ht)]
      exact (hflow_on_ρlim.2.2 t ht z (Set.mem_univ z)).congr_of_eventuallyEq hEv
  · intro z t ht
    have hEqOn : Set.EqOn (fun s => charX (clampToIcc T s) z) (fun s => charX s z)
        (Set.Icc 0 T) := fun s hs => by
      change charX (clampToIcc T s) z = charX s z; rw [hclamp_id s hs]
    have hEqOnV : Set.EqOn (fun s => charV (clampToIcc T s) z) (fun s => charV s z)
        (Set.Icc 0 T) := fun s hs => by
      change charV (clampToIcc T s) z = charV s z; rw [hclamp_id s hs]
    obtain ⟨h1, h2⟩ := h_boundary_ρlim z t ht
    refine ⟨?_, ?_⟩
    · change HasDerivWithinAt (fun s => charX (clampToIcc T s) z)
        (charV (clampToIcc T t) z) (Set.Icc 0 T) t
      rw [hclamp_id t ht]
      exact h1.congr hEqOn (hEqOn ht)
    · change HasDerivWithinAt (fun s => charV (clampToIcc T s) z)
        (-(convolveFunctionMeasure gradW
            (spatialMarginal (vlasovSolutionViaPushforward
              (fun s' z' => charX (clampToIcc T s') z')
              (fun s' z' => charV (clampToIcc T s') z') f₀ t))
            (charX (clampToIcc T t) z))) (Set.Icc 0 T) t
      rw [h_rho_clamp t, hclamp_id t ht]
      exact h2.congr hEqOnV (hEqOnV ht)
  · intro s hs
    rw [h_rho_clamp s, hclamp_id s hs]
    exact le_trans (VlasovMeasureCurve.extend_hasMoment hT.le ρ_lim s)
      (hMbar_mono (clampToIcc T s) (clampToIcc_mem hT.le s))
  · intro s hs
    rw [h_rho_clamp s, hclamp_id s hs]
    exact VlasovMeasureCurve.extend_yIntegrable hT.le ρ_lim s
  · intro s
    rw [h_rho_clamp s]
    have : IsProbabilityMeasure (ρ_lim.extend (clampToIcc T s)) :=
      VlasovMeasureCurve.extend_isProb ρ_lim (clampToIcc T s)
    exact (convolveFunctionMeasure_lipschitz_in_x gradW L hL
      (ρ_lim.extend (clampToIcc T s)) (h_int_ρ_lim (clampToIcc T s))).continuous
  · intro s
    exact picardCharFlow_aemeasurable gradW L hL ρ_lim.extend h_int_ρ_lim charX charV hT.le
      hflow_on_ρlim h_boundary_ρlim f₀ (clampToIcc T s) (clampToIcc_mem hT.le s)
  · intro s x
    rw [h_rho_clamp s]
    exact h_int_ρ_lim (clampToIcc T s) x

/-- **Sub-helper for `_picard_fixedPointFlow`** — the Picard fixed-point
self-consistency equation.  For `t ∈ Icc 0 T`,

`ρ_lim.extend t = spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)`,

proved by the triangle through the iterates `x n`: the marginal-vs-limit leg
tends to `0` by `h_tendsto`, the flow-pushforward leg is `≤ Dn n · q` by the
pointwise contraction `picardLimit_flow_pointwise_contraction` (with
`Dn n := (supW1On (Icc 0 T) (x n).ρ ρ_lim.ρ).toReal → 0` from the
supW1On-Cauchy structure), and `picardLimit_fixed_point_eq` closes.  The
contraction ratio `q` is threaded by its defining equation `hq_def`
(let-bound parent supplies `rfl`). -/
private lemma picardLimit_self_consistency
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (m : ℝ → ℝ) (hMbar_nn : 0 ≤ m T)
    (hMbar_mono : ∀ t ∈ Set.Icc (0 : ℝ) T, m t ≤ m T)
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_lt : q < 1)
    (hq_def : q = gronwallBound 0 ((max 1 L : NNReal) : ℝ) (L : ℝ) T)
    (D₀ : ℝ) (hD₀_nn : 0 ≤ D₀)
    (x : ℕ → VlasovMeasureCurve d T m)
    (charXs charVs : ℕ → ℝ → PhaseSpace d → PhysSpace d)
    (h_contract : ∀ k, supW1On (Set.Icc 0 T) (x k).ρ (x (k + 1)).ρ ≤
      ENNReal.ofReal (q ^ k * D₀))
    (h_flow : ∀ k,
      IsCharacteristicFlowOn gradW (x k).extend (charXs k) (charVs k)
        (Set.Ioo 0 T) Set.univ ∧
      (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => charXs k s z) (charVs k t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charVs k s z)
          (-(convolveFunctionMeasure gradW ((x k).extend t) (charXs k t z)))
          (Set.Icc 0 T) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        (x (k + 1)).ρ t = Measure.map (fun z : PhaseSpace d => charXs k t z) f₀))
    (ρ_lim : VlasovMeasureCurve d T m)
    (h_tendsto : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Filter.Tendsto (fun n => wasserstein1 ((x n).ρ t) (ρ_lim.ρ t))
        Filter.atTop (nhds 0))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow_on_ρlim : IsCharacteristicFlowOn gradW ρ_lim.extend charX charV
      (Set.Ioo 0 T) Set.univ)
    (h_boundary_ρlim : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
      HasDerivWithinAt (fun s => charV s z)
        (-(convolveFunctionMeasure gradW (ρ_lim.extend t) (charX t z)))
        (Set.Icc 0 T) t)
    (h_int_ρ_lim : ∀ t (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (ρ_lim.extend t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ρ_lim.extend t =
      spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t) := by
  have he : ∀ (ν : VlasovMeasureCurve d T m) s, s ∈ Set.Icc (0 : ℝ) T →
      ν.extend s = ν.ρ s := by
    intro ν s hs
    unfold VlasovMeasureCurve.extend clampToIcc; congr 1
    rw [min_eq_left hs.2, max_eq_right hs.1]
  have hMm : ∀ (ν : VlasovMeasureCurve d T m), ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫ y, ‖y‖ ∂(ν.extend t) ≤ m T :=
    fun ν t _ => le_trans (VlasovMeasureCurve.extend_hasMoment hT.le ν t)
      (hMbar_mono (clampToIcc T t) (clampToIcc_mem hT.le t))
  have h_int_ext_gen : ∀ (ν : VlasovMeasureCurve d T m) (t : ℝ) (xp : PhysSpace d),
      Integrable (fun y => gradW (xp - y)) (ν.extend t) := fun ν t xp =>
    integrable_gradW_shift gradW L hL (ν.extend t)
      (VlasovMeasureCurve.extend_yIntegrable hT.le ν t) xp
  have hCI := fun k => envelopeStep_contractionInputs gradW L hL f₀ hf₀_int hT.le (x k)
    (m T) hMbar_nn (hMm (x k)) (charXs k) (charVs k)
    (h_flow k).1 (h_flow k).2.1 (h_int_ext_gen (x k))
  have hCI_lim := envelopeStep_contractionInputs gradW L hL f₀ hf₀_int hT.le ρ_lim
    (m T) hMbar_nn (hMm ρ_lim) charX charV hflow_on_ρlim h_boundary_ρlim h_int_ρ_lim
  have h_marg : ∀ s ∈ Set.Icc (0 : ℝ) T,
      spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)
        = Measure.map (fun z => charX s z) f₀ := by
    intro s hs
    have h_pair_meas := charFlow_measurable_via_gronwall gradW L hL ρ_lim.extend h_int_ρ_lim
      charX charV T hT.le hCI_lim.2.2.2.1 hCI_lim.2.2.2.2.1 hCI_lim.2.2.2.2.2 s hs
    unfold spatialMarginal vlasovSolutionViaPushforward
    rw [Measure.map_map measurable_fst h_pair_meas]
    rfl
  have h_cauchy := picard_iterate_isCauchy_of_contraction
    (Set.Icc (0 : ℝ) T) (fun n => (x n).ρ) q hq_nn hq_lt D₀ hD₀_nn h_contract
  have h_uniform := picard_iterate_limit_uniform_tendsto
    (Set.Icc (0 : ℝ) T) (fun n => (x n).ρ) ρ_lim.ρ h_cauchy h_tendsto
  have h_sup_ne_top : ∀ n, supW1On (Set.Icc 0 T) (x n).ρ ρ_lim.ρ ≠ ⊤ :=
    fun n => supW1On_ne_top_of_VlasovMeasureCurve (m T) hMbar_mono (x n) ρ_lim
  have h_sup_tendsto : Filter.Tendsto
      (fun n => supW1On (Set.Icc 0 T) (x n).ρ ρ_lim.ρ) Filter.atTop (nhds 0) := by
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    obtain ⟨N, hN⟩ := h_uniform ε hε
    refine ⟨N, fun n hn => ?_⟩
    unfold supW1On
    exact iSup_le fun s => iSup_le fun hs => hN n hn s hs
  set Dn : ℕ → ℝ := fun n => (supW1On (Set.Icc 0 T) (x n).ρ ρ_lim.ρ).toReal with hDn_def
  have hDn_nn : ∀ n, 0 ≤ Dn n := fun n => ENNReal.toReal_nonneg
  have hDn_tendsto : Filter.Tendsto Dn Filter.atTop (nhds 0) := by
    have h := (ENNReal.tendsto_toReal (show (0:ENNReal) ≠ ⊤ by simp)).comp h_sup_tendsto
    rw [ENNReal.toReal_zero] at h
    exact h
  have h_W1_fin_curve : ∀ n, ∀ s ∈ Set.Icc (0 : ℝ) T,
      wasserstein1 ((x n).extend s) (ρ_lim.extend s) ≠ ⊤ := by
    intro n s hs
    rw [he (x n) s hs, he ρ_lim s hs]
    have := (x n).isProb s; have := ρ_lim.isProb s
    exact wasserstein1_ne_top_of_finite_moment _ _
      ((x n).yIntegrable s hs) (ρ_lim.yIntegrable s hs)
  have h_W1_bound_curve : ∀ n, ∀ s ∈ Set.Icc (0 : ℝ) T,
      (wasserstein1 ((x n).extend s) (ρ_lim.extend s)).toReal ≤ Dn n := by
    intro n s hs
    rw [he (x n) s hs, he ρ_lim s hs]
    exact ENNReal.toReal_mono (h_sup_ne_top n)
      (wasserstein1_le_supW1On (Set.Icc 0 T) (x n).ρ ρ_lim.ρ s hs)
  have h_term2 : ∀ n t, t ∈ Set.Icc (0 : ℝ) T →
      (wasserstein1 (Measure.map (fun z => charXs n t z) f₀)
                    (Measure.map (fun z => charX t z) f₀)).toReal ≤ Dn n * q :=
    fun n t ht => picardLimit_flow_pointwise_contraction gradW L hL f₀ hf₀_int hT
      m hMbar_nn hMbar_mono (x n) ρ_lim (charXs n) (charVs n) charX charV
      (h_flow n).1 (h_flow n).2.1 hflow_on_ρlim h_boundary_ρlim
      (Dn n) (hDn_nn n) (h_W1_fin_curve n) (h_W1_bound_curve n) q hq_def t ht
  intro t ht
  rw [he ρ_lim t ht, h_marg t ht]
  exact picardLimit_fixed_point_eq f₀ m x ρ_lim charXs charX
    (fun n t' ht' => (h_flow n).2.2 t' ht') h_tendsto
    (fun n t' ht' => (hCI n).1 t' ht') (fun t' ht' => hCI_lim.1 t' ht')
    (fun n t' ht' => (hCI n).2.2.1 t' ht') (fun t' ht' => hCI_lim.2.2.1 t' ht')
    Dn q (by simpa using hDn_tendsto.mul_const q) h_term2 t ht

/-- **Sub-helper for `vlasovWellPosedness_local`** — the Picard fixed-point
self-consistent flow.

Given `f₀ : Measure (PhaseSpace d)` with finite first moment, produces a
characteristic flow `(charX, charV)` whose **own pushforward's spatial
marginal** is the reference measure the flow is built against — i.e., the
Picard fixed point at the spatial-marginal-curve level:

  `ρ_t := spatialMarginal (Measure.map (z ↦ (charX t z, charV t z)) f₀)`
  `charX, charV solve the Vlasov ODE against this ρ`.

The body carries the substantive Picard analysis:

* M-fixed-point: pick a moment bound `M ≥ A/(1 - B)` where
  `A = gronwallBound 1 (1+L) ‖gradW 0‖ T · (M_f₀ + 1)` and
  `B = L · (exp((1+L)·T) - 1)/(1+L) · (M_f₀ + 1)`.  Requires `B < 1`,
  which is the genuine convergence criterion for the moment iteration
  (stronger than the contraction predicate `LocalSmallnessContraction
  L T` alone for large `M_f₀` — the contraction predicate gates the q
  factor; the M-fixed-point additionally requires the moment iteration
  to converge).
* Picard sequence `x_n : ℕ → VlasovMeasureCurve d T M` starting from
  `x_0 := constantCurve (spatialMarginal f₀)` and `x_{n+1} := Phi_step(x_n)`.
* Contraction via `Phi_supW1_contraction`: `supW1On (Φρ) (Φσ) ≤ q · D`
  with `q < 1`.  Apply `picard_iterate_isCauchy_of_contraction` +
  `picard_iterate_exists_limit` to get the W₁-limit
  `ρ_lim : VlasovMeasureCurve d T M`.
* Self-consistency `Φ(ρ_lim) = ρ_lim`: triangle through `x_n`.
* Apply `exists_vlasov_characteristicFlow_global_smallT` to `ρ_lim.extend`
  to get the flow.

**Metric-dependence note**.  The convergence rests on two independent
predicates:
* `LocalSmallnessContraction L T := L · (exp((max 1 L)·T) - 1) / (max 1 L) < 1`
  — exponential in T, from `Phi_supW1_contraction`'s W₁-based shape.
* `LocalSmallnessPLBuffer L T := L · T² < 1` — quadratic, from
  per-ball Picard-Lindelöf's ball geometry.

These are genuinely independent (neither universally implies the other), so
each predicate matches its own sub-argument.

Under the Wbar refactor (Dobrushin 1979, §5), both constraints become
linear-in-T and align: `LocalSmallnessContraction` reduces to
`C₂(L)·T < 1`, and the single algebraic constraint then suffices and is
satisfiable for any `L > 0` by taking `T < 1/C₂(L)`.

**Output bundle** (designed to feed
`vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn` directly):

* Flow `(charX, charV)` against the *spatial marginal of the pushforward*
  — the load-bearing self-consistency conjunct.
* Boundary regularity.
* Uniform moment bound `M_ρ` on the spatial marginal trajectory. -/
theorem vlasovWellPosedness_local_picard_fixedPointFlow
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (hTL_PL : LocalSmallnessPLBuffer L T)
    (hTL_con : LocalSmallnessContraction L T)
    (hB : (L : ℝ) / (1 + (L : ℝ)) * (Real.exp ((1 + (L : ℝ)) * T) - 1) < 1) :
    ∃ (charX charV : ℝ → PhaseSpace d → PhysSpace d) (M_ρ : ℝ), 0 ≤ M_ρ ∧
      -- Self-consistent characteristic flow: against the spatial marginal
      -- of its own phase-space pushforward.
      IsCharacteristicFlowOn gradW
        (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
        charX charV (Set.Ioo 0 T) Set.univ ∧
      -- Boundary regularity: HasDerivWithinAt on `Icc 0 T` for every z and
      -- t ∈ Icc 0 T.
      (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV s z)
          (-(convolveFunctionMeasure gradW
              (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
              (charX t z)))
          (Set.Icc 0 T) t) ∧
      -- Uniform first-moment bound on the spatial-marginal trajectory.
      (∀ s ∈ Set.Icc (0 : ℝ) T,
        ∫ y, ‖y‖ ∂(spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) ≤ M_ρ) ∧
      -- First-moment integrability on the spatial-marginal trajectory.
      (∀ s ∈ Set.Icc (0 : ℝ) T,
        Integrable (fun y : PhysSpace d => ‖y‖)
          (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))) ∧
      -- Continuity of the convolution force in `x` (uniformly in `s`).
      (∀ s, Continuous (fun x =>
        convolveFunctionMeasure gradW
          (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x)) ∧
      -- **AEMeasurable witness**, projected from the Picard fixed-point
      -- construction's continuity-in-z — supplies the `h_aemeas` conjunct
      -- in downstream `_finalAssembly_*`.
      (∀ s, AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀) ∧
      -- **Universal-in-s convolution integrability**.  For `s ∈ Icc 0 T`
      -- follows from `h_y_int_ρ` + Lipschitz of `gradW`; the extension to
      -- all `s` uses constant-extension (clamp) past T inside the Picard
      -- construction.  Supplies the `h_int_conv` conjunct in downstream
      -- `_finalAssembly_*`.
      (∀ s (x : PhysSpace d),
        Integrable (fun y => gradW (x - y))
          (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))) := by
  -- ============================================================
  -- Step 1: Spatial marginal setup.
  -- μ₀ := spatialMarginal f₀ = Measure.map Prod.fst f₀.
  -- IsProbabilityMeasure μ₀ via Measure.isProbabilityMeasure_map.
  -- Integrable ‖·‖ μ₀ from hf₀_int via integral_map on Prod.fst.
  -- ============================================================
  have hμ₀_prob : IsProbabilityMeasure (spatialMarginal f₀) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hμ₀_int : Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal f₀) := by
    unfold spatialMarginal
    rw [integrable_map_measure
      (Continuous.aestronglyMeasurable continuous_norm) measurable_fst.aemeasurable]
    -- Need: Integrable (‖·‖ ∘ Prod.fst) f₀ = Integrable (fun z => ‖z.1‖) f₀.
    -- This follows from hf₀_int (Integrable ‖·‖ f₀) and ‖z.1‖ ≤ ‖z‖.
    refine hf₀_int.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact (measurable_fst.norm.aestronglyMeasurable)
    · simp only [Function.comp_def, Real.norm_of_nonneg (norm_nonneg _)]
      exact (norm_fst_le z)
  -- **F1 (phase-space anchor)**: `M_f₀` is the *phase-space* first moment
  -- `∫z‖z‖∂f₀`, NOT the spatial marginal — matching `phi_moment_envelope_le`'s
  -- (A.2) `integral_map` initial value, so the envelope dominates both the
  -- pushforward moments (A.2) and the spatial base case (`∫‖x‖∂μ₀ ≤ M_f₀`).
  let M_f₀ : ℝ := ∫ z : PhaseSpace d, ‖z‖ ∂f₀
  have hM_f₀_nn : 0 ≤ M_f₀ := integral_nonneg (fun z => norm_nonneg z)
  -- ============================================================
  -- Step 2: time-dependent moment envelope `m` (option 2, dissolving the
  -- constant-`M` fixed-point).  `gronwall_envelope_exists` (Piece A.3) under
  -- `hB := B(T) < 1` yields a monotone `m` that is `Φ`-invariant at the moment
  -- level, so `Φ : space(m) → space(m)` and the Picard sequence stays in one
  -- fixed curve space.
  -- ============================================================
  obtain ⟨m, hm_mono, hm_ge, hm_inv⟩ :=
    gronwall_envelope_exists M_f₀ ‖gradW 0‖ hM_f₀_nn (norm_nonneg _) L T hT.le hB
  have hm_nn : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ m t :=
    fun t ht => le_trans hM_f₀_nn (hm_ge t ht)
  have hMbar_nn : 0 ≤ m T := hm_nn T ⟨hT.le, le_refl T⟩
  have hMbar_mono : ∀ t ∈ Set.Icc (0 : ℝ) T, m t ≤ m T :=
    fun t ht => hm_mono ht ⟨hT.le, le_refl T⟩ ht.2
  -- ============================================================
  -- Step 3: Convolution integrability for constantCurve.
  -- For the base case x 0 = constantCurve μ₀, need h_int_ext:
  --   ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) ((constantCurve μ₀).extend t).
  -- This reduces to: Integrable (fun y => gradW (x - y)) μ₀, which follows
  -- from hμ₀_int + Lipschitz bound on gradW.
  -- Integrability of gradW against μ₀.
  -- ============================================================
  have h_int_gradW_μ₀ : ∀ (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (spatialMarginal f₀) :=
    fun x_pt => integrable_gradW_shift gradW L hL (spatialMarginal f₀) hμ₀_int x_pt
  -- ============================================================
  -- Step 4: Picard sequence + contraction bound.
  -- The sequence x : ℕ → VlasovMeasureCurve d T M is built by Phi_step +
  -- induction; the contraction estimate uses Phi_supW1_contraction applied
  -- to consecutive iterates.
  -- ============================================================
  -- `q` is the M-INDEPENDENT genuine contraction ratio (not 2M·q_true).
  -- `Phi_supW1_contraction` outputs `q · D` per step, so `q^k · D₀ =
  -- q^k · (2M)` is the iterated contraction bound; the contraction factor
  -- `q = gronwallBound 0 (max 1 L) L T = (L/(max 1 L)) · (exp((max 1 L)·T) - 1)`
  -- is separated from the W₁-input bound `D₀ = 2M`.  `hq_lt` closes by direct
  -- citation of `hTL_con` (LocalSmallnessContraction) after one unfold.
  let q : ℝ := gronwallBound 0 ((max 1 L : NNReal) : ℝ) (L : ℝ) T
  have hq_nn : 0 ≤ q := by
    have hK_nn : (0 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := NNReal.coe_nonneg _
    have hε_nn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
    have := gronwallBound_mono (δ := (0 : ℝ)) (K := ((max 1 L : NNReal) : ℝ))
      (ε := (L : ℝ)) (le_refl 0) hε_nn hK_nn hT.le
    rw [gronwallBound_x0] at this; exact this
  -- Direct citation: `LocalSmallnessContraction L T` IS `q < 1` after
  -- unfolding both definitions.  No local derivation; the named-lemma
  -- pattern from the soundness-fix mechanism.
  have hq_lt : q < 1 := hTL_con.gronwallBound_lt_one
  -- D₀: initial supW1On bound = supW1On (x 0).ρ (x 1).ρ ≤ 2 * M.
  let D₀ : ℝ := 2 * (m T)
  have hD₀_nn : 0 ≤ D₀ := by linarith [hMbar_nn]
  -- Picard sequence + contraction, in the fixed envelope space `m`.  The
  -- recursion uses `Phi_step_envelope` per step + `Phi_supW1_contraction`
  -- for the geometric bound.
  -- **Enriched existential**: the Picard sequence exposes, per
  -- step `k`, the flow `(charXs k, charVs k)` against `(x k).extend` — exactly
  -- `Phi_step_envelope`'s output shape — plus the pushforward identity
  -- `(x(k+1)).ρ t = map (charXs k t) f₀`.  Exposing the flows lets the
  -- self-consistency proof (Step 8) feed them directly to `Phi_supW1_contraction`,
  -- dissolving the (un-banked) ODE-uniqueness that re-deriving them would need.
  have hμ₀_int_fst : Integrable (fun z : PhaseSpace d => ‖z.1‖) f₀ :=
    hf₀_int.mono' measurable_fst.norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact norm_fst_le z)
  have hμ₀_le_m : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫ y, ‖y‖ ∂(spatialMarginal f₀) ≤ m t := by
    intro t ht
    have h_eq : ∫ y, ‖y‖ ∂(spatialMarginal f₀) = ∫ z, ‖z.1‖ ∂f₀ := by
      unfold spatialMarginal
      rw [integral_map measurable_fst.aemeasurable continuous_norm.aestronglyMeasurable]
    have h_le : ∫ z, ‖z.1‖ ∂f₀ ≤ M_f₀ :=
      integral_mono hμ₀_int_fst hf₀_int (fun z => norm_fst_le z)
    rw [h_eq]; exact le_trans h_le (hm_ge t ht)
  obtain ⟨x, charXs, charVs, h_contract, h_flow⟩ :=
    vlasovWellPosedness_local_picard_sequence W gradW hgradW L hL f₀ hf₀_int hT hTL_PL
      m hm_mono hm_nn hm_inv hMbar_nn hMbar_mono hμ₀_prob hμ₀_int hμ₀_le_m
      q hq_nn rfl D₀ hD₀_nn rfl
  -- ============================================================
  -- Step 5: Extract limit ρ_lim via picard_iterate_exists_limit.
  -- ============================================================
  obtain ⟨ρ_lim, h_tendsto⟩ :=
    picard_iterate_exists_limit x q hq_nn hq_lt D₀ hD₀_nn h_contract
  -- ============================================================
  -- Step 6: Convolution integrability for ρ_lim.extend.
  -- Needed by exists_vlasov_characteristicFlow_global_smallT.
  -- Integrability of gradW against ρ_lim.extend t.
  -- ============================================================
  have h_int_ρ_lim : ∀ t (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (ρ_lim.extend t) := fun t x_pt =>
    integrable_gradW_shift gradW L hL (ρ_lim.extend t)
      (VlasovMeasureCurve.extend_yIntegrable hT.le ρ_lim t) x_pt
  -- Convolution continuity for ρ_lim.extend, universal in t.
  -- Deduced from ρ_lim.extend_convCont + h_int_ρ_lim restricted to Icc 0 T.
  have h_conv_cont_ρ_lim : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ_lim.extend t) x) := by
    intro x_pt
    have h_int_Icc : ∀ t ∈ Set.Icc (0 : ℝ) T,
        Integrable (fun y => gradW (x_pt - y)) (ρ_lim.ρ t) := by
      intro t ht
      have h_eq : ρ_lim.extend t = ρ_lim.ρ t := by
        unfold VlasovMeasureCurve.extend clampToIcc
        congr 1
        rw [min_eq_left ht.2, max_eq_right ht.1]
      rw [← h_eq]; exact h_int_ρ_lim t x_pt
    exact VlasovMeasureCurve.extend_convCont gradW L hL hT.le ρ_lim x_pt h_int_Icc
  -- ============================================================
  -- Step 7: Flow construction via exists_vlasov_characteristicFlow_global_smallT.
  -- Build (charX, charV) against ρ_lim.extend.
  -- ============================================================
  obtain ⟨charX, charV, hflow_on_ρlim, h_boundary_ρlim⟩ :=
    exists_vlasov_characteristicFlow_global_smallT W gradW hgradW L hL
      ρ_lim.extend h_int_ρ_lim h_conv_cont_ρ_lim
      (fun t => VlasovMeasureCurve.extend_yIntegrable hT.le ρ_lim t)
      (m T) hMbar_nn
      (fun t => le_trans (VlasovMeasureCurve.extend_hasMoment hT.le ρ_lim t)
        (hMbar_mono (clampToIcc T t) (clampToIcc_mem hT.le t)))
      T hT.le hTL_PL
  -- ============================================================
  -- Step 8: Self-consistency.  For t ∈ Icc 0 T,
  --   ρ_lim.ρ t = spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t).
  -- This is the Picard fixed-point equation: Phi charX f₀ t = ρ_lim.ρ t,
  -- proved by triangle through x n using contraction + tendsto.
  -- ============================================================
  -- ============================================================
  -- Self-consistency on Icc 0 T.
  -- For t ∈ Icc 0 T:
  --   ρ_lim.extend t = ρ_lim.ρ t   (by clampToIcc identity on Icc)
  --   ρ_lim.ρ t = spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)
  -- The second equality is the Picard fixed-point equation, proved by triangle
  -- through x n using contraction + tendsto.
  -- ============================================================
  have h_self_consist : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ρ_lim.extend t =
      spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t) :=
    -- Step 8 extracted as `picardLimit_self_consistency`; the let-bound `q`'s
    -- defining equation is supplied by `rfl`.
    picardLimit_self_consistency gradW L hL f₀ hf₀_int hT m hMbar_nn hMbar_mono
      q hq_nn hq_lt rfl D₀ hD₀_nn x charXs charVs h_contract h_flow
      ρ_lim h_tendsto charX charV hflow_on_ρlim h_boundary_ρlim h_int_ρ_lim
  -- ============================================================
  -- Step 9: Bundle with a CLAMPED flow `cX s := charX (clampToIcc T s)`.
  --
  -- The raw flow from `exists_vlasov_characteristicFlow_global_smallT` is
  -- controlled only on `[0, T]`; off-window it is uncontrolled
  -- `Classical.choose` data with no growth bound.  The conclusion's
  -- universal-in-`s` conjuncts (convolution integrability + continuity-in-x
  -- for ALL `s`) therefore cannot hold for the raw flow.  We return instead
  -- the clamped flow, whose pushforward at any `s` equals the on-window
  -- pushforward at `clampToIcc T s ∈ [0, T]` — hence globally controlled.
  -- On `[0, T]` the clamp is the identity (`clampToIcc T s = s`), so every
  -- window conjunct (flow ODE on Ioo, boundary on Icc, moment, integrability)
  -- transfers from the raw flow via `clampToIcc`-congruence.
  -- ============================================================
  exact picardFlow_clamp_bundle gradW L hL f₀ hT m hMbar_nn hMbar_mono ρ_lim
    charX charV hflow_on_ρlim h_boundary_ρlim h_int_ρ_lim h_self_consist

/-- **Sub-helper for `vlasovWellPosedness_local`** — moment-bound transport.

Given the Picard fixed-point flow's bundle (from
`_picard_fixedPointFlow`), produces `HasFiniteFirstMoment (f t)` for
`t ∈ Icc 0 T`, where `f := vlasovSolutionViaPushforward charX charV f₀`.

**Proof strategy**:

1. Boundary transport: extract `h_init / h_cont_Icc / h_deriv_Ico` from
   `hflow_on + h_boundary` via `characteristicFlow_boundary_regularity`.
2. `flow_distance_growth_bound_on` applied to `(charX, charV)` produces
   the growth constant `C_T` with `‖(charX t z, charV t z)‖ ≤ C_T * (‖z‖ + 1)`.
3. Probability of `f t = Measure.map (z ↦ (charX t z, charV t z)) f₀` from
   the AEMeasurable witness.
4. Integrable `‖·‖` on `f t`: via `integrable_map_measure` + growth bound +
   `Integrable ‖·‖ f₀`.

Factored out to keep `vlasovWellPosedness_local`'s body a clean glue. -/
theorem vlasovWellPosedness_local_moment
    {d : ℕ}
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (_hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (_hTL_PL : LocalSmallnessPLBuffer L T)
    (_hTL_con : LocalSmallnessContraction L T)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hflow_on : IsCharacteristicFlowOn gradW
      (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
      charX charV (Set.Ioo 0 T) Set.univ)
    (h_boundary : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
      HasDerivWithinAt (fun s => charV s z)
        (-(convolveFunctionMeasure gradW
            (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
            (charX t z)))
        (Set.Icc 0 T) t)
    (hM_ρ_bound : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∫ y, ‖y‖ ∂(spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) ≤ M_ρ)
    (h_y_int_ρ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖)
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)))
    (_hconv_cont : ∀ s, Continuous (fun x =>
      convolveFunctionMeasure gradW
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x))
    -- Passed from `_picard_fixedPointFlow`'s enriched output: the
    -- AEMeasurable witness + universal-in-s convolution integrability.
    (h_aemeas : ∀ s, AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀)
    (h_int_conv : ∀ s (x : PhysSpace d),
      Integrable (fun y => gradW (x - y))
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasFiniteFirstMoment (vlasovSolutionViaPushforward charX charV f₀ t) := by
  -- IsProbabilityMeasure for the spatial marginal (needed for the flow typeclass).
  -- spatialMarginal μ = Measure.map Prod.fst μ, so IsProbabilityMeasure_map needs
  -- AEMeasurable Prod.fst (Measure.map ... f₀). Since Prod.fst is measurable,
  -- it is AEMeasurable wrt any measure.
  have hρ_prob : ∀ s, IsProbabilityMeasure
      (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) := by
    intro s
    unfold spatialMarginal vlasovSolutionViaPushforward
    -- Need IsProbabilityMeasure (Measure.map Prod.fst (Measure.map (fun z => ...) f₀))
    -- Use Measure.map_map to compose, then isProbabilityMeasure_map on the composition.
    have h_aemeas_pair : AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀ :=
      h_aemeas s
    have h_prob_inner : IsProbabilityMeasure
        (Measure.map (fun z : PhaseSpace d => (charX s z, charV s z)) f₀) :=
      Measure.isProbabilityMeasure_map h_aemeas_pair
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  -- Step 1: Extract h_init, h_cont_Icc, h_deriv_Ico via boundary transport.
  obtain ⟨h_init, h_cont_Icc, h_deriv_Ico⟩ :=
    characteristicFlow_boundary_regularity gradW
      (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
      charX charV T hT.le hflow_on h_boundary
  -- Step 2: Growth bound from flow_distance_growth_bound_on.
  obtain ⟨C_T, hC_T_nn, h_growth⟩ :=
    flow_distance_growth_bound_on gradW L hL
      (fun s => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))
      charX charV T hT.le
      h_init h_cont_Icc h_deriv_Ico
      M_ρ hM_ρ_nn hM_ρ_bound h_y_int_ρ h_int_conv
  -- Step 3: Conclude HasFiniteFirstMoment.
  unfold HasFiniteFirstMoment vlasovSolutionViaPushforward
  refine ⟨Measure.isProbabilityMeasure_map (h_aemeas t), ?_⟩
  -- Integrable ‖·‖ wrt Measure.map (fun z => (charX t z, charV t z)) f₀.
  rw [integrable_map_measure
    (Continuous.aestronglyMeasurable continuous_norm) (h_aemeas t)]
  -- Now need: Integrable (fun z : PhaseSpace d => ‖(charX t z, charV t z)‖) f₀.
  have h_dom_int : Integrable (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) f₀ := by
    have h1 : Integrable (fun z : PhaseSpace d => C_T * ‖z‖) f₀ :=
      hf₀_int.const_mul C_T
    have h2 : Integrable (fun _ : PhaseSpace d => C_T) f₀ := integrable_const _
    have h_eq : (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) =
                fun z => C_T * ‖z‖ + C_T := by funext z; ring
    rw [h_eq]; exact h1.add h2
  -- The goal after rw is: Integrable (‖·‖ ∘ fun z => (charX t z, charV t z)) f₀
  -- = Integrable (fun z => ‖(charX t z, charV t z)‖) f₀.
  -- Dominator: C_T * (‖z‖ + 1); AE bound from h_growth.
  have h_norm_aesm : AEStronglyMeasurable
      (fun z : PhaseSpace d => ‖(charX t z, charV t z)‖) f₀ :=
    (h_aemeas t).norm.aestronglyMeasurable
  refine h_dom_int.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · -- AEStronglyMeasurable of ‖·‖ ∘ (charX t, charV t).
    -- After integrable_map_measure rewrite, goal is for the composition form.
    convert h_norm_aesm using 1
    rfl
  · -- Pointwise bound: ‖(charX t z, charV t z)‖ ≤ C_T * (‖z‖ + 1).
    -- The norm in the goal is ‖(‖·‖ ∘ ...)(z)‖ = ‖‖(charX t z, charV t z)‖‖.
    simp only [Function.comp_def, Real.norm_of_nonneg (norm_nonneg _)]
    exact h_growth t ht z

/-- **Sub-helper for `vlasovWellPosedness_local`** — IsLagrangianVlasovSolutionOn
threading.

Given the Picard fixed-point flow's bundle (from
`_picard_fixedPointFlow`), produces the
`IsLagrangianVlasovSolutionOn gradW f T` conjunct via the 20-hypothesis
threading through
`vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn`.

**Proof strategy**:

1. Boundary transport: extract `h_init / h_cont_Icc / h_deriv_Ico`.
2. Universal-in-`s` convolution integrability (handling `s` outside
   `[0, T]` via the clamp-extension argument).
3. AEMeasurable witness.
4. `IsCharacteristicFlowSelfConsistent`: `∀ t, ρ_lim t = Φ charX f₀ t`,
   which expands by definition since `ρ_lim = spatialMarginal ∘ f` and
   `f = vlasovSolutionViaPushforward charX charV f₀`; spatial marginal
   of pushforward = pushforward under `Prod.fst ∘ ...` = `Φ charX f₀`.
   The composition is the `Measure.map_map`-with-AEMeasurable bridge.
5. Continuity of `gradW`: `hL.continuous`.
6. Probability instance of `spatialMarginal ∘ f`: derived from
   AEMeasurable + IsProbabilityMeasure f₀.
7. Final invocation: `vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn`
   with the full hypothesis bundle.

Factored out to keep `vlasovWellPosedness_local`'s body a clean glue. -/
theorem vlasovWellPosedness_local_isLagrangian
    {d : ℕ}
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (_hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (_hTL_PL : LocalSmallnessPLBuffer L T)
    (_hTL_con : LocalSmallnessContraction L T)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hflow_on : IsCharacteristicFlowOn gradW
      (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
      charX charV (Set.Ioo 0 T) Set.univ)
    (h_boundary : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
      HasDerivWithinAt (fun s => charV s z)
        (-(convolveFunctionMeasure gradW
            (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
            (charX t z)))
        (Set.Icc 0 T) t)
    (hM_ρ_bound : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∫ y, ‖y‖ ∂(spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) ≤ M_ρ)
    (h_y_int_ρ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖)
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)))
    (hconv_cont : ∀ s, Continuous (fun x =>
      convolveFunctionMeasure gradW
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x))
    -- Passed from `_picard_fixedPointFlow`'s enriched output: the
    -- AEMeasurable witness + universal-in-s convolution integrability.
    (h_aemeas : ∀ s, AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀)
    (h_int_conv : ∀ s (x : PhysSpace d),
      Integrable (fun y => gradW (x - y))
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))) :
    IsLagrangianVlasovSolutionOn gradW
      (vlasovSolutionViaPushforward charX charV f₀) T := by
  -- IsProbabilityMeasure for the spatial marginal (needed for the target typeclass).
  have hρ_prob : ∀ s, IsProbabilityMeasure
      (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) := by
    intro s
    unfold spatialMarginal vlasovSolutionViaPushforward
    have h_aemeas_pair : AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀ :=
      h_aemeas s
    have _h_prob_inner : IsProbabilityMeasure
        (Measure.map (fun z : PhaseSpace d => (charX s z, charV s z)) f₀) :=
      Measure.isProbabilityMeasure_map h_aemeas_pair
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  -- Step 1: Extract h_init, h_cont_Icc, h_deriv_Ico via boundary transport.
  obtain ⟨h_init, h_cont_Icc, h_deriv_Ico⟩ :=
    characteristicFlow_boundary_regularity gradW
      (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
      charX charV T hT.le hflow_on h_boundary
  -- Step 2: IsCharacteristicFlowSelfConsistent
  -- ρ t = spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)
  --     = Measure.map Prod.fst (Measure.map (fun z => (charX t z, charV t z)) f₀)
  --     = Measure.map (Prod.fst ∘ fun z => (charX t z, charV t z)) f₀
  --         [by map_map_of_aemeasurable]
  --     = Measure.map (charX t) f₀
  have hself : IsCharacteristicFlowSelfConsistent charX f₀
      (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) := by
    intro t
    simp only []
    unfold spatialMarginal vlasovSolutionViaPushforward
    -- Goal: Measure.map Prod.fst (Measure.map (fun z => (charX t z, charV t z)) f₀)
    --     = Measure.map (fun z => charX t z) f₀
    have h_comp : Measure.map Prod.fst
        (Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) f₀) =
        Measure.map (Prod.fst ∘ fun z : PhaseSpace d => (charX t z, charV t z)) f₀ := by
      apply AEMeasurable.map_map_of_aemeasurable
      · exact measurable_fst.aemeasurable
      · exact h_aemeas t
    rw [h_comp]; congr 1
  -- Step 3: Apply the main threading theorem.
  exact vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn
    gradW L hL charX charV f₀ hf₀_int hT
    hflow_on h_init h_cont_Icc h_deriv_Ico
    M_ρ hM_ρ_nn hM_ρ_bound h_y_int_ρ h_int_conv
    hself h_aemeas hL.continuous hconv_cont

/-- **Local existence of a Vlasov solution on `[0, T]`.**

Under the joint constraint `LocalSmallnessPLBuffer L T` (`L · T² < 1`) +
`LocalSmallnessContraction L T`, produces a local-time Vlasov solution
`f : ℝ → Measure (PhaseSpace d)` on `[0, T]` satisfying initial
condition + local finite first moment + `IsLagrangianVlasovSolutionOn`.

The forward-iteration continuation extends from local `T` to arbitrary
`T_target` via **fixed-`T_0`** iteration: the contraction time `T_0`
depends only on `L` (not on the moment bound `M_n` propagating through
iterations), because `Phi_supW1_contraction`'s `q` is
`gronwallBound 0 (max 1 L) (L · D) T` — independent of `M_n`.  So the
continuation iterates `[0, T_0], [T_0, 2 T_0], …` with constant step `T_0`,
reaching any `T_target` in `⌈T_target / T_0⌉` windows; gluing then bridges
from `IsLagrangianVlasovSolutionOn` (local) to `IsLagrangianVlasovSolution`
(global).

**Proof strategy**:

1. Initial spatial marginal: `μ₀ := spatialMarginal f₀`.  By
   `HasFiniteFirstMoment f₀`, `μ₀` is a probability measure with
   `Integrable ‖·‖`.  Let `M_f₀ := ∫ ‖z‖ ∂f₀` (finite by
   `hf₀.2.integral_norm_le`).

2. Picard sequence on spatial marginals:
   - `ρ_0 := constantCurve μ₀`.
   - `ρ_{n+1}` obtained via `Phi_step` applied to `ρ_n`'s flow.

   Each `ρ_n` lives in `VlasovMeasureCurve d T M` for an appropriate
   `M` chosen so that the growth bound from
   `flow_distance_growth_bound_on` stays within `M` across iterations
   (the M-preservation constraint).

3. Contraction estimate via `Phi_supW1_contraction`:
   `supW1On (ρ_n.ρ) (ρ_{n+1}.ρ) ≤ ENNReal.ofReal (q^n * D₀)`
   for `q := gronwallBound 0 (max 1 L) (L · D) T < 1` (since `T` is
   small enough per the joint constraint).

4. Apply `picard_iterate_isCauchy_of_contraction` to get the ENNReal-form
   Cauchy condition on the `supW1On` pseudodistance.

5. Apply `picard_iterate_exists_limit` to extract the
   limit `ρ_lim : VlasovMeasureCurve d T M` plus pointwise W₁-tendsto.

6. Self-consistency `Φ(ρ_lim) = ρ_lim`: triangle through `ρ_n` using
   the uniform-tendsto helper, contraction, and pointwise tendsto.

7. Apply `exists_vlasov_characteristicFlow_global_smallT`
   to `ρ_lim.extend` to get the characteristic flow `(charX, charV)`
   against the self-consistent limit.

8. Define `f := vlasovSolutionViaPushforward charX charV f₀`.  Verify:
   - `f 0 = f₀` (from `IsCharacteristicFlowOn`'s initial-condition
     clause + `Measure.map_id`).
   - `HasFiniteFirstMoment (f t)` on `[0, T]` (from
     `flow_distance_growth_bound_on` applied to `(charX, charV)` +
     `hf₀.2`).
   - `IsLagrangianVlasovSolutionOn gradW f T` via
     `vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn`.

The body invokes `vlasovWellPosedness_local_picard_fixedPointFlow` for the
Picard fixed-point flow, then `vlasovWellPosedness_local_finalAssembly_*`
for the moment and Lagrangian conjuncts, deriving `f 0 = f₀` inline. -/
theorem vlasovWellPosedness_local
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d))
    (hf₀ : HasFiniteFirstMoment f₀)
    {T : ℝ} (hT : 0 < T)
    (hTL_PL : LocalSmallnessPLBuffer L T)
    (hTL_con : LocalSmallnessContraction L T)
    (hB : (L : ℝ) / (1 + (L : ℝ)) * (Real.exp ((1 + (L : ℝ)) * T) - 1) < 1) :
    ∃ (f : ℝ → Measure (PhaseSpace d))
      (charX charV : ℝ → PhaseSpace d → PhysSpace d),
      f 0 = f₀ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t)) ∧
      -- FLAT (window-constant) uniform first-moment bound on the spatial marginal.
      (∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M) ∧
      IsLagrangianVlasovSolutionOn gradW f T ∧
      -- Explicit flow bundle: pushforward, AEMeasurable, and boundary derivatives.
      -- These use the SAME charX charV as the outer ∃ (not the hidden witnesses
      -- inside IsLagrangianVlasovSolutionOn), enabling downstream consumers to
      -- use them without witness-identity issues.
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        f t = Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) (f 0)) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) (f 0)) ∧
      (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (f t)) (charX t z)))
          (Set.Icc 0 T) t) ∧
      -- Initial condition for the outer charX charV (same witnesses as boundary bundle above).
      (∀ z : PhaseSpace d, charX 0 z = z.1 ∧ charV 0 z = z.2) := by
  -- The body is decomposed into two sub-helpers plus an inline glue:
  --   * `vlasovWellPosedness_local_picard_fixedPointFlow` carries the Picard
  --     mathematics — spatial-marginal setup, the Picard sequence via
  --     `Phi_step`, the contraction estimate via `Phi_supW1_contraction`,
  --     the limit via `picard_iterate_exists_limit`,
  --     self-consistency `Φ(ρ_lim) = ρ_lim`, and the flow construction via
  --     `exists_vlasov_characteristicFlow_global_smallT`.
  --   * `vlasovWellPosedness_local_finalAssembly_*` thread the moment and
  --     `IsLagrangianVlasovSolutionOn` conjuncts through
  --     `vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn`.
  --   * This body invokes both, derives `f 0 = f₀` inline, and assembles.
  obtain ⟨hf₀_prob, hf₀_int⟩ := hf₀
  have : IsProbabilityMeasure f₀ := hf₀_prob
  -- Sub-helper invocation: produces the self-consistent flow + regularity
  -- + AEMeasurable witness + universal-in-s convolution integrability.
  obtain ⟨charX, charV, _M_ρ, _hM_ρ_nn, _hflow_on, _h_boundary,
          _hM_ρ_bound, _h_y_int_ρ, _hconv_cont, _h_aemeas, _h_int_conv⟩ :=
    vlasovWellPosedness_local_picard_fixedPointFlow W gradW hgradW L hL
      f₀ hf₀_int hT hTL_PL hTL_con hB
  -- Bundle the f-shape result.
  refine ⟨vlasovSolutionViaPushforward charX charV f₀, charX, charV, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (a) f 0 = f₀.  The flow's initial-condition clause gives
    -- (charX 0 z, charV 0 z) = z for every z, so the pushforward at t = 0
    -- is `Measure.map id f₀ = f₀`.  Proved inline via the sub-helper's
    -- initial-condition projection at t = 0.
    have h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z := by
      intro z
      have := (_hflow_on.1 z (Set.mem_univ z))
      exact Prod.ext this.1 this.2
    change vlasovSolutionViaPushforward charX charV f₀ 0 = f₀
    unfold vlasovSolutionViaPushforward
    have h_at_0 : (fun z : PhaseSpace d => (charX 0 z, charV 0 z)) = id := by
      funext z; exact h_init z
    rw [h_at_0, Measure.map_id]
  · -- (b) HasFiniteFirstMoment (f t) on Icc 0 T.  Deferred to the
    -- _finalAssembly sub-helper (since it requires C_T from
    -- flow_distance_growth_bound_on, plus the integral_map +
    -- pushforward-moment-bound chain — exactly the threading work that
    -- the _finalAssembly sub-helper handles).
    intro t ht
    exact vlasovWellPosedness_local_moment W gradW hgradW L hL
      f₀ hf₀_int hT hTL_PL hTL_con charX charV
      _M_ρ _hM_ρ_nn _hflow_on _h_boundary _hM_ρ_bound _h_y_int_ρ _hconv_cont
      _h_aemeas _h_int_conv
      t ht
  · -- (b′) FLAT uniform first-moment bound on the spatial marginal.
    -- The picard fixed-point flow already exposes exactly this bound
    -- (`_hM_ρ_bound`) for `M_ρ := _M_ρ` against
    -- `spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ ·)`,
    -- which is `spatialMarginal (f ·)` by definition of `f` here.
    exact ⟨_M_ρ, _hM_ρ_nn, _hM_ρ_bound⟩
  · -- (c) IsLagrangianVlasovSolutionOn gradW f T.  Handled by the
    -- _finalAssembly sub-helper: it derives the AEMeasurable witness, the
    -- IsCharacteristicFlowSelfConsistent discharge, the universal-in-s
    -- convolution integrability (extension of `_hconv_cont`'s implications),
    -- and threads all the hypotheses through
    -- `vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn`.
    exact vlasovWellPosedness_local_isLagrangian W gradW hgradW L hL
      f₀ hf₀_int hT hTL_PL hTL_con charX charV
      _M_ρ _hM_ρ_nn _hflow_on _h_boundary _hM_ρ_bound _h_y_int_ρ _hconv_cont
      _h_aemeas _h_int_conv
  · -- (d) Explicit pushforward equation for the outer charX charV.
    -- vlasovSolutionViaPushforward charX charV f₀ t = Measure.map (charX t, charV t) f₀
    -- by DEFINITION. And f 0 = f₀ (from goal (a), which used the initial condition).
    -- So f t = Measure.map (charX t, charV t) (f 0) by congruence on f 0 = f₀.
    have h_f0_eq : vlasovSolutionViaPushforward charX charV f₀ 0 = f₀ := by
      have h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z :=
        fun z => Prod.ext (_hflow_on.1 z (Set.mem_univ z)).1 (_hflow_on.1 z (Set.mem_univ z)).2
      simp [vlasovSolutionViaPushforward,
            show (fun z : PhaseSpace d => (charX 0 z, charV 0 z)) = id from funext h_init]
    intro t _
    show vlasovSolutionViaPushforward charX charV f₀ t =
      Measure.map (fun z : PhaseSpace d => (charX t z, charV t z))
        (vlasovSolutionViaPushforward charX charV f₀ 0)
    rw [h_f0_eq]
    -- After rw, goal is: vlasovSolutionViaPushforward charX charV f₀ t = Measure.map ... f₀
    -- This is rfl by definition of vlasovSolutionViaPushforward.
    rfl
  · -- (e) Explicit AEMeasurable for the outer charX charV.
    -- AEMeasurable (fun z => (charX s z, charV s z)) f₀ comes from _h_aemeas.
    -- The expected type uses (f 0) = vlasovSolutionViaPushforward charX charV f₀ 0 = f₀.
    have h_f0_eq : vlasovSolutionViaPushforward charX charV f₀ 0 = f₀ := by
      have h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z :=
        fun z => Prod.ext (_hflow_on.1 z (Set.mem_univ z)).1 (_hflow_on.1 z (Set.mem_univ z)).2
      simp [vlasovSolutionViaPushforward,
            show (fun z : PhaseSpace d => (charX 0 z, charV 0 z)) = id from funext h_init]
    intro s _
    rw [h_f0_eq]
    exact _h_aemeas s
  · -- (f) Boundary regularity bundle: HasDerivWithinAt on Icc 0 T for all z, t.
    -- Directly from `_h_boundary` (the picard fixed-point flow's boundary output).
    -- The measure in the velocity derivative uses spatialMarginal (f t) where
    -- f = vlasovSolutionViaPushforward charX charV f₀, which is the same as
    -- what _h_boundary was built against.
    exact _h_boundary
  · -- (g) Initial condition for the outer charX charV witnesses.
    -- From _hflow_on.1 (IsCharacteristicFlowOn's first conjunct).
    intro z
    exact _hflow_on.1 z (Set.mem_univ z)

/-! ## Banked infrastructure: localized `hasDerivAt_of_hasDerivAt_of_ne` -/
-- Generic real-analysis helper banked for `vlasovWellPosedness_glue` case (a)'s substantive
-- close.  Mathlib's `hasDerivAt_of_hasDerivAt_of_ne`
-- (Mathlib/Analysis/Calculus/FDeriv/Extend.lean) requires a UNIVERSAL
-- `∀ y ≠ x, HasDerivAt f (g y) y` hypothesis; the `vlasovWellPosedness_glue` setting only
-- gives HasDerivAt on a bounded interval `Ioo 0 (T + T_0)`.  This helper
-- localizes the Mathlib pattern to a neighborhood-eventually hypothesis,
-- enabling case (a)'s close via union of one-sided extension lemmas.

section HasDerivAtPunctured
open scoped Topology
open Filter

/-- Local version of `hasDerivAt_of_hasDerivAt_of_ne` (Mathlib/Analysis/Calculus/
FDeriv/Extend.lean): if `f : ℝ → ℝ` has HasDerivAt with derivative `g(y)` at
every `y ≠ x₀` in some neighborhood of `x₀`, and both `f` and `g` are continuous
at `x₀`, then `f` has HasDerivAt with derivative `g(x₀)` at `x₀`.

The proof composes `hasDerivWithinAt_Iic_of_tendsto_deriv` (left side) +
`hasDerivWithinAt_Ici_of_tendsto_deriv` (right side) + `HasDerivWithinAt.union`,
following the Mathlib lemma's proof structure but with locally-quantified
hypothesis (enabling use when the punctured-HasDerivAt holds only on a bounded
interval, not all of ℝ). -/
theorem hasDerivAt_of_hasDerivAt_of_ne_in_nhds
    {f g : ℝ → ℝ} {x₀ : ℝ}
    (h_diff_ne : ∀ᶠ y in 𝓝 x₀, y ≠ x₀ → HasDerivAt f (g y) y)
    (hf : ContinuousAt f x₀) (hg : ContinuousAt g x₀) :
    HasDerivAt f (g x₀) x₀ := by
  -- Extract an open ball around x₀ on which the punctured HasDerivAt holds.
  obtain ⟨U, hU_sub, hU_open, hx₀_U⟩ := mem_nhds_iff.mp h_diff_ne
  obtain ⟨ε, ε_pos, hε⟩ := Metric.isOpen_iff.mp hU_open x₀ hx₀_U
  -- Right side: HasDerivWithinAt on Ici x₀ via hasDerivWithinAt_Ici_of_tendsto_deriv.
  have h_right : HasDerivWithinAt f (g x₀) (Set.Ici x₀) x₀ := by
    have hs_right : Set.Ioo x₀ (x₀ + ε) ∈ 𝓝[>] x₀ :=
      Ioo_mem_nhdsGT (by linarith : x₀ < x₀ + ε)
    have h_diff_right : DifferentiableOn ℝ f (Set.Ioo x₀ (x₀ + ε)) := by
      intro y hy
      have hy_U : y ∈ U := hε (by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        exact ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩)
      exact (hU_sub hy_U (ne_of_gt hy.1)).differentiableAt.differentiableWithinAt
    apply hasDerivWithinAt_Ici_of_tendsto_deriv h_diff_right hf.continuousWithinAt hs_right
    have h_g_tendsto : Tendsto g (𝓝[>] x₀) (𝓝 (g x₀)) := tendsto_inf_left hg
    apply h_g_tendsto.congr'
    apply mem_of_superset hs_right
    intro y hy
    have hy_U : y ∈ U := hε (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩)
    exact (hU_sub hy_U (ne_of_gt hy.1)).deriv.symm
  -- Left side: symmetric.
  have h_left : HasDerivWithinAt f (g x₀) (Set.Iic x₀) x₀ := by
    have hs_left : Set.Ioo (x₀ - ε) x₀ ∈ 𝓝[<] x₀ :=
      Ioo_mem_nhdsLT (by linarith : x₀ - ε < x₀)
    have h_diff_left : DifferentiableOn ℝ f (Set.Ioo (x₀ - ε) x₀) := by
      intro y hy
      have hy_U : y ∈ U := hε (by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        exact ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩)
      exact (hU_sub hy_U (ne_of_lt hy.2)).differentiableAt.differentiableWithinAt
    apply hasDerivWithinAt_Iic_of_tendsto_deriv h_diff_left hf.continuousWithinAt hs_left
    have h_g_tendsto : Tendsto g (𝓝[<] x₀) (𝓝 (g x₀)) := tendsto_inf_left hg
    apply h_g_tendsto.congr'
    apply mem_of_superset hs_left
    intro y hy
    have hy_U : y ∈ U := hε (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩)
    exact (hU_sub hy_U (ne_of_lt hy.2)).deriv.symm
  -- Union via Set.Iic_union_Ici = Set.univ → HasDerivAt at x₀.
  simpa using h_left.union h_right

end HasDerivAtPunctured

/-! ## Variable-`T_target` continuation via fixed-`T_0` iteration -/
-- Composes `vlasovWellPosedness_local` against itself to extend the local
-- solution from `[0, T_0]` to `[0, T_target]` for any `T_target > 0`.  The
-- contraction time `T_0` is *fixed* (depends only on `L`, not on iteration-
-- accumulated moment bounds) — see the docstring on `vlasovWellPosedness_local`
-- (above) for why fixed-`T_0` is the correct iteration shape (the
-- `Phi_supW1_contraction` factor `q` depends only on `L` and `T`).
--
-- Two sub-theorems:
-- * `vlasovWellPosedness_glue`: extend a solution on `[0, T]` by one
--   window of length `T_0`, gluing at `t = T`.
-- * `vlasovWellPosedness_forward`: `Nat.rec` iteration of `vlasovWellPosedness_glue`
--   to reach any `T_target`.
--
-- The universal-in-`t` bridge (below) then goes from
-- `IsLagrangianVlasovSolutionOn` (any `T_target`) to
-- `IsLagrangianVlasovSolution` (universal-in-`t`), and uniqueness follows.

/-- The `t = T` seam of the glue: both one-sided derivatives of the spliced
flow at the junction agree (`g`'s flow starts at the identity on
`f_prev T`'s data), so `HasDerivWithinAt.union` on `Iic T ∪ Ici T = univ`
gives the two-sided derivative, restricted back to `Icc 0 (T + T_0)`. -/
private lemma vlasovWellPosedness_glue_boundary_seam {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    {T T_0 : ℝ} (hT_pos : 0 < T) (hT_0_pos : 0 < T_0)
    (f_prev g f_next : ℝ → Measure (PhaseSpace d))
    (charX_prev charV_prev charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    (hdef_f : f_next = fun t => if t ≤ T then f_prev t else g (t - T))
    (h_prev_boundary : ∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
        HasDerivWithinAt (fun s => charX_prev s z) (charV_prev t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV_prev s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (f_prev t)) (charX_prev t z)))
          (Set.Icc 0 T) t)
    (hg_boundary : ∀ (w : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T_0 →
        HasDerivWithinAt (fun s => charX_g s w) (charV_g t w) (Set.Icc 0 T_0) t ∧
        HasDerivWithinAt (fun s => charV_g s w)
          (-(convolveFunctionMeasure gradW (spatialMarginal (g t)) (charX_g t w)))
          (Set.Icc 0 T_0) t)
    (hg_init : g 0 = f_prev T)
    (hg_init_cond : ∀ (w : PhaseSpace d), charX_g 0 w = w.1 ∧ charV_g 0 w = w.2)
    (z : PhaseSpace d) :
    HasDerivWithinAt
      (fun s => if s ≤ T then charX_prev s z
        else charX_g (s - T) (charX_prev T z, charV_prev T z))
      (charV_prev T z) (Set.Icc 0 (T + T_0)) T ∧
    HasDerivWithinAt
      (fun s => if s ≤ T then charV_prev s z
        else charV_g (s - T) (charX_prev T z, charV_prev T z))
      (-(convolveFunctionMeasure gradW (spatialMarginal (f_next T)) (charX_prev T z)))
      (Set.Icc 0 (T + T_0)) T := by
  have hT_in : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
  have h_bX := (h_prev_boundary z T hT_in).1
  have h_bV := (h_prev_boundary z T hT_in).2
  have h0_T0_in : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T_0 := ⟨le_refl 0, hT_0_pos.le⟩
  have h_g_bX := (hg_boundary (charX_prev T z, charV_prev T z) 0 h0_T0_in).1
  have h_g_bV := (hg_boundary (charX_prev T z, charV_prev T z) 0 h0_T0_in).2
  have h_nhd_L : Set.Icc 0 T ∈ nhdsWithin T (Set.Iic T) := Icc_mem_nhdsLE hT_pos
  have h_nhd_R : Set.Icc 0 T_0 ∈ nhdsWithin (0 : ℝ) (Set.Ici 0) := Icc_mem_nhdsGE hT_0_pos
  -- charX: left one-sided
  have hX_Lic := h_bX.mono_of_mem_nhdsWithin h_nhd_L
  have hX_left : HasDerivWithinAt
      (fun s => if s ≤ T then charX_prev s z
        else charX_g (s - T) (charX_prev T z, charV_prev T z))
      (charV_prev T z) (Set.Iic T) T :=
    hX_Lic.congr_of_mem (fun s hs => by simp [Set.mem_Iic.mp hs]) Set.self_mem_Iic
  -- charX: right one-sided via chain rule on g's boundary
  have hX_Ici0 := h_g_bX.mono_of_mem_nhdsWithin h_nhd_R
  have h_sub_R : HasDerivWithinAt (· - T) 1 (Set.Ici T) T :=
    ((hasDerivAt_id' T).sub_const T).hasDerivWithinAt
  have h_mapR : Set.MapsTo (· - T) (Set.Ici T) (Set.Ici 0) :=
    fun s hs => Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp hs])
  have h_chainX : HasDerivWithinAt
      (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z))
      (charV_g 0 (charX_prev T z, charV_prev T z)) (Set.Ici T) T := by
    have := HasDerivWithinAt.scomp_of_eq T hX_Ici0 h_sub_R h_mapR (sub_self T).symm
    simpa [Function.comp_def, one_smul] using this
  have hVg0_eq : charV_g 0 (charX_prev T z, charV_prev T z) = charV_prev T z :=
    (hg_init_cond (charX_prev T z, charV_prev T z)).2
  rw [hVg0_eq] at h_chainX
  have hX_right : HasDerivWithinAt
      (fun s => if s ≤ T then charX_prev s z
        else charX_g (s - T) (charX_prev T z, charV_prev T z))
      (charV_prev T z) (Set.Ici T) T :=
    h_chainX.congr_of_mem
      (fun s hs => by
        by_cases hle : s ≤ T
        · have heq : s = T := le_antisymm hle (Set.mem_Ici.mp hs)
          simp [heq, sub_self,
            (hg_init_cond (charX_prev T z, charV_prev T z)).1]
        · simp [hle])
      Set.self_mem_Ici
  have hX_union := hX_left.union hX_right
  rw [Set.Iic_union_Ici] at hX_union
  -- charV: analogously
  have hV_Lic := h_bV.mono_of_mem_nhdsWithin h_nhd_L
  have hV_left : HasDerivWithinAt
      (fun s => if s ≤ T then charV_prev s z
        else charV_g (s - T) (charX_prev T z, charV_prev T z))
      (-(convolveFunctionMeasure gradW (spatialMarginal (f_next T)) (charX_prev T z)))
      (Set.Iic T) T := by
    simp only [hdef_f, ite_eq_left (le_refl T)]
    exact hV_Lic.congr_of_mem (fun s hs => by simp [Set.mem_Iic.mp hs]) Set.self_mem_Iic
  have hV_Ici0 := h_g_bV.mono_of_mem_nhdsWithin h_nhd_R
  have h_chainV : HasDerivWithinAt
      (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z))
      (-(convolveFunctionMeasure gradW
        (spatialMarginal (g 0))
        (charX_g 0 (charX_prev T z, charV_prev T z))))
      (Set.Ici T) T := by
    have := HasDerivWithinAt.scomp_of_eq T hV_Ici0 h_sub_R h_mapR (sub_self T).symm
    simpa [Function.comp_def, one_smul] using this
  have hXg0_eq : charX_g 0 (charX_prev T z, charV_prev T z) = charX_prev T z :=
    (hg_init_cond (charX_prev T z, charV_prev T z)).1
  have hg0_spat : spatialMarginal (g 0) = spatialMarginal (f_prev T) :=
    congrArg spatialMarginal hg_init
  have hfnextT : spatialMarginal (f_next T) = spatialMarginal (f_prev T) :=
    congrArg spatialMarginal (by rw [hdef_f]; simp only [ite_eq_left (le_refl T)])
  rw [hXg0_eq, hg0_spat, ← hfnextT] at h_chainV
  have hV_right : HasDerivWithinAt
      (fun s => if s ≤ T then charV_prev s z
        else charV_g (s - T) (charX_prev T z, charV_prev T z))
      (-(convolveFunctionMeasure gradW (spatialMarginal (f_next T)) (charX_prev T z)))
      (Set.Ici T) T :=
    h_chainV.congr_of_mem
      (fun s hs => by
        by_cases hle : s ≤ T
        · have heq : s = T := le_antisymm hle (Set.mem_Ici.mp hs)
          simp [heq, sub_self,
            (hg_init_cond (charX_prev T z, charV_prev T z)).2]
        · simp [hle])
      Set.self_mem_Ici
  have hV_union := hV_left.union hV_right
  rw [Set.Iic_union_Ici] at hV_union
  exact ⟨hX_union.hasDerivAt Filter.univ_mem |>.hasDerivWithinAt,
    hV_union.hasDerivAt Filter.univ_mem |>.hasDerivWithinAt⟩

private lemma vlasovWellPosedness_glue_boundary {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    {T T_0 : ℝ} (hT_pos : 0 < T) (hT_0_pos : 0 < T_0)
    (f_prev g f_next : ℝ → Measure (PhaseSpace d))
    (charX_prev charV_prev charX_g charV_g charX_next charV_next :
        ℝ → PhaseSpace d → PhysSpace d)
    (hdef_X : charX_next = fun t z =>
        if t ≤ T then charX_prev t z else charX_g (t - T) (charX_prev T z, charV_prev T z))
    (hdef_V : charV_next = fun t z =>
        if t ≤ T then charV_prev t z else charV_g (t - T) (charX_prev T z, charV_prev T z))
    (hdef_f : f_next = fun t => if t ≤ T then f_prev t else g (t - T))
    (h_prev_boundary : ∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
        HasDerivWithinAt (fun s => charX_prev s z) (charV_prev t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV_prev s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (f_prev t)) (charX_prev t z)))
          (Set.Icc 0 T) t)
    (hg_boundary : ∀ (w : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T_0 →
        HasDerivWithinAt (fun s => charX_g s w) (charV_g t w) (Set.Icc 0 T_0) t ∧
        HasDerivWithinAt (fun s => charV_g s w)
          (-(convolveFunctionMeasure gradW (spatialMarginal (g t)) (charX_g t w)))
          (Set.Icc 0 T_0) t)
    (hg_init : g 0 = f_prev T)
    (hg_init_cond : ∀ (w : PhaseSpace d), charX_g 0 w = w.1 ∧ charV_g 0 w = w.2) :
    ∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) (T + T_0) →
      HasDerivWithinAt (fun s => charX_next s z) (charV_next t z) (Set.Icc 0 (T + T_0)) t ∧
      HasDerivWithinAt (fun s => charV_next s z)
        (-(convolveFunctionMeasure gradW (spatialMarginal (f_next t)) (charX_next t z)))
        (Set.Icc 0 (T + T_0)) t := by
  subst hdef_X hdef_V
  intro z t ht
  simp only []
  -- Abbreviate the initial phase-space point for g
  have hz₀_def : (charX_prev T z, charV_prev T z) = (charX_prev T z, charV_prev T z) := rfl
  by_cases ht_le : t ≤ T
  · -- t ≤ T: use h_prev_boundary + upgrade to Icc 0 (T + T_0)
    simp only [ite_eq_left ht_le]
    have ht_in : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1, ht_le⟩
    have h_bX := (h_prev_boundary z t ht_in).1
    have h_bV := (h_prev_boundary z t ht_in).2
    by_cases ht_eqT : t = T
    · -- t = T: the seam case, extracted as `_glue_boundary_seam`.
      rw [ht_eqT]
      exact vlasovWellPosedness_glue_boundary_seam gradW hT_pos hT_0_pos f_prev g f_next
        charX_prev charV_prev charX_g charV_g hdef_f h_prev_boundary hg_boundary
        hg_init hg_init_cond z
    · -- t < T: use mono_of_mem_nhdsWithin to extend to Icc 0 (T + T_0)
      have ht_ltT : t < T := lt_of_le_of_ne ht_le ht_eqT
      -- Get Icc 0 T ∈ nhdsWithin t (Icc 0 (T + T_0))
      have h_mem : Set.Icc (0 : ℝ) T ∈ nhdsWithin t (Set.Icc 0 (T + T_0)) := by
        rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
        · exact (nhdsWithin_mono 0 Set.Icc_subset_Ici_self) (Icc_mem_nhdsGE hT_pos)
        · exact mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds ht_pos ht_ltT)
      -- Upgrade HasDerivWithinAt from Icc 0 T to Icc 0 (T + T_0)
      have hX_big := h_bX.mono_of_mem_nhdsWithin h_mem
      have hV_big := h_bV.mono_of_mem_nhdsWithin h_mem
      -- Congr: charX_next = charX_prev on Icc 0 T (within Icc 0 (T+T_0))
      have hX_ev : (fun s => if s ≤ T then charX_prev s z
            else charX_g (s - T) (charX_prev T z, charV_prev T z))
          =ᶠ[nhdsWithin t (Set.Icc 0 (T + T_0))] (charX_prev · z) :=
        Filter.Eventually.mono h_mem (fun s hs => by simp [hs.2])
      have hV_ev : (fun s => if s ≤ T then charV_prev s z
            else charV_g (s - T) (charX_prev T z, charV_prev T z))
          =ᶠ[nhdsWithin t (Set.Icc 0 (T + T_0))] (charV_prev · z) :=
        Filter.Eventually.mono h_mem (fun s hs => by simp [hs.2])
      -- f_next t = f_prev t, so marginals match
      have hfnext : f_next t = f_prev t := by rw [hdef_f]; simp only [ite_eq_left ht_le]
      have hfnext_spat : spatialMarginal (f_next t) = spatialMarginal (f_prev t) :=
        congrArg spatialMarginal hfnext
      rw [← hfnext_spat] at hV_big
      constructor
      · exact hX_big.congr_of_eventuallyEq_of_mem hX_ev ht
      · exact hV_big.congr_of_eventuallyEq_of_mem hV_ev ht
  · -- T < t: use hg_boundary + chain rule
    push Not at ht_le
    simp only [ite_eq_right (not_le.mpr ht_le)]
    have htT_mem : t - T ∈ Set.Icc (0 : ℝ) T_0 := ⟨by linarith, by linarith [ht.2]⟩
    have h_bdry_gX := (hg_boundary (charX_prev T z, charV_prev T z) (t - T) htT_mem).1
    have h_bdry_gV := (hg_boundary (charX_prev T z, charV_prev T z) (t - T) htT_mem).2
    by_cases ht_ltTT0 : t < T + T_0
    · -- t ∈ Ioo T (T + T_0): interior case, use HasDerivAt + congr
      have htT_Ioo : t - T ∈ Set.Ioo (0 : ℝ) T_0 := ⟨by linarith, by linarith⟩
      have hX_da := h_bdry_gX.hasDerivAt (Icc_mem_nhds htT_Ioo.1 htT_Ioo.2)
      have hV_da := h_bdry_gV.hasDerivAt (Icc_mem_nhds htT_Ioo.1 htT_Ioo.2)
      have h_sub : HasDerivAt (· - T) 1 t := (hasDerivAt_id' t).sub_const T
      have h_chainX : HasDerivAt (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z))
          (charV_g (t - T) (charX_prev T z, charV_prev T z)) t := by
        have := HasDerivAt.scomp_of_eq t hX_da h_sub rfl
        simpa [Function.comp_def, one_smul] using this
      have h_chainV : HasDerivAt (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z))
          (-(convolveFunctionMeasure gradW
            (spatialMarginal (g (t - T)))
            (charX_g (t - T) (charX_prev T z, charV_prev T z)))) t := by
        have := HasDerivAt.scomp_of_eq t hV_da h_sub rfl
        simpa [Function.comp_def, one_smul] using this
      -- f_next t = g (t - T), so marginals match
      have h_fnext_t : f_next t = g (t - T) := by
        rw [hdef_f]; simp only [ite_eq_right (not_le.mpr ht_le)]
      rw [← congrArg spatialMarginal h_fnext_t] at h_chainV
      -- piecewise = charX_g (· - T) (charX_prev T z, charV_prev T z) near t (since T < t)
      have h_ev_gt : ∀ᶠ s in nhds t, T < s := eventually_gt_nhds ht_le
      have hX_ev : (fun s => if s ≤ T then charX_prev s z
            else charX_g (s - T) (charX_prev T z, charV_prev T z))
          =ᶠ[nhds t] (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z)) :=
        Filter.Eventually.mono h_ev_gt (fun s hs => by simp [not_le.mpr hs])
      have hV_ev : (fun s => if s ≤ T then charV_prev s z
            else charV_g (s - T) (charX_prev T z, charV_prev T z))
          =ᶠ[nhds t] (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z)) :=
        Filter.Eventually.mono h_ev_gt (fun s hs => by simp [not_le.mpr hs])
      exact ⟨(h_chainX.congr_of_eventuallyEq hX_ev).hasDerivWithinAt,
             (h_chainV.congr_of_eventuallyEq hV_ev).hasDerivWithinAt⟩
    · -- t = T + T_0: endpoint, use mono_of_mem_nhdsWithin + chain rule + mono
      push Not at ht_ltTT0
      have htT0 : t = T + T_0 := le_antisymm ht.2 ht_ltTT0
      rw [show t - T = T_0 from by linarith] at h_bdry_gX h_bdry_gV
      -- Upgrade to Iic T_0 via Icc_mem_nhdsLE
      have h_nhd_LE : Set.Icc 0 T_0 ∈ nhdsWithin T_0 (Set.Iic T_0) := Icc_mem_nhdsLE hT_0_pos
      have hX_Lic := h_bdry_gX.mono_of_mem_nhdsWithin h_nhd_LE
      have hV_Lic := h_bdry_gV.mono_of_mem_nhdsWithin h_nhd_LE
      -- Chain rule: (· - T) maps Iic (T + T_0) to Iic T_0
      have h_sub_LE : HasDerivWithinAt (· - T) 1 (Set.Iic (T + T_0)) (T + T_0) :=
        ((hasDerivAt_id' (T + T_0)).sub_const T).hasDerivWithinAt.mono
          (fun _ _ => Set.mem_univ _)
      have h_mapLE : Set.MapsTo (· - T) (Set.Iic (T + T_0)) (Set.Iic T_0) :=
        fun s hs => Set.mem_Iic.mpr (by linarith [Set.mem_Iic.mp hs])
      have h_chainX : HasDerivWithinAt
          (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z))
          (charV_g T_0 (charX_prev T z, charV_prev T z)) (Set.Iic (T + T_0)) (T + T_0) := by
        have := HasDerivWithinAt.scomp_of_eq (T + T_0) hX_Lic h_sub_LE h_mapLE
          (show T_0 = (T + T_0) - T by ring)
        simpa [Function.comp_def, one_smul] using this
      have h_chainV : HasDerivWithinAt
          (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z))
          (-(convolveFunctionMeasure gradW
            (spatialMarginal (g T_0))
            (charX_g T_0 (charX_prev T z, charV_prev T z))))
          (Set.Iic (T + T_0)) (T + T_0) := by
        have := HasDerivWithinAt.scomp_of_eq (T + T_0) hV_Lic h_sub_LE h_mapLE
          (show T_0 = (T + T_0) - T by ring)
        simpa [Function.comp_def, one_smul] using this
      -- Congr: near T+T_0 within Iic (T+T_0), points > T eventually
      have h_ev_gt2 : ∀ᶠ s in nhdsWithin (T + T_0) (Set.Iic (T + T_0)), T < s :=
        (eventually_gt_nhds (show T < T + T_0 by linarith)).filter_mono nhdsWithin_le_nhds
      have hX_ev2 : (fun s => if s ≤ T then charX_prev s z
            else charX_g (s - T) (charX_prev T z, charV_prev T z))
          =ᶠ[nhdsWithin (T + T_0) (Set.Iic (T + T_0))]
          (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z)) :=
        Filter.Eventually.mono h_ev_gt2 (fun s hs => by simp [not_le.mpr hs])
      have hV_ev2 : (fun s => if s ≤ T then charV_prev s z
            else charV_g (s - T) (charX_prev T z, charV_prev T z))
          =ᶠ[nhdsWithin (T + T_0) (Set.Iic (T + T_0))]
          (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z)) :=
        Filter.Eventually.mono h_ev_gt2 (fun s hs => by simp [not_le.mpr hs])
      have h_Iic_sub : Set.Icc 0 (T + T_0) ⊆ Set.Iic (T + T_0) := Set.Icc_subset_Iic_self
      have h_TT0_Iic : (T + T_0) ∈ Set.Iic (T + T_0) := Set.mem_Iic.mpr (le_refl _)
      -- f_next (T + T_0) = g T_0
      have h_fnext_TT0 : f_next (T + T_0) = g T_0 := by
        simp [hdef_f, not_le.mpr (show T < T + T_0 by linarith)]
      constructor
      · have h_cX : HasDerivWithinAt
            (fun s => if s ≤ T then charX_prev s z
              else charX_g (s - T) (charX_prev T z, charV_prev T z))
            (charV_g T_0 (charX_prev T z, charV_prev T z))
            (Set.Icc 0 (T + T_0)) (T + T_0) :=
          (h_chainX.congr_of_eventuallyEq_of_mem hX_ev2 h_TT0_Iic).mono h_Iic_sub
        rw [htT0]
        rw [show T + T_0 - T = T_0 from by ring]
        exact h_cX
      · have h_cV : HasDerivWithinAt
            (fun s => if s ≤ T then charV_prev s z
              else charV_g (s - T) (charX_prev T z, charV_prev T z))
            (-(convolveFunctionMeasure gradW
              (spatialMarginal (g T_0))
              (charX_g T_0 (charX_prev T z, charV_prev T z))))
            (Set.Icc 0 (T + T_0)) (T + T_0) :=
          (h_chainV.congr_of_eventuallyEq_of_mem hV_ev2 h_TT0_Iic).mono h_Iic_sub
        rw [htT0]
        rw [h_fnext_TT0]
        rw [show T + T_0 - T = T_0 from by ring]
        exact h_cV


/-- **Route 2 inner kernel for `glue_step` `h_cont_g`** (LEFT / `Iic T`): continuity
at the seam `T` of `s ↦ (∇W ∗ μ_s)(charX s z)`, where the window measure curve `μ` is
the flow-pushforward of `f₀`.

Proven from PROVEN tools only (no deferred OT).  The pushforward rewrite
`(∇W ∗ μ_s)(x) = ∫ z', gradW (x − charX s z') ∂f₀` (`integral_map`) turns the
moving-measure convolution into a fixed-`f₀` integral with moving integrand, closed by
dominated convergence: convergence from the flow's seam continuity `h_charX_cont`,
domination from the Gronwall growth bound `hC_T` (Piece A) against `f₀`'s finite first
moment.  This is the structural reason `h_cont_g` does NOT need the general narrow→W₁
kernel — its consumer carries a pushforward representation. -/
lemma flowConv_continuousWithinAt_Iic_seam
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (μ : ℝ → Measure (PhysSpace d))
    (h_push : ∀ s ∈ Set.Icc (0 : ℝ) T,
        μ s = Measure.map (fun z : PhaseSpace d => charX s z) f₀)
    (h_aemeas : ∀ s ∈ Set.Icc (0 : ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => charX s z) f₀)
    (h_charX_cont : ∀ z : PhaseSpace d,
        ContinuousWithinAt (fun s => charX s z) (Set.Icc (0 : ℝ) T) T)
    (C_T : ℝ) (_hC_T_nn : 0 ≤ C_T)
    (hC_T : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d, ‖charX s z‖ ≤ C_T * (‖z‖ + 1))
    (z : PhaseSpace d) :
    ContinuousWithinAt (fun s => convolveFunctionMeasure gradW (μ s) (charX s z))
      (Set.Iic T) T := by
  have h_nhd_L : Set.Icc (0 : ℝ) T ∈ nhdsWithin T (Set.Iic T) := Icc_mem_nhdsLE hT
  have hgradW_cont : Continuous gradW := hL.continuous
  have hL_nn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  -- Pushforward rewrite of the convolution, eventually in s (on the window).
  have h_eq : (fun s => convolveFunctionMeasure gradW (μ s) (charX s z))
      =ᶠ[nhdsWithin T (Set.Iic T)]
      (fun s => ∫ z', gradW (charX s z - charX s z') ∂f₀) := by
    apply Filter.Eventually.mono h_nhd_L
    intro s hs
    change ∫ y, gradW (charX s z - y) ∂(μ s)
        = ∫ z', gradW (charX s z - charX s z') ∂f₀
    rw [h_push s hs]
    exact integral_map (h_aemeas s hs)
      (hgradW_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  -- The rewritten f₀-integral is continuous at T by dominated convergence.
  have h_cont_rhs : ContinuousWithinAt
      (fun s => ∫ z', gradW (charX s z - charX s z') ∂f₀) (Set.Iic T) T := by
    apply continuousWithinAt_of_dominated
      (bound := fun z' => ‖gradW 0‖ + (L : ℝ) * (C_T * (‖z‖ + 1))
        + (L : ℝ) * (C_T * (‖z'‖ + 1)))
    · -- AEStronglyMeasurable in z', eventually in s
      apply Filter.Eventually.mono h_nhd_L
      intro s hs
      exact (hgradW_cont.measurable.comp_aemeasurable
        (aemeasurable_const.sub (h_aemeas s hs))).aestronglyMeasurable
    · -- pointwise dominator bound, eventually in s
      apply Filter.Eventually.mono h_nhd_L
      intro s hs
      apply Filter.Eventually.of_forall
      intro z'
      have h1 : ‖gradW (charX s z - charX s z')‖
          ≤ ‖gradW 0‖ + (L : ℝ) * ‖charX s z - charX s z'‖ := by
        have hd := hL.dist_le_mul (charX s z - charX s z') 0
        simp only [dist_eq_norm, sub_zero] at hd
        have htri : ‖gradW (charX s z - charX s z')‖
            ≤ ‖gradW 0‖ + ‖gradW (charX s z - charX s z') - gradW 0‖ := by
          have := norm_add_le (gradW (charX s z - charX s z') - gradW 0) (gradW 0)
          simp only [sub_add_cancel] at this; linarith
        linarith
      have h2 : ‖charX s z - charX s z'‖ ≤ ‖charX s z‖ + ‖charX s z'‖ := norm_sub_le _ _
      have h3 : ‖charX s z‖ ≤ C_T * (‖z‖ + 1) := hC_T s hs z
      have h4 : ‖charX s z'‖ ≤ C_T * (‖z'‖ + 1) := hC_T s hs z'
      nlinarith [mul_le_mul_of_nonneg_left (h2.trans (add_le_add h3 h4)) hL_nn]
    · -- integrability of the dominator
      apply Integrable.add (integrable_const _)
      exact ((hf₀_int.add (integrable_const (1 : ℝ))).const_mul C_T).const_mul (L : ℝ)
    · -- pointwise continuity in s, a.e. z'
      apply Filter.Eventually.of_forall
      intro z'
      have hcz : ContinuousWithinAt (fun s => charX s z) (Set.Iic T) T :=
        (h_charX_cont z).mono_of_mem_nhdsWithin h_nhd_L
      have hcz' : ContinuousWithinAt (fun s => charX s z') (Set.Iic T) T :=
        (h_charX_cont z').mono_of_mem_nhdsWithin h_nhd_L
      exact hgradW_cont.continuousAt.comp_continuousWithinAt (hcz.sub hcz')
  -- Bridge value at T and conclude.
  have h_val_T : convolveFunctionMeasure gradW (μ T) (charX T z)
      = ∫ z', gradW (charX T z - charX T z') ∂f₀ := by
    have hT_mem : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_refl T⟩
    change ∫ y, gradW (charX T z - y) ∂(μ T)
        = ∫ z', gradW (charX T z - charX T z') ∂f₀
    rw [h_push T hT_mem]
    exact integral_map (h_aemeas T hT_mem)
      (hgradW_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact h_cont_rhs.congr_of_eventuallyEq h_eq h_val_T

/-- **Route 2 inner kernel for `glue_step` `h_cont_g`** (RIGHT / `Ici a`): the
exact mirror of `flowConv_continuousWithinAt_Iic_seam`, but on `Set.Ici a` over a
generic window `[a, b]` with the seam at the lower endpoint `a`.  Same proof shape;
the only set-dependent swaps are `Iic T → Ici a`, `Icc_mem_nhdsLE → Icc_mem_nhdsGE`,
and the window `[0, T] → [a, b]`.  Used for the RIGHT side of the seam at `T` where
`charX` is the composed position flow `Z_s z = charX_g (s-T) (charX_prev T z, …)` and
`μ s = spatialMarginal (g (s-T))` is its pushforward of `f₀`. -/
lemma flowConv_continuousWithinAt_Ici_seam
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {a b : ℝ} (hab : a < b)
    (μ : ℝ → Measure (PhysSpace d))
    (h_push : ∀ s ∈ Set.Icc a b,
        μ s = Measure.map (fun z : PhaseSpace d => charX s z) f₀)
    (h_aemeas : ∀ s ∈ Set.Icc a b,
        AEMeasurable (fun z : PhaseSpace d => charX s z) f₀)
    (h_charX_cont : ∀ z : PhaseSpace d,
        ContinuousWithinAt (fun s => charX s z) (Set.Ici a) a)
    (C_T : ℝ) (_hC_T_nn : 0 ≤ C_T)
    (hC_T : ∀ s ∈ Set.Icc a b, ∀ z : PhaseSpace d, ‖charX s z‖ ≤ C_T * (‖z‖ + 1))
    (z : PhaseSpace d) :
    ContinuousWithinAt (fun s => convolveFunctionMeasure gradW (μ s) (charX s z))
      (Set.Ici a) a := by
  have h_nhd_R : Set.Icc a b ∈ nhdsWithin a (Set.Ici a) := Icc_mem_nhdsGE hab
  have hgradW_cont : Continuous gradW := hL.continuous
  have hL_nn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  -- Pushforward rewrite of the convolution, eventually in s (on the window).
  have h_eq : (fun s => convolveFunctionMeasure gradW (μ s) (charX s z))
      =ᶠ[nhdsWithin a (Set.Ici a)]
      (fun s => ∫ z', gradW (charX s z - charX s z') ∂f₀) := by
    apply Filter.Eventually.mono h_nhd_R
    intro s hs
    change ∫ y, gradW (charX s z - y) ∂(μ s)
        = ∫ z', gradW (charX s z - charX s z') ∂f₀
    rw [h_push s hs]
    exact integral_map (h_aemeas s hs)
      (hgradW_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  -- The rewritten f₀-integral is continuous at a by dominated convergence.
  have h_cont_rhs : ContinuousWithinAt
      (fun s => ∫ z', gradW (charX s z - charX s z') ∂f₀) (Set.Ici a) a := by
    apply continuousWithinAt_of_dominated
      (bound := fun z' => ‖gradW 0‖ + (L : ℝ) * (C_T * (‖z‖ + 1))
        + (L : ℝ) * (C_T * (‖z'‖ + 1)))
    · -- AEStronglyMeasurable in z', eventually in s
      apply Filter.Eventually.mono h_nhd_R
      intro s hs
      exact (hgradW_cont.measurable.comp_aemeasurable
        (aemeasurable_const.sub (h_aemeas s hs))).aestronglyMeasurable
    · -- pointwise dominator bound, eventually in s
      apply Filter.Eventually.mono h_nhd_R
      intro s hs
      apply Filter.Eventually.of_forall
      intro z'
      have h1 : ‖gradW (charX s z - charX s z')‖
          ≤ ‖gradW 0‖ + (L : ℝ) * ‖charX s z - charX s z'‖ := by
        have hd := hL.dist_le_mul (charX s z - charX s z') 0
        simp only [dist_eq_norm, sub_zero] at hd
        have htri : ‖gradW (charX s z - charX s z')‖
            ≤ ‖gradW 0‖ + ‖gradW (charX s z - charX s z') - gradW 0‖ := by
          have := norm_add_le (gradW (charX s z - charX s z') - gradW 0) (gradW 0)
          simp only [sub_add_cancel] at this; linarith
        linarith
      have h2 : ‖charX s z - charX s z'‖ ≤ ‖charX s z‖ + ‖charX s z'‖ := norm_sub_le _ _
      have h3 : ‖charX s z‖ ≤ C_T * (‖z‖ + 1) := hC_T s hs z
      have h4 : ‖charX s z'‖ ≤ C_T * (‖z'‖ + 1) := hC_T s hs z'
      nlinarith [mul_le_mul_of_nonneg_left (h2.trans (add_le_add h3 h4)) hL_nn]
    · -- integrability of the dominator
      apply Integrable.add (integrable_const _)
      exact ((hf₀_int.add (integrable_const (1 : ℝ))).const_mul C_T).const_mul (L : ℝ)
    · -- pointwise continuity in s, a.e. z'
      apply Filter.Eventually.of_forall
      intro z'
      have hcz : ContinuousWithinAt (fun s => charX s z) (Set.Ici a) a := h_charX_cont z
      have hcz' : ContinuousWithinAt (fun s => charX s z') (Set.Ici a) a := h_charX_cont z'
      exact hgradW_cont.continuousAt.comp_continuousWithinAt (hcz.sub hcz')
  -- Bridge value at a and conclude.
  have h_val_a : convolveFunctionMeasure gradW (μ a) (charX a z)
      = ∫ z', gradW (charX a z - charX a z') ∂f₀ := by
    have ha_mem : a ∈ Set.Icc a b := ⟨le_refl a, hab.le⟩
    change ∫ y, gradW (charX a z - y) ∂(μ a)
        = ∫ z', gradW (charX a z - charX a z') ∂f₀
    rw [h_push a ha_mem]
    exact integral_map (h_aemeas a ha_mem)
      (hgradW_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact h_cont_rhs.congr_of_eventuallyEq h_eq h_val_a

/-- gradW-kernel integrability on the spatial marginals of a finite-first-moment
curve (window-generic over the curve `μ`).  The first-moment transfer to the
marginal feeds `integrable_gradW_shift`. -/
private lemma dobrushinFlow_marginal_gradW_integrable
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (T : ℝ) (μ : ℝ → Measure (PhaseSpace d))
    (hμ_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (μ t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (spatialMarginal (μ t)) := by
  intro t ht x_pt
  have : IsProbabilityMeasure (μ t) := (hμ_mom t ht).1
  have : IsProbabilityMeasure (spatialMarginal (μ t)) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have h_y_int : Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal (μ t)) := by
    unfold spatialMarginal
    rw [integrable_map_measure
      (by exact (continuous_norm.measurable).aestronglyMeasurable)
      measurable_fst.aemeasurable]
    refine Integrable.mono' (hμ_mom t ht).2
      ((continuous_norm.comp continuous_fst).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => ?_)
    change |‖z.1‖| ≤ ‖z‖
    rw [abs_of_nonneg (norm_nonneg _)]; exact norm_fst_le z
  exact integrable_gradW_shift gradW L hL (spatialMarginal (μ t)) h_y_int x_pt

/-- First-moment integrability transfers to the spatial marginal:
`∫ ‖z‖ ∂μ < ∞` gives `∫ ‖y‖ ∂(spatialMarginal μ) < ∞`. -/
private lemma vlasovGlue_marginal_norm_integrable
    {d : ℕ} [NeZero d]
    (μ : Measure (PhaseSpace d)) (hμ : HasFiniteFirstMoment μ) :
    Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal μ) := by
  have : IsProbabilityMeasure μ := hμ.1
  unfold spatialMarginal
  rw [integrable_map_measure
    (by exact (continuous_norm.measurable).aestronglyMeasurable)
    measurable_fst.aemeasurable]
  refine Integrable.mono' hμ.2
    ((continuous_norm.comp continuous_fst).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => ?_)
  change |‖z.1‖| ≤ ‖z‖
  rw [abs_of_nonneg (norm_nonneg _)]; exact norm_fst_le z

/-- Continuity of the spatial-gradient component `gradXφ` of a smooth test
function `φ` on phase space. -/
private lemma vlasovGlue_gradXφ_continuous
    {d : ℕ} [NeZero d]
    (φ : PhaseSpace d → ℝ) (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (gradXφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z : PhaseSpace d, gradXφ z = gradient (fun x => φ (x, z.2)) z.1) :
    Continuous gradXφ := by
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
  have heqX : gradXφ = fun z => gradient (fun x => φ (x, z.2)) z.1 :=
    funext hgradXφ
  rw [heqX]
  simp_rw [gradient, hfderiv_X]
  exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
    ((ContinuousLinearMap.isBoundedLinearMap_comp_right
      (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d))).continuous.comp
      (hφ_smooth.continuous_fderiv (by simp)))

/-- Continuity of the velocity-gradient component `gradVφ` of a smooth test
function `φ` on phase space. -/
private lemma vlasovGlue_gradVφ_continuous
    {d : ℕ} [NeZero d]
    (φ : PhaseSpace d → ℝ) (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (gradVφ : PhaseSpace d → PhysSpace d)
    (hgradVφ : ∀ z : PhaseSpace d, gradVφ z = gradient (fun v => φ (z.1, v)) z.2) :
    Continuous gradVφ := by
  have hfderiv_V : ∀ z : PhaseSpace d,
      fderiv ℝ (fun v => φ (z.1, v)) z.2 =
      (fderiv ℝ φ z).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) :=
    fun z => by
      have h1 : HasFDerivAt φ (fderiv ℝ φ z) z :=
        (hφ_smooth.differentiable (by simp) z).hasFDerivAt
      have h2 : HasFDerivAt (fun v : PhysSpace d => (z.1, v))
          (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) z.2 :=
        hasFDerivAt_prodMk_right z.1 z.2
      exact (h1.comp z.2 h2).fderiv
  have heqV : gradVφ = fun z => gradient (fun v => φ (z.1, v)) z.2 :=
    funext hgradVφ
  rw [heqV]
  simp_rw [gradient, hfderiv_V]
  exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
    ((ContinuousLinearMap.isBoundedLinearMap_comp_right
      (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d))).continuous.comp
      (hφ_smooth.continuous_fderiv (by simp)))

/-- Uniform sup-bound on both gradient components of a compactly supported
smooth test function: `‖∇_x φ‖, ‖∇_v φ‖ ≤ M_φ := sup ‖fderiv φ‖`. -/
private lemma vlasovGlue_gradφ_bound
    {d : ℕ} [NeZero d]
    (φ : PhaseSpace d → ℝ) (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z : PhaseSpace d, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z : PhaseSpace d, gradVφ z = gradient (fun v => φ (z.1, v)) z.2) :
    ∃ M_φ : ℝ, (∀ z : PhaseSpace d, ‖gradXφ z‖ ≤ M_φ) ∧
      (∀ z : PhaseSpace d, ‖gradVφ z‖ ≤ M_φ) := by
  have hfderiv_cont : Continuous (fderiv ℝ φ) :=
    hφ_smooth.continuous_fderiv (by norm_num)
  have hfderiv_compact : HasCompactSupport (fderiv ℝ φ) :=
    HasCompactSupport.fderiv (𝕜 := ℝ) hφ_compact
  obtain ⟨M_φ, hM_φ⟩ := hfderiv_cont.bounded_above_of_compact_support hfderiv_compact
  refine ⟨M_φ, fun z => ?_, fun z => ?_⟩
  · have hfd : fderiv ℝ (fun x => φ (x, z.2)) z.1 =
        (fderiv ℝ φ z).comp
          (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) := by
      have h1 : HasFDerivAt φ (fderiv ℝ φ z) z :=
        (hφ_smooth.differentiable (by simp) z).hasFDerivAt
      have h2 : HasFDerivAt (fun x : PhysSpace d => (x, z.2))
          (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) z.1 :=
        hasFDerivAt_prodMk_left z.1 z.2
      exact (h1.comp z.1 h2).fderiv
    rw [hgradXφ z, gradient, hfd,
      (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.norm_map]
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.norm_inl_le_one (𝕜 := ℝ)
        (E := PhysSpace d) (F := PhysSpace d)) (norm_nonneg _)) ?_
    rw [mul_one]; exact hM_φ z
  · have hfd : fderiv ℝ (fun v => φ (z.1, v)) z.2 =
        (fderiv ℝ φ z).comp
          (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) := by
      have h1 : HasFDerivAt φ (fderiv ℝ φ z) z :=
        (hφ_smooth.differentiable (by simp) z).hasFDerivAt
      have h2 : HasFDerivAt (fun v : PhysSpace d => (z.1, v))
          (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) z.2 :=
        hasFDerivAt_prodMk_right z.1 z.2
      exact (h1.comp z.2 h2).fderiv
    rw [hgradVφ z, gradient, hfd,
      (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.norm_map]
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.norm_inr_le_one (𝕜 := ℝ)
        (E := PhysSpace d) (F := PhysSpace d)) (norm_nonneg _)) ?_
    rw [mul_one]; exact hM_φ z

/-- Convolution force bound from a first-moment envelope:
`‖(gradW ⋆ ρ) x‖ ≤ ‖gradW 0‖ + L·‖x‖ + L·M` for a probability measure `ρ`
with `∫ ‖y‖ ∂ρ ≤ M`. -/
private lemma vlasovGlue_conv_force_bound
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : Measure (PhysSpace d)) [IsProbabilityMeasure ρ]
    (M : ℝ) (hM : ∫ y, ‖y‖ ∂ρ ≤ M)
    (h_y_int : Integrable (fun y : PhysSpace d => ‖y‖) ρ)
    (h_int : ∀ x : PhysSpace d, Integrable (fun y => gradW (x - y)) ρ)
    (x : PhysSpace d) :
    ‖convolveFunctionMeasure gradW ρ x‖
      ≤ ‖gradW 0‖ + (L : ℝ) * ‖x‖ + (L : ℝ) * M := by
  unfold convolveFunctionMeasure
  have h_sub_int : Integrable (fun y => ‖x - y‖) ρ :=
    Integrable.mono' ((integrable_const ‖x‖).add h_y_int)
      ((aestronglyMeasurable_const (b := x)).sub aestronglyMeasurable_id |>.norm)
      (Filter.Eventually.of_forall fun y => by
        simp only [Real.norm_of_nonneg (norm_nonneg _)]; exact norm_sub_le x y)
  have h_pt : ∀ y : PhysSpace d,
      ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + (L : ℝ) * ‖x - y‖ := by
    intro y
    have hd := hL.dist_le_mul (x - y) 0
    simp only [dist_eq_norm, sub_zero] at hd
    have h_tri : ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x - y) - gradW 0‖ := by
      have := norm_add_le (gradW (x - y) - gradW 0) (gradW 0)
      simp only [sub_add_cancel] at this; linarith
    linarith
  have h_bnd_int :
      Integrable (fun y => ‖gradW 0‖ + (L : ℝ) * ‖x - y‖) ρ :=
    (integrable_const _).add (h_sub_int.const_mul _)
  calc ‖∫ y, gradW (x - y) ∂ρ‖
      ≤ ∫ y, ‖gradW (x - y)‖ ∂ρ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y, (‖gradW 0‖ + (L : ℝ) * ‖x - y‖) ∂ρ :=
        integral_mono (h_int x).norm h_bnd_int h_pt
    _ = ‖gradW 0‖ + (L : ℝ) * ∫ y, ‖x - y‖ ∂ρ := by
        rw [integral_add (integrable_const _) (h_sub_int.const_mul _)]
        simp [integral_const, measureReal_def, measure_univ, integral_const_mul]
    _ ≤ ‖gradW 0‖ + (L : ℝ) * ‖x‖ + (L : ℝ) * M := by
        have h_int_le : ∫ y, ‖x - y‖ ∂ρ ≤ ‖x‖ + M := by
          calc ∫ y, ‖x - y‖ ∂ρ
              ≤ ∫ y, (‖x‖ + ‖y‖) ∂ρ :=
                integral_mono h_sub_int ((integrable_const _).add h_y_int)
                  (fun y => norm_sub_le x y)
            _ = ‖x‖ + ∫ y, ‖y‖ ∂ρ := by
                rw [integral_add (integrable_const _) h_y_int]
                simp [integral_const, measureReal_def, measure_univ]
            _ ≤ ‖x‖ + M := by linarith
        nlinarith [mul_le_mul_of_nonneg_left h_int_le L.coe_nonneg]

/-- Window growth bound for a characteristic flow given boundary regularity:
clamps the marginal curve into `[0, T]` (for the universal probability
instance), derives the interior `IsCharacteristicFlowOn` from the boundary
bundle, and applies `characteristicFlow_boundary_regularity` +
`flow_distance_growth_bound_on`.  Returns the linear growth constant `C`
together with per-`z` window continuity of the joint flow curve. -/
private lemma vlasovGlue_flow_growthBound
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (μ : ℝ → Measure (PhaseSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT_pos : 0 < T)
    (hμ_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (μ t))
    (hM : ∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (μ t)) ≤ M)
    (h_ic : ∀ z : PhaseSpace d, charX 0 z = z.1 ∧ charV 0 z = z.2)
    (h_boundary : ∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
        HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (μ t)) (charX t z)))
          (Set.Icc 0 T) t) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
        ‖(charX s z, charV s z)‖ ≤ C * (‖z‖ + 1)) ∧
      (∀ z : PhaseSpace d,
        ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T)) := by
  obtain ⟨M, hM_nn, hM_bd⟩ := hM
  set clampT : ℝ → ℝ := fun t => max 0 (min t T) with hclampT_def
  have hclampT_mem : ∀ t, clampT t ∈ Set.Icc (0 : ℝ) T := by
    intro t
    simp only [hclampT_def, Set.mem_Icc]
    exact ⟨le_max_left _ _, max_le hT_pos.le (min_le_right _ _)⟩
  have hclampT_id : ∀ t ∈ Set.Icc (0 : ℝ) T, clampT t = t := by
    intro t ht
    simp only [hclampT_def, min_eq_left ht.2, max_eq_right ht.1]
  set ρc : ℝ → Measure (PhysSpace d) :=
    fun t => spatialMarginal (μ (clampT t)) with hρc_def
  have hρc_isProb : ∀ t, IsProbabilityMeasure (ρc t) := by
    intro t
    have : IsProbabilityMeasure (μ (clampT t)) :=
      (hμ_mom (clampT t) (hclampT_mem t)).1
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hM_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(ρc t) ≤ M := by
    intro t _ht
    rw [hρc_def]
    exact hM_bd (clampT t) (hclampT_mem t)
  have h_y_int_ρc : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖) (ρc t) := by
    intro t ht
    have h_eq : ρc t = spatialMarginal (μ t) := by
      simp only [hρc_def, hclampT_id t ht]
    rw [h_eq]
    exact vlasovGlue_marginal_norm_integrable (μ t) (hμ_mom t ht)
  have h_int_ρc : ∀ t (x : PhysSpace d),
      Integrable (fun y => gradW (x - y)) (ρc t) :=
    fun t x => by
      have := dobrushinFlow_marginal_gradW_integrable gradW L hL T μ hμ_mom
        (clampT t) (hclampT_mem t) x
      simpa only [hρc_def] using this
  have h_bdry_ρc : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
      HasDerivWithinAt (fun s => charV s z)
        (-(convolveFunctionMeasure gradW (ρc t) (charX t z)))
        (Set.Icc 0 T) t := by
    intro z t ht
    have h_eq : ρc t = spatialMarginal (μ t) := by
      simp only [hρc_def, hclampT_id t ht]
    rw [h_eq]
    exact h_boundary z t ht
  have h_flow_ρc : IsCharacteristicFlowOn gradW ρc charX charV
      (Set.Ioo 0 T) Set.univ := by
    refine ⟨fun z _ => h_ic z, fun t ht z _ => ?_, fun t ht z _ => ?_⟩
    · have ht_Icc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
      exact ((h_bdry_ρc z t ht_Icc).1).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    · have ht_Icc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
      exact ((h_bdry_ρc z t ht_Icc).2).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  obtain ⟨h_init_ρc, h_cont_Icc_ρc, h_deriv_Ico_ρc⟩ :=
    characteristicFlow_boundary_regularity gradW ρc charX charV T hT_pos.le
      h_flow_ρc h_bdry_ρc
  obtain ⟨C, hC_nn, hC_pair⟩ :=
    flow_distance_growth_bound_on gradW L hL ρc charX charV T hT_pos.le
      h_init_ρc h_cont_Icc_ρc h_deriv_Ico_ρc M hM_nn hM_ρ h_y_int_ρc h_int_ρc
  exact ⟨C, hC_nn, hC_pair, h_cont_Icc_ρc⟩

/-- Generic seam continuity of the force-integral functional
`s ↦ ∫ ⟪V s z, ∇ₓφ(Φ s z)⟫ − ⟪(gradW ⋆ ρ s)(X s z), ∇ᵥφ(Φ s z)⟫ ∂f₀`
at a window endpoint, by dominated convergence.  `S` is the one-sided
neighborhood filter set (`Iic T` or `Ici T`), `W` the compact window
(`Icc 0 T` or `Icc T (T+T₀)`) carrying the uniform data: a linear growth
bound `C` on the flow, a moment envelope `M` on the marginal curve `ρ`, and
kernel integrability.  Instantiated on the LEFT by `f_prev`'s window flow and
on the RIGHT by the composed flow off `g`. -/
private lemma vlasovGlue_seam_forceIntegral_cont
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ_cont : Continuous gradXφ) (hgradVφ_cont : Continuous gradVφ)
    (M_φ : ℝ)
    (hgradXφ_bd : ∀ z : PhaseSpace d, ‖gradXφ z‖ ≤ M_φ)
    (hgradVφ_bd : ∀ z : PhaseSpace d, ‖gradVφ z‖ ≤ M_φ)
    (ρ : ℝ → Measure (PhysSpace d))
    (X V : ℝ → PhaseSpace d → PhysSpace d)
    (T₀ : ℝ) (S : Set ℝ) (W : Set ℝ)
    (hW_nhd : W ∈ nhdsWithin T₀ S)
    (hρ_prob : ∀ s ∈ W, IsProbabilityMeasure (ρ s))
    (M : ℝ) (hM : ∀ s ∈ W, ∫ y, ‖y‖ ∂(ρ s) ≤ M)
    (h_y_int : ∀ s ∈ W, Integrable (fun y : PhysSpace d => ‖y‖) (ρ s))
    (h_int : ∀ s ∈ W, ∀ x : PhysSpace d, Integrable (fun y => gradW (x - y)) (ρ s))
    (C : ℝ)
    (hC_pair : ∀ s ∈ W, ∀ z : PhaseSpace d, ‖(X s z, V s z)‖ ≤ C * (‖z‖ + 1))
    (h_aemeas : ∀ s ∈ W, AEMeasurable (fun z : PhaseSpace d => (X s z, V s z)) f₀)
    (h_X_cont : ∀ z : PhaseSpace d, ContinuousWithinAt (fun s => X s z) S T₀)
    (h_V_cont : ∀ z : PhaseSpace d, ContinuousWithinAt (fun s => V s z) S T₀)
    (h_conv_cwn : ∀ z : PhaseSpace d, ContinuousWithinAt
        (fun s => convolveFunctionMeasure gradW (ρ s) (X s z)) S T₀) :
    ContinuousWithinAt
      (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ (V s z) (gradXφ (X s z, V s z)) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (ρ s) (X s z))
            (gradVφ (X s z, V s z))) ∂f₀) S T₀ := by
  set bound_fn : PhaseSpace d → ℝ := fun z =>
    M_φ * (C * (‖z‖ + 1))
    + (‖gradW 0‖ + (L : ℝ) * (C * (‖z‖ + 1)) + (L : ℝ) * M) * M_φ
    with hbound_def
  have hbound_int : Integrable bound_fn f₀ := by
    have ha : Integrable
        (fun z : PhaseSpace d =>
          (M_φ * C + L * M_φ * C) * ‖z‖
          + (M_φ * C + (‖gradW 0‖ + L * C + L * M) * M_φ)) f₀ :=
      (hf₀_int.const_mul _).add (integrable_const _)
    refine ha.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [hbound_def]; ring
  have h_conv_force : ∀ s ∈ W, ∀ x : PhysSpace d,
      ‖convolveFunctionMeasure gradW (ρ s) x‖
        ≤ ‖gradW 0‖ + (L : ℝ) * ‖x‖ + (L : ℝ) * M := by
    intro s hs x
    have := hρ_prob s hs
    exact vlasovGlue_conv_force_bound gradW L hL (ρ s) M (hM s hs)
      (h_y_int s hs) (h_int s hs) x
  have hB : ∀ s ∈ W, ∀ z : PhaseSpace d,
      ‖@inner ℝ (PhysSpace d) _ (V s z) (gradXφ (X s z, V s z)) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (ρ s) (X s z))
            (gradVφ (X s z, V s z))‖ ≤ bound_fn z := by
    intro s hs z
    have hV : ‖V s z‖ ≤ C * (‖z‖ + 1) :=
      le_trans (norm_snd_le (X s z, V s z)) (hC_pair s hs z)
    have hX : ‖X s z‖ ≤ C * (‖z‖ + 1) :=
      le_trans (norm_fst_le (X s z, V s z)) (hC_pair s hs z)
    have ht1 : ‖@inner ℝ (PhysSpace d) _ (V s z) (gradXφ (X s z, V s z))‖
        ≤ M_φ * (C * (‖z‖ + 1)) := by
      refine le_trans (norm_inner_le_norm _ _) ?_
      have := mul_le_mul hV (hgradXφ_bd (X s z, V s z))
        (norm_nonneg _) (le_trans (norm_nonneg _) hV)
      calc ‖V s z‖ * ‖gradXφ (X s z, V s z)‖
          ≤ (C * (‖z‖ + 1)) * M_φ := this
        _ = M_φ * (C * (‖z‖ + 1)) := by ring
    have ht2 : ‖@inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ s) (X s z))
          (gradVφ (X s z, V s z))‖
        ≤ (‖gradW 0‖ + (L : ℝ) * (C * (‖z‖ + 1)) + (L : ℝ) * M) * M_φ := by
      refine le_trans (norm_inner_le_norm _ _) ?_
      have hc : ‖convolveFunctionMeasure gradW (ρ s) (X s z)‖
          ≤ ‖gradW 0‖ + (L : ℝ) * (C * (‖z‖ + 1)) + (L : ℝ) * M := by
        refine le_trans (h_conv_force s hs (X s z)) ?_
        have := mul_le_mul_of_nonneg_left hX L.coe_nonneg
        linarith
      have hcnn : 0 ≤ ‖gradW 0‖ + (L : ℝ) * (C * (‖z‖ + 1)) + (L : ℝ) * M :=
        le_trans (norm_nonneg _) hc
      exact mul_le_mul hc (hgradVφ_bd (X s z, V s z)) (norm_nonneg _) hcnn
    calc ‖_ - _‖
        ≤ ‖@inner ℝ (PhysSpace d) _ (V s z) (gradXφ (X s z, V s z))‖
          + ‖@inner ℝ (PhysSpace d) _
              (convolveFunctionMeasure gradW (ρ s) (X s z))
              (gradVφ (X s z, V s z))‖ := norm_sub_le _ _
      _ ≤ bound_fn z := by simp only [hbound_def]; linarith
  apply continuousWithinAt_of_dominated (bound := bound_fn)
  · -- AEStronglyMeasurable in z, eventually in s
    apply Filter.Eventually.mono hW_nhd
    intro s hs
    have h_aem_pair := h_aemeas s hs
    have h_aem_X : AEMeasurable (fun z : PhaseSpace d => X s z) f₀ :=
      measurable_fst.comp_aemeasurable h_aem_pair
    have h_aem_V : AEMeasurable (fun z : PhaseSpace d => V s z) f₀ :=
      measurable_snd.comp_aemeasurable h_aem_pair
    have h1 : AEStronglyMeasurable
        (fun z : PhaseSpace d => @inner ℝ (PhysSpace d) _ (V s z)
          (gradXφ (X s z, V s z))) f₀ := by
      have hg : AEMeasurable (fun z : PhaseSpace d => gradXφ (X s z, V s z)) f₀ :=
        hgradXφ_cont.measurable.comp_aemeasurable (h_aem_X.prodMk h_aem_V)
      exact (continuous_inner.measurable.comp_aemeasurable
        (h_aem_V.prodMk hg)).aestronglyMeasurable
    have h2 : AEStronglyMeasurable
        (fun z : PhaseSpace d => @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ s) (X s z))
          (gradVφ (X s z, V s z))) f₀ := by
      have hconv_aem : AEMeasurable
          (fun z : PhaseSpace d => convolveFunctionMeasure gradW (ρ s) (X s z)) f₀ := by
        have hconv_cont' : Continuous (fun x : PhysSpace d =>
            convolveFunctionMeasure gradW (ρ s) x) := by
          have := hρ_prob s hs
          exact (convolveFunctionMeasure_lipschitz_in_x gradW L hL
            (ρ s) (h_int s hs)).continuous
        exact hconv_cont'.measurable.comp_aemeasurable h_aem_X
      have hg : AEMeasurable (fun z : PhaseSpace d => gradVφ (X s z, V s z)) f₀ :=
        hgradVφ_cont.measurable.comp_aemeasurable (h_aem_X.prodMk h_aem_V)
      exact (continuous_inner.measurable.comp_aemeasurable
        (hconv_aem.prodMk hg)).aestronglyMeasurable
    exact h1.sub h2
  · -- dominator bound, eventually in s
    apply Filter.Eventually.mono hW_nhd
    intro s hs
    exact Filter.Eventually.of_forall fun z => hB s hs z
  · exact hbound_int
  · -- pointwise continuity in s, for every z
    apply Filter.Eventually.of_forall
    intro z
    have h_pair_cwn : ContinuousWithinAt (fun s => (X s z, V s z)) S T₀ :=
      (h_X_cont z).prodMk (h_V_cont z)
    have h_gX_cwn : ContinuousWithinAt
        (fun s => gradXφ (X s z, V s z)) S T₀ :=
      hgradXφ_cont.continuousAt.comp_continuousWithinAt h_pair_cwn
    have h_gV_cwn : ContinuousWithinAt
        (fun s => gradVφ (X s z, V s z)) S T₀ :=
      hgradVφ_cont.continuousAt.comp_continuousWithinAt h_pair_cwn
    have h_term1 : ContinuousWithinAt
        (fun s => @inner ℝ (PhysSpace d) _ (V s z)
          (gradXφ (X s z, V s z))) S T₀ :=
      (h_V_cont z).inner h_gX_cwn
    have h_term2 : ContinuousWithinAt
        (fun s => @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ s) (X s z))
          (gradVφ (X s z, V s z))) S T₀ :=
      (h_conv_cwn z).inner h_gV_cwn
    exact h_term1.sub h_term2

/-- LEFT seam continuity of the force-integral functional at `T`: on `Iic T`
the glued solution agrees with `f_prev` (via `hf_next_le`), whose window
pushforward representation reduces the claim to the generic seam DCT lemma
`vlasovGlue_seam_forceIntegral_cont` on `f_prev`'s window flow. -/
private lemma vlasovGlue_seam_contLeft
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT_pos : 0 < T)
    (f_prev : ℝ → Measure (PhaseSpace d))
    (h_prev_init : f_prev 0 = f₀)
    (h_prev_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f_prev t))
    (hM_prev : ∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f_prev t)) ≤ M)
    (charX_prev charV_prev : ℝ → PhaseSpace d → PhysSpace d)
    (h_prev_push : ∀ t ∈ Set.Icc (0 : ℝ) T,
        f_prev t =
          Measure.map (fun z : PhaseSpace d => (charX_prev t z, charV_prev t z)) (f_prev 0))
    (h_prev_aemeas : ∀ s ∈ Set.Icc (0 : ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) (f_prev 0))
    (h_prev_boundary : ∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
        HasDerivWithinAt (fun s => charX_prev s z) (charV_prev t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV_prev s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (f_prev t)) (charX_prev t z)))
          (Set.Icc 0 T) t)
    (h_prev_ic : ∀ z : PhaseSpace d, charX_prev 0 z = z.1 ∧ charV_prev 0 z = z.2)
    (f_next : ℝ → Measure (PhaseSpace d))
    (hf_next_le : ∀ s, s ≤ T → f_next s = f_prev s)
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z : PhaseSpace d, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z : PhaseSpace d, gradVφ z = gradient (fun v => φ (z.1, v)) z.2) :
    ContinuousWithinAt
      (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
              @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (spatialMarginal (f_next s)) z.1)
                (gradVφ z)) ∂(f_next s)) (Set.Iic T) T := by
  have h_nhd_L : Set.Icc (0 : ℝ) T ∈ nhdsWithin T (Set.Iic T) :=
    Icc_mem_nhdsLE hT_pos
  have hgradXφ_cont : Continuous gradXφ :=
    vlasovGlue_gradXφ_continuous φ hφ_smooth gradXφ hgradXφ
  have hgradVφ_cont : Continuous gradVφ :=
    vlasovGlue_gradVφ_continuous φ hφ_smooth gradVφ hgradVφ
  have h_int_marg := dobrushinFlow_marginal_gradW_integrable gradW L hL T
    f_prev h_prev_mom
  have h_push_marg : ∀ s ∈ Set.Icc (0 : ℝ) T,
      spatialMarginal (f_prev s)
        = Measure.map (fun z : PhaseSpace d => charX_prev s z) f₀ := by
    intro s hs
    have h_pair_aem : AEMeasurable
        (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) f₀ :=
      h_prev_init ▸ h_prev_aemeas s hs
    unfold spatialMarginal
    rw [h_prev_push s hs, h_prev_init,
        AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable h_pair_aem]
    rfl
  have h_aemeas_marg : ∀ s ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => charX_prev s z) f₀ := by
    intro s hs
    have h_pair_aem : AEMeasurable
        (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) f₀ :=
      h_prev_init ▸ h_prev_aemeas s hs
    exact measurable_fst.comp_aemeasurable h_pair_aem
  obtain ⟨M_ρ, hM_ρ_nn, hM_ρ⟩ := hM_prev
  have h_y_int_marg : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal (f_prev t)) :=
    fun t ht => vlasovGlue_marginal_norm_integrable (f_prev t) (h_prev_mom t ht)
  obtain ⟨C_T, hC_T_nn, hC_T_pair, h_cont_Icc_prev⟩ :=
    vlasovGlue_flow_growthBound gradW L hL f_prev charX_prev charV_prev
      T hT_pos h_prev_mom ⟨M_ρ, hM_ρ_nn, hM_ρ⟩ h_prev_ic h_prev_boundary
  have hC_T : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖charX_prev s z‖ ≤ C_T * (‖z‖ + 1) := by
    intro s hs z
    exact le_trans (norm_fst_le (charX_prev s z, charV_prev s z))
      (hC_T_pair s hs z)
  have h_conv_z_cont : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Continuous (fun z : PhaseSpace d =>
        convolveFunctionMeasure gradW (spatialMarginal (f_prev s)) z.1) := by
    intro s hs
    have : IsProbabilityMeasure (f_prev s) := (h_prev_mom s hs).1
    have : IsProbabilityMeasure (spatialMarginal (f_prev s)) :=
      Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    exact (convolveFunctionMeasure_lipschitz_in_x gradW L hL
      (spatialMarginal (f_prev s)) (h_int_marg s hs)).continuous.comp continuous_fst
  have h_integrand_cont : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Continuous (fun z : PhaseSpace d =>
        @inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
        @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (spatialMarginal (f_prev s)) z.1)
          (gradVφ z)) := by
    intro s hs
    exact (continuous_snd.inner hgradXφ_cont).sub
      ((h_conv_z_cont s hs).inner hgradVφ_cont)
  have h_eq_L : (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (f_next s)) z.1)
            (gradVφ z)) ∂(f_next s))
      =ᶠ[nhdsWithin T (Set.Iic T)]
      (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ (charV_prev s z)
            (gradXφ (charX_prev s z, charV_prev s z)) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (f_prev s))
              (charX_prev s z))
            (gradVφ (charX_prev s z, charV_prev s z))) ∂f₀) := by
    apply Filter.Eventually.mono h_nhd_L
    intro s hs
    have h_fnext : f_next s = f_prev s := hf_next_le s hs.2
    have h_marg : spatialMarginal (f_next s) = spatialMarginal (f_prev s) :=
      congrArg spatialMarginal h_fnext
    have h_aemeas_f₀ : AEMeasurable
        (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) f₀ :=
      h_prev_init ▸ h_prev_aemeas s hs
    change (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
            @inner ℝ (PhysSpace d) _
              (convolveFunctionMeasure gradW (spatialMarginal (f_next s)) z.1)
              (gradVφ z)) ∂(f_next s))
        = ∫ z, (@inner ℝ (PhysSpace d) _ (charV_prev s z)
              (gradXφ (charX_prev s z, charV_prev s z)) -
            @inner ℝ (PhysSpace d) _
              (convolveFunctionMeasure gradW (spatialMarginal (f_prev s))
                (charX_prev s z))
              (gradVφ (charX_prev s z, charV_prev s z))) ∂f₀
    have h_meq : f_next s
        = Measure.map
            (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) f₀ := by
      rw [h_fnext, h_prev_push s hs, h_prev_init]
    rw [h_marg, h_meq,
        integral_map h_aemeas_f₀
          (h_integrand_cont s hs).aestronglyMeasurable]
  obtain ⟨M_φ, hgradXφ_bd, hgradVφ_bd⟩ :=
    vlasovGlue_gradφ_bound φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ
  have h_X_cont : ∀ z : PhaseSpace d,
      ContinuousWithinAt (fun s => charX_prev s z) (Set.Iic T) T := fun z =>
    ((h_prev_boundary z T
        ⟨hT_pos.le, le_refl T⟩).1.continuousWithinAt).mono_of_mem_nhdsWithin h_nhd_L
  have h_V_cont : ∀ z : PhaseSpace d,
      ContinuousWithinAt (fun s => charV_prev s z) (Set.Iic T) T := fun z =>
    ((h_prev_boundary z T
        ⟨hT_pos.le, le_refl T⟩).2.continuousWithinAt).mono_of_mem_nhdsWithin h_nhd_L
  have h_conv_cwn : ∀ z : PhaseSpace d, ContinuousWithinAt
      (fun s => convolveFunctionMeasure gradW (spatialMarginal (f_prev s))
        (charX_prev s z)) (Set.Iic T) T := fun z =>
    flowConv_continuousWithinAt_Iic_seam gradW L hL charX_prev f₀
      hf₀_int hT_pos (fun s => spatialMarginal (f_prev s))
      h_push_marg h_aemeas_marg
      (fun z' => (h_cont_Icc_prev z').continuousWithinAt
        (Set.right_mem_Icc.mpr hT_pos.le) |>.fst) C_T hC_T_nn hC_T z
  have h_cont_pf : ContinuousWithinAt
      (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ (charV_prev s z)
            (gradXφ (charX_prev s z, charV_prev s z)) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (f_prev s))
              (charX_prev s z))
            (gradVφ (charX_prev s z, charV_prev s z))) ∂f₀)
      (Set.Iic T) T :=
    vlasovGlue_seam_forceIntegral_cont gradW L hL f₀ hf₀_int gradXφ gradVφ
      hgradXφ_cont hgradVφ_cont M_φ hgradXφ_bd hgradVφ_bd
      (fun s => spatialMarginal (f_prev s)) charX_prev charV_prev
      T (Set.Iic T) (Set.Icc 0 T) h_nhd_L
      (fun s hs => by
        have : IsProbabilityMeasure (f_prev s) := (h_prev_mom s hs).1
        exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable)
      M_ρ hM_ρ h_y_int_marg h_int_marg C_T hC_T_pair
      (fun s hs => h_prev_init ▸ h_prev_aemeas s hs)
      h_X_cont h_V_cont h_conv_cwn
  have h_val_T : (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (f_next T)) z.1)
            (gradVφ z)) ∂(f_next T))
      = ∫ z, (@inner ℝ (PhysSpace d) _ (charV_prev T z)
            (gradXφ (charX_prev T z, charV_prev T z)) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (f_prev T))
              (charX_prev T z))
            (gradVφ (charX_prev T z, charV_prev T z))) ∂f₀ := by
    have hT_Icc : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
    have h_fnext_T : f_next T = f_prev T := hf_next_le T (le_refl T)
    have h_marg : spatialMarginal (f_next T) = spatialMarginal (f_prev T) :=
      congrArg spatialMarginal h_fnext_T
    have h_aemeas_f₀_T : AEMeasurable
        (fun z : PhaseSpace d => (charX_prev T z, charV_prev T z)) f₀ :=
      h_prev_init ▸ h_prev_aemeas T hT_Icc
    have h_meq : f_next T
        = Measure.map
            (fun z : PhaseSpace d => (charX_prev T z, charV_prev T z)) f₀ := by
      rw [h_fnext_T, h_prev_push T hT_Icc, h_prev_init]
    rw [h_marg, h_meq,
        integral_map h_aemeas_f₀_T (h_integrand_cont T hT_Icc).aestronglyMeasurable]
  exact h_cont_pf.congr_of_eventuallyEq h_eq_L h_val_T

/-- A shifted flow curve `s ↦ Φ (s − T) w` is continuous within `Ici T` at `T`
when the unshifted curve has a one-sided derivative at `0` on `[0, T_0]`. -/
private lemma vlasovGlue_shifted_flow_contWithin
    {d : ℕ} [NeZero d]
    (charW : ℝ → PhaseSpace d → PhysSpace d) (w : PhaseSpace d) {v₀ : PhysSpace d}
    (T : ℝ) {T_0 : ℝ} (hT_0_pos : 0 < T_0)
    (hb : HasDerivWithinAt (fun s => charW s w) v₀ (Set.Icc 0 T_0) 0) :
    ContinuousWithinAt (fun s => charW (s - T) w) (Set.Ici T) T := by
  have h_nhdsW_0 : Set.Icc (0 : ℝ) T_0 ∈ nhdsWithin 0 (Set.Ici 0) :=
    Icc_mem_nhdsGE hT_0_pos
  have h_cont : ContinuousWithinAt (fun s => charW s w) (Set.Ici 0) 0 :=
    hb.continuousWithinAt.mono_of_mem_nhdsWithin h_nhdsW_0
  have h_sub_cont : ContinuousWithinAt (fun s : ℝ => s - T) (Set.Ici T) T :=
    ((continuous_id.sub continuous_const).continuousAt).continuousWithinAt
  have h_sub_maps : Set.MapsTo (fun s : ℝ => s - T) (Set.Ici T) (Set.Ici 0) :=
    fun s hs => Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp hs])
  exact ContinuousWithinAt.comp_of_eq h_cont h_sub_cont h_sub_maps (sub_self T)

/-- Composed-pushforward infrastructure on the glued window `[T, T+T_0]`:
`g (s−T)` is the pushforward of `f₀` by the composed phase-space flow
(`g`'s window flow after the outer time-`T` map `(XT, VT)`), its spatial
marginal is the pushforward by the composed position map, and both composed
maps are a.e.-measurable. -/
private lemma vlasovGlue_composed_pushforward
    {d : ℕ} [NeZero d]
    (f₀ : Measure (PhaseSpace d))
    (g : ℝ → Measure (PhaseSpace d))
    (f_prevT : Measure (PhaseSpace d))
    (charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    (XT VT : PhaseSpace d → PhysSpace d)
    {T T_0 : ℝ}
    (h_outer_aemeas : AEMeasurable (fun z : PhaseSpace d => (XT z, VT z)) f₀)
    (h_prevT_push : f_prevT = Measure.map (fun z : PhaseSpace d => (XT z, VT z)) f₀)
    (hg_init : g 0 = f_prevT)
    (hg_push_ex : ∀ t ∈ Set.Icc (0 : ℝ) T_0,
        g t = Measure.map (fun z : PhaseSpace d => (charX_g t z, charV_g t z)) (g 0))
    (hg_aemeas_ex : ∀ s ∈ Set.Icc (0 : ℝ) T_0,
        AEMeasurable (fun z : PhaseSpace d => (charX_g s z, charV_g s z)) (g 0)) :
    (∀ τ ∈ Set.Icc (0 : ℝ) T_0,
        AEMeasurable (fun z : PhaseSpace d =>
          (charX_g τ (XT z, VT z), charV_g τ (XT z, VT z))) f₀) ∧
    (∀ s ∈ Set.Icc T (T + T_0),
        g (s - T) = Measure.map (fun z : PhaseSpace d =>
          (charX_g (s - T) (XT z, VT z), charV_g (s - T) (XT z, VT z))) f₀) ∧
    (∀ s ∈ Set.Icc T (T + T_0),
        spatialMarginal (g (s - T)) = Measure.map (fun z : PhaseSpace d =>
          charX_g (s - T) (XT z, VT z)) f₀) ∧
    (∀ s ∈ Set.Icc T (T + T_0),
        AEMeasurable (fun z : PhaseSpace d => charX_g (s - T) (XT z, VT z)) f₀) := by
  have h_g_at_aemeas : ∀ τ ∈ Set.Icc (0 : ℝ) T_0,
      AEMeasurable (fun z : PhaseSpace d => (charX_g τ z, charV_g τ z))
        (Measure.map (fun z : PhaseSpace d => (XT z, VT z)) f₀) := by
    intro τ hτ
    have := hg_aemeas_ex τ hτ
    rw [hg_init, h_prevT_push] at this
    exact this
  have h_comp_aemeas : ∀ τ ∈ Set.Icc (0 : ℝ) T_0,
      AEMeasurable (fun z : PhaseSpace d =>
        (charX_g τ (XT z, VT z), charV_g τ (XT z, VT z))) f₀ := by
    intro τ hτ
    exact (h_g_at_aemeas τ hτ).comp_aemeasurable h_outer_aemeas
  have h_push_comp : ∀ s ∈ Set.Icc T (T + T_0),
      g (s - T) = Measure.map (fun z : PhaseSpace d =>
        (charX_g (s - T) (XT z, VT z), charV_g (s - T) (XT z, VT z))) f₀ := by
    intro s hs
    have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rw [hg_push_ex (s - T) hsT_Icc, hg_init, h_prevT_push,
        AEMeasurable.map_map_of_aemeasurable
          (h_g_at_aemeas (s - T) hsT_Icc) h_outer_aemeas]
    rfl
  refine ⟨h_comp_aemeas, h_push_comp, fun s hs => ?_, fun s hs => ?_⟩
  · have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    unfold spatialMarginal
    rw [h_push_comp s hs,
        AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable
          (h_comp_aemeas (s - T) hsT_Icc)]
    rfl
  · have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact measurable_fst.comp_aemeasurable (h_comp_aemeas (s - T) hsT_Icc)

/-- Pointwise composed-pushforward rewrite of the force integral on the glued
window: for `s ∈ [T, T+T_0]` the integral of the force integrand against
`f_next s` equals the integral of the flow-composed integrand against `f₀`.
Serves both the eventually-equal rewrite and the value-at-`T` bridge of the
RIGHT seam close. -/
private lemma vlasovGlue_composed_integral_eq
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d))
    {T T_0 : ℝ} (hT_pos : 0 < T)
    (f_prev g : ℝ → Measure (PhaseSpace d))
    (h_prev_init : f_prev 0 = f₀)
    (charX_prev charV_prev charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    (h_prev_push : ∀ t ∈ Set.Icc (0 : ℝ) T,
        f_prev t =
          Measure.map (fun z : PhaseSpace d => (charX_prev t z, charV_prev t z)) (f_prev 0))
    (hg_init : g 0 = f_prev T)
    (hg_init_cond : ∀ z : PhaseSpace d, charX_g 0 z = z.1 ∧ charV_g 0 z = z.2)
    (f_next : ℝ → Measure (PhaseSpace d))
    (hf_next_T : f_next T = f_prev T)
    (hf_next_gt : ∀ s, T < s → f_next s = g (s - T))
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (h_comp_aemeas : ∀ τ ∈ Set.Icc (0 : ℝ) T_0,
        AEMeasurable (fun z : PhaseSpace d =>
          (charX_g τ (charX_prev T z, charV_prev T z),
           charV_g τ (charX_prev T z, charV_prev T z))) f₀)
    (h_g_push_comp : ∀ s ∈ Set.Icc T (T + T_0),
        g (s - T) = Measure.map (fun z : PhaseSpace d =>
          (charX_g (s - T) (charX_prev T z, charV_prev T z),
           charV_g (s - T) (charX_prev T z, charV_prev T z))) f₀)
    (h_integrand_cont : ∀ τ ∈ Set.Icc (0 : ℝ) T_0,
        Continuous (fun z : PhaseSpace d =>
          @inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (g τ)) z.1)
            (gradVφ z)))
    (s : ℝ) (hs : s ∈ Set.Icc T (T + T_0)) :
    (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
        @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (spatialMarginal (f_next s)) z.1)
          (gradVφ z)) ∂(f_next s))
      = ∫ z, (@inner ℝ (PhysSpace d) _
            (charV_g (s - T) (charX_prev T z, charV_prev T z))
            (gradXφ (charX_g (s - T) (charX_prev T z, charV_prev T z),
                     charV_g (s - T) (charX_prev T z, charV_prev T z))) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (g (s - T)))
              (charX_g (s - T) (charX_prev T z, charV_prev T z)))
            (gradVφ (charX_g (s - T) (charX_prev T z, charV_prev T z),
                     charV_g (s - T) (charX_prev T z, charV_prev T z)))) ∂f₀ := by
  have hT_Icc : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
  have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  by_cases hs_eq : s = T
  · -- s = T: f_next T = f_prev T = composed pushforward (collapse g at 0 = id)
    have hs_T_zero : s - T = 0 := by rw [hs_eq]; exact sub_self T
    have h_fnext_s : f_next s = f_prev T := by
      rw [hs_eq]; exact hf_next_T
    have h_marg_eq : spatialMarginal (f_next s) = spatialMarginal (g (s - T)) := by
      rw [h_fnext_s, hs_T_zero, hg_init]
    have h_meq : f_next s = Measure.map
        (fun z : PhaseSpace d =>
          (charX_g (s - T) (charX_prev T z, charV_prev T z),
           charV_g (s - T) (charX_prev T z, charV_prev T z))) f₀ := by
      rw [h_fnext_s, h_prev_push T hT_Icc, h_prev_init]
      apply Measure.map_congr
      apply Filter.Eventually.of_forall
      intro z
      simp only [hs_T_zero, (hg_init_cond _).1, (hg_init_cond _).2]
    rw [h_marg_eq, h_meq,
        integral_map (h_comp_aemeas (s - T) hsT_Icc)
          (h_integrand_cont (s - T) hsT_Icc).aestronglyMeasurable]
  · -- s > T: f_next s = g (s − T) = composed pushforward
    have hs_gt : T < s := lt_of_le_of_ne hs.1 (Ne.symm hs_eq)
    have h_fnext_s : f_next s = g (s - T) := hf_next_gt s hs_gt
    have h_marg_eq : spatialMarginal (f_next s) = spatialMarginal (g (s - T)) :=
      congrArg spatialMarginal h_fnext_s
    have h_meq : f_next s = Measure.map
        (fun z : PhaseSpace d =>
          (charX_g (s - T) (charX_prev T z, charV_prev T z),
           charV_g (s - T) (charX_prev T z, charV_prev T z))) f₀ := by
      rw [h_fnext_s]; exact h_g_push_comp s hs
    rw [h_marg_eq, h_meq,
        integral_map (h_comp_aemeas (s - T) hsT_Icc)
          (h_integrand_cont (s - T) hsT_Icc).aestronglyMeasurable]

/-- RIGHT seam continuity of the force-integral functional at `T`: on `Ici T`
the glued solution is `g (·−T)` (via `hf_next_T`/`hf_next_gt`), represented as
the composed pushforward of `f₀` by `g`'s window flow after `f_prev`'s time-`T`
flow; the claim reduces to the generic seam DCT lemma
`vlasovGlue_seam_forceIntegral_cont` on the composed flow. -/
private lemma vlasovGlue_seam_contRight
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT_pos : 0 < T) {T_0 : ℝ} (hT_0_pos : 0 < T_0)
    (f_prev : ℝ → Measure (PhaseSpace d))
    (h_prev_init : f_prev 0 = f₀)
    (h_prev_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f_prev t))
    (hM_prev : ∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f_prev t)) ≤ M)
    (charX_prev charV_prev : ℝ → PhaseSpace d → PhysSpace d)
    (h_prev_push : ∀ t ∈ Set.Icc (0 : ℝ) T,
        f_prev t =
          Measure.map (fun z : PhaseSpace d => (charX_prev t z, charV_prev t z)) (f_prev 0))
    (h_prev_aemeas : ∀ s ∈ Set.Icc (0 : ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) (f_prev 0))
    (h_prev_boundary : ∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
        HasDerivWithinAt (fun s => charX_prev s z) (charV_prev t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV_prev s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (f_prev t)) (charX_prev t z)))
          (Set.Icc 0 T) t)
    (h_prev_ic : ∀ z : PhaseSpace d, charX_prev 0 z = z.1 ∧ charV_prev 0 z = z.2)
    (g : ℝ → Measure (PhaseSpace d))
    (charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    (hg_init : g 0 = f_prev T)
    (hg_mom : ∀ t ∈ Set.Icc (0 : ℝ) T_0, HasFiniteFirstMoment (g t))
    (hg_mom_unif : ∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T_0, ∫ y, ‖y‖ ∂(spatialMarginal (g t)) ≤ M)
    (hg_push_ex : ∀ t ∈ Set.Icc (0 : ℝ) T_0,
        g t = Measure.map (fun z : PhaseSpace d => (charX_g t z, charV_g t z)) (g 0))
    (hg_aemeas_ex : ∀ s ∈ Set.Icc (0 : ℝ) T_0,
        AEMeasurable (fun z : PhaseSpace d => (charX_g s z, charV_g s z)) (g 0))
    (hg_boundary : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T_0,
        HasDerivWithinAt (fun s => charX_g s z) (charV_g t z) (Set.Icc 0 T_0) t ∧
        HasDerivWithinAt (fun s => charV_g s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (g t)) (charX_g t z)))
          (Set.Icc 0 T_0) t)
    (hg_init_cond : ∀ z : PhaseSpace d, charX_g 0 z = z.1 ∧ charV_g 0 z = z.2)
    (f_next : ℝ → Measure (PhaseSpace d))
    (hf_next_T : f_next T = f_prev T)
    (hf_next_gt : ∀ s, T < s → f_next s = g (s - T))
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z : PhaseSpace d, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z : PhaseSpace d, gradVφ z = gradient (fun v => φ (z.1, v)) z.2) :
    ContinuousWithinAt
      (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
              @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (spatialMarginal (f_next s)) z.1)
                (gradVφ z)) ∂(f_next s)) (Set.Ici T) T := by
  have hT_Icc : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
  have h_nhd_R : Set.Icc T (T + T_0) ∈ nhdsWithin T (Set.Ici T) :=
    Icc_mem_nhdsGE (by linarith : T < T + T_0)
  have h_outer_aemeas : AEMeasurable
      (fun z : PhaseSpace d => (charX_prev T z, charV_prev T z)) f₀ :=
    h_prev_init ▸ h_prev_aemeas T hT_Icc
  set Zpos : ℝ → PhaseSpace d → PhysSpace d :=
    fun s z => charX_g (s - T) (charX_prev T z, charV_prev T z) with hZpos_def
  set Zvel : ℝ → PhaseSpace d → PhysSpace d :=
    fun s z => charV_g (s - T) (charX_prev T z, charV_prev T z) with hZvel_def
  have hgradXφ_cont : Continuous gradXφ :=
    vlasovGlue_gradXφ_continuous φ hφ_smooth gradXφ hgradXφ
  have hgradVφ_cont : Continuous gradVφ :=
    vlasovGlue_gradVφ_continuous φ hφ_smooth gradVφ hgradVφ
  have h_int_marg_g := dobrushinFlow_marginal_gradW_integrable gradW L hL T_0
    g hg_mom
  -- Composed pushforward of g's spatial marginal (hoisted helper), bridged to
  -- the Zpos/Zvel forms.
  have h_prevT_push : f_prev T
      = Measure.map (fun z : PhaseSpace d => (charX_prev T z, charV_prev T z)) f₀ := by
    rw [h_prev_push T hT_Icc, h_prev_init]
  obtain ⟨h_comp_aemeas, h_g_push_comp', h_push_marg', h_aemeas_marg'⟩ :=
    vlasovGlue_composed_pushforward f₀ g (f_prev T) charX_g charV_g
      (charX_prev T) (charV_prev T) h_outer_aemeas h_prevT_push hg_init
      hg_push_ex hg_aemeas_ex
  have h_g_push_comp : ∀ s ∈ Set.Icc T (T + T_0),
      g (s - T) = Measure.map
        (fun z : PhaseSpace d => (Zpos s z, Zvel s z)) f₀ := by
    intro s hs
    simpa only [hZpos_def, hZvel_def] using h_g_push_comp' s hs
  have h_push_marg : ∀ s ∈ Set.Icc T (T + T_0),
      spatialMarginal (g (s - T))
        = Measure.map (fun z : PhaseSpace d => Zpos s z) f₀ := by
    intro s hs
    simpa only [hZpos_def] using h_push_marg' s hs
  have h_aemeas_marg : ∀ s ∈ Set.Icc T (T + T_0),
      AEMeasurable (fun z : PhaseSpace d => Zpos s z) f₀ := by
    intro s hs
    simpa only [hZpos_def] using h_aemeas_marg' s hs
  -- Composed growth bound: Piece A on g over [0,T_0] composed with Piece A on
  -- prev at T (both via the hoisted clamp construction).
  obtain ⟨C_prev, hC_prev_nn, hC_prev_pair, _h_cont_Icc_prev⟩ :=
    vlasovGlue_flow_growthBound gradW L hL f_prev charX_prev charV_prev
      T hT_pos h_prev_mom hM_prev h_prev_ic h_prev_boundary
  obtain ⟨C_g, hC_g_nn, hC_g_pair, _h_cont_Icc_g⟩ :=
    vlasovGlue_flow_growthBound gradW L hL g charX_g charV_g
      T_0 hT_0_pos hg_mom hg_mom_unif hg_init_cond hg_boundary
  obtain ⟨M_g, _hM_g_nn, hM_g_bd⟩ := hg_mom_unif
  have h_y_int_marg_g : ∀ τ ∈ Set.Icc (0 : ℝ) T_0,
      Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal (g τ)) :=
    fun τ hτ => vlasovGlue_marginal_norm_integrable (g τ) (hg_mom τ hτ)
  set C_comp : ℝ := C_g * C_prev + C_g with hC_comp_def
  have hC_comp_nn : 0 ≤ C_comp := by positivity
  have hC_comp_pair : ∀ s ∈ Set.Icc T (T + T_0), ∀ z : PhaseSpace d,
      ‖(Zpos s z, Zvel s z)‖ ≤ C_comp * (‖z‖ + 1) := by
    intro s hs z
    have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h_prev : ‖(charX_prev T z, charV_prev T z)‖ ≤ C_prev * (‖z‖ + 1) :=
      hC_prev_pair T hT_Icc z
    have h_g : ‖(charX_g (s - T) (charX_prev T z, charV_prev T z),
                 charV_g (s - T) (charX_prev T z, charV_prev T z))‖
        ≤ C_g * (‖(charX_prev T z, charV_prev T z)‖ + 1) :=
      hC_g_pair (s - T) hsT_Icc (charX_prev T z, charV_prev T z)
    have hz1 : (0 : ℝ) ≤ ‖z‖ + 1 := by positivity
    calc ‖(Zpos s z, Zvel s z)‖
        = ‖(charX_g (s - T) (charX_prev T z, charV_prev T z),
            charV_g (s - T) (charX_prev T z, charV_prev T z))‖ := by
          simp only [hZpos_def, hZvel_def]
      _ ≤ C_g * (‖(charX_prev T z, charV_prev T z)‖ + 1) := h_g
      _ ≤ C_g * (C_prev * (‖z‖ + 1) + 1) := by
          apply mul_le_mul_of_nonneg_left _ hC_g_nn; linarith
      _ ≤ C_comp * (‖z‖ + 1) := by
          simp only [hC_comp_def]
          nlinarith [mul_nonneg hC_g_nn (norm_nonneg z),
            mul_nonneg (mul_nonneg hC_g_nn hC_prev_nn) hz1]
  have hC_comp_X : ∀ s ∈ Set.Icc T (T + T_0), ∀ z : PhaseSpace d,
      ‖Zpos s z‖ ≤ C_comp * (‖z‖ + 1) := by
    intro s hs z
    exact le_trans (norm_fst_le (Zpos s z, Zvel s z)) (hC_comp_pair s hs z)
  -- Seam continuity of the composed flow at T (hoisted shift helper).
  have h_Zpos_cont : ∀ z : PhaseSpace d,
      ContinuousWithinAt (fun s => Zpos s z) (Set.Ici T) T := by
    intro z
    have := vlasovGlue_shifted_flow_contWithin charX_g
      (charX_prev T z, charV_prev T z) T hT_0_pos
      (hg_boundary (charX_prev T z, charV_prev T z) 0 ⟨le_refl 0, hT_0_pos.le⟩).1
    simpa only [hZpos_def] using this
  have h_Zvel_cont : ∀ z : PhaseSpace d,
      ContinuousWithinAt (fun s => Zvel s z) (Set.Ici T) T := by
    intro z
    have := vlasovGlue_shifted_flow_contWithin charV_g
      (charX_prev T z, charV_prev T z) T hT_0_pos
      (hg_boundary (charX_prev T z, charV_prev T z) 0 ⟨le_refl 0, hT_0_pos.le⟩).2
    simpa only [hZvel_def] using this
  -- Continuity of the un-pushed integrand in z (for integral_map's
  -- AEStronglyMeasurable side).
  have h_conv_z_cont : ∀ τ ∈ Set.Icc (0 : ℝ) T_0,
      Continuous (fun z : PhaseSpace d =>
        convolveFunctionMeasure gradW (spatialMarginal (g τ)) z.1) := by
    intro τ hτ
    have : IsProbabilityMeasure (g τ) := (hg_mom τ hτ).1
    have : IsProbabilityMeasure (spatialMarginal (g τ)) :=
      Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    exact (convolveFunctionMeasure_lipschitz_in_x gradW L hL
      (spatialMarginal (g τ)) (h_int_marg_g τ hτ)).continuous.comp continuous_fst
  have h_integrand_cont : ∀ τ ∈ Set.Icc (0 : ℝ) T_0,
      Continuous (fun z : PhaseSpace d =>
        @inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
        @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (spatialMarginal (g τ)) z.1)
          (gradVφ z)) := by
    intro τ hτ
    exact (continuous_snd.inner hgradXφ_cont).sub
      ((h_conv_z_cont τ hτ).inner hgradVφ_cont)
  -- Eventually-equal rewrite to the composed-pushforward form (pointwise helper).
  have h_intg_eq := vlasovGlue_composed_integral_eq gradW f₀ hT_pos f_prev g
    h_prev_init charX_prev charV_prev charX_g charV_g h_prev_push hg_init
    hg_init_cond f_next hf_next_T hf_next_gt gradXφ gradVφ h_comp_aemeas
    h_g_push_comp' h_integrand_cont
  have h_eq_R : (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (f_next s)) z.1)
            (gradVφ z)) ∂(f_next s))
      =ᶠ[nhdsWithin T (Set.Ici T)]
      (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ (Zvel s z)
            (gradXφ (Zpos s z, Zvel s z)) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (g (s - T)))
              (Zpos s z))
            (gradVφ (Zpos s z, Zvel s z))) ∂f₀) := by
    apply Filter.Eventually.mono h_nhd_R
    intro s hs
    simpa only [hZpos_def, hZvel_def] using h_intg_eq s hs
  obtain ⟨M_φ, hgradXφ_bd, hgradVφ_bd⟩ :=
    vlasovGlue_gradφ_bound φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ
  -- DCT via the generic seam lemma on the composed flow.
  have h_conv_cwn : ∀ z : PhaseSpace d, ContinuousWithinAt
      (fun s => convolveFunctionMeasure gradW (spatialMarginal (g (s - T)))
        (Zpos s z)) (Set.Ici T) T := fun z =>
    flowConv_continuousWithinAt_Ici_seam gradW L hL Zpos f₀
      hf₀_int (by linarith : T < T + T_0)
      (fun s => spatialMarginal (g (s - T)))
      h_push_marg h_aemeas_marg h_Zpos_cont C_comp hC_comp_nn hC_comp_X z
  have h_aemeas_W : ∀ s ∈ Set.Icc T (T + T_0),
      AEMeasurable (fun z : PhaseSpace d => (Zpos s z, Zvel s z)) f₀ := by
    intro s hs
    have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    simpa only [hZpos_def, hZvel_def] using h_comp_aemeas (s - T) hsT_Icc
  have h_cont_pf : ContinuousWithinAt
      (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ (Zvel s z)
            (gradXφ (Zpos s z, Zvel s z)) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (g (s - T)))
              (Zpos s z))
            (gradVφ (Zpos s z, Zvel s z))) ∂f₀)
      (Set.Ici T) T :=
    vlasovGlue_seam_forceIntegral_cont gradW L hL f₀ hf₀_int gradXφ gradVφ
      hgradXφ_cont hgradVφ_cont M_φ hgradXφ_bd hgradVφ_bd
      (fun s => spatialMarginal (g (s - T))) Zpos Zvel
      T (Set.Ici T) (Set.Icc T (T + T_0)) h_nhd_R
      (fun s hs => by
        have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
          ⟨by linarith [hs.1], by linarith [hs.2]⟩
        have : IsProbabilityMeasure (g (s - T)) := (hg_mom (s - T) hsT_Icc).1
        exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable)
      M_g
      (fun s hs => hM_g_bd (s - T) ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      (fun s hs => h_y_int_marg_g (s - T) ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      (fun s hs => h_int_marg_g (s - T) ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      C_comp hC_comp_pair h_aemeas_W h_Zpos_cont h_Zvel_cont h_conv_cwn
  -- Value at T bridge (pointwise helper at s = T).
  have h_val_T : (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (f_next T)) z.1)
            (gradVφ z)) ∂(f_next T))
      = ∫ z, (@inner ℝ (PhysSpace d) _ (Zvel T z)
            (gradXφ (Zpos T z, Zvel T z)) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (g (T - T)))
              (Zpos T z))
            (gradVφ (Zpos T z, Zvel T z))) ∂f₀ := by
    simpa only [hZpos_def, hZvel_def] using
      h_intg_eq T ⟨le_refl T, by linarith⟩
  exact h_cont_pf.congr_of_eventuallyEq h_eq_R h_val_T

/-- `HasDerivAt` of the glued position flow at interior times of the extended
window: piecewise from `f_prev`'s flow (`t < T`), the two-sided union of the
boundary bundles (`t = T`), and `g`'s shifted flow (`t > T`).  Pure ODE gluing —
takes only the position projections of the flow hypotheses. -/
private lemma vlasovGlue_flowX_hasDerivAt
    {d : ℕ} [NeZero d]
    (charX_prev charV_prev charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    {T T_0 : ℝ} (hT_pos : 0 < T) (hT_0_pos : 0 < T_0)
    (h_prev_flowX : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ z : PhaseSpace d,
        HasDerivAt (fun s => charX_prev s z) (charV_prev t z) t)
    (h_prev_boundaryX : ∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
        HasDerivWithinAt (fun s => charX_prev s z) (charV_prev t z) (Set.Icc 0 T) t)
    (hg_boundaryX : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T_0,
        HasDerivWithinAt (fun s => charX_g s z) (charV_g t z) (Set.Icc 0 T_0) t)
    (hg_init_cond : ∀ z : PhaseSpace d, charX_g 0 z = z.1 ∧ charV_g 0 z = z.2)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) (T + T_0)) (z : PhaseSpace d) :
    HasDerivAt (fun s => if s ≤ T then charX_prev s z
        else charX_g (s - T) (charX_prev T z, charV_prev T z))
      (if t ≤ T then charV_prev t z
        else charV_g (t - T) (charX_prev T z, charV_prev T z)) t := by
  by_cases ht_le : t ≤ T
  · simp only [ite_eq_left ht_le]
    -- Sub-case: t < T (strict interior) vs t = T (boundary)
    by_cases ht_lt : t < T
    · -- t < T strict: piecewise function = charX_prev · z near t
      have h_ev : (fun s => if s ≤ T then charX_prev s z
          else charX_g (s - T) (charX_prev T z, charV_prev T z)) =ᶠ[nhds t]
          (fun s => charX_prev s z) := by
        apply Filter.Eventually.mono (eventually_lt_nhds ht_lt)
        intro s hs; simp [le_of_lt hs]
      exact ((h_prev_flowX t ⟨ht.1, ht_lt⟩ z).congr_of_eventuallyEq h_ev)
    · -- t = T: boundary HasDerivAt via HasDerivWithinAt.union (Iic T ∪ Ici T = univ)
      push Not at ht_lt
      have h_t_eq : t = T := le_antisymm ht_le ht_lt
      have hT_in : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
      have h_bX := h_prev_boundaryX z T hT_in
      have h0_T0_in : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T_0 := ⟨le_refl 0, hT_0_pos.le⟩
      have h_g_bX := hg_boundaryX (charX_prev T z, charV_prev T z) 0 h0_T0_in
      have h_nhd_L : Set.Icc 0 T ∈ nhdsWithin T (Set.Iic T) := Icc_mem_nhdsLE hT_pos
      have h_nhd_R : Set.Icc 0 T_0 ∈ nhdsWithin (0 : ℝ) (Set.Ici 0) :=
        Icc_mem_nhdsGE hT_0_pos
      -- LEFT: HasDerivWithinAt charX_prev on Iic T at T
      have hX_Lic := h_bX.mono_of_mem_nhdsWithin h_nhd_L
      have hX_left : HasDerivWithinAt
          (fun s => if s ≤ T then charX_prev s z
            else charX_g (s - T) (charX_prev T z, charV_prev T z))
          (charV_prev T z) (Set.Iic T) T :=
        hX_Lic.congr_of_mem (fun s hs => by simp [Set.mem_Iic.mp hs]) Set.self_mem_Iic
      -- RIGHT: chain rule from g's boundary at 0
      have hX_Ici0 := h_g_bX.mono_of_mem_nhdsWithin h_nhd_R
      have h_sub_R : HasDerivWithinAt (· - T) 1 (Set.Ici T) T :=
        ((hasDerivAt_id' T).sub_const T).hasDerivWithinAt
      have h_mapR : Set.MapsTo (· - T) (Set.Ici T) (Set.Ici 0) :=
        fun s hs => Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp hs])
      have h_chainX : HasDerivWithinAt
          (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z))
          (charV_g 0 (charX_prev T z, charV_prev T z)) (Set.Ici T) T := by
        have := HasDerivWithinAt.scomp_of_eq T hX_Ici0 h_sub_R h_mapR (sub_self T).symm
        simpa [Function.comp_def, one_smul] using this
      have hVg0_eq : charV_g 0 (charX_prev T z, charV_prev T z) = charV_prev T z :=
        (hg_init_cond (charX_prev T z, charV_prev T z)).2
      rw [hVg0_eq] at h_chainX
      have hX_right : HasDerivWithinAt
          (fun s => if s ≤ T then charX_prev s z
            else charX_g (s - T) (charX_prev T z, charV_prev T z))
          (charV_prev T z) (Set.Ici T) T :=
        h_chainX.congr_of_mem
          (fun s hs => by
            by_cases hle : s ≤ T
            · have heq : s = T := le_antisymm hle (Set.mem_Ici.mp hs)
              simp [heq, sub_self,
                (hg_init_cond (charX_prev T z, charV_prev T z)).1]
            · simp [hle])
          Set.self_mem_Ici
      have hX_union := hX_left.union hX_right
      rw [Set.Iic_union_Ici] at hX_union
      rw [h_t_eq]
      exact hX_union.hasDerivAt Filter.univ_mem
  · simp only [ite_eq_right ht_le]
    push Not at ht_le
    -- t > T: use hg_boundaryX at (t - T) with chain rule for (s ↦ s - T)
    have htT_mem : t - T ∈ Set.Ioo (0 : ℝ) T_0 := ⟨by linarith, by linarith [ht.2]⟩
    have h_g_deriv : HasDerivAt (fun s => charX_g s (charX_prev T z, charV_prev T z))
        (charV_g (t - T) (charX_prev T z, charV_prev T z)) (t - T) :=
      (hg_boundaryX (charX_prev T z, charV_prev T z) (t - T)
          (Set.Ioo_subset_Icc_self htT_mem)).hasDerivAt
        (Icc_mem_nhds htT_mem.1 htT_mem.2)
    have h_sub : HasDerivAt (· - T) 1 t := (hasDerivAt_id' t).sub_const T
    have h_chain : HasDerivAt (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z))
        (charV_g (t - T) (charX_prev T z, charV_prev T z)) t := by
      have := HasDerivAt.scomp_of_eq t h_g_deriv h_sub rfl
      simpa [Function.comp_def, one_smul] using this
    have h_ev : (fun s => if s ≤ T then charX_prev s z
        else charX_g (s - T) (charX_prev T z, charV_prev T z)) =ᶠ[nhds t]
        (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z)) := by
      apply Filter.Eventually.mono (eventually_gt_nhds ht_le)
      intro s hs; simp [not_le.mpr hs]
    exact h_chain.congr_of_eventuallyEq h_ev

/-- `HasDerivAt` of the glued velocity flow at interior times of the extended
window, with the force term against the glued measure `f_next` (consumed only
through its value hypotheses).  Mirrors `vlasovGlue_flowX_hasDerivAt` with the
velocity projections and the marginal bridges. -/
private lemma vlasovGlue_flowV_hasDerivAt
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (f_prev g : ℝ → Measure (PhaseSpace d))
    (charX_prev charV_prev charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    {T T_0 : ℝ} (hT_pos : 0 < T) (hT_0_pos : 0 < T_0)
    (h_prev_flowV : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ z : PhaseSpace d,
        HasDerivAt (fun s => charV_prev s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (f_prev t))
              (charX_prev t z))) t)
    (h_prev_boundaryV : ∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
        HasDerivWithinAt (fun s => charV_prev s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (f_prev t)) (charX_prev t z)))
          (Set.Icc 0 T) t)
    (hg_boundaryV : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T_0,
        HasDerivWithinAt (fun s => charV_g s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (g t)) (charX_g t z)))
          (Set.Icc 0 T_0) t)
    (hg_init : g 0 = f_prev T)
    (hg_init_cond : ∀ z : PhaseSpace d, charX_g 0 z = z.1 ∧ charV_g 0 z = z.2)
    (f_next : ℝ → Measure (PhaseSpace d))
    (hf_next_le : ∀ s, s ≤ T → f_next s = f_prev s)
    (hf_next_gt : ∀ s, T < s → f_next s = g (s - T))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) (T + T_0)) (z : PhaseSpace d) :
    HasDerivAt (fun s => if s ≤ T then charV_prev s z
        else charV_g (s - T) (charX_prev T z, charV_prev T z))
      (-(convolveFunctionMeasure gradW (spatialMarginal (f_next t))
          (if t ≤ T then charX_prev t z
            else charX_g (t - T) (charX_prev T z, charV_prev T z)))) t := by
  by_cases ht_le : t ≤ T
  · simp only [ite_eq_left ht_le]
    -- Sub-case: t < T (strict interior) vs t = T (boundary)
    by_cases ht_lt : t < T
    · -- t < T strict: piecewise function = charV_prev · z near t
      have h_ev : (fun s => if s ≤ T then charV_prev s z
          else charV_g (s - T) (charX_prev T z, charV_prev T z)) =ᶠ[nhds t]
          (fun s => charV_prev s z) := by
        apply Filter.Eventually.mono (eventually_lt_nhds ht_lt)
        intro s hs; simp [le_of_lt hs]
      have h_fnext_t : f_next t = f_prev t := hf_next_le t ht_le
      have h_prev_deriv := h_prev_flowV t ⟨ht.1, ht_lt⟩ z
      have h_eq_marg : spatialMarginal (f_prev t) = spatialMarginal (f_next t) :=
        congrArg spatialMarginal h_fnext_t.symm
      simp only [h_eq_marg] at h_prev_deriv
      exact h_prev_deriv.congr_of_eventuallyEq h_ev
    · -- t = T: boundary HasDerivAt via HasDerivWithinAt.union (same as charX case)
      push Not at ht_lt
      have h_t_eq : t = T := le_antisymm ht_le ht_lt
      have hT_in : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
      have h_bV := h_prev_boundaryV z T hT_in
      have h0_T0_in : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T_0 := ⟨le_refl 0, hT_0_pos.le⟩
      have h_g_bV := hg_boundaryV (charX_prev T z, charV_prev T z) 0 h0_T0_in
      have h_nhd_L : Set.Icc 0 T ∈ nhdsWithin T (Set.Iic T) := Icc_mem_nhdsLE hT_pos
      have h_nhd_R : Set.Icc 0 T_0 ∈ nhdsWithin (0 : ℝ) (Set.Ici 0) :=
        Icc_mem_nhdsGE hT_0_pos
      -- Bridge f_prev T ↔ f_next T (for spatial marginal in goal vs h_bV)
      have hfnextT : f_next T = f_prev T := hf_next_le T (le_refl T)
      have hfnextT_spat : spatialMarginal (f_next T) = spatialMarginal (f_prev T) :=
        congrArg spatialMarginal hfnextT
      -- LEFT: HasDerivWithinAt charV_prev on Iic T at T
      have hV_Lic := h_bV.mono_of_mem_nhdsWithin h_nhd_L
      have hV_left : HasDerivWithinAt
          (fun s => if s ≤ T then charV_prev s z
            else charV_g (s - T) (charX_prev T z, charV_prev T z))
          (-(convolveFunctionMeasure gradW (spatialMarginal (f_next T))
              (charX_prev T z)))
          (Set.Iic T) T := by
        rw [hfnextT_spat]
        exact hV_Lic.congr_of_mem (fun s hs => by simp [Set.mem_Iic.mp hs])
          Set.self_mem_Iic
      -- RIGHT: chain rule from g's boundary at 0
      have hV_Ici0 := h_g_bV.mono_of_mem_nhdsWithin h_nhd_R
      have h_sub_R : HasDerivWithinAt (· - T) 1 (Set.Ici T) T :=
        ((hasDerivAt_id' T).sub_const T).hasDerivWithinAt
      have h_mapR : Set.MapsTo (· - T) (Set.Ici T) (Set.Ici 0) :=
        fun s hs => Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp hs])
      have h_chainV : HasDerivWithinAt
          (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z))
          (-(convolveFunctionMeasure gradW
            (spatialMarginal (g 0))
            (charX_g 0 (charX_prev T z, charV_prev T z))))
          (Set.Ici T) T := by
        have := HasDerivWithinAt.scomp_of_eq T hV_Ici0 h_sub_R h_mapR (sub_self T).symm
        simpa [Function.comp_def, one_smul] using this
      have hXg0_eq : charX_g 0 (charX_prev T z, charV_prev T z) = charX_prev T z :=
        (hg_init_cond (charX_prev T z, charV_prev T z)).1
      have hg0_spat : spatialMarginal (g 0) = spatialMarginal (f_prev T) :=
        congrArg spatialMarginal hg_init
      rw [hXg0_eq, hg0_spat, ← hfnextT_spat] at h_chainV
      have hV_right : HasDerivWithinAt
          (fun s => if s ≤ T then charV_prev s z
            else charV_g (s - T) (charX_prev T z, charV_prev T z))
          (-(convolveFunctionMeasure gradW (spatialMarginal (f_next T))
              (charX_prev T z)))
          (Set.Ici T) T :=
        h_chainV.congr_of_mem
          (fun s hs => by
            by_cases hle : s ≤ T
            · have heq : s = T := le_antisymm hle (Set.mem_Ici.mp hs)
              simp [heq, sub_self,
                (hg_init_cond (charX_prev T z, charV_prev T z)).2]
            · simp [hle])
          Set.self_mem_Ici
      have hV_union := hV_left.union hV_right
      rw [Set.Iic_union_Ici] at hV_union
      rw [h_t_eq]
      exact hV_union.hasDerivAt Filter.univ_mem
  · simp only [ite_eq_right ht_le]
    push Not at ht_le
    -- t > T: use hg_boundaryV at (t - T)
    have htT_mem : t - T ∈ Set.Ioo (0 : ℝ) T_0 := ⟨by linarith, by linarith [ht.2]⟩
    have h_g_deriv : HasDerivAt (fun s => charV_g s (charX_prev T z, charV_prev T z))
        (-(convolveFunctionMeasure gradW (spatialMarginal (g (t - T)))
            (charX_g (t - T) (charX_prev T z, charV_prev T z)))) (t - T) :=
      (hg_boundaryV (charX_prev T z, charV_prev T z) (t - T)
          (Set.Ioo_subset_Icc_self htT_mem)).hasDerivAt
        (Icc_mem_nhds htT_mem.1 htT_mem.2)
    have h_sub : HasDerivAt (· - T) 1 t := (hasDerivAt_id' t).sub_const T
    have h_chain : HasDerivAt (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z))
        (-(convolveFunctionMeasure gradW (spatialMarginal (g (t - T)))
            (charX_g (t - T) (charX_prev T z, charV_prev T z)))) t := by
      have := HasDerivAt.scomp_of_eq t h_g_deriv h_sub rfl
      simpa [Function.comp_def, one_smul] using this
    -- f_next t = g (t - T) when t > T
    have h_fnext_t : f_next t = g (t - T) := hf_next_gt t ht_le
    -- Rewrite derivative value: g (t-T) → f_next t
    rw [← congrArg spatialMarginal h_fnext_t] at h_chain
    have h_ev : (fun s => if s ≤ T then charV_prev s z
        else charV_g (s - T) (charX_prev T z, charV_prev T z)) =ᶠ[nhds t]
        (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z)) := by
      apply Filter.Eventually.mono (eventually_gt_nhds ht_le)
      intro s hs; simp [not_le.mpr hs]
    exact h_chain.congr_of_eventuallyEq h_ev

/-- The weak PDE holds at every time `t' ≠ T` near the seam: to the left the
glued solution is `f_prev` (use its weak PDE), to the right it is `g (·−T)`
(use `g`'s weak PDE with the shift chain rule). -/
private lemma vlasovGlue_diff_ne
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (f_prev g : ℝ → Measure (PhaseSpace d))
    {T T_0 : ℝ}
    (h_prev_vlasov : IsVlasovSolutionOn gradW f_prev T)
    (h_g_vlasov : IsVlasovSolutionOn gradW g T_0)
    (f_next : ℝ → Measure (PhaseSpace d))
    (hf_next_le : ∀ s, s ≤ T → f_next s = f_prev s)
    (hf_next_gt : ∀ s, T < s → f_next s = g (s - T))
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z : PhaseSpace d, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z : PhaseSpace d, gradVφ z = gradient (fun v => φ (z.1, v)) z.2) :
    ∀ t' ∈ Set.Ioo (0 : ℝ) (T + T_0), t' ≠ T → HasDerivAt
      (fun s => ∫ z, φ z ∂f_next s)
      ((∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
              @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (spatialMarginal (f_next t')) z.1)
                (gradVφ z)) ∂(f_next t')) + 0) t' := by
  intro t' ht' ht'_ne
  rcases lt_or_gt_of_ne ht'_ne with ht'_lt | ht'_gt
  · -- t' < T: use h_prev_vlasov + bridge f_next = f_prev on left of T
    have ht'_prev : t' ∈ Set.Ioo (0 : ℝ) T := ⟨ht'.1, ht'_lt⟩
    have h_ev : (fun s => ∫ z, φ z ∂f_next s) =ᶠ[nhds t']
        (fun s => ∫ z, φ z ∂f_prev s) := by
      apply Filter.Eventually.mono (eventually_lt_nhds ht'_lt)
      intro s hs; simp [hf_next_le s (le_of_lt hs)]
    have h_fnext_t' : f_next t' = f_prev t' := hf_next_le t' (le_of_lt ht'_lt)
    have h_deriv := h_prev_vlasov φ hφ_smooth hφ_compact gradXφ gradVφ
        hgradXφ hgradVφ t' ht'_prev
    rw [show (fun _ => (0 : ℝ)) t' = 0 from rfl, add_zero] at h_deriv
    have h_marg : spatialMarginal (f_next t') = spatialMarginal (f_prev t') :=
      congrArg spatialMarginal h_fnext_t'
    rw [add_zero, h_marg, h_fnext_t']
    exact h_deriv.congr_of_eventuallyEq h_ev
  · -- t' > T: use h_g_vlasov + chain rule + bridge f_next = g (·-T)
    have ht'_g : t' - T ∈ Set.Ioo (0 : ℝ) T_0 := ⟨by linarith, by linarith [ht'.2]⟩
    have h_ev : (fun s => ∫ z, φ z ∂f_next s) =ᶠ[nhds t']
        (fun s => ∫ z, φ z ∂g (s - T)) := by
      apply Filter.Eventually.mono (eventually_gt_nhds ht'_gt)
      intro s hs; simp [hf_next_gt s hs]
    have h_fnext_t' : f_next t' = g (t' - T) := hf_next_gt t' ht'_gt
    have h_g_deriv := h_g_vlasov φ hφ_smooth hφ_compact gradXφ gradVφ
        hgradXφ hgradVφ (t' - T) ht'_g
    rw [show (fun _ => (0 : ℝ)) (t' - T) = 0 from rfl, add_zero] at h_g_deriv
    have h_sub : HasDerivAt (· - T) 1 t' := (hasDerivAt_id' t').sub_const T
    have h_chain : HasDerivAt (fun s => ∫ z, φ z ∂g (s - T))
        (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
          @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (spatialMarginal (g (t' - T))) z.1)
            (gradVφ z)) ∂g (t' - T)) t' := by
      have := HasDerivAt.comp_of_eq t' h_g_deriv h_sub rfl
      simpa [Function.comp_def, mul_one] using this
    have h_marg : spatialMarginal (f_next t') = spatialMarginal (g (t' - T)) :=
      congrArg spatialMarginal h_fnext_t'
    rw [add_zero, h_marg, h_fnext_t']
    exact h_chain.congr_of_eventuallyEq h_ev

/-- LEFT seam continuity of the plain test-function integral at `T`: on `Iic T`
the glued solution agrees with `f_prev`; DCT with the constant dominator `Cφ`
against the window pushforward. -/
private lemma vlasovGlue_intCont_left
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    {T : ℝ} (hT_pos : 0 < T)
    (f_prev : ℝ → Measure (PhaseSpace d))
    (h_prev_init : f_prev 0 = f₀)
    (charX_prev charV_prev : ℝ → PhaseSpace d → PhysSpace d)
    (h_prev_push : ∀ t ∈ Set.Icc (0 : ℝ) T,
        f_prev t =
          Measure.map (fun z : PhaseSpace d => (charX_prev t z, charV_prev t z)) (f_prev 0))
    (h_prev_aemeas : ∀ s ∈ Set.Icc (0 : ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) (f_prev 0))
    (h_prev_boundary : ∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
        HasDerivWithinAt (fun s => charX_prev s z) (charV_prev t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV_prev s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (f_prev t)) (charX_prev t z)))
          (Set.Icc 0 T) t)
    (f_next : ℝ → Measure (PhaseSpace d))
    (hf_next_le : ∀ s, s ≤ T → f_next s = f_prev s)
    (φ : PhaseSpace d → ℝ) (hφ_cont : Continuous φ)
    (Cφ : ℝ) (hCφ : ∀ z : PhaseSpace d, ‖φ z‖ ≤ Cφ) :
    ContinuousWithinAt (fun s => ∫ z, φ z ∂f_next s) (Set.Iic T) T := by
  have h_nhd_L : Set.Icc (0 : ℝ) T ∈ nhdsWithin T (Set.Iic T) :=
    Icc_mem_nhdsLE hT_pos
  -- Equation: f_next = f_prev = pushforward of f₀ on Icc 0 T
  have h_eq_L : (fun s => ∫ z, φ z ∂f_next s) =ᶠ[nhdsWithin T (Set.Iic T)]
      (fun s => ∫ z, φ (charX_prev s z, charV_prev s z) ∂f₀) := by
    apply Filter.Eventually.mono h_nhd_L
    intro s hs
    change ∫ z, φ z ∂f_next s = ∫ z, φ (charX_prev s z, charV_prev s z) ∂f₀
    have h_fnext : f_next s = f_prev s := hf_next_le s hs.2
    have h_aemeas_f₀ : AEMeasurable
        (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) f₀ :=
      h_prev_init ▸ h_prev_aemeas s hs
    rw [h_fnext, h_prev_push s hs, h_prev_init]
    exact integral_map h_aemeas_f₀ hφ_cont.aestronglyMeasurable
  -- DCT for the pushforward-composed form
  have h_cont_pf : ContinuousWithinAt
      (fun s => ∫ z, φ (charX_prev s z, charV_prev s z) ∂f₀) (Set.Iic T) T := by
    apply continuousWithinAt_of_dominated (bound := fun _ => Cφ)
    · apply Filter.Eventually.mono h_nhd_L
      intro s hs
      have h_pair_aem : AEMeasurable
          (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) f₀ :=
        h_prev_init ▸ h_prev_aemeas s hs
      exact (hφ_cont.measurable.comp_aemeasurable h_pair_aem).aestronglyMeasurable
    · apply Filter.Eventually.mono h_nhd_L
      intro s _
      exact Filter.Eventually.of_forall fun z => hCφ _
    · exact integrable_const _
    · apply Filter.Eventually.of_forall
      intro z
      have hT_Icc : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
      have h_bX := (h_prev_boundary z T hT_Icc).1
      have h_bV := (h_prev_boundary z T hT_Icc).2
      have h_pair_Icc : ContinuousWithinAt
          (fun s => (charX_prev s z, charV_prev s z)) (Set.Icc 0 T) T :=
        h_bX.continuousWithinAt.prodMk h_bV.continuousWithinAt
      have h_pair_Iic : ContinuousWithinAt
          (fun s => (charX_prev s z, charV_prev s z)) (Set.Iic T) T :=
        h_pair_Icc.mono_of_mem_nhdsWithin h_nhd_L
      exact hφ_cont.continuousAt.comp_continuousWithinAt h_pair_Iic
  -- Value at T: bridge via the pushforward formula
  have h_val_T : (∫ z, φ z ∂f_next T)
      = ∫ z, φ (charX_prev T z, charV_prev T z) ∂f₀ := by
    have hT_Icc : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
    have h_fnext_T : f_next T = f_prev T := hf_next_le T (le_refl T)
    have h_aemeas_f₀_T : AEMeasurable
        (fun z : PhaseSpace d => (charX_prev T z, charV_prev T z)) f₀ :=
      h_prev_init ▸ h_prev_aemeas T hT_Icc
    rw [h_fnext_T, h_prev_push T hT_Icc, h_prev_init]
    exact integral_map h_aemeas_f₀_T hφ_cont.aestronglyMeasurable
  exact h_cont_pf.congr_of_eventuallyEq h_eq_L h_val_T

/-- RIGHT seam continuity of the plain test-function integral at `T`: on
`Ici T` the glued solution is the composed pushforward off `g`; DCT with the
constant dominator `Cφ`. -/
private lemma vlasovGlue_intCont_right
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    {T : ℝ} (hT_pos : 0 < T) {T_0 : ℝ} (hT_0_pos : 0 < T_0)
    (f_prev : ℝ → Measure (PhaseSpace d))
    (h_prev_init : f_prev 0 = f₀)
    (charX_prev charV_prev : ℝ → PhaseSpace d → PhysSpace d)
    (h_prev_push : ∀ t ∈ Set.Icc (0 : ℝ) T,
        f_prev t =
          Measure.map (fun z : PhaseSpace d => (charX_prev t z, charV_prev t z)) (f_prev 0))
    (h_prev_aemeas : ∀ s ∈ Set.Icc (0 : ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) (f_prev 0))
    (g : ℝ → Measure (PhaseSpace d))
    (charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    (hg_init : g 0 = f_prev T)
    (hg_push_ex : ∀ t ∈ Set.Icc (0 : ℝ) T_0,
        g t = Measure.map (fun z : PhaseSpace d => (charX_g t z, charV_g t z)) (g 0))
    (hg_aemeas_ex : ∀ s ∈ Set.Icc (0 : ℝ) T_0,
        AEMeasurable (fun z : PhaseSpace d => (charX_g s z, charV_g s z)) (g 0))
    (hg_boundary : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T_0,
        HasDerivWithinAt (fun s => charX_g s z) (charV_g t z) (Set.Icc 0 T_0) t ∧
        HasDerivWithinAt (fun s => charV_g s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (g t)) (charX_g t z)))
          (Set.Icc 0 T_0) t)
    (hg_init_cond : ∀ z : PhaseSpace d, charX_g 0 z = z.1 ∧ charV_g 0 z = z.2)
    (f_next : ℝ → Measure (PhaseSpace d))
    (hf_next_T : f_next T = f_prev T)
    (hf_next_gt : ∀ s, T < s → f_next s = g (s - T))
    (φ : PhaseSpace d → ℝ) (hφ_cont : Continuous φ)
    (Cφ : ℝ) (hCφ : ∀ z : PhaseSpace d, ‖φ z‖ ≤ Cφ) :
    ContinuousWithinAt (fun s => ∫ z, φ z ∂f_next s) (Set.Ici T) T := by
  have h_nhd_R : Set.Icc T (T + T_0) ∈ nhdsWithin T (Set.Ici T) :=
    Icc_mem_nhdsGE (by linarith : T < T + T_0)
  have hT_Icc : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
  have h_outer_aemeas : AEMeasurable
      (fun z : PhaseSpace d => (charX_prev T z, charV_prev T z)) f₀ :=
    h_prev_init ▸ h_prev_aemeas T hT_Icc
  -- Eventually-equal: f_next s = composed pushforward on Icc T (T+T_0)
  have h_eq_R : (fun s => ∫ z, φ z ∂f_next s) =ᶠ[nhdsWithin T (Set.Ici T)]
      (fun s => ∫ z, φ
        (charX_g (s - T) (charX_prev T z, charV_prev T z),
         charV_g (s - T) (charX_prev T z, charV_prev T z)) ∂f₀) := by
    apply Filter.Eventually.mono h_nhd_R
    intro s hs
    change ∫ z, φ z ∂f_next s = ∫ z, φ
        (charX_g (s - T) (charX_prev T z, charV_prev T z),
         charV_g (s - T) (charX_prev T z, charV_prev T z)) ∂f₀
    have hs_T : T ≤ s := hs.1
    have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
      ⟨by linarith, by linarith [hs.2]⟩
    by_cases hs_eq : s = T
    · -- s = T: f_next s = f_next T = f_prev T = (charX_prev T, charV_prev T)#f₀
      --   RHS at s = T uses hg_init_cond to collapse (charX_g 0, charV_g 0) = id
      have hs_T_zero : s - T = 0 := by rw [hs_eq]; exact sub_self T
      have h_fnext_s : f_next s = f_prev T := by
        rw [hs_eq]; exact hf_next_T
      rw [h_fnext_s, h_prev_push T hT_Icc, h_prev_init,
          integral_map h_outer_aemeas hφ_cont.aestronglyMeasurable]
      congr 1
      funext z
      rw [hs_T_zero, (hg_init_cond _).1, (hg_init_cond _).2]
    · -- s > T: f_next s = g (s - T) = composed pushforward
      have hs_gt : T < s := lt_of_le_of_ne hs_T (Ne.symm hs_eq)
      have h_fnext_s : f_next s = g (s - T) := hf_next_gt s hs_gt
      rw [h_fnext_s, hg_push_ex (s - T) hsT_Icc, hg_init,
          h_prev_push T hT_Icc, h_prev_init]
      have h_g_at_sT : AEMeasurable
          (fun z : PhaseSpace d => (charX_g (s - T) z, charV_g (s - T) z))
          (Measure.map (fun z : PhaseSpace d =>
            (charX_prev T z, charV_prev T z)) f₀) := by
        have := hg_aemeas_ex (s - T) hsT_Icc
        rw [hg_init, h_prev_push T hT_Icc, h_prev_init] at this
        exact this
      have h_comp_aem : AEMeasurable
          (fun z : PhaseSpace d =>
            (charX_g (s - T) (charX_prev T z, charV_prev T z),
             charV_g (s - T) (charX_prev T z, charV_prev T z))) f₀ :=
        h_g_at_sT.comp_aemeasurable h_outer_aemeas
      rw [AEMeasurable.map_map_of_aemeasurable h_g_at_sT h_outer_aemeas]
      exact integral_map h_comp_aem hφ_cont.aestronglyMeasurable
  -- DCT for the composed-pushforward form
  have h_cont_pf : ContinuousWithinAt
      (fun s => ∫ z, φ
        (charX_g (s - T) (charX_prev T z, charV_prev T z),
         charV_g (s - T) (charX_prev T z, charV_prev T z)) ∂f₀)
      (Set.Ici T) T := by
    apply continuousWithinAt_of_dominated (bound := fun _ => Cφ)
    · apply Filter.Eventually.mono h_nhd_R
      intro s hs
      have hsT_Icc : s - T ∈ Set.Icc (0 : ℝ) T_0 :=
        ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have h_g_at_sT : AEMeasurable
          (fun z : PhaseSpace d => (charX_g (s - T) z, charV_g (s - T) z))
          (Measure.map (fun z : PhaseSpace d =>
            (charX_prev T z, charV_prev T z)) f₀) := by
        have := hg_aemeas_ex (s - T) hsT_Icc
        rw [hg_init, h_prev_push T hT_Icc, h_prev_init] at this
        exact this
      have h_comp_aem : AEMeasurable
          (fun z : PhaseSpace d =>
            (charX_g (s - T) (charX_prev T z, charV_prev T z),
             charV_g (s - T) (charX_prev T z, charV_prev T z))) f₀ :=
        h_g_at_sT.comp_aemeasurable h_outer_aemeas
      exact (hφ_cont.measurable.comp_aemeasurable h_comp_aem).aestronglyMeasurable
    · apply Filter.Eventually.mono h_nhd_R
      intro s _
      exact Filter.Eventually.of_forall fun z => hCφ _
    · exact integrable_const _
    · -- Pointwise continuity: chain rule for (· - T) at T with charX_g/charV_g at 0
      apply Filter.Eventually.of_forall
      intro z
      have h0_Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T_0 := ⟨le_refl 0, hT_0_pos.le⟩
      have h_g_bX := (hg_boundary (charX_prev T z, charV_prev T z) 0 h0_Icc).1
      have h_g_bV := (hg_boundary (charX_prev T z, charV_prev T z) 0 h0_Icc).2
      have h_nhdsW_0 : Set.Icc (0 : ℝ) T_0 ∈ nhdsWithin 0 (Set.Ici 0) :=
        Icc_mem_nhdsGE hT_0_pos
      have h_g_bX_cont : ContinuousWithinAt
          (fun s' => charX_g s' (charX_prev T z, charV_prev T z))
          (Set.Ici 0) 0 :=
        h_g_bX.continuousWithinAt.mono_of_mem_nhdsWithin h_nhdsW_0
      have h_g_bV_cont : ContinuousWithinAt
          (fun s' => charV_g s' (charX_prev T z, charV_prev T z))
          (Set.Ici 0) 0 :=
        h_g_bV.continuousWithinAt.mono_of_mem_nhdsWithin h_nhdsW_0
      have h_sub_cont : ContinuousWithinAt (fun s : ℝ => s - T) (Set.Ici T) T :=
        ((continuous_id.sub continuous_const).continuousAt).continuousWithinAt
      have h_sub_maps : Set.MapsTo (fun s : ℝ => s - T) (Set.Ici T) (Set.Ici 0) :=
        fun s hs => Set.mem_Ici.mpr (by linarith [Set.mem_Ici.mp hs])
      have h_chainX : ContinuousWithinAt
          (fun s => charX_g (s - T) (charX_prev T z, charV_prev T z))
          (Set.Ici T) T :=
        ContinuousWithinAt.comp_of_eq h_g_bX_cont h_sub_cont h_sub_maps (sub_self T)
      have h_chainV : ContinuousWithinAt
          (fun s => charV_g (s - T) (charX_prev T z, charV_prev T z))
          (Set.Ici T) T :=
        ContinuousWithinAt.comp_of_eq h_g_bV_cont h_sub_cont h_sub_maps (sub_self T)
      have h_pair : ContinuousWithinAt
          (fun s => (charX_g (s - T) (charX_prev T z, charV_prev T z),
                     charV_g (s - T) (charX_prev T z, charV_prev T z)))
          (Set.Ici T) T :=
        h_chainX.prodMk h_chainV
      exact hφ_cont.continuousAt.comp_continuousWithinAt h_pair
  -- Value at T: integrate the s = T case
  have h_val_T : (∫ z, φ z ∂f_next T) = ∫ z, φ
      (charX_g (T - T) (charX_prev T z, charV_prev T z),
       charV_g (T - T) (charX_prev T z, charV_prev T z)) ∂f₀ := by
    rw [hf_next_T, h_prev_push T hT_Icc, h_prev_init,
        integral_map h_outer_aemeas hφ_cont.aestronglyMeasurable]
    congr 1; funext z
    rw [show T - T = (0 : ℝ) from sub_self T,
        (hg_init_cond _).1, (hg_init_cond _).2]
  exact h_cont_pf.congr_of_eventuallyEq h_eq_R h_val_T

/-- Pushforward equation for the glued solution against the glued piecewise
flow, on the extended window.  Serves both `IsLagrangianVlasovSolutionOn`'s
pushforward conjunct and the explicit conjunct (v). -/
private lemma vlasovGlue_pushforward_eq
    {d : ℕ} [NeZero d]
    (f_prev g : ℝ → Measure (PhaseSpace d))
    (charX_prev charV_prev charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    {T T_0 : ℝ} (hT_pos : 0 < T)
    (h_prev_push : ∀ t ∈ Set.Icc (0 : ℝ) T,
        f_prev t =
          Measure.map (fun z : PhaseSpace d => (charX_prev t z, charV_prev t z)) (f_prev 0))
    (h_prev_aemeas : ∀ s ∈ Set.Icc (0 : ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) (f_prev 0))
    (hg_init : g 0 = f_prev T)
    (hg_push_ex : ∀ t ∈ Set.Icc (0 : ℝ) T_0,
        g t = Measure.map (fun z : PhaseSpace d => (charX_g t z, charV_g t z)) (g 0))
    (hg_aemeas_ex : ∀ s ∈ Set.Icc (0 : ℝ) T_0,
        AEMeasurable (fun z : PhaseSpace d => (charX_g s z, charV_g s z)) (g 0))
    (f_next : ℝ → Measure (PhaseSpace d))
    (hf_next_le : ∀ s, s ≤ T → f_next s = f_prev s)
    (hf_next_gt : ∀ s, T < s → f_next s = g (s - T))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (T + T_0)) :
    f_next t = Measure.map (fun z : PhaseSpace d =>
      ((if t ≤ T then charX_prev t z
         else charX_g (t - T) (charX_prev T z, charV_prev T z)),
       (if t ≤ T then charV_prev t z
         else charV_g (t - T) (charX_prev T z, charV_prev T z)))) (f_next 0) := by
  rw [hf_next_le 0 hT_pos.le]
  by_cases ht_le : t ≤ T
  · simp only [ite_eq_left ht_le]
    rw [hf_next_le t ht_le]
    exact h_prev_push t ⟨ht.1, ht_le⟩
  · simp only [ite_eq_right ht_le]
    push Not at ht_le
    rw [hf_next_gt t ht_le]
    have hT_mem : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
    have htT_mem : t - T ∈ Set.Icc (0 : ℝ) T_0 := ⟨by linarith, by linarith [ht.2]⟩
    rw [hg_push_ex (t - T) htT_mem, hg_init, h_prev_push T hT_mem]
    have h_prev_T_aemeas := h_prev_aemeas T hT_mem
    have h_g_at_tT := hg_aemeas_ex (t - T) htT_mem
    rw [hg_init, h_prev_push T hT_mem] at h_g_at_tT
    rw [AEMeasurable.map_map_of_aemeasurable h_g_at_tT h_prev_T_aemeas]
    rfl

/-- AEMeasurability of the glued piecewise flow against `f_next 0` on the
extended window.  Serves both `IsLagrangianVlasovSolutionOn`'s conjunct and
the explicit conjunct (vi). -/
private lemma vlasovGlue_flow_aemeasurable
    {d : ℕ} [NeZero d]
    (f_prev g : ℝ → Measure (PhaseSpace d))
    (charX_prev charV_prev charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    {T T_0 : ℝ} (hT_pos : 0 < T)
    (h_prev_push : ∀ t ∈ Set.Icc (0 : ℝ) T,
        f_prev t =
          Measure.map (fun z : PhaseSpace d => (charX_prev t z, charV_prev t z)) (f_prev 0))
    (h_prev_aemeas : ∀ s ∈ Set.Icc (0 : ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) (f_prev 0))
    (hg_init : g 0 = f_prev T)
    (hg_aemeas_ex : ∀ s ∈ Set.Icc (0 : ℝ) T_0,
        AEMeasurable (fun z : PhaseSpace d => (charX_g s z, charV_g s z)) (g 0))
    (f_next : ℝ → Measure (PhaseSpace d))
    (hf_next_le : ∀ s, s ≤ T → f_next s = f_prev s)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) (T + T_0)) :
    AEMeasurable (fun z : PhaseSpace d =>
      ((if s ≤ T then charX_prev s z
         else charX_g (s - T) (charX_prev T z, charV_prev T z)),
       (if s ≤ T then charV_prev s z
         else charV_g (s - T) (charX_prev T z, charV_prev T z)))) (f_next 0) := by
  rw [hf_next_le 0 hT_pos.le]
  by_cases hs_le : s ≤ T
  · simp only [ite_eq_left hs_le]
    exact h_prev_aemeas s ⟨hs.1, hs_le⟩
  · simp only [ite_eq_right hs_le]
    push Not at hs_le
    have hT_mem : T ∈ Set.Icc (0 : ℝ) T := ⟨hT_pos.le, le_refl T⟩
    have hsT_mem : s - T ∈ Set.Icc (0 : ℝ) T_0 := ⟨by linarith, by linarith [hs.2]⟩
    have h_g_at_sT := hg_aemeas_ex (s - T) hsT_mem
    rw [hg_init, h_prev_push T hT_mem] at h_g_at_sT
    exact h_g_at_sT.comp_aemeasurable (h_prev_aemeas T hT_mem)

/-- Finite first moment of the glued solution on the extended window,
piecewise from the two window moment hypotheses. -/
private lemma vlasovGlue_moment
    {d : ℕ} [NeZero d]
    (f_prev g : ℝ → Measure (PhaseSpace d))
    {T T_0 : ℝ}
    (h_prev_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f_prev t))
    (hg_mom : ∀ t ∈ Set.Icc (0 : ℝ) T_0, HasFiniteFirstMoment (g t))
    (f_next : ℝ → Measure (PhaseSpace d))
    (hf_next_le : ∀ s, s ≤ T → f_next s = f_prev s)
    (hf_next_gt : ∀ s, T < s → f_next s = g (s - T)) :
    ∀ t ∈ Set.Icc (0 : ℝ) (T + T_0), HasFiniteFirstMoment (f_next t) := by
  intro t ht
  by_cases ht_le : t ≤ T
  · rw [hf_next_le t ht_le]
    exact h_prev_mom t ⟨ht.1, ht_le⟩
  · push Not at ht_le
    rw [hf_next_gt t ht_le]
    exact hg_mom (t - T) ⟨by linarith, by linarith [ht.2]⟩

/-- FLAT uniform first-moment bound on the glued solution's spatial marginal:
`max` of the two window envelopes, no cross-term. -/
private lemma vlasovGlue_moment_flat
    {d : ℕ} [NeZero d]
    (f_prev g : ℝ → Measure (PhaseSpace d))
    {T T_0 : ℝ}
    (hM_prev : ∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f_prev t)) ≤ M)
    (hg_mom_unif : ∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T_0, ∫ y, ‖y‖ ∂(spatialMarginal (g t)) ≤ M)
    (f_next : ℝ → Measure (PhaseSpace d))
    (hf_next_le : ∀ s, s ≤ T → f_next s = f_prev s)
    (hf_next_gt : ∀ s, T < s → f_next s = g (s - T)) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ t ∈ Set.Icc (0 : ℝ) (T + T_0),
        ∫ y, ‖y‖ ∂(spatialMarginal (f_next t)) ≤ M := by
  obtain ⟨M_prev, hM_prev_nn, hM_prev_bd⟩ := hM_prev
  obtain ⟨M_g, _hM_g_nn, hM_g_bd⟩ := hg_mom_unif
  refine ⟨max M_prev M_g, le_trans hM_prev_nn (le_max_left _ _), fun t ht => ?_⟩
  by_cases ht_le : t ≤ T
  · rw [hf_next_le t ht_le]
    exact le_trans (hM_prev_bd t ⟨ht.1, ht_le⟩) (le_max_left _ _)
  · push Not at ht_le
    rw [hf_next_gt t ht_le]
    exact le_trans (hM_g_bd (t - T) ⟨by linarith, by linarith [ht.2]⟩) (le_max_right _ _)

/-- **One-window glue step.**

Given a solution `f_prev : ℝ → Measure (PhaseSpace d)` on `[0, T]`
satisfying the local-existence conjuncts (initial condition + finite first
moment + `IsLagrangianVlasovSolutionOn`), and a window length `T_0`
satisfying the smallness constraints `LocalSmallnessPLBuffer L T_0` +
`LocalSmallnessContraction L T_0`, produces a glued solution
`f_next : ℝ → Measure (PhaseSpace d)` on `[0, T + T_0]` that agrees with
`f_prev` on `[0, T]`.

**Proof strategy**:

1. Shift the initial condition: apply `vlasovWellPosedness_local` to
   `f_prev T` (which has finite first moment by `h_prev_mom T`) with
   window length `T_0`.  Gives a solution `g : ℝ → Measure (PhaseSpace d)`
   on `[0, T_0]` with `g 0 = f_prev T`.

2. Glue: define `f_next t := if t ≤ T then f_prev t else g (t - T)`.
   Agreement at `t = T` is by `g 0 = f_prev T`.

3. Verify the four output conjuncts:
   - Initial: `f_next 0 = f_prev 0 = f₀`.
   - Moment: piecewise from `h_prev_mom` and `g`'s moment bound.
   - `IsLagrangianVlasovSolutionOn` on `[0, T + T_0]`:
     * `IsVlasovSolutionOn`: weak PDE on `Ioo 0 (T + T_0)` — split at `T`,
       use `h_prev_lag.1` for `Ioo 0 T` part and `g`'s for `Ioo T (T+T_0)`,
       continuity at `T` from the integral being continuous.
     * Flow: glue the per-window flows via standard ODE composition
       (charX_next(t, z) := if t ≤ T then charX_prev(t, z) else
       charX_g(t - T, (charX_prev(T, z), charV_prev(T, z)))).
     * Pushforward equation: holds piecewise.
     * AEMeasurable witness: composition of AEMeasurable maps. -/
theorem vlasovWellPosedness_glue
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d))
    (hf₀ : HasFiniteFirstMoment f₀)
    {T : ℝ} (hT_pos : 0 < T)
    (f_prev : ℝ → Measure (PhaseSpace d))
    (h_prev_init : f_prev 0 = f₀)
    (h_prev_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f_prev t))
    -- FLAT (window-constant) uniform first-moment bound on f_prev's spatial marginal.
    (hM_prev : ∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f_prev t)) ≤ M)
    -- Explicit flow witnesses for f_prev (avoids witness-identity issues with
    -- IsLagrangianVlasovSolutionOn)
    (charX_prev charV_prev : ℝ → PhaseSpace d → PhysSpace d)
    (h_prev_vlasov : IsVlasovSolutionOn gradW f_prev T)
    (h_prev_flow : IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f_prev t))
        charX_prev charV_prev (Set.Ioo 0 T) Set.univ)
    (h_prev_push : ∀ t ∈ Set.Icc (0 : ℝ) T,
        f_prev t =
          Measure.map (fun z : PhaseSpace d => (charX_prev t z, charV_prev t z)) (f_prev 0))
    (h_prev_aemeas : ∀ s ∈ Set.Icc (0 : ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX_prev s z, charV_prev s z)) (f_prev 0))
    (h_prev_boundary : ∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
        HasDerivWithinAt (fun s => charX_prev s z) (charV_prev t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV_prev s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (f_prev t)) (charX_prev t z)))
          (Set.Icc 0 T) t)
    (h_prev_ic : ∀ z : PhaseSpace d, charX_prev 0 z = z.1 ∧ charV_prev 0 z = z.2)
    {T_0 : ℝ} (hT_0_pos : 0 < T_0)
    (hT_0_small_PL : LocalSmallnessPLBuffer L T_0)
    (hT_0_small_con : LocalSmallnessContraction L T_0)
    (hT_0_small_B : (L : ℝ) / (1 + (L : ℝ)) * (Real.exp ((1 + (L : ℝ)) * T_0) - 1) < 1) :
    ∃ (f_next : ℝ → Measure (PhaseSpace d))
      (charX_next charV_next : ℝ → PhaseSpace d → PhysSpace d),
      (∀ t ∈ Set.Icc (0 : ℝ) T, f_next t = f_prev t) ∧
      f_next 0 = f₀ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) (T + T_0), HasFiniteFirstMoment (f_next t)) ∧
      -- FLAT (window-constant) uniform first-moment bound on the spatial marginal.
      (∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ Set.Icc (0 : ℝ) (T + T_0), ∫ y, ‖y‖ ∂(spatialMarginal (f_next t)) ≤ M) ∧
      IsLagrangianVlasovSolutionOn gradW f_next (T + T_0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) (T + T_0),
          f_next t =
            Measure.map (fun z : PhaseSpace d => (charX_next t z, charV_next t z)) (f_next 0)) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) (T + T_0),
          AEMeasurable (fun z : PhaseSpace d => (charX_next s z, charV_next s z)) (f_next 0)) ∧
      (∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) (T + T_0) →
          HasDerivWithinAt (fun s => charX_next s z) (charV_next t z) (Set.Icc 0 (T + T_0)) t ∧
          HasDerivWithinAt (fun s => charV_next s z)
            (-(convolveFunctionMeasure gradW (spatialMarginal (f_next t)) (charX_next t z)))
            (Set.Icc 0 (T + T_0)) t) ∧
      (∀ z : PhaseSpace d, charX_next 0 z = z.1 ∧ charV_next 0 z = z.2) := by
  -- The gluing closes the boundary at `t = T` by combining the boundary
  -- regularity bundles from both windows: HasDerivWithinAt at T from the
  -- LEFT (via f_prev's boundary bundle at endpoint T) and HasDerivWithinAt
  -- at 0 from the RIGHT (via g's boundary bundle at endpoint 0), giving
  -- HasDerivAt at t = T in `f_next`'s frame.
  --
  -- Step 1: invoke vlasovWellPosedness_local on f_prev T to get g on [0, T_0]
  have h_prev_T_mom : HasFiniteFirstMoment (f_prev T) :=
    h_prev_mom T (Set.right_mem_Icc.mpr hT_pos.le)
  obtain ⟨g, charX_g, charV_g, hg_init, hg_mom, hg_mom_unif, hg_lag, hg_push_ex, hg_aemeas_ex,
          hg_boundary, hg_init_cond⟩ :=
    vlasovWellPosedness_local W gradW hgradW L hL
      (f_prev T) h_prev_T_mom hT_0_pos hT_0_small_PL hT_0_small_con hT_0_small_B
  -- Step 2: define the glued solution piecewise
  let f_next : ℝ → Measure (PhaseSpace d) :=
    fun t => if t ≤ T then f_prev t else g (t - T)
  -- Step 3: verify the output conjuncts
  -- Piecewise flow: for t ≤ T use charX_prev, for t > T compose with charX_g shifted
  let charX_next : ℝ → PhaseSpace d → PhysSpace d := fun t z =>
    if t ≤ T then charX_prev t z else charX_g (t - T) (charX_prev T z, charV_prev T z)
  let charV_next : ℝ → PhaseSpace d → PhysSpace d := fun t z =>
    if t ≤ T then charV_prev t z else charV_g (t - T) (charX_prev T z, charV_prev T z)
  have h_g_vlasov : IsVlasovSolutionOn gradW g T_0 := hg_lag.1
  refine ⟨f_next, charX_next, charV_next, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Conjunct (i): agreement on [0, T]
    intro t ht
    simp only [f_next]
    have ht_le : t ≤ T := ht.2
    simp [ht_le]
  · -- Conjunct (ii): initial condition f_next 0 = f₀
    simp only [f_next]
    have h0_le : (0 : ℝ) ≤ T := hT_pos.le
    simp [h0_le, h_prev_init]
  · -- Conjunct (iii): HasFiniteFirstMoment on [0, T + T_0] (hoisted helper)
    exact vlasovGlue_moment f_prev g h_prev_mom hg_mom f_next
      (fun s hs => ite_eq_left hs) (fun s hs => ite_eq_right (not_le.mpr hs))
  · -- Conjunct (iii′): FLAT uniform first-moment bound (hoisted helper)
    exact vlasovGlue_moment_flat f_prev g hM_prev hg_mom_unif f_next
      (fun s hs => ite_eq_left hs) (fun s hs => ite_eq_right (not_le.mpr hs))
  · -- Conjunct (iv): IsLagrangianVlasovSolutionOn gradW f_next (T + T_0)
    refine ⟨?_, charX_next, charV_next, ?_, ?_, ?_⟩
    · -- IsVlasovSolutionOn gradW f_next (T + T_0)
      -- Sub-sorry: PDE gluing — on Ioo 0 (T + T_0), piecewise from h_prev_vlasov and h_g_vlasov
      -- Sub-sorry (a): IsVlasovSolutionOn for the glued solution.
      -- Strategy: for t ∈ Ioo 0 T use h_prev_vlasov (with f_next = f_prev near t);
      -- for t ∈ Ioo T (T+T_0) use h_g_vlasov shifted (f_next t = g (t-T));
      -- at t = T use continuity of t ↦ ∫ φ ∂f_next t from both sides.
      have h_vlasov_glue : IsVlasovSolutionOn gradW f_next (T + T_0) := by
        intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ t ht
        -- Off-seam weak PDE at every t' ≠ T (hoisted helper); the two strict
        -- branches consume it directly, the seam derives its eventual form.
        have h_diff_ne := vlasovGlue_diff_ne gradW f_prev g
          h_prev_vlasov h_g_vlasov f_next (fun s hs => ite_eq_left hs)
          (fun s hs => ite_eq_right (not_le.mpr hs)) φ hφ_smooth hφ_compact
          gradXφ gradVφ hgradXφ hgradVφ
        by_cases ht_lt : t < T
        · -- t ∈ Ioo 0 T: off-seam weak PDE
          rw [show (fun _ => (0 : ℝ)) t = 0 from rfl]
          exact h_diff_ne t ht (ne_of_lt ht_lt)
        · by_cases ht_gt : T < t
          · -- t ∈ Ioo T (T + T_0): off-seam weak PDE
            rw [show (fun _ => (0 : ℝ)) t = 0 from rfl]
            exact h_diff_ne t ht (ne_of_gt ht_gt)
          · -- t = T: boundary case via `hasDerivAt_of_hasDerivAt_of_ne_in_nhds`.
            -- Three sub-arguments: (1) HasDerivAt at every nearby t' ≠ T from the
            -- off-seam helper; (2) ContinuousAt of the integral function at T;
            -- (3) ContinuousAt of the derivative function at T.
            push Not at ht_gt
            have h_t_eq : t = T := le_antisymm ht_gt (not_lt.mp ht_lt)
            -- Step 1: HasDerivAt at every nearby t' ≠ T, in eventual form.
            have h_diff_ne_ev : ∀ᶠ t' in nhds T, t' ≠ T → HasDerivAt
                (fun s => ∫ z, φ z ∂f_next s)
                ((∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                        @inner ℝ (PhysSpace d) _
                          (convolveFunctionMeasure gradW (spatialMarginal (f_next t')) z.1)
                          (gradVφ z)) ∂(f_next t')) + 0) t' := by
              have hU_mem : Set.Ioo (0 : ℝ) (T + T_0) ∈ nhds T :=
                Ioo_mem_nhds hT_pos (by linarith)
              exact Filter.Eventually.mono hU_mem (fun t' ht' => h_diff_ne t' ht')
            -- Step 2: ContinuousAt of integral function at T.
            -- Decomposed into LEFT (Iic T) + RIGHT (Ici T) closes, joined via
            -- `Iic_union_Ici = univ`.
            have hφ_cont : Continuous φ := hφ_smooth.continuous
            obtain ⟨Cφ, hCφ⟩ := hφ_cont.bounded_above_of_compact_support hφ_compact
            obtain ⟨hf₀_prob, hf₀_int⟩ := hf₀
            have : IsProbabilityMeasure f₀ := hf₀_prob
            -- LEFT side: substantive close via DCT on f_prev's pushforward.
            have h_cont_f_left : ContinuousWithinAt (fun s => ∫ z, φ z ∂f_next s)
                (Set.Iic T) T :=
              vlasovGlue_intCont_left gradW f₀ hT_pos f_prev h_prev_init
                charX_prev charV_prev h_prev_push h_prev_aemeas h_prev_boundary
                f_next (fun s hs => ite_eq_left hs) φ hφ_cont Cφ hCφ
            -- RIGHT side: substantive close via DCT on the composed pushforward
            -- (charX_g (s-T), charV_g (s-T)) ∘ (charX_prev T, charV_prev T).
            -- At s = T, hg_init_cond bridges (charX_g 0, charV_g 0) = id, matching f_prev T.
            have h_cont_f_right : ContinuousWithinAt (fun s => ∫ z, φ z ∂f_next s)
                (Set.Ici T) T :=
              vlasovGlue_intCont_right gradW f₀ hT_pos hT_0_pos f_prev h_prev_init
                charX_prev charV_prev h_prev_push h_prev_aemeas g charX_g charV_g
                hg_init hg_push_ex hg_aemeas_ex hg_boundary hg_init_cond
                f_next (ite_eq_left (le_refl T)) (fun s hs => ite_eq_right (not_le.mpr hs))
                φ hφ_cont Cφ hCφ
            -- Combine via union
            have h_cont_f : ContinuousAt (fun s => ∫ z, φ z ∂f_next s) T := by
              have h_union := h_cont_f_left.union h_cont_f_right
              rw [Set.Iic_union_Ici] at h_union
              exact h_union.continuousAt Filter.univ_mem
            -- Step 3: ContinuousAt of the derivative functional at the seam T.
            -- Mirror `h_cont_f`'s one-sided-union structure (Iic/Ici +
            -- `Set.Iic_union_Ici`).  Each side discharges by push-to-f₀ +
            -- DCT; the integrand's force term carries
            -- `convolveFunctionMeasure gradW (spatialMarginal (f_next ·)) z.1`, whose
            -- seam continuity closes from PROVEN TOOLS via the pushforward
            -- representation: `f_prev`/`g` are flow-pushforwards of `f₀`, so the
            -- convolution rewrites by `integral_map` to a fixed-`f₀` integral, closed
            -- by the inner kernels `flowConv_continuousWithinAt_{Iic,Ici}_seam`
            -- (Piece-A-dominated DCT).  LEFT uses `spatialMarginal (f_prev ·)`,
            -- RIGHT the composed flow off `g`.
            have h_cont_g : ContinuousAt (fun t' =>
                (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                        @inner ℝ (PhysSpace d) _
                          (convolveFunctionMeasure gradW (spatialMarginal (f_next t')) z.1)
                          (gradVφ z)) ∂(f_next t')) + 0) T := by
              simp only [add_zero]
              -- LEFT side (s ≤ T): f_next = f_prev = pushforward of f₀; force term
              -- uses `spatialMarginal (f_prev ·)`.  Discharge: push-to-f₀ + DCT.
              have h_left : ContinuousWithinAt
                  (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                          @inner ℝ (PhysSpace d) _
                            (convolveFunctionMeasure gradW (spatialMarginal (f_next s)) z.1)
                            (gradVφ z)) ∂(f_next s)) (Set.Iic T) T :=
                vlasovGlue_seam_contLeft gradW L hL f₀ hf₀_int hT_pos f_prev h_prev_init
                  h_prev_mom hM_prev charX_prev charV_prev h_prev_push h_prev_aemeas
                  h_prev_boundary h_prev_ic f_next (fun s hs => ite_eq_left hs)
                  φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ
              -- RIGHT side (s ≥ T): f_next = g (·−T) = composed pushforward; symmetric
              -- to `h_left`.  The flow is the COMPOSED phase-space flow
              -- `Φ_s z = (charX_g (s−T) (charX_prev T z, charV_prev T z),
              --           charV_g (s−T) (charX_prev T z, charV_prev T z))`, and the
              -- position part `Z_s z = charX_g (s−T) (charX_prev T z, charV_prev T z)`
              -- is what the force-term convolution sees.  Pushforward, AEMeasurability,
              -- and seam continuity are copied/adapted from the PROVEN
              -- `h_cont_f_right` (composed-pushforward machinery); the growth bound is
              -- the composed Piece A (g over [0,T_0] ∘ prev at T); the force-term seam
              -- continuity uses the `Ici` sibling kernel `flowConv_continuousWithinAt_Ici_seam`.
              have h_right : ContinuousWithinAt
                  (fun s => ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
                          @inner ℝ (PhysSpace d) _
                            (convolveFunctionMeasure gradW (spatialMarginal (f_next s)) z.1)
                            (gradVφ z)) ∂(f_next s)) (Set.Ici T) T :=
                vlasovGlue_seam_contRight gradW L hL f₀ hf₀_int hT_pos hT_0_pos
                  f_prev h_prev_init h_prev_mom hM_prev charX_prev charV_prev
                  h_prev_push h_prev_aemeas h_prev_boundary h_prev_ic
                  g charX_g charV_g hg_init hg_mom hg_mom_unif hg_push_ex
                  hg_aemeas_ex hg_boundary hg_init_cond f_next
                  (ite_eq_left (le_refl T)) (fun s hs => ite_eq_right (not_le.mpr hs))
                  φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ
              have h_union := h_left.union h_right
              rw [Set.Iic_union_Ici] at h_union
              exact h_union.continuousAt Filter.univ_mem
            -- Step 4: Apply the localized helper.
            rw [h_t_eq]
            exact hasDerivAt_of_hasDerivAt_of_ne_in_nhds h_diff_ne_ev h_cont_f h_cont_g
      exact h_vlasov_glue
    · -- IsCharacteristicFlowOn for the glued flow
      -- Sub-sorry: flow initial condition + HasDerivAt for piecewise flow
      have h_flow_glue : IsCharacteristicFlowOn gradW
          (fun t => spatialMarginal (f_next t)) charX_next charV_next
          (Set.Ioo 0 (T + T_0)) Set.univ := by
        refine ⟨?_, ?_, ?_⟩
        · -- Initial condition: charX_next 0 z = z.1 ∧ charV_next 0 z = z.2
          intro z _
          simp only [charX_next, charV_next, ite_eq_left hT_pos.le]
          exact h_prev_flow.1 z (Set.mem_univ z)
        · -- HasDerivAt charX_next at t for t ∈ Ioo 0 (T + T_0) (hoisted helper)
          intro t ht z _
          simp only [charX_next, charV_next]
          exact vlasovGlue_flowX_hasDerivAt charX_prev charV_prev charX_g charV_g
            hT_pos hT_0_pos
            (fun t' ht' z' => h_prev_flow.2.1 t' ht' z' (Set.mem_univ z'))
            (fun z' t' ht' => (h_prev_boundary z' t' ht').1)
            (fun z' t' ht' => (hg_boundary z' t' ht').1)
            hg_init_cond t ht z
        · -- HasDerivAt charV_next at t for t ∈ Ioo 0 (T + T_0) (hoisted helper)
          intro t ht z _
          simp only [charX_next, charV_next]
          exact vlasovGlue_flowV_hasDerivAt gradW f_prev g charX_prev charV_prev
            charX_g charV_g hT_pos hT_0_pos
            (fun t' ht' z' => h_prev_flow.2.2 t' ht' z' (Set.mem_univ z'))
            (fun z' t' ht' => (h_prev_boundary z' t' ht').2)
            (fun z' t' ht' => (hg_boundary z' t' ht').2)
            hg_init hg_init_cond f_next (fun s hs => ite_eq_left hs)
            (fun s hs => ite_eq_right (not_le.mpr hs)) t ht z
      exact h_flow_glue
    · -- Pushforward equation for f_next on Icc 0 (T + T_0) (hoisted helper)
      intro t ht
      simp only [charX_next, charV_next]
      exact vlasovGlue_pushforward_eq f_prev g charX_prev charV_prev charX_g charV_g
        hT_pos h_prev_push h_prev_aemeas hg_init hg_push_ex hg_aemeas_ex f_next
        (fun s hs => ite_eq_left hs) (fun s hs => ite_eq_right (not_le.mpr hs)) t ht
    · -- AEMeasurability ∧ boundary ContinuousOn on Icc 0 (T + T_0).
      refine ⟨?_, ?_⟩
      · -- AEMeasurability of the glued flow (hoisted helper).
        intro s hs
        simp only [charX_next, charV_next]
        exact vlasovGlue_flow_aemeasurable f_prev g charX_prev charV_prev
          charX_g charV_g hT_pos h_prev_push h_prev_aemeas hg_init hg_aemeas_ex
          f_next (fun s' hs' => ite_eq_left hs') s hs
      · -- Boundary ContinuousOn on Icc 0 (T + T_0): project the boundary bundle.
        intro z s hs
        exact ((vlasovWellPosedness_glue_boundary gradW hT_pos hT_0_pos f_prev g f_next
          charX_prev charV_prev charX_g charV_g charX_next charV_next rfl rfl rfl
          h_prev_boundary hg_boundary hg_init hg_init_cond z s hs).1.continuousWithinAt.prodMk
          (vlasovWellPosedness_glue_boundary gradW hT_pos hT_0_pos f_prev g f_next
            charX_prev charV_prev charX_g charV_g charX_next charV_next rfl rfl rfl
            h_prev_boundary hg_boundary hg_init hg_init_cond z s hs).2.continuousWithinAt)
  · -- Conjunct (v): explicit pushforward for charX_next charV_next (hoisted helper)
    intro t ht
    simp only [charX_next, charV_next]
    exact vlasovGlue_pushforward_eq f_prev g charX_prev charV_prev charX_g charV_g
      hT_pos h_prev_push h_prev_aemeas hg_init hg_push_ex hg_aemeas_ex f_next
      (fun s hs => ite_eq_left hs) (fun s hs => ite_eq_right (not_le.mpr hs)) t ht
  · -- Conjunct (vi): AEMeasurable for charX_next charV_next (hoisted helper)
    intro s hs
    simp only [charX_next, charV_next]
    exact vlasovGlue_flow_aemeasurable f_prev g charX_prev charV_prev
      charX_g charV_g hT_pos h_prev_push h_prev_aemeas hg_init hg_aemeas_ex
      f_next (fun s' hs' => ite_eq_left hs') s hs
  · -- Conjunct (vii): boundary bundle for charX_next charV_next on Icc 0 (T + T_0)
    exact vlasovWellPosedness_glue_boundary gradW hT_pos hT_0_pos f_prev g f_next
      charX_prev charV_prev charX_g charV_g charX_next charV_next rfl rfl rfl
      h_prev_boundary hg_boundary hg_init hg_init_cond
  · -- Conjunct (viii): initial condition for charX_next charV_next
    intro z
    simp only [charX_next, charV_next, ite_eq_left hT_pos.le]
    exact h_prev_ic z

/-- For every positive Lipschitz constant there is a window length satisfying all
three per-window smallness constraints — the PL buffer, the contraction, and the
envelope closure.  Pure threshold arithmetic: `T_0 := min(1/√L, T_0_con, T_0_env)/2`
with each threshold positive for every `L > 0` (no `L < 1` restriction). -/
lemma exists_localSmallness_window (L : NNReal) (hL_pos : (0 : ℝ) < L) :
    ∃ T_0 : ℝ, 0 < T_0 ∧ LocalSmallnessPLBuffer L T_0 ∧ LocalSmallnessContraction L T_0 ∧
      (L : ℝ) / (1 + (L : ℝ)) * (Real.exp ((1 + (L : ℝ)) * T_0) - 1) < 1 := by
  let T_0_PL : ℝ := 1 / Real.sqrt L
  let T_0_con : ℝ := Real.log (max 1 (L : ℝ) / (L : ℝ) + 1) / max 1 (L : ℝ)
  let T_0_env : ℝ := Real.log (1 + (1 + (L : ℝ)) / (L : ℝ)) / (1 + (L : ℝ))
  let T_0 : ℝ := min (min T_0_PL T_0_con) T_0_env / 2
  have hL_nn : (0 : ℝ) ≤ L := NNReal.coe_nonneg L
  have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt hL_pos
  have hsqrtL_pos : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr hL_pos
  have hs_eq : (Real.sqrt (L : ℝ)) ^ 2 = (L : ℝ) := Real.sq_sqrt hL_nn
  have hK_pos : (0 : ℝ) < max 1 (L : ℝ) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hT_0_PL_pos : 0 < T_0_PL := by
    change 0 < 1 / Real.sqrt (L : ℝ); positivity
  have hKL_gt1 : 1 < max 1 (L : ℝ) / (L : ℝ) + 1 := by
    have : 0 < max 1 (L : ℝ) / (L : ℝ) := div_pos hK_pos hL_pos
    linarith
  have hT_0_con_pos : 0 < T_0_con :=
    div_pos (Real.log_pos hKL_gt1) hK_pos
  have h_1L_pos : (0 : ℝ) < 1 + (L : ℝ) := by linarith [hL_pos]
  have hT_0_env_pos : 0 < T_0_env := by
    change 0 < Real.log (1 + (1 + (L : ℝ)) / (L : ℝ)) / (1 + (L : ℝ))
    have h_arg_gt1 : 1 < 1 + (1 + (L : ℝ)) / (L : ℝ) := by
      have : 0 < (1 + (L : ℝ)) / (L : ℝ) := by positivity
      linarith
    exact div_pos (Real.log_pos h_arg_gt1) h_1L_pos
  have hT_0_min_pos : 0 < min (min T_0_PL T_0_con) T_0_env :=
    lt_min (lt_min hT_0_PL_pos hT_0_con_pos) hT_0_env_pos
  have hT0_pos : 0 < T_0 := by
    change 0 < min (min T_0_PL T_0_con) T_0_env / 2; linarith
  have hTL_T0_PL : LocalSmallnessPLBuffer L T_0 := by
    change (L : ℝ) * T_0 ^ 2 < 1
    have h_T_0_le : T_0 ≤ 1 / (2 * Real.sqrt (L : ℝ)) := by
      change min (min T_0_PL T_0_con) T_0_env / 2 ≤ 1 / (2 * Real.sqrt (L : ℝ))
      have h_min_le : min (min T_0_PL T_0_con) T_0_env ≤ T_0_PL :=
        le_trans (min_le_left _ _) (min_le_left _ _)
      have hrw : (1 : ℝ) / (2 * Real.sqrt (L : ℝ)) = (1 / Real.sqrt (L : ℝ)) / 2 := by
        rw [div_div, mul_comm (2 : ℝ) (Real.sqrt (L : ℝ))]
      rw [hrw]
      have hTPL : T_0_PL = 1 / Real.sqrt (L : ℝ) := rfl
      rw [hTPL] at h_min_le; linarith
    have h_T_0_nn : 0 ≤ T_0 := le_of_lt hT0_pos
    have h_sq_le : T_0 ^ 2 ≤ (1 / (2 * Real.sqrt (L : ℝ))) ^ 2 :=
      pow_le_pow_left₀ h_T_0_nn h_T_0_le 2
    have h_mul_le : (L : ℝ) * T_0 ^ 2 ≤ (L : ℝ) * (1 / (2 * Real.sqrt (L : ℝ))) ^ 2 :=
      mul_le_mul_of_nonneg_left h_sq_le hL_nn
    have h_eq : (L : ℝ) * (1 / (2 * Real.sqrt (L : ℝ))) ^ 2 = 1 / 4 := by
      rw [div_pow, one_pow, mul_pow, hs_eq]; field_simp; ring
    rw [h_eq] at h_mul_le; linarith
  have hTL_T0_con : LocalSmallnessContraction L T_0 := by
    change (L : ℝ) * (Real.exp ((max 1 (L : ℝ)) * T_0) - 1) / (max 1 (L : ℝ)) < 1
    set K : ℝ := max 1 (L : ℝ) with hK_def
    have h_T_0_lt : T_0 < T_0_con := by
      change min (min T_0_PL T_0_con) T_0_env / 2 < T_0_con
      have h_min_le : min (min T_0_PL T_0_con) T_0_env ≤ T_0_con :=
        le_trans (min_le_left _ _) (min_le_right _ _)
      linarith
    have hKL1_pos : (0 : ℝ) < K / (L : ℝ) + 1 := by
      have : 0 < K / (L : ℝ) := div_pos hK_pos hL_pos
      linarith
    have h_KT0_lt : K * T_0 < Real.log (K / (L : ℝ) + 1) := by
      have hTcon : T_0_con = Real.log (K / (L : ℝ) + 1) / K := rfl
      rw [hTcon] at h_T_0_lt
      have hh := (lt_div_iff₀ hK_pos).mp h_T_0_lt
      nlinarith [hh]
    have h_exp_lt : Real.exp (K * T_0) < K / (L : ℝ) + 1 := by
      have := Real.exp_lt_exp.mpr h_KT0_lt
      rwa [Real.exp_log hKL1_pos] at this
    have h_sub_lt : Real.exp (K * T_0) - 1 < K / (L : ℝ) := by linarith
    have h_num_lt : (L : ℝ) * (Real.exp (K * T_0) - 1) < K := by
      have := mul_lt_mul_of_pos_left h_sub_lt hL_pos
      rwa [mul_div_cancel₀ _ hL_ne] at this
    rw [div_lt_one hK_pos]
    exact h_num_lt
  have hTL_T0_B :
      (L : ℝ) / (1 + (L : ℝ)) * (Real.exp ((1 + (L : ℝ)) * T_0) - 1) < 1 := by
    have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt hL_pos
    have h_1L_ne : (1 + (L : ℝ)) ≠ 0 := ne_of_gt h_1L_pos
    have h_ratio_pos : (0 : ℝ) < (1 + (L : ℝ)) / (L : ℝ) := div_pos h_1L_pos hL_pos
    have h_arg_pos : (0 : ℝ) < 1 + (1 + (L : ℝ)) / (L : ℝ) := by linarith
    have h_T_0_lt_env : T_0 < T_0_env := by
      change min (min T_0_PL T_0_con) T_0_env / 2 < T_0_env
      have h_min_le : min (min T_0_PL T_0_con) T_0_env ≤ T_0_env := min_le_right _ _
      linarith
    have h_lin_lt : (1 + (L : ℝ)) * T_0
        < Real.log (1 + (1 + (L : ℝ)) / (L : ℝ)) := by
      have h_env_eq : (1 + (L : ℝ)) * T_0_env
          = Real.log (1 + (1 + (L : ℝ)) / (L : ℝ)) := by
        change (1 + (L : ℝ)) *
            (Real.log (1 + (1 + (L : ℝ)) / (L : ℝ)) / (1 + (L : ℝ)))
          = Real.log (1 + (1 + (L : ℝ)) / (L : ℝ))
        field_simp
      calc (1 + (L : ℝ)) * T_0
          < (1 + (L : ℝ)) * T_0_env := mul_lt_mul_of_pos_left h_T_0_lt_env h_1L_pos
        _ = Real.log (1 + (1 + (L : ℝ)) / (L : ℝ)) := h_env_eq
    have h_exp_lt : Real.exp ((1 + (L : ℝ)) * T_0)
        < 1 + (1 + (L : ℝ)) / (L : ℝ) := by
      calc Real.exp ((1 + (L : ℝ)) * T_0)
          < Real.exp (Real.log (1 + (1 + (L : ℝ)) / (L : ℝ))) :=
            Real.exp_lt_exp.mpr h_lin_lt
        _ = 1 + (1 + (L : ℝ)) / (L : ℝ) := Real.exp_log h_arg_pos
    have h_diff_lt : Real.exp ((1 + (L : ℝ)) * T_0) - 1 < (1 + (L : ℝ)) / (L : ℝ) := by
      linarith
    have hcoef_pos : (0 : ℝ) < (L : ℝ) / (1 + (L : ℝ)) := div_pos hL_pos h_1L_pos
    calc (L : ℝ) / (1 + (L : ℝ)) * (Real.exp ((1 + (L : ℝ)) * T_0) - 1)
        < (L : ℝ) / (1 + (L : ℝ)) * ((1 + (L : ℝ)) / (L : ℝ)) :=
          mul_lt_mul_of_pos_left h_diff_lt hcoef_pos
      _ = 1 := by field_simp
  exact ⟨T_0, hT0_pos, hTL_T0_PL, hTL_T0_con, hTL_T0_B⟩

/-- **Forward iteration to arbitrary `T_target`.**

Extends the local-existence theorem from its small-`T` smallness window
to any `T_target > 0`, by iterating the local theorem with shifted initial
data at a fixed step `T_0` depending only on `L` (no `L < 1` hypothesis).

**Proof strategy**:

1. Pick `T_0 := min(T_0_PL, T_0_con, T_0_env) / 2`, with `T_0_PL := 1/√L`
   (the PL-buffer threshold for `L · T_0² < 1`), `T_0_con`/`T_0_env` the
   contraction/envelope thresholds.  Each is positive for every `L > 0`, so
   `T_0 > 0` and all three smallness constraints hold.

2. Pick `N := ⌈T_target / T_0⌉₊` so that `N · T_0 ≥ T_target`.

3. `Nat.rec` construction: a solution holding the conjuncts at `T = n·T_0`.
   - Base case: apply `vlasovWellPosedness_local` directly.
   - Step case (`n → n+1`): apply `vlasovWellPosedness_glue` to extend.

4. Take `f := f_N` and verify the conjuncts for `T_target ≤ N · T_0` via
   `IsLagrangianVlasovSolutionOn`'s monotonicity in `T` (project down). -/
theorem vlasovWellPosedness_forward
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (hL_pos : (0 : ℝ) < L)
    (f₀ : Measure (PhaseSpace d))
    (hf₀ : HasFiniteFirstMoment f₀)
    {T_target : ℝ} (hT_target : 0 < T_target) :
    ∃ f : ℝ → Measure (PhaseSpace d),
      f 0 = f₀ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T_target, HasFiniteFirstMoment (f t)) ∧
      IsLagrangianVlasovSolutionOn gradW f T_target := by
  -- T_0 must satisfy the PL-buffer, contraction, and envelope constraints —
  -- all supplied by the pure-arithmetic `exists_localSmallness_window`.
  obtain ⟨T_0, hT0_pos, hTL_T0_PL, hTL_T0_con, hTL_T0_B⟩ :=
    exists_localSmallness_window L hL_pos
  -- Step 2: N = ⌈T_target / T_0⌉₊ windows of size T_0 cover T_target.
  let N : ℕ := ⌈T_target / T_0⌉₊
  have hN_pos : 0 < N := by
    change 0 < ⌈T_target / T_0⌉₊
    rw [Nat.ceil_pos]
    exact div_pos hT_target hT0_pos
  have hN_covers : T_target ≤ (N : ℝ) * T_0 := by
    have hle := Nat.le_ceil (T_target / T_0)
    have hT0_pos' := hT0_pos
    calc T_target = T_target / T_0 * T_0 := by field_simp
         _ ≤ (⌈T_target / T_0⌉₊ : ℝ) * T_0 :=
              mul_le_mul_of_nonneg_right hle (le_of_lt hT0_pos)
  -- Step 3: Induction on n : ℕ — solution exists on [0, (n+1)·T_0].
  -- The induction carries explicit flow witnesses (charX, charV) and the full
  -- 7-component bundle to enable vlasovWellPosedness_glue calls without witness-identity issues.
  let T_n := fun n : ℕ => ((n + 1 : ℕ) : ℝ) * T_0
  have h_ind : ∀ n : ℕ,
      ∃ (f : ℝ → Measure (PhaseSpace d))
        (charX charV : ℝ → PhaseSpace d → PhysSpace d),
        f 0 = f₀ ∧
        (∀ t ∈ Set.Icc (0 : ℝ) (T_n n), HasFiniteFirstMoment (f t)) ∧
        -- FLAT (window-constant) uniform first-moment bound on the spatial marginal.
        (∃ M : ℝ, 0 ≤ M ∧
          ∀ t ∈ Set.Icc (0 : ℝ) (T_n n), ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M) ∧
        IsVlasovSolutionOn gradW f (T_n n) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) (T_n n),
            f t = Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) (f 0)) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) (T_n n),
            AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) (f 0)) ∧
        (∀ (z : PhaseSpace d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) (T_n n) →
            HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 (T_n n)) t ∧
            HasDerivWithinAt (fun s => charV s z)
              (-(convolveFunctionMeasure gradW (spatialMarginal (f t)) (charX t z)))
              (Set.Icc 0 (T_n n)) t) ∧
        (∀ z : PhaseSpace d, charX 0 z = z.1 ∧ charV 0 z = z.2) := by
    intro n
    induction n with
    | zero =>
      -- Base: n = 0, need solution on [0, 1·T_0] = [0, T_0].
      simp only [T_n, zero_add, Nat.cast_one, one_mul]
      obtain ⟨f, charX, charV, hf_init, hf_mom, hf_mom_unif, hf_lag, hf_push, hf_aemeas,
        hf_boundary, hf_ic⟩ :=
        vlasovWellPosedness_local W gradW hgradW L hL f₀ hf₀ hT0_pos hTL_T0_PL hTL_T0_con hTL_T0_B
      exact ⟨f, charX, charV, hf_init, hf_mom, hf_mom_unif, hf_lag.1, hf_push, hf_aemeas,
        hf_boundary, hf_ic⟩
    | succ n ih =>
      -- Step: n+1 → (n+2)·T_0.  Use vlasovWellPosedness_glue with T = (n+1)·T_0 > 0.
      obtain ⟨f_n, charX_n, charV_n, hfn_init, hfn_mom, hfn_mom_unif, hfn_vlasov,
              hfn_push, hfn_aemeas, hfn_boundary, hfn_ic⟩ := ih
      simp only [T_n] at hfn_mom hfn_mom_unif hfn_vlasov hfn_push hfn_aemeas hfn_boundary
      have hT_n_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) * T_0 :=
        mul_pos (by exact_mod_cast Nat.succ_pos n) hT0_pos
      -- Derive IsCharacteristicFlowOn from h_prev_boundary + hasDerivAt
      -- (interior points t ∈ Ioo 0 T_n have Icc 0 T_n ∈ 𝓝 t, so HasDerivWithinAt → HasDerivAt)
      have hfn_flow : IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f_n t))
          charX_n charV_n (Set.Ioo 0 (((n + 1 : ℕ) : ℝ) * T_0)) Set.univ := by
        refine ⟨fun z _ => hfn_ic z, ?_, ?_⟩
        · intro t ht z _
          exact ((hfn_boundary z t (Set.Ioo_subset_Icc_self ht)).1).hasDerivAt
            (Icc_mem_nhds ht.1 ht.2)
        · intro t ht z _
          exact ((hfn_boundary z t (Set.Ioo_subset_Icc_self ht)).2).hasDerivAt
            (Icc_mem_nhds ht.1 ht.2)
      obtain ⟨f_next, charX_next, charV_next, _h_agree, h_init, h_mom, h_mom_unif, h_lag,
              h_push, h_aemeas, h_boundary, h_ic⟩ :=
        vlasovWellPosedness_glue W gradW hgradW L hL f₀ hf₀ hT_n_pos
          f_n hfn_init hfn_mom hfn_mom_unif
          charX_n charV_n hfn_vlasov hfn_flow
          hfn_push hfn_aemeas hfn_boundary hfn_ic
          hT0_pos hTL_T0_PL hTL_T0_con hTL_T0_B
      -- Need: T_n (n+1) = T_n n + T_0
      have h_T_eq : T_n (n + 1) = T_n n + T_0 := by
        simp only [T_n]; push_cast; ring
      refine ⟨f_next, charX_next, charV_next, h_init, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h_T_eq]; exact h_mom
      · rw [h_T_eq]; exact h_mom_unif
      · rw [h_T_eq]; exact h_lag.1
      · rw [h_T_eq]; exact h_push
      · rw [h_T_eq]; exact h_aemeas
      · rw [h_T_eq]; exact h_boundary
      · exact h_ic
  -- Step 4: Apply h_ind at n = N - 1 (since N ≥ 1).
  have hN_pred : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos hN_pos
  obtain ⟨f, charX_f, charV_f, hf_init, hf_mom, _hf_mom_unif, hf_vlasov,
          hf_push, hf_aemeas, hf_boundary, hf_ic⟩ := h_ind (N - 1)
  simp only [T_n] at hf_mom hf_vlasov hf_push hf_aemeas hf_boundary
  rw [hN_pred] at hf_mom hf_vlasov hf_push hf_aemeas hf_boundary
  -- Step 5: Restrict from [0, N·T_0] down to [0, T_target].
  refine ⟨f, hf_init, ?_, ?_⟩
  · -- Moment bound on [0, T_target] ⊆ [0, N·T_0].
    intro t ht
    exact hf_mom t ⟨ht.1, le_trans ht.2 hN_covers⟩
  · -- IsLagrangianVlasovSolutionOn on [0, T_target] ≤ [0, N·T_0].
    -- Derive IsCharacteristicFlowOn for T_target from hf_boundary (restrict to Ioo 0 T_target).
    have hf_flow : IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f t))
        charX_f charV_f (Set.Ioo 0 T_target) Set.univ := by
      refine ⟨fun z _ => hf_ic z, ?_, ?_⟩
      · intro t ht z _
        have ht_lt_NT0 : t < (N : ℝ) * T_0 := lt_of_lt_of_le ht.2 hN_covers
        exact ((hf_boundary z t ⟨le_of_lt ht.1, le_of_lt ht_lt_NT0⟩).1).hasDerivAt
          (Icc_mem_nhds ht.1 ht_lt_NT0)
      · intro t ht z _
        have ht_lt_NT0 : t < (N : ℝ) * T_0 := lt_of_lt_of_le ht.2 hN_covers
        exact ((hf_boundary z t ⟨le_of_lt ht.1, le_of_lt ht_lt_NT0⟩).2).hasDerivAt
          (Icc_mem_nhds ht.1 ht_lt_NT0)
    refine ⟨?_, charX_f, charV_f, ?_, ?_, ?_⟩
    · -- IsVlasovSolutionOn: restrict Ioo 0 T_target ⊆ Ioo 0 (N·T_0)
      intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ t ht
      exact hf_vlasov φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ t
        ⟨ht.1, lt_of_lt_of_le ht.2 hN_covers⟩
    · exact hf_flow
    · -- pushforward eq: restrict Icc 0 T_target ⊆ Icc 0 (N·T_0)
      intro t ht
      exact hf_push t ⟨ht.1, le_trans ht.2 hN_covers⟩
    · -- AEMeasurable ∧ boundary ContinuousOn, restricted to Icc 0 T_target.
      refine ⟨?_, ?_⟩
      · intro s hs
        exact hf_aemeas s ⟨hs.1, le_trans hs.2 hN_covers⟩
      · intro z
        have h_big : ContinuousOn (fun s => (charX_f s z, charV_f s z))
            (Set.Icc 0 ((N : ℝ) * T_0)) := fun t ht =>
          ((hf_boundary z t ht).1.continuousWithinAt).prodMk
            ((hf_boundary z t ht).2.continuousWithinAt)
        exact h_big.mono (fun t ht => ⟨ht.1, le_trans ht.2 hN_covers⟩)

/-! ## Uniqueness over `IsLagrangianVlasovSolutionOn` per window -/
-- Two Lagrangian solutions on `[0, T_target]` with the same initial measure
-- agree on `[0, T_target]`.  The argument: contraction in `Phi_supW1_contraction`
-- + Banach fixed-point uniqueness on the iterated windows.  Within the
-- `IsLagrangianVlasovSolutionOn` class, the flow witness is bundled, so
-- pushforward + flow uniqueness chains directly.  (The broader uniqueness
-- over `IsVlasovSolution` — weak-PDE-only solutions without an explicit
-- flow — requires the Eulerian-to-Lagrangian / DiPerna-Lions superposition
-- principle, which is out of scope.)
--
-- The uniqueness proof bounds the *integrated trajectory distance*
-- `∫ ‖Φ_f − Φ_g‖ ∂μ₀` directly via `integrated_coupling_gronwall_bound` (the
-- `Q 0 = 0` case) — never forming `t ↦ (wasserstein1 (f t) (g t)).toReal` —
-- so closed-window continuity of the real-valued W₁ distance is not needed.


/-- The origin trajectory `s ↦ (charX s 0, charV s 0)` of a flow continuous on
`[0, T]` is norm-bounded by some `Kc ≥ 0` (compactness). -/
private lemma dobrushinFlow_origin_trajectory_bound
    {d : ℕ} [NeZero d] (T : ℝ)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hcont : ContinuousOn (fun s => (charX s 0, charV s 0)) (Set.Icc (0 : ℝ) T)) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖(charX s 0, charV s 0)‖ ≤ Kc := by
  have hbdd : BddAbove ((fun s => ‖(charX s 0, charV s 0)‖) '' Set.Icc (0 : ℝ) T) :=
    IsCompact.bddAbove_image isCompact_Icc hcont.norm
  obtain ⟨Kc, hKc⟩ := hbdd
  refine ⟨max Kc 0, le_max_right _ _, fun s hs => ?_⟩
  exact le_trans (hKc (Set.mem_image_of_mem _ hs)) (le_max_left _ _)

/-- Linear-in-`‖ω‖` norm bound on a flow from its Lipschitz-in-`z` estimate and
a bound on the origin trajectory: `‖Φ s ω‖ ≤ e^{KT} ‖ω‖ + Kc` on `[0, T]`. -/
private lemma dobrushinFlow_flow_norm_bound
    {d : ℕ} [NeZero d]
    (T : ℝ) (K : NNReal)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d) (Kc : ℝ)
    (hlip : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
      dist ((charX s z₁, charV s z₁) : PhaseSpace d) (charX s z₂, charV s z₂) ≤
      dist z₁ z₂ * Real.exp (((K : NNReal) : ℝ) * (s - 0)))
    (hKc : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖(charX s 0, charV s 0)‖ ≤ Kc) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω : PhaseSpace d,
      ‖(charX s ω, charV s ω)‖ ≤ Real.exp (((K : NNReal) : ℝ) * T) * ‖ω‖ + Kc := by
  have hK_nn : (0 : ℝ) ≤ ((K : NNReal) : ℝ) := K.coe_nonneg
  set EKT : ℝ := Real.exp (((K : NNReal) : ℝ) * T) with hEKT_def
  intro s hs ω
  have htri : ‖(charX s ω, charV s ω)‖ ≤
      dist ((charX s ω, charV s ω) : PhaseSpace d) (charX s 0, charV s 0)
        + ‖(charX s 0, charV s 0)‖ := by
    rw [dist_eq_norm]
    calc ‖(charX s ω, charV s ω)‖
        = ‖((charX s ω, charV s ω) - (charX s 0, charV s 0))
            + ((charX s 0, charV s 0) : PhaseSpace d)‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖((charX s ω, charV s ω) : PhaseSpace d) - (charX s 0, charV s 0)‖
            + ‖(charX s 0, charV s 0)‖ := norm_add_le _ _
  have hdist_le : dist ((charX s ω, charV s ω) : PhaseSpace d) (charX s 0, charV s 0)
      ≤ EKT * ‖ω‖ := by
    refine le_trans (hlip s hs ω 0) ?_
    rw [dist_zero_right]
    have hsT : (((K : NNReal) : ℝ)) * (s - 0) ≤ (((K : NNReal) : ℝ)) * T := by
      rw [sub_zero]; exact mul_le_mul_of_nonneg_left hs.2 hK_nn
    have hexp_le : Real.exp (((K : NNReal) : ℝ) * (s - 0)) ≤ EKT :=
      Real.exp_le_exp.mpr hsT
    calc ‖ω‖ * Real.exp (((K : NNReal) : ℝ) * (s - 0))
        ≤ ‖ω‖ * EKT := mul_le_mul_of_nonneg_left hexp_le (norm_nonneg _)
      _ = EKT * ‖ω‖ := by ring
  calc ‖(charX s ω, charV s ω)‖
      ≤ dist ((charX s ω, charV s ω) : PhaseSpace d) (charX s 0, charV s 0)
          + ‖(charX s 0, charV s 0)‖ := htri
    _ ≤ EKT * ‖ω‖ + Kc := by
        gcongr
        exact hKc s hs

/-- Pushforward-convolution identity, generic in the base `ν`: when
`μ s = (charX s, charV s)_# ν`, the convolution force against the spatial
marginal of `μ s` is the `ν`-integral of the pushed-forward kernel. -/
private lemma dobrushinFlow_conv_pushforward
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (T : ℝ)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (μ : ℝ → Measure (PhaseSpace d)) (ν : Measure (PhaseSpace d))
    (hpush : ∀ t ∈ Set.Icc (0 : ℝ) T,
      μ t = Measure.map (fun z => (charX t z, charV t z)) ν)
    (haem : ∀ s ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) ν) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x : PhysSpace d,
      convolveFunctionMeasure gradW (spatialMarginal (μ s)) x
        = ∫ ω', gradW (x - charX s ω') ∂ν := by
  intro s hs x
  unfold convolveFunctionMeasure spatialMarginal
  rw [hpush s hs]
  have haem_s : AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) ν :=
    haem s hs
  have hmeas_gradW : AEStronglyMeasurable
      (fun y : PhysSpace d => gradW (x - y))
      (Measure.map Prod.fst (Measure.map (fun z => (charX s z, charV s z)) ν)) :=
    (hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  rw [integral_map measurable_fst.aemeasurable hmeas_gradW]
  have hmeas_inner : AEStronglyMeasurable
      (fun z : PhaseSpace d => gradW (x - z.1))
      (Measure.map (fun z => (charX s z, charV s z)) ν) :=
    ((hL.continuous.comp (continuous_const.sub continuous_fst))).aestronglyMeasurable
  rw [integral_map haem_s hmeas_inner]

/-- Companion integrability transfer for `dobrushinFlow_conv_pushforward`,
generic in the base `ν`. -/
private lemma dobrushinFlow_gradW_int_pushforward
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (T : ℝ)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (μ : ℝ → Measure (PhaseSpace d)) (ν : Measure (PhaseSpace d))
    (hpush : ∀ t ∈ Set.Icc (0 : ℝ) T,
      μ t = Measure.map (fun z => (charX t z, charV t z)) ν)
    (haem : ∀ s ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) ν)
    (hint_sm : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (spatialMarginal (μ t))) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x : PhysSpace d,
      Integrable (fun ω' => gradW (x - charX s ω')) ν := by
  intro s hs x
  have hsm := hint_sm s hs x
  unfold spatialMarginal at hsm
  rw [hpush s hs] at hsm
  rw [integrable_map_measure
    (g := fun y : PhysSpace d => gradW (x - y))
    ((hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    measurable_fst.aemeasurable] at hsm
  simp only [Function.comp_def] at hsm
  rw [integrable_map_measure
    (g := fun z : PhaseSpace d => gradW (x - z.1))
    ((hL.continuous.comp (continuous_const.sub continuous_fst)).aestronglyMeasurable)
    (haem s hs)] at hsm
  exact hsm

/-- Phase-space integrability of a pushforward flow over its base, from the
first moments of the pushed-forward curve. -/
private lemma dobrushinFlow_phase_int_pushforward
    {d : ℕ} [NeZero d] (T : ℝ)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (μ : ℝ → Measure (PhaseSpace d)) (ν : Measure (PhaseSpace d))
    (hpush : ∀ t ∈ Set.Icc (0 : ℝ) T,
      μ t = Measure.map (fun z => (charX t z, charV t z)) ν)
    (haem : ∀ s ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) ν)
    (hmom : ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun z : PhaseSpace d => ‖z‖) (μ t)) :
    ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun ω' : PhaseSpace d => (charX s ω', charV s ω')) ν := by
  intro s hs
  have hid : Integrable (fun z : PhaseSpace d => z) (μ s) :=
    (integrable_norm_iff aestronglyMeasurable_id).mp (hmom s hs)
  rw [hpush s hs] at hid
  rw [integrable_map_measure
    (g := fun z : PhaseSpace d => z) aestronglyMeasurable_id (haem s hs)] at hid
  exact hid

/-- Global continuity in `s` of the clamped Vlasov field along a clamped
trajectory: velocity slot continuous from the flow; force slot a pushforward
integral over the base `ν`, continuous by moment-free dominated convergence.
Generic in the base `ν` and clamp `clampT`. -/
private lemma dobrushinFlow_field_continuous
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (T : ℝ) (K : NNReal)
    (clampT : ℝ → ℝ) (hclampT_mem : ∀ s, clampT s ∈ Set.Icc (0 : ℝ) T)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (μ : ℝ → Measure (PhaseSpace d)) (ν : Measure (PhaseSpace d)) (Kc : ℝ)
    (b : ℝ → PhaseSpace d → PhaseSpace d) (X : ℝ → PhaseSpace d → PhaseSpace d)
    (hb : b = fun s => vlasovVectorField gradW (fun s => spatialMarginal (μ (clampT s))) s)
    (hX : X = fun s ω => (charX (clampT s) ω, charV (clampT s) ω))
    (hflowcont : ∀ z, Continuous (fun s => (charX (clampT s) z, charV (clampT s) z)))
    (hpush : ∀ t ∈ Set.Icc (0 : ℝ) T,
      μ t = Measure.map (fun z => (charX t z, charV t z)) ν)
    (haem : ∀ s ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) ν)
    (hν_prob : IsProbabilityMeasure ν)
    (hν_mom : Integrable (fun z : PhaseSpace d => ‖z‖) ν)
    (hKc : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖(charX s 0, charV s 0)‖ ≤ Kc)
    (hlip : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
      dist ((charX s z₁, charV s z₁) : PhaseSpace d) (charX s z₂, charV s z₂) ≤
      dist z₁ z₂ * Real.exp (((K : NNReal) : ℝ) * (s - 0))) :
    ∀ ω, Continuous (fun s => b s (X s ω)) := by
  intro ω
  have := hν_prob
  set EKT : ℝ := Real.exp (((K : NNReal) : ℝ) * T) with hEKT_def
  have hΦnorm : ∀ s : ℝ, ∀ z : PhaseSpace d,
      ‖(charX (clampT s) z, charV (clampT s) z)‖ ≤ EKT * ‖z‖ + Kc := by
    rw [hEKT_def]
    exact fun s z =>
      dobrushinFlow_flow_norm_bound T K charX charV Kc hlip hKc
        (clampT s) (hclampT_mem s) z
  subst hb hX
  set xS : ℝ → PhysSpace d := fun s => charX (clampT s) ω with hxS_def
  have hxS_cont : Continuous xS := (continuous_fst.comp (hflowcont ω))
  have hforce_eq : ∀ s : ℝ,
      convolveFunctionMeasure gradW (spatialMarginal (μ (clampT s))) (xS s)
        = ∫ ω', gradW (xS s - charX (clampT s) ω') ∂ν := by
    intro s
    exact dobrushinFlow_conv_pushforward gradW L hL T charX charV μ ν hpush haem
      (clampT s) (hclampT_mem s) (xS s)
  have hforce_cont : Continuous
      (fun s => ∫ ω', gradW (xS s - charX (clampT s) ω') ∂ν) := by
    set bnd : PhaseSpace d → ℝ := fun ω' =>
      ‖gradW 0‖ + (L : ℝ) * ((EKT * ‖ω‖ + Kc) + (EKT * ‖ω'‖ + Kc)) with hbnd_def
    have hbnd_int : Integrable bnd ν := by
      simp only [hbnd_def]
      have hmom : Integrable (fun ω' : PhaseSpace d => ‖ω'‖) ν := hν_mom
      have hL_EKT : Integrable (fun ω' : PhaseSpace d => (L : ℝ) * (EKT * ‖ω'‖)) ν := by
        have : Integrable (fun ω' : PhaseSpace d => EKT * ‖ω'‖) ν :=
          hmom.const_mul EKT
        exact this.const_mul (L : ℝ)
      have heq : (fun ω' : PhaseSpace d =>
          ‖gradW 0‖ + (L : ℝ) * ((EKT * ‖ω‖ + Kc) + (EKT * ‖ω'‖ + Kc))) =
          fun ω' => (‖gradW 0‖ + (L : ℝ) * ((EKT * ‖ω‖ + Kc) + Kc))
            + (L : ℝ) * (EKT * ‖ω'‖) := by
        funext ω'; ring
      rw [heq]; exact (integrable_const _).add hL_EKT
    refine continuous_of_dominated
      (fun s => ?_) (fun s => Filter.Eventually.of_forall (fun ω' => ?_)) hbnd_int
      (Filter.Eventually.of_forall (fun ω' => ?_))
    · have haem_charX : AEMeasurable (fun ω' : PhaseSpace d => charX (clampT s) ω') ν :=
        (measurable_fst.comp_aemeasurable (haem (clampT s) (hclampT_mem s)))
      exact ((hL.continuous.comp
          (continuous_const.sub continuous_id)).measurable.comp_aemeasurable
        haem_charX).aestronglyMeasurable
    · have hd := hL.dist_le_mul (xS s - charX (clampT s) ω') 0
      simp only [dist_eq_norm, sub_zero] at hd
      have h_tri : ‖gradW (xS s - charX (clampT s) ω')‖ ≤
          ‖gradW 0‖ + ‖gradW (xS s - charX (clampT s) ω') - gradW 0‖ := by
        have := norm_add_le (gradW (xS s - charX (clampT s) ω') - gradW 0) (gradW 0)
        simp only [sub_add_cancel] at this; linarith
      have hsub_le : ‖xS s - charX (clampT s) ω'‖ ≤ ‖xS s‖ + ‖charX (clampT s) ω'‖ :=
        norm_sub_le _ _
      have hxS_le : ‖xS s‖ ≤ EKT * ‖ω‖ + Kc := by
        simp only [hxS_def]
        exact le_trans
          (norm_fst_le ((charX (clampT s) ω, charV (clampT s) ω) : PhaseSpace d))
          (hΦnorm s ω)
      have hcharX_le : ‖charX (clampT s) ω'‖ ≤ EKT * ‖ω'‖ + Kc :=
        le_trans
          (norm_fst_le ((charX (clampT s) ω', charV (clampT s) ω') : PhaseSpace d))
          (hΦnorm s ω')
      have h_mul := mul_le_mul_of_nonneg_left
        (le_trans hsub_le (add_le_add hxS_le hcharX_le)) L.coe_nonneg
      simp only [hbnd_def]; linarith
    · exact hL.continuous.comp (hxS_cont.sub
        (continuous_fst.comp (hflowcont ω')))
  have hvel_cont : Continuous (fun s => (charX (clampT s) ω, charV (clampT s) ω).2) :=
    continuous_snd.comp (hflowcont ω)
  have hbody : (fun s => vlasovVectorField gradW
        (fun s => spatialMarginal (μ (clampT s))) s
        ((charX (clampT s) ω, charV (clampT s) ω)))
      = fun s => ((charX (clampT s) ω, charV (clampT s) ω).2,
          -(∫ ω', gradW (xS s - charX (clampT s) ω') ∂ν)) := by
    funext s
    simp only [vlasovVectorField]
    refine Prod.ext rfl ?_
    change -(convolveFunctionMeasure gradW (spatialMarginal (μ (clampT s)))
        (charX (clampT s) ω, charV (clampT s) ω).1)
      = -(∫ ω', gradW (xS s - charX (clampT s) ω') ∂ν)
    rw [hforce_eq s]
  rw [hbody]
  exact hvel_cont.prodMk hforce_cont.neg

/-- Open-window flow ODE in `z` for the clamped field: on `Ioo 0 T` the clamp
is the identity, so the witness `HasDerivAt` pair transfers to
`HasDerivWithinAt` on `Ici s` against the clamped vector field. -/
private lemma dobrushinFlow_deriv_Ioo
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (T : ℝ) (clampT : ℝ → ℝ)
    (hclampT_id : ∀ s ∈ Set.Icc (0 : ℝ) T, clampT s = s)
    (μ : ℝ → Measure (PhaseSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow_x : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
      HasDerivAt (fun s' => charX s' z) (charV s z) s)
    (hflow_v : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
      HasDerivAt (fun s' => charV s' z)
        (-(convolveFunctionMeasure gradW (spatialMarginal (μ s)) (charX s z))) s) :
    ∀ z : PhaseSpace d, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW (fun s => spatialMarginal (μ (clampT s))) s
          (charX s z, charV s z)) (Set.Ici s) s := by
  intro z s hs
  have hsIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
  have hat : HasDerivAt (fun s' => (charX s' z, charV s' z))
      (vlasovVectorField gradW (fun s => spatialMarginal (μ s)) s
        (charX s z, charV s z)) s := by
    change HasDerivAt (fun s' => (charX s' z, charV s' z))
      ((charX s z, charV s z).2,
       -(convolveFunctionMeasure gradW (spatialMarginal (μ s))
          (charX s z, charV s z).1)) s
    exact (hflow_x s hs z (Set.mem_univ z)).prodMk (hflow_v s hs z (Set.mem_univ z))
  have hmeas : spatialMarginal (μ (clampT s)) = spatialMarginal (μ s) := by
    rw [hclampT_id s hsIcc]
  have hvf_eq : vlasovVectorField gradW (fun s => spatialMarginal (μ (clampT s))) s
        (charX s z, charV s z)
      = vlasovVectorField gradW (fun s => spatialMarginal (μ s)) s
        (charX s z, charV s z) := by
    simp only [vlasovVectorField, hmeas]
  rw [hvf_eq]; exact hat.hasDerivWithinAt

/-- Per-`ω` continuity on `[0, T]` of a clamped trajectory family read through
a projection: the clamp composes continuously and is the identity on-window. -/
private lemma dobrushinFlow_clamped_cont
    {d : ℕ} [NeZero d] {Ω : Type*}
    (T : ℝ) (clampT : ℝ → ℝ) (hclampT_cont : Continuous clampT)
    (hclampT_mem : ∀ s, clampT s ∈ Set.Icc (0 : ℝ) T)
    (hclampT_id : ∀ s ∈ Set.Icc (0 : ℝ) T, clampT s = s)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (proj : Ω → PhaseSpace d)
    (hcontIcc : ∀ z, ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc 0 T))
    (X : ℝ → Ω → PhaseSpace d)
    (hX : X = fun s ω => (charX (clampT s) (proj ω), charV (clampT s) (proj ω))) :
    ∀ ω, ContinuousOn (fun s => X s ω) (Set.Icc 0 T) := by
  intro ω
  have hbase : ContinuousOn (fun s => (charX s (proj ω), charV s (proj ω)))
      (Set.Icc 0 T) := hcontIcc (proj ω)
  apply ContinuousOn.congr
    (f := fun s => (charX (clampT s) (proj ω), charV (clampT s) (proj ω)))
  · exact hbase.comp hclampT_cont.continuousOn (fun s hs => hclampT_mem s)
  · intro s hs; simp only [hX, hclampT_id s hs]

/-- Per-`ω` ODE on `Ioo 0 T` of a clamped trajectory family against the
clamped field (`HasDerivWithinAt` on `Ioi s`), via the witness `HasDerivAt`
pair and on-window clamp-identity congruence. -/
private lemma dobrushinFlow_clamped_deriv
    {d : ℕ} [NeZero d] {Ω : Type*}
    (gradW : PhysSpace d → PhysSpace d)
    (T : ℝ) (clampT : ℝ → ℝ)
    (hclampT_id : ∀ s ∈ Set.Icc (0 : ℝ) T, clampT s = s)
    (μ : ℝ → Measure (PhaseSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (proj : Ω → PhaseSpace d)
    (hflow_x : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
      HasDerivAt (fun s' => charX s' z) (charV s z) s)
    (hflow_v : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
      HasDerivAt (fun s' => charV s' z)
        (-(convolveFunctionMeasure gradW (spatialMarginal (μ s)) (charX s z))) s)
    (b : ℝ → PhaseSpace d → PhaseSpace d)
    (hb_id : ∀ s ∈ Set.Icc (0 : ℝ) T,
      b s = vlasovVectorField gradW (fun s => spatialMarginal (μ s)) s)
    (X : ℝ → Ω → PhaseSpace d)
    (hX : X = fun s ω => (charX (clampT s) (proj ω), charV (clampT s) (proj ω))) :
    ∀ ω, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s => X s ω) (b s (X s ω)) (Set.Ioi s) s := by
  intro ω s hs
  have hsIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
  have hat : HasDerivAt (fun s' => (charX s' (proj ω), charV s' (proj ω)))
      (vlasovVectorField gradW (fun s => spatialMarginal (μ s)) s
        (charX s (proj ω), charV s (proj ω))) s := by
    change HasDerivAt (fun s' => (charX s' (proj ω), charV s' (proj ω)))
      ((charX s (proj ω), charV s (proj ω)).2,
       -(convolveFunctionMeasure gradW (spatialMarginal (μ s))
          (charX s (proj ω), charV s (proj ω)).1)) s
    exact (hflow_x s hs (proj ω) (Set.mem_univ _)).prodMk
      (hflow_v s hs (proj ω) (Set.mem_univ _))
  have hwithin : HasDerivWithinAt (fun s' => (charX s' (proj ω), charV s' (proj ω)))
      (vlasovVectorField gradW (fun s => spatialMarginal (μ s)) s
        (charX s (proj ω), charV s (proj ω))) (Set.Ioi s) s := hat.hasDerivWithinAt
  have heq : Set.EqOn (fun s' => X s' ω)
      (fun s' => (charX s' (proj ω), charV s' (proj ω))) (Set.Ioo (0 : ℝ) T) := by
    intro s' hs'; simp only [hX, hclampT_id s' ⟨hs'.1.le, hs'.2.le⟩]
  have hmem_nhds : Set.Ioo (0 : ℝ) T ∈ nhdsWithin s (Set.Ioi s) :=
    mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hs)
  have hx : X s ω = (charX s (proj ω), charV s (proj ω)) := by
    simp only [hX, hclampT_id s hsIcc]
  have hwithin' := hwithin.congr_of_eventuallyEq
    (Filter.eventually_of_mem hmem_nhds (fun s' hs' => heq hs'))
    hx
  rw [hb_id s hsIcc, hx]; exact hwithin'


/-- First-moment transfer to the base: `∫ ‖proj ω‖ dπ₀` is finite when the
pushed-forward marginal has a finite first moment. -/
private lemma dobrushinFlow_proj_moment
    {d : ℕ} [NeZero d] {Ω : Type*} [MeasurableSpace Ω]
    (π₀ : Measure Ω) (proj : Ω → PhaseSpace d) (hproj : Measurable proj)
    (μ0 : Measure (PhaseSpace d)) (hmarg : μ0 = Measure.map proj π₀)
    (hmom : Integrable (fun z : PhaseSpace d => ‖z‖) μ0) :
    Integrable (fun ω : Ω => ‖proj ω‖) π₀ := by
  have hmap : Integrable (fun z : PhaseSpace d => ‖z‖) (Measure.map proj π₀) := by
    rw [← hmarg]; exact hmom
  exact (integrable_map_measure continuous_norm.aestronglyMeasurable
    hproj.aemeasurable).mp hmap

/-- On `[0, T]` the clamped Vlasov field coincides with the genuine field. -/
private lemma dobrushinFlow_clamped_field_id
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (T : ℝ) (clampT : ℝ → ℝ)
    (hclampT_id : ∀ s ∈ Set.Icc (0 : ℝ) T, clampT s = s)
    (μ : ℝ → Measure (PhaseSpace d))
    (b : ℝ → PhaseSpace d → PhaseSpace d)
    (hb : b = fun s => vlasovVectorField gradW (fun s => spatialMarginal (μ (clampT s))) s) :
    ∀ s ∈ Set.Icc (0 : ℝ) T,
      b s = vlasovVectorField gradW (fun s => spatialMarginal (μ s)) s := by
  intro s hs
  have hmeas : spatialMarginal (μ (clampT s)) = spatialMarginal (μ s) := by
    rw [hclampT_id s hs]
  funext z; simp only [hb, vlasovVectorField, hmeas]

/-- Moment-free dominator bound: the coupled trajectory difference is bounded
by `e^{KT}(‖proj_f ω‖ + ‖proj_g ω‖) + (K_f + K_g)` on `[0, T]`. -/
private lemma dobrushinFlow_dominator_bound
    {d : ℕ} [NeZero d] {Ω : Type*}
    (T : ℝ) (clampT : ℝ → ℝ)
    (hclampT_id : ∀ s ∈ Set.Icc (0 : ℝ) T, clampT s = s)
    (charX_f charV_f charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    (proj_f proj_g : Ω → PhaseSpace d)
    (EKT K_f K_g : ℝ)
    (hfnorm : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω : PhaseSpace d,
      ‖(charX_f s ω, charV_f s ω)‖ ≤ EKT * ‖ω‖ + K_f)
    (hgnorm : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω : PhaseSpace d,
      ‖(charX_g s ω, charV_g s ω)‖ ≤ EKT * ‖ω‖ + K_g)
    (X_f X_g : ℝ → Ω → PhaseSpace d)
    (hX_f : X_f = fun s ω => (charX_f (clampT s) (proj_f ω), charV_f (clampT s) (proj_f ω)))
    (hX_g : X_g = fun s ω => (charX_g (clampT s) (proj_g ω), charV_g (clampT s) (proj_g ω))) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω,
      ‖X_f s ω - X_g s ω‖ ≤ EKT * ‖proj_f ω‖ + EKT * ‖proj_g ω‖ + (K_f + K_g) := by
  intro s hs ω
  have hclamp_eq : clampT s = s := hclampT_id s hs
  have hXf : X_f s ω = (charX_f s (proj_f ω), charV_f s (proj_f ω)) := by
    simp only [hX_f, hclamp_eq]
  have hXg : X_g s ω = (charX_g s (proj_g ω), charV_g s (proj_g ω)) := by
    simp only [hX_g, hclamp_eq]
  rw [hXf, hXg]
  calc ‖(charX_f s (proj_f ω), charV_f s (proj_f ω))
          - (charX_g s (proj_g ω), charV_g s (proj_g ω))‖
      ≤ ‖(charX_f s (proj_f ω), charV_f s (proj_f ω))‖
          + ‖(charX_g s (proj_g ω), charV_g s (proj_g ω))‖ := norm_sub_le _ _
    _ ≤ (EKT * ‖proj_f ω‖ + K_f) + (EKT * ‖proj_g ω‖ + K_g) := by
        have hf_bd := hfnorm s hs (proj_f ω)
        have hg_bd := hgnorm s hs (proj_g ω)
        gcongr
    _ = EKT * ‖proj_f ω‖ + EKT * ‖proj_g ω‖ + (K_f + K_g) := by ring

/-- Global continuity in `s` of the integrated trajectory distance
`s ↦ ∫ ‖X_f s − X_g s‖ dπ₀`, by moment-free dominated convergence (the clamp
makes the integrand globally continuous per `ω` and globally dominated). -/
private lemma dobrushinFlow_Q_continuous
    {d : ℕ} [NeZero d] {Ω : Type*} [MeasurableSpace Ω]
    (T : ℝ) (clampT : ℝ → ℝ) (hclampT_cont : Continuous clampT)
    (hclampT_mem : ∀ s, clampT s ∈ Set.Icc (0 : ℝ) T)
    (hclampT_id : ∀ s ∈ Set.Icc (0 : ℝ) T, clampT s = s)
    (π₀ : Measure Ω)
    (charX_f charV_f charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    (proj_f proj_g : Ω → PhaseSpace d)
    (hcontIcc_f : ∀ z, ContinuousOn (fun s => (charX_f s z, charV_f s z)) (Set.Icc 0 T))
    (hcontIcc_g : ∀ z, ContinuousOn (fun s => (charX_g s z, charV_g s z)) (Set.Icc 0 T))
    (X_f X_g : ℝ → Ω → PhaseSpace d)
    (hX_f : X_f = fun s ω => (charX_f (clampT s) (proj_f ω), charV_f (clampT s) (proj_f ω)))
    (hX_g : X_g = fun s ω => (charX_g (clampT s) (proj_g ω), charV_g (clampT s) (proj_g ω)))
    (hmeas_f : ∀ s, Measurable (X_f s)) (hmeas_g : ∀ s, Measurable (X_g s))
    (dom : Ω → ℝ) (hdom_int : Integrable dom π₀)
    (hdom : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω, ‖X_f s ω - X_g s ω‖ ≤ dom ω) :
    Continuous (fun s => ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π₀) := by
  have hXf_cont_glob : ∀ ω, Continuous (fun s => X_f s ω) := by
    intro ω
    have : Continuous (fun s => (charX_f (clampT s) (proj_f ω), charV_f (clampT s) (proj_f ω))) :=
      (hcontIcc_f (proj_f ω)).comp_continuous hclampT_cont (fun s => hclampT_mem s)
    simpa only [hX_f] using this
  have hXg_cont_glob : ∀ ω, Continuous (fun s => X_g s ω) := by
    intro ω
    have : Continuous (fun s => (charX_g (clampT s) (proj_g ω), charV_g (clampT s) (proj_g ω))) :=
      (hcontIcc_g (proj_g ω)).comp_continuous hclampT_cont (fun s => hclampT_mem s)
    simpa only [hX_g] using this
  refine continuous_of_dominated
    (fun s => ((hmeas_f s).sub (hmeas_g s)).norm.aestronglyMeasurable)
    (fun s => Filter.Eventually.of_forall (fun ω => ?_))
    hdom_int
    (Filter.Eventually.of_forall (fun ω => ((hXf_cont_glob ω).sub (hXg_cont_glob ω)).norm))
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  have hcl : clampT s ∈ Set.Icc (0 : ℝ) T := hclampT_mem s
  have hXf : X_f s ω = X_f (clampT s) ω := by
    simp only [hX_f]; rw [hclampT_id (clampT s) hcl]
  have hXg : X_g s ω = X_g (clampT s) ω := by
    simp only [hX_g]; rw [hclampT_id (clampT s) hcl]
  rw [hXf, hXg]; exact hdom (clampT s) hcl ω

/-- **Cross-field bound**: the convolution-force difference of the two fields
along the second trajectory is bounded by `(max 1 L)` times the integrated
trajectory distance — established through the two marginal identities on the
common base `π₀`, never forming `wasserstein1 (f s) (g s)`. -/
private lemma dobrushinFlow_cross_field_bound
    {d : ℕ} [NeZero d] {Ω : Type*} [MeasurableSpace Ω]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (T : ℝ) (clampT : ℝ → ℝ)
    (hclampT_id : ∀ s ∈ Set.Icc (0 : ℝ) T, clampT s = s)
    (π₀ : Measure Ω)
    (f g : ℝ → Measure (PhaseSpace d))
    (charX_f charV_f charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    (proj_f proj_g : Ω → PhaseSpace d)
    (hproj_f : Measurable proj_f) (hproj_g : Measurable proj_g)
    (hpush_f : ∀ t ∈ Set.Icc (0 : ℝ) T,
      f t = Measure.map (fun z => (charX_f t z, charV_f t z)) (f 0))
    (haem_f : ∀ s ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => (charX_f s z, charV_f s z)) (f 0))
    (hpush_g : ∀ t ∈ Set.Icc (0 : ℝ) T,
      g t = Measure.map (fun z => (charX_g t z, charV_g t z)) (g 0))
    (haem_g : ∀ s ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => (charX_g s z, charV_g s z)) (g 0))
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hg_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (g t))
    (hmarg_f : f 0 = Measure.map proj_f π₀)
    (hmarg_g : g 0 = Measure.map proj_g π₀)
    (h_int_f : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (spatialMarginal (f t)))
    (h_int_g : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (spatialMarginal (g t)))
    (hmeas_charf : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Measurable (fun z : PhaseSpace d => (charX_f s z, charV_f s z)))
    (hmeas_charg : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Measurable (fun z : PhaseSpace d => (charX_g s z, charV_g s z)))
    (X_f X_g : ℝ → Ω → PhaseSpace d)
    (hX_f : X_f = fun s ω => (charX_f (clampT s) (proj_f ω), charV_f (clampT s) (proj_f ω)))
    (hX_g : X_g = fun s ω => (charX_g (clampT s) (proj_g ω), charV_g (clampT s) (proj_g ω)))
    (b_f b_g : ℝ → PhaseSpace d → PhaseSpace d)
    (hb_f_id : ∀ s ∈ Set.Icc (0 : ℝ) T,
      b_f s = vlasovVectorField gradW (fun s => spatialMarginal (f s)) s)
    (hb_g_id : ∀ s ∈ Set.Icc (0 : ℝ) T,
      b_g s = vlasovVectorField gradW (fun s => spatialMarginal (g s)) s)
    (hmeas_f : ∀ s, Measurable (X_f s)) (hmeas_g : ∀ s, Measurable (X_g s))
    (dom : Ω → ℝ) (hdom_int : Integrable dom π₀)
    (hdom : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω, ‖X_f s ω - X_g s ω‖ ≤ dom ω) :
    ∀ ω, ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖b_f s (X_g s ω) - b_g s (X_g s ω)‖ ≤
        ((max 1 L : NNReal) : ℝ) * ∫ ω', ‖X_f s ω' - X_g s ω'‖ ∂π₀ := by
  intro ω s hs
  have : IsProbabilityMeasure (f s) := (hf_mom s hs).1
  have : IsProbabilityMeasure (g s) := (hg_mom s hs).1
  have hL_le_max : (L : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by
    rw [NNReal.coe_max, NNReal.coe_one]; exact le_max_right _ _
  set x : PhysSpace d := (X_g s ω).1 with hx_def
  have hb_f_s := hb_f_id s hs
  have hb_g_s := hb_g_id s hs
  have h_form : b_f s (X_g s ω) - b_g s (X_g s ω) =
      ((0 : PhysSpace d),
       convolveFunctionMeasure gradW (spatialMarginal (g s)) x
         - convolveFunctionMeasure gradW (spatialMarginal (f s)) x) := by
    rw [hb_f_s, hb_g_s]
    simp only [vlasovVectorField, Prod.mk_sub_mk, sub_self, hx_def]
    refine Prod.ext rfl ?_
    change -(convolveFunctionMeasure gradW (spatialMarginal (f s)) (X_g s ω).1)
          - -(convolveFunctionMeasure gradW (spatialMarginal (g s)) (X_g s ω).1)
        = convolveFunctionMeasure gradW (spatialMarginal (g s)) (X_g s ω).1
          - convolveFunctionMeasure gradW (spatialMarginal (f s)) (X_g s ω).1
    abel
  rw [h_form, Prod.norm_def]
  simp only [norm_zero]
  rw [max_eq_right (norm_nonneg _)]
  rw [dobrushinFlow_conv_pushforward gradW L hL T charX_g charV_g g (g 0)
        hpush_g haem_g s hs x,
      dobrushinFlow_conv_pushforward gradW L hL T charX_f charV_f f (f 0)
        hpush_f haem_f s hs x]
  have hmeas_charf_s : Measurable (fun z : PhaseSpace d => charX_f s z) :=
    measurable_fst.comp (hmeas_charf s hs)
  have hmeas_charg_s : Measurable (fun z : PhaseSpace d => charX_g s z) :=
    measurable_fst.comp (hmeas_charg s hs)
  have hmap_g : (∫ ω', gradW (x - charX_g s ω') ∂(g 0))
      = ∫ ω, gradW (x - charX_g s (proj_g ω)) ∂π₀ := by
    rw [hmarg_g]
    exact integral_map hproj_g.aemeasurable
      (((hL.continuous.comp (continuous_const.sub continuous_id)).measurable.comp
        hmeas_charg_s).aestronglyMeasurable)
  have hmap_f : (∫ ω', gradW (x - charX_f s ω') ∂(f 0))
      = ∫ ω, gradW (x - charX_f s (proj_f ω)) ∂π₀ := by
    rw [hmarg_f]
    exact integral_map hproj_f.aemeasurable
      (((hL.continuous.comp (continuous_const.sub continuous_id)).measurable.comp
        hmeas_charf_s).aestronglyMeasurable)
  rw [hmap_g, hmap_f]
  have hint_g_π : Integrable (fun ω => gradW (x - charX_g s (proj_g ω))) π₀ := by
    have hbase : Integrable (fun ω' => gradW (x - charX_g s ω')) (g 0) :=
      dobrushinFlow_gradW_int_pushforward gradW L hL T charX_g charV_g g (g 0)
        hpush_g haem_g h_int_g s hs x
    rw [hmarg_g] at hbase
    exact (integrable_map_measure
      (((hL.continuous.comp (continuous_const.sub continuous_id)).measurable.comp
        hmeas_charg_s).aestronglyMeasurable) hproj_g.aemeasurable).mp hbase
  have hint_f_π : Integrable (fun ω => gradW (x - charX_f s (proj_f ω))) π₀ := by
    have hbase : Integrable (fun ω' => gradW (x - charX_f s ω')) (f 0) :=
      dobrushinFlow_gradW_int_pushforward gradW L hL T charX_f charV_f f (f 0)
        hpush_f haem_f h_int_f s hs x
    rw [hmarg_f] at hbase
    exact (integrable_map_measure
      (((hL.continuous.comp (continuous_const.sub continuous_id)).measurable.comp
        hmeas_charf_s).aestronglyMeasurable) hproj_f.aemeasurable).mp hbase
  rw [← integral_sub hint_g_π hint_f_π]
  have h_pt : ∀ ω, ‖gradW (x - charX_g s (proj_g ω)) - gradW (x - charX_f s (proj_f ω))‖
      ≤ (L : ℝ) * ‖charX_f s (proj_f ω) - charX_g s (proj_g ω)‖ := by
    intro ω
    have hd := hL.dist_le_mul (x - charX_g s (proj_g ω)) (x - charX_f s (proj_f ω))
    rw [dist_eq_norm, dist_eq_norm] at hd
    have hsub : (x - charX_g s (proj_g ω)) - (x - charX_f s (proj_f ω))
        = charX_f s (proj_f ω) - charX_g s (proj_g ω) := by abel
    rw [hsub] at hd; exact hd
  have hf_phase_int : Integrable
      (fun ω => ((charX_f s (proj_f ω), charV_f s (proj_f ω)) : PhaseSpace d)) π₀ := by
    have hbase : Integrable (fun ω' : PhaseSpace d => (charX_f s ω', charV_f s ω')) (f 0) :=
      dobrushinFlow_phase_int_pushforward T charX_f charV_f f (f 0)
        hpush_f haem_f (fun t ht => (hf_mom t ht).2) s hs
    rw [hmarg_f] at hbase
    exact (integrable_map_measure (hmeas_charf s hs).aestronglyMeasurable
      hproj_f.aemeasurable).mp hbase
  have hg_phase_int : Integrable
      (fun ω => ((charX_g s (proj_g ω), charV_g s (proj_g ω)) : PhaseSpace d)) π₀ := by
    have hbase : Integrable (fun ω' : PhaseSpace d => (charX_g s ω', charV_g s ω')) (g 0) :=
      dobrushinFlow_phase_int_pushforward T charX_g charV_g g (g 0)
        hpush_g haem_g (fun t ht => (hg_mom t ht).2) s hs
    rw [hmarg_g] at hbase
    exact (integrable_map_measure (hmeas_charg s hs).aestronglyMeasurable
      hproj_g.aemeasurable).mp hbase
  have hnorm_int_le :
      ‖∫ ω, (gradW (x - charX_g s (proj_g ω)) - gradW (x - charX_f s (proj_f ω))) ∂π₀‖
        ≤ ∫ ω, (L : ℝ) * ‖charX_f s (proj_f ω) - charX_g s (proj_g ω)‖ ∂π₀ := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine integral_mono (hint_g_π.sub hint_f_π).norm ?_ h_pt
    have hdiff_int : Integrable
        (fun ω => charX_f s (proj_f ω) - charX_g s (proj_g ω)) π₀ :=
      (hf_phase_int.fst).sub (hg_phase_int.fst)
    exact (hdiff_int.norm.const_mul (L : ℝ))
  refine le_trans hnorm_int_le ?_
  rw [integral_const_mul]
  have hpt2 : ∀ ω, ‖charX_f s (proj_f ω) - charX_g s (proj_g ω)‖ ≤ ‖X_f s ω - X_g s ω‖ := by
    intro ω
    have hXf : X_f s ω = (charX_f s (proj_f ω), charV_f s (proj_f ω)) := by
      simp only [hX_f, hclampT_id s hs]
    have hXg : X_g s ω = (charX_g s (proj_g ω), charV_g s (proj_g ω)) := by
      simp only [hX_g, hclampT_id s hs]
    rw [hXf, hXg]
    have hsplit : ((charX_f s (proj_f ω), charV_f s (proj_f ω)) : PhaseSpace d)
          - (charX_g s (proj_g ω), charV_g s (proj_g ω)) =
        ((charX_f s (proj_f ω) - charX_g s (proj_g ω)),
          (charV_f s (proj_f ω) - charV_g s (proj_g ω))) := by
      rw [Prod.mk_sub_mk]
    rw [hsplit, Prod.norm_def]; exact le_max_left _ _
  have hdiff_norm_int : Integrable
      (fun ω => ‖charX_f s (proj_f ω) - charX_g s (proj_g ω)‖) π₀ :=
    ((hf_phase_int.fst).sub (hg_phase_int.fst)).norm
  have hXdiff_norm_int : Integrable (fun ω => ‖X_f s ω - X_g s ω‖) π₀ :=
    Integrable.mono' hdom_int
      ((hmeas_f s).sub (hmeas_g s)).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hdom s hs ω)
  have hQ_le : ∫ ω, ‖charX_f s (proj_f ω) - charX_g s (proj_g ω)‖ ∂π₀
      ≤ ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π₀ :=
    integral_mono hdiff_norm_int hXdiff_norm_int hpt2
  calc (L : ℝ) * ∫ ω, ‖charX_f s (proj_f ω) - charX_g s (proj_g ω)‖ ∂π₀
      ≤ (L : ℝ) * ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π₀ :=
        mul_le_mul_of_nonneg_left hQ_le L.coe_nonneg
    _ ≤ ((max 1 L : NNReal) : ℝ) * ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π₀ :=
        mul_le_mul_of_nonneg_right hL_le_max (integral_nonneg fun _ => norm_nonneg _)

/-- Conclusion transfer: rewrite the integrated-coupling core's bound and the
associated integrability from the clamped `X`-form into the conclusion's
`proj`-form, using the initial-identity of the flows at `t = 0`. -/
private lemma dobrushinFlow_conclusion_transfer
    {d : ℕ} [NeZero d] {Ω : Type*} [MeasurableSpace Ω]
    (T : ℝ) (hT : 0 < T) (clampT : ℝ → ℝ)
    (hclampT_id : ∀ s ∈ Set.Icc (0 : ℝ) T, clampT s = s)
    (π₀ : Measure Ω) (L : NNReal)
    (charX_f charV_f charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    (proj_f proj_g : Ω → PhaseSpace d)
    (hinit_f' : ∀ z : PhaseSpace d, (charX_f 0 z, charV_f 0 z) = z)
    (hinit_g' : ∀ z : PhaseSpace d, (charX_g 0 z, charV_g 0 z) = z)
    (X_f X_g : ℝ → Ω → PhaseSpace d)
    (hX_f : X_f = fun s ω => (charX_f (clampT s) (proj_f ω), charV_f (clampT s) (proj_f ω)))
    (hX_g : X_g = fun s ω => (charX_g (clampT s) (proj_g ω), charV_g (clampT s) (proj_g ω)))
    (hmeas_f : ∀ s, Measurable (X_f s)) (hmeas_g : ∀ s, Measurable (X_g s))
    (dom : Ω → ℝ) (hdom_int : Integrable dom π₀)
    (hdom : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω, ‖X_f s ω - X_g s ω‖ ≤ dom ω)
    (hcore : ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫ ω, ‖X_f t ω - X_g t ω‖ ∂π₀) ≤
        (∫ ω, ‖X_f 0 ω - X_g 0 ω‖ ∂π₀) * Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun ω => ‖((charX_f t (proj_f ω), charV_f t (proj_f ω)) : PhaseSpace d)
              - (charX_g t (proj_g ω), charV_g t (proj_g ω))‖) π₀ ∧
      (∫ ω, ‖((charX_f t (proj_f ω), charV_f t (proj_f ω)) : PhaseSpace d)
              - (charX_g t (proj_g ω), charV_g t (proj_g ω))‖ ∂π₀)
        ≤ (∫ ω, ‖proj_f ω - proj_g ω‖ ∂π₀)
            * Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t) := by
  intro t ht
  have hbound := hcore t ht
  have hbase0 : (∫ ω, ‖X_f 0 ω - X_g 0 ω‖ ∂π₀) = ∫ ω, ‖proj_f ω - proj_g ω‖ ∂π₀ := by
    apply integral_congr_ae
    filter_upwards with ω
    have hXf0 : X_f 0 ω = proj_f ω := by
      simp only [hX_f, hclampT_id 0 ⟨le_refl 0, hT.le⟩]; exact hinit_f' (proj_f ω)
    have hXg0 : X_g 0 ω = proj_g ω := by
      simp only [hX_g, hclampT_id 0 ⟨le_refl 0, hT.le⟩]; exact hinit_g' (proj_g ω)
    rw [hXf0, hXg0]
  have hlhs : (∫ ω, ‖X_f t ω - X_g t ω‖ ∂π₀)
      = ∫ ω, ‖((charX_f t (proj_f ω), charV_f t (proj_f ω)) : PhaseSpace d)
             - (charX_g t (proj_g ω), charV_g t (proj_g ω))‖ ∂π₀ := by
    apply integral_congr_ae
    filter_upwards with ω
    have hXf : X_f t ω = (charX_f t (proj_f ω), charV_f t (proj_f ω)) := by
      simp only [hX_f, hclampT_id t ht]
    have hXg : X_g t ω = (charX_g t (proj_g ω), charV_g t (proj_g ω)) := by
      simp only [hX_g, hclampT_id t ht]
    rw [hXf, hXg]
  rw [hlhs, hbase0] at hbound
  refine ⟨?_, hbound⟩
  have hXfe : ∀ ω, X_f t ω = (charX_f t (proj_f ω), charV_f t (proj_f ω)) := fun ω => by
    simp only [hX_f, hclampT_id t ht]
  have hXge : ∀ ω, X_g t ω = (charX_g t (proj_g ω), charV_g t (proj_g ω)) := fun ω => by
    simp only [hX_g, hclampT_id t ht]
  have hint_t : Integrable (fun ω => ‖X_f t ω - X_g t ω‖) π₀ :=
    Integrable.mono' hdom_int
      ((hmeas_f t).sub (hmeas_g t)).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hdom t ht ω)
  simpa only [hXfe, hXge] using hint_t

/-- **Shared integrated-coupling core for the Dobrushin stability bound.**

Generalizes the body of `dobrushin_uniqueness_On` over an arbitrary base
coupling measure `π₀` on `Ω` with measurable projections
`proj_f, proj_g : Ω → PhaseSpace d` such that `f 0 = (proj_f)_# π₀` and
`g 0 = (proj_g)_# π₀`.  Trajectory families are `X_μ s ω := Φ_μ s (proj_μ ω)`.
Concludes the integrated trajectory-distance bound

  ∫ ω, ‖Φ_f t (proj_f ω) − Φ_g t (proj_g ω)‖ ∂π₀
    ≤ (∫ ω, ‖proj_f ω − proj_g ω‖ ∂π₀) · exp(2·(max 1 L)·t)

via `integrated_coupling_gronwall_bound` with the moment-free Lipschitz-in-`z`
dominator (`dom ω = e^{KT}(‖proj_f ω‖ + ‖proj_g ω‖) + (K_f + K_g)`, integrable
through the two marginal moments) and the force-estimate-free cross-field bound
(the convolution difference bounded pointwise by `gradW`-Lipschitz, integrated
against `π₀` through the two marginal identities — never forming
`wasserstein1 (f s) (g s)`).

Two consumers:
* `dobrushin_uniqueness_On` — `proj_f = proj_g = id`, `π₀ = f 0 = g 0`, so the
  RHS base integral is `0` and the conclusion collapses to `f t = g t`.
* the mean-field `dobrushin` — `proj_f = fst`, `proj_g = snd`, `π₀` an optimal
  coupling of `(f 0, g 0)`, so the RHS base integral is `W₁(f 0, g 0)` and the
  LHS dominates `W₁(f t, g t)` by the easy direction of Kantorovich–Rubinstein.

Base-generic: the only base-specific work is the two marginal identities
`hmarg_f`/`hmarg_g`; the flow regularity, dominator, and cross-field force bound
are established generically over `π₀`. -/
private theorem dobrushin_integrated_flow_bound_On
    {d : ℕ} [NeZero d]
    {Ω : Type*} [MeasurableSpace Ω]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (T : ℝ) (hT : 0 < T)
    (π₀ : Measure Ω) [IsProbabilityMeasure π₀]
    (proj_f proj_g : Ω → PhaseSpace d)
    (hproj_f : Measurable proj_f) (hproj_g : Measurable proj_g)
    (charX_f charV_f charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    (hinit_f : ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
        charX_f 0 z = z.1 ∧ charV_f 0 z = z.2)
    (hflow_f_x : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
        HasDerivAt (fun s' => charX_f s' z) (charV_f s z) s)
    (hflow_f_v : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
        HasDerivAt (fun s' => charV_f s' z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (f s)) (charX_f s z))) s)
    (hpush_f : ∀ t ∈ Set.Icc (0 : ℝ) T,
        f t = Measure.map (fun z => (charX_f t z, charV_f t z)) (f 0))
    (haem_f : ∀ s ∈ Set.Icc (0 : ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX_f s z, charV_f s z)) (f 0))
    (hcontIcc_f : ∀ ω, ContinuousOn (fun s => (charX_f s ω, charV_f s ω)) (Set.Icc 0 T))
    (hinit_g : ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
        charX_g 0 z = z.1 ∧ charV_g 0 z = z.2)
    (hflow_g_x : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
        HasDerivAt (fun s' => charX_g s' z) (charV_g s z) s)
    (hflow_g_v : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ z ∈ (Set.univ : Set (PhaseSpace d)),
        HasDerivAt (fun s' => charV_g s' z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (g s)) (charX_g s z))) s)
    (hpush_g : ∀ t ∈ Set.Icc (0 : ℝ) T,
        g t = Measure.map (fun z => (charX_g t z, charV_g t z)) (g 0))
    (haem_g : ∀ s ∈ Set.Icc (0 : ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX_g s z, charV_g s z)) (g 0))
    (hcontIcc_g : ∀ ω, ContinuousOn (fun s => (charX_g s ω, charV_g s ω)) (Set.Icc 0 T))
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hg_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (g t))
    (hmarg_f : f 0 = Measure.map proj_f π₀)
    (hmarg_g : g 0 = Measure.map proj_g π₀) :
    (∀ s ∈ Set.Icc (0 : ℝ) T,
        Measurable (fun z : PhaseSpace d => (charX_f s z, charV_f s z))) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) T,
        Measurable (fun z : PhaseSpace d => (charX_g s z, charV_g s z))) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun ω => ‖((charX_f t (proj_f ω), charV_f t (proj_f ω)) : PhaseSpace d)
              - (charX_g t (proj_g ω), charV_g t (proj_g ω))‖) π₀ ∧
      (∫ ω, ‖((charX_f t (proj_f ω), charV_f t (proj_f ω)) : PhaseSpace d)
              - (charX_g t (proj_g ω), charV_g t (proj_g ω))‖ ∂π₀)
        ≤ (∫ ω, ‖proj_f ω - proj_g ω‖ ∂π₀)
            * Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t) := by
  -- Probability instances.
  have hf_isProb : ∀ t ∈ Set.Icc (0 : ℝ) T, IsProbabilityMeasure (f t) :=
    fun t ht => (hf_mom t ht).1
  have hg_isProb : ∀ t ∈ Set.Icc (0 : ℝ) T, IsProbabilityMeasure (g t) :=
    fun t ht => (hg_mom t ht).1
  have hf0_prob : IsProbabilityMeasure (f 0) := (hf_mom 0 ⟨le_refl 0, hT.le⟩).1
  have hg0_prob : IsProbabilityMeasure (g 0) := (hg_mom 0 ⟨le_refl 0, hT.le⟩).1
  -- Clamp into [0, T].
  set clampT : ℝ → ℝ := (fun s => max 0 (min s T)) with hclampT_def
  have hclampT_mem : ∀ s, clampT s ∈ Set.Icc (0 : ℝ) T := by
    intro s; simp only [hclampT_def, Set.mem_Icc]
    exact ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩
  have hclampT_id : ∀ s ∈ Set.Icc (0 : ℝ) T, clampT s = s := by
    intro s hs; simp only [hclampT_def, min_eq_left hs.2, max_eq_right hs.1]
  -- Clamped trajectory families over the base `Ω`, read through the projections.
  set X_f : ℝ → Ω → PhaseSpace d :=
    fun s ω => (charX_f (clampT s) (proj_f ω), charV_f (clampT s) (proj_f ω)) with hX_f_def
  set X_g : ℝ → Ω → PhaseSpace d :=
    fun s ω => (charX_g (clampT s) (proj_g ω), charV_g (clampT s) (proj_g ω)) with hX_g_def
  -- Clamped Vlasov vector fields.
  set b_f : ℝ → PhaseSpace d → PhaseSpace d :=
    fun s => vlasovVectorField gradW (fun s => spatialMarginal (f (clampT s))) s
    with hb_f_def
  set b_g : ℝ → PhaseSpace d → PhaseSpace d :=
    fun s => vlasovVectorField gradW (fun s => spatialMarginal (g (clampT s))) s
    with hb_g_def
  -- gradW-kernel integrability on the spatial marginals (window-generic over μ).
  have h_int_helper := dobrushinFlow_marginal_gradW_integrable gradW L hL T
  have h_int_f := h_int_helper f hf_mom
  have h_int_g := h_int_helper g hg_mom
  have hfc_int : ∀ s (x : PhysSpace d),
      Integrable (fun y => gradW (x - y)) (spatialMarginal (f (clampT s))) :=
    fun s x => h_int_f (clampT s) (hclampT_mem s) x
  have hgc_int : ∀ s (x : PhysSpace d),
      Integrable (fun y => gradW (x - y)) (spatialMarginal (g (clampT s))) :=
    fun s x => h_int_g (clampT s) (hclampT_mem s) x
  have hfc_isProb : ∀ s, IsProbabilityMeasure (spatialMarginal (f (clampT s))) := by
    intro s; have := hf_isProb (clampT s) (hclampT_mem s)
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hgc_isProb : ∀ s, IsProbabilityMeasure (spatialMarginal (g (clampT s))) := by
    intro s; have := hg_isProb (clampT s) (hclampT_mem s)
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  -- Universal (max 1 L)-Lipschitz of the clamped vector fields.
  have hL_f : ∀ s, LipschitzWith (max 1 L) (b_f s) := fun s =>
    vlasovVectorField_lipschitzWith gradW L hL
      (fun s => spatialMarginal (f (clampT s))) hfc_int s
  have hL_g : ∀ s, LipschitzWith (max 1 L) (b_g s) := fun s =>
    vlasovVectorField_lipschitzWith gradW L hL
      (fun s => spatialMarginal (g (clampT s))) hgc_int s
  -- On [0, T] the clamped field coincides with the genuine field.
  have hb_f_id := dobrushinFlow_clamped_field_id gradW T clampT hclampT_id f b_f hb_f_def
  have hb_g_id := dobrushinFlow_clamped_field_id gradW T clampT hclampT_id g b_g hb_g_def
  -- Open-window flow ODE in z (HasDerivWithinAt on `Ici s`, `s ∈ Ioo 0 T`).
  have hderiv_Ioo_f := dobrushinFlow_deriv_Ioo gradW T clampT hclampT_id f
    charX_f charV_f hflow_f_x hflow_f_v
  have hderiv_Ioo_g := dobrushinFlow_deriv_Ioo gradW T clampT hclampT_id g
    charX_g charV_g hflow_g_x hflow_g_v
  have hinit_f' : ∀ z : PhaseSpace d, (charX_f 0 z, charV_f 0 z) = z := by
    intro z; obtain ⟨hx, hv⟩ := hinit_f z (Set.mem_univ z); rw [hx, hv]
  have hinit_g' : ∀ z : PhaseSpace d, (charX_g 0 z, charV_g 0 z) = z := by
    intro z; obtain ⟨hx, hv⟩ := hinit_g z (Set.mem_univ z); rw [hx, hv]
  have hmeas_charf : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Measurable (fun z : PhaseSpace d => (charX_f s z, charV_f s z)) :=
    charFlow_measurable_via_gronwall_Ioo gradW L hL
      (fun s => spatialMarginal (f (clampT s))) hfc_int charX_f charV_f T hT.le
      hinit_f' hcontIcc_f hderiv_Ioo_f
  have hmeas_charg : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Measurable (fun z : PhaseSpace d => (charX_g s z, charV_g s z)) :=
    charFlow_measurable_via_gronwall_Ioo gradW L hL
      (fun s => spatialMarginal (g (clampT s))) hgc_int charX_g charV_g T hT.le
      hinit_g' hcontIcc_g hderiv_Ioo_g
  -- Universal-in-`s` measurability of the clamped flows (clampT s ∈ [0,T]),
  -- composed with the (measurable) projections to land on `Ω`.
  have hmeas_f : ∀ s, Measurable (X_f s) := by
    intro s
    simpa only [hX_f_def, Function.comp_def] using
      (hmeas_charf (clampT s) (hclampT_mem s)).comp hproj_f
  have hmeas_g : ∀ s, Measurable (X_g s) := by
    intro s
    simpa only [hX_g_def, Function.comp_def] using
      (hmeas_charg (clampT s) (hclampT_mem s)).comp hproj_g
  have hclampT_cont : Continuous clampT :=
    continuous_const.max (continuous_id.min continuous_const)
  -- Per-ω continuity of the clamped trajectories on [0, T].
  have hcont_f := dobrushinFlow_clamped_cont T clampT hclampT_cont hclampT_mem
    hclampT_id charX_f charV_f proj_f hcontIcc_f X_f hX_f_def
  have hcont_g := dobrushinFlow_clamped_cont T clampT hclampT_cont hclampT_mem
    hclampT_id charX_g charV_g proj_g hcontIcc_g X_g hX_g_def
  -- Per-ω ODE of the clamped trajectories on Ioo 0 T (HasDerivWithinAt Ioi).
  have hderiv_f := dobrushinFlow_clamped_deriv gradW T clampT hclampT_id f
    charX_f charV_f proj_f hflow_f_x hflow_f_v b_f hb_f_id X_f hX_f_def
  have hderiv_g := dobrushinFlow_clamped_deriv gradW T clampT hclampT_id g
    charX_g charV_g proj_g hflow_g_x hflow_g_v b_g hb_g_id X_g hX_g_def
  -- Moment-free dominator: `dom ω = e^{KT}(‖proj_f ω‖ + ‖proj_g ω‖) + (K_f + K_g)`.
  set K : NNReal := max 1 L with hK_def
  have hK_nn : (0 : ℝ) ≤ ((K : NNReal) : ℝ) := K.coe_nonneg
  set EKT : ℝ := Real.exp (((K : NNReal) : ℝ) * T) with hEKT_def
  have hlip_f : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
      dist ((charX_f s z₁, charV_f s z₁) : PhaseSpace d) (charX_f s z₂, charV_f s z₂) ≤
      dist z₁ z₂ * Real.exp (((K : NNReal) : ℝ) * (s - 0)) :=
    charFlow_lipschitzInZ_via_gronwall_Ioo gradW L hL
      (fun s => spatialMarginal (f (clampT s))) hfc_int charX_f charV_f T hT.le
      hinit_f' hcontIcc_f hderiv_Ioo_f
  have hlip_g : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
      dist ((charX_g s z₁, charV_g s z₁) : PhaseSpace d) (charX_g s z₂, charV_g s z₂) ≤
      dist z₁ z₂ * Real.exp (((K : NNReal) : ℝ) * (s - 0)) :=
    charFlow_lipschitzInZ_via_gronwall_Ioo gradW L hL
      (fun s => spatialMarginal (g (clampT s))) hgc_int charX_g charV_g T hT.le
      hinit_g' hcontIcc_g hderiv_Ioo_g
  obtain ⟨K_f, hK_f_nn, hK_f⟩ :=
    dobrushinFlow_origin_trajectory_bound T charX_f charV_f (hcontIcc_f 0)
  obtain ⟨K_g, hK_g_nn, hK_g⟩ :=
    dobrushinFlow_origin_trajectory_bound T charX_g charV_g (hcontIcc_g 0)
  have hfnorm : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω : PhaseSpace d,
      ‖(charX_f s ω, charV_f s ω)‖ ≤ EKT * ‖ω‖ + K_f := by
    rw [hEKT_def]
    exact dobrushinFlow_flow_norm_bound T K charX_f charV_f K_f hlip_f hK_f
  have hgnorm : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω : PhaseSpace d,
      ‖(charX_g s ω, charV_g s ω)‖ ≤ EKT * ‖ω‖ + K_g := by
    rw [hEKT_def]
    exact dobrushinFlow_flow_norm_bound T K charX_g charV_g K_g hlip_g hK_g
  set dom : Ω → ℝ := fun ω => EKT * ‖proj_f ω‖ + EKT * ‖proj_g ω‖ + (K_f + K_g) with hdom_def
  have hmom_f : Integrable (fun ω : Ω => ‖proj_f ω‖) π₀ :=
    dobrushinFlow_proj_moment π₀ proj_f hproj_f (f 0) hmarg_f
      (hf_mom 0 ⟨le_refl 0, hT.le⟩).2
  have hmom_g : Integrable (fun ω : Ω => ‖proj_g ω‖) π₀ :=
    dobrushinFlow_proj_moment π₀ proj_g hproj_g (g 0) hmarg_g
      (hg_mom 0 ⟨le_refl 0, hT.le⟩).2
  have hdom_int : Integrable dom π₀ := by
    simp only [hdom_def]
    exact ((hmom_f.const_mul EKT).add (hmom_g.const_mul EKT)).add (integrable_const _)
  have hdom : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω, ‖X_f s ω - X_g s ω‖ ≤ dom ω := by
    simp only [hdom_def]
    exact dobrushinFlow_dominator_bound T clampT hclampT_id charX_f charV_f
      charX_g charV_g proj_f proj_g EKT K_f K_g hfnorm hgnorm X_f X_g hX_f_def hX_g_def
  -- Cross-field bound ε and its self-reference to Q (over the base π₀).
  set Q : ℝ → ℝ := fun s => ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π₀ with hQ_def
  set ε : ℝ → ℝ := fun s => ((max 1 L : NNReal) : ℝ) * Q s with hε_def
  have hQ_cont : ContinuousOn Q (Set.Icc 0 T) := by
    have hQglob : Continuous Q := by
      simp only [hQ_def]
      exact dobrushinFlow_Q_continuous T clampT hclampT_cont hclampT_mem hclampT_id
        π₀ charX_f charV_f charX_g charV_g proj_f proj_g hcontIcc_f hcontIcc_g
        X_f X_g hX_f_def hX_g_def hmeas_f hmeas_g dom hdom_int hdom
    exact hQglob.continuousOn
  have hε_int : IntervalIntegrable ε MeasureTheory.volume 0 T := by
    have hεcont : ContinuousOn ε (Set.Icc 0 T) := by
      simp only [hε_def]; exact continuousOn_const.mul hQ_cont
    exact hεcont.intervalIntegrable_of_Icc hT.le
  have hε_nn : ∀ s ∈ Set.Icc (0 : ℝ) T, 0 ≤ ε s := by
    intro s _; simp only [hε_def]
    exact mul_nonneg (le_trans zero_le_one
      (by rw [NNReal.coe_max, NNReal.coe_one]; exact le_max_left _ _))
      (integral_nonneg (fun ω => norm_nonneg _))
  have h_self : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ε s ≤ ((max 1 L : NNReal) : ℝ) * ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π₀ := by
    intro s _; exact le_refl _
  have hint : ∀ ω, IntervalIntegrable
      (fun s => b_f s (X_f s ω) - b_g s (X_g s ω)) MeasureTheory.volume 0 T := by
    intro ω
    have hcf : Continuous (fun s => b_f s (X_f s ω)) := by
      have h := dobrushinFlow_field_continuous gradW L hL T K clampT hclampT_mem
        charX_f charV_f f (f 0) K_f b_f
        (fun s z => (charX_f (clampT s) z, charV_f (clampT s) z)) hb_f_def rfl
        (fun z => (hcontIcc_f z).comp_continuous hclampT_cont (fun s => hclampT_mem s))
        hpush_f haem_f hf0_prob (hf_mom 0 ⟨le_refl 0, hT.le⟩).2 hK_f hlip_f (proj_f ω)
      simpa only [hX_f_def] using h
    have hcg : Continuous (fun s => b_g s (X_g s ω)) := by
      have h := dobrushinFlow_field_continuous gradW L hL T K clampT hclampT_mem
        charX_g charV_g g (g 0) K_g b_g
        (fun s z => (charX_g (clampT s) z, charV_g (clampT s) z)) hb_g_def rfl
        (fun z => (hcontIcc_g z).comp_continuous hclampT_cont (fun s => hclampT_mem s))
        hpush_g haem_g hg0_prob (hg_mom 0 ⟨le_refl 0, hT.le⟩).2 hK_g hlip_g (proj_g ω)
      simpa only [hX_g_def] using h
    exact ((hcf.sub hcg).continuousOn).intervalIntegrable_of_Icc hT.le
  -- Cross-field bound: convolution difference bounded pointwise by the coupled
  -- trajectory distance, integrated against `π₀` through the two marginals.
  have h_diff : ∀ ω, ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖b_f s (X_g s ω) - b_g s (X_g s ω)‖ ≤ ε s := by
    simp only [hε_def, hQ_def]
    exact dobrushinFlow_cross_field_bound gradW L hL T clampT hclampT_id π₀ f g
      charX_f charV_f charX_g charV_g proj_f proj_g hproj_f hproj_g
      hpush_f haem_f hpush_g haem_g hf_mom hg_mom hmarg_f hmarg_g
      h_int_f h_int_g hmeas_charf hmeas_charg X_f X_g hX_f_def hX_g_def
      b_f b_g hb_f_id hb_g_id hmeas_f hmeas_g dom hdom_int hdom
  -- Apply the integrated collapse core.
  have hcore := integrated_coupling_gronwall_bound π₀ X_f X_g b_f b_g
    (max 1 L) T hT.le hL_f hcont_f hcont_g hderiv_f hderiv_g hint
    hmeas_f hmeas_g dom hdom_int hdom ε hε_int hε_nn h_diff h_self
  refine ⟨hmeas_charf, hmeas_charg, ?_⟩
  exact dobrushinFlow_conclusion_transfer T hT clampT hclampT_id π₀ L
    charX_f charV_f charX_g charV_g proj_f proj_g hinit_f' hinit_g'
    X_f X_g hX_f_def hX_g_def hmeas_f hmeas_g dom hdom_int hdom hcore

/-- **Localized Dobrushin uniqueness on `[0, T]`** for two
`IsLagrangianVlasovSolutionOn` solutions with the same initial data and
finite first moments.

**Why the Lagrangian class**: the weak `IsVlasovSolutionOn` class cannot
soundly carry this conclusion:
the Gronwall step (`wassersteinGronwallCoupling_gronwall_le`) demands
`ContinuousOn (Icc 0 T)` of `t ↦ (W₁ (f t) (g t)).toReal` — *closed* interval
— but `IsVlasovSolutionOn` constrains the weak PDE only on the *open*
`Ioo 0 T`, leaving the endpoint values `f T`, `g T` free (a weak solution may
jump at `t = T`).  So closed-window W₁-continuity is not a consequence of the
weak class.  Realigning to `IsLagrangianVlasovSolutionOn` fixes this: the
flow witness supplies `f t = (charX t)_# (f 0)` on the closed `Icc 0 T` plus
boundary flow regularity, pinning the endpoints.  (Uniqueness over the weak
class would need the DiPerna-Lions superposition principle, out of scope.)
The caller `vlasovWellPosedness_uniqueness` already holds the Lagrangian
witness, so this is zero-cost upstream.

**Closure path (via the integrated-coupling core)**:
the proof wires through `integrated_coupling_gronwall_bound` instead of the
W₁-continuity + right-derivative-liminf + Gronwall chain.  Set
`μ₀ := f 0 = g 0` and let `Φ_f, Φ_g` be the (clamped)
characteristic flows.  The core bounds the integrated trajectory distance
`Q t := ∫ ω, ‖Φ_f t ω − Φ_g t ω‖ ∂μ₀` by `Q 0 · exp(2 (max 1 L) t)`; since the
flows start at the identity, `Q 0 = 0`, so `Q t ≤ 0`.  Hence `Φ_f t = Φ_g t`
μ₀-a.e., and `f t = (Φ_f t)_# μ₀ = (Φ_g t)_# μ₀ = g t` by `Measure.map_congr`.

The crux input is the cross-field bound `h_diff`, established directly from the
pushforward identity `spatialMarginal (f s) = (charX_f s)_# μ₀` + `gradW`
Lipschitz under the integral (two `integral_map` steps) — it never forms
`wasserstein1 (f s) (g s)`.

The measurability and the dominator route through the *open-interval* helpers
(`charFlow_measurable_via_gronwall_Ioo` /
`charFlow_lipschitzInZ_via_gronwall_Ioo`), which consume only the witness ODE
on `Ioo 0 T`:
* the `s = 0` right-derivatives (`hderivIco_f`/`hderivIco_g`) are no longer
  needed — the `Ioo`-only flow ODE (`hderiv_Ioo_f`/`hderiv_Ioo_g`) suffices;
* the uniform-in-`s` first-moment envelope (`Mf`/`Mg`) and
  `flow_distance_growth_bound_on` are replaced by a moment-free dominator
  `dom ω = 2 e^{KT} ‖ω‖ + (K_f + K_g)` built from the flow's Lipschitz-in-`z`
  bound + compactness of the origin trajectory on `[0, T]`; it uses ONLY
  `f 0`'s initial first moment;
* the per-`ω` interval-integrability (`hint`) is closed by global continuity in
  `s` of each clamped field (velocity slot continuous; force slot a
  pushforward integral, continuous via moment-free DCT). -/
private theorem dobrushin_uniqueness_On
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (T : ℝ) (hT : 0 < T)
    (hf : IsLagrangianVlasovSolutionOn gradW f T)
    (hg : IsLagrangianVlasovSolutionOn gradW g T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hg_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (g t))
    (hfg0 : f 0 = g 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, f t = g t := by
  -- Routed through the shared `dobrushin_integrated_flow_bound_On` core with
  -- the **diagonal** coupling `π₀ = f 0` and `proj_f = proj_g = id`.
  -- Then the RHS base integral `∫ ‖id ω − id ω‖ = 0`, so the integrated bound
  -- forces `Φ_f t = Φ_g t` `f 0`-a.e., hence
  -- `f t = (Φ_f t)_# (f 0) = (Φ_g t)_# (f 0) = g t`.
  have hf0_prob : IsProbabilityMeasure (f 0) := (hf_mom 0 ⟨le_refl 0, hT.le⟩).1
  obtain ⟨_, charX_f, charV_f, hflow_f, hpush_f, haem_f, hcontIcc_f⟩ := hf
  obtain ⟨_, charX_g, charV_g, hflow_g, hpush_g, haem_g, hcontIcc_g⟩ := hg
  obtain ⟨hinit_f, hflow_f_x, hflow_f_v⟩ := hflow_f
  obtain ⟨hinit_g, hflow_g_x, hflow_g_v⟩ := hflow_g
  have hmarg_f : f 0 = Measure.map id (f 0) := by rw [Measure.map_id]
  have hmarg_g : g 0 = Measure.map id (f 0) := by rw [Measure.map_id, hfg0]
  have hcore := dobrushin_integrated_flow_bound_On gradW L hL f g T hT
    (f 0) id id measurable_id measurable_id
    charX_f charV_f charX_g charV_g
    hinit_f hflow_f_x hflow_f_v hpush_f haem_f hcontIcc_f
    hinit_g hflow_g_x hflow_g_v hpush_g haem_g hcontIcc_g
    hf_mom hg_mom hmarg_f hmarg_g
  obtain ⟨_, _, hmain⟩ := hcore
  intro t ht
  obtain ⟨hint_t, hbound⟩ := hmain t ht
  have hrhs0 : (∫ ω, ‖(id ω : PhaseSpace d) - id ω‖ ∂(f 0)) = 0 := by
    simp only [id_eq, sub_self, norm_zero, integral_zero]
  rw [hrhs0, zero_mul] at hbound
  simp only [id_eq] at hint_t hbound
  have hnn : 0 ≤ ∫ ω, ‖((charX_f t ω, charV_f t ω) : PhaseSpace d)
      - (charX_g t ω, charV_g t ω)‖ ∂(f 0) :=
    integral_nonneg (fun ω => norm_nonneg _)
  have hz : (∫ ω, ‖((charX_f t ω, charV_f t ω) : PhaseSpace d)
      - (charX_g t ω, charV_g t ω)‖ ∂(f 0)) = 0 := le_antisymm hbound hnn
  have hae_zero : (fun ω => ‖((charX_f t ω, charV_f t ω) : PhaseSpace d)
      - (charX_g t ω, charV_g t ω)‖) =ᵐ[f 0] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω => norm_nonneg _) hint_t).mp hz
  have hflow_ae : (fun ω => ((charX_f t ω, charV_f t ω) : PhaseSpace d))
      =ᵐ[f 0] (fun ω => (charX_g t ω, charV_g t ω)) := by
    filter_upwards [hae_zero] with ω hω
    have hnz : ‖((charX_f t ω, charV_f t ω) : PhaseSpace d)
        - (charX_g t ω, charV_g t ω)‖ = 0 := hω
    exact sub_eq_zero.mp (norm_eq_zero.mp hnz)
  have hpush_g' : g t = Measure.map (fun z => (charX_g t z, charV_g t z)) (f 0) := by
    rw [hpush_g t ht, hfg0]
  rw [hpush_f t ht, hpush_g']
  exact Measure.map_congr hflow_ae

/-- **Mean-field Dobrushin stability on the window `[0, T]`**, in the *primal
coupling* metric.

Concludes `W₁(f t, g t) ≤ exp(2·(max 1 L)·t) · wasserstein1Coupling (f 0, g 0)`
— the dual `W₁` on the LHS, the *coupling-inf* metric on the RHS (= Dobrushin's
metric ρbar).  Proved **without Foundation B**: for *every* coupling `π` of
`(f 0, g 0)` the shared `dobrushin_integrated_flow_bound_On` core (coupling-
generic in `(π, proj_f, proj_g)`) gives
  `W₁(f t, g t) ≤ ∫⁻ edist d(pushforward π) ≤ exp(…) · ∫⁻ edist z.1 z.2 ∂π`,
the first step by the easy direction of Kantorovich–Rubinstein
(`wasserstein1_pushforward_le_iInf`).  Taking `le_iInf` over couplings (the
constant `exp(…) ∈ (0,∞)` pulled through via `ENNReal.div_le_iff_le_mul`) yields
the coupling-metric RHS — **no optimal coupling / attainment needed** (cf.
Dobrushin 1979, eq. 6.8, ε-optimal couplings).  The all-dual form is recovered
downstream (`dobrushin`) via the single labelled `wasserstein1_eq_coupling`
duality bridge — the project's lone Foundation-B use.

Force-estimate-free: never forms a force estimate, never touches the
`W₁`-continuity / right-derivative route. -/
private theorem dobrushin_meanfield_On
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (T : ℝ) (hT : 0 < T)
    (hf : IsLagrangianVlasovSolutionOn gradW f T)
    (hg : IsLagrangianVlasovSolutionOn gradW g T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hg_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (g t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      wasserstein1 (f t) (g t)
        ≤ ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t))
            * wasserstein1Coupling (f 0) (g 0) := by
  have hf0_prob : IsProbabilityMeasure (f 0) := (hf_mom 0 ⟨le_refl 0, hT.le⟩).1
  have hg0_prob : IsProbabilityMeasure (g 0) := (hg_mom 0 ⟨le_refl 0, hT.le⟩).1
  obtain ⟨_, charX_f, charV_f, hflow_f, hpush_f, haem_f, hcontIcc_f⟩ := hf
  obtain ⟨_, charX_g, charV_g, hflow_g, hpush_g, haem_g, hcontIcc_g⟩ := hg
  obtain ⟨hinit_f, hflow_f_x, hflow_f_v⟩ := hflow_f
  obtain ⟨hinit_g, hflow_g_x, hflow_g_v⟩ := hflow_g
  intro t ht
  have hft_prob : IsProbabilityMeasure (f t) := (hf_mom t ht).1
  have hgt_prob : IsProbabilityMeasure (g t) := (hg_mom t ht).1
  have hft : Measure.map (fun z => (charX_f t z, charV_f t z)) (f 0) = f t :=
    (hpush_f t ht).symm
  have hgt : Measure.map (fun z => (charX_g t z, charV_g t z)) (g 0) = g t :=
    (hpush_g t ht).symm
  have hft_fm : Integrable (fun y => dist y (0 : PhaseSpace d)) (f t) := by
    simpa only [dist_zero_right] using (hf_mom t ht).2
  have hgt_fm : Integrable (fun y => dist y (0 : PhaseSpace d)) (g t) := by
    simpa only [dist_zero_right] using (hg_mom t ht).2
  have hc_ne0 :
      ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hc_neTop :
      ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t)) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have h_per : ∀ (π : Measure (PhaseSpace d × PhaseSpace d)),
      IsCoupling π (f 0) (g 0) →
      wasserstein1 (f t) (g t)
        ≤ ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t))
            * ∫⁻ z, edist z.1 z.2 ∂π := by
    intro π hπ
    have hπ_prob : IsProbabilityMeasure π := by
      constructor
      have hmap : (Measure.map Prod.fst π) Set.univ = (1 : ENNReal) := by
        rw [hπ.1, measure_univ]
      rwa [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] at hmap
    have hmarg_f : f 0 = Measure.map Prod.fst π := hπ.1.symm
    have hmarg_g : g 0 = Measure.map Prod.snd π := hπ.2.symm
    obtain ⟨hmeas_charf, hmeas_charg, hmain⟩ :=
      dobrushin_integrated_flow_bound_On gradW L hL f g T hT
        π Prod.fst Prod.snd measurable_fst measurable_snd
        charX_f charV_f charX_g charV_g
        hinit_f hflow_f_x hflow_f_v hpush_f haem_f hcontIcc_f
        hinit_g hflow_g_x hflow_g_v hpush_g haem_g hcontIcc_g
        hf_mom hg_mom hmarg_f hmarg_g
    obtain ⟨hint_t, hbound⟩ := hmain t ht
    have hmom_fst : Integrable (fun ω : PhaseSpace d × PhaseSpace d => ‖ω.1‖) π := by
      have hm : Integrable (fun z : PhaseSpace d => ‖z‖) (Measure.map Prod.fst π) := by
        rw [← hmarg_f]; exact (hf_mom 0 ⟨le_refl 0, hT.le⟩).2
      exact (integrable_map_measure continuous_norm.aestronglyMeasurable
        measurable_fst.aemeasurable).mp hm
    have hmom_snd : Integrable (fun ω : PhaseSpace d × PhaseSpace d => ‖ω.2‖) π := by
      have hm : Integrable (fun z : PhaseSpace d => ‖z‖) (Measure.map Prod.snd π) := by
        rw [← hmarg_g]; exact (hg_mom 0 ⟨le_refl 0, hT.le⟩).2
      exact (integrable_map_measure continuous_norm.aestronglyMeasurable
        measurable_snd.aemeasurable).mp hm
    have hbase_int : Integrable (fun ω : PhaseSpace d × PhaseSpace d => ‖ω.1 - ω.2‖) π :=
      Integrable.mono' (hmom_fst.add hmom_snd)
        ((measurable_fst.sub measurable_snd).norm.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_of_nonneg (norm_nonneg _)]; exact norm_sub_le _ _)
    have h_push := wasserstein1_pushforward_le_iInf
      (fun z => (charX_f t z, charV_f t z)) (fun z => (charX_g t z, charV_g t z))
      (hmeas_charf t ht) (hmeas_charg t ht) (f 0) (g 0) 0
      (by rw [hft]; infer_instance) (by rw [hgt]; infer_instance)
      (by rw [hft]; exact hft_fm) (by rw [hgt]; exact hgt_fm)
    rw [hft, hgt] at h_push
    have h_iInf_le :
        (⨅ (π' : Measure (PhaseSpace d × PhaseSpace d)) (_ : IsCoupling π' (f 0) (g 0)),
          ∫⁻ z, edist (charX_f t z.1, charV_f t z.1) (charX_g t z.2, charV_g t z.2) ∂π')
          ≤ ∫⁻ z, edist (charX_f t z.1, charV_f t z.1) (charX_g t z.2, charV_g t z.2) ∂π :=
      iInf_le_of_le π (iInf_le _ hπ)
    have hWt_lint : wasserstein1 (f t) (g t)
        ≤ ∫⁻ z, edist (charX_f t z.1, charV_f t z.1) (charX_g t z.2, charV_g t z.2) ∂π :=
      le_trans h_push h_iInf_le
    have hlint_eq :
        (∫⁻ z, edist (charX_f t z.1, charV_f t z.1) (charX_g t z.2, charV_g t z.2) ∂π)
          = ENNReal.ofReal (∫ ω, ‖((charX_f t ω.1, charV_f t ω.1) : PhaseSpace d)
              - (charX_g t ω.2, charV_g t ω.2)‖ ∂π) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint_t
        (Filter.Eventually.of_forall fun ω => norm_nonneg _)]
      refine lintegral_congr fun z => ?_
      rw [edist_dist, dist_eq_norm]
    rw [hlint_eq] at hWt_lint
    refine le_trans hWt_lint ?_
    calc ENNReal.ofReal (∫ ω, ‖((charX_f t ω.1, charV_f t ω.1) : PhaseSpace d)
              - (charX_g t ω.2, charV_g t ω.2)‖ ∂π)
        ≤ ENNReal.ofReal ((∫ ω, ‖ω.1 - ω.2‖ ∂π)
            * Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t)) :=
          ENNReal.ofReal_le_ofReal hbound
      _ = ENNReal.ofReal (∫ ω, ‖ω.1 - ω.2‖ ∂π)
            * ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t)) :=
          ENNReal.ofReal_mul (integral_nonneg fun _ => norm_nonneg _)
      _ = ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t))
            * ENNReal.ofReal (∫ ω, ‖ω.1 - ω.2‖ ∂π) := mul_comm _ _
      _ = ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t))
            * ∫⁻ z, edist z.1 z.2 ∂π := by
          rw [ofReal_integral_eq_lintegral_ofReal hbase_int
            (Filter.Eventually.of_forall fun ω => norm_nonneg _)]
          refine congrArg
            (fun w => ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t)) * w) ?_
          refine lintegral_congr fun z => ?_
          rw [edist_dist, dist_eq_norm]
  -- Take the iInf over couplings of (f 0, g 0).
  rw [show wasserstein1Coupling (f 0) (g 0)
        = ⨅ (π : Measure (PhaseSpace d × PhaseSpace d)) (_ : IsCoupling π (f 0) (g 0)),
            ∫⁻ z, edist z.1 z.2 ∂π from rfl, mul_comm,
    ← ENNReal.div_le_iff_le_mul (Or.inl hc_ne0) (Or.inl hc_neTop)]
  refine le_iInf fun π => le_iInf fun hπ => ?_
  rw [ENNReal.div_le_iff_le_mul (Or.inl hc_ne0) (Or.inl hc_neTop), mul_comm]
  exact h_per π hπ

/-- **Uniqueness on the local window**.

Two `IsLagrangianVlasovSolutionOn`s with the same initial data agree on
`[0, T_target]`.

**Proof** (closed via Dobrushin uniqueness composition):

1. Extract `IsVlasovSolutionOn` from each `IsLagrangianVlasovSolutionOn`.
2. Note `f 0 = f₀ = g 0` from the init hypotheses.
3. Apply `dobrushin_uniqueness_On` (localized Dobrushin uniqueness, the
   private helper above) to conclude `f t = g t`. -/
theorem vlasovWellPosedness_uniqueness
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (_hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d))
    (_hf₀ : HasFiniteFirstMoment f₀)
    {T_target : ℝ} (hT_target : 0 < T_target)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf_init : f 0 = f₀) (hg_init : g 0 = f₀)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T_target, HasFiniteFirstMoment (f t))
    (hg_mom : ∀ t ∈ Set.Icc (0 : ℝ) T_target, HasFiniteFirstMoment (g t))
    (hf_lag : IsLagrangianVlasovSolutionOn gradW f T_target)
    (hg_lag : IsLagrangianVlasovSolutionOn gradW g T_target) :
    ∀ t ∈ Set.Icc (0 : ℝ) T_target, f t = g t := by
  -- The two solutions share the same initial datum f₀
  have hfg0 : f 0 = g 0 := hf_init.trans hg_init.symm
  -- Apply the localized Dobrushin uniqueness (Helper above).  Pass the full
  -- Lagrangian witness directly (post-realignment, item 3 is over the
  -- Lagrangian-On class for soundness — see its docstring).
  exact dobrushin_uniqueness_On gradW L hL f g T_target hT_target
    hf_lag hg_lag hf_mom hg_mom hfg0

/-! ## Universal-in-`t` bridge to `IsLagrangianVlasovSolution` -/
-- Combines `vlasovWellPosedness_forward` (forward iteration) +
-- `vlasovWellPosedness_uniqueness` into a single universal-in-`t`
-- existence theorem.  The universal `f` is constructed as the colimit of
-- the per-`T_target` solutions, well-defined by the uniqueness agreement on
-- overlaps.

/-- `IsLagrangianVlasovSolutionOn` is antitone in the window length: a Lagrangian
solution on `[0, T]` restricts to one on any `[0, T'] ⊆ [0, T]`. -/
lemma IsLagrangianVlasovSolutionOn.mono_window
    {d : ℕ}
    {gradW : PhysSpace d → PhysSpace d} {g : ℝ → Measure (PhaseSpace d)}
    {T T' : ℝ} (h : IsLagrangianVlasovSolutionOn gradW g T) (hTT' : T' ≤ T) :
    IsLagrangianVlasovSolutionOn gradW g T' := by
  obtain ⟨h_sol, charX, charV, h_flow, h_push, h_aemeas, h_cont⟩ := h
  refine ⟨?_, charX, charV, ?_, ?_, ?_⟩
  · intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ s hs
    exact h_sol φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ s
      ⟨hs.1, lt_of_lt_of_le hs.2 hTT'⟩
  · exact h_flow.mono (Set.Ioo_subset_Ioo le_rfl hTT') Set.Subset.rfl
  · intro s hs; exact h_push s ⟨hs.1, le_trans hs.2 hTT'⟩
  · refine ⟨?_, ?_⟩
    · intro s hs; exact h_aemeas s ⟨hs.1, le_trans hs.2 hTT'⟩
    · intro z; exact (h_cont z).mono (fun u hu => ⟨hu.1, le_trans hu.2 hTT'⟩)

/-- Continuity (within a window, at a point) of `t ↦ ∫ g d(fcur t)` for a curve
represented on the window as a flow pushforward: dominated convergence against
the fixed `f₀`, then transfer along the representation. -/
lemma integral_continuousWithinAt_of_flow_rep
    {d : ℕ}
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (fcur : ℝ → Measure (PhaseSpace d))
    (Φ : ℝ → PhaseSpace d → PhaseSpace d)
    (g : PhaseSpace d → ℝ) (hg_cont : Continuous g) (C : ℝ)
    (hgC : ∀ z : PhaseSpace d, ‖g z‖ ≤ C)
    (B t₀ : ℝ) (ht₀B : t₀ ∈ Set.Icc (0 : ℝ) B)
    (h_integral_eq : ∀ t ∈ Set.Icc (0 : ℝ) B,
      ∫ z, g z ∂(fcur t) = ∫ z, g (Φ t z) ∂f₀)
    (h_aesm : ∀ t ∈ Set.Icc (0 : ℝ) B,
      MeasureTheory.AEStronglyMeasurable (fun z => g (Φ t z)) f₀)
    (h_ptcont : ∀ z, ContinuousWithinAt (fun t => Φ t z) (Set.Icc (0 : ℝ) B) t₀) :
    ContinuousWithinAt (fun t => ∫ z, g z ∂(fcur t)) (Set.Icc (0 : ℝ) B) t₀ := by
  have h_cont_flow : ContinuousWithinAt
      (fun t => ∫ z, g (Φ t z) ∂f₀) (Set.Icc (0 : ℝ) B) t₀ := by
    apply continuousWithinAt_of_dominated (μ := f₀) (bound := fun _ => C)
    · exact Filter.Eventually.mono self_mem_nhdsWithin fun t ht => h_aesm t ht
    · apply Filter.Eventually.mono self_mem_nhdsWithin; intro t _
      exact Filter.Eventually.of_forall fun z => hgC _
    · exact MeasureTheory.integrable_const C
    · exact Filter.Eventually.of_forall fun z =>
        hg_cont.continuousAt.comp_continuousWithinAt (h_ptcont z)
  exact h_cont_flow.congr_of_eventuallyEq
    (Filter.Eventually.mono self_mem_nhdsWithin fun t ht => h_integral_eq t ht)
    (h_integral_eq t₀ ht₀B)

/-- **Universal-in-`t` (forward) existence — bridge to the marquee form**.

For any Lipschitz constant `L > 0`, produces a single `f : ℝ → Measure
(PhaseSpace d)` satisfying `IsLagrangianVlasovSolutionOn` for every
`T_target > 0`, with finite first moment and narrow continuity on `Ici 0`.
Composes `vlasovWellPosedness_forward` (forward iteration) +
`vlasovWellPosedness_uniqueness` (agreement on overlaps).

**Proof strategy**:

1. Apply `vlasovWellPosedness_forward` with `T_target := n` for each
   `n : ℕ`, getting per-`n` solutions `f_n : ℝ → Measure (PhaseSpace d)`.

2. By `vlasovWellPosedness_uniqueness`, `f_n` and `f_m` agree
   on `Icc 0 (min n m)`.

3. Define `f t := f_{⌈t⌉ + 1} t` for `t ≥ 0`.  By step 2, this is
   well-defined on `t ≥ 0`.

4. `IsLagrangianVlasovSolutionOn gradW f T_target` for each `T_target`:
   composes from the per-window solutions.

5. Narrow continuity on `Ici 0`: standard DCT using moment bound + flow
   growth.

The problem is a forward Cauchy problem; backward time is not on the
critical path. -/
theorem vlasovWellPosedness_universal_existence
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (hL_pos : (0 : ℝ) < L)
    (f₀ : Measure (PhaseSpace d))
    (hf₀ : HasFiniteFirstMoment f₀) :
    ∃ f : ℝ → Measure (PhaseSpace d),
      f 0 = f₀ ∧
      -- Forward-only conjuncts: the universal-in-t Vlasov well-posedness is
      -- a forward Cauchy problem; backward time is not on the critical path.
      (∀ t ∈ Set.Ici (0 : ℝ), HasFiniteFirstMoment (f t)) ∧
      (∀ T_target : ℝ, 0 < T_target →
        IsLagrangianVlasovSolutionOn gradW f T_target) ∧
      (∀ (g : PhaseSpace d → ℝ), Continuous g → Bornology.IsBounded (Set.range g) →
        ContinuousOn (fun t => ∫ z, g z ∂f t) (Set.Ici 0)) := by
  -- Step 1. For each n : ℕ, choose a solution on [0, n+1] via forward iteration.
  -- h_fwd_exists n gives ∃ g, g 0 = f₀ ∧ (moment on [0,n+1]) ∧ IsLagrangianVlasovSolutionOn n+1
  have h_fwd_exists : ∀ n : ℕ,
      ∃ g : ℝ → Measure (PhaseSpace d),
        g 0 = f₀ ∧
        (∀ t ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1), HasFiniteFirstMoment (g t)) ∧
        IsLagrangianVlasovSolutionOn gradW g ((n : ℝ) + 1) := by
    intro n
    exact vlasovWellPosedness_forward W gradW hgradW L hL hL_pos f₀ hf₀
      (by positivity : (0 : ℝ) < (n : ℝ) + 1)
  -- Step 2. Pick canonical per-n solutions via Classical.choice.
  let sol : ℕ → ℝ → Measure (PhaseSpace d) :=
    fun n => Classical.choose (h_fwd_exists n)
  have h_sol_init : ∀ n : ℕ, sol n 0 = f₀ :=
    fun n => (Classical.choose_spec (h_fwd_exists n)).1
  have h_sol_mom : ∀ n : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1),
      HasFiniteFirstMoment (sol n t) :=
    fun n => (Classical.choose_spec (h_fwd_exists n)).2.1
  have h_sol_lag : ∀ n : ℕ, IsLagrangianVlasovSolutionOn gradW (sol n) ((n : ℝ) + 1) :=
    fun n => (Classical.choose_spec (h_fwd_exists n)).2.2
  -- Step 3. Agreement on overlaps via uniqueness.
  -- Any two per-n solutions agree on [0, n+1]: restrict sol m from [0, m+1]
  -- to [0, n+1] via inline monotonicity, then apply vlasovWellPosedness_uniqueness.
  have h_agree : ∀ n m : ℕ, n ≤ m →
      ∀ t ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1), sol n t = sol m t := by
    intro n m hnm t ht
    -- Cast inequality: (n : ℝ) + 1 ≤ (m : ℝ) + 1
    have hnm_cast : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      have : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
      linarith
    -- Restrict sol m from [0, m+1] to [0, n+1] via window monotonicity
    have h_sol_m_on_n : IsLagrangianVlasovSolutionOn gradW (sol m) ((n : ℝ) + 1) :=
      (h_sol_lag m).mono_window hnm_cast
    -- Apply vlasovWellPosedness_uniqueness on window [0, n+1]
    exact vlasovWellPosedness_uniqueness W gradW hgradW L hL f₀ hf₀
      (by linarith [Nat.cast_nonneg (α := ℝ) n] : (0 : ℝ) < (n : ℝ) + 1)
      (sol n) (sol m) (h_sol_init n) (h_sol_init m)
      (h_sol_mom n)
      (fun s hs => h_sol_mom m s ⟨hs.1, le_trans hs.2 hnm_cast⟩)
      (h_sol_lag n) h_sol_m_on_n
      t ht
  -- Step 4. Define the universal-in-forward-time solution.
  -- For t ≥ 0: use sol ⌈t⌉₊ at t.  For t < 0: f₀ (unconstrained by the
  -- forward-only statement; the claims below only quantify over t ≥ 0).
  let f : ℝ → Measure (PhaseSpace d) :=
    fun t => if 0 ≤ t then sol (⌈t⌉₊) t else f₀
  -- Step 5. Prove the four conjuncts.
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  -- Conjunct 1: f 0 = f₀
  · change (if (0 : ℝ) ≤ 0 then sol ⌈(0 : ℝ)⌉₊ 0 else f₀) = f₀
    simp [h_sol_init 0]
  -- Conjunct 2: ∀ t ∈ Ici 0, HasFiniteFirstMoment (f t)
  · intro t ht
    have ht_nn : (0 : ℝ) ≤ t := ht
    change HasFiniteFirstMoment (if 0 ≤ t then sol ⌈t⌉₊ t else f₀)
    simp only [ht_nn, ↓reduceIte]
    apply h_sol_mom (⌈t⌉₊) t
    refine ⟨ht_nn, ?_⟩
    exact le_trans (Nat.le_ceil t) (by linarith)
  -- Conjunct 3: ∀ T_target > 0, IsLagrangianVlasovSolutionOn gradW f T_target
  · -- For T_target > 0, let N = ⌈T_target⌉₊.  The solution sol N exists on [0, N+1]
    -- with N+1 ≥ T_target.  Agreement h_agree gives f t = sol N t on [0, T_target].
    -- Restrict sol N's IsLagrangianVlasovSolutionOn to [0, T_target] and convert to f.
    intro T_target hT_target_pos
    set N := ⌈T_target⌉₊ with hN_def
    have hT_le_N : T_target ≤ (N : ℝ) := Nat.le_ceil T_target
    -- Agreement: f t = sol N t for t ∈ [0, T_target]
    have h_agree_fN : ∀ t ∈ Set.Icc (0 : ℝ) T_target, f t = sol N t := by
      intro t ht
      have ht_nn : (0 : ℝ) ≤ t := ht.1
      change (if 0 ≤ t then sol ⌈t⌉₊ t else f₀) = sol N t
      simp only [ht_nn, ↓reduceIte]
      exact h_agree ⌈t⌉₊ N (Nat.ceil_mono ht.2) t
        ⟨ht.1, le_trans (Nat.le_ceil t) (by linarith)⟩
    -- Extract components from h_sol_lag N
    obtain ⟨h_pde_N, charX_N, charV_N, h_flow_N, h_push_N, h_aemeas_N, h_boundary_N⟩ :=
      h_sol_lag N
    -- Compute f 0 = sol N 0
    have h_f0_solN : f 0 = sol N 0 :=
      h_agree_fN 0 ⟨le_refl 0, hT_target_pos.le⟩
    refine ⟨?_, charX_N, charV_N, ?_, ?_, ?_⟩
    · -- IsVlasovSolutionOn gradW f T_target: for each t ∈ Ioo 0 T_target,
      -- f and sol N agree near t, so HasDerivAt transfers via EventuallyEq.
      intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ t ht
      have ht_lt_N1 : t < (N : ℝ) + 1 := lt_of_lt_of_le ht.2 (by linarith)
      have h_from_N := h_pde_N φ hφ_smooth hφ_compact gradXφ gradVφ
        hgradXφ hgradVφ t ⟨ht.1, ht_lt_N1⟩
      -- The functions fun s => ∫ φ ∂(f s) and fun s => ∫ φ ∂(sol N s) agree near t
      have h_eq : (fun s => ∫ z, φ z ∂(f s)) =ᶠ[nhds t] (fun s => ∫ z, φ z ∂(sol N s)) := by
        apply Filter.Eventually.mono (Ioo_mem_nhds ht.1 ht.2)
        intro s hs
        change ∫ z, φ z ∂f s = ∫ z, φ z ∂sol N s
        congr 1
        exact h_agree_fN s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      -- After congr_of_eventuallyEq, the derivative body still refers to sol N t.
      -- Rewrite the goal: f t = sol N t (h_agree_fN) so the derivative bodies match.
      have h_result := h_from_N.congr_of_eventuallyEq h_eq
      simp only [h_agree_fN t ⟨le_of_lt ht.1, ht.2.le⟩]
      exact h_result
    · -- IsCharacteristicFlowOn on Ioo 0 T_target.
      -- h_flow_N uses ρ = spatialMarginal ∘ sol N; we need ρ = spatialMarginal ∘ f.
      -- On Ioo 0 T_target, f t = sol N t (from h_agree_fN), so spatialMarginals agree.
      refine ⟨h_flow_N.1, ?_, ?_⟩
      · intro t ht z _
        exact h_flow_N.2.1 t (Set.Ioo_subset_Ioo le_rfl (by linarith) ht) z (Set.mem_univ z)
      · intro t ht z _
        simp only [h_agree_fN t ⟨le_of_lt ht.1, ht.2.le⟩]
        exact h_flow_N.2.2 t (Set.Ioo_subset_Ioo le_rfl (by linarith) ht) z (Set.mem_univ z)
    · -- Pushforward: f t = Measure.map (charX_N t, charV_N t) (f 0) for t ∈ Icc 0 T_target
      intro t ht
      rw [h_agree_fN t ht, h_f0_solN]
      exact h_push_N t ⟨ht.1, le_trans ht.2 (by linarith)⟩
    · -- AEMeasurable ∧ boundary ContinuousOn on Icc 0 T_target.
      refine ⟨?_, ?_⟩
      · intro s hs
        rw [h_f0_solN]
        exact h_aemeas_N s ⟨hs.1, le_trans hs.2 (by linarith)⟩
      · -- Boundary ContinuousOn: `sol N`'s boundary conjunct, same flow
        -- `charX_N/charV_N`, restricted from `Icc 0 (N+1)` to `Icc 0 T_target`.
        intro z
        exact (h_boundary_N z).mono (Set.Icc_subset_Icc le_rfl (by linarith))
  -- Conjunct 4: narrow continuity on Ici 0
  · -- Strategy: ContinuousOn (Ici 0) = ∀ t₀ ≥ 0, ContinuousWithinAt at t₀.
    -- For t₀ > 0: use flow continuity from HasDerivAt (interior) + integral_map + DCT.
    -- For t₀ = 0: right-continuity via DCT using the boundary regularity bundle.
    intro g hg_cont hg_bdd
    -- Extract probability measure structure from hf₀
    obtain ⟨hf₀_prob, hf₀_int⟩ := hf₀
    have hf₀_prob_inst : IsProbabilityMeasure f₀ := hf₀_prob
    -- Extract a uniform bound C for g from the bounded-range hypothesis
    obtain ⟨C, hg_range⟩ := hg_bdd.subset_closedBall (0 : ℝ)
    -- C is a non-negative bound: ∀ z, ‖g z‖ ≤ C
    have hgC : ∀ z : PhaseSpace d, ‖g z‖ ≤ C := fun z => by
      have h := Metric.mem_closedBall.mp (hg_range (Set.mem_range_self z))
      simp only [Real.dist_eq, sub_zero] at h
      rwa [Real.norm_eq_abs]
    -- Show ContinuousOn by checking ContinuousWithinAt at each point
    intro t₀ ht₀
    have ht₀_nn := Set.mem_Ici.mp ht₀
    rcases ht₀_nn.eq_or_lt with h_eq | ht₀_pos
    · -- t₀ = 0: right-continuity via DCT.  The endpoint analog of the interior
      -- case: pointwise continuity of `t ↦ (charX_N t z, charV_N t z)` at 0 is
      -- supplied by `sol N`'s boundary `ContinuousOn` conjunct, replacing the
      -- interior case's two-sided `HasDerivAt` (unavailable at the left endpoint).
      rw [← h_eq]
      set N : ℕ := 1 with hN_def
      have hN_cast_pos : (0 : ℝ) < (N : ℝ) := by norm_num [hN_def]
      have h_agree_fN : ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ), f t = sol N t := by
        intro t ht
        have ht_nn := ht.1
        change (if 0 ≤ t then sol ⌈t⌉₊ t else f₀) = sol N t
        simp only [ht_nn, ↓reduceIte]
        exact h_agree ⌈t⌉₊ N ((Nat.ceil_mono ht.2).trans_eq (Nat.ceil_natCast N))
          t ⟨ht.1, le_trans (Nat.le_ceil t) (by linarith)⟩
      obtain ⟨_h_pde, charX_N, charV_N, h_flow_N, h_push_N, h_aemeas_N, h_boundary_N⟩ :=
        h_sol_lag N
      have h_integral_eq : ∀ t ∈ Set.Icc 0 (N : ℝ),
          ∫ z, g z ∂(f t) = ∫ z, g (charX_N t z, charV_N t z) ∂f₀ := by
        intro t ht_Icc
        rw [h_agree_fN t ht_Icc]
        have ht_ext : t ∈ Set.Icc (0 : ℝ) ((N : ℝ) + 1) :=
          ⟨ht_Icc.1, le_trans ht_Icc.2 (le_add_of_nonneg_right one_pos.le)⟩
        rw [h_push_N t ht_ext, ← h_sol_init N]
        exact integral_map (h_aemeas_N t ht_ext) hg_cont.measurable.aestronglyMeasurable
      have hIcc_mem : Set.Icc 0 (N : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ici 0) :=
        Icc_mem_nhdsGE hN_cast_pos
      refine (integral_continuousWithinAt_of_flow_rep f₀ f
        (fun t z => (charX_N t z, charV_N t z)) g hg_cont C hgC (N : ℝ) 0
        ⟨le_refl 0, hN_cast_pos.le⟩ h_integral_eq ?_ ?_).mono_of_mem_nhdsWithin hIcc_mem
      · intro t ht_mem
        exact (hg_cont.measurable.comp_aemeasurable
          (h_sol_init N ▸ h_aemeas_N t ⟨ht_mem.1, le_trans ht_mem.2
            (le_add_of_nonneg_right one_pos.le)⟩)).aestronglyMeasurable
      · intro z
        exact ((h_boundary_N z).continuousWithinAt
          ⟨le_refl 0, by linarith⟩).mono
          (Set.Icc_subset_Icc le_rfl (by linarith))
    · -- t₀ > 0: t₀ ∈ Ioi 0.  Use the interior flow continuity.
      -- Choose N so that t₀ is in the interior of [0, N].
      set N := ⌈t₀⌉₊ + 1 with hN_def
      have hN_cast_pos : (0 : ℝ) < (N : ℝ) := by positivity
      have ht₀_lt_N : t₀ < (N : ℝ) := by
        push_cast [hN_def]
        exact lt_add_of_le_of_pos (Nat.le_ceil t₀) one_pos
      -- Agreement: f t = sol N t for t ∈ [0, N]
      have h_agree_fN : ∀ t ∈ Set.Icc (0 : ℝ) (N : ℝ), f t = sol N t := by
        intro t ht
        have ht_nn := ht.1
        change (if 0 ≤ t then sol ⌈t⌉₊ t else f₀) = sol N t
        simp only [ht_nn, ↓reduceIte]
        exact h_agree ⌈t⌉₊ N ((Nat.ceil_mono ht.2).trans_eq (Nat.ceil_natCast N))
          t ⟨ht.1, le_trans (Nat.le_ceil t) (by linarith)⟩
      -- Extract flow witnesses from h_sol_lag N
      obtain ⟨_h_pde, charX_N, charV_N, h_flow_N, h_push_N, h_aemeas_N, _⟩ := h_sol_lag N
      -- The integral ∫ g ∂(f t) = ∫ z, g (charX_N t z, charV_N t z) ∂f₀
      -- for all t ∈ Icc 0 N (via pushforward formula + h_agree).
      have h_integral_eq : ∀ t ∈ Set.Icc 0 (N : ℝ),
          ∫ z, g z ∂(f t) = ∫ z, g (charX_N t z, charV_N t z) ∂f₀ := by
        intro t ht_Icc
        rw [h_agree_fN t ht_Icc]
        have ht_ext : t ∈ Set.Icc (0 : ℝ) ((N : ℝ) + 1) :=
          ⟨ht_Icc.1, le_trans ht_Icc.2 (le_add_of_nonneg_right one_pos.le)⟩
        rw [h_push_N t ht_ext, ← h_sol_init N]
        exact integral_map (h_aemeas_N t ht_ext) hg_cont.measurable.aestronglyMeasurable
      -- The set Icc 0 N is a neighborhood of t₀ within Ici 0 (since 0 < t₀ < N).
      have hIcc_mem : Set.Icc 0 (N : ℝ) ∈ nhdsWithin t₀ (Set.Ici 0) := by
        apply nhdsWithin_le_nhds; exact Icc_mem_nhds ht₀_pos ht₀_lt_N
      refine (integral_continuousWithinAt_of_flow_rep f₀ f
        (fun t z => (charX_N t z, charV_N t z)) g hg_cont C hgC (N : ℝ) t₀
        ⟨ht₀_pos.le, ht₀_lt_N.le⟩ h_integral_eq ?_ ?_).mono_of_mem_nhdsWithin hIcc_mem
      · intro t ht_mem
        exact (hg_cont.measurable.comp_aemeasurable
          (h_sol_init N ▸ h_aemeas_N t ⟨ht_mem.1, le_trans ht_mem.2
            (le_add_of_nonneg_right one_pos.le)⟩)).aestronglyMeasurable
      · intro z
        have ht₀_in_Ioo : t₀ ∈ Set.Ioo (0 : ℝ) ((N : ℝ) + 1) :=
          ⟨ht₀_pos, by push_cast [hN_def]; linarith [Nat.le_ceil t₀]⟩
        have hX_deriv := h_flow_N.2.1 t₀ ht₀_in_Ioo z (Set.mem_univ z)
        have hV_deriv := h_flow_N.2.2 t₀ ht₀_in_Ioo z (Set.mem_univ z)
        exact (hX_deriv.continuousAt.prodMk hV_deriv.continuousAt).continuousWithinAt

/-! ## §10  Marquee theorem (tex: thm:vlasov-wp) -/

/-- The `L = 0` (zero-force) branch of `vlasovWellPosedness`: the explicit
affine flow `(x, v) ↦ (x + t·v, v)` pushes `f₀` to a per-window Lagrangian
solution.  Every force-side obligation is trivial since `gradW ≡ 0`; the
moment/continuity threads come from the affine growth `‖x + t·v‖ ≤ (1+|t|)‖z‖`.
`f_sol` is threaded by its defining equation (let-bound caller supplies
`rfl`). -/
private lemma vlasovWellPosedness_zeroForce_solutionOn {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW_zero : ∀ x, gradW x = 0)
    (f₀ : Measure (PhaseSpace d)) (hf₀ : HasFiniteFirstMoment f₀)
    (f_sol : ℝ → Measure (PhaseSpace d))
    (hf_sol : f_sol = fun t => Measure.map
      (fun z : PhaseSpace d => (z.1 + t • z.2, z.2)) f₀)
    (T : ℝ) (hT : 0 < T) :
    IsLagrangianVlasovSolutionOn gradW f_sol T := by
  subst hf_sol
  have := hf₀.1
  let charX : ℝ → PhaseSpace d → PhysSpace d := fun t z => z.1 + t • z.2
  let charV : ℝ → PhaseSpace d → PhysSpace d := fun _ z => z.2
  have hconv_zero : ∀ (ρ : Measure (PhysSpace d)) (x : PhysSpace d),
      convolveFunctionMeasure gradW ρ x = 0 := by
    intros ρ x
    simp only [convolveFunctionMeasure]
    have : (fun y => gradW (x - y)) = fun _ => (0 : PhysSpace d) := by
      funext y; exact hgradW_zero (x - y)
    rw [this, integral_zero]
  have hL_zero : LipschitzWith 0 gradW := by
    rw [show gradW = fun _ => 0 from funext hgradW_zero]
    exact LipschitzWith.const' 0
  have hflow_univ : IsCharacteristicFlow gradW
      (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
      charX charV := by
    refine ⟨?_, ?_, ?_⟩
    · intro z; simp [charX, charV]
    · intro t z
      have h1 : HasDerivAt (fun s => z.1 + s • z.2) z.2 t := by
        have h1' : HasDerivAt (fun _ : ℝ => z.1) 0 t := hasDerivAt_const t z.1
        have h2' : HasDerivAt (fun s : ℝ => s • z.2) ((1 : ℝ) • z.2) t :=
          (hasDerivAt_id (𝕜 := ℝ) t).smul_const z.2
        have := h1'.add h2'; simp only [zero_add, one_smul] at this; exact this
      exact h1
    · intro t z
      simp only [vlasovSolutionViaPushforward, charX, charV]
      rw [hconv_zero, neg_zero]
      exact hasDerivAt_const t z.2
  have hself : IsCharacteristicFlowSelfConsistent charX f₀
      (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) := by
    intro t
    simp only [vlasovSolutionViaPushforward, spatialMarginal, charX, charV]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
  have h_flow_meas : ∀ s, AEMeasurable
      (fun z : PhaseSpace d => (charX s z, charV s z)) f₀ := by
    intro s; fun_prop
  have hgradW_cont : Continuous gradW := by
    have hz : gradW = fun _ => 0 := funext hgradW_zero
    rw [hz]; exact continuous_const
  have hconv_cont : ∀ s, Continuous (fun x =>
      convolveFunctionMeasure gradW
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x) := by
    intro s
    have hz : (fun x => convolveFunctionMeasure gradW
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x) =
        fun _ => 0 := funext (hconv_zero _)
    rw [hz]; exact continuous_const
  have h_int_conv : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y))
      (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) := by
    intro s x
    have h_zero : (fun y : PhysSpace d => gradW (x - y)) = fun _ => (0 : PhysSpace d) := by
      funext y; exact hgradW_zero (x - y)
    rw [h_zero]; exact integrable_zero _ _ _
  have hspatial_prob : ∀ s, IsProbabilityMeasure
      (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) := by
    intro s
    unfold spatialMarginal vlasovSolutionViaPushforward
    have _hpair : AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀ :=
      h_flow_meas s
    have _h_prob_inner : IsProbabilityMeasure
        (Measure.map (fun z : PhaseSpace d => (charX s z, charV s z)) f₀) :=
      Measure.isProbabilityMeasure_map _hpair
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have h_init0 : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z := by
    intro z; simp [charX, charV]
  have hnorm_bound : ∀ (s : ℝ) (z : PhaseSpace d), ‖charX s z‖ ≤ (1 + |s|) * ‖z‖ := by
    intro s z
    simp only [charX]
    have hle2 : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
    have htabs : 0 ≤ |s| := abs_nonneg s
    have hsmul : ‖s • z.2‖ = |s| * ‖z.2‖ := by rw [norm_smul, Real.norm_eq_abs]
    have htri := norm_add_le z.1 (s • z.2)
    have hle1 : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
    have := mul_le_mul_of_nonneg_left hle2 htabs; rw [hsmul] at htri; nlinarith
  have hflow_on : IsCharacteristicFlowOn gradW
      (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
      charX charV (Set.Ioo 0 T) Set.univ :=
    ⟨fun z _ => hflow_univ.1 z, fun t _ z _ => hflow_univ.2.1 t z,
     fun t _ z _ => hflow_univ.2.2 t z⟩
  have h_cont_Icc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T) := by
    intro z; simp only [charX, charV]; fun_prop
  have h_deriv_Ico : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW
          (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) s
          (charX s z, charV s z))
        (Set.Ici s) s := by
    intro z s _
    have hpair : HasDerivAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW
          (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) s
          (charX s z, charV s z)) s := by
      simp only [vlasovVectorField]
      exact (hflow_univ.2.1 s z).prodMk (hflow_univ.2.2 s z)
    exact hpair.hasDerivWithinAt
  have hmom_int : ∀ s,
      ∫ y, ‖y‖ ∂(spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))
        = ∫ z, ‖charX s z‖ ∂f₀ := by
    intro s
    have hs_eq : spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)
        = Measure.map (fun z => charX s z) f₀ := hself s
    rw [hs_eq]; exact integral_map (by fun_prop) (by fun_prop)
  have h_y_int : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖)
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) := by
    intro s _
    have hs_eq : spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)
        = Measure.map (fun z => charX s z) f₀ := hself s
    rw [hs_eq, integrable_map_measure (by fun_prop) (by fun_prop)]
    apply Integrable.mono' (hf₀.2.const_mul (1 + |s|))
    · fun_prop
    · apply Filter.Eventually.of_forall; intro z
      rw [Function.comp_apply, Real.norm_of_nonneg (norm_nonneg _)]
      exact hnorm_bound s z
  have hM_ρ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∫ y, ‖y‖ ∂(spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))
        ≤ (1 + T) * ∫ z, ‖z‖ ∂f₀ := by
    intro s hs
    rw [hmom_int s]
    have hbound_s : ∀ z : PhaseSpace d, ‖charX s z‖ ≤ (1 + T) * ‖z‖ := by
      intro z
      have h2 : (1 + |s|) ≤ (1 + T) := by
        have hss : |s| = s := abs_of_nonneg hs.1
        rw [hss]; linarith [hs.2]
      calc ‖charX s z‖ ≤ (1 + |s|) * ‖z‖ := hnorm_bound s z
        _ ≤ (1 + T) * ‖z‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    calc ∫ z, ‖charX s z‖ ∂f₀
        ≤ ∫ z, (1 + T) * ‖z‖ ∂f₀ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => norm_nonneg _))
            (hf₀.2.const_mul (1 + T)) (Filter.Eventually.of_forall hbound_s)
      _ = (1 + T) * ∫ z, ‖z‖ ∂f₀ := by rw [integral_const_mul]
  have hM_ρ_nn : 0 ≤ (1 + T) * ∫ z, ‖z‖ ∂f₀ :=
    mul_nonneg (by linarith [hT]) (integral_nonneg (fun z => norm_nonneg _))
  exact vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn
    gradW 0 hL_zero charX charV f₀ hf₀.2 hT
    hflow_on h_init0 h_cont_Icc h_deriv_Ico
    ((1 + T) * ∫ z, ‖z‖ ∂f₀) hM_ρ_nn hM_ρ h_y_int h_int_conv
    hself h_flow_meas hgradW_cont hconv_cont


/-- (tex: thm:vlasov-wp)
Forward-in-time existence for the Vlasov equation.

Let f_0 ∈ 𝒫_1(ℝ^d × ℝ^d) be a probability measure with finite first moment.
Under Assumption ass:W, for an arbitrary Lipschitz constant of `gradW`, there
exists a narrowly continuous curve `t ↦ f_t ∈ 𝒫_1(ℝ^d × ℝ^d)` on `[0, ∞)`,
with `f_{t=0} = f_0`, solving eq:vlasov in the Lagrangian sense on every forward
window `[0, T_target]`.

Per-window uniqueness over the Lagrangian class is provided separately by
`vlasovWellPosedness_uniqueness`.  The proof case-splits on `L = 0` (constant
force, explicit solution) vs `0 < L` (the substantive forward-iteration path),
and holds for every `L` (no smallness restriction). -/
theorem vlasovWellPosedness
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    -- Lipschitz constant of gradW (arbitrary; no smallness restriction).
    -- External callers extract `L` from `[AssW W]`'s `lipschitzGrad` existential.
    (L : NNReal) (hL_gradW : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d))
    (hf₀ : HasFiniteFirstMoment f₀) :
    -- Vlasov well-posedness is a forward-in-time Cauchy problem.  The forward-only
    -- `∃` is the mathematically accurate statement; per-window uniqueness is
    -- provided by `vlasovWellPosedness_uniqueness` as a separate interface.
    ∃ f : ℝ → Measure (PhaseSpace d),
      -- initial condition
      f 0 = f₀ ∧
      -- each f_t has finite first moment, for t ≥ 0.
      (∀ t ∈ Set.Ici (0 : ℝ), HasFiniteFirstMoment (f t)) ∧
      -- f solves the Vlasov equation IN THE LAGRANGIAN SENSE on every forward
      -- window [0, T_target].  Per-T_target `IsLagrangianVlasovSolutionOn` is the
      -- forward-only analog of the universal `IsLagrangianVlasovSolution`; the
      -- latter would require backward-time machinery which is not on the critical
      -- path for the well-posedness theorem.
      (∀ T_target : ℝ, 0 < T_target →
        IsLagrangianVlasovSolutionOn gradW f T_target) ∧
      -- f is narrowly continuous: t ↦ ∫ g df_t is continuous on the forward
      -- time domain `Set.Ici 0`, for every bounded continuous g.
      (∀ (g : PhaseSpace d → ℝ), Continuous g → Bornology.IsBounded (Set.range g) →
        ContinuousOn (fun t => ∫ z, g z ∂f t) (Set.Ici 0)) := by
  -- Step 1: Case split on whether L = 0 (constant force) or 0 < L.  Both
  -- branches are proved; the theorem holds for every Lipschitz constant.
  by_cases hL_pos : (0 : ℝ) < L
  · -- Case: 0 < L — the substantive path via forward iteration.
    -- `vlasovWellPosedness_universal_existence` produces per-T_target
    -- `IsLagrangianVlasovSolutionOn` (forward-only); the marquee bundles that
    -- shape directly as the existence claim.  Per-window uniqueness is
    -- available via `vlasovWellPosedness_uniqueness` as a separate interface.
    exact vlasovWellPosedness_universal_existence W gradW hgradW L hL_gradW
      hL_pos f₀ hf₀
  · -- Case: L = 0 (gradW is constant; explicit constant-force solution).
    -- Step L0-1: L = 0 as an NNReal.
    have hL_zero : L = 0 := by
      apply NNReal.coe_eq_zero.mp
      exact le_antisymm (not_lt.mp hL_pos) (NNReal.coe_nonneg L)
    -- Step L0-2: gradW ≡ 0 everywhere (LipschitzWith 0 means constant;
    -- gradient_zero_of_even gives gradW 0 = 0; so gradW ≡ 0).
    have hgradW_zero : ∀ x, gradW x = 0 := by
      intro x
      have hconst : ∀ a b, gradW a = gradW b := by
        rw [hL_zero] at hL_gradW
        exact (LipschitzWith.zero_iff gradW).mp hL_gradW
      have h0 : gradW 0 = 0 := by
        rw [hgradW 0]; exact gradient_zero_of_even W
      calc gradW x = gradW 0 := hconst x 0
        _ = 0 := h0
    -- Step L0-4: Define the explicit affine solution.
    let charX : ℝ → PhaseSpace d → PhysSpace d := fun t z => z.1 + t • z.2
    let charV : ℝ → PhaseSpace d → PhysSpace d := fun _ z => z.2
    let f_sol : ℝ → Measure (PhaseSpace d) :=
      fun t => Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) f₀
    -- Step L0-5: f_sol 0 = f₀.
    have hf_init : f_sol 0 = f₀ := by
      simp only [f_sol, charX, charV]
      have : (fun z : PhaseSpace d => (z.1 + (0 : ℝ) • z.2, z.2)) = id := by
        funext z; simp
      rw [this, Measure.map_id]
    -- Step L0-6: Each f_sol t has finite first moment.
    have hf_mom : ∀ t, HasFiniteFirstMoment (f_sol t) := by
      intro t
      constructor
      · -- IsProbabilityMeasure: pushforward of a probability measure under measurable map.
        have := hf₀.1
        apply Measure.isProbabilityMeasure_map
        fun_prop
      · -- Integrable ‖·‖: reduce to f₀ via integral_map, then bound by (1+|t|)·‖z‖.
        have := hf₀.1
        rw [integrable_map_measure (by fun_prop) (by fun_prop)]
        apply Integrable.mono' (hf₀.2.const_mul (1 + |t|))
        · fun_prop
        · apply Filter.Eventually.of_forall; intro z
          simp only [Function.comp_apply, charX, charV]
          -- Goal: ‖‖(z.1+t•z.2, z.2)‖‖ ≤ (1+|t|) * ‖z‖
          rw [Real.norm_of_nonneg (norm_nonneg _)]
          -- Goal: ‖(z.1+t•z.2, z.2)‖ ≤ (1+|t|) * ‖z‖
          have hle1 : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
          have hle2 : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
          have htabs : 0 ≤ |t| := abs_nonneg t
          have hsmul : ‖t • z.2‖ = |t| * ‖z.2‖ := by rw [norm_smul, Real.norm_eq_abs]
          have htri := norm_add_le z.1 (t • z.2)
          have hn : 0 ≤ ‖z‖ := norm_nonneg _
          have h1 : ‖z.1 + t • z.2‖ ≤ (1 + |t|) * ‖z‖ := by
            have := mul_le_mul_of_nonneg_left hle2 htabs; rw [hsmul] at htri; nlinarith
          have h2 : ‖z.2‖ ≤ (1 + |t|) * ‖z‖ := by nlinarith
          rw [Prod.norm_def]
          exact max_le_iff.mpr ⟨h1, h2⟩
    -- Step L0-8: Narrow continuity.
    have hf_cont : ∀ (g : PhaseSpace d → ℝ), Continuous g → Bornology.IsBounded (Set.range g) →
        Continuous (fun t => ∫ z, g z ∂f_sol t) := by
      intro g hg_cont hg_bdd
      -- Extract uniform bound C: ∀ x, ‖g x‖ ≤ C.
      obtain ⟨C, hC⟩ := hg_bdd.exists_norm_le
      have hC_range : ∀ x : PhaseSpace d, ‖g x‖ ≤ C :=
        fun x => hC (g x) (Set.mem_range_self x)
      -- Rewrite via integral_map: ∫ g df_sol(t) = ∫ z, g(z.1+t•z.2, z.2) df₀.
      have h_rw : ∀ t, ∫ z, g z ∂f_sol t = ∫ z, g (z.1 + t • z.2, z.2) ∂f₀ := by
        intro t
        simp only [f_sol, charX, charV]
        rw [integral_map (by fun_prop) (by fun_prop)]
      simp_rw [h_rw]
      -- Apply continuous_of_dominated.
      have := hf₀.1
      apply continuous_of_dominated
      · intro t; exact (hg_cont.comp (by fun_prop)).aestronglyMeasurable
      · intro t; apply Filter.Eventually.of_forall; intro z
        exact hC_range _
      · exact integrable_const C
      · apply Filter.Eventually.of_forall; intro z
        exact hg_cont.comp (by fun_prop)
    -- Assemble ∃ (post-refactor: forward-only existence, no uniqueness clause).
    refine ⟨f_sol, hf_init, ?_, ?_, ?_⟩
    · -- Moment bound on Ici 0 — discard t < 0.
      intro t _
      exact hf_mom t
    · -- Per-T_target `IsLagrangianVlasovSolutionOn` — the zero-force branch,
      -- extracted as `vlasovWellPosedness_zeroForce_solutionOn`.
      intro T hT
      exact vlasovWellPosedness_zeroForce_solutionOn gradW hgradW_zero f₀ hf₀
        f_sol rfl T hT
    · -- Narrow continuity restricted to Ici 0.
      intro g hg_cont hg_bdd
      exact (hf_cont g hg_cont hg_bdd).continuousOn

/-! ## §10  Dobrushin stability chain -/
--
-- These declarations live here (rather than in `Basic.lean`) because their
-- substantive close needs `convolveFunctionMeasure_lipschitz_in_x`, defined in
-- this file: a `Basic.lean`-resident declaration cannot call a
-- `CharacteristicFlow.lean` declaration (import direction).  The pure-FA
-- placeholders, the helpers that don't depend on the force-Lipschitz estimate,
-- and the marquee `meanFieldLimit` (which takes the Dobrushin estimate as a
-- hypothesis) remain in `Basic.lean`.


/-- Package the bound and positivity of C into the existential conclusion of dobrushin:
∃ C > 0, ∀ t ≥ 0, W₁(f_t, g_t) ≤ exp(C·t) · W₁(f_0, g_0).
Depends on dobrushin_C_choice (in Basic.lean) and dobrushin_ennreal_bound. -/
lemma dobrushin_package_exists
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [_hW : AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (_hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsLagrangianVlasovSolution gradW f)
    (hg : IsLagrangianVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, 0 ≤ t →
        wasserstein1 (f t) (g t) ≤
          ENNReal.ofReal (Real.exp (C * t)) * wasserstein1Coupling (f 0) (g 0) := by
  -- Routed through the integrated-coupling core via `dobrushin_meanfield_On`:
  -- pick C = 2·(max 1 L) and window each `t ≥ 0` at `T = t + 1` (uniform in
  -- `t`, including `t = 0`) via `.toOn`.  This bypasses the Gronwall-coupling
  -- W₁-continuity / right-derivative analytic route entirely.
  refine ⟨2 * ((max 1 L : NNReal) : ℝ), ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by
      rw [NNReal.coe_max, NNReal.coe_one]; exact le_max_left _ _
    linarith
  · intro t ht
    exact dobrushin_meanfield_On gradW L hL f g (t + 1) (by linarith)
      (hf.toOn (t + 1)) (hg.toOn (t + 1))
      (fun s _ => hf_prob s) (fun s _ => hg_prob s) t ⟨ht, by linarith⟩

/-- (tex: thm:dobrushin)
Dobrushin's stability theorem (1979).

Under Assumption ass:W, there exists a constant C = C(L) > 0 such that for any
two measure-valued solutions f_t, g_t ∈ 𝒫_1(ℝ^d × ℝ^d) of the Vlasov equation
eq:vlasov,

  W_1(f_t, g_t) ≤ e^{C·t} · W_1(f_0, g_0),   for all t ≥ 0,

where W_1 is the Wasserstein-1 distance.
The proof uses a coupling via the characteristic flows eq:char and a Gronwall
inequality; the key estimate is |∇W * ρ − ∇W * σ|_∞ ≤ L · W_1(ρ, σ).

The `[AssW W]` instance and `hgradW` record the standing setup ass:W (∇W the
gradient of an even C^{1,1} potential); the inequality itself consumes only
the Lipschitz bound `hL` — see `dobrushin_on` below for the minimal-hypothesis
window form with the explicit constant `C = 2 · max 1 L`. -/
theorem dobrushin
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [hW : AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    -- L is the Lipschitz constant of ∇W from Assumption ass:W
    (L : NNReal) (hL : LipschitzWith L gradW)
    -- f and g are two Lagrangian Vlasov solutions (carrying characteristic
    -- flow witnesses).
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : IsLagrangianVlasovSolution gradW f)
    (hg : IsLagrangianVlasovSolution gradW g)
    (hf_prob : ∀ t, HasFiniteFirstMoment (f t))
    (hg_prob : ∀ t, HasFiniteFirstMoment (g t)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, 0 ≤ t →
        wasserstein1 (f t) (g t) ≤
          ENNReal.ofReal (Real.exp (C * t)) * wasserstein1 (f 0) (g 0) := by
  -- close via dobrushin_package_exists (B-free coupling core), then convert the
  -- primal-coupling RHS `wasserstein1Coupling (f 0) (g 0)` to the dual RHS
  -- `wasserstein1 (f 0) (g 0)` via the KR duality bridge `wasserstein1_eq_coupling`
  -- (the sole Foundation-B use in this corollary).
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    dobrushin_package_exists W gradW hgradW L hL f g hf hg hf_prob hg_prob
  refine ⟨C, hC_pos, fun t ht => ?_⟩
  have : IsProbabilityMeasure (f 0) := (hf_prob 0).1
  have : IsProbabilityMeasure (g 0) := (hg_prob 0).1
  have hfm0 : Integrable (fun y => dist y (0 : PhaseSpace d)) (f 0) := by
    simpa only [dist_zero_right] using (hf_prob 0).2
  have hgm0 : Integrable (fun y => dist y (0 : PhaseSpace d)) (g 0) := by
    simpa only [dist_zero_right] using (hg_prob 0).2
  rw [wasserstein1_eq_coupling (f 0) (g 0) 0 hfm0 hgm0]
  exact hC_bound t ht

/-- **Dobrushin stability on the window `[0, T]`** — the public form of the
uniform-constant estimate, with the dual `W₁` metric on both sides.

Unlike the marquee `dobrushin` (global two-sided solutions, existential
constant), this form (i) consumes exactly what `vlasovWellPosedness` emits —
per-window `IsLagrangianVlasovSolutionOn` plus window moments — and (ii)
exposes the **explicit constant** `C = 2 · max 1 L`, which depends only on
the force's Lipschitz bound, not on the solution pair.  That uniformity is
what a mean-field argument quantifying over a family of solutions (e.g.
empirical curves, once their flow witnesses are formalized) needs. -/
theorem dobrushin_on
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (T : ℝ) (hT : 0 < T)
    (hf : IsLagrangianVlasovSolutionOn gradW f T)
    (hg : IsLagrangianVlasovSolutionOn gradW g T)
    (hf_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t))
    (hg_mom : ∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (g t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      wasserstein1 (f t) (g t) ≤
        ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t)) *
          wasserstein1 (f 0) (g 0) := by
  intro t ht
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_refl 0, hT.le⟩
  have : IsProbabilityMeasure (f 0) := (hf_mom 0 h0).1
  have : IsProbabilityMeasure (g 0) := (hg_mom 0 h0).1
  have hfm0 : Integrable (fun y => dist y (0 : PhaseSpace d)) (f 0) := by
    simpa only [dist_zero_right] using (hf_mom 0 h0).2
  have hgm0 : Integrable (fun y => dist y (0 : PhaseSpace d)) (g 0) := by
    simpa only [dist_zero_right] using (hg_mom 0 h0).2
  rw [wasserstein1_eq_coupling (f 0) (g 0) 0 hfm0 hgm0]
  exact dobrushin_meanfield_On gradW L hL f g T hT hf hg hf_mom hg_mom t ht

/-- **Forward-global Dobrushin stability with the explicit uniform constant.**

Stability for the solution class `vlasovWellPosedness` constructs: the
hypotheses are verbatim the existence theorem's conclusion clauses (the
per-window `IsLagrangianVlasovSolutionOn` family on every horizon, moments on
`Set.Ici 0`), and the estimate holds for all `t ≥ 0` with the
pair-independent constant `C = 2 · max 1 L`.  This is the arrow that lets the
existence output feed a Dobrushin-type stability input; see
`vlasovWellPosedness_stability` for the packaged composition. -/
theorem dobrushin_forward
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f g : ℝ → Measure (PhaseSpace d))
    (hf : ∀ T : ℝ, 0 < T → IsLagrangianVlasovSolutionOn gradW f T)
    (hg : ∀ T : ℝ, 0 < T → IsLagrangianVlasovSolutionOn gradW g T)
    (hf_mom : ∀ t ∈ Set.Ici (0 : ℝ), HasFiniteFirstMoment (f t))
    (hg_mom : ∀ t ∈ Set.Ici (0 : ℝ), HasFiniteFirstMoment (g t)) :
    ∀ t : ℝ, 0 ≤ t →
      wasserstein1 (f t) (g t) ≤
        ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t)) *
          wasserstein1 (f 0) (g 0) := by
  intro t ht
  exact dobrushin_on gradW L hL f g (t + 1) (by linarith)
    (hf (t + 1) (by linarith)) (hg (t + 1) (by linarith))
    (fun s hs => hf_mom s hs.1) (fun s hs => hg_mom s hs.1) t ⟨ht, by linarith⟩

/-- **Well-posedness package: existence + stability, chained.**

For any two initial data `f₀, g₀ ∈ 𝒫₁`, the curves produced by
`vlasovWellPosedness` satisfy the Dobrushin estimate with the explicit
constant `C = 2 · max 1 L` at every `t ≥ 0` — the composition of the two
headline theorems, recorded so that the existence output demonstrably feeds
the stability input (`dobrushin_forward`). -/
theorem vlasovWellPosedness_stability
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ) [AssW W]
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ g₀ : Measure (PhaseSpace d))
    (hf₀ : HasFiniteFirstMoment f₀) (hg₀ : HasFiniteFirstMoment g₀) :
    ∃ f g : ℝ → Measure (PhaseSpace d),
      f 0 = f₀ ∧ g 0 = g₀ ∧
      (∀ T : ℝ, 0 < T → IsLagrangianVlasovSolutionOn gradW f T) ∧
      (∀ T : ℝ, 0 < T → IsLagrangianVlasovSolutionOn gradW g T) ∧
      ∀ t : ℝ, 0 ≤ t →
        wasserstein1 (f t) (g t) ≤
          ENNReal.ofReal (Real.exp (2 * ((max 1 L : NNReal) : ℝ) * t)) *
            wasserstein1 f₀ g₀ := by
  obtain ⟨f, hf_init, hf_mom, hf_lag, _⟩ :=
    vlasovWellPosedness W gradW hgradW L hL f₀ hf₀
  obtain ⟨g, hg_init, hg_mom, hg_lag, _⟩ :=
    vlasovWellPosedness W gradW hgradW L hL g₀ hg₀
  refine ⟨f, g, hf_init, hg_init, hf_lag, hg_lag, ?_⟩
  have h := dobrushin_forward gradW L hL f g hf_lag hg_lag hf_mom hg_mom
  simpa only [hf_init, hg_init] using h

/-- **Coupling-metric Dobrushin stability estimate** — the `wasserstein1Coupling`
(primal) analogue of `DobrushinStabilityEstimate` (Basic).  LHS is the genuine
dual `W₁` metric; the RHS base is the primal coupling-inf metric
`wasserstein1Coupling`.  This is the form the **B-free** core
(`dobrushin_package_exists`) produces. -/
def DobrushinStabilityEstimateCoupling {d : ℕ}
    (f g : ℝ → Measure (PhaseSpace d)) (C : ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    wasserstein1 (f t) (g t) ≤
      ENNReal.ofReal (Real.exp (C * t)) * wasserstein1Coupling (f 0) (g 0)

/-- **Mean-field limit — B-free coupling form.**

The `meanFieldLimit` (Basic) analogue that consumes the **coupling-metric**
stability estimate (`DobrushinStabilityEstimateCoupling`, produced B-free by
`dobrushin_package_exists`) and **coupling-metric** initial convergence
(`wasserstein1Coupling (μ_0^N) f₀ → 0`).  The conclusion is unchanged:
convergence of the empirical curves to the Vlasov solution in the genuine dual
`W₁` metric.  Axiom-clean (`#print axioms`): **B-free**.

**Why coupling-`hInit` — the initial-convergence type the B-free limit requires.**
The B-free estimate puts `wasserstein1Coupling` on the RHS base, so the squeeze
needs `wasserstein1Coupling (μ_0^N) f₀ → 0`.  Standard dual-`W₁` initial
convergence does NOT supply this B-free: `wasserstein1 ≤ wasserstein1Coupling`
(`wasserstein1_le_wasserstein1Coupling`), so dual-small does not bound the
coupling — the easy direction runs the wrong way for a *hypothesis*; converting
dual→coupling is the hard direction (= Foundation B, `wasserstein1_eq_coupling`).
The two are mathematically equal (KR duality) and coupling-convergence is the
*natural* form for empirical measures (one exhibits couplings to bound the cost
from above), so this is a nominal — not a real — strengthening.  The all-dual
`meanFieldLimit` (Basic) remains the standard-hypothesis form, routing through
the all-dual `dobrushin` (the single Foundation-B bridge). -/
theorem meanFieldLimit_coupling
    {d : ℕ}
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (_hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (_hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) (_hf₀ : HasFiniteFirstMoment f₀)
    (f : ℝ → Measure (PhaseSpace d))
    (_hf_sol : IsLagrangianVlasovSolution gradW f)
    (hf_init : f 0 = f₀)
    (X V : (N : ℕ) → ℝ → Fin N → PhysSpace d)
    (_hSol : ∀ (N : ℕ), IsNewtonSolution N gradW (X N) (V N))
    -- initial empirical measures converge to f₀ in the COUPLING metric
    (hInit : Filter.Tendsto
      (fun N : ℕ => wasserstein1Coupling (empiricalMeasure N (X N 0) (V N 0)) f₀)
      Filter.atTop (nhds 0))
    (C : ℝ) (hC : 0 < C)
    (hDobrushin : ∀ (N : ℕ), DobrushinStabilityEstimateCoupling
      (empiricalMeasureCurve N (X N) (V N)) f C)
    (T : ℝ) (_hT : 0 < T) :
    Filter.Tendsto
      (fun N : ℕ => ⨆ t ∈ Set.Icc 0 T,
        wasserstein1 (empiricalMeasureCurve N (X N) (V N) t) (f t))
      Filter.atTop (nhds 0) := by
  have hsup_bound : ∀ N : ℕ,
      ⨆ t ∈ Set.Icc 0 T, wasserstein1 (empiricalMeasureCurve N (X N) (V N) t) (f t) ≤
        ENNReal.ofReal (Real.exp (C * T)) *
          wasserstein1Coupling (empiricalMeasureCurve N (X N) (V N) 0) (f 0) := by
    intro N
    apply iSup_le; intro t
    apply iSup_le; intro ht
    calc wasserstein1 (empiricalMeasureCurve N (X N) (V N) t) (f t)
        ≤ ENNReal.ofReal (Real.exp (C * t)) *
            wasserstein1Coupling (empiricalMeasureCurve N (X N) (V N) 0) (f 0) :=
          hDobrushin N t ht.1
      _ ≤ ENNReal.ofReal (Real.exp (C * T)) *
            wasserstein1Coupling (empiricalMeasureCurve N (X N) (V N) 0) (f 0) := by
          apply mul_le_mul_of_nonneg_right _ (zero_le)
          apply ENNReal.ofReal_le_ofReal
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (le_of_lt hC))
  have hUpper : Filter.Tendsto
      (fun N : ℕ => ENNReal.ofReal (Real.exp (C * T)) *
        wasserstein1Coupling (empiricalMeasureCurve N (X N) (V N) 0) (f 0))
      Filter.atTop (nhds 0) := by
    have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (Real.exp (C * T)))
      hInit (Or.inr ENNReal.ofReal_ne_top)
    simpa [empiricalMeasureCurve, hf_init, mul_zero] using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper
    (fun _ => zero_le) hsup_bound

end Vlasov
