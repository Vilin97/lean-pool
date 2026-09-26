/-
Copyright (c) 2026 Petr Girg, Petr Nečesal, Martin Dvořák, Jakub Psutka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Petr Girg, Petr Nečesal, Martin Dvořák, Jakub Psutka
-/

module

public import LeanPool.NemytskiiLebesgue.Closure
public import LeanPool.NemytskiiLebesgue.Frechet
public import LeanPool.NemytskiiLebesgue.Nemytskii
public import LeanPool.NemytskiiLebesgue.RealIso

/-!
# Nemytskii operators: IntegralFunctional

Adapted from `madvorak/nemytskii-lebesgue` (Apache-2.0).
-/

public section

namespace NemytskiiLebesgue

open scoped NemytskiiLebesgue

open MeasureTheory
open scoped ENNReal

theorem IsCaratheodory.integralFunctional_wellDefined
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F} (hf : IsCaratheodory f μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p ≠ ⊤)
    {a : Ω → ℝ} (ha : Integrable a μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCp : ∀ᵐ ω ∂μ, ∀ ξ : D, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ p.toReal)
    {u : Ω → D} (hup : MemLp u p μ) :
    Integrable (fun ω : Ω => f ω (u ω)) μ := by
  rw [←memLp_one_iff_integrable]
  exact
    hf.memLp_nemytskii_of_growth
      h1p
      hp
      le_rfl
      ENNReal.one_ne_top
      (memLp_one_iff_integrable.← ha)
      hC
      ((div_one p).symm ▸ hfaCp)
      hup

theorem IsCaratheodory.integralFunctional_wellDefined_real
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ}
    {f : Ω → ℝ^m → ℝ} (hf : IsCaratheodory f μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {a : Ω → ℝ} (ha : Integrable a μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCp : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ p.toReal)
    {u : Ω → ℝ^m} (hup : MemLp u p μ) :
    Integrable (fun ω : Ω => f ω (u ω)) μ :=
  hf.integralFunctional_wellDefined h1p hp.ne_top ha hC hfaCp hup

/-- Regard a real-valued integrand as taking values in one-dimensional Euclidean space. -/
@[expose] noncomputable def outR1 {Ω : Type*} {m : ℕ} (f : Ω → ℝ^m → ℝ) :
    Ω → ℝ^m → ℝ^1 :=
  (realLIE <| f · ·)

/-- Transport the output of an integrand derivative to one-dimensional Euclidean space. -/
@[expose] noncomputable def outR1nested {Ω : Type*} {m : ℕ} (f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)) :
    Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ^1) :=
  (realLIE.toContinuousLinearMap.comp <| f' · ·)

lemma IsCaratheodory.outR1
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ}
    {f : Ω → ℝ^m → ℝ} (hf : IsCaratheodory f μ) :
    IsCaratheodory (NemytskiiLebesgue.outR1 f) μ :=
  hf.comp_continuous realLIE.continuous

lemma IsCaratheodory.outR1nested
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ}
    {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)} (hf' : IsCaratheodory f' μ) :
    IsCaratheodory (NemytskiiLebesgue.outR1nested f') μ :=
  hf'.comp_continuous (by fun_prop)

lemma hasFDerivAt_outR1_outR1nested
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ}
    {f : Ω → ℝ^m → ℝ} {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)}
    (hff' : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (f ω) (f' ω ξ) ξ) :
    ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (NemytskiiLebesgue.outR1 f ω) (NemytskiiLebesgue.outR1nested f'
      ω ξ) ξ :=
  hff'.mono ↓(fun _ => realLIE.toContinuousLinearMap.hasFDerivAt.comp _ <| · _)

lemma outR1nested_norm_eq
    {Ω : Type*}
    {m : ℕ}
    (f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)) (ω : Ω) (ξ : ℝ^m) :
    ‖NemytskiiLebesgue.outR1nested f' ω ξ‖ = ‖f' ω ξ‖ := by
  have f'_norm : ∀ v : ℝ^m, ‖realLIE.toContinuousLinearMap (f' ω ξ v)‖ = ‖f' ω ξ v‖ := by
    bound
  refine
    le_antisymm
      (ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg (f' ω ξ)) fun v :
        ℝ^m => ?_)
      (ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg
        (NemytskiiLebesgue.outR1nested f' ω ξ)) fun v : ℝ^m => ?_)
  · exact f'_norm v ▸ ContinuousLinearMap.le_opNorm ..
  · exact le_trans (f'_norm v).ge ((realLIE.toContinuousLinearMap.comp (f' ω ξ)).le_opNorm v)

lemma outR1nested_growth
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ}
    (f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ))
    {b : Ω → ℝ} {C α : ℝ}
    (hf'bCα : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ α) :
    ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, ‖NemytskiiLebesgue.outR1nested f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ α := by
  filter_upwards [hf'bCα] with ω hω ξ using le_trans (by rw [outR1nested_norm_eq]) (hω ξ)

-- end all private

lemma IsCaratheodory.memLp_nemytskii_deriv
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ}
    {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)} (hf' : IsCaratheodory f' μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {b : Ω → ℝ} (hbq : MemLp b ↱q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfbCp : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ (p - 1))
    {u : Ω → ℝ^m} (hup : MemLp u ↱p μ) :
    MemLp (fun ω : Ω => f' ω (u ω)) ↱q μ :=
  have hp : 1 ≤ p :=
    hpq.lt.le
  have hq : 1 ≤ q :=
    hpq.symm.lt.le
  memLp_nemytskii_of_growth_of_aestronglyMeasurable
    (zero_lt_one.trans_le (ENNReal.ofReal_one ▸ ENNReal.ofReal_le_ofReal hp))
    ENNReal.ofReal_ne_top
    (ENNReal.ofReal_one ▸ ENNReal.ofReal_le_ofReal hq)
    ENNReal.ofReal_ne_top
    hbq
    hC
    (by
      simp_all only [ENNReal.toReal_div]
      change ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ |b ω| + C * ‖ξ‖ ^ ((↱p).toReal / (↱q).toReal)
      filter_upwards [hfbCp] with ω hω ξ using
        le_trans
          (hω ξ)
          (add_le_add (le_abs_self _) (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _)
            le_rfl (by linarith)) hC))
        |> le_trans <| by simp [hpq.div_conj_eq_sub_one,
            ENNReal.toReal_ofReal (zero_le_one.trans hp),
            ENNReal.toReal_ofReal (zero_le_one.trans hq)]
    )
    hup
    (hf'.aestronglyMeas_nemytskii_of_aestronglyMeas hup.aestronglyMeasurable)

lemma IsCaratheodory.integrable_nemytskii_deriv_apply
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ} {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)} (hf' : IsCaratheodory f' μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {b : Ω → ℝ} (hbq : MemLp b ↱q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hf'bCp : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ (p - 1))
    {u : Ω → ℝ^m} (hup : MemLp u ↱p μ)
    {v : Ω → ℝ^m} (hvp : MemLp v ↱p μ) :
    Integrable (fun ω : Ω => (f' ω (u ω)) (v ω)) μ := by
  have f'_u_in_Lq : MemLp (fun ω : Ω => f' ω (u ω)) ↱q μ := by
    apply_rules [memLp_nemytskii_deriv]
  have integrabl : Integrable (fun ω : Ω => ‖f' ω (u ω)‖ * ‖v ω‖) μ := by
    convert! f'_u_in_Lq.norm.integrable_mul hvp.norm using 1
    exact hpq.symm.ennrealOfReal
  apply integrabl.mono'
  · have cont : Continuous (fun p : (ℝ^m →L[ℝ] ℝ) × ℝ^m => p.fst p.snd) := by
      fun_prop
    exact cont.comp_aestronglyMeasurable (f'_u_in_Lq.aestronglyMeasurable.prodMk
      hvp.aestronglyMeasurable)
  · exact Filter.Eventually.of_forall ↓(ContinuousLinearMap.le_opNorm _ _)

lemma norm_integral_le_eLpNorm_one_toReal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (g : Ω → ℝ) :
    ‖∫ ω : Ω, g ω ∂μ‖ ≤ (eLpNorm g 1 μ).toReal := by
  by_cases hg : AEStronglyMeasurable g μ
  · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal _ _ hg] <;> norm_num
    convert! norm_integral_le_lintegral_norm g using 1
    norm_num [Real.enorm_eq_ofReal_abs]
  · rw [integral_non_aestronglyMeasurable hg, norm_zero]
    exact ENNReal.toReal_nonneg

theorem IsCaratheodory.integralFunctional_frechet_deriv
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ}
    {f : Ω → ℝ^m → ℝ} (hf : IsCaratheodory f μ)
    {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)} (hf' : IsCaratheodory f' μ)
    (hff' : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (f ω) (f' ω ξ) ξ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {b : Ω → ℝ} (h0b : 0 ≤ᵐ[μ] b) (hbq : MemLp b ↱q μ)
    {C : ℝ} (hC : 0 < C)
    (hf'bCp : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ (p - 1))
    {u : Ω → ℝ^m} (hup : MemLp u ↱p μ) :
    (∀ v : Ω → ℝ^m, MemLp v ↱p μ →
      Integrable (fun ω : Ω => (f' ω (u ω)) (v ω)) μ) ∧
    (∀ ε > 0, ∃ δ > 0, ∀ l : Ω → ℝ^m,
      MemLp l ↱p μ →
        eLpNorm l ↱p μ ≤ ↱δ →
          ‖∫ ω : Ω, (f ω (u ω + l ω) - f ω (u ω) - (f' ω (u ω)) (l ω)) ∂μ‖ ≤
            ε * (eLpNorm l ↱p μ).toReal) := by
  constructor
  · exact ↓(hf'.integrable_nemytskii_deriv_apply hpq hbq hC.le hf'bCp hup)
  · have nemytskii_bound : ∀ ε > 0, ∃ δ > 0, ∀ l : Ω → ℝ^m,
        MemLp l ↱p μ → eLpNorm l ↱p μ ≤ ↱δ →
          eLpNorm (fun ω : Ω => NemytskiiLebesgue.outR1 f ω (u ω + l ω) - NemytskiiLebesgue.outR1 f
            ω (u ω) - NemytskiiLebesgue.outR1nested f' ω (u ω) (l ω)) ↱(1 : ℝ) μ ≤
          ↱ε * eLpNorm l ↱p μ := by
      apply hf.outR1.eLpNorm_frechet_remainder_le_ofReal_mul_eLpNorm hf'.outR1nested
        (hasFDerivAt_outR1_outR1nested hff') hpq.lt.le hpq.symm.lt.le hpq.symm h0b hbq hC _ hup
      rw [hpq.div_conj_eq_sub_one]
      exact outR1nested_growth f' hf'bCp
    intro ε hε
    obtain ⟨δ, hδ, hbound⟩ := nemytskii_bound ε hε
    use δ, hδ
    intro l hl hl'
    have key := hbound l hl hl'
    change eLpNorm (fun ω => realLIE (f ω (u ω + l ω)) - realLIE (f ω (u ω)) -
      realLIE (f' ω (u ω) (l ω))) ↱(1 : ℝ) μ ≤ ↱ε * eLpNorm l ↱p μ at key
    simp only [← map_sub, eLpNorm_realLIE, ENNReal.ofReal_one] at key
    apply (norm_integral_le_eLpNorm_one_toReal _).trans
    convert ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hl.eLpNorm_ne_top) key using 1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le]

end NemytskiiLebesgue
