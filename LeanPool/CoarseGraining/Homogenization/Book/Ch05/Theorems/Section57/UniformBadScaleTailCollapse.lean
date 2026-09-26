/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformBadScaleTail
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleTailCollapse
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.BadScaleThresholds

/-! # Uniform Bad Scale Tail Collapse -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open scoped ENNReal

/-!
# Collapse of the uniform endpoint bad-scale tail

This file turns the synchronized endpoint component estimate into one
stretched-exponential bad-scale tail with exponent `d`, up to explicit
deterministic threshold and prefactor-gap conditions.
-/

noncomputable section

theorem two_exp_terms_le_exp_of_prefactor_gap
    {c₁ c₂ A T₀ T : ℝ}
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hA : T₀ ≤ A)
    (hpref : c₁ + c₂ ≤ Real.exp (T₀ - T)) :
    c₁ * Real.exp (-A) + c₂ * Real.exp (-A) ≤ Real.exp (-T) := by
  have hEA : Real.exp (-A) ≤ Real.exp (-T₀) :=
    Real.exp_le_exp.mpr (by linarith)
  have hsum :
      c₁ * Real.exp (-A) + c₂ * Real.exp (-A) ≤
        (c₁ + c₂) * Real.exp (-T₀) := by
    calc
      c₁ * Real.exp (-A) + c₂ * Real.exp (-A)
          ≤ c₁ * Real.exp (-T₀) + c₂ * Real.exp (-T₀) := by
            nlinarith [mul_le_mul_of_nonneg_left hEA hc₁,
              mul_le_mul_of_nonneg_left hEA hc₂]
      _ = (c₁ + c₂) * Real.exp (-T₀) := by ring
  calc
    c₁ * Real.exp (-A) + c₂ * Real.exp (-A)
        ≤ (c₁ + c₂) * Real.exp (-T₀) := hsum
    _ ≤ Real.exp (T₀ - T) * Real.exp (-T₀) :=
        mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le
    _ = Real.exp (-T) := by
        rw [← Real.exp_add]
        congr 1
        ring

theorem measureReal_badScaleEvent_le_exp_tail_of_uniformEndpoint_component_sum
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {H : ℕ → ℕ → Ω → ℝ} {t α : ℝ} {q : ℕ}
    {S qPlus Cbottom wq Ktop Kbottom A Alead Atail η : ℝ}
    (hcomponent :
      μ.real (badScaleEvent H t α q) ≤
        S * (Real.exp (-(A ^ η)) * Ktop) +
          qPlus * (Cbottom * wq) *
            (Real.exp (-(A ^ η)) * Kbottom))
    (hAlead_A : Alead ≤ A ^ η)
    (hpref :
      max 0 (S * Ktop) +
          max 0 (qPlus * (Cbottom * wq) * Kbottom) ≤
        Real.exp (Alead - Atail)) :
    μ.real (badScaleEvent H t α q) ≤ Real.exp (-Atail) := by
  have hcomponent_coeff :
      μ.real (badScaleEvent H t α q) ≤
        (S * Ktop) * Real.exp (-(A ^ η)) +
          (qPlus * (Cbottom * wq) * Kbottom) * Real.exp (-(A ^ η)) := by
    calc
      μ.real (badScaleEvent H t α q)
          ≤ S * (Real.exp (-(A ^ η)) * Ktop) +
              qPlus * (Cbottom * wq) *
                (Real.exp (-(A ^ η)) * Kbottom) := hcomponent
      _ =
        (S * Ktop) * Real.exp (-(A ^ η)) +
          (qPlus * (Cbottom * wq) * Kbottom) * Real.exp (-(A ^ η)) := by
          ring
  have hcomponent_max :
      μ.real (badScaleEvent H t α q) ≤
        max 0 (S * Ktop) * Real.exp (-(A ^ η)) +
          max 0 (qPlus * (Cbottom * wq) * Kbottom) *
            Real.exp (-(A ^ η)) := by
    have htop :
        (S * Ktop) * Real.exp (-(A ^ η)) ≤
          max 0 (S * Ktop) * Real.exp (-(A ^ η)) :=
      mul_le_mul_of_nonneg_right
        (le_max_right 0 (S * Ktop)) (Real.exp_pos _).le
    have hbottom :
        (qPlus * (Cbottom * wq) * Kbottom) * Real.exp (-(A ^ η)) ≤
          max 0 (qPlus * (Cbottom * wq) * Kbottom) *
            Real.exp (-(A ^ η)) :=
      mul_le_mul_of_nonneg_right
        (le_max_right 0 (qPlus * (Cbottom * wq) * Kbottom))
        (Real.exp_pos _).le
    linarith
  exact hcomponent_max.trans
    (two_exp_terms_le_exp_of_prefactor_gap
      (c₁ := max 0 (S * Ktop))
      (c₂ := max 0 (qPlus * (Cbottom * wq) * Kbottom))
      (A := A ^ η) (T₀ := Alead) (T := Atail)
      (le_max_left 0 (S * Ktop))
      (le_max_left 0 (qPlus * (Cbottom * wq) * Kbottom))
      hAlead_A hpref)

/-- Uniform endpoint bad-scale tail after selected denominator, with the
deterministic prefactor gap still explicit. -/
theorem measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_uniformEndpoint_tail_of_prefactor_gap
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Ccrude Centry a : ℝ,
      0 < Cfluct ∧ 0 < Ccrude ∧ 0 < Centry ∧ 0 < a ∧
      ∀ {t αbad Btail : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct),
        hInf.params = params →
      ∀ {q : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hInf.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let ctop : ℝ :=
          min (t - αbad)
            (min (b - αbad)
              (min ((t - αbad) * (1 + b / a))
                (b - αbad * (1 + b / a))))
        let η : ℝ := ((d : ℕ) : ℝ)
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let Dhigh : ℝ := 2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ)
        let Dcrude : ℝ := K * Ccrude * hInf.thetaHat ^ (2 : ℕ)
        let Den : ℝ := uniformEndpointHighDenominator Dhigh Dcrude t η
        let Blead : ℝ := Den * (3 : ℝ) ^ (L + 1)
        let Acrude : ℝ := (3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1)) / Dcrude
        let Alead : ℝ := (((3 : ℝ) ^ (q : ℝ) / Blead) ^ η)
        let Atail : ℝ := (((3 : ℝ) ^ (q : ℝ) / Btail) ^ η)
        let ρtop : ℝ := (3 : ℝ) ^ ctop
        let ρbottom : ℝ := (3 : ℝ) ^ (2 * (t - αbad) / η)
        let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
        let Ctop : ℝ :=
          (S.card : ℝ) * weightedLinearExpKernelConst w (ρtop ^ (2 : ℝ))
        let ChighBottom : ℝ :=
          ((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) *
            weightedGeometricExpKernelConst w (ρbottom ^ η)
        0 < t →
        0 ≤ αbad →
        αbad < t →
        αbad < b →
        αbad * (1 + b / a) < b →
        αbad < a →
        t ≤ b →
        0 < Btail →
        1 ≤ (3 : ℝ) ^ (q : ℝ) / Blead →
        1 ≤ Acrude →
        (let Lcut : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1);
          Lcut + 1 < (1 - αbad / a) * (q : ℝ)) →
        max 0 Ctop + max 0 ChighBottom ≤ Real.exp (Alead - Atail) →
        P.real (badScaleEvent Hshift t αbad q) ≤ Real.exp (-Atail) := by
  obtain ⟨Cfluct, Ccrude, Centry, a,
      hCfluct, hCcrude, hCentry, ha, hselected⟩ :=
    measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_uniformEndpoint_selected_denominator
      (d := d) params
  refine ⟨Cfluct, Ccrude, Centry, a,
    hCfluct, hCcrude, hCentry, ha, ?_⟩
  intro t αbad Btail P hP hStruct hInf hparams q
  dsimp only
  intro ht hα_nonneg hαt hαb hαharm hαa htb hBtail hlead_one
    hAcrude_one hq_large hpref
  let : IsProbabilityMeasure P := hP.isProbability
  let K : ℝ := quenchedProbeEnvelopeConst d
  let N0 : ℕ :=
    annealedAlgebraicEntryScale P
      hInf.toQuantitativeCoarseGrainedEllipticity Centry
  let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
    fun M N aω =>
      quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
  let S : Finset (NormalizedProbeIndex d) := Finset.univ
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let ctop : ℝ :=
    min (t - αbad)
      (min (b - αbad)
        (min ((t - αbad) * (1 + b / a))
          (b - αbad * (1 + b / a))))
  let η : ℝ := ((d : ℕ) : ℝ)
  let w : ℝ := ((3 ^ d : ℕ) : ℝ)
  let Dhigh : ℝ := 2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ)
  let Dcrude : ℝ := K * Ccrude * hInf.thetaHat ^ (2 : ℕ)
  let Den : ℝ := uniformEndpointHighDenominator Dhigh Dcrude t η
  let Blead : ℝ := Den * (3 : ℝ) ^ (L + 1)
  let A : ℝ := (3 : ℝ) ^ ((q : ℝ) - (L + 1)) / Den
  let Acrude : ℝ := (3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1)) / Dcrude
  let Alead : ℝ := (((3 : ℝ) ^ (q : ℝ) / Blead) ^ η)
  let Atail : ℝ := (((3 : ℝ) ^ (q : ℝ) / Btail) ^ η)
  let ρtop : ℝ := (3 : ℝ) ^ ctop
  let ρbottom : ℝ := (3 : ℝ) ^ (2 * (t - αbad) / η)
  let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
  have hDen_pos : 0 < Den := by
    simpa [Den] using
      uniformEndpointHighDenominator_pos
        (Dhigh := Dhigh) (Dcrude := Dcrude) (t := t) (d := η)
  have hBlead_pos : 0 < Blead := by
    dsimp [Blead]
    exact mul_pos hDen_pos
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) (L + 1))
  have hη_pos : 0 < η := by
    dsimp [η]
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hAlead_A : Alead ≤ A ^ η := by
    have hden : Den * (3 : ℝ) ^ (L + 1) ≤ Blead := by rfl
    simpa [Alead, A, Blead] using
      selected_tail_parameter_power_le_high
        (q := q) (Den := Den) (B := Blead) (η := η) (O := L + 1)
        hDen_pos hBlead_pos hη_pos hden
  have hA_one : 1 ≤ A := by
    have hlead_A : (3 : ℝ) ^ (q : ℝ) / Blead ≤ A := by
      have hpow_nonneg : 0 ≤ (3 : ℝ) ^ (q : ℝ) :=
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
      calc
        (3 : ℝ) ^ (q : ℝ) / Blead
            ≤ (3 : ℝ) ^ (q : ℝ) / (Den * (3 : ℝ) ^ (L + 1)) :=
              div_le_div_of_nonneg_left hpow_nonneg
                (mul_pos hDen_pos
                  (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) (L + 1)))
                (by rfl)
        _ = A := by
              exact (rpow_three_sub_div_eq_div_mul_rpow
                (x := (q : ℝ)) (O := L + 1) (Den := Den)
                hDen_pos.ne').symm
    exact hlead_one.trans hlead_A
  have hcomponent :=
    hselected (t := t) (αbad := αbad)
      hP hStruct hInf hparams (q := q)
      ht hα_nonneg hαt hαb hαharm hαa htb
      hA_one hAcrude_one hq_large
  exact
    measureReal_badScaleEvent_le_exp_tail_of_uniformEndpoint_component_sum
      (μ := P) (H := Hshift) (t := t) (α := αbad) (q := q)
      (S := (S.card : ℝ)) (qPlus := ((q + 1 : ℕ) : ℝ))
      (Cbottom := Cbottom) (wq := w ^ q)
      (Ktop := weightedLinearExpKernelConst w (ρtop ^ (2 : ℝ)))
      (Kbottom := weightedGeometricExpKernelConst w (ρbottom ^ η))
      (A := A) (Alead := Alead) (Atail := Atail) (η := η)
      (by
        simpa [K, N0, Hshift, S, b, L, ctop, η, w, Dhigh, Dcrude,
          Den, A, Acrude, ρtop, ρbottom, Cbottom] using hcomponent)
      hAlead_A
      (by
        simpa [K, S, b, L, ctop, η, w, Dhigh, Dcrude, Den, Blead,
          A, Acrude, Alead, Atail, ρtop, ρbottom, Cbottom] using hpref)

/-- Endpoint tail after discharging the lead, crude-bottom, and crude-top
threshold side conditions by explicit ceilings. -/
theorem measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_uniformEndpoint_tail_of_thresholds_and_prefactor_gap
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Ccrude Centry a : ℝ,
      0 < Cfluct ∧ 0 < Ccrude ∧ 0 < Centry ∧ 0 < a ∧
      ∀ {t αbad Btail : ℝ},
      ∀ {P : Ch04.RestrictionCoeffLaw d}
        (hP : Ch04.RestrictionLawCarrier P)
        (hStruct : Ch04.RestrictionStructuralLaw P)
        (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct),
        hInf.params = params →
      ∀ {q : ℕ},
        let K : ℝ := quenchedProbeEnvelopeConst d
        let N0 : ℕ :=
          annealedAlgebraicEntryScale P
            hInf.toQuantitativeCoarseGrainedEllipticity Centry
        let Hshift : ℕ → ℕ → RegCoeffField d → ℝ :=
          fun M N aω =>
            quenchedProbeEnvelope hP hStruct (N0 + M) (N0 + N) aω
        let S : Finset (NormalizedProbeIndex d) := Finset.univ
        let b : ℝ := (d : ℝ) / 2
        let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
        let ctop : ℝ :=
          min (t - αbad)
            (min (b - αbad)
              (min ((t - αbad) * (1 + b / a))
                (b - αbad * (1 + b / a))))
        let η : ℝ := ((d : ℕ) : ℝ)
        let w : ℝ := ((3 ^ d : ℕ) : ℝ)
        let Dhigh : ℝ := 2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ)
        let Dcrude : ℝ := K * Ccrude * hInf.thetaHat ^ (2 : ℕ)
        let Den : ℝ := uniformEndpointHighDenominator Dhigh Dcrude t η
        let Blead : ℝ := Den * (3 : ℝ) ^ (L + 1)
        let Alead : ℝ := (((3 : ℝ) ^ (q : ℝ) / Blead) ^ η)
        let Atail : ℝ := (((3 : ℝ) ^ (q : ℝ) / Btail) ^ η)
        let ρtop : ℝ := (3 : ℝ) ^ ctop
        let ρbottom : ℝ := (3 : ℝ) ^ (2 * (t - αbad) / η)
        let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
        let Ctop : ℝ :=
          (S.card : ℝ) * weightedLinearExpKernelConst w (ρtop ^ (2 : ℝ))
        let ChighBottom : ℝ :=
          ((q + 1 : ℕ) : ℝ) * (Cbottom * w ^ q) *
            weightedGeometricExpKernelConst w (ρbottom ^ η)
        0 < t →
        0 ≤ αbad →
        αbad < t →
        αbad < b →
        αbad * (1 + b / a) < b →
        αbad < a →
        t ≤ b →
        0 < Btail →
        Nat.ceil (Real.log Blead / Real.log 3) ≤ q →
        Nat.ceil
            ((Real.log Dcrude + (t * (L + 1)) * Real.log (3 : ℝ)) /
              (t * Real.log (3 : ℝ))) ≤ q →
        Nat.ceil ((L + 1) / (1 - αbad / a) + 1) ≤ q →
        max 0 Ctop + max 0 ChighBottom ≤ Real.exp (Alead - Atail) →
        P.real (badScaleEvent Hshift t αbad q) ≤ Real.exp (-Atail) := by
  obtain ⟨Cfluct, Ccrude, Centry, a,
      hCfluct, hCcrude, hCentry, ha, htail⟩ :=
    measureReal_shiftedBadScaleEvent_quenchedProbeEnvelope_le_uniformEndpoint_tail_of_prefactor_gap
      (d := d) params
  refine ⟨Cfluct, Ccrude, Centry, a,
    hCfluct, hCcrude, hCentry, ha, ?_⟩
  intro t αbad Btail P hP hStruct hInf hparams q
  dsimp only
  intro ht hα_nonneg hαt hαb hαharm hαa htb hBtail hq_lead
    hq_crude hq_cut hpref
  let K : ℝ := quenchedProbeEnvelopeConst d
  let b : ℝ := (d : ℝ) / 2
  let L : ℝ := (a * Real.log 3)⁻¹ * Real.log (max (2 * K) 1)
  let η : ℝ := ((d : ℕ) : ℝ)
  let Dhigh : ℝ := 2 * K * Cfluct * hInf.thetaHat ^ (2 : ℕ)
  let Dcrude : ℝ := K * Ccrude * hInf.thetaHat ^ (2 : ℕ)
  let Den : ℝ := uniformEndpointHighDenominator Dhigh Dcrude t η
  let Blead : ℝ := Den * (3 : ℝ) ^ (L + 1)
  have hK_pos : 0 < K := by
    simpa [K] using quenchedProbeEnvelopeConst_pos d
  have hDcrude_pos : 0 < Dcrude := by
    dsimp [Dcrude]
    exact mul_pos (mul_pos hK_pos hCcrude) (pow_pos hInf.thetaHat_pos 2)
  have hDen_pos : 0 < Den := by
    simpa [Den] using
      uniformEndpointHighDenominator_pos
        (Dhigh := Dhigh) (Dcrude := Dcrude) (t := t) (d := η)
  have hBlead_pos : 0 < Blead := by
    dsimp [Blead]
    exact mul_pos hDen_pos
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) (L + 1))
  have hlead_one : 1 ≤ (3 : ℝ) ^ (q : ℝ) / Blead := by
    simpa [Blead] using
      one_le_rpow_three_linear_sub_nat_div_of_natCeil_le
        (β := (1 : ℝ)) (O := (0 : ℝ)) (D := Blead) (q := q)
        (by norm_num) hBlead_pos
        (by simpa [Blead, L] using hq_lead)
  have hcrude_one :
      1 ≤ (3 : ℝ) ^ (t * (q : ℝ) - t * (L + 1)) / Dcrude := by
    simpa [mul_assoc] using
      one_le_rpow_three_linear_sub_nat_div_of_natCeil_le
        (β := t) (O := t * (L + 1)) (D := Dcrude) (q := q)
        ht hDcrude_pos hq_crude
  have hδ : 0 < 1 - αbad / a := by
    have hdiv : αbad / a < 1 := by
      rw [div_lt_iff₀ ha]
      nlinarith
    linarith
  have hcut :
      L + 1 < (1 - αbad / a) * (q : ℝ) := by
    exact
      large_scale_cutoff_of_natCeil_add_one_le
        (L := L) (δ := 1 - αbad / a) (q := q) hδ hq_cut
  simpa [K, b, L, η, Dhigh, Dcrude, Den, Blead] using
    htail (t := t) (αbad := αbad) (Btail := Btail)
      hP hStruct hInf hparams (q := q)
      ht hα_nonneg hαt hαb hαharm hαa htb hBtail
      hlead_one hcrude_one (by simpa [K, L] using hcut) hpref

end

end Section57
end Ch05
end Book
end Homogenization
