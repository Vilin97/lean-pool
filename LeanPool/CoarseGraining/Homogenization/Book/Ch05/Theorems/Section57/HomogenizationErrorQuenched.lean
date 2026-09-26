/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationQuenched
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UnitEllipticityMinimalExpLogSq
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationErrorMinimalScale
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformHomogenizationQuenched

/-! # Homogenization Error Quenched -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open scoped ENNReal MatrixOrder BigOperators

/-!
# Quenched finite-q homogenization-error corollary

This file converts the Section 5.7 minimal-scale theorem into a finite-`q`
bound on `\mathcal E_{r,\infty,q}` above a single random scale.
-/

noncomputable section

theorem deterministic_unitEllipticity_bound_le_squareEnvelope
    {K θ D τ α : ℝ} {m : ℕ}
    (hKD : K * θ ^ (2 : ℕ) ≤ D ^ α)
    (hD : 0 < D) (hατ : α ≤ τ) :
    K * θ ^ (2 : ℕ) ≤
      (Real.rpow (3 : ℝ) ((τ / 2) * (m : ℝ)) *
        Real.sqrt (((3 : ℝ) ^ m / D) ^ (-α))) ^ (2 : ℕ) := by
  have hDα_pos : 0 < D ^ α := Real.rpow_pos_of_pos hD α
  have hfactor_ge_one :
      1 ≤ Real.rpow (3 : ℝ) ((τ - α) * (m : ℝ)) := by
    exact Real.one_le_rpow
      (by norm_num : (1 : ℝ) ≤ 3)
      (mul_nonneg (sub_nonneg.mpr hατ) (by positivity))
  have hnum_pos : 0 < (3 : ℝ) ^ m := by positivity
  have hB_nonneg : 0 ≤ (((3 : ℝ) ^ m / D) ^ (-α)) := by
    positivity
  have hA_sq :
      Real.rpow (3 : ℝ) ((τ / 2) * (m : ℝ)) ^ (2 : ℕ) =
        Real.rpow (3 : ℝ) (τ * (m : ℝ)) := by
    let x : ℝ := (τ / 2) * (m : ℝ)
    have hpow₀ :
        Real.rpow (3 : ℝ) (x * (2 : ℝ)) =
          Real.rpow (Real.rpow (3 : ℝ) x) (2 : ℝ) := by
      exact Real.rpow_mul (x := (3 : ℝ))
        (by norm_num : (0 : ℝ) ≤ 3) x (2 : ℝ)
    have hpow :
        Real.rpow (3 : ℝ) (x * (2 : ℝ)) =
          Real.rpow (3 : ℝ) x ^ (2 : ℕ) := by
      simpa [Real.rpow_two] using hpow₀
    calc
      Real.rpow (3 : ℝ) ((τ / 2) * (m : ℝ)) ^ (2 : ℕ)
          = Real.rpow (3 : ℝ) (x * (2 : ℝ)) := by
            simpa [x] using hpow.symm
      _ = Real.rpow (3 : ℝ) (τ * (m : ℝ)) := by
            congr 1
            ring
  have hB_eq :
      (((3 : ℝ) ^ m / D) ^ (-α)) =
        Real.rpow (3 : ℝ) (-α * (m : ℝ)) * D ^ α := by
    have hpowm_eq : ((3 : ℝ) ^ m : ℝ) = Real.rpow (3 : ℝ) (m : ℝ) := by
      simp
    have hpow_mul :
        Real.rpow (Real.rpow (3 : ℝ) (m : ℝ)) (-α) =
          Real.rpow (3 : ℝ) ((m : ℝ) * (-α)) := by
      exact (Real.rpow_mul (x := (3 : ℝ))
        (by norm_num : (0 : ℝ) ≤ 3) (m : ℝ) (-α)).symm
    rw [Real.div_rpow hnum_pos.le hD.le (-α)]
    rw [Real.rpow_neg hD.le α]
    rw [hpowm_eq]
    change
      Real.rpow (Real.rpow (3 : ℝ) (m : ℝ)) (-α) /
          (D ^ α)⁻¹ =
        Real.rpow (3 : ℝ) (-α * (m : ℝ)) * D ^ α
    rw [hpow_mul]
    field_simp [Real.rpow_pos_of_pos hD α |>.ne']
  have henv_eq :
      (Real.rpow (3 : ℝ) ((τ / 2) * (m : ℝ)) *
        Real.sqrt (((3 : ℝ) ^ m / D) ^ (-α))) ^ (2 : ℕ) =
        Real.rpow (3 : ℝ) ((τ - α) * (m : ℝ)) * D ^ α := by
    calc
      (Real.rpow (3 : ℝ) ((τ / 2) * (m : ℝ)) *
          Real.sqrt (((3 : ℝ) ^ m / D) ^ (-α))) ^ (2 : ℕ)
          =
        Real.rpow (3 : ℝ) ((τ / 2) * (m : ℝ)) ^ (2 : ℕ) *
          (((3 : ℝ) ^ m / D) ^ (-α)) := by
            rw [mul_pow, Real.sq_sqrt hB_nonneg]
      _ =
        Real.rpow (3 : ℝ) (τ * (m : ℝ)) *
          (Real.rpow (3 : ℝ) (-α * (m : ℝ)) * D ^ α) := by
            rw [hA_sq, hB_eq]
      _ =
        Real.rpow (3 : ℝ) ((τ - α) * (m : ℝ)) * D ^ α := by
            have hcombine :
                Real.rpow (3 : ℝ) (τ * (m : ℝ)) *
                    Real.rpow (3 : ℝ) (-α * (m : ℝ)) =
                  Real.rpow (3 : ℝ) ((τ - α) * (m : ℝ)) := by
              calc
                Real.rpow (3 : ℝ) (τ * (m : ℝ)) *
                    Real.rpow (3 : ℝ) (-α * (m : ℝ))
                    =
                  Real.rpow (3 : ℝ) (τ * (m : ℝ) + -α * (m : ℝ)) := by
                    exact (Real.rpow_add (by norm_num : (0 : ℝ) < 3)
                      (τ * (m : ℝ)) (-α * (m : ℝ))).symm
                _ = Real.rpow (3 : ℝ) ((τ - α) * (m : ℝ)) := by
                    congr 1
                    ring
            rw [← mul_assoc, hcombine]
  calc
    K * θ ^ (2 : ℕ) ≤ D ^ α := hKD
    _ = 1 * D ^ α := by ring
    _ ≤ Real.rpow (3 : ℝ) ((τ - α) * (m : ℝ)) * D ^ α :=
        mul_le_mul_of_nonneg_right hfactor_ge_one hDα_pos.le
    _ =
      (Real.rpow (3 : ℝ) ((τ / 2) * (m : ℝ)) *
        Real.sqrt (((3 : ℝ) ^ m / D) ^ (-α))) ^ (2 : ℕ) := henv_eq.symm

theorem finset_univ_fin_two_sup'_if_eq_max
    {Ω : Type*} (X Y : Ω → ℝ) (ω : Ω) :
    (Finset.univ : Finset (Fin 2)).sup'
        (by exact ⟨0, by simp⟩)
        (fun i => if i = 0 then X ω else Y ω) =
      max (X ω) (Y ω) := by
  classical
  apply le_antisymm
  · refine Finset.sup'_le _ _ ?_
    intro i _hi
    fin_cases i <;> simp
  · refine max_le ?_ ?_
    · have hmem : (0 : Fin 2) ∈ (Finset.univ : Finset (Fin 2)) := by simp
      exact (Finset.le_sup' (fun i => if i = 0 then X ω else Y ω) hmem).trans_eq
        (by simp)
    · have hmem : (1 : Fin 2) ∈ (Finset.univ : Finset (Fin 2)) := by simp
      exact (Finset.le_sup' (fun i => if i = 0 then X ω else Y ω) hmem).trans_eq
        (by simp)

theorem isBigO_gammaSigma_max_two_of_scales
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {η AJ AU : ℝ} (hη : 0 < η)
    {XJ XU : Ω → ℝ}
    (hJ : IsBigO μ (gammaSigma η) XJ AJ)
    (hU : IsBigO μ (gammaSigma η) XU AU) :
    IsBigO μ (gammaSigma η) (fun ω => max (XJ ω) (XU ω))
      (((3 * Real.log (2 : ℝ)) ^ η⁻¹) * max AJ AU) := by
  classical
  let S : Finset (Fin 2) := Finset.univ
  have hS : S.Nonempty := by
    exact ⟨0, by simp [S]⟩
  let Z : Fin 2 → Ω → ℝ := fun i ω =>
    if i = 0 then XJ ω else XU ω
  let A : Fin 2 → ℝ := fun i => if i = 0 then AJ else AU
  have hcard : 2 ≤ S.card := by
    simp [S]
  have hZA : ∀ i ∈ S, IsBigO μ (gammaSigma η) (Z i) (A i) := by
    intro i _hi
    fin_cases i <;> simp [Z, A, hJ, hU]
  have hsup :=
    IndependentSums.isBigO_gammaSigma_finset_sup'_of_scales
      (μ := μ) (s := S) (hs := hS) (X := Z) (a := A) (σ := η)
      hη hcard hZA
  have hfun :
      (fun ω => S.sup' hS (fun i => Z i ω)) =
        fun ω => max (XJ ω) (XU ω) := by
    funext ω
    simpa [S, Z] using finset_univ_fin_two_sup'_if_eq_max XJ XU ω
  have hA : S.sup' hS A = max AJ AU := by
    simpa [S, A] using
      finset_univ_fin_two_sup'_if_eq_max
        (fun _ : Unit => AJ) (fun _ : Unit => AU) ()
  have hcard_real : (S.card : ℝ) = (2 : ℝ) := by
    simp [S]
  simpa [hfun, hA, hcard_real] using hsup

/-- Finite-`sigma` minimal-scale control of the full finite-`q`
homogenization error on origin cubes.

The random scale is the maximum of the `J` minimal scale and the localized
unit-ellipticity minimal scale; all deterministic terms are collapsed into
the single factor `(3^m / X)^(-alpha/2)`. -/
theorem exists_homogenizationErrorOnOriginCube_interpolated_expLogSq
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ α : ℝ, 0 < α ∧
      α < max params.sUpper params.sLower ∧
      ∀ {σ τ r q : ℝ}, 0 < σ →
        max params.sUpper params.sLower < τ / 2 →
        α < τ / 2 →
        τ ≤ 1 →
        0 ≤ r * q →
        0 < (r - τ / 2) * q →
        0 < q →
        let ηJ : ℝ := finiteQuenchedTailExponent d σ τ
        let ηU : ℝ := finiteQuenchedTailExponent d σ (τ / 2)
        let η : ℝ := min ηJ ηU
        ∃ Cscale : ℝ, 0 < Cscale ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
            hΓ.sigma = σ → hΓ.params = params →
            ∃ X : RegCoeffField d → ℝ,
              IsBigO P (gammaSigma η) X
                (Real.exp
                  (Cscale * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ))) ∧
              (∀ aω, 1 ≤ X aω) ∧
                ∀ᵐ aω ∂P,
                  ∀ (ha : Ch04.AELocallyUniformlyEllipticField aω) {m : ℕ},
                    X aω ≤ (3 : ℝ) ^ m →
                    let Cresp : ℝ :=
                      Real.sqrt
                        (4 * (Fintype.card (BlockCoord d) : ℝ) *
                          (Fintype.card (NormalizedProbeIndex d) : ℝ));
                    let Cneg : ℝ :=
                      (Ch02.geometricDiscount (τ / 2) 1)⁻¹ *
                        (2 * Real.sqrt
                          ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)));
                    let A : ℝ := max Cresp Cneg * Real.rpow (3 : ℝ) (τ / 2);
                    Ch02.HomogenizationErrorOnCube
                        (originCube d ((m : ℕ) : ℤ)) r
                        Ch02.MultiscaleExponent.infinity (.finite q)
                        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
                          aω ha)
                        (scalarMatrix (d := d) (barSigmaLimit hP hStruct)) ≤
                      Real.rpow
                          (Ch02.geometricDiscount r q *
                            (Ch02.geometricDiscount (r - τ / 2) q)⁻¹)
                          (1 / q) *
                        A *
                          Real.sqrt (((3 : ℝ) ^ m / X aω) ^ (-α)) := by
  obtain ⟨α, hα_pos, hαmax, hJbase⟩ :=
    exists_quenchedLocalizedEstimate_interpolated_expLogSq_uniformAnnealedExponent
      (d := d) params
  refine ⟨α, hα_pos, hαmax, ?_⟩
  intro σ τ r q hσ_pos hτ_half hατ_half hτ_le_one hrq hδq hq
  dsimp only
  let ηJ : ℝ := finiteQuenchedTailExponent d σ τ
  let ηU : ℝ := finiteQuenchedTailExponent d σ (τ / 2)
  let η : ℝ := min ηJ ηU
  have hτ2_pos : 0 < τ / 2 :=
    (max_sUpper_sLower_pos params).trans hτ_half
  have hτ_pos : 0 < τ := by linarith
  have hmaxτ : max params.sUpper params.sLower < τ := by
    have hhalf_lt : τ / 2 < τ := by linarith
    exact hτ_half.trans hhalf_lt
  have hηJ_pos : 0 < ηJ := by
    simpa [ηJ] using finiteQuenchedTailExponent_pos
      (d := d) (σ := σ) (t := τ) hσ_pos hτ_pos
  have hηU_pos : 0 < ηU := by
    simpa [ηU] using finiteQuenchedTailExponent_pos
      (d := d) (σ := σ) (t := τ / 2) hσ_pos hτ2_pos
  have hη_pos : 0 < η := by
    dsimp [η]
    exact lt_min hηJ_pos hηU_pos
  obtain ⟨CJ, hCJ_pos, hJlaw⟩ :=
    hJbase (σ := σ) hσ_pos (t := τ) hmaxτ hτ_le_one
  obtain ⟨CU, hCU_pos, hUlaw⟩ :=
    exists_unitEllipticityMinimalScale_interpolated_expLogSq
      (d := d) (σ := σ) hσ_pos params
      (t := τ / 2) (α := α)
      hτ2_pos hα_pos.le hατ_half
  let Ksup : ℝ := (3 * Real.log (2 : ℝ)) ^ η⁻¹
  let Cscale : ℝ := 4 * max 0 (Real.log Ksup) + CJ + CU
  have hKsup_pos : 0 < Ksup := by
    dsimp [Ksup]
    exact Real.rpow_pos_of_pos
      (mul_pos (by norm_num : (0 : ℝ) < 3)
        (Real.log_pos (by norm_num : (1 : ℝ) < 2))) _
  have hCscale_pos : 0 < Cscale := by
    dsimp [Cscale]
    have hmax_nonneg : 0 ≤ max 0 (Real.log Ksup) := le_max_left 0 _
    nlinarith
  refine ⟨Cscale, hCscale_pos, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams
  let : IsProbabilityMeasure P := hP.isProbability
  obtain ⟨XJ, hOJ_raw, hXJ_one, hJpoint⟩ :=
    hJlaw hP hStruct hΓ hσ_eq hparams
  obtain ⟨XU, hOU_raw, hXU_one, hUpoint⟩ :=
    hUlaw hP hStruct hΓ hσ_eq hparams
  let X : RegCoeffField d → ℝ := fun aω => max (XJ aω) (XU aω)
  let AJ : ℝ :=
    Real.exp (CJ * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ))
  let AU : ℝ :=
    Real.exp (CU * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ))
  have hOJ :
      IsBigO P (gammaSigma η) XJ AJ := by
    exact Ch04.IsBigO.gammaSigma_mono_exponent
      (μ := P) (ρ := η) (σ := ηJ)
      (by dsimp [η]; exact min_le_left _ _) (by simpa [ηJ, AJ] using hOJ_raw)
  have hOU :
      IsBigO P (gammaSigma η) XU AU := by
    exact Ch04.IsBigO.gammaSigma_mono_exponent
      (μ := P) (ρ := η) (σ := ηU)
      (by dsimp [η]; exact min_le_right _ _) (by simpa [ηU, AU] using hOU_raw)
  have hOmax_raw :
      IsBigO P (gammaSigma η) X
        (Ksup * max AJ AU) := by
    simpa [X, Ksup] using
      isBigO_gammaSigma_max_two_of_scales
        (μ := P) (η := η) (AJ := AJ) (AU := AU)
        hη_pos hOJ hOU
  have hscale_final :
      Ksup * max AJ AU ≤
        Real.exp
          (Cscale * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ)) := by
    let L2 : ℝ := (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ)
    let Ck : ℝ := 4 * max 0 (Real.log Ksup)
    have hL2_nonneg : 0 ≤ L2 := by dsimp [L2]; positivity
    have hAJ_le : AJ ≤ Real.exp ((CJ + CU) * L2) := by
      refine Real.exp_le_exp.mpr ?_
      dsimp [AJ, L2]
      nlinarith [mul_nonneg hCU_pos.le hL2_nonneg]
    have hAU_le : AU ≤ Real.exp ((CJ + CU) * L2) := by
      refine Real.exp_le_exp.mpr ?_
      dsimp [AU, L2]
      nlinarith [mul_nonneg hCJ_pos.le hL2_nonneg]
    have hmax_le : max AJ AU ≤ Real.exp ((CJ + CU) * L2) :=
      max_le hAJ_le hAU_le
    have hK_le : Ksup ≤ Real.exp (Ck * L2) := by
      have hraw :=
        const_mul_rpow_max_one_le_exp_logSq
          (A := Ksup) (θ := hΓ.thetaHat) (p := (0 : ℝ))
          hKsup_pos hΓ.thetaHat_pos.le (by norm_num)
      simpa [Ksup, Ck, L2] using hraw
    calc
      Ksup * max AJ AU
          ≤ Ksup * Real.exp ((CJ + CU) * L2) :=
            mul_le_mul_of_nonneg_left hmax_le hKsup_pos.le
      _ ≤ Real.exp (Ck * L2) * Real.exp ((CJ + CU) * L2) :=
            mul_le_mul_of_nonneg_right hK_le (Real.exp_pos _).le
      _ = Real.exp (Cscale * L2) := by
            rw [← Real.exp_add]
            dsimp [Cscale, Ck]
            ring_nf
  have hO :
      IsBigO P (gammaSigma η) X
        (Real.exp
          (Cscale * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ))) :=
    IsBigO.mono_scale (μ := P) (Ψ := gammaSigma η) hOmax_raw hscale_final
  refine ⟨X, hO, ?_, ?_⟩
  · intro aω
    dsimp [X]
    exact hXJ_one aω |>.trans (le_max_left _ _)
  have hJprobeAE :
      ∀ᵐ aω ∂P,
        ∀ i : NormalizedProbeIndex d,
          ∀ {m n : ℕ},
            XJ aω ≤ (3 : ℝ) ^ m →
            n < m →
            (3 : ℝ) ^ (-τ * ((m - n : ℕ) : ℝ)) *
                localizedLimitNormalizedJMax hP hStruct m n
                  (normalizedProbeVec i) aω ≤
              ((3 : ℝ) ^ m / XJ aω) ^ (-α) := by
    rw [MeasureTheory.ae_all_iff]
    intro i
    exact hJpoint (normalizedProbeVec i)
      (normalizedProbeVec_dotProduct_self_le_one i)
  filter_upwards [hJprobeAE, hUpoint] with aω hJprobe hUnit
  intro ha m hXm
  have hXJ_pos : 0 < XJ aω :=
    lt_of_lt_of_le zero_lt_one (hXJ_one aω)
  have hXU_pos : 0 < XU aω :=
    lt_of_lt_of_le zero_lt_one (hXU_one aω)
  have hScale : max (XJ aω) (XU aω) ≤ (3 : ℝ) ^ m := by
    simpa [X] using hXm
  have hUpper : hΓ.params.sUpper < τ / 2 := by
    have hs : params.sUpper ≤ max params.sUpper params.sLower := le_max_left _ _
    exact by simpa [hparams] using hs.trans_lt hτ_half
  have hLower : hΓ.params.sLower < τ / 2 := by
    have hs : params.sLower ≤ max params.sUpper params.sLower := le_max_right _ _
    exact by simpa [hparams] using hs.trans_lt hτ_half
  have hProbe :
      ∀ {n : ℕ},
        XJ aω ≤ (3 : ℝ) ^ m →
        n < m →
        Real.rpow (3 : ℝ) (-τ * ((m - n : ℕ) : ℝ)) *
            localizedNormalizedProbeJMax hP hStruct m n aω ≤
          ((3 : ℝ) ^ m / XJ aω) ^ (-α) := by
    intro n hXJn hnm
    let W : ℝ := Real.rpow (3 : ℝ) (-τ * ((m - n : ℕ) : ℝ))
    have hW_pos : 0 < W := by
      dsimp [W]
      positivity
    exact
      weighted_localizedNormalizedProbeJMax_le_of_forall_probe
        hP hStruct (m := m) (n := n) aω (W := W)
        (R := ((3 : ℝ) ^ m / XJ aω) ^ (-α))
        hW_pos
        (by
          intro i
          simpa [W] using hJprobe i hXJn hnm)
  have hUnit_m :
      localizedLimitWeightedUnitEllipticitySup hP hStruct hΓ.params m aω ≤
        (Real.rpow (3 : ℝ) ((τ / 2) * (m : ℝ)) *
          Real.sqrt (((3 : ℝ) ^ m / XU aω) ^ (-α))) ^ (2 : ℕ) := by
    exact hUnit (by exact (le_max_right _ _).trans hScale)
  simpa [X] using
    homogenizationErrorOnOriginCube_le_of_two_minimalScales_probeJ
      hP hStruct hΓ ha (m := m) (r := r) (τ := τ)
      (δ := r - τ / 2) (q := q) (XJ := XJ aω) (XU := XU aω)
      (α := α) rfl hτ_pos hrq hδq hq hUpper hLower hα_pos.le
      hXJ_pos hXU_pos hProbe hUnit_m hScale

/-- Endpoint (`σ = ∞`) minimal-scale control of the full finite-`q`
homogenization error on origin cubes.

The random scale is the maximum of the endpoint `J` minimal scale and a
deterministic unit-ellipticity scale depending on `thetaHat`; the latter is
absorbed into the same `exp(C log^2(2 + thetaHat))` prefactor. -/
theorem exists_homogenizationErrorOnOriginCube_uniformEndpoint_expLogSq
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ α : ℝ, 0 < α ∧
      α < max params.sUpper params.sLower ∧
      ∀ {τ r q : ℝ},
        max params.sUpper params.sLower < τ / 2 →
        α < τ / 2 →
        τ ≤ 1 →
        0 ≤ r * q →
        0 < (r - τ / 2) * q →
        0 < q →
        let η : ℝ := ((d : ℕ) : ℝ)
        ∃ Cscale : ℝ, 0 < Cscale ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct),
            hInf.params = params →
            ∃ X : RegCoeffField d → ℝ,
              IsBigO P (gammaSigma η) X
                (Real.exp
                  (Cscale * (Real.log (2 + hInf.thetaHat)) ^ (2 : ℕ))) ∧
              (∀ aω, 1 ≤ X aω) ∧
                ∀ᵐ aω ∂P,
                  ∀ (ha : Ch04.AELocallyUniformlyEllipticField aω) {m : ℕ},
                    X aω ≤ (3 : ℝ) ^ m →
                    let Cresp : ℝ :=
                      Real.sqrt
                        (4 * (Fintype.card (BlockCoord d) : ℝ) *
                          (Fintype.card (NormalizedProbeIndex d) : ℝ));
                    let Cneg : ℝ :=
                      (Ch02.geometricDiscount (τ / 2) 1)⁻¹ *
                        (2 * Real.sqrt
                          ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)));
                    let A : ℝ := max Cresp Cneg * Real.rpow (3 : ℝ) (τ / 2);
                    Ch02.HomogenizationErrorOnCube
                        (originCube d ((m : ℕ) : ℤ)) r
                        Ch02.MultiscaleExponent.infinity (.finite q)
                        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
                          aω ha)
                        (scalarMatrix (d := d) (barSigmaLimit hP hStruct)) ≤
                      Real.rpow
                          (Ch02.geometricDiscount r q *
                            (Ch02.geometricDiscount (r - τ / 2) q)⁻¹)
                          (1 / q) *
                        A *
                          Real.sqrt (((3 : ℝ) ^ m / X aω) ^ (-α)) := by
  obtain ⟨α, hα_pos, hαmax, hJbase⟩ :=
    exists_quenchedLocalizedEstimate_uniformEndpoint_expLogSq_parameterAlpha
      (d := d) params
  refine ⟨α, hα_pos, hαmax, ?_⟩
  intro τ r q hτ_half hατ_half hτ_le_one hrq hδq hq
  dsimp only
  have hτ2_pos : 0 < τ / 2 :=
    (max_sUpper_sLower_pos params).trans hτ_half
  have hτ_pos : 0 < τ := by linarith
  have hmaxτ : max params.sUpper params.sLower < τ := by
    have hhalf_lt : τ / 2 < τ := by linarith
    exact hτ_half.trans hhalf_lt
  have hτ_dim : τ ≤ (d : ℝ) / 2 := by
    have hd : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast params.two_le_dim
    have hone : (1 : ℝ) ≤ (d : ℝ) / 2 := by nlinarith
    exact hτ_le_one.trans hone
  let η : ℝ := ((d : ℕ) : ℝ)
  have hη_pos : 0 < η := by
    dsimp [η]
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2)
      params.two_le_dim
  obtain ⟨CJ, hCJ_pos, hJlaw⟩ :=
    hJbase (t := τ) hmaxτ hτ_dim
  let Kunit : ℝ := Ch04.gammaMomentConst (1 : ℝ) * (params.xi : ℝ)
  let Aextra : ℝ := (max 1 Kunit) ^ α⁻¹
  let pextra : ℝ := 2 * α⁻¹
  let CD : ℝ := 4 * max 0 (Real.log Aextra) + 2 * pextra
  let Ksup : ℝ := (3 * Real.log (2 : ℝ)) ^ η⁻¹
  let Cscale : ℝ := 4 * max 0 (Real.log Ksup) + CJ + CD
  have hKunit_pos : 0 < Kunit := by
    dsimp [Kunit]
    exact mul_pos (IndependentSums.gammaMomentConst_pos zero_lt_one)
      (by exact_mod_cast params.xi_pos)
  have hAextra_pos : 0 < Aextra := by
    dsimp [Aextra]
    exact Real.rpow_pos_of_pos
      (lt_of_lt_of_le zero_lt_one (le_max_left 1 Kunit)) α⁻¹
  have hpextra_nonneg : 0 ≤ pextra := by
    dsimp [pextra]
    positivity
  have hCD_nonneg : 0 ≤ CD := by
    dsimp [CD]
    have hlog_nonneg : 0 ≤ max 0 (Real.log Aextra) := le_max_left 0 _
    nlinarith
  have hKsup_pos : 0 < Ksup := by
    dsimp [Ksup]
    exact Real.rpow_pos_of_pos
      (mul_pos (by norm_num : (0 : ℝ) < 3)
        (Real.log_pos (by norm_num : (1 : ℝ) < 2))) _
  have hCscale_pos : 0 < Cscale := by
    dsimp [Cscale]
    have hlog_nonneg : 0 ≤ max 0 (Real.log Ksup) := le_max_left 0 _
    nlinarith
  refine ⟨Cscale, hCscale_pos, ?_⟩
  intro P hP hStruct hInf hparams
  let : IsProbabilityMeasure P := hP.isProbability
  obtain ⟨XJ, hOJ, hXJ_one, hJpoint⟩ :=
    hJlaw hP hStruct hInf hparams
  let θ : ℝ := hInf.thetaHat
  let D : ℝ := (max 1 (Kunit * θ ^ (2 : ℕ))) ^ α⁻¹
  let X : RegCoeffField d → ℝ := fun aω => max (XJ aω) D
  have hD_one : 1 ≤ D := by
    dsimp [D]
    exact Real.one_le_rpow (le_max_left 1 (Kunit * θ ^ (2 : ℕ)))
      (inv_nonneg.mpr hα_pos.le)
  have hD_pos : 0 < D := lt_of_lt_of_le zero_lt_one hD_one
  have hDpow_eq : D ^ α = max 1 (Kunit * θ ^ (2 : ℕ)) := by
    dsimp [D]
    exact Real.rpow_inv_rpow
      (le_trans zero_le_one (le_max_left 1 (Kunit * θ ^ (2 : ℕ))))
      hα_pos.ne'
  have hKD_le : Kunit * θ ^ (2 : ℕ) ≤ D ^ α := by
    calc
      Kunit * θ ^ (2 : ℕ) ≤ max 1 (Kunit * θ ^ (2 : ℕ)) :=
        le_max_right 1 _
      _ = D ^ α := hDpow_eq.symm
  let AJ : ℝ := Real.exp (CJ * (Real.log (2 + θ)) ^ (2 : ℕ))
  have hOD_raw :
      IsBigO P (gammaSigma η) (fun _ : RegCoeffField d => D) D := by
    exact Ch04.isBigO_gammaSigma_const_of_abs_le
      (μ := P) (σ := η) (A := D) (c := D)
      hD_pos.le (by rw [abs_of_pos hD_pos])
  have hOmax_raw :
      IsBigO P (gammaSigma η) X (Ksup * max AJ D) := by
    simpa [X, Ksup, AJ, η] using
      isBigO_gammaSigma_max_two_of_scales
        (μ := P) (η := η) (AJ := AJ) (AU := D)
        hη_pos (by simpa [η, AJ, θ] using hOJ) hOD_raw
  have hD_poly : D ≤ Aextra * (max 1 θ) ^ pextra := by
    simpa [D, Kunit, Aextra, pextra, θ] using
      rpow_max_one_mul_sq_le_const_mul_rpow
        (A := Kunit) (θ := θ) (r := α⁻¹)
        hInf.thetaHat_pos.le (inv_nonneg.mpr hα_pos.le)
  have hD_exp :
      D ≤ Real.exp (CD * (Real.log (2 + θ)) ^ (2 : ℕ)) := by
    calc
      D ≤ Aextra * (max 1 θ) ^ pextra := hD_poly
      _ ≤ Real.exp (CD * (Real.log (2 + θ)) ^ (2 : ℕ)) := by
          simpa [CD, θ] using
            const_mul_rpow_max_one_le_exp_logSq
              (A := Aextra) (θ := θ) (p := pextra)
              hAextra_pos hInf.thetaHat_pos.le hpextra_nonneg
  have hscale_final :
      Ksup * max AJ D ≤
        Real.exp
          (Cscale * (Real.log (2 + θ)) ^ (2 : ℕ)) := by
    let L2 : ℝ := (Real.log (2 + θ)) ^ (2 : ℕ)
    let Ck : ℝ := 4 * max 0 (Real.log Ksup)
    have hL2_nonneg : 0 ≤ L2 := by dsimp [L2]; positivity
    have hAJ_le : AJ ≤ Real.exp ((CJ + CD) * L2) := by
      refine Real.exp_le_exp.mpr ?_
      dsimp [AJ, L2]
      nlinarith [mul_nonneg hCD_nonneg hL2_nonneg]
    have hD_le : D ≤ Real.exp ((CJ + CD) * L2) := by
      calc
        D ≤ Real.exp (CD * L2) := by simpa [L2] using hD_exp
        _ ≤ Real.exp ((CJ + CD) * L2) := by
            refine Real.exp_le_exp.mpr ?_
            nlinarith [mul_nonneg hCJ_pos.le hL2_nonneg]
    have hmax_le : max AJ D ≤ Real.exp ((CJ + CD) * L2) :=
      max_le hAJ_le hD_le
    have hK_le : Ksup ≤ Real.exp (Ck * L2) := by
      have hraw :=
        const_mul_rpow_max_one_le_exp_logSq
          (A := Ksup) (θ := θ) (p := (0 : ℝ))
          hKsup_pos hInf.thetaHat_pos.le (by norm_num)
      simpa [Ksup, Ck, L2, θ] using hraw
    calc
      Ksup * max AJ D
          ≤ Ksup * Real.exp ((CJ + CD) * L2) :=
            mul_le_mul_of_nonneg_left hmax_le hKsup_pos.le
      _ ≤ Real.exp (Ck * L2) * Real.exp ((CJ + CD) * L2) :=
            mul_le_mul_of_nonneg_right hK_le (Real.exp_pos _).le
      _ = Real.exp (Cscale * L2) := by
            rw [← Real.exp_add]
            dsimp [Cscale, Ck]
            ring_nf
  have hO :
      IsBigO P (gammaSigma η) X
        (Real.exp
          (Cscale * (Real.log (2 + hInf.thetaHat)) ^ (2 : ℕ))) :=
    IsBigO.mono_scale (μ := P) (Ψ := gammaSigma η) hOmax_raw
      (by simpa [θ] using hscale_final)
  refine ⟨X, hO, ?_, ?_⟩
  · intro aω
    dsimp [X]
    exact (hXJ_one aω).trans (le_max_left _ _)
  have hJprobeAE :
      ∀ᵐ aω ∂P,
        ∀ i : NormalizedProbeIndex d,
          ∀ {m n : ℕ},
            XJ aω ≤ (3 : ℝ) ^ m →
            n < m →
            (3 : ℝ) ^ (-τ * ((m - n : ℕ) : ℝ)) *
                localizedLimitNormalizedJMax hP hStruct m n
                  (normalizedProbeVec i) aω ≤
              ((3 : ℝ) ^ m / XJ aω) ^ (-α) := by
    rw [MeasureTheory.ae_all_iff]
    intro i
    exact hJpoint (normalizedProbeVec i)
      (normalizedProbeVec_dotProduct_self_le_one i)
  have hUnitAE :
      ∀ᵐ aω ∂P, ∀ m : ℕ,
        localizedLimitWeightedUnitEllipticitySup hP hStruct hInf.params m aω ≤
          Kunit * θ ^ (2 : ℕ) := by
    rw [MeasureTheory.ae_all_iff]
    intro m
    simpa [Kunit, θ, hparams] using!
      hInf.localizedLimitWeightedUnitEllipticitySup_le_thetaHat_sq_ae
        (m := m)
  filter_upwards [hJprobeAE, hUnitAE] with aω hJprobe hUnit
  intro ha m hXm
  let hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct :=
    hInf.toGammaSigma 1 zero_lt_one
  have hXJ_pos : 0 < XJ aω :=
    lt_of_lt_of_le zero_lt_one (hXJ_one aω)
  have hScale : max (XJ aω) D ≤ (3 : ℝ) ^ m := by
    simpa [X] using hXm
  have hUpper : hΓ.params.sUpper < τ / 2 := by
    have hs : params.sUpper ≤ max params.sUpper params.sLower := le_max_left _ _
    simpa [hΓ, GammaInfinityCoarseGrainedEllipticity.toGammaSigma, hparams]
      using hs.trans_lt hτ_half
  have hLower : hΓ.params.sLower < τ / 2 := by
    have hs : params.sLower ≤ max params.sUpper params.sLower := le_max_right _ _
    simpa [hΓ, GammaInfinityCoarseGrainedEllipticity.toGammaSigma, hparams]
      using hs.trans_lt hτ_half
  have hProbe :
      ∀ {n : ℕ},
        XJ aω ≤ (3 : ℝ) ^ m →
        n < m →
        Real.rpow (3 : ℝ) (-τ * ((m - n : ℕ) : ℝ)) *
            localizedNormalizedProbeJMax hP hStruct m n aω ≤
          ((3 : ℝ) ^ m / XJ aω) ^ (-α) := by
    intro n hXJn hnm
    let W : ℝ := Real.rpow (3 : ℝ) (-τ * ((m - n : ℕ) : ℝ))
    have hW_pos : 0 < W := by
      dsimp [W]
      positivity
    exact
      weighted_localizedNormalizedProbeJMax_le_of_forall_probe
        hP hStruct (m := m) (n := n) aω (W := W)
        (R := ((3 : ℝ) ^ m / XJ aω) ^ (-α))
        hW_pos
        (by
          intro i
          simpa [W] using hJprobe i hXJn hnm)
  have hα_le_τ : α ≤ τ := by nlinarith
  have hUnit_m :
      localizedLimitWeightedUnitEllipticitySup hP hStruct hΓ.params m aω ≤
        (Real.rpow (3 : ℝ) ((τ / 2) * (m : ℝ)) *
          Real.sqrt (((3 : ℝ) ^ m / D) ^ (-α))) ^ (2 : ℕ) := by
    have hunit' :
        localizedLimitWeightedUnitEllipticitySup hP hStruct hInf.params m aω ≤
          Kunit * θ ^ (2 : ℕ) := by
      exact hUnit m
    calc
      localizedLimitWeightedUnitEllipticitySup hP hStruct hΓ.params m aω
          =
        localizedLimitWeightedUnitEllipticitySup hP hStruct hInf.params m aω := by
          simp [hΓ, GammaInfinityCoarseGrainedEllipticity.toGammaSigma]
      _ ≤ Kunit * θ ^ (2 : ℕ) := hunit'
      _ ≤
        (Real.rpow (3 : ℝ) ((τ / 2) * (m : ℝ)) *
          Real.sqrt (((3 : ℝ) ^ m / D) ^ (-α))) ^ (2 : ℕ) :=
            deterministic_unitEllipticity_bound_le_squareEnvelope
              (K := Kunit) (θ := θ) (D := D) (τ := τ) (α := α)
              (m := m) hKD_le hD_pos hα_le_τ
  simpa [X, hΓ, GammaInfinityCoarseGrainedEllipticity.toGammaSigma] using
    homogenizationErrorOnOriginCube_le_of_two_minimalScales_probeJ
      hP hStruct hΓ ha (m := m) (r := r) (τ := τ)
      (δ := r - τ / 2) (q := q) (XJ := XJ aω) (XU := D)
      (α := α) rfl hτ_pos hrq hδq hq hUpper hLower hα_pos.le
      hXJ_pos hD_pos hProbe hUnit_m hScale

end

end Section57
end Ch05
end Book
end Homogenization
