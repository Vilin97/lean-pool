/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.UniformBadScaleMinimalQuantitative
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.AbsoluteScaleCompression

/-! # Uniform Scale Compression Final -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

/-!
# Scale compression at the uniform endpoint

This file compresses the explicit `Γ∞` endpoint minimal-scale normalization to
the manuscript `exp(C log^2(2 + thetaHat))` envelope.
-/

noncomputable section

theorem uniformEndpointHighDenominator_mul_sq_le_const_mul_rpow
    {A B θ t η : ℝ}
    (hA : 0 ≤ A) (hθ : 0 ≤ θ)
    (ht : 0 < t) (htη : t ≤ η / 2) :
    let κ : ℝ := (η - 2 * t) / t
    let C : ℝ := max 1 (((max 1 A) ^ (2 : ℝ)) * ((max 1 B) ^ κ))
    let p : ℝ := 4 + 2 * κ
    uniformEndpointHighDenominator (A * θ ^ (2 : ℕ)) (B * θ ^ (2 : ℕ)) t η ≤
      C * (max 1 θ) ^ p := by
  intro κ C p
  have hκ_nonneg : 0 ≤ κ := by
    dsimp [κ]
    have hnum : 0 ≤ η - 2 * t := by linarith
    positivity
  have hp_nonneg : 0 ≤ p := by
    dsimp [p]
    nlinarith
  have hx_pos : 0 < max 1 θ :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 θ)
  have hxpow_one : 1 ≤ (max 1 θ) ^ p :=
    Real.one_le_rpow (le_max_left 1 θ) hp_nonneg
  have hDhi_nonneg : 0 ≤ A * θ ^ (2 : ℕ) := by positivity
  have hDhi_sq_le_max :
      (A * θ ^ (2 : ℕ)) ^ (2 : ℝ) ≤
        (max 1 (A * θ ^ (2 : ℕ))) ^ (2 : ℝ) :=
    Real.rpow_le_rpow hDhi_nonneg (le_max_right 1 _) (by norm_num)
  have hDhi_poly :
      (A * θ ^ (2 : ℕ)) ^ (2 : ℝ) ≤
        (max 1 A) ^ (2 : ℝ) * (max 1 θ) ^ (4 : ℝ) := by
    have h :=
      rpow_max_one_mul_sq_le_const_mul_rpow
        (A := A) (θ := θ) (r := (2 : ℝ)) hθ (by norm_num)
    calc
      (A * θ ^ (2 : ℕ)) ^ (2 : ℝ)
          ≤ (max 1 (A * θ ^ (2 : ℕ))) ^ (2 : ℝ) := hDhi_sq_le_max
      _ ≤ (max 1 A) ^ (2 : ℝ) * (max 1 θ) ^ (2 * (2 : ℝ)) := h
      _ = (max 1 A) ^ (2 : ℝ) * (max 1 θ) ^ (4 : ℝ) := by ring_nf
  have hDcr_poly :
      (max 1 (B * θ ^ (2 : ℕ))) ^ κ ≤
        (max 1 B) ^ κ * (max 1 θ) ^ (2 * κ) :=
    rpow_max_one_mul_sq_le_const_mul_rpow
      (A := B) (θ := θ) (r := κ) hθ hκ_nonneg
  have hDhi_poly_nonneg :
      0 ≤ (max 1 A) ^ (2 : ℝ) * (max 1 θ) ^ (4 : ℝ) := by
    positivity
  have hDcr_nonneg :
      0 ≤ (max 1 (B * θ ^ (2 : ℕ))) ^ κ := by
    exact (Real.rpow_pos_of_pos
      (lt_of_lt_of_le zero_lt_one (le_max_left 1 _)) κ).le
  have hconst_nonneg :
      0 ≤ (max 1 A) ^ (2 : ℝ) * (max 1 B) ^ κ := by
    positivity
  have hprod_poly :
      (A * θ ^ (2 : ℕ)) ^ (2 : ℝ) *
          (max 1 (B * θ ^ (2 : ℕ))) ^ κ ≤
        ((max 1 A) ^ (2 : ℝ) * (max 1 B) ^ κ) *
          (max 1 θ) ^ p := by
    calc
      (A * θ ^ (2 : ℕ)) ^ (2 : ℝ) *
          (max 1 (B * θ ^ (2 : ℕ))) ^ κ
          ≤ ((max 1 A) ^ (2 : ℝ) * (max 1 θ) ^ (4 : ℝ)) *
              ((max 1 B) ^ κ * (max 1 θ) ^ (2 * κ)) :=
            mul_le_mul hDhi_poly hDcr_poly hDcr_nonneg hDhi_poly_nonneg
      _ = ((max 1 A) ^ (2 : ℝ) * (max 1 B) ^ κ) *
              ((max 1 θ) ^ (4 : ℝ) * (max 1 θ) ^ (2 * κ)) := by ring
      _ = ((max 1 A) ^ (2 : ℝ) * (max 1 B) ^ κ) *
              (max 1 θ) ^ p := by
            dsimp [p]
            rw [← Real.rpow_add hx_pos]
  have hC_one : 1 ≤ C := by
    dsimp [C]
    exact le_max_left 1 _
  have hconst_le_C :
      (max 1 A) ^ (2 : ℝ) * (max 1 B) ^ κ ≤ C := by
    dsimp [C]
    exact le_max_right 1 _
  have hprod_le :
      (A * θ ^ (2 : ℕ)) ^ (2 : ℝ) *
          (max 1 (B * θ ^ (2 : ℕ))) ^ κ ≤
        C * (max 1 θ) ^ p :=
    hprod_poly.trans
      (mul_le_mul_of_nonneg_right hconst_le_C
        (Real.rpow_pos_of_pos hx_pos p).le)
  have hone_le : 1 ≤ C * (max 1 θ) ^ p := by
    nlinarith [hC_one, hxpow_one]
  simpa [uniformEndpointHighDenominator, κ, C, p] using
    max_le hone_le hprod_le

theorem uniformEndpointBlead_le_const_mul_rpow
    {A B θ t η U : ℝ}
    (hA : 0 ≤ A) (hθ : 0 ≤ θ)
    (ht : 0 < t) (htη : t ≤ η / 2) (hU : 0 ≤ U) :
    let κ : ℝ := (η - 2 * t) / t
    let Cden : ℝ :=
      max 1 (((max 1 A) ^ (2 : ℝ)) * ((max 1 B) ^ κ))
    let p : ℝ := 4 + 2 * κ
    let C : ℝ := Cden * U
    uniformEndpointHighDenominator (A * θ ^ (2 : ℕ)) (B * θ ^ (2 : ℕ)) t η *
        U ≤
      C * (max 1 θ) ^ p := by
  intro κ Cden p C
  have hden :=
    uniformEndpointHighDenominator_mul_sq_le_const_mul_rpow
      (A := A) (B := B) (θ := θ) (t := t) (η := η)
      hA hθ ht htη
  calc
    uniformEndpointHighDenominator (A * θ ^ (2 : ℕ)) (B * θ ^ (2 : ℕ)) t η * U
        ≤ (Cden * (max 1 θ) ^ p) * U :=
          mul_le_mul_of_nonneg_right (by simpa [κ, Cden, p] using hden) hU
    _ = C * (max 1 θ) ^ p := by
          dsimp [C]
          ring

theorem max_zero_log_le_log_max_one_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    max 0 (Real.log x) ≤ Real.log (max 1 x) := by
  by_cases hxzero : x = 0
  · simp [hxzero]
  have hx_pos : 0 < x := lt_of_le_of_ne hx (fun h => hxzero h.symm)
  by_cases h1x : 1 ≤ x
  · have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg h1x
    rw [max_eq_right hlog_nonneg, max_eq_right h1x]
  · have hx1 : x ≤ 1 := le_of_not_ge h1x
    have hlog_nonpos : Real.log x ≤ 0 := by
      simpa using Real.log_le_log hx_pos hx1
    rw [max_eq_left hlog_nonpos, max_eq_left hx1]
    simp

theorem max_zero_div_nonneg_le {x c : ℝ} (hc : 0 < c) :
    max 0 (x / c) ≤ max 0 x / c := by
  by_cases hx : 0 ≤ x
  · have hxdiv : 0 ≤ x / c := by positivity
    rw [max_eq_right hxdiv, max_eq_right hx]
  · have hxle : x ≤ 0 := le_of_not_ge hx
    have hxdivle : x / c ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg hxle hc.le
    rw [max_eq_left hxdivle, max_eq_left hxle]
    simp

theorem pow_three_uniformEndpoint_crudeCutoff_le_const_mul_rpow
    {A θ t L : ℝ}
    (hA : 0 < A) (hθ : 0 ≤ θ) (ht : 0 < t) (hL : 0 ≤ L) :
    let D : ℝ := A * θ ^ (2 : ℕ)
    let Qcrude : ℕ :=
      Nat.ceil
        ((Real.log D + (t * (L + 1)) * Real.log (3 : ℝ)) /
          (t * Real.log (3 : ℝ)))
    let C : ℝ := 3 * (3 : ℝ) ^ (L + 1) * (max 1 A) ^ t⁻¹
    (3 : ℝ) ^ Qcrude ≤ C * (max 1 θ) ^ (2 * t⁻¹) := by
  intro D Qcrude C
  let y : ℝ :=
    (Real.log D + (t * (L + 1)) * Real.log (3 : ℝ)) /
      (t * Real.log (3 : ℝ))
  have hlog3_pos : 0 < Real.log (3 : ℝ) :=
    Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hden_pos : 0 < t * Real.log (3 : ℝ) := mul_pos ht hlog3_pos
  have hL1_nonneg : 0 ≤ L + 1 := by linarith
  have hD_nonneg : 0 ≤ D := by dsimp [D]; positivity
  have hy_eq : y = L + 1 + Real.log D / (t * Real.log (3 : ℝ)) := by
    dsimp [y]
    field_simp [hden_pos.ne']
    ring
  have hmax_y :
      max 0 y ≤ L + 1 + max 0 (Real.log D) / (t * Real.log (3 : ℝ)) := by
    refine (max_le ?_ ?_)
    · exact add_nonneg hL1_nonneg (div_nonneg (le_max_left 0 _) hden_pos.le)
    · rw [hy_eq]
      calc
        L + 1 + Real.log D / (t * Real.log (3 : ℝ))
            ≤ L + 1 + max 0 (Real.log D / (t * Real.log (3 : ℝ))) :=
              by
                have h := le_max_right 0
                  (Real.log D / (t * Real.log (3 : ℝ)))
                linarith
        _ ≤ L + 1 + max 0 (Real.log D) / (t * Real.log (3 : ℝ)) :=
              by
                have h :=
                  max_zero_div_nonneg_le (x := Real.log D)
                    (c := t * Real.log (3 : ℝ)) hden_pos
                linarith
  have hceil_mono : Qcrude ≤ Nat.ceil (max 0 y) := by
    dsimp [Qcrude, y]
    exact Nat.ceil_mono (le_max_right 0 y)
  have hpow_ceil :
      (3 : ℝ) ^ Qcrude ≤
        3 * Real.exp (Real.log (3 : ℝ) * max 0 y) := by
    calc
      (3 : ℝ) ^ Qcrude
          ≤ (3 : ℝ) ^ Nat.ceil (max 0 y) :=
            pow_three_nat_mono hceil_mono
      _ ≤ 3 * Real.exp (Real.log (3 : ℝ) * max 0 y) :=
            pow_three_natCeil_le_three_mul_exp (le_max_left 0 y)
  have hexp_y :
      Real.exp (Real.log (3 : ℝ) * max 0 y) ≤
        (3 : ℝ) ^ (L + 1) * (max 1 D) ^ t⁻¹ := by
    have hlogD_bound :
        max 0 (Real.log D) / t ≤ Real.log (max 1 D) / t :=
      div_le_div_of_nonneg_right
        (max_zero_log_le_log_max_one_of_nonneg hD_nonneg) ht.le
    calc
      Real.exp (Real.log (3 : ℝ) * max 0 y)
          ≤ Real.exp
              (Real.log (3 : ℝ) *
                (L + 1 + max 0 (Real.log D) /
                  (t * Real.log (3 : ℝ)))) :=
            Real.exp_le_exp.mpr
              (mul_le_mul_of_nonneg_left hmax_y hlog3_pos.le)
      _ = (3 : ℝ) ^ (L + 1) *
            Real.exp (max 0 (Real.log D) / t) := by
          have harg :
              Real.log (3 : ℝ) *
                  (L + 1 + max 0 (Real.log D) /
                    (t * Real.log (3 : ℝ))) =
                Real.log (3 : ℝ) * (L + 1) +
                  max 0 (Real.log D) / t := by
            field_simp [ht.ne', hlog3_pos.ne']
          rw [harg, Real.exp_add]
          have h3 :
              Real.exp (Real.log (3 : ℝ) * (L + 1)) =
                (3 : ℝ) ^ (L + 1) := by
            rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
          rw [h3]
      _ ≤ (3 : ℝ) ^ (L + 1) * (max 1 D) ^ t⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc
            Real.exp (max 0 (Real.log D) / t)
                ≤ Real.exp (Real.log (max 1 D) / t) :=
                  Real.exp_le_exp.mpr hlogD_bound
            _ = (max 1 D) ^ t⁻¹ := by
                  have hmax_pos : 0 < max 1 D :=
                    lt_of_lt_of_le zero_lt_one (le_max_left 1 D)
                  rw [Real.rpow_def_of_pos hmax_pos]
                  ring_nf
  have hD_poly :
      (max 1 D) ^ t⁻¹ ≤
        (max 1 A) ^ t⁻¹ * (max 1 θ) ^ (2 * t⁻¹) := by
    simpa [D] using
      rpow_max_one_mul_sq_le_const_mul_rpow
        (A := A) (θ := θ) (r := t⁻¹) hθ (inv_nonneg.mpr ht.le)
  calc
    (3 : ℝ) ^ Qcrude
        ≤ 3 * Real.exp (Real.log (3 : ℝ) * max 0 y) := hpow_ceil
    _ ≤ 3 * ((3 : ℝ) ^ (L + 1) * (max 1 D) ^ t⁻¹) :=
        mul_le_mul_of_nonneg_left hexp_y (by norm_num)
    _ ≤ 3 * ((3 : ℝ) ^ (L + 1) *
        ((max 1 A) ^ t⁻¹ * (max 1 θ) ^ (2 * t⁻¹))) := by
        gcongr
    _ = C * (max 1 θ) ^ (2 * t⁻¹) := by
        dsimp [C]
        ring

theorem explicit_uniformEndpoint_minimalScale_prefactor_le_exp_logSq
    {d : ℕ} [NeZero d] {Cfluct Ccrude a t αbad : ℝ} {R : ℕ}
    (hCfluct : 0 < Cfluct) (hCcrude : 0 < Ccrude)
    (ha : 0 < a) (ht : 0 < t) (htb : t ≤ (d : ℝ) / 2) :
    let K : ℝ := quenchedProbeEnvelopeConst d
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
    let ρtop : ℝ := (3 : ℝ) ^ ctop
    let ρbottom : ℝ := (3 : ℝ) ^ (2 * (t - αbad) / η)
    let Cbottom : ℝ := Real.exp 1 * max 1 (S.card : ℝ)
    let Ctop : ℝ :=
      (S.card : ℝ) * weightedLinearExpKernelConst w (ρtop ^ (2 : ℝ))
    let Kbottom : ℝ := weightedGeometricExpKernelConst w (ρbottom ^ η)
    let M : ℝ := max 1 (max 0 Ctop + max 0 (Cbottom * Kbottom))
    let Qcut : ℕ := Nat.ceil ((L + 1) / (1 - αbad / a) + 1)
    ∃ Cscale : ℝ, 0 < Cscale ∧
      ∀ θ : ℝ, 0 < θ →
        let Dhigh : ℝ := 2 * K * Cfluct * θ ^ (2 : ℕ)
        let Dcrude : ℝ := K * Ccrude * θ ^ (2 : ℕ)
        let Den : ℝ := uniformEndpointHighDenominator Dhigh Dcrude t η
        let Blead : ℝ := Den * (3 : ℝ) ^ (L + 1)
        let Btail : ℝ := 2 * Blead
        let B : ℝ := max 1 Btail
        let cgap : ℝ := Blead ^ (-η) - Btail ^ (-η)
        let ρgap : ℝ := (3 : ℝ) ^ η
        let Qpref : ℕ :=
          max (Nat.ceil (max 0 (Real.log M)))
            (max R (Nat.ceil ((2 * max 0 (-(Real.log cgap))) /
              Real.log ρgap)))
        let Qlead : ℕ := Nat.ceil (Real.log Blead / Real.log 3)
        let Qcrude : ℕ :=
          Nat.ceil
            ((Real.log Dcrude + (t * (L + 1)) * Real.log (3 : ℝ)) /
              (t * Real.log (3 : ℝ)))
        let Q : ℕ := max Qpref (max Qlead (max Qcrude Qcut))
        3 * ((3 : ℝ) ^ Q) * B ≤
          Real.exp (Cscale * (Real.log (2 + θ)) ^ (2 : ℕ)) := by
  classical
  intro K S b L ctop η w ρtop ρbottom Cbottom Ctop Kbottom M Qcut
  have hK_pos : 0 < K := by
    simpa [K] using quenchedProbeEnvelopeConst_pos (d := d)
  have hη_pos : 0 < η := by
    dsimp [η]
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    have hlog_nonneg : 0 ≤ Real.log (max (2 * K) 1) :=
      Real.log_nonneg (le_max_right (2 * K) 1)
    positivity
  let Ahi : ℝ := 2 * K * Cfluct
  let Acr : ℝ := K * Ccrude
  let U : ℝ := (3 : ℝ) ^ (L + 1)
  let κ : ℝ := (η - 2 * t) / t
  let Cden : ℝ :=
    max 1 (((max 1 Ahi) ^ (2 : ℝ)) * ((max 1 Acr) ^ κ))
  let pDen : ℝ := 4 + 2 * κ
  let Ablead : ℝ := Cden * U
  have hAhi_pos : 0 < Ahi := by dsimp [Ahi]; positivity
  have hAcr_pos : 0 < Acr := by dsimp [Acr]; positivity
  have hU_pos : 0 < U := by dsimp [U]; positivity
  have hU_one : 1 ≤ U := by
    dsimp [U]
    exact Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 3) (by linarith)
  have hκ_nonneg : 0 ≤ κ := by
    dsimp [κ, η]
    have hnum : 0 ≤ ((d : ℕ) : ℝ) - 2 * t := by linarith
    positivity
  have hpDen_nonneg : 0 ≤ pDen := by
    dsimp [pDen]
    nlinarith
  have hCden_pos : 0 < Cden := by
    dsimp [Cden]
    exact lt_of_lt_of_le zero_lt_one (le_max_left 1 _)
  have hAlead_pos : 0 < Ablead := by
    dsimp [Ablead]
    exact mul_pos hCden_pos hU_pos
  obtain ⟨Cbase, hCbase_pos, hbase⟩ :=
    explicit_threshold_prefactor_le_exp_logSq_of_Blead_le_poly
      (η := η) (A := Ablead) (p := pDen) (M := M)
      (R := R) (Qcut := Qcut) hη_pos hAlead_pos hpDen_nonneg
  let CcrudePoly : ℝ := 3 * U * (max 1 Acr) ^ t⁻¹
  let pcrude : ℝ := 2 * t⁻¹
  let CcrudeScale : ℝ :=
    1 + (4 * max 0 (Real.log CcrudePoly) + 2 * pcrude)
  let Cscale : ℝ := Cbase + CcrudeScale
  have hCcrudePoly_pos : 0 < CcrudePoly := by
    dsimp [CcrudePoly, U]
    positivity
  have hpcrude_nonneg : 0 ≤ pcrude := by
    dsimp [pcrude]
    positivity
  have hCcrudeScale_pos : 0 < CcrudeScale := by
    dsimp [CcrudeScale]
    have hmax_nonneg : 0 ≤ max 0 (Real.log CcrudePoly) := le_max_left 0 _
    nlinarith
  have hCscale_pos : 0 < Cscale := by
    dsimp [Cscale]
    positivity
  refine ⟨Cscale, hCscale_pos, ?_⟩
  intro θ hθ_pos Dhigh Dcrude Den Blead Btail B cgap ρgap Qpref Qlead Qcrude Q
  let Qbase : ℕ := max Qpref (max Qlead Qcut)
  let L2 : ℝ := (Real.log (2 + θ)) ^ (2 : ℕ)
  have hθ_nonneg : 0 ≤ θ := hθ_pos.le
  have hDen_one : 1 ≤ Den := by
    simpa [Den] using
      one_le_uniformEndpointHighDenominator
        (Dhigh := Dhigh) (Dcrude := Dcrude) (t := t) (d := η)
  have hBlead_one : 1 ≤ Blead := by
    dsimp [Blead]
    nlinarith
  have hBlead_poly :
      Blead ≤ Ablead * (max 1 θ) ^ pDen := by
    simpa [Dhigh, Dcrude, Den, Blead, Ahi, Acr, U, κ, Cden, pDen, Ablead] using
      uniformEndpointBlead_le_const_mul_rpow
        (A := Ahi) (B := Acr) (θ := θ) (t := t) (η := η) (U := U)
        hAhi_pos.le hθ_nonneg ht (by simpa [η, b] using htb) hU_pos.le
  have hbaseθ :
      3 * ((3 : ℝ) ^ Qbase) * B ≤ Real.exp (Cbase * L2) := by
    simpa [Btail, B, cgap, ρgap, Qpref, Qlead, Qbase, L2] using
      hbase θ hθ_nonneg Blead hBlead_one hBlead_poly
  have hqcrude_poly :
      (3 : ℝ) ^ Qcrude ≤ CcrudePoly * (max 1 θ) ^ pcrude := by
    simpa [Dcrude, Qcrude, CcrudePoly, pcrude, Acr, U] using
      pow_three_uniformEndpoint_crudeCutoff_le_const_mul_rpow
        (A := Acr) (θ := θ) (t := t) (L := L)
        hAcr_pos hθ_nonneg ht hL_nonneg
  have hqcrude_exp :
      (3 : ℝ) ^ Qcrude ≤ Real.exp (CcrudeScale * L2) := by
    have hraw :=
      const_mul_rpow_max_one_le_exp_logSq
        (A := CcrudePoly) (θ := θ) (p := pcrude)
        hCcrudePoly_pos hθ_nonneg hpcrude_nonneg
    have hraw' :
        CcrudePoly * (max 1 θ) ^ pcrude ≤
          Real.exp ((4 * max 0 (Real.log CcrudePoly) + 2 * pcrude) * L2) := by
      simpa [L2] using hraw
    have hscale :
        Real.exp ((4 * max 0 (Real.log CcrudePoly) + 2 * pcrude) * L2) ≤
          Real.exp (CcrudeScale * L2) := by
      refine Real.exp_le_exp.mpr ?_
      have hL2_nonneg : 0 ≤ L2 := by dsimp [L2]; positivity
      have hcoef :
          4 * max 0 (Real.log CcrudePoly) + 2 * pcrude ≤ CcrudeScale := by
        dsimp [CcrudeScale]
        linarith
      exact mul_le_mul_of_nonneg_right hcoef hL2_nonneg
    exact hqcrude_poly.trans (hraw'.trans hscale)
  have hQ_le : Q ≤ Qbase + Qcrude := by
    dsimp [Q, Qbase]
    omega
  have hpowQ :
      (3 : ℝ) ^ Q ≤ (3 : ℝ) ^ (Qbase + Qcrude) :=
    pow_three_nat_mono hQ_le
  have hcombine :
      3 * ((3 : ℝ) ^ Q) * B ≤
        (3 * ((3 : ℝ) ^ Qbase) * B) * (3 : ℝ) ^ Qcrude := by
    calc
      3 * ((3 : ℝ) ^ Q) * B
          ≤ 3 * ((3 : ℝ) ^ (Qbase + Qcrude)) * B := by
            gcongr
      _ = (3 * ((3 : ℝ) ^ Qbase) * B) * (3 : ℝ) ^ Qcrude := by
            rw [pow_add]
            ring
  calc
    3 * ((3 : ℝ) ^ Q) * B
        ≤ (3 * ((3 : ℝ) ^ Qbase) * B) * (3 : ℝ) ^ Qcrude := hcombine
    _ ≤ Real.exp (Cbase * L2) * Real.exp (CcrudeScale * L2) := by
        exact mul_le_mul hbaseθ hqcrude_exp (by positivity) (by positivity)
    _ = Real.exp (Cscale * L2) := by
        rw [← Real.exp_add]
        dsimp [Cscale]
        ring_nf

end

end Section57
end Ch05
end Book
end Homogenization
