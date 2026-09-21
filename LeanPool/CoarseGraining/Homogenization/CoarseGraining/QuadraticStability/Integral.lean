/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.L2Space
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.QuadraticStability.CauchySchwarz

/-! # Integral -/

namespace Homogenization

/-!
# Quadratic stability, item B′3 (integral form)

The integral half of Lemma 4.1 (`l.quadratic.stability`) of the high-moment
paper (Armstrong–Kuusi–Loher, to appear): stability of the two quadratic
minima under an `L∞`-comparable perturbation of the coefficient field supported
on `S`.

We assume only the two scalar Euler identities at the single test field
`Y := Zt − Z` (no subspace, no minimization, no existence), and derive the
sharpened bound with constant `6K`.

## Chosen integrability package for `(h4)`

We assume `IntegrableOn` over `U` of the five real-valued pairing integrands
that actually appear in the proof:

* `x ↦ Z·BZ`, `x ↦ Z·BtZ`, `x ↦ Y·BtY`  (three diagonal energies), and
* `x ↦ Z·BtY`, `x ↦ Z·BY`  (the two cross pairings with the test field `Y`).

This is the minimal explicit list sufficient for every integral split, the
Cauchy–Schwarz step, and the localization; each hypothesis is a concrete
`ℝ`-valued `IntegrableOn`, directly dischargeable by a consumer holding
`L²` minimizers.  (The energy `Zt·BtZt` needs no separate hypothesis: it equals
`Z·BtZ + 2 Z·BtY + Y·BtY` a.e. by symmetry.)

No `EuclideanSpace`.
-/

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-! ## Two elementary analytic helpers -/

/-- Integral Cauchy–Schwarz for two nonnegative integrable functions:
`∫ √f·√g ≤ √(∫f)·√(∫g)`. -/
theorem integral_sqrt_mul_sqrt_le
    {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g) :
    ∫ x, Real.sqrt (f x) * Real.sqrt (g x) ∂μ ≤
      Real.sqrt (∫ x, f x ∂μ) * Real.sqrt (∫ x, g x ∂μ) := by
  have hsf_meas : AEStronglyMeasurable (fun x => Real.sqrt (f x)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hf.1
  have hsg_meas : AEStronglyMeasurable (fun x => Real.sqrt (g x)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hg.1
  have hsqf : (fun x => Real.sqrt (f x) ^ 2) =ᵐ[μ] f := by
    filter_upwards [hf0] with x hx; rw [Real.sq_sqrt hx]
  have hsqg : (fun x => Real.sqrt (g x) ^ 2) =ᵐ[μ] g := by
    filter_upwards [hg0] with x hx; rw [Real.sq_sqrt hx]
  have hmemf : MemLp (fun x => Real.sqrt (f x)) 2 μ :=
    (memLp_two_iff_integrable_sq hsf_meas).2 (hf.congr hsqf.symm)
  have hmemg : MemLp (fun x => Real.sqrt (g x)) 2 μ :=
    (memLp_two_iff_integrable_sq hsg_meas).2 (hg.congr hsqg.symm)
  have hsf0 : 0 ≤ᵐ[μ] fun x => Real.sqrt (f x) :=
    Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _
  have hsg0 : 0 ≤ᵐ[μ] fun x => Real.sqrt (g x) :=
    Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _
  have key := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    hsf0 hsg0 (by simpa using hmemf) (by simpa using hmemg)
  have hrf : ∫ x, Real.sqrt (f x) ^ (2 : ℝ) ∂μ = ∫ x, f x ∂μ :=
    integral_congr_ae (by filter_upwards [hf0] with x hx; rw [Real.rpow_two, Real.sq_sqrt hx])
  have hrg : ∫ x, Real.sqrt (g x) ^ (2 : ℝ) ∂μ = ∫ x, g x ∂μ :=
    integral_congr_ae (by filter_upwards [hg0] with x hx; rw [Real.rpow_two, Real.sq_sqrt hx])
  rw [hrf, hrg] at key
  rw [Real.sqrt_eq_rpow (∫ x, f x ∂μ), Real.sqrt_eq_rpow (∫ x, g x ∂μ)]
  convert key using 2

/-- AM–GM in the form `√a·√b ≤ (a+b)/2` for nonnegative reals. -/
theorem sqrt_mul_sqrt_le_half_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt a * Real.sqrt b ≤ (a + b) / 2 := by
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb,
    Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- If `0 ≤ G` and `G ≤ C·√G` with `0 ≤ C`, then `G ≤ C²`. -/
theorem le_sq_of_le_mul_sqrt {G C : ℝ} (hG : 0 ≤ G) (hC : 0 ≤ C)
    (h : G ≤ C * Real.sqrt G) : G ≤ C ^ 2 := by
  have hsG : Real.sqrt G ≤ C := by
    rcases eq_or_lt_of_le (Real.sqrt_nonneg G) with h0 | hpos
    · exact h0 ▸ hC
    · have hGsq : Real.sqrt G * Real.sqrt G ≤ C * Real.sqrt G := by
        rw [Real.mul_self_sqrt hG]; exact h
      exact le_of_mul_le_mul_right hGsq hpos
  calc G = Real.sqrt G ^ 2 := (Real.sq_sqrt hG).symm
    _ ≤ C ^ 2 := by gcongr

/-! ## Data and hypotheses for B′3 -/

/-- **B′3.**  Stability of the two quadratic minima under an `L∞`-comparable,
`S`-supported perturbation.  Constant `6K`. -/
theorem abs_setIntegral_energy_sub_le
    {U S : Set (Vec d)} {B Bt : Vec d → BlockMat d} {Z Zt : Vec d → BlockVec d} {K : ℝ}
    (hU : MeasurableSet U) (hS : MeasurableSet S) (hSU : S ⊆ U)
    (hK : 1 ≤ K)
    -- (h1)+(h2, a.e. part) bundled: pointwise matrix facts a.e. on `U`.
    (hae : ∀ᵐ x ∂(volume.restrict U),
      IsSymmetricBlockMat (B x) ∧ IsSymmetricBlockMat (Bt x) ∧
      (∀ W : BlockVec d, 0 ≤ blockVecDot W (blockMatVecMul (B x) W)) ∧
      (∀ W : BlockVec d, 0 ≤ blockVecDot W (blockMatVecMul (Bt x) W)) ∧
      BlockMatLoewnerLE (Bt x) (K • B x) ∧ BlockMatLoewnerLE (B x) (K • Bt x))
    -- (h3) coefficient agreement off `S`.
    (hagree : ∀ᵐ x ∂(volume.restrict (U \ S)), B x = Bt x)
    -- (h4) integrability package (see module docstring).
    (hIntBZZ : IntegrableOn (fun x => blockVecDot (Z x) (blockMatVecMul (B x) (Z x))) U)
    (hIntBtZZ : IntegrableOn (fun x => blockVecDot (Z x) (blockMatVecMul (Bt x) (Z x))) U)
    (hIntBtYY : IntegrableOn
      (fun x => blockVecDot (Zt x - Z x) (blockMatVecMul (Bt x) (Zt x - Z x))) U)
    (hIntBtZY : IntegrableOn
      (fun x => blockVecDot (Z x) (blockMatVecMul (Bt x) (Zt x - Z x))) U)
    (hIntBZY : IntegrableOn
      (fun x => blockVecDot (Z x) (blockMatVecMul (B x) (Zt x - Z x))) U)
    -- (h5) the two scalar Euler identities at the single test field `Y`.
    (hEulerB : ∫ x in U, blockVecDot (Zt x - Z x) (blockMatVecMul (B x) (Z x)) = 0)
    (hEulerBt : ∫ x in U, blockVecDot (Zt x - Z x) (blockMatVecMul (Bt x) (Zt x)) = 0) :
    |(∫ x in U, blockVecDot (Zt x) (blockMatVecMul (Bt x) (Zt x))) -
        (∫ x in U, blockVecDot (Z x) (blockMatVecMul (B x) (Z x)))| ≤
      6 * K * ∫ x in S, blockVecDot (Z x) (blockMatVecMul (B x) (Z x)) := by
  classical
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK
  set Y : Vec d → BlockVec d := fun x => Zt x - Z x with hY
  -- integrand abbreviations
  set eB : Vec d → ℝ := fun x => blockVecDot (Z x) (blockMatVecMul (B x) (Z x)) with heB
  set eBtZ : Vec d → ℝ := fun x => blockVecDot (Z x) (blockMatVecMul (Bt x) (Z x)) with heBtZ
  set eBtY : Vec d → ℝ := fun x => blockVecDot (Y x) (blockMatVecMul (Bt x) (Y x)) with heBtY
  set pBtZY : Vec d → ℝ := fun x => blockVecDot (Z x) (blockMatVecMul (Bt x) (Y x)) with hpBtZY
  set pBZY : Vec d → ℝ := fun x => blockVecDot (Z x) (blockMatVecMul (B x) (Y x)) with hpBZY
  set eBtZt : Vec d → ℝ := fun x => blockVecDot (Zt x) (blockMatVecMul (Bt x) (Zt x)) with heBtZt
  -- rename integrability hypotheses to the abbreviations
  have hIA : IntegrableOn eB U := hIntBZZ
  have hIC : IntegrableOn eBtZ U := hIntBtZZ
  have hID : IntegrableOn eBtY U := hIntBtYY
  have hIE : IntegrableOn pBtZY U := hIntBtZY
  have hIF : IntegrableOn pBZY U := hIntBZY
  -- abbreviations for the energy integrals
  set G : ℝ := ∫ x in U, eBtY x with hG
  set ES : ℝ := ∫ x in S, eB x with hES
  set Etot : ℝ := ∫ x in U, eB x with hEtot
  set Ettot : ℝ := ∫ x in U, eBtZt x with hEttot
  -- a.e. facts restricted to `S`
  have haeS : ∀ᵐ x ∂(volume.restrict S), _ :=
    hae.filter_mono (ae_mono (Measure.restrict_mono hSU le_rfl))
  -- `Zt x = Z x + Y x`
  have hZt : ∀ x, Zt x = Z x + Y x := by intro x; simp only [hY]; abel
  ------------------------------------------------------------------
  -- Nonnegativity of the two `S`-energies and of `G`.
  ------------------------------------------------------------------
  have heB0U : 0 ≤ᵐ[volume.restrict U] eB := by
    filter_upwards [hae] with x hx using hx.2.2.1 (Z x)
  have heB0S : 0 ≤ᵐ[volume.restrict S] eB := by
    filter_upwards [haeS] with x hx using hx.2.2.1 (Z x)
  have heBtY0U : 0 ≤ᵐ[volume.restrict U] eBtY := by
    filter_upwards [hae] with x hx using hx.2.2.2.1 (Y x)
  have hES0 : 0 ≤ ES := setIntegral_nonneg_of_ae_restrict heB0S
  have hG0 : 0 ≤ G := setIntegral_nonneg_of_ae_restrict heBtY0U
  ------------------------------------------------------------------
  -- Euler-derived integral identities.
  ------------------------------------------------------------------
  -- `∫_U Z·BY = 0`  (first Euler + a.e. symmetry of `B`).
  have hpBZY0 : (∫ x in U, pBZY x) = 0 := by
    have hsym : pBZY =ᵐ[volume.restrict U]
        fun x => blockVecDot (Y x) (blockMatVecMul (B x) (Z x)) := by
      filter_upwards [hae] with x hx
      exact blockVecDot_blockMatVecMul_comm_of_isSymmetricBlockMat hx.1 (Z x) (Y x)
    rw [integral_congr_ae hsym]; exact hEulerB
  -- `∫_U Z·BtY = -G`  (second Euler + a.e. symmetry of `Bt`).
  have hpBtZY_eq : (∫ x in U, pBtZY x) = -G := by
    have hsplit : (fun x => blockVecDot (Y x) (blockMatVecMul (Bt x) (Zt x)))
        =ᵐ[volume.restrict U] fun x => pBtZY x + eBtY x := by
      filter_upwards [hae] with x hx
      have hcomm : blockVecDot (Y x) (blockMatVecMul (Bt x) (Z x)) =
          blockVecDot (Z x) (blockMatVecMul (Bt x) (Y x)) :=
        blockVecDot_blockMatVecMul_comm_of_isSymmetricBlockMat hx.2.1 (Y x) (Z x)
      simp only [hpBtZY, heBtY, hZt x, blockMatVecMul_add, blockVecDot_add_right, hcomm]
    have := hEulerBt
    rw [integral_congr_ae hsplit, integral_add hIE hID] at this
    linarith [this]
  ------------------------------------------------------------------
  -- Step (ii): `G ≤ 4K·ES`.
  ------------------------------------------------------------------
  -- defect field `δ1 = Z·(Bt−B)Y`, vanishing a.e. off `S`.
  set δ1 : Vec d → ℝ := fun x => pBtZY x - pBZY x with hδ1
  have hID1 : IntegrableOn δ1 U := hIE.sub hIF
  have hδ1_off : ∀ᵐ x ∂volume, x ∈ U \ S → δ1 x = 0 := by
    rw [← ae_restrict_iff' (hU.diff hS)]
    filter_upwards [hagree] with x hx
    simp only [hδ1, hpBtZY, hpBZY, hx, sub_self]
  -- `∫_U δ1 = -G`
  have hδ1U : (∫ x in U, δ1 x) = -G := by
    rw [show (fun x => δ1 x) = fun x => pBtZY x - pBZY x from rfl,
      integral_sub hIE hIF, hpBtZY_eq, hpBZY0]; ring
  -- localize to `S`
  have hδ1S : (∫ x in S, δ1 x) = -G := by
    rw [← setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hU.nullMeasurableSet hSU hδ1_off]; exact hδ1U
  -- pointwise bound on `S`: `|δ1| ≤ 2√K·√eB·√eBtY`
  set h1 : Vec d → ℝ := fun x => 2 * Real.sqrt K * Real.sqrt (eB x) * Real.sqrt (eBtY x) with hh1
  have hbound1 : ∀ᵐ x ∂(volume.restrict S), |δ1 x| ≤ h1 x := by
    filter_upwards [haeS] with x hx
    have hb2 := abs_blockVecDot_sub_le_of_blockMatLoewnerLE
      hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hK hx.2.2.2.2.1 hx.2.2.2.2.2 (Z x) (Y x)
    simpa only [hδ1, hpBtZY, hpBZY, heB, heBtY, hh1, mul_assoc] using hb2
  -- `h1` is integrable on `S` (dominated by `√K·(eB+eBtY)`)
  have hIA_S : IntegrableOn eB S := hIA.mono_set hSU
  have hIC_S : IntegrableOn eBtZ S := hIC.mono_set hSU
  have hID_S : IntegrableOn eBtY S := hID.mono_set hSU
  have hID1_S : IntegrableOn δ1 S := hID1.mono_set hSU
  have hh1_meas : AEStronglyMeasurable h1 (volume.restrict S) := by
    apply AEStronglyMeasurable.mul
    apply AEStronglyMeasurable.mul
    · exact aestronglyMeasurable_const
    · exact Real.continuous_sqrt.comp_aestronglyMeasurable hIA_S.1
    · exact Real.continuous_sqrt.comp_aestronglyMeasurable hID_S.1
  have hIh1_S : IntegrableOn h1 S := by
    refine Integrable.mono' (g := fun x => Real.sqrt K * (eB x + eBtY x))
      ((hIA_S.add hID_S).const_mul (Real.sqrt K)) hh1_meas ?_
    filter_upwards [heB0S, (ae_mono (Measure.restrict_mono hSU le_rfl) heBtY0U)]
      with x hxB hxD
    have hle := sqrt_mul_sqrt_le_half_add hxB hxD
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hK' : (0 : ℝ) ≤ Real.sqrt K := Real.sqrt_nonneg _
    nlinarith [hle, hK', mul_le_mul_of_nonneg_left hle (by positivity : (0:ℝ) ≤ 2 * Real.sqrt K)]
  -- integrate the pointwise bound and apply Cauchy–Schwarz
  have hStep : G ≤ 2 * Real.sqrt K * Real.sqrt ES * Real.sqrt G := by
    have habs : G = |∫ x in S, δ1 x| := by rw [hδ1S, abs_neg, abs_of_nonneg hG0]
    have hle1 : |∫ x in S, δ1 x| ≤ ∫ x in S, |δ1 x| := by
      simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := volume.restrict S) δ1
    have hle2 : (∫ x in S, |δ1 x|) ≤ ∫ x in S, h1 x :=
      setIntegral_mono_ae_restrict hID1_S.abs hIh1_S hbound1
    -- `∫_S h1 = 2√K · ∫_S √eB·√eBtY`
    have hh1_int : (∫ x in S, h1 x) =
        2 * Real.sqrt K * ∫ x in S, Real.sqrt (eB x) * Real.sqrt (eBtY x) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hh1]; ring
    have hcs : (∫ x in S, Real.sqrt (eB x) * Real.sqrt (eBtY x)) ≤
        Real.sqrt ES * Real.sqrt (∫ x in S, eBtY x) := by
      rw [hES]
      exact integral_sqrt_mul_sqrt_le hIA_S hID_S heB0S
        (ae_mono (Measure.restrict_mono hSU le_rfl) heBtY0U)
    -- monotonicity: `∫_S eBtY ≤ G`
    have hmono : (∫ x in S, eBtY x) ≤ G := by
      rw [hG]; exact setIntegral_mono_set hID heBtY0U (LE.le.eventuallyLE hSU)
    have hsqrtES : (0 : ℝ) ≤ Real.sqrt ES := Real.sqrt_nonneg _
    have hmono' : Real.sqrt (∫ x in S, eBtY x) ≤ Real.sqrt G := Real.sqrt_le_sqrt hmono
    calc G = |∫ x in S, δ1 x| := habs
      _ ≤ ∫ x in S, |δ1 x| := hle1
      _ ≤ ∫ x in S, h1 x := hle2
      _ = 2 * Real.sqrt K * ∫ x in S, Real.sqrt (eB x) * Real.sqrt (eBtY x) := hh1_int
      _ ≤ 2 * Real.sqrt K * (Real.sqrt ES * Real.sqrt (∫ x in S, eBtY x)) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ ≤ 2 * Real.sqrt K * (Real.sqrt ES * Real.sqrt G) := by gcongr
      _ = 2 * Real.sqrt K * Real.sqrt ES * Real.sqrt G := by ring
  have hG4 : G ≤ 4 * K * ES := by
    have := le_sq_of_le_mul_sqrt hG0 (by positivity) hStep
    have hsq : (2 * Real.sqrt K * Real.sqrt ES) ^ 2 = 4 * K * ES := by
      have hKe : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK0
      have hEe : Real.sqrt ES ^ 2 = ES := Real.sq_sqrt hES0
      nlinarith [hKe, hEe]
    rwa [hsq] at this
  ------------------------------------------------------------------
  -- Step (iii): the exact identity `Ettot − Etot = ∫_S δ2 − G`.
  ------------------------------------------------------------------
  set δ2 : Vec d → ℝ := fun x => eBtZ x - eB x with hδ2
  have hID2 : IntegrableOn δ2 U := hIC.sub hIA
  have hID2_S : IntegrableOn δ2 S := hID2.mono_set hSU
  have hδ2_off : ∀ᵐ x ∂volume, x ∈ U \ S → δ2 x = 0 := by
    rw [← ae_restrict_iff' (hU.diff hS)]
    filter_upwards [hagree] with x hx
    simp only [hδ2, heBtZ, heB, hx, sub_self]
  -- `Ettot = ∫_U eBtZ − G`
  have hEttot_eq : Ettot = (∫ x in U, eBtZ x) - G := by
    have hexp : eBtZt =ᵐ[volume.restrict U] fun x => eBtZ x + 2 * pBtZY x + eBtY x := by
      filter_upwards [hae] with x hx
      have hcomm : blockVecDot (Y x) (blockMatVecMul (Bt x) (Z x)) =
          blockVecDot (Z x) (blockMatVecMul (Bt x) (Y x)) :=
        blockVecDot_blockMatVecMul_comm_of_isSymmetricBlockMat hx.2.1 (Y x) (Z x)
      simp only [heBtZt, heBtZ, hpBtZY, heBtY, hZt x, blockMatVecMul_add,
        blockVecDot_add_left, blockVecDot_add_right, hcomm]
      ring
    have hstep1 : (∫ x in U, eBtZt x) =
        (∫ x in U, (eBtZ x + 2 * pBtZY x)) + ∫ x in U, eBtY x := by
      rw [integral_congr_ae hexp]
      exact integral_add (hIC.add (hIE.const_mul 2)) hID
    have hstep2 : (∫ x in U, (eBtZ x + 2 * pBtZY x)) =
        (∫ x in U, eBtZ x) + 2 * ∫ x in U, pBtZY x := by
      rw [integral_add hIC (hIE.const_mul 2), integral_const_mul]
    rw [hEttot, hstep1, hstep2, hpBtZY_eq]; ring
  -- `Ettot − Etot = ∫_S δ2 − G`
  have hIdentity : Ettot - Etot = (∫ x in S, δ2 x) - G := by
    have hδ2U : (∫ x in U, δ2 x) = (∫ x in U, eBtZ x) - Etot := by
      rw [hEtot]; exact integral_sub hIC hIA
    have hδ2S : (∫ x in S, δ2 x) = (∫ x in U, δ2 x) :=
      (setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hU.nullMeasurableSet hSU hδ2_off).symm
    rw [hEttot_eq, hδ2S, hδ2U]; ring
  ------------------------------------------------------------------
  -- Step (iv): `|∫_S δ2| ≤ 2K·ES`.
  ------------------------------------------------------------------
  have hbound2 : ∀ᵐ x ∂(volume.restrict S), |δ2 x| ≤ 2 * K * eB x := by
    filter_upwards [haeS] with x hx
    have hb2 := abs_blockVecDot_sub_le_of_blockMatLoewnerLE
      hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hK hx.2.2.2.2.1 hx.2.2.2.2.2 (Z x) (Z x)
    -- `eBtZ x ≤ K·eB x`
    have hloew : eBtZ x ≤ K * eB x :=
      blockVecDot_le_smul_of_blockMatLoewnerLE hx.2.2.2.2.1 (Z x)
    have heBx : 0 ≤ eB x := hx.2.2.1 (Z x)
    -- turn the B′2 sqrt-bound into `2K·eB`
    have hsqrtle : Real.sqrt (eBtZ x) ≤ Real.sqrt K * Real.sqrt (eB x) := by
      calc Real.sqrt (eBtZ x) ≤ Real.sqrt (K * eB x) := Real.sqrt_le_sqrt hloew
        _ = Real.sqrt K * Real.sqrt (eB x) := Real.sqrt_mul hK0 _
    have hchain : 2 * Real.sqrt K * Real.sqrt (eB x) * Real.sqrt (eBtZ x) ≤ 2 * K * eB x := by
      have hKe : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt hK0
      have hEe : Real.sqrt (eB x) * Real.sqrt (eB x) = eB x := Real.mul_self_sqrt heBx
      have hMnn : (0 : ℝ) ≤ 2 * Real.sqrt K * Real.sqrt (eB x) := by positivity
      calc 2 * Real.sqrt K * Real.sqrt (eB x) * Real.sqrt (eBtZ x)
          ≤ 2 * Real.sqrt K * Real.sqrt (eB x) * (Real.sqrt K * Real.sqrt (eB x)) :=
            mul_le_mul_of_nonneg_left hsqrtle hMnn
        _ = 2 * (Real.sqrt K * Real.sqrt K) * (Real.sqrt (eB x) * Real.sqrt (eB x)) := by ring
        _ = 2 * K * eB x := by rw [hKe, hEe]
    calc |δ2 x| = |blockVecDot (Z x) (blockMatVecMul (Bt x) (Z x)) -
            blockVecDot (Z x) (blockMatVecMul (B x) (Z x))| := by rw [hδ2, heBtZ, heB]
      _ ≤ 2 * Real.sqrt K * Real.sqrt (eB x) * Real.sqrt (eBtZ x) := by
            simpa only [heB, heBtZ, mul_assoc] using hb2
      _ ≤ 2 * K * eB x := hchain
  have hδ2_bound : |∫ x in S, δ2 x| ≤ 2 * K * ES := by
    have hle1 : |∫ x in S, δ2 x| ≤ ∫ x in S, |δ2 x| := by
      simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := volume.restrict S) δ2
    have hle2 : (∫ x in S, |δ2 x|) ≤ ∫ x in S, 2 * K * eB x :=
      setIntegral_mono_ae_restrict hID2_S.abs (hIA_S.const_mul _) hbound2
    have hrw : (∫ x in S, 2 * K * eB x) = 2 * K * ES := by
      rw [hES]; exact integral_const_mul _ _
    linarith [hle1, hle2, hrw.le, hrw.ge]
  ------------------------------------------------------------------
  -- Step (v): combine.  `|Ettot − Etot| ≤ 2K·ES + 4K·ES = 6K·ES`.
  ------------------------------------------------------------------
  have hfinal : |Ettot - Etot| ≤ 6 * K * ES := by
    rw [hIdentity]
    calc |(∫ x in S, δ2 x) - G| ≤ |∫ x in S, δ2 x| + |G| := abs_sub _ _
      _ = |∫ x in S, δ2 x| + G := by rw [abs_of_nonneg hG0]
      _ ≤ 2 * K * ES + 4 * K * ES := add_le_add hδ2_bound hG4
      _ = 6 * K * ES := by ring
  simpa only [hEttot, hEtot, hES] using hfinal

end Homogenization
