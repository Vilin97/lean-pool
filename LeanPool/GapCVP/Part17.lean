/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.GapCVP.Part16

/-! # GapCVP proof, part 17 -/

noncomputable section

open StateTransition (EvalsToInTime)
open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace Factor400FinitePRadiusBounds

open GapCVP.Factor400FinitePNormCorollary GapCVP.Factor400FinitePRadiusArithmetic

private theorem finiteP_inv_mul_num (p : ℚ) (hp : 1 ≤ p) :
    (p : ℝ)⁻¹ * (p.num.natAbs : ℝ) = (p.den : ℝ) := by
  rw [finitePExponent_cast p hp, inv_div]
  apply div_mul_cancel₀
  exact_mod_cast (finitePExponent_num_pos p hp).ne'

private theorem finitePRadius_power_bound (p : ℚ) (hp : 1 ≤ p) (R : ℕ) :
    (R : ℝ) ^ p.den ≤
      (finitePRadius p R : ℝ) ^ p.num.natAbs := by
  have hscale : 0 < (finitePRadiusScale p : ℝ) := by
    exact_mod_cast finitePRadiusScale_pos p hp
  have hnatural := finitePRadiusNumerator_spec p hp R
  have hreal :
      (finitePRadiusScale p : ℝ) ^ p.num.natAbs *
          (R : ℝ) ^ p.den ≤
        (finitePRadiusNumerator p R : ℝ) ^ p.num.natAbs := by
    exact_mod_cast hnatural
  rw [finitePRadius_cast, div_pow]
  apply (le_div_iff₀ (pow_pos hscale _)).mpr
  simpa only [mul_comm] using hreal

private theorem finitePRadius_lower
    (p : ℚ) (hp : 1 ≤ p) (R : ℕ) (hR : 0 < R) :
    (R : ℝ) ^ ((p : ℝ)⁻¹) ≤ (finitePRadius p R : ℝ) := by
  have hnum : 0 < (p.num.natAbs : ℝ) := by
    exact_mod_cast finitePExponent_num_pos p hp
  have hradius : 0 ≤ (finitePRadius p R : ℝ) := by
    exact_mod_cast (finitePRadius_pos p hp R hR).le
  calc
    (R : ℝ) ^ ((p : ℝ)⁻¹) =
        (R : ℝ) ^
          ((p.den : ℝ) * (p.num.natAbs : ℝ)⁻¹) := by
      rw [finitePExponent_cast p hp, inv_div]
      rfl
    _ = ((R : ℝ) ^ p.den) ^ (p.num.natAbs : ℝ)⁻¹ := by
      rw [Real.rpow_mul (by positivity), Real.rpow_natCast]
    _ ≤ (finitePRadius p R : ℝ) := by
      apply (Real.rpow_inv_le_iff_of_pos
        (by positivity) hradius hnum).mpr
      simpa only [Real.rpow_natCast] using
        finitePRadius_power_bound p hp R

private theorem finiteP_root_rpow_num (p : ℚ) (hp : 1 ≤ p) (R : ℕ) :
    ((R : ℝ) ^ ((p : ℝ)⁻¹)) ^ p.num.natAbs =
      (R : ℝ) ^ p.den := by
  calc
    ((R : ℝ) ^ ((p : ℝ)⁻¹)) ^ p.num.natAbs =
        (R : ℝ) ^
          ((p : ℝ)⁻¹ * (p.num.natAbs : ℝ)) :=
      (Real.rpow_mul_natCast (by positivity)
        ((p : ℝ)⁻¹) p.num.natAbs).symm
    _ = (R : ℝ) ^ (p.den : ℝ) := by
      rw [finiteP_inv_mul_num p hp]
    _ = (R : ℝ) ^ p.den := Real.rpow_natCast _ _

private theorem finitePRadius_floor_le_scaled_root
    (p : ℚ) (hp : 1 ≤ p) (R : ℕ) :
    (Nat.nthRoot p.num.natAbs
      (finitePRadiusScale p ^ p.num.natAbs * R ^ p.den) : ℝ) ≤
        (finitePRadiusScale p : ℝ) *
          (R : ℝ) ^ ((p : ℝ)⁻¹) := by
  have hnum := finitePExponent_num_pos p hp
  have hscale : 0 ≤ (finitePRadiusScale p : ℝ) := by positivity
  have hfloor := Nat.pow_nthRoot_le
    (a := finitePRadiusScale p ^ p.num.natAbs * R ^ p.den)
    (n := p.num.natAbs) (Or.inl hnum.ne')
  have hreal :
      (Nat.nthRoot p.num.natAbs
        (finitePRadiusScale p ^ p.num.natAbs * R ^ p.den) : ℝ)
          ^ p.num.natAbs ≤
        (finitePRadiusScale p : ℝ) ^ p.num.natAbs *
          (R : ℝ) ^ p.den := by
    exact_mod_cast hfloor
  apply (pow_le_pow_iff_left₀ (by positivity)
    (mul_nonneg hscale (by positivity)) hnum.ne').mp
  rw [mul_pow, finiteP_root_rpow_num p hp R]
  exact hreal

private theorem finitePRadius_le_root_add_inv
    (p : ℚ) (hp : 1 ≤ p) (R : ℕ) :
    (finitePRadius p R : ℝ) ≤
      (R : ℝ) ^ ((p : ℝ)⁻¹) +
        (finitePRadiusScale p : ℝ)⁻¹ := by
  have hscale : 0 < (finitePRadiusScale p : ℝ) := by
    exact_mod_cast finitePRadiusScale_pos p hp
  have hnumerator :
      finitePRadiusNumerator p R ≤
        Nat.nthRoot p.num.natAbs
            (finitePRadiusScale p ^ p.num.natAbs * R ^ p.den) + 1 :=
    finitePCeilingRoot_le_nthRoot_add_one p.num.natAbs
      (finitePRadiusScale p ^ p.num.natAbs * R ^ p.den)
  have hnumerator_real :
      (finitePRadiusNumerator p R : ℝ) ≤
        (Nat.nthRoot p.num.natAbs
          (finitePRadiusScale p ^ p.num.natAbs * R ^ p.den) : ℝ) + 1 := by
    exact_mod_cast hnumerator
  rw [finitePRadius_cast]
  apply (div_le_iff₀ hscale).mpr
  calc
    (finitePRadiusNumerator p R : ℝ) ≤
        (Nat.nthRoot p.num.natAbs
          (finitePRadiusScale p ^ p.num.natAbs * R ^ p.den) : ℝ) + 1 :=
      hnumerator_real
    _ ≤ (finitePRadiusScale p : ℝ) *
          (R : ℝ) ^ ((p : ℝ)⁻¹) + 1 := by
      linarith [finitePRadius_floor_le_scaled_root p hp R]
    _ = ((R : ℝ) ^ ((p : ℝ)⁻¹) +
          (finitePRadiusScale p : ℝ)⁻¹) *
            (finitePRadiusScale p : ℝ) := by
      field_simp

private theorem finitePRadius_overhead_exponent_le_quarter
    (p : ℚ) (hp : 1 ≤ p) :
    (p : ℝ) * (finitePRadiusScale p : ℝ)⁻¹ ≤ (1 : ℝ) / 4 := by
  have hscale : 0 < (finitePRadiusScale p : ℝ) := by
    exact_mod_cast finitePRadiusScale_pos p hp
  change (p : ℝ) / (finitePRadiusScale p : ℝ) ≤ (1 : ℝ) / 4
  apply (div_le_div_iff₀ hscale (by norm_num)).mpr
  linarith [four_mul_le_finitePRadiusScale p]

private theorem exp_quarter_lt_two : Real.exp ((1 : ℝ) / 4) < 2 := by
  have hbound := Real.exp_lt_two_add_div_two_sub
    (x := (1 : ℝ) / 4) (by norm_num) (by norm_num)
  calc
    Real.exp ((1 : ℝ) / 4) <
        (2 + (1 : ℝ) / 4) / (2 - (1 : ℝ) / 4) := hbound
    _ < 2 := by norm_num

private theorem finitePRadius_overhead_rpow_lt_two
    (p : ℚ) (hp : 1 ≤ p) :
    (1 + (finitePRadiusScale p : ℝ)⁻¹) ^ (p : ℝ) < 2 := by
  have hp_real : 0 < (p : ℝ) := by
    have hp' : 0 < p := lt_of_lt_of_le (by norm_num) hp
    exact_mod_cast hp'
  have hscale : 0 < (finitePRadiusScale p : ℝ) := by
    exact_mod_cast finitePRadiusScale_pos p hp
  have hbase : 0 < 1 + (finitePRadiusScale p : ℝ)⁻¹ := by
    positivity
  have hlog :
      Real.log (1 + (finitePRadiusScale p : ℝ)⁻¹) ≤
        (finitePRadiusScale p : ℝ)⁻¹ := by
    simpa only [add_sub_cancel_left] using
      Real.log_le_sub_one_of_pos hbase
  have hexponent :
      Real.log (1 + (finitePRadiusScale p : ℝ)⁻¹) *
        (p : ℝ) ≤ (1 : ℝ) / 4 := by
    calc
      Real.log (1 + (finitePRadiusScale p : ℝ)⁻¹) *
          (p : ℝ) ≤
        (finitePRadiusScale p : ℝ)⁻¹ * (p : ℝ) :=
        mul_le_mul_of_nonneg_right hlog hp_real.le
      _ = (p : ℝ) * (finitePRadiusScale p : ℝ)⁻¹ := by ring
      _ ≤ (1 : ℝ) / 4 :=
        finitePRadius_overhead_exponent_le_quarter p hp
  calc
    (1 + (finitePRadiusScale p : ℝ)⁻¹) ^ (p : ℝ) =
        Real.exp
          (Real.log (1 + (finitePRadiusScale p : ℝ)⁻¹) *
            (p : ℝ)) := Real.rpow_def_of_pos hbase _
    _ ≤ Real.exp ((1 : ℝ) / 4) := Real.exp_le_exp.mpr hexponent
    _ < 2 := exp_quarter_lt_two

private theorem finitePRadius_le_scaled_root
    (p : ℚ) (hp : 1 ≤ p) (R : ℕ) (hR : 0 < R) :
    (finitePRadius p R : ℝ) ≤
      (R : ℝ) ^ ((p : ℝ)⁻¹) *
        (1 + (finitePRadiusScale p : ℝ)⁻¹) := by
  have hp_real : 0 < (p : ℝ) := by
    have hp' : 0 < p := lt_of_lt_of_le (by norm_num) hp
    exact_mod_cast hp'
  have hR_one : (1 : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast hR
  have hroot_one : 1 ≤ (R : ℝ) ^ ((p : ℝ)⁻¹) :=
    Real.one_le_rpow hR_one (inv_nonneg.mpr hp_real.le)
  have hscale_inv : 0 ≤ (finitePRadiusScale p : ℝ)⁻¹ := by
    positivity
  calc
    (finitePRadius p R : ℝ) ≤
        (R : ℝ) ^ ((p : ℝ)⁻¹) +
          (finitePRadiusScale p : ℝ)⁻¹ :=
      finitePRadius_le_root_add_inv p hp R
    _ ≤ (R : ℝ) ^ ((p : ℝ)⁻¹) *
          (1 + (finitePRadiusScale p : ℝ)⁻¹) := by
      linarith [mul_nonneg
        (sub_nonneg.mpr hroot_one) hscale_inv]

private theorem finitePRadius_rpow_lt_two_mul
    (p : ℚ) (hp : 1 ≤ p) (R : ℕ) (hR : 0 < R) :
    (finitePRadius p R : ℝ) ^ (p : ℝ) < 2 * (R : ℝ) := by
  have hp_real : 0 < (p : ℝ) := by
    have hp' : 0 < p := lt_of_lt_of_le (by norm_num) hp
    exact_mod_cast hp'
  have hR_real : 0 < (R : ℝ) := by exact_mod_cast hR
  have hradius : 0 ≤ (finitePRadius p R : ℝ) := by
    exact_mod_cast (finitePRadius_pos p hp R hR).le
  have hscaled := finitePRadius_le_scaled_root p hp R hR
  have hpower := Real.rpow_le_rpow hradius hscaled hp_real.le
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.rpow_inv_rpow (by positivity) hp_real.ne'] at hpower
  calc
    (finitePRadius p R : ℝ) ^ (p : ℝ) ≤
        (R : ℝ) *
          (1 + (finitePRadiusScale p : ℝ)⁻¹) ^ (p : ℝ) := hpower
    _ < 2 * (R : ℝ) := by
      linarith [mul_lt_mul_of_pos_left
        (finitePRadius_overhead_rpow_lt_two p hp) hR_real]

end Factor400FinitePRadiusBounds

namespace Factor400FinitePNormSourceReduction

open scoped BigOperators

open GapCVP.Factor400FinitePNormCorollary GapCVP.Factor400FinitePNormPromiseReduction
open GapCVP.Factor400BinaryCodeDecodingCorollary GapCVP.Factor400BinaryDecodingPromiseReduction

private theorem finitePNorm_of_binary_squaredNorm
    (p : ℚ) (hp : 1 ≤ p) {n R : ℕ}
    (vector : Fin n → ℤ)
    (hbinary : ∀ index, vector index = 0 ∨ vector index = 1)
    (hweight : GapCVP.Core.integerSquaredNorm vector = R) :
    finitePNorm p (fun index => (vector index : ℝ)) =
      (R : ℝ) ^ ((p : ℝ)⁻¹) := by
  have hp_pos : (0 : ℚ) < p := lt_of_lt_of_le (by norm_num) hp
  have hp_real : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pos
  unfold finitePNorm
  congr 1
  rw [← hweight]
  unfold GapCVP.Core.integerSquaredNorm
  push_cast
  apply Finset.sum_congr rfl
  intro index _
  rcases hbinary index with hzero | hone
  · simp only [hzero, Int.cast_zero, abs_zero, ne_eq, hp_real.ne', not_false_eq_true,
      Real.zero_rpow,
        Int.natAbs_zero, CharP.cast_eq_zero, OfNat.ofNat_ne_zero, zero_pow]
  · simp only [hone, Int.cast_one, abs_one, Real.one_rpow, isUnit_one, Int.natAbs_of_isUnit,
      Nat.cast_one,
        one_pow]

private theorem finiteP_power_sum_le_scaled_binary_radius
    (p : ℚ) (hp : 1 ≤ p)
    (I : GapCVPInstance) (R : ℕ)
    (radius : ℚ) (hradius : 0 ≤ radius)
    (hradius_power :
      (radius : ℝ) ^ (p : ℝ) ≤ 2 * (R : ℝ))
    (vector : Fin I.dimension → ℤ)
    (hshort :
      finitePNorm p (fun index => (vector index : ℝ)) ≤
        finitePGapFactor p I * (radius : ℝ)) :
    (∑ index : Fin I.dimension,
      |(vector index : ℝ)| ^ (p : ℝ)) ≤
      2 * binaryCodeGapFactor I.dimension * (R : ℝ) := by
  have hp_pos : (0 : ℚ) < p := lt_of_lt_of_le (by norm_num) hp
  have hp_real : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pos
  have hradius_real : (0 : ℝ) ≤ (radius : ℝ) := by
    exact_mod_cast hradius
  have hfactor : 0 ≤ finitePGapFactor p I := by
    unfold finitePGapFactor
    positivity
  have hgap : 0 ≤ binaryCodeGapFactor I.dimension := by
    unfold binaryCodeGapFactor
    positivity
  calc
    (∑ index : Fin I.dimension,
        |(vector index : ℝ)| ^ (p : ℝ)) =
        finitePNorm p (fun index => (vector index : ℝ)) ^ (p : ℝ) :=
      (finitePNorm_rpow p hp_pos _).symm
    _ ≤ (finitePGapFactor p I * (radius : ℝ)) ^ (p : ℝ) :=
      Real.rpow_le_rpow
        (finitePNorm_nonneg p _) hshort hp_real.le
    _ = finitePGapFactor p I ^ (p : ℝ) *
          (radius : ℝ) ^ (p : ℝ) :=
      Real.mul_rpow hfactor hradius_real
    _ = binaryCodeGapFactor I.dimension *
          (radius : ℝ) ^ (p : ℝ) := by
      rw [finitePGapFactor_rpow p hp I]
    _ ≤ binaryCodeGapFactor I.dimension *
          (2 * (R : ℝ)) :=
      mul_le_mul_of_nonneg_left hradius_power hgap
    _ = 2 * binaryCodeGapFactor I.dimension * (R : ℝ) := by ring

private theorem finiteP_binaryLift_squaredNorm_le_power_sum
    (p : ℚ) (hp : 1 ≤ p)
    {n : ℕ} (vector : Fin n → ℤ) :
    (GapCVP.Core.integerSquaredNorm
      (binaryWordLift (GapCVP.Core.binaryResidue vector)) : ℝ) ≤
      ∑ index : Fin n, |(vector index : ℝ)| ^ (p : ℝ) := by
  calc
    (GapCVP.Core.integerSquaredNorm
        (binaryWordLift (GapCVP.Core.binaryResidue vector)) : ℝ) =
        (hammingNorm (GapCVP.Core.binaryResidue vector) : ℝ) := by
          exact_mod_cast integerSquaredNorm_binaryWordLift
            (GapCVP.Core.binaryResidue vector)
    _ = ((finitePSignedBinarySupport vector).card : ℝ) := by
          simp only [hammingNorm, Core.binaryResidue, ne_eq,
            finitePSignedBinarySupport]
          congr 1
    _ ≤ ∑ index : Fin n, |(vector index : ℝ)| ^ (p : ℝ) :=
          finitePSignedBinarySupport_card_le_power_sum p hp vector

private theorem finiteP_binaryLift_solves
    (H : GapCVP.Core.BinaryAffineSystem)
    (vector : Fin H.dimension → ℤ)
    (hsolve : H.Solves vector) :
    H.Solves (binaryWordLift (GapCVP.Core.binaryResidue vector)) := by
  simp only [GapCVP.Core.BinaryAffineSystem.Solves, decide_eq_true_eq] at hsolve ⊢
  simpa only [binaryResidue_binaryWordLift] using hsolve

end Factor400FinitePNormSourceReduction

namespace Factor400FinitePNormUnconditional

open scoped BigOperators

open GapCVP.Factor400FinitePNormCorollary

private theorem finitePCompactCanonicalYes_mem
    (p : ℚ) (hp : 1 ≤ p) :
    (finitePGapCVPPromise p hp).yes
      SourceMachineRouting.canonicalYesWord := by
  simp only [GapCVP.Factor400FinitePNormCorollary.finitePGapCVPPromise, decide_eq_true_eq]
  have hp_pos : (0 : ℚ) < p := lt_of_lt_of_le (by norm_num) hp
  have hp_real : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_pos
  refine ⟨SourceMachineRouting.canonicalYesInstance, rfl,
    SourceMachineRouting.canonicalYesInstance_wellFormed, ?_⟩
  refine ⟨fun _ => 0, ?_⟩
  simp only [finitePLatticeDistance, finitePNorm, SourceMachineRouting.canonicalYesInstance,
      finitePLatticeDiscrepancy, Rat.cast_zero,
          Int.cast_zero, mul_zero,
      Finset.sum_const_zero, sub_self, abs_zero, ne_eq, hp_real.ne', not_false_eq_true,
          Real.zero_rpow,
      inv_ne_zero hp_real.ne', Rat.cast_one, zero_le_one]

end Factor400FinitePNormUnconditional

namespace PaperFinitePNormSourceReduction

open scoped BigOperators

open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.Factor400BinaryCodeDecodingCorollary
open GapCVP.Factor400BinaryInstanceBridge GapCVP.Factor400BinaryConstructiveSourcePlaces
open GapCVP.BinarySourceTautologyNormalizationExact GapCVP.OriginalThreeSATNPHardness
open GapCVP.SourcePreprocessingSemantics GapCVP.SourcePreprocessingTM GapCVP.FormulaBridge
open GapCVP.FourFamilySoundness GapCVP.NormalizedRecordDecoder GapCVP.PhysicalWordSoundness
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.Factor400FinitePNormCorollary GapCVP.Factor400FinitePNormPromiseReduction
open GapCVP.Factor400FinitePNormSourceReduction GapCVP.Factor400FinitePNormUnconditional
open GapCVP.Factor400FinitePRadiusArithmetic GapCVP.Factor400FinitePRadiusBounds

private abbrev paperFinitePPhysicalSystem
    (encodingLength : ℕ) (formula : ThreeCNF) : BinaryAffineSystem :=
  physicalFormulaSystem encodingLength formula

private theorem paperVariableArityFinitePPhysicalSystem_dimension
    (encodingLength : ℕ) (formula : ThreeCNF) :
    (paperFinitePPhysicalSystem
      encodingLength formula).dimension =
      sourceFormulaDimension encodingLength
        (srcFormula formula) := by
  rfl

private theorem paperVariableArityFinitePPhysicalSystem_dimension_pos
    (encodingLength : ℕ) (formula : ThreeCNF) :
    0 < (paperFinitePPhysicalSystem
      encodingLength formula).dimension :=
  physicalFormulaSystem_dimension_pos
    encodingLength formula

private def paperFinitePPhysicalFormulaInstance
    (p : ℚ) (hp : 1 ≤ p)
    (encodingLength : ℕ) (formula : ThreeCNF) : GapCVPInstance :=
  effectiveGapCVPInstance
    (paperFinitePPhysicalSystem encodingLength formula)
    (paperVariableArityFinitePPhysicalSystem_dimension_pos
      encodingLength formula)
    (finitePRadius p
      (paperVariableArityIntegerRadius encodingLength formula))
    (finitePRadius_pos p hp
      (paperVariableArityIntegerRadius encodingLength formula)
      (paperVariableArityIntegerRadius_pos encodingLength formula))

private theorem paperVariableArityFinitePPhysicalFormulaInstance_wellFormed
    (p : ℚ) (hp : 1 ≤ p)
    (encodingLength : ℕ) (formula : ThreeCNF) :
    gapCVPWellFormed
      (paperFinitePPhysicalFormulaInstance
        p hp encodingLength formula) := by
  unfold paperFinitePPhysicalFormulaInstance
  exact effectiveGapCVPInstance_wellFormed _ _ _ _

private theorem paperVariableArityFinitePPhysicalSystem_oneHot_of_satisfiable
    (encodingLength : ℕ) (formula : ThreeCNF)
    (satisfiable : ∃ assignment : ℕ → Bool,
      ∀ clause ∈ formula, clauseSatisfied assignment clause) :
    ∃ values : Fin
        (sourceFormulaDimension encodingLength
          (srcFormula formula)) → ℤ,
      (paperFinitePPhysicalSystem
        encodingLength formula).Solves values ∧
      (∀ index, values index = 0 ∨ values index = 1) ∧
      integerSquaredNorm values =
        paperVariableArityIntegerRadius encodingLength formula := by
  exact paperVariableArityPhysicalFormulaSystem_oneHot_of_satisfiable
    encodingLength formula satisfiable

theorem
    paperVariableArityFinitePPhysicalSystem_satisfiable_of_scaled_hamming
    (encodingLength : ℕ) (formula : ThreeCNF)
    (values : Fin
      (sourceFormulaDimension encodingLength
        (srcFormula formula)) → ℤ)
    (solution : (paperFinitePPhysicalSystem
      encodingLength formula).Solves values)
    (short :
      (integerSquaredNorm values : ℝ) ≤
        2 * binaryCodeGapFactor
          (sourceFormulaDimension encodingLength
            (srcFormula formula)) *
          (paperVariableArityIntegerRadius
            encodingLength formula : ℝ)) :
    ∃ assignment : ℕ → Bool,
      ∀ clause ∈ formula, clauseSatisfied assignment clause := by
  exact
    paperVariableArityPhysicalWordBinarySystem_satisfiable_of_scaled_hamming
      encodingLength formula values solution short

theorem
    paperVariableArityFinitePPhysicalSystem_satisfiable_of_finiteP_short
    (p : ℚ) (hp : 1 ≤ p)
    (encodingLength : ℕ) (formula : ThreeCNF)
    (values : Fin
      (sourceFormulaDimension encodingLength
        (srcFormula formula)) → ℤ)
    (solution :
      (paperFinitePPhysicalSystem
        encodingLength formula).Solves values)
    (short :
      finitePNorm p (fun index => (values index : ℝ)) ≤
        finitePGapFactor p
          (paperFinitePPhysicalFormulaInstance
            p hp encodingLength formula) *
          (finitePRadius p
            (paperVariableArityIntegerRadius
              encodingLength formula) : ℝ)) :
    ∃ assignment : ℕ → Bool,
      ∀ clause ∈ formula, clauseSatisfied assignment clause := by
  let R := paperVariableArityIntegerRadius encodingLength formula
  let radius := finitePRadius p R
  let lifted := binaryWordLift (binaryResidue values)
  have hR : 0 < R :=
    paperVariableArityIntegerRadius_pos encodingLength formula
  have hradius : 0 < radius := finitePRadius_pos p hp R hR
  have hradiusPower : (radius : ℝ) ^ (p : ℝ) ≤ 2 * (R : ℝ) :=
    (finitePRadius_rpow_lt_two_mul p hp R hR).le
  apply
    paperVariableArityFinitePPhysicalSystem_satisfiable_of_scaled_hamming
      encodingLength formula lifted
  · exact finiteP_binaryLift_solves
      (paperFinitePPhysicalSystem
        encodingLength formula) values solution
  · calc
      (integerSquaredNorm lifted : ℝ) ≤
          ∑ index, |(values index : ℝ)| ^ (p : ℝ) :=
        finiteP_binaryLift_squaredNorm_le_power_sum p hp values
      _ ≤ 2 * binaryCodeGapFactor
          (sourceFormulaDimension encodingLength
            (srcFormula formula)) * (R : ℝ) := by
        exact finiteP_power_sum_le_scaled_binary_radius
          p hp (paperFinitePPhysicalFormulaInstance
            p hp encodingLength formula)
          R radius hradius.le hradiusPower values short

theorem
    paperVariableArityFinitePPhysicalFormulaInstance_close_of_satisfiable
    (p : ℚ) (hp : 1 ≤ p)
    (encodingLength : ℕ) (formula : ThreeCNF)
    (satisfiable : ∃ assignment : ℕ → Bool,
      ∀ clause ∈ formula, clauseSatisfied assignment clause) :
    ∃ coefficients : Fin
        (paperFinitePPhysicalFormulaInstance
          p hp encodingLength formula).dimension → ℤ,
      finitePLatticeDistance p
          (paperFinitePPhysicalFormulaInstance
            p hp encodingLength formula) coefficients ≤
        ((paperFinitePPhysicalFormulaInstance
            p hp encodingLength formula).radius : ℝ) := by
  let H := paperFinitePPhysicalSystem
    encodingLength formula
  let R := paperVariableArityIntegerRadius encodingLength formula
  let radius := finitePRadius p R
  have hR : 0 < R :=
    paperVariableArityIntegerRadius_pos encodingLength formula
  have hradius : 0 < radius := finitePRadius_pos p hp R hR
  have hdimension : 0 < H.dimension :=
    paperVariableArityFinitePPhysicalSystem_dimension_pos
      encodingLength formula
  obtain ⟨values, solution, binary, weight⟩ :=
    paperVariableArityFinitePPhysicalSystem_oneHot_of_satisfiable
      encodingLength formula satisfiable
  have hdimensions :
      H.dimension = sourceFormulaDimension
        encodingLength (srcFormula formula) :=
    paperVariableArityFinitePPhysicalSystem_dimension
      encodingLength formula
  let valuesH : Fin H.dimension → ℤ :=
    fun index => values ((finCongr hdimensions) index)
  have solutionH : H.Solves valuesH := by
    change (paperFinitePPhysicalSystem
      encodingLength formula).Solves _
    have valuesEqual : valuesH = values := by
      funext index
      rfl
    rw [valuesEqual]
    exact solution
  have binaryH : ∀ index, valuesH index = 0 ∨ valuesH index = 1 := by
    intro index
    exact binary ((finCongr hdimensions) index)
  have normTransport :
      integerSquaredNorm valuesH = integerSquaredNorm values := by
    unfold integerSquaredNorm
    simpa [valuesH] using
      Equiv.sum_comp (finCongr hdimensions)
        (fun index => (values index).natAbs ^ 2)
  have weightH : integerSquaredNorm valuesH = R :=
    normTransport.trans weight
  have consistent : H.effectiveReducedConsistent = true :=
    (BinaryAffineSystem.effectiveReducedConsistent_iff_solvable
      H).mpr ⟨valuesH, solutionH⟩
  have coset :
      H.Solves
        (H.effectiveAffineRepresentative -
          (H.effectiveAffineRepresentative - valuesH)) := by
    simpa using solutionH
  obtain ⟨coefficients, representation⟩ :=
    (effectiveConstructionAInstance_solution_coset
      H consistent
        (H.effectiveAffineRepresentative - valuesH)).mp coset
  have discrepancy :
      effectiveFinitePSignedDiscrepancy H coefficients = valuesH := by
    unfold effectiveFinitePSignedDiscrepancy
    rw [representation]
    simp
  have norm :
      finitePNorm p (fun index => (valuesH index : ℝ)) =
        (R : ℝ) ^ ((p : ℝ)⁻¹) :=
    finitePNorm_of_binary_squaredNorm p hp valuesH binaryH weightH
  have distance :
      finitePLatticeDistance p
          (effectiveGapCVPInstance H hdimension radius hradius)
          coefficients ≤ (radius : ℝ) := by
    rw [finitePLatticeDistance_effective_eq_signed_norm,
      discrepancy, norm]
    exact finitePRadius_lower p hp R hR
  refine ⟨coefficients, ?_⟩
  simpa [paperFinitePPhysicalFormulaInstance,
    effectiveGapCVPInstance, adaptGapCVPInstance,
    GapCVP.Core.effectiveConstructionAInstance,
    H, R, radius] using distance

theorem
    paperVariableArityFinitePPhysicalFormulaInstance_far_of_unsatisfiable
    (p : ℚ) (hp : 1 ≤ p)
    (encodingLength : ℕ) (formula : ThreeCNF)
    (consistent :
      (paperFinitePPhysicalSystem
        encodingLength formula).effectiveReducedConsistent = true)
    (unsatisfiable : ¬ ∃ assignment : ℕ → Bool,
      ∀ clause ∈ formula, clauseSatisfied assignment clause) :
    ∀ coefficients : Fin
        (paperFinitePPhysicalFormulaInstance
          p hp encodingLength formula).dimension → ℤ,
      finitePGapFactor p
          (paperFinitePPhysicalFormulaInstance
            p hp encodingLength formula) *
          ((paperFinitePPhysicalFormulaInstance
            p hp encodingLength formula).radius : ℝ) <
        finitePLatticeDistance p
          (paperFinitePPhysicalFormulaInstance
            p hp encodingLength formula) coefficients := by
  let H := paperFinitePPhysicalSystem
    encodingLength formula
  let R := paperVariableArityIntegerRadius encodingLength formula
  let radius := finitePRadius p R
  have hR : 0 < R :=
    paperVariableArityIntegerRadius_pos encodingLength formula
  have hradius : 0 < radius := finitePRadius_pos p hp R hR
  have hdimension : 0 < H.dimension :=
    paperVariableArityFinitePPhysicalSystem_dimension_pos
      encodingLength formula
  intro coefficients
  apply lt_of_not_ge
  intro short
  have norm :
      finitePNorm p (fun index =>
        (effectiveFinitePSignedDiscrepancy H coefficients index : ℝ)) ≤
          finitePGapFactor p
            (paperFinitePPhysicalFormulaInstance
              p hp encodingLength formula) * (radius : ℝ) := by
    have distance := finitePLatticeDistance_effective_eq_signed_norm
      p H hdimension radius hradius coefficients
    simpa only [paperFinitePPhysicalFormulaInstance, ge_iff_le] using (distance ▸ short)
  apply unsatisfiable
  apply paperVariableArityFinitePPhysicalSystem_satisfiable_of_finiteP_short
    p hp encodingLength formula
    (effectiveFinitePSignedDiscrepancy H coefficients)
  · exact effectiveFinitePSignedDiscrepancy_solves
      H consistent coefficients
  · exact norm

private def paperFinitePSourceInstance
    (p : ℚ) (hp : 1 ≤ p) (input : List Bool) : GapCVPInstance := by
  classical
  exact
    match decodeThreeCNF input with
    | none => finitePCanonicalNoInstance
    | some formula =>
      if encodeThreeCNF formula = input then
        match readPaperVariableArityNormalizedSourceDescriptor
            (paperSourcePreprocessingOutput input) with
        | none => finitePCanonicalNoInstance
        | some descriptor =>
          if descriptor.originalWord = input then
            if descriptor.normalizedClauses = [] then
              SourceMachineRouting.canonicalYesInstance
            else
              if (paperFinitePPhysicalSystem
                    input.length descriptor.originalFormula).effectiveReducedConsistent then
                paperFinitePPhysicalFormulaInstance
                  p hp input.length descriptor.originalFormula
              else
                finitePCanonicalNoInstance
          else
            finitePCanonicalNoInstance
      else
        finitePCanonicalNoInstance

private def paperVariableArityFinitePSourceMap
    (p : ℚ) (hp : 1 ≤ p) (input : List Bool) : List Bool :=
  encodeGapCVPInstance
    (paperFinitePSourceInstance p hp input)

private theorem paperVariableArityFinitePSourceInstance_of_decode_none
    (p : ℚ) (hp : 1 ≤ p)
    (input : List Bool)
    (decode : decodeThreeCNF input = none) :
    paperFinitePSourceInstance p hp input =
      finitePCanonicalNoInstance := by
  simp only [paperFinitePSourceInstance, decode]

private theorem paperVariableArityFinitePSourceInstance_of_noncanonical
    (p : ℚ) (hp : 1 ≤ p)
    (input : List Bool) (formula : ThreeCNF)
    (decode : decodeThreeCNF input = some formula)
    (noncanonical : encodeThreeCNF formula ≠ input) :
    paperFinitePSourceInstance p hp input =
      finitePCanonicalNoInstance := by
  simp only [paperFinitePSourceInstance, decode, noncanonical, ↓reduceIte]

private theorem paperVariableArityFinitePSourceInstance_of_normalized_empty
    (p : ℚ) (hp : 1 ≤ p)
    (input : List Bool) (formula : ThreeCNF)
    (decode : decodeThreeCNF input = some formula)
    (canonical : encodeThreeCNF formula = input)
    (empty : paperSourceNormalizedClauses formula = []) :
    paperFinitePSourceInstance p hp input =
      SourceMachineRouting.canonicalYesInstance := by
  unfold paperFinitePSourceInstance
  simp only [decode, ite_eq_left canonical]
  have descriptor :
      readPaperVariableArityNormalizedSourceDescriptor
          (paperSourcePreprocessingOutput input) =
        some
          { retainedFormula := noTautClauses formula
            normalizedClauses := paperSourceNormalizedClauses formula
            originalFormula := formula
            originalWord := encodeThreeCNF formula } := by
    rw [← canonical]
    exact readPaperVariableArityNormalizedSourceDescriptor_valid formula
  rw [descriptor]
  simp only [canonical, ↓reduceIte, empty]

private theorem paperVariableArityFinitePSourceInstance_of_inconsistent
    (p : ℚ) (hp : 1 ≤ p)
    (input : List Bool) (formula : ThreeCNF)
    (decode : decodeThreeCNF input = some formula)
    (canonical : encodeThreeCNF formula = input)
    (nonempty : paperSourceNormalizedClauses formula ≠ [])
    (inconsistent :
      (paperFinitePPhysicalSystem
        input.length formula).effectiveReducedConsistent = false) :
    paperFinitePSourceInstance p hp input =
      finitePCanonicalNoInstance := by
  unfold paperFinitePSourceInstance
  simp only [decode, ite_eq_left canonical]
  have descriptor :
      readPaperVariableArityNormalizedSourceDescriptor
          (paperSourcePreprocessingOutput input) =
        some
          { retainedFormula := noTautClauses formula
            normalizedClauses := paperSourceNormalizedClauses formula
            originalFormula := formula
            originalWord := encodeThreeCNF formula } := by
    rw [← canonical]
    exact readPaperVariableArityNormalizedSourceDescriptor_valid formula
  rw [descriptor]
  simp only [canonical, ↓reduceIte, nonempty, inconsistent, Bool.false_eq_true]

private theorem paperVariableArityFinitePSourceInstance_of_consistent
    (p : ℚ) (hp : 1 ≤ p)
    (input : List Bool) (formula : ThreeCNF)
    (decode : decodeThreeCNF input = some formula)
    (canonical : encodeThreeCNF formula = input)
    (nonempty : paperSourceNormalizedClauses formula ≠ [])
    (consistent :
      (paperFinitePPhysicalSystem
        input.length formula).effectiveReducedConsistent = true) :
    paperFinitePSourceInstance p hp input =
      paperFinitePPhysicalFormulaInstance
        p hp input.length formula := by
  unfold paperFinitePSourceInstance
  simp only [decode, ite_eq_left canonical]
  have descriptor :
      readPaperVariableArityNormalizedSourceDescriptor
          (paperSourcePreprocessingOutput input) =
        some
          { retainedFormula := noTautClauses formula
            normalizedClauses := paperSourceNormalizedClauses formula
            originalFormula := formula
            originalWord := encodeThreeCNF formula } := by
    rw [← canonical]
    exact readPaperVariableArityNormalizedSourceDescriptor_valid formula
  rw [descriptor]
  simp only [canonical, ↓reduceIte, nonempty, consistent]

private theorem paperVariableArityFinitePSourceMap_completeness
    (p : ℚ) (hp : 1 ≤ p)
    (input : List Bool)
    (satisfiable : paperOriginalThreeSATLanguage input) :
    (finitePGapCVPPromise p hp).yes
      (paperVariableArityFinitePSourceMap p hp input) := by
  obtain ⟨formula, canonical, assignment⟩ :=
    (paperOriginalThreeSATLanguage_iff input).mp satisfiable
  have decode : decodeThreeCNF input = some formula := by
    rw [← canonical]
    exact decodeThreeCNF_encode formula
  by_cases empty : paperSourceNormalizedClauses formula = []
  · unfold paperVariableArityFinitePSourceMap
    rw [paperVariableArityFinitePSourceInstance_of_normalized_empty
      p hp input formula decode canonical empty]
    exact finitePCompactCanonicalYes_mem p hp
  · obtain ⟨vector, solution, _, _⟩ :=
      paperVariableArityFinitePPhysicalSystem_oneHot_of_satisfiable
        input.length formula assignment
    have consistent :
        (paperFinitePPhysicalSystem
          input.length formula).effectiveReducedConsistent = true :=
      (BinaryAffineSystem.effectiveReducedConsistent_iff_solvable
        (paperFinitePPhysicalSystem
          input.length formula)).mpr ⟨vector, solution⟩
    simp only [GapCVP.Factor400FinitePNormCorollary.finitePGapCVPPromise, decide_eq_true_eq]
    refine ⟨paperFinitePPhysicalFormulaInstance
      p hp input.length formula, ?_,
      paperVariableArityFinitePPhysicalFormulaInstance_wellFormed
        p hp input.length formula, ?_⟩
    · unfold paperVariableArityFinitePSourceMap
      rw [paperVariableArityFinitePSourceInstance_of_consistent
        p hp input formula decode canonical empty consistent]
      rfl
    · exact
        paperVariableArityFinitePPhysicalFormulaInstance_close_of_satisfiable
          p hp input.length formula assignment

private theorem paperVariableArityFinitePSourceMap_soundness
    (p : ℚ) (hp : 1 ≤ p)
    (input : List Bool)
    (unsatisfiable : ¬ paperOriginalThreeSATLanguage input) :
    (finitePGapCVPPromise p hp).no
      (paperVariableArityFinitePSourceMap p hp input) := by
  classical
  cases decode : decodeThreeCNF input with
  | none =>
      unfold paperVariableArityFinitePSourceMap
      rw [paperVariableArityFinitePSourceInstance_of_decode_none
        p hp input decode]
      exact finitePCanonicalNo_mem_no p hp
  | some formula =>
      by_cases canonical : encodeThreeCNF formula = input
      · by_cases empty : paperSourceNormalizedClauses formula = []
        · exfalso
          apply unsatisfiable
          apply (paperOriginalThreeSATLanguage_iff input).mpr
          exact ⟨formula, canonical,
            paperVariableArityOriginal_satisfiable_of_normalized_empty
              formula empty⟩
        · cases consistent :
              (paperFinitePPhysicalSystem
                input.length formula).effectiveReducedConsistent with
          | false =>
              unfold paperVariableArityFinitePSourceMap
              rw [paperVariableArityFinitePSourceInstance_of_inconsistent
                p hp input formula decode canonical empty consistent]
              exact finitePCanonicalNo_mem_no p hp
          | true =>
              have originalUnsatisfiable :
                  ¬ ∃ assignment : ℕ → Bool,
                    ∀ clause ∈ formula,
                      clauseSatisfied assignment clause := by
                intro assignment
                apply unsatisfiable
                exact (paperOriginalThreeSATLanguage_iff input).mpr
                  ⟨formula, canonical, assignment⟩
              simp only [GapCVP.Factor400FinitePNormCorollary.finitePGapCVPPromise,
                  decide_eq_true_eq]
              refine ⟨paperFinitePPhysicalFormulaInstance
                p hp input.length formula, ?_,
                paperVariableArityFinitePPhysicalFormulaInstance_wellFormed
                  p hp input.length formula, ?_⟩
              · unfold paperVariableArityFinitePSourceMap
                rw [paperVariableArityFinitePSourceInstance_of_consistent
                  p hp input formula decode canonical empty consistent]
                rfl
              · exact
                  paperVariableArityFinitePPhysicalFormulaInstance_far_of_unsatisfiable
                    p hp input.length formula consistent
                    originalUnsatisfiable
      · unfold paperVariableArityFinitePSourceMap
        rw [paperVariableArityFinitePSourceInstance_of_noncanonical
          p hp input formula decode canonical]
        exact finitePCanonicalNo_mem_no p hp

private def paperVariableArityFinitePSourceReductionOfMachine
    (p : ℚ) (hp : 1 ≤ p)
    (machine : BitTM (paperVariableArityFinitePSourceMap p hp)) :
    PromiseReduction paperOriginalThreeSATLanguage
      (finitePGapCVPPromise p hp) where
  map := paperVariableArityFinitePSourceMap p hp
  polynomial_time := ⟨machine⟩
  completeness := paperVariableArityFinitePSourceMap_completeness p hp
  soundness := paperVariableArityFinitePSourceMap_soundness p hp

private theorem paperVariableArityFiniteP_nphard_of_sourceMachine
    (p : ℚ) (hp : 1 ≤ p)
    (machine : BitTM (paperVariableArityFinitePSourceMap p hp)) :
    NPHardPromise (finitePGapCVPPromise p hp) :=
  nphardPromise_of_nphard_of_promiseReduction
    paperOriginalThreeSATIsNPHard
    (paperVariableArityFinitePSourceReductionOfMachine p hp machine)
    polynomialTimeClosedUnderComposition

end PaperFinitePNormSourceReduction

namespace Factor400PaperVariableArityFinitePNormUnconditional

open Turing GapCVP.BinaryEncoding GapCVP.CNFBoundedRecordFoldTM
open GapCVP.SourceCanonicalFixedWordTuringTM GapCVP.OutputPolynomialCompositionClosure
open GapCVP.SourceWholeOutputAssemblyTM GapCVP.Factor400BinaryCodeDecodingCorollary
open GapCVP.SourcePreprocessingSemantics GapCVP.FormulaBridge GapCVP.FourFamilySoundness
open GapCVP.CanonicalMatrixShape GapCVP.CanonicalPhysicalMatrixShape
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalMatrixCellInstantiation
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalRadiusMachine
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.PhysicalNormalizedBranchTM GapCVP.PhysicalNormalizedCanonicalGuardTM
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianSourceConsistencyBridge
open GapCVP.GaussianExactSourceInitializer GapCVP.GaussianSourceInitializerInstantiation
open GapCVP.GaussianOutputSerializerTM GapCVP.ExactPhysicalSourceTM
open GapCVP.Factor400FinitePNormCorollary GapCVP.Factor400FinitePNormPromiseReduction
open GapCVP.Factor400FinitePRadiusArithmetic GapCVP.Factor400FinitePRadiusSourceTM
open GapCVP.Factor400FinitePRadiusRationalAtomTM GapCVP.PaperFinitePNormSourceReduction

private theorem paperVariableArityPhysicalOneHotWeightUnary_eq_integerRadius
    (formula : ThreeCNF) :
    physicalOneHotWeightUnary
        (encodeThreeCNF formula) =
      List.replicate
        (paperVariableArityIntegerRadius
          (encodeThreeCNF formula).length formula) true := by
  rw [paperVariableArityPhysicalOneHotWeightUnary_valid]
  unfold paperVariableArityIntegerRadius sourceBinaryDecodingRadius
  rw [paperVariableAritySourceFormula_clauses_length]

private def paperFinitePThresholdUnary (p : ℚ)
    (input : List Bool) : List Bool :=
  List.replicate
    (finitePRadiusScale p ^ p.num.natAbs *
      (physicalOneHotWeightUnary input).length ^ p.den)
    true

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityFinitePThresholdUnaryComputable (p : ℚ) :
    BitTM
      (paperFinitePThresholdUnary p) := by
  have physical := GapCVP.TMComposition.computableInPolyTime
    paperVariableArityPhysicalOneHotWeightUnaryComputable
    (polynomialValueUnaryComputable
      (Polynomial.C (finitePRadiusScale p ^ p.num.natAbs) *
        Polynomial.X ^ p.den))
  change BitTM
    (fun input : List Bool =>
      List.replicate
        (finitePRadiusScale p ^ p.num.natAbs *
          (physicalOneHotWeightUnary input).length ^ p.den)
        true)
  simpa only [eq_natCast, Nat.cast_pow, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_natCast,
      Nat.cast_id, Polynomial.eval_X, Function.comp_def] using physical

private theorem paperVariableArityFinitePThresholdUnary_valid
    (p : ℚ) (formula : ThreeCNF) :
    paperFinitePThresholdUnary p
        (encodeThreeCNF formula) =
      List.replicate
        (finitePRadiusScale p ^ p.num.natAbs *
          paperVariableArityIntegerRadius
            (encodeThreeCNF formula).length formula ^ p.den)
        true := by
  unfold paperFinitePThresholdUnary
  rw [paperVariableArityPhysicalOneHotWeightUnary_eq_integerRadius formula]
  simp only [List.length_replicate]

private def paperFinitePNumeratorUnary (p : ℚ) :
    List Bool → List Bool :=
  finitePNthRootUnaryOutput p.num.natAbs
    (paperFinitePThresholdUnary p)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityFinitePNumeratorUnaryComputable (p : ℚ) :
    BitTM
      (paperFinitePNumeratorUnary p) :=
  finitePNthRootUnaryComputable p.num.natAbs
    (paperVariableArityFinitePThresholdUnaryComputable p)

private theorem paperVariableArityFinitePNumeratorUnary_valid
    (p : ℚ) (hp : 1 ≤ p) (formula : ThreeCNF) :
    paperFinitePNumeratorUnary p
        (encodeThreeCNF formula) =
      List.replicate
        (finitePRadiusNumerator p
          (paperVariableArityIntegerRadius
            (encodeThreeCNF formula).length formula)) true := by
  unfold paperFinitePNumeratorUnary
  exact finitePNthRootUnaryOutput_valid p.num.natAbs
    (finitePExponent_num_pos p hp)
    (paperFinitePThresholdUnary p)
    (encodeThreeCNF formula)
    (finitePRadiusScale p ^ p.num.natAbs *
      paperVariableArityIntegerRadius
        (encodeThreeCNF formula).length formula ^ p.den)
    (paperVariableArityFinitePThresholdUnary_valid p formula)

private def paperVariableArityFinitePRadiusAtomicOutput (p : ℚ) :
    List Bool → List Bool :=
  sourceReducedRationalAtomicOutput
    (finitePRadiusScale p) (paperFinitePNumeratorUnary p)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityFinitePRadiusAtomicComputable (p : ℚ) :
    BitTM
      (paperVariableArityFinitePRadiusAtomicOutput p) :=
  sourceReducedRationalAtomicComputable
    (finitePRadiusScale p)
    (paperVariableArityFinitePNumeratorUnaryComputable p)

private theorem paperVariableArityFinitePRadiusAtomicOutput_valid
    (p : ℚ) (hp : 1 ≤ p) (formula : ThreeCNF) :
    paperVariableArityFinitePRadiusAtomicOutput p
        (encodeThreeCNF formula) =
      encodeAtomic
        (finitePRadius p
          (paperVariableArityIntegerRadius
            (encodeThreeCNF formula).length formula)) := by
  unfold paperVariableArityFinitePRadiusAtomicOutput
  have physical := sourceReducedRationalAtomicOutput_valid
    (finitePRadiusScale p)
    (paperFinitePNumeratorUnary p)
    (encodeThreeCNF formula)
    (finitePRadiusNumerator p
      (paperVariableArityIntegerRadius
        (encodeThreeCNF formula).length formula))
    (finitePRadiusScale_pos p hp)
    (paperVariableArityFinitePNumeratorUnary_valid p hp formula)
  simpa only [finitePRadius] using physical

private noncomputable def paperFinitePPhysicalStructuralOutput
    (p : ℚ) {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (cell : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    List Bool → List Bool :=
  paperGaussianStructuralSourceWord shape
    (paperVariableArityFinitePRadiusAtomicComputable p)
    (gaussianPaperVariableArityCanonicalSourceReducedStateComputable cell)

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityFinitePPhysicalStructuralOutputComputable
    (p : ℚ) {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (cell : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    BitTM
      (paperFinitePPhysicalStructuralOutput p cell) :=
  paperVariableArityGaussianStructuralSourceWordComputable shape
    (paperVariableArityFinitePRadiusAtomicComputable p)
    (gaussianPaperVariableArityCanonicalSourceReducedStateComputable cell)

private theorem paperVariableArityFinitePPhysicalStructuralOutput_valid
    (p : ℚ) (hp : 1 ≤ p)
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (cell : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (formula : ThreeCNF) :
    paperFinitePPhysicalStructuralOutput p cell
        (encodeThreeCNF formula) =
      encodeGapCVPInstance
        (paperFinitePPhysicalFormulaInstance p hp
          (encodeThreeCNF formula).length formula) := by
  unfold paperFinitePPhysicalStructuralOutput
  have physical :=
    paperVariableArityGaussianStructuralSourceWord_eq_encodeGapCVPInstance
      shape
      (paperVariableArityFinitePRadiusAtomicComputable p)
      (gaussianPaperVariableArityCanonicalSourceReducedStateComputable cell)
      formula
      (finitePRadius p
        (paperVariableArityIntegerRadius
          (encodeThreeCNF formula).length formula))
      (finitePRadius_pos p hp
        (paperVariableArityIntegerRadius
          (encodeThreeCNF formula).length formula)
        (paperVariableArityIntegerRadius_pos
          (encodeThreeCNF formula).length formula))
      (paperVariableArityFinitePRadiusAtomicOutput_valid p hp formula)
      (gaussianPaperVariableArityCanonicalSourceReducedStateOutput_effective
        cell formula)
  simpa only [paperFinitePPhysicalFormulaInstance, paperFinitePPhysicalSystem] using physical

private def paperFinitePPhysicalRoutedOutput
    (p : ℚ) {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (cell : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (input : List Bool) : List Bool :=
  if physicalCanonicalNormalizedEmptyGuard input then
    SourceMachineRouting.canonicalYesWord
  else if physicalCanonicalNormalizedNonemptyGuard input then
    if binaryGaussianSourceConsistencyGuard
        paperCanonicalSourceBinarySystem input then
      paperFinitePPhysicalStructuralOutput p cell input
    else
      finitePCanonicalNoWord
  else
    finitePCanonicalNoWord

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityFinitePPhysicalRoutedOutputComputable
    (p : ℚ) {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (cell : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    BitTM
      (paperFinitePPhysicalRoutedOutput p cell) := by
  have consistency := sourcePreservingConditionalComputable
    (gaussianPaperVariableArityAllInputExactConsistencyComputable cell)
    (paperVariableArityFinitePPhysicalStructuralOutputComputable p cell)
    finitePCanonicalNoWord
  have nonempty := sourcePreservingConditionalComputable
    paperVariableArityPhysicalCanonicalNormalizedNonemptyGuardComputable
    consistency finitePCanonicalNoWord
  exact binaryGaussianDynamicBranchComputable
    paperVariableArityPhysicalCanonicalNormalizedEmptyGuardComputable
    (sourceFixedWordComputable SourceMachineRouting.canonicalYesWord)
    nonempty

private theorem paperVariableArityFinitePPhysicalRoutedOutput_eq_sourceMap
    (p : ℚ) (hp : 1 ≤ p)
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (cell : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (input : List Bool) :
    paperFinitePPhysicalRoutedOutput p cell input =
      paperVariableArityFinitePSourceMap p hp input := by
  cases decoded : decodeThreeCNF input with
  | none =>
      have canonical : constructiveCanonicalSourceMarker input = false := by
        simp only [constructiveCanonicalSourceMarker, decoded]
      have empty :
          physicalCanonicalNormalizedEmptyGuard input =
            false := by
        simp only [physicalCanonicalNormalizedEmptyGuard, canonical, Bool.false_and]
      have nonempty :
          physicalCanonicalNormalizedNonemptyGuard input =
            false := by
        simp only [physicalCanonicalNormalizedNonemptyGuard, canonical, Bool.false_and]
      unfold paperVariableArityFinitePSourceMap
      rw [paperVariableArityFinitePSourceInstance_of_decode_none
        p hp input decoded]
      simp only [paperFinitePPhysicalRoutedOutput,
        empty, Bool.false_eq_true, ↓reduceIte, nonempty]
      rfl
  | some formula =>
      by_cases canonical : encodeThreeCNF formula = input
      · subst input
        by_cases empty :
            paperSourceNormalizedClauses formula = []
        · have emptyGuard :
              physicalCanonicalNormalizedEmptyGuard
                (encodeThreeCNF formula) = true := by
            simp only [physicalCanonicalNormalizedEmptyGuard, constructiveCanonicalSourceMarker,
                decodeThreeCNF_encode,
                decide_true, physicalNormalizedEmptyMarker,
                    paperVariableArityPhysicalNormalizedNonemptyMarker_valid, empty, ne_eq,
                not_true_eq_false, decide_false, Bool.not_false, Bool.and_self]
          unfold paperVariableArityFinitePSourceMap
          rw [paperVariableArityFinitePSourceInstance_of_normalized_empty
            p hp (encodeThreeCNF formula) formula (by simp only [decodeThreeCNF_encode]) rfl empty]
          simp only [paperFinitePPhysicalRoutedOutput,
            emptyGuard, ↓reduceIte]
          rfl
        · have emptyGuard :
              physicalCanonicalNormalizedEmptyGuard
                (encodeThreeCNF formula) = false := by
            simp only [physicalCanonicalNormalizedEmptyGuard, constructiveCanonicalSourceMarker,
                decodeThreeCNF_encode,
                decide_true, physicalNormalizedEmptyMarker,
                    paperVariableArityPhysicalNormalizedNonemptyMarker_valid, ne_eq, empty,
                not_false_eq_true, Bool.not_true, Bool.and_false]
          have nonemptyGuard :
              physicalCanonicalNormalizedNonemptyGuard
                (encodeThreeCNF formula) = true := by
            simp only [physicalCanonicalNormalizedNonemptyGuard, constructiveCanonicalSourceMarker,
                decodeThreeCNF_encode,
                decide_true, paperVariableArityPhysicalNormalizedNonemptyMarker_valid, ne_eq,
                    empty, not_false_eq_true,
                Bool.and_self]
          cases consistent :
              (physicalFormulaSystem
                (encodeThreeCNF formula).length
                formula).effectiveReducedConsistent with
          | false =>
              have finitePInconsistent :
                  (paperFinitePPhysicalSystem
                    (encodeThreeCNF formula).length
                    formula).effectiveReducedConsistent = false := by
                simpa only [paperFinitePPhysicalSystem] using consistent
              unfold paperVariableArityFinitePSourceMap
              rw [paperVariableArityFinitePSourceInstance_of_inconsistent
                p hp (encodeThreeCNF formula) formula
                (by simp only [decodeThreeCNF_encode]) rfl empty finitePInconsistent]
              simp only [paperFinitePPhysicalRoutedOutput,
                emptyGuard, Bool.false_eq_true, ↓reduceIte,
                nonemptyGuard,
                paperVariableArityExactPhysicalConsistencyGuard_encode,
                consistent]
              rfl
          | true =>
              have finitePConsistent :
                  (paperFinitePPhysicalSystem
                    (encodeThreeCNF formula).length
                    formula).effectiveReducedConsistent = true := by
                simpa only [paperFinitePPhysicalSystem,
                    Core.BinaryAffineSystem.effectiveReducedConsistent_iff] using
                    consistent
              unfold paperVariableArityFinitePSourceMap
              rw [paperVariableArityFinitePSourceInstance_of_consistent
                p hp (encodeThreeCNF formula) formula
                (by simp only [decodeThreeCNF_encode]) rfl empty finitePConsistent]
              simp only [paperFinitePPhysicalRoutedOutput,
                emptyGuard, Bool.false_eq_true, ↓reduceIte,
                nonemptyGuard,
                paperVariableArityExactPhysicalConsistencyGuard_encode,
                consistent]
              exact paperVariableArityFinitePPhysicalStructuralOutput_valid
                p hp cell formula
      · have sourceGuard :
            constructiveCanonicalSourceMarker input = false := by
          simp only [constructiveCanonicalSourceMarker, decoded, canonical, decide_false]
        have emptyGuard :
            physicalCanonicalNormalizedEmptyGuard input =
              false := by
          simp only [physicalCanonicalNormalizedEmptyGuard, sourceGuard, Bool.false_and]
        have nonemptyGuard :
            physicalCanonicalNormalizedNonemptyGuard input =
              false := by
          simp only [physicalCanonicalNormalizedNonemptyGuard, sourceGuard, Bool.false_and]
        unfold paperVariableArityFinitePSourceMap
        rw [paperVariableArityFinitePSourceInstance_of_noncanonical
          p hp input formula decoded canonical]
        simp only [paperFinitePPhysicalRoutedOutput,
          emptyGuard, Bool.false_eq_true, ↓reduceIte, nonemptyGuard]
        rfl

@[irreducible] private noncomputable def paperVariableArityFinitePSourceMapMachine
    (p : ℚ) (hp : 1 ≤ p) :
    BitTM
      (paperVariableArityFinitePSourceMap p hp) := by
  let shape := paperCanonicalPhysicalMatrixShape
  let cell := paperVariableArityCanonicalPhysicalMatrixCellComputer shape
  have machine :=
    paperVariableArityFinitePPhysicalRoutedOutputComputable p cell
  have equality :
      paperFinitePPhysicalRoutedOutput p cell =
        paperVariableArityFinitePSourceMap p hp :=
    funext (paperVariableArityFinitePPhysicalRoutedOutput_eq_sourceMap
      p hp cell)
  rwa [equality] at machine

theorem paperVariableArityFinitePNPHardPromise
    (p : ℚ) (hp : 1 ≤ p) :
    NPHardPromise (finitePGapCVPPromise p hp) :=
  paperVariableArityFiniteP_nphard_of_sourceMachine p hp
    (paperVariableArityFinitePSourceMapMachine p hp)

end Factor400PaperVariableArityFinitePNormUnconditional

namespace PaperNearestAffineGeneric

open scoped BigOperators

open GapCVP.Factor400BinaryCodeDecodingCorollary GapCVP.Factor400BinaryDecodingPromiseReduction
open GapCVP.Factor400BinaryDecodingPromiseHardness

private noncomputable abbrev nearestInstanceOfAffine
    (system : GapCVP.Core.BinaryAffineSystem) (radius : ℕ) :
    BinaryNearestCodewordInstance where
  blockLength := system.dimension
  generatorRank := system.dimension
  generator := fun row column =>
    (system.effectiveSquareBasisMatrix row column : ZMod 2)
  target := fun row => (system.effectiveAffineRepresentative row : ZMod 2)
  radius := radius

private theorem nearestInstanceOfAffine_eq_basisResidue
    (system : GapCVP.Core.BinaryAffineSystem) (radius : ℕ)
    (coefficients : Fin system.dimension → ℤ) :
    binaryNearestCodeword (nearestInstanceOfAffine system radius)
        (GapCVP.Core.binaryResidue coefficients) =
      GapCVP.Core.binaryResidue
        (system.effectiveSquareBasisMatrix.mulVec coefficients) := by
  funext index
  change
    (∑ column,
      ((system.effectiveSquareBasisMatrix index column : ℤ) : ZMod 2) *
        (coefficients column : ZMod 2)) =
      ((system.effectiveSquareBasisMatrix.mulVec coefficients index : ℤ) :
        ZMod 2)
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul]

private theorem nearestInstanceOfAffine_mem_kernel
    (system : GapCVP.Core.BinaryAffineSystem) (radius : ℕ)
    (coefficients : Fin system.dimension → ZMod 2) :
    system.check.mulVec
      (binaryNearestCodeword
        (nearestInstanceOfAffine system radius) coefficients) = 0 := by
  let lifted := binaryWordLift coefficients
  have kernel : system.InLattice
      (system.effectiveSquareBasisMatrix.mulVec lifted) :=
    (system.inLattice_iff_exists_effectiveSquareBasisMatrix _).mpr
      ⟨lifted, rfl⟩
  have codeword :
      binaryNearestCodeword
          (nearestInstanceOfAffine system radius) coefficients =
        GapCVP.Core.binaryResidue
          (system.effectiveSquareBasisMatrix.mulVec lifted) := by
    calc
      binaryNearestCodeword
          (nearestInstanceOfAffine system radius) coefficients =
        binaryNearestCodeword
          (nearestInstanceOfAffine system radius)
          (GapCVP.Core.binaryResidue (binaryWordLift coefficients)) :=
        congrArg
          (binaryNearestCodeword (nearestInstanceOfAffine system radius))
          (binaryResidue_binaryWordLift coefficients).symm
      _ = GapCVP.Core.binaryResidue
          (system.effectiveSquareBasisMatrix.mulVec
            (binaryWordLift coefficients)) :=
        nearestInstanceOfAffine_eq_basisResidue
          system radius (binaryWordLift coefficients)
  rw [codeword]
  simpa only [GapCVP.Core.BinaryAffineSystem.InLattice, decide_eq_true_eq] using kernel

private theorem nearestInstanceOfAffine_residual_solves
    (system : GapCVP.Core.BinaryAffineSystem) (radius : ℕ)
    (consistent : system.effectiveReducedConsistent = true)
    (coefficients : Fin system.dimension → ZMod 2) :
    system.Solves
      (binaryWordLift
        (binaryNearestTarget (nearestInstanceOfAffine system radius) -
          binaryNearestCodeword
            (nearestInstanceOfAffine system radius) coefficients)) := by
  simp only [GapCVP.Core.BinaryAffineSystem.Solves, decide_eq_true_eq]
  have target : system.check.mulVec
      (binaryNearestTarget (nearestInstanceOfAffine system radius)) =
        system.rightHandSide := by
    have representative := system.effectiveAffineRepresentative_solves consistent
    simp only [GapCVP.Core.BinaryAffineSystem.Solves, decide_eq_true_eq] at representative
    change system.check.mulVec
      (GapCVP.Core.binaryResidue system.effectiveAffineRepresentative) =
        system.rightHandSide
    exact representative
  have kernel := nearestInstanceOfAffine_mem_kernel
    system radius coefficients
  change system.check.mulVec
    (GapCVP.Core.binaryResidue
      (binaryWordLift
        (binaryNearestTarget (nearestInstanceOfAffine system radius) -
          binaryNearestCodeword
            (nearestInstanceOfAffine system radius) coefficients))) =
      system.rightHandSide
  rw [binaryResidue_binaryWordLift]
  funext row
  change
    (∑ column : Fin system.dimension,
      system.check row column *
        (binaryNearestTarget
            (nearestInstanceOfAffine system radius) column -
          binaryNearestCodeword
            (nearestInstanceOfAffine system radius) coefficients column)) =
      system.rightHandSide row
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  calc
    _ = system.rightHandSide row - 0 := by
      congr 1
      · exact congrFun target row
      · exact congrFun kernel row
    _ = system.rightHandSide row := sub_zero _

private theorem nearestInstanceOfAffine_completeness
    (system : GapCVP.Core.BinaryAffineSystem) (radius : ℕ)
    (dimensionPositive : 0 < system.dimension)
    (radiusPositive : 0 < radius)
    (consistent : system.effectiveReducedConsistent = true)
    (vector : Fin system.dimension → ℤ)
    (solution : system.Solves vector)
    (binary : ∀ index, vector index = 0 ∨ vector index = 1)
    (weight : GapCVP.Core.integerSquaredNorm vector = radius) :
    binaryNearestCodewordPromise.yes
      (encodeBinaryNearestCodewordInstance
        (nearestInstanceOfAffine system radius)) := by
  simp only [GapCVP.Factor400BinaryDecodingPromiseHardness.binaryNearestCodewordPromise,
      decide_eq_true_eq]
  have representative := system.effectiveAffineRepresentative_solves consistent
  have difference :
      system.InLattice (system.effectiveAffineRepresentative - vector) := by
    apply
      (system.solves_sub_iff_inLattice representative
        (system.effectiveAffineRepresentative - vector)).mp
    simpa only [sub_sub_cancel] using solution
  obtain ⟨coefficients, coefficientsCorrect⟩ :=
    (system.inLattice_iff_exists_effectiveSquareBasisMatrix
      (system.effectiveAffineRepresentative - vector)).mp difference
  refine ⟨nearestInstanceOfAffine system radius, rfl,
    dimensionPositive, radiusPositive,
    GapCVP.Core.binaryResidue coefficients, ?_⟩
  have codeword := nearestInstanceOfAffine_eq_basisResidue
    system radius coefficients
  have residual :
      binaryNearestTarget (nearestInstanceOfAffine system radius) -
          binaryNearestCodeword (nearestInstanceOfAffine system radius)
            (GapCVP.Core.binaryResidue coefficients) =
        GapCVP.Core.binaryResidue vector := by
    calc
      binaryNearestTarget (nearestInstanceOfAffine system radius) -
          binaryNearestCodeword (nearestInstanceOfAffine system radius)
            (GapCVP.Core.binaryResidue coefficients) =
        GapCVP.Core.binaryResidue system.effectiveAffineRepresentative -
          GapCVP.Core.binaryResidue
            (system.effectiveSquareBasisMatrix.mulVec coefficients) := by
        rw [codeword]
        rfl
      _ = GapCVP.Core.binaryResidue
          (system.effectiveAffineRepresentative -
            system.effectiveSquareBasisMatrix.mulVec coefficients) :=
        (GapCVP.Core.binaryResidue_sub
          system.effectiveAffineRepresentative
          (system.effectiveSquareBasisMatrix.mulVec coefficients)).symm
      _ = GapCVP.Core.binaryResidue vector := by
        rw [coefficientsCorrect]
        simp only [sub_sub_cancel]
  change
    hammingNorm
        (binaryNearestTarget (nearestInstanceOfAffine system radius) -
          binaryNearestCodeword (nearestInstanceOfAffine system radius)
            (GapCVP.Core.binaryResidue coefficients)) ≤ radius
  rw [residual]
  calc
    hammingNorm (GapCVP.Core.binaryResidue vector) =
        GapCVP.Core.integerSquaredNorm vector :=
      (integerSquaredNorm_eq_hammingNorm_binaryResidue vector binary).symm
    _ = radius := weight
    _ ≤ radius := le_rfl

private theorem nearestInstanceOfAffine_soundness
    (system : GapCVP.Core.BinaryAffineSystem) (radius : ℕ)
    (dimensionPositive : 0 < system.dimension)
    (radiusPositive : 0 < radius)
    (consistent : system.effectiveReducedConsistent = true)
    (soundness : ∀ vector : Fin system.dimension → ℤ,
      system.Solves vector →
      (GapCVP.Core.integerSquaredNorm vector : ℝ) ≤
        2 * binaryCodeGapFactor system.dimension * (radius : ℝ) → False) :
    binaryNearestCodewordPromise.no
      (encodeBinaryNearestCodewordInstance
        (nearestInstanceOfAffine system radius)) := by
  simp only [GapCVP.Factor400BinaryDecodingPromiseHardness.binaryNearestCodewordPromise,
      decide_eq_true_eq]
  refine ⟨nearestInstanceOfAffine system radius, rfl,
    dimensionPositive, radiusPositive, ?_⟩
  intro coefficients
  apply lt_of_not_ge
  intro short
  let residual :=
    binaryNearestTarget (nearestInstanceOfAffine system radius) -
      binaryNearestCodeword
        (nearestInstanceOfAffine system radius) coefficients
  apply soundness (binaryWordLift residual)
  · exact nearestInstanceOfAffine_residual_solves
      system radius consistent coefficients
  · rw [integerSquaredNorm_binaryWordLift]
    have factorNonnegative : 0 ≤ binaryCodeGapFactor system.dimension := by
      unfold binaryCodeGapFactor
      positivity
    have radiusNonnegative : (0 : ℝ) ≤ (radius : ℝ) := by
      positivity
    change (hammingNorm residual : ℝ) ≤
      2 * binaryCodeGapFactor system.dimension * (radius : ℝ)
    change (hammingNorm residual : ℝ) ≤
      binaryCodeGapFactor system.dimension * (radius : ℝ) at short
    linarith [mul_nonneg factorNonnegative radiusNonnegative]

end PaperNearestAffineGeneric

namespace PaperNearestInstance

open GapCVP.Factor400BinaryDecodingPromiseReduction
open GapCVP.Factor400BinaryDecodingPromiseHardness
open GapCVP.Factor400BinaryConstructiveSourcePlaces GapCVP.FormulaBridge
open GapCVP.FourFamilySoundness GapCVP.PhysicalColumnOrder GapCVP.PhysicalWordSoundness
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.PaperNearestAffineGeneric

private noncomputable def paperNearestFormulaInstance
    (encodingLength : ℕ) (formula : ThreeCNF) :
    BinaryNearestCodewordInstance :=
  nearestInstanceOfAffine
    (physicalWordBinarySystem encodingLength formula)
    (paperVariableArityIntegerRadius encodingLength formula)

private theorem paperVariableArityNearestFormulaInstance_completeness
    (encodingLength : ℕ) (formula : ThreeCNF)
    (satisfiable : ∃ assignment : ℕ → Bool,
      ∀ clause ∈ formula, clauseSatisfied assignment clause) :
    binaryNearestCodewordPromise.yes
      (encodeBinaryNearestCodewordInstance
        (paperNearestFormulaInstance
          encodingLength formula)) := by
  let system := physicalWordBinarySystem
    encodingLength formula
  obtain ⟨vector, solution, binary, weight⟩ :=
    paperVariableArityPhysicalWordBinarySystem_oneHot_of_satisfiable
      encodingLength formula satisfiable
  refine nearestInstanceOfAffine_completeness
    system (paperVariableArityIntegerRadius encodingLength formula)
    ?_ ?_ ?_ vector ?_ ?_ ?_
  · exact sourceFormulaDimension_pos encodingLength
      (srcFormula formula)
  · exact paperVariableArityIntegerRadius_pos encodingLength formula
  · exact physicalFormulaSystem_consistent_of_satisfiable
      encodingLength formula satisfiable
  · exact solution
  · exact binary
  · exact weight

private theorem paperVariableArityNearestFormulaInstance_soundness
    (encodingLength : ℕ) (formula : ThreeCNF)
    (consistent :
      (physicalWordBinarySystem
        encodingLength formula).effectiveReducedConsistent = true)
    (unsatisfiable : ¬ ∃ assignment : ℕ → Bool,
      ∀ clause ∈ formula, clauseSatisfied assignment clause) :
    binaryNearestCodewordPromise.no
      (encodeBinaryNearestCodewordInstance
        (paperNearestFormulaInstance
          encodingLength formula)) := by
  let system := physicalWordBinarySystem
    encodingLength formula
  apply nearestInstanceOfAffine_soundness
    system (paperVariableArityIntegerRadius encodingLength formula)
  · exact sourceFormulaDimension_pos encodingLength
      (srcFormula formula)
  · exact paperVariableArityIntegerRadius_pos encodingLength formula
  · exact consistent
  · intro vector solution short
    exact unsatisfiable
      (paperVariableArityPhysicalWordBinarySystem_satisfiable_of_scaled_hamming
        encodingLength formula vector solution short)

end PaperNearestInstance

namespace Factor400BinaryDecodingPhysicalWordGaussianPayloadTM

open Turing GapCVP.BinaryEncoding GapCVP.Factor400BinaryDecodingPromiseReduction
open GapCVP.BinaryStructuralRecordTM GapCVP.BinaryGaussianStructuralRecordIndex
open GapCVP.Factor400BinaryEffectiveBasisSerializerTM GapCVP.SourceWholeOutputAssemblyTM
open GapCVP.SourceWholeOutputValidBranchRecordTM
open GapCVP.SourceMixedRadixMaskSelectedFlatPreparationTM

private def compactPhysicalNearestStructuralRecords
    (record : BinaryNearestCodewordInstance) : List (List Bool) :=
  [encodeAtomic record.blockLength, encodeAtomic record.radius] ++
    sourceVectorStructuralRecords record.blockLength
      (fun index => ((record.target index).val : ℤ)) ++
    sourceMatrixStructuralRecords record.blockLength
      record.generatorRank
      (fun row column => ((record.generator row column).val : ℤ))

private theorem compactPhysicalNearestStructuralRecords_length
    (record : BinaryNearestCodewordInstance)
    (hsquare : record.generatorRank = record.blockLength) :
    (compactPhysicalNearestStructuralRecords record).length =
      2 + record.blockLength + record.blockLength * record.blockLength := by
  simp only [compactPhysicalNearestStructuralRecords, List.cons_append, List.nil_append,
      List.length_cons,
    List.length_append, sourceVectorStructuralRecords_length, sourceMatrixStructuralRecords_length,
    hsquare, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd]

private theorem compactPhysicalNearestStructuralRecords_flatten
    (record : BinaryNearestCodewordInstance)
    (hsquare : record.generatorRank = record.blockLength) :
    encodeAtomic record.blockLength ++
        (compactPhysicalNearestStructuralRecords record).flatten =
      encodeBinaryNearestCodewordInstance record := by
  simp only [compactPhysicalNearestStructuralRecords, List.cons_append, List.nil_append,
      List.flatten_cons,
      List.flatten_append, sourceVectorStructuralRecords_flatten,
          sourceMatrixStructuralRecords_flatten,
      encodeBinaryNearestCodewordInstance, hsquare, List.append_assoc]

private theorem compactPhysicalNearestStructuralRecords_getD_dimension
    (record : BinaryNearestCodewordInstance) :
    (compactPhysicalNearestStructuralRecords record).getD 0 [] =
      encodeAtomic record.blockLength := by
  rfl

private theorem compactPhysicalNearestStructuralRecords_getD_radius
    (record : BinaryNearestCodewordInstance) :
    (compactPhysicalNearestStructuralRecords record).getD 1 [] =
      encodeAtomic record.radius := by
  rfl

private theorem compactPhysicalNearestStructuralRecords_getD_target
    (record : BinaryNearestCodewordInstance)
    (index : Fin record.blockLength) :
    (compactPhysicalNearestStructuralRecords record).getD
        (2 + index.val) [] =
      encodeAtomic (((record.target index).val : ℤ)) := by
  let vector := sourceVectorStructuralRecords
    record.blockLength (fun index => ((record.target index).val : ℤ))
  let matrix := sourceMatrixStructuralRecords
    record.blockLength record.generatorRank
      (fun row column => ((record.generator row column).val : ℤ))
  have hsplit : compactPhysicalNearestStructuralRecords record =
      [encodeAtomic record.blockLength, encodeAtomic record.radius] ++
        (vector ++ matrix) := by
    simp only [compactPhysicalNearestStructuralRecords, List.cons_append, List.nil_append, vector,
        matrix]
  rw [hsplit]
  have hprefix :
      ([encodeAtomic record.blockLength,
        encodeAtomic record.radius] : List (List Bool)).length ≤
          2 + index.val := by
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, le_add_iff_nonneg_right,
        zero_le]
  rw [List.getD_append_right
    [encodeAtomic record.blockLength, encodeAtomic record.radius]
    (vector ++ matrix) [] (2 + index.val) hprefix]
  simp only [List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.add_sub_cancel_left]
  have hindex : index.val < vector.length := by
    simp only [sourceVectorStructuralRecords_length, Fin.is_lt, vector]
  rw [List.getD_append vector matrix [] index.val hindex]
  exact sourceVectorStructuralRecords_getD
    record.blockLength (fun index => ((record.target index).val : ℤ)) index

private theorem compactPhysicalNearestStructuralRecords_getD_basis
    (record : BinaryNearestCodewordInstance)
    (row : Fin record.blockLength)
    (column : Fin record.generatorRank) :
    (compactPhysicalNearestStructuralRecords record).getD
        (2 + record.blockLength +
          row.val * record.generatorRank + column.val) [] =
      encodeAtomic (((record.generator row column).val : ℤ)) := by
  let vector := sourceVectorStructuralRecords
    record.blockLength (fun index => ((record.target index).val : ℤ))
  let matrix := sourceMatrixStructuralRecords
    record.blockLength record.generatorRank
      (fun row column => ((record.generator row column).val : ℤ))
  have hsplit : compactPhysicalNearestStructuralRecords record =
      [encodeAtomic record.blockLength, encodeAtomic record.radius] ++
        (vector ++ matrix) := by
    simp only [compactPhysicalNearestStructuralRecords, List.cons_append, List.nil_append, vector,
        matrix]
  rw [hsplit]
  have hprefix :
      ([encodeAtomic record.blockLength,
        encodeAtomic record.radius] : List (List Bool)).length ≤
        2 + record.blockLength +
          row.val * record.generatorRank + column.val := by
    simp only [List.length_cons, List.length_nil]
    omega
  rw [List.getD_append_right
    [encodeAtomic record.blockLength, encodeAtomic record.radius]
    (vector ++ matrix) []
    (2 + record.blockLength +
      row.val * record.generatorRank + column.val) hprefix]
  have hfirst :
      2 + record.blockLength +
          row.val * record.generatorRank + column.val -
        ([encodeAtomic record.blockLength,
          encodeAtomic record.radius] : List (List Bool)).length =
        record.blockLength +
          row.val * record.generatorRank + column.val := by
    simp only [List.length_cons, List.length_nil]
    omega
  rw [hfirst]
  have hvector : vector.length ≤
      record.blockLength +
        row.val * record.generatorRank + column.val := by
    simp only [vector, sourceVectorStructuralRecords_length]
    omega
  rw [List.getD_append_right vector matrix []
    (record.blockLength +
      row.val * record.generatorRank + column.val) hvector]
  have hsecond :
      record.blockLength +
          row.val * record.generatorRank + column.val - vector.length =
        row.val * record.generatorRank + column.val := by
    simp only [vector, sourceVectorStructuralRecords_length]
    omega
  rw [hsecond]
  exact sourceMatrixStructuralRecords_getD
    record.blockLength record.generatorRank
      (fun row column => ((record.generator row column).val : ℤ))
      row column

private theorem compactPhysicalStructuralSourceWord_eq_flattenRecords
    (dimension : SourceQaryMaskDynamicGridWidth)
    (atom : ConstructiveStructuralAtomComputer)
    (input : List Bool) (width : ℕ)
    (records : List (List Bool))
    (hdimension : dimension.output input =
      List.replicate width true)
    (hcount : records.length = 2 + width + width * width)
    (hatoms : ∀ rank : ℕ, rank < records.length →
      atom.output (constructiveStructuralRankQuery
        dimension input rank) = records.getD rank []) :
    constructiveStructuralSourceWord dimension atom input =
      records.flatten := by
  have hcounter :
      constructiveStructuralRecordCountOutput dimension input =
        List.replicate records.length true := by
    rw [constructiveStructuralRecordCountOutput_valid
      dimension input width hdimension, hcount]
  have hdescriptors :
      constructiveStructuralDescriptorOutput dimension atom input =
        sourceFlatAtomicDescriptorStream records :=
    constructiveStructuralDescriptorOutput_eq_records
      dimension atom input width records hdimension hcount hatoms
  change effectiveSourceSerializerOutput
    (constructiveStructuralRecordCountOutput dimension)
    (constructiveStructuralDescriptorOutput dimension atom) input = _
  exact effectiveSourceSerializerOutput_eq_flatten
    (constructiveStructuralRecordCountOutput dimension)
    (constructiveStructuralDescriptorOutput dimension atom)
    (fun _ => records) input hcounter hdescriptors

end Factor400BinaryDecodingPhysicalWordGaussianPayloadTM

namespace PaperNearestIntegerTargetAtom

open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.Factor400BinaryDecodingPhysicalWordSourceTM
open GapCVP.GaussianPhysicalWordRankIndexTM
open GapCVP.Factor400BinaryCompactPhysicalGaussianOutputSerializerTM GapCVP.CanonicalMatrixShape
open GapCVP.BinaryStructuralRecordTM
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.GaussianOutputSerializerTM GapCVP.GaussianAdaptivePackedTraceCorrectness
open GapCVP.SourceWholeOutputAssemblyTM

private def paperNearestRankIntegerTargetAtom
    (reduced : List Bool → List Bool) : List Bool → List Bool :=
  compactPhysicalDecodingGaussianIntegerTargetAtom ∘
    compactPhysicalGaussianRankTargetStateQuery reduced

private noncomputable def paperVariableArityNearestRankIntegerTargetAtomComputable
    {reduced : List Bool → List Bool}
    (computer : BitTM reduced) :
    BitTM
      (paperNearestRankIntegerTargetAtom reduced) :=
  GapCVP.TMComposition.computableInPolyTime
    (compactPhysicalGaussianRankTargetStateQueryComputable computer)
    compactPhysicalDecodingGaussianIntegerTargetAtomComputable

private theorem paperVariableArityNearestRankIntegerTargetAtom_query
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {reduced : List Bool → List Bool}
    (formula : ThreeCNF) (rank : ℕ)
    (index : Fin
      (physicalFormulaSystem
        (encodeThreeCNF formula).length formula).dimension)
    (indexCorrect : rank - 2 = index.val)
    (actual :
      reduced (encodeThreeCNF formula) =
        effectiveGaussianPackedStateWord
          (physicalFormulaSystem
            (encodeThreeCNF formula).length formula).effectiveGaussianState
          (encodeThreeCNF formula)) :
    paperNearestRankIntegerTargetAtom reduced
        (constructiveStructuralRankQuery
          (paperGaussianSourceDimensionWidth shape)
          (encodeThreeCNF formula) rank) =
      encodeAtomic
        ((physicalFormulaSystem
          (encodeThreeCNF formula).length formula).effectiveAffineRepresentative
            index) := by
  unfold paperNearestRankIntegerTargetAtom
  rw [Function.comp_apply]
  unfold compactPhysicalGaussianRankTargetStateQuery
  rw [factor400PhysicalWordGaussianTargetCoordinateUnary_query,
    paperGaussianRankReducedState_query
      shape formula rank actual, indexCorrect]
  exact compactPhysicalDecodingGaussianIntegerTargetAtom_effective
    (physicalFormulaSystem
      (encodeThreeCNF formula).length formula)
    index (encodeThreeCNF formula)

end PaperNearestIntegerTargetAtom

namespace PaperNearestStructuralAtom

open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.CLStructuralAtomicNaturalWriter
open GapCVP.Factor400BinaryDecodingPromiseReduction
open GapCVP.Factor400BinaryDecodingPhysicalWordSourceTM
open GapCVP.Factor400BinaryDecodingPhysicalWordGaussianPayloadTM GapCVP.BinaryStructuralRecordTM
open GapCVP.BinaryExplicitAffineRows GapCVP.BinaryGaussianStructuralAtomTM
open GapCVP.GaussianAdaptivePivotStepTM GapCVP.GaussianAdaptivePackedTraceCorrectness
open GapCVP.GaussianPackedStateBasisAtomTM
open GapCVP.Factor400BinaryCompactPhysicalGaussianOutputSerializerTM GapCVP.CanonicalMatrixShape
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.GaussianOutputSerializerTM GapCVP.SourceWholeOutputAssemblyTM
open GapCVP.PaperBinaryCodingTM GapCVP.PaperNearestInstance GapCVP.PaperNearestIntegerTargetAtom

private def paperNearestRankBinaryBasisAtom
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (reduced : List Bool → List Bool) : List Bool → List Bool :=
  compactPhysicalDecodingBinaryBasisAtom ∘
    gaussianPackedIndexedBasisTag ∘
      paperGaussianRankBasisStateQuery shape reduced

private noncomputable def paperVariableArityNearestRankBinaryBasisAtomComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {reduced : List Bool → List Bool}
    (computer : BitTM reduced) :
    BitTM
      (paperNearestRankBinaryBasisAtom shape reduced) :=
  GapCVP.TMComposition.computableInPolyTime
    (GapCVP.TMComposition.computableInPolyTime
      (paperVariableArityGaussianRankBasisStateQueryComputable shape computer)
      gaussianPackedIndexedBasisTagComputable)
    compactPhysicalDecodingBinaryBasisAtomComputable

private theorem paperVariableArityNearestRankBinaryBasisAtom_query
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {reduced : List Bool → List Bool}
    (formula : ThreeCNF) (rank : ℕ)
    (row column : Fin
      (physicalFormulaSystem
        (encodeThreeCNF formula).length formula).dimension)
    (rowCorrect :
      (rank - (2 + (physicalFormulaSystem
        (encodeThreeCNF formula).length formula).dimension)) /
        (physicalFormulaSystem
          (encodeThreeCNF formula).length formula).dimension = row.val)
    (columnCorrect :
      (rank - (2 + (physicalFormulaSystem
        (encodeThreeCNF formula).length formula).dimension)) %
        (physicalFormulaSystem
          (encodeThreeCNF formula).length formula).dimension = column.val)
    (actual :
      reduced (encodeThreeCNF formula) =
        effectiveGaussianPackedStateWord
          (physicalFormulaSystem
            (encodeThreeCNF formula).length formula).effectiveGaussianState
          (encodeThreeCNF formula)) :
    paperNearestRankBinaryBasisAtom shape reduced
        (constructiveStructuralRankQuery
          (paperGaussianSourceDimensionWidth shape)
          (encodeThreeCNF formula) rank) =
      encodeAtomic
        (((((physicalFormulaSystem
            (encodeThreeCNF formula).length formula).effectiveSquareBasisMatrix
            row column : ℤ) : ZMod 2).val : ℤ)) := by
  unfold paperNearestRankBinaryBasisAtom
  simp only [Function.comp_apply]
  unfold paperGaussianRankBasisStateQuery
  rw [paperVariableArityGaussianBasisRowUnary_query
        shape formula rank,
      paperVariableArityGaussianBasisColumnUnary_query
        shape formula rank,
      paperGaussianRankReducedState_query
        shape formula rank actual,
      rowCorrect, columnCorrect]
  simpa only [gaussianPackedIndexedBasisStateWord,
    affineCellQuery, List.append_assoc] using
    (show compactPhysicalDecodingBinaryBasisAtom
      (gaussianPackedIndexedBasisTag
        (gaussianPackedIndexedBasisStateWord row.val column.val
          (effectiveGaussianPackedStateWord
            (physicalFormulaSystem
              (encodeThreeCNF formula).length formula).effectiveGaussianState
            (encodeThreeCNF formula)))) =
        encodeAtomic
          (((((physicalFormulaSystem
              (encodeThreeCNF formula).length formula).effectiveSquareBasisMatrix
              row column : ℤ) : ZMod 2).val : ℤ)) by
      rw [gaussianPackedIndexedBasisTag_state]
      exact compactPhysicalDecodingBinaryBasisAtom_effective
        (physicalFormulaSystem
          (encodeThreeCNF formula).length formula)
        row column)

private def paperNearestStructuralAtomOutput
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    (reduced : List Bool → List Bool) : List Bool → List Bool :=
  binaryGaussianDynamicBranchOutput
    (structuralRankLessBit structuralRankOneBound)
    (paperGaussianRankDimensionAtomicOutput shape)
    (binaryGaussianDynamicBranchOutput
      (structuralRankLessBit structuralRankTwoBound)
      (compactPhysicalGaussianRankRadiusAtom
        paperCodingRadiusAtomic)
      (binaryGaussianDynamicBranchOutput
        (structuralRankLessBit
          (paperGaussianRankTargetBound shape))
        (paperNearestRankIntegerTargetAtom reduced)
        (paperNearestRankBinaryBasisAtom shape reduced)))

private noncomputable def paperVariableArityNearestStructuralAtomComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {reduced : List Bool → List Bool}
    (computer : BitTM reduced) :
    BitTM
      (paperNearestStructuralAtomOutput shape reduced) := by
  have tail := binaryGaussianDynamicBranchComputable
    (structuralRankLessSelectionComputable
      (paperVariableArityGaussianRankTargetBoundComputable shape))
    (paperVariableArityNearestRankIntegerTargetAtomComputable computer)
    (paperVariableArityNearestRankBinaryBasisAtomComputable shape computer)
  have radius := binaryGaussianDynamicBranchComputable
    (structuralRankLessSelectionComputable
      structuralRankTwoBoundComputable)
    (compactPhysicalGaussianRankRadiusAtomComputable
      paperVariableArityCodingRadiusAtomicComputable)
    tail
  exact binaryGaussianDynamicBranchComputable
    (structuralRankLessSelectionComputable
      structuralRankOneBoundComputable)
    (paperVariableArityGaussianRankDimensionAtomicComputable shape)
    radius

/-- GapCVP reduction support. -/
@[irreducible] noncomputable def
    paperVariableArityNearestStructuralAtomComputer
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {reduced : List Bool → List Bool}
    (computer : BitTM reduced) :
    ConstructiveStructuralAtomComputer :=
  compactPhysicalGaussianStructuralAtomComputerPack
    (paperNearestStructuralAtomOutput shape reduced)
    (paperVariableArityNearestStructuralAtomComputable shape computer)

@[simp] private theorem paperVariableArityNearestStructuralAtomComputer_output
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {reduced : List Bool → List Bool}
    (computer : BitTM reduced)
    (input : List Bool) :
    (paperVariableArityNearestStructuralAtomComputer shape computer).output
        input =
      paperNearestStructuralAtomOutput shape reduced input := by
  unfold paperVariableArityNearestStructuralAtomComputer
  exact compactPhysicalGaussianStructuralAtomComputerPack_output
    (paperNearestStructuralAtomOutput shape reduced)
    (paperVariableArityNearestStructuralAtomComputable shape computer)
    input

private theorem paperVariableArityNearestStructuralAtomOutput_correct
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {reduced : List Bool → List Bool}
    (formula : ThreeCNF)
    (actual :
      reduced (encodeThreeCNF formula) =
        effectiveGaussianPackedStateWord
          (physicalFormulaSystem
            (encodeThreeCNF formula).length formula).effectiveGaussianState
          (encodeThreeCNF formula))
    (rank : ℕ)
    (bound : rank <
      (compactPhysicalNearestStructuralRecords
        (paperNearestFormulaInstance
          (encodeThreeCNF formula).length formula)).length) :
    paperNearestStructuralAtomOutput shape reduced
        (constructiveStructuralRankQuery
          (paperGaussianSourceDimensionWidth shape)
          (encodeThreeCNF formula) rank) =
      (compactPhysicalNearestStructuralRecords
        (paperNearestFormulaInstance
          (encodeThreeCNF formula).length formula)).getD rank [] := by
  let source := encodeThreeCNF formula
  let system := physicalFormulaSystem
    source.length formula
  let record := paperNearestFormulaInstance
    source.length formula
  let width := paperGaussianSourceDimensionWidth shape
  let query := constructiveStructuralRankQuery width source rank
  have one :
      structuralRankLessBit structuralRankOneBound query =
        decide (rank < 1) :=
    structuralRankOneDecision_query width source rank
  have two :
      structuralRankLessBit structuralRankTwoBound query =
        decide (rank < 2) :=
    structuralRankTwoDecision_query width source rank
  have boundary :
      paperGaussianRankTargetBound shape query =
        List.replicate (2 + system.dimension) true := by
    exact paperVariableArityGaussianRankTargetBound_query
      shape formula rank
  have target :
      structuralRankLessBit
          (paperGaussianRankTargetBound shape) query =
        decide (rank < 2 + system.dimension) :=
    structuralRankLessBit_valid
      (paperGaussianRankTargetBound shape)
      query rank (2 + system.dimension)
      (structuralRankUnary_query width source rank) boundary
  change paperNearestStructuralAtomOutput
    shape reduced query =
      (compactPhysicalNearestStructuralRecords record).getD rank []
  unfold paperNearestStructuralAtomOutput
    binaryGaussianDynamicBranchOutput
  rw [one]
  by_cases zeroRank : rank < 1
  · rw [decide_eq_true zeroRank, ite_eq_left (by decide)]
    have exactRank : rank = 0 := by omega
    subst rank
    change
      paperGaussianRankDimensionAtomicOutput shape
          (constructiveStructuralRankQuery
            (paperGaussianSourceDimensionWidth shape)
            source 0) =
        (compactPhysicalNearestStructuralRecords record).getD 0 []
    unfold paperGaussianRankDimensionAtomicOutput
    rw [Function.comp_apply,
      paperGaussianRankDimensionUnary_query shape formula 0,
      compactPhysicalNearestStructuralRecords_getD_dimension record]
    simp only [structuralAtomicNaturalWord, List.length_replicate]
    rfl
  · rw [decide_eq_false zeroRank, ite_eq_right (by decide), two]
    by_cases radiusRank : rank < 2
    · rw [decide_eq_true radiusRank, ite_eq_left (by decide)]
      have exactRank : rank = 1 := by omega
      subst rank
      change compactPhysicalGaussianRankRadiusAtom
          paperCodingRadiusAtomic
            (constructiveStructuralRankQuery
              (paperGaussianSourceDimensionWidth shape)
              source 1) =
        (compactPhysicalNearestStructuralRecords record).getD 1 []
      unfold compactPhysicalGaussianRankRadiusAtom
      rw [Function.comp_apply, structuralRankOriginalSource_query,
        paperVariableArityCodingRadiusAtomic_valid formula,
        compactPhysicalNearestStructuralRecords_getD_radius record]
      rfl
    · rw [decide_eq_false radiusRank, ite_eq_right (by decide), target]
      by_cases targetRank : rank < 2 + system.dimension
      · rw [decide_eq_true targetRank, ite_eq_left (by decide)]
        have indexBound : rank - 2 < system.dimension := by omega
        let index : Fin system.dimension := ⟨rank - 2, indexBound⟩
        have exactRank : rank = 2 + index.val := by
          dsimp [index]
          omega
        have atom := paperVariableArityNearestRankIntegerTargetAtom_query
          shape formula rank index rfl actual
        have exactRecord :
            (compactPhysicalNearestStructuralRecords record).getD
                rank [] =
              encodeAtomic (system.effectiveAffineRepresentative index) := by
          rw [exactRank,
            compactPhysicalNearestStructuralRecords_getD_target
              record index]
          exact congrArg encodeAtomic
            (binaryIntegerLift_intCast_of_zero_or_one
              (system.effectiveAffineRepresentative_eq_zero_or_one index))
        rw [exactRecord]
        exact atom
      · rw [decide_eq_false targetRank, ite_eq_right (by decide)]
        have positive : 0 < system.dimension :=
          physicalFormulaSystem_dimension_pos
            source.length formula
        have square : record.generatorRank = record.blockLength := by
          rfl
        have records :
            rank < 2 + system.dimension +
              system.dimension * system.dimension := by
          have actualBound : rank <
              (compactPhysicalNearestStructuralRecords record).length := by
            simpa only [record, source] using bound
          rw [compactPhysicalNearestStructuralRecords_length
            record square] at actualBound
          exact actualBound
        have start : 2 + system.dimension ≤ rank := by omega
        have offset :
            rank - (2 + system.dimension) <
              system.dimension * system.dimension := by omega
        have rowBound :
            (rank - (2 + system.dimension)) / system.dimension <
              system.dimension :=
          (Nat.div_lt_iff_lt_mul positive).2 offset
        let row : Fin system.dimension :=
          ⟨(rank - (2 + system.dimension)) / system.dimension, rowBound⟩
        let column : Fin system.dimension :=
          ⟨(rank - (2 + system.dimension)) % system.dimension,
            Nat.mod_lt _ positive⟩
        have decomposition :
            row.val * system.dimension + column.val =
              rank - (2 + system.dimension) := by
          dsimp [row, column]
          rw [Nat.mul_comm]
          exact Nat.div_add_mod _ _
        have exactRank :
            rank = 2 + system.dimension +
              row.val * system.dimension + column.val := by
          omega
        have atom := paperVariableArityNearestRankBinaryBasisAtom_query
          shape formula rank row column rfl rfl actual
        have exactRecord :
            (compactPhysicalNearestStructuralRecords record).getD
                rank [] =
              encodeAtomic (((system.effectiveSquareBasisMatrix row column : ZMod 2).val : ℤ))
                  := by
          rw [exactRank]
          exact compactPhysicalNearestStructuralRecords_getD_basis
            record row column
        rw [exactRecord]
        exact atom

end PaperNearestStructuralAtom

namespace PaperNearestGaussianPayloadTM

open Turing GapCVP.Core GapCVP.BinaryEncoding GapCVP.CNFFlatPhysicalBinaryAppendTM
open GapCVP.Factor400BinaryDecodingPromiseReduction
open GapCVP.Factor400BinaryDecodingPhysicalWordGaussianPayloadTM GapCVP.CanonicalMatrixShape
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.BinaryStructuralRecordTM GapCVP.GaussianSourceInitializerInstantiation
open GapCVP.GaussianAdaptivePackedTraceCorrectness GapCVP.GaussianOutputSerializerTM
open GapCVP.PaperBinaryCodingTM GapCVP.PaperNearestAffineGeneric GapCVP.PaperNearestInstance
open GapCVP.PaperNearestStructuralAtom

private noncomputable def paperNearestStructuralSourceWord
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {reduced : List Bool → List Bool}
    (computer : BitTM reduced) : List Bool → List Bool :=
  constructiveStructuralSourceWord
    (paperGaussianSourceDimensionWidth shape)
    (paperVariableArityNearestStructuralAtomComputer shape computer)

private noncomputable def paperVariableArityNearestStructuralSourceWordComputable
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {reduced : List Bool → List Bool}
    (computer : BitTM reduced) :
    BitTM
      (paperNearestStructuralSourceWord shape computer) :=
  constructiveStructuralSourceWordComputable
    (paperGaussianSourceDimensionWidth shape)
    (paperVariableArityNearestStructuralAtomComputer shape computer)

private theorem paperVariableArityNearestStructuralSourceWord_valid
    (shape : PaperVariableArityCanonicalBinaryMatrixShape)
    {reduced : List Bool → List Bool}
    (computer : BitTM reduced)
    (formula : ThreeCNF)
    (actual :
      reduced (encodeThreeCNF formula) =
        effectiveGaussianPackedStateWord
          (physicalFormulaSystem
            (encodeThreeCNF formula).length formula).effectiveGaussianState
          (encodeThreeCNF formula)) :
    paperNearestStructuralSourceWord shape computer
        (encodeThreeCNF formula) =
      (compactPhysicalNearestStructuralRecords
        (paperNearestFormulaInstance
          (encodeThreeCNF formula).length formula)).flatten := by
  let record := paperNearestFormulaInstance
    (encodeThreeCNF formula).length formula
  unfold paperNearestStructuralSourceWord
  apply compactPhysicalStructuralSourceWord_eq_flattenRecords
    (paperGaussianSourceDimensionWidth shape)
    (paperVariableArityNearestStructuralAtomComputer shape computer)
    (encodeThreeCNF formula) record.blockLength
    (compactPhysicalNearestStructuralRecords record)
  · simpa only [record, paperNearestFormulaInstance,
      nearestInstanceOfAffine, physicalFormulaSystem]
      using paperVariableArityGaussianSourceDimensionWidth_valid
        shape formula
  · exact compactPhysicalNearestStructuralRecords_length record rfl
  · intro rank bound
    rw [paperVariableArityNearestStructuralAtomComputer_output]
    exact paperVariableArityNearestStructuralAtomOutput_correct
      shape formula actual rank bound

private noncomputable def paperVariableArityNearestStructuralOutput
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (cell : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (input : List Bool) : List Bool :=
  paperCodingBlockLengthAtomic input ++
    paperNearestStructuralSourceWord shape
      (gaussianPaperVariableArityCanonicalSourceReducedStateComputable cell)
      input

private noncomputable def paperVariableArityNearestStructuralOutputComputable
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (cell : PaperVariableArityCanonicalBinaryMatrixCellComputer shape) :
    BitTM
      (paperVariableArityNearestStructuralOutput cell) :=
  pointwiseAppendComputable
    paperVariableArityCodingBlockLengthAtomicComputable
    (paperVariableArityNearestStructuralSourceWordComputable shape
      (gaussianPaperVariableArityCanonicalSourceReducedStateComputable cell))

private theorem paperVariableArityNearestStructuralOutput_valid
    {shape : PaperVariableArityCanonicalBinaryMatrixShape}
    (cell : PaperVariableArityCanonicalBinaryMatrixCellComputer shape)
    (formula : ThreeCNF) :
    paperVariableArityNearestStructuralOutput cell
        (encodeThreeCNF formula) =
      encodeBinaryNearestCodewordInstance
        (paperNearestFormulaInstance
          (encodeThreeCNF formula).length formula) := by
  unfold paperVariableArityNearestStructuralOutput
  rw [paperVariableArityCodingBlockLengthAtomic_valid formula,
    paperVariableArityNearestStructuralSourceWord_valid shape
      (gaussianPaperVariableArityCanonicalSourceReducedStateComputable cell)
      formula
      (gaussianPaperVariableArityCanonicalSourceReducedStateOutput_effective
        cell formula)]
  exact compactPhysicalNearestStructuralRecords_flatten
    (paperNearestFormulaInstance
      (encodeThreeCNF formula).length formula) rfl

end PaperNearestGaussianPayloadTM

namespace PaperNearestRoutedSource

open GapCVP.BinaryEncoding GapCVP.Factor400BinaryDecodingPromiseReduction
open GapCVP.Factor400BinaryDecodingPromiseHardness GapCVP.OriginalThreeSATNPHardness
open GapCVP.CanonicalPhysicalMatrixShape GapCVP.PhysicalColumnOrder
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalSourceMap
open GapCVP.GaussianExactSourceInitializer GapCVP.GaussianSourceConsistencyBridge
open GapCVP.PaperNearestInstance GapCVP.OutputPolynomialCompositionClosure
open GapCVP.SourceWholeOutputAssemblyTM

private def paperNearestRoutedSourceMap
    (output : List Bool → List Bool) (input : List Bool) : List Bool :=
  if constructiveCanonicalSourceMarker input then
    if binaryGaussianSourceConsistencyGuard
        paperCanonicalSourceBinarySystem input then
      output input
    else
      encodeBinaryNearestCodewordInstance canonicalBinaryNearestCodewordNo
  else
    encodeBinaryNearestCodewordInstance canonicalBinaryNearestCodewordNo

private noncomputable def paperVariableArityNearestRoutedSourceComputable
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer)
    {output : List Bool → List Bool}
    (computer : BitTM output) :
    BitTM
      (paperNearestRoutedSourceMap output) := by
  have consistency := sourcePreservingConditionalComputable
    (gaussianPaperVariableArityAllInputExactConsistencyComputable worker)
    computer
    (encodeBinaryNearestCodewordInstance canonicalBinaryNearestCodewordNo)
  exact sourcePreservingConditionalComputable
    constructiveCanonicalSourceMarkerComputable consistency
    (encodeBinaryNearestCodewordInstance canonicalBinaryNearestCodewordNo)

private theorem paperVariableArityNearestRoutedSource_completeness
    (output : List Bool → List Bool)
    (valid : ∀ formula : ThreeCNF,
      output (encodeThreeCNF formula) =
        encodeBinaryNearestCodewordInstance
          (paperNearestFormulaInstance
            (encodeThreeCNF formula).length formula))
    (input : List Bool)
    (membership : paperOriginalThreeSATLanguage input) :
    binaryNearestCodewordPromise.yes
      (paperNearestRoutedSourceMap output input) := by
  obtain ⟨formula, encoding, satisfiable⟩ :=
    (GapCVP.OriginalThreeSATNPHardness.paperOriginalThreeSATLanguage_iff input).mp membership
  subst input
  have consistent :=
    physicalFormulaSystem_consistent_of_satisfiable
      (encodeThreeCNF formula).length formula satisfiable
  have selected : binaryGaussianSourceConsistencyGuard
      paperCanonicalSourceBinarySystem
      (encodeThreeCNF formula) = true := by
    simpa only [binaryGaussianSourceConsistencyGuard, paperCanonicalSourceBinarySystem,
        decodeThreeCNF_encode,
        ↓reduceIte, Core.BinaryAffineSystem.effectiveReducedConsistent_iff, physicalFormulaSystem]
            using consistent
  simpa only [paperNearestRoutedSourceMap, constructiveCanonicalSourceMarker,
      decodeThreeCNF_encode,
      decide_true, ↓reduceIte, selected, valid formula] using
      paperVariableArityNearestFormulaInstance_completeness (encodeThreeCNF formula).length formula
          satisfiable

private theorem paperVariableArityNearestRoutedSource_soundness
    (output : List Bool → List Bool)
    (valid : ∀ formula : ThreeCNF,
      output (encodeThreeCNF formula) =
        encodeBinaryNearestCodewordInstance
          (paperNearestFormulaInstance
            (encodeThreeCNF formula).length formula))
    (input : List Bool)
    (nonmembership : ¬ paperOriginalThreeSATLanguage input) :
    binaryNearestCodewordPromise.no
      (paperNearestRoutedSourceMap output input) := by
  cases decoded : decodeThreeCNF input with
  | none =>
      simpa only [paperNearestRoutedSourceMap, constructiveCanonicalSourceMarker, decoded,
          Bool.false_eq_true,
          ↓reduceIte] using canonicalBinaryNearestCodewordNo_mem
  | some formula =>
      by_cases canonical : encodeThreeCNF formula = input
      · subst input
        have unsatisfiable : ¬ ∃ assignment : ℕ → Bool,
            ∀ clause ∈ formula, clauseSatisfied assignment clause := by
          intro satisfiable
          exact nonmembership
            ((GapCVP.OriginalThreeSATNPHardness.paperOriginalThreeSATLanguage_iff
              (encodeThreeCNF formula)).mpr ⟨formula, rfl, satisfiable⟩)
        cases consistent :
            (physicalWordBinarySystem
              (encodeThreeCNF formula).length formula).effectiveReducedConsistent with
        | false =>
            simpa only [paperNearestRoutedSourceMap, constructiveCanonicalSourceMarker,
                decodeThreeCNF_encode,
                decide_true, ↓reduceIte, binaryGaussianSourceConsistencyGuard,
                    paperCanonicalSourceBinarySystem, consistent,
                Bool.false_eq_true] using canonicalBinaryNearestCodewordNo_mem
        | true =>
            simpa only [paperNearestRoutedSourceMap, constructiveCanonicalSourceMarker,
                decodeThreeCNF_encode,
                decide_true, ↓reduceIte, binaryGaussianSourceConsistencyGuard,
                    paperCanonicalSourceBinarySystem, consistent,
                valid formula] using
                paperVariableArityNearestFormulaInstance_soundness (encodeThreeCNF formula).length
                    formula consistent unsatisfiable
      · simpa only [paperNearestRoutedSourceMap, constructiveCanonicalSourceMarker, decoded,
          canonical, decide_false,
            Bool.false_eq_true, ↓reduceIte] using canonicalBinaryNearestCodewordNo_mem

private noncomputable def paperVariableArityNearestSourceReduction
    (worker : PaperVariableArityCanonicalPhysicalBinaryMatrixCellComputer)
    {output : List Bool → List Bool}
    (computer : BitTM output)
    (valid : ∀ formula : ThreeCNF,
      output (encodeThreeCNF formula) =
        encodeBinaryNearestCodewordInstance
          (paperNearestFormulaInstance
            (encodeThreeCNF formula).length formula)) :
    PromiseReduction paperOriginalThreeSATLanguage
      binaryNearestCodewordPromise where
  map := paperNearestRoutedSourceMap output
  polynomial_time :=
    ⟨paperVariableArityNearestRoutedSourceComputable worker computer⟩
  completeness := paperVariableArityNearestRoutedSource_completeness
    output valid
  soundness := paperVariableArityNearestRoutedSource_soundness
    output valid

end PaperNearestRoutedSource

namespace Factor400PaperVariableArityNearestUnconditional

open GapCVP.Factor400BinaryDecodingPromiseHardness GapCVP.OriginalThreeSATNPHardness
open GapCVP.CanonicalPhysicalMatrixShape
open GapCVP.Factor400BinaryConstructivePaperVariableArityPhysicalMatrixCellInstantiation
open GapCVP.PaperNearestGaussianPayloadTM GapCVP.PaperNearestRoutedSource

private noncomputable def paperVariableArityNearestUnconditionalSourceReduction :
    PromiseReduction paperOriginalThreeSATLanguage binaryNearestCodewordPromise :=
  paperVariableArityNearestSourceReduction
    (paperVariableArityCanonicalPhysicalMatrixCellComputer
      paperCanonicalPhysicalMatrixShape)
    (paperVariableArityNearestStructuralOutputComputable
      (paperVariableArityCanonicalPhysicalMatrixCellComputer
        paperCanonicalPhysicalMatrixShape))
    (paperVariableArityNearestStructuralOutput_valid
      (paperVariableArityCanonicalPhysicalMatrixCellComputer
        paperCanonicalPhysicalMatrixShape))

theorem binaryNearestCodeword_nphard_unconditional :
    NPHardPromise binaryNearestCodewordPromise :=
  nphardPromise_of_nphard_of_promiseReduction
    paperOriginalThreeSATIsNPHard
    paperVariableArityNearestUnconditionalSourceReduction
    polynomialTimeClosedUnderComposition

end Factor400PaperVariableArityNearestUnconditional

end GapCVP

end
