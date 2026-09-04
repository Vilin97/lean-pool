/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import LeanPool.EhrhartVolumeInequality.Variation
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import all LeanPool.EhrhartVolumeInequality.Variation
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Geometry.Manifold.Sheaf.Basic

/-!
# Ehrhart volume inequality: FourierAnalysis

Fourier, Dolbeault, and weighted Bochner estimates.
-/

noncomputable local instance {n : ℕ} :
    CoeFun (ContDiffBump (0 : Fin n → ℝ)) (fun _ => (Fin n → ℝ) → ℝ) :=
  ⟨ContDiffBump.toFun⟩

noncomputable section

namespace Ehrhart

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace BergmanJetTorusEnvelope

open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert BergmanDiagonalBasisIndependence MomentOptimizer
open MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergman
open BergmanJetUpperEnvelope BergmanJetEnvelopeLimit JetEnvelopeRightDerivative
open scoped BigOperators ENNReal Topology

private def momentEnvelopeTimeSlice
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) (t : ℝ) : ℝ :=
  if ht : 0 < t then
    momentJointUpperEnvelope K F htransport p
      (sourcePositiveJointTimePoint z t ht)
  else
    momentNormalizedPotential F (realLogCoordinate z)

@[simp] private theorem momentEnvelopeTimeSlice_zero
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) :
    momentEnvelopeTimeSlice K F htransport p z 0 =
      momentNormalizedPotential F (realLogCoordinate z) := by
  simp only [momentEnvelopeTimeSlice, lt_self_iff_false, ↓reduceDIte]

private theorem momentEnvelopeTimeSlice_of_nonpositive
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) {t : ℝ} (ht : t ≤ 0) :
    momentEnvelopeTimeSlice K F htransport p z t =
      momentNormalizedPotential F (realLogCoordinate z) := by
  simp only [momentEnvelopeTimeSlice, not_lt.mpr ht, ↓reduceDIte]

private theorem momentEnvelopeTimeSlice_of_positive
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) {t : ℝ} (ht : 0 < t) :
    momentEnvelopeTimeSlice K F htransport p z t =
      momentJointUpperEnvelope K F htransport p
        (sourcePositiveJointTimePoint z t ht) := by
  simp only [momentEnvelopeTimeSlice, ht, ↓reduceDIte]

private theorem momentEnvelopeTimeSlice_le_normalized_add
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) {t : ℝ} (ht : 0 < t) :
    momentEnvelopeTimeSlice K F htransport p z t ≤
      momentNormalizedPotential F (realLogCoordinate z) +
        BodyScale.canonicalScale K * t := by
  rw [momentEnvelopeTimeSlice_of_positive K F htransport p z ht]
  have h := momentJointUpperEnvelope_le_majorant
    K F htransport p (sourcePositiveJointTimePoint z t ht)
  simpa only [ge_iff_le, momentJointMajorant, jointRealCoordinate_sourcePositiveJointTimePoint,
    jointLogTime_sourcePositiveJointTimePoint] using h

private def momentTorusEnvelopeTimeSlice
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : LogTorus n) (t : ℝ) : ℝ :=
  momentEnvelopeTimeSlice K F htransport p
    (sourceTorusCoverPoint q) t

@[simp] private theorem momentTorusEnvelopeTimeSlice_zero
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : LogTorus n) :
    momentTorusEnvelopeTimeSlice K F htransport p q 0 =
      momentNormalizedPotential F q.1 := by
  unfold momentTorusEnvelopeTimeSlice
  rw [momentEnvelopeTimeSlice_zero,
    realLogCoordinate_sourceTorusCoverPoint]

private theorem momentTorusEnvelopeTimeSlice_le_normalized_add
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : LogTorus n) {t : ℝ} (ht : 0 < t) :
    momentTorusEnvelopeTimeSlice K F htransport p q t ≤
      momentNormalizedPotential F q.1 +
        BodyScale.canonicalScale K * t := by
  unfold momentTorusEnvelopeTimeSlice
  simpa only [realLogCoordinate_sourceTorusCoverPoint] using
    momentEnvelopeTimeSlice_le_normalized_add
      K F htransport p (sourceTorusCoverPoint q) ht

private theorem measurable_momentTorusEnvelopeTimeSlice
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (t : ℝ) :
    Measurable
      (fun q : LogTorus n =>
        momentTorusEnvelopeTimeSlice K F htransport p q t) := by
  by_cases ht : 0 < t
  · have hpoint :
        Measurable
          (fun q : LogTorus n =>
            sourcePositiveJointTimePoint
              (sourceTorusCoverPoint q) t ht) := by
      apply Measurable.subtype_mk
      have hcover := measurable_sourceTorusCoverPoint (n := n)
      fun_prop
    change Measurable
      (fun q : LogTorus n =>
        if h : 0 < t then
          momentJointUpperEnvelope K F htransport p
            (sourcePositiveJointTimePoint
              (sourceTorusCoverPoint q) t h)
        else
          momentNormalizedPotential F
            (realLogCoordinate (sourceTorusCoverPoint q)))
    simp only [dite_eq_left ht]
    exact (upperSemicontinuous_momentJointUpperEnvelope
      K F htransport p).measurable.comp hpoint
  · have hnonpos : t ≤ 0 := le_of_not_gt ht
    have heq :
        (fun q : LogTorus n =>
          momentTorusEnvelopeTimeSlice K F htransport p q t) =
        (fun q : LogTorus n =>
          momentNormalizedPotential F q.1) := by
      funext q
      unfold momentTorusEnvelopeTimeSlice
      rw [momentEnvelopeTimeSlice_of_nonpositive
        K F htransport p (sourceTorusCoverPoint q) hnonpos,
        realLogCoordinate_sourceTorusCoverPoint]
    rw [heq]
    exact (continuous_momentNormalizedPotential F).measurable.comp
      measurable_fst

end BergmanJetTorusEnvelope

namespace BergmanJetPhaseLaplace

open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MonomialIntegrability MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity MomentWeakBergman
open scoped BigOperators ENNReal Topology

private theorem exists_momentNormalized_phase_linear_coercivity
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier) :
    ∃ δ C : ℝ, 0 < δ ∧
      ∀ x : Space n,
        phase u (momentNormalizedPotential F) x ≤
          C - δ * ‖x‖ := by
  obtain ⟨δ, C, hδ, hcoerc⟩ :=
    exists_finiteEnergySource_interior_phase_linear_coercivity
      F htransport hu
  let c : ℝ :=
    Real.log
      (finiteEnergySourcePartition F /
        normalizedVolume K.carrier)
  refine ⟨δ, C - c, hδ, ?_⟩
  intro x
  have hx := hcoerc x
  change
    pairing u x -
        (F.potential x +
          Real.log
            (finiteEnergySourcePartition F /
              normalizedVolume K.carrier)) ≤
      C - c - δ * ‖x‖
  dsimp [c]
  linarith

private theorem exists_momentNormalizedPhaseMaximizer
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier) :
    ∃ x : Space n, ∀ y : Space n,
      phase u (momentNormalizedPotential F) y ≤
        phase u (momentNormalizedPotential F) x := by
  obtain ⟨δ, C, hδ, hcoerc⟩ :=
    exists_momentNormalized_phase_linear_coercivity
      F htransport hu
  let φ := momentNormalizedPotential F
  let R : ℝ := max 0 ((C - phase u φ 0) / δ)
  apply (continuous_phase u
    (continuous_momentNormalizedPotential F)).exists_forall_ge' 0
  filter_upwards [
    (isCompact_closedBall (0 : Space n) R).compl_mem_cocompact
  ] with x hx
  have hxnorm : R < ‖x‖ := by
    apply lt_of_not_ge
    intro h
    apply hx
    simpa only [mem_closedBall, dist_zero_right] using h
  have hR : C - phase u φ 0 ≤ δ * R := by
    have hrange : (C - phase u φ 0) / δ ≤ R :=
      le_max_right _ _
    simpa only [tsub_le_iff_right, ge_iff_le, mul_comm] using (div_le_iff₀ hδ).mp hrange
  have hscale := mul_lt_mul_of_pos_left hxnorm hδ
  have hbound := hcoerc x
  change phase u φ x ≤ phase u φ 0
  change phase u φ x ≤ C - δ * ‖x‖ at hbound
  nlinarith

private theorem momentNormalized_monomialIntegral_le_exp_mul_base
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    {M : ℝ}
    (hM : ∀ x : Space n,
      phase u (momentNormalizedPotential F) x ≤ M)
    {k : ℝ} (hk : 1 ≤ k) :
    monomialIntegral k u (momentNormalizedPotential F) ≤
      Real.exp ((k - 1) * M) *
        monomialIntegral 1 u (momentNormalizedPotential F) := by
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hkint :=
    integrable_monomialWeight_momentNormalized_of_mem_interior
      F htransport hu hkpos
  have hbase :=
    integrable_monomialWeight_momentNormalized_of_mem_interior
      F htransport hu (k := (1 : ℝ)) zero_lt_one
  have hmajor := hbase.const_mul (Real.exp ((k - 1) * M))
  unfold monomialIntegral
  calc
    (∫ x : Space n,
      monomialWeight k u (momentNormalizedPotential F) x
        ∂(volume : Measure (Space n))) ≤
      ∫ x : Space n,
        Real.exp ((k - 1) * M) *
          monomialWeight 1 u
            (momentNormalizedPotential F) x
          ∂(volume : Measure (Space n)) := by
            apply integral_mono hkint hmajor
            intro x
            unfold monomialWeight
            change
              Real.exp (k *
                (pairing u x - momentNormalizedPotential F x)) ≤
                Real.exp ((k - 1) * M) *
                  Real.exp (1 *
                    (pairing u x - momentNormalizedPotential F x))
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have hx := hM x
            unfold phase at hx
            nlinarith
    _ = Real.exp ((k - 1) * M) *
        (∫ x : Space n,
          monomialWeight 1 u
            (momentNormalizedPotential F) x
          ∂(volume : Measure (Space n))) :=
      integral_const_mul _ _

private theorem momentNormalized_log_monomialIntegral_div_le
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    {M : ℝ}
    (hM : ∀ x : Space n,
      phase u (momentNormalizedPotential F) x ≤ M)
    {k : ℝ} (hk : 1 ≤ k) :
    Real.log
      (monomialIntegral k u (momentNormalizedPotential F)) / k ≤
        |M| +
          |Real.log
            (monomialIntegral 1 u
              (momentNormalizedPotential F))| := by
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hI :=
    monomialIntegral_momentNormalized_pos
      F htransport hu hkpos
  have hbase :=
    monomialIntegral_momentNormalized_pos
      F htransport hu (k := (1 : ℝ)) zero_lt_one
  have hupper :=
    momentNormalized_monomialIntegral_le_exp_mul_base
      F htransport hu hM hk
  have hlog := Real.log_le_log hI hupper
  rw [Real.log_mul (Real.exp_ne_zero _) hbase.ne',
    Real.log_exp] at hlog
  apply (div_le_iff₀ hkpos).mpr
  calc
    Real.log
      (monomialIntegral k u (momentNormalizedPotential F)) ≤
        (k - 1) * M +
          Real.log
            (monomialIntegral 1 u
              (momentNormalizedPotential F)) := hlog
    _ ≤ k * |M| +
          k * |Real.log
            (monomialIntegral 1 u
              (momentNormalizedPotential F))| := by
      apply add_le_add
      · calc
          (k - 1) * M ≤
              (k - 1) * |M| :=
            mul_le_mul_of_nonneg_left
              (le_abs_self M) (sub_nonneg.mpr hk)
          _ ≤ k * |M| :=
            mul_le_mul_of_nonneg_right
              (by linarith) (abs_nonneg M)
      · calc
          Real.log
            (monomialIntegral 1 u
              (momentNormalizedPotential F)) ≤
              |Real.log
                (monomialIntegral 1 u
                  (momentNormalizedPotential F))| :=
            le_abs_self _
          _ ≤ k * |Real.log
              (monomialIntegral 1 u
                (momentNormalizedPotential F))| := by
            have hnonneg :
                0 ≤ |Real.log
                  (monomialIntegral 1 u
                    (momentNormalizedPotential F))| :=
              abs_nonneg _
            nlinarith
    _ = (|M| +
            |Real.log
              (monomialIntegral 1 u
                (momentNormalizedPotential F))|) * k := by ring

private theorem exists_momentNormalized_log_monomialIntegral_uniform_bound
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier) :
    ∃ C : ℝ, ∀ k : ℕ, 0 < k →
      Real.log
        (monomialIntegral (k : ℝ) u
          (momentNormalizedPotential F)) /
            (k : ℝ) ≤ C := by
  obtain ⟨δ, M, hδ, hphase⟩ :=
    exists_momentNormalized_phase_linear_coercivity
      F htransport hu
  have hM : ∀ x : Space n,
      phase u (momentNormalizedPotential F) x ≤ M := by
    intro x
    exact (hphase x).trans
      (sub_le_self _ (mul_nonneg hδ.le (norm_nonneg x)))
  refine ⟨|M| +
    |Real.log
      (monomialIntegral 1 u
        (momentNormalizedPotential F))|, ?_⟩
  intro k hk
  have hkreal : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hk
  exact momentNormalized_log_monomialIntegral_div_le
    F htransport hu hM hkreal

end BergmanJetPhaseLaplace

namespace BergmanJetMonomialEnvelopeLower

open Set Function Filter MeasureTheory Metric
open SupportFunction MonomialIntegrability BergmanMonomials BergmanDiagonalBasisIndependence
open LatticeAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity
open MomentWeakBergman BergmanJetRealGeodesic BergmanJetUpperEnvelope
open BergmanJetEnvelopePlurisubharmonic BergmanJetEnvelopeLimit BergmanJetTorusEnvelope
open BergmanJetPhaseLaplace JetEnvelopeRightDerivative ActualJetUpperEnvelope
open scoped BigOperators ENNReal Topology

private def repeatedMomentMonomialIndex
    {n k : ℕ} (K : CenteredBody n)
    (hk : 0 < k)
    (u : monomialIndex K k)
    (s : ℕ) (hs : 0 < s) :
    monomialIndex K (s * k) := by
  have hsk : 0 < s * k := Nat.mul_pos hs hk
  refine ⟨(u : Space n), ?_⟩
  apply (mem_monomialIndex_iff K hsk
    (u : Space n)).mpr
  obtain ⟨hu, hz⟩ :=
    (mem_monomialIndex_iff K hk
      (u : Space n)).mp u.property
  refine ⟨hu, ?_⟩
  intro i
  obtain ⟨m, hm⟩ := hz i
  refine ⟨(s : ℤ) * m, ?_⟩
  change
    (((s : ℤ) * m : ℤ) : ℝ) =
      ((s * k : ℕ) : ℝ) * (u : Space n) i
  push_cast
  change ((s : ℕ) : ℝ) * (m : ℝ) =
    ((s : ℕ) : ℝ) * (k : ℝ) * (u : Space n) i
  have hm' : (m : ℝ) = (k : ℝ) * (u : Space n) i := by
    exact_mod_cast hm
  rw [hm']
  ring

private theorem moment_diagonalTerm_le_diagonalKernel
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k)
    (x : Space n) :
    diagonalTerm K k (momentNormalizedPotential F) u x ≤
      diagonalKernel K k
        (momentNormalizedPotential F) x := by
  classical
  let := (monomialIndex_finite K hk).fintype
  unfold diagonalKernel
  rw [tsum_fintype]
  have hnonneg :
      ∀ v : monomialIndex K k,
        0 ≤ diagonalTerm K k
          (momentNormalizedPotential F) v x := by
    intro v
    unfold diagonalTerm
    exact div_nonneg (Real.exp_pos _).le
      (monomialIntegral_momentNormalized_pos
        F htransport v.property.1
        (by exact_mod_cast hk)).le
  simpa only [ge_iff_le] using
    (Finset.single_le_sum
      (s := (Finset.univ : Finset (monomialIndex K k)))
      (f := fun v : monomialIndex K k =>
        diagonalTerm K k (momentNormalizedPotential F) v x)
      (fun v _ => hnonneg v)
      (Finset.mem_univ u))

private theorem moment_pairing_sub_log_monomialNorm_le_log_diagonal
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k)
    (x : Space n) :
    pairing (u : Space n) x -
      Real.log
        (monomialIntegral (k : ℝ) (u : Space n)
          (momentNormalizedPotential F)) / (k : ℝ) ≤
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) x) / (k : ℝ) := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hnorm :
      0 < monomialNormSquared k (u : Space n)
        (momentNormalizedPotential F) :=
    monomialIntegral_momentNormalized_pos
      F htransport u.property.1 hkreal
  have hterm :
      0 < diagonalTerm K k
        (momentNormalizedPotential F) u x := by
    unfold diagonalTerm
    exact div_pos (Real.exp_pos _) hnorm
  have hle := moment_diagonalTerm_le_diagonalKernel
    K hk F htransport u x
  have hlog := Real.log_le_log hterm hle
  unfold diagonalTerm at hlog
  rw [Real.log_div (Real.exp_ne_zero _) hnorm.ne',
    Real.log_exp] at hlog
  calc
    pairing (u : Space n) x -
        Real.log
          (monomialIntegral (k : ℝ) (u : Space n)
            (momentNormalizedPotential F)) / (k : ℝ) =
      ((k : ℝ) * pairing (u : Space n) x -
        Real.log
          (monomialNormSquared k (u : Space n)
            (momentNormalizedPotential F))) / (k : ℝ) := by
          unfold monomialNormSquared
          field_simp
    _ ≤ Real.log
        (diagonalKernel K k
          (momentNormalizedPotential F) x) / (k : ℝ) :=
      (div_le_div_iff_of_pos_right hkreal).mpr hlog

private theorem moment_fixedMonomial_pairing_sub_le_log_diagonal
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k)
    {C : ℝ}
    (hC : ∀ l : ℕ, 0 < l →
      Real.log
        (monomialIntegral (l : ℝ) (u : Space n)
          (momentNormalizedPotential F)) /
            (l : ℝ) ≤ C)
    (s : ℕ) (hs : 0 < s)
    (x : Space n) :
    pairing (u : Space n) x - C ≤
      Real.log
        (diagonalKernel K (s * k)
          (momentNormalizedPotential F) x) /
            ((s * k : ℕ) : ℝ) := by
  have hsk := Nat.mul_pos hs hk
  let v := repeatedMomentMonomialIndex K hk u s hs
  have hnorm := hC (s * k) hsk
  have hdiag :=
    moment_pairing_sub_log_monomialNorm_le_log_diagonal
      K hsk F htransport v x
  change
    pairing (u : Space n) x -
      Real.log
        (monomialIntegral ((s * k : ℕ) : ℝ)
          (u : Space n)
          (momentNormalizedPotential F)) /
            ((s * k : ℕ) : ℝ) ≤
      Real.log
        (diagonalKernel K (s * k)
          (momentNormalizedPotential F) x) /
            ((s * k : ℕ) : ℝ) at hdiag
  linarith

private theorem moment_fixedMonomial_pairing_sub_le_positiveJointGeodesic
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k)
    {C : ℝ}
    (hC : ∀ l : ℕ, 0 < l →
      Real.log
        (monomialIntegral (l : ℝ) (u : Space n)
          (momentNormalizedPotential F)) /
            (l : ℝ) ≤ C)
    (p : TorusCharacters.LogSpace n)
    (s : ℕ) (hs : 0 < s)
    (q : PositiveJointLogSpace n) :
    pairing (u : Space n)
        (realLogCoordinate q.val.1) - C ≤
      momentPositiveJointGeodesic K F htransport p
        (s * k - 1) q := by
  let l := s * k - 1
  have hsk : 0 < s * k := Nat.mul_pos hs hk
  have hl : l + 1 = s * k := by
    dsimp [l]
    omega
  let N :=
    Nat.floor
      (BodyScale.canonicalScale K *
        ((l + 1 : ℕ) : ℝ))
  calc
    pairing (u : Space n)
        (realLogCoordinate q.val.1) - C ≤
      Real.log
        (diagonalKernel K (s * k)
          (momentNormalizedPotential F)
          (realLogCoordinate q.val.1)) /
            ((s * k : ℕ) : ℝ) :=
      moment_fixedMonomial_pairing_sub_le_log_diagonal
        K hk F htransport u hC s hs
        (realLogCoordinate q.val.1)
    _ = Real.log
        (diagonalKernel K (l + 1)
          (momentNormalizedPotential F)
          (realLogCoordinate q.val.1)) /
            ((l + 1 : ℕ) : ℝ) := by rw [hl]
    _ = momentJetGeodesic K
        (Nat.zero_lt_succ l) F htransport p N q.val.1 0 :=
      (momentJetGeodesic_zero_eq_log_diagonalKernel
        K (Nat.zero_lt_succ l) F htransport p q.val.1 N).symm
    _ ≤ momentJetGeodesic K
        (Nat.zero_lt_succ l) F htransport p N
        q.val.1 (jointLogTime q) :=
      monotone_momentJetGeodesic
        K (Nat.zero_lt_succ l) F htransport p q.val.1 N
        (jointLogTime_pos q).le
    _ = momentPositiveJointGeodesic
        K F htransport p l q := by
      symm
      exact momentPositiveJointGeodesic_eq_momentJetGeodesic
        K F htransport p l q

private theorem moment_fixedMonomial_pairing_sub_le_tailSup
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k)
    {C : ℝ}
    (hC : ∀ l : ℕ, 0 < l →
      Real.log
        (monomialIntegral (l : ℝ) (u : Space n)
          (momentNormalizedPotential F)) /
            (l : ℝ) ≤ C)
    (p : TorusCharacters.LogSpace n)
    (r : ℕ) (q : PositiveJointLogSpace n) :
    pairing (u : Space n)
        (realLogCoordinate q.val.1) - C ≤
      momentJointTailSup K F htransport p r q := by
  let a := momentJointTailStart K F htransport p + r
  let s := a + 1
  have hs : 0 < s := by
    dsimp [s]
    omega
  have hbig : a + 1 ≤ s * k := by
    dsimp [s]
    exact Nat.le_mul_of_pos_right (a + 1) hk
  let j := s * k - 1 - a
  have hindex : a + j = s * k - 1 := by
    dsimp [j]
    omega
  calc
    pairing (u : Space n)
        (realLogCoordinate q.val.1) - C ≤
      momentPositiveJointGeodesic K F htransport p
        (s * k - 1) q :=
      moment_fixedMonomial_pairing_sub_le_positiveJointGeodesic
        K hk F htransport u hC p s hs q
    _ = momentPositiveJointGeodesic K F htransport p
        (a + j) q := by rw [hindex]
    _ ≤ momentJointTailSup K F htransport p r q := by
      unfold momentJointTailSup
      apply le_csSup
        (momentJointTailSup_range_bddAbove
          K F htransport p r q)
      refine ⟨j, ?_⟩
      change
        momentPositiveJointGeodesic K F htransport p
          (momentJointTailStart K F htransport p + r + j) q =
        momentPositiveJointGeodesic K F htransport p
          (a + j) q
      rfl

private theorem moment_fixedMonomial_pairing_sub_le_tailUpperEnvelope
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k)
    {C : ℝ}
    (hC : ∀ l : ℕ, 0 < l →
      Real.log
        (monomialIntegral (l : ℝ) (u : Space n)
          (momentNormalizedPotential F)) /
            (l : ℝ) ≤ C)
    (p : TorusCharacters.LogSpace n)
    (r : ℕ) (q : PositiveJointLogSpace n) :
    pairing (u : Space n)
        (realLogCoordinate q.val.1) - C ≤
      momentJointTailUpperEnvelope K F htransport p r q := by
  calc
    pairing (u : Space n)
        (realLogCoordinate q.val.1) - C ≤
      momentJointTailSup K F htransport p r q :=
      moment_fixedMonomial_pairing_sub_le_tailSup
        K hk F htransport u hC p r q
    _ ≤ momentJointTailUpperEnvelope
        K F htransport p r q :=
      le_upperRegularization
        (momentJointTailSup K F htransport p r) q
        (momentJointTailSup_localUpperBounds_nonempty
          K F htransport p r q)

private theorem moment_fixedMonomial_pairing_sub_le_upperEnvelope
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k)
    {C : ℝ}
    (hC : ∀ l : ℕ, 0 < l →
      Real.log
        (monomialIntegral (l : ℝ) (u : Space n)
          (momentNormalizedPotential F)) /
            (l : ℝ) ≤ C)
    (p : TorusCharacters.LogSpace n)
    (q : PositiveJointLogSpace n) :
    pairing (u : Space n)
        (realLogCoordinate q.val.1) - C ≤
      momentJointUpperEnvelope K F htransport p q := by
  apply (le_ciInf_iff
    (momentJointTailUpperEnvelope_bddBelow
      K F htransport p q)).mpr
  intro r
  exact moment_fixedMonomial_pairing_sub_le_tailUpperEnvelope
    K hk F htransport u hC p r q

private theorem moment_fixedMonomial_pairing_sub_le_torusEnvelope
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k)
    {C : ℝ}
    (hC : ∀ l : ℕ, 0 < l →
      Real.log
        (monomialIntegral (l : ℝ) (u : Space n)
          (momentNormalizedPotential F)) /
            (l : ℝ) ≤ C)
    (p : TorusCharacters.LogSpace n)
    (q : WeightedTorusHilbert.LogTorus n)
    {t : ℝ} (ht : 0 < t) :
    pairing (u : Space n) q.1 - C ≤
      momentTorusEnvelopeTimeSlice
        K F htransport p q t := by
  unfold momentTorusEnvelopeTimeSlice
  rw [momentEnvelopeTimeSlice_of_positive
    K F htransport p (sourceTorusCoverPoint q) ht]
  have h := moment_fixedMonomial_pairing_sub_le_upperEnvelope
    K hk F htransport u hC p
      (sourcePositiveJointTimePoint
        (sourceTorusCoverPoint q) t ht)
  simpa only [sourcePositiveJointTimePoint, Complex.ofReal_exp, Complex.ofReal_div,
    Complex.ofReal_ofNat, tsub_le_iff_right, ge_iff_le,
    realLogCoordinate_sourceTorusCoverPoint] using h

private theorem exists_moment_fixedMonomial_torusEnvelope_lower
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) :
    ∃ C : ℝ, ∀ (p : TorusCharacters.LogSpace n)
      (q : WeightedTorusHilbert.LogTorus n)
      (t : ℝ), 0 < t →
        pairing (u : Space n) q.1 - C ≤
          momentTorusEnvelopeTimeSlice
            K F htransport p q t := by
  obtain ⟨C, hC⟩ :=
    exists_momentNormalized_log_monomialIntegral_uniform_bound
      F htransport u.property.1
  exact ⟨C, fun p q t ht =>
    moment_fixedMonomial_pairing_sub_le_torusEnvelope
      K hk F htransport u hC p q ht⟩

end BergmanJetMonomialEnvelopeLower

namespace BergmanJetPointwiseLogKernel

open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MonomialIntegrability BergmanMonomials MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentRegularity MomentWeakBergman
open MomentWeakGlobalKernel BergmanJetPhaseLaplace BergmanJetMonomialEnvelopeLower
open MomentMoserTrudinger SpatialBergmanPointwiseAsymptotics
open scoped BigOperators ENNReal Topology

private theorem exists_eventual_momentNormalized_uniform_moving_phase_coercivity
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u₀ : Space n} (hu₀ : u₀ ∈ interior K.carrier)
    (u : ℕ → Space n)
    (hu : Tendsto u atTop (𝓝 u₀)) :
    ∃ d C : ℝ, 0 < d ∧
      ∀ᶠ k : ℕ in atTop, ∀ z : Space n,
        phase (u k) (momentNormalizedPotential F) z ≤
          C - d * ‖z‖ := by
  obtain ⟨δ, C, hδ, hcoerce⟩ :=
    exists_momentNormalized_phase_linear_coercivity
      F htransport hu₀
  have hnorm :
      Tendsto (fun k : ℕ => ‖u k - u₀‖)
        atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero] using (hu.sub_const u₀).norm
  have hscaled :
      Tendsto (fun k : ℕ => (n : ℝ) * ‖u k - u₀‖)
        atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hnorm.const_mul (n : ℝ)
  have hsmall :
      ∀ᶠ k : ℕ in atTop,
        (n : ℝ) * ‖u k - u₀‖ < δ / 2 :=
    hscaled (Iio_mem_nhds (half_pos hδ))
  refine ⟨δ / 2, C, half_pos hδ, ?_⟩
  filter_upwards [hsmall] with k hk z
  have hpair :
      pairing (u k - u₀) z ≤ (δ / 2) * ‖z‖ := by
    calc
      pairing (u k - u₀) z ≤ |pairing (u k - u₀) z| :=
        le_abs_self _
      _ ≤ ((n : ℝ) * ‖u k - u₀‖) * ‖z‖ :=
        MonomialDivergence.abs_pairing_le_dimension_mul_norm
          (u k - u₀) z
      _ ≤ (δ / 2) * ‖z‖ :=
        mul_le_mul_of_nonneg_right hk.le (norm_nonneg z)
  have hsplit :
      phase (u k) (momentNormalizedPotential F) z =
        phase u₀ (momentNormalizedPotential F) z +
          pairing (u k - u₀) z := by
    unfold phase
    rw [MonomialDivergence.pairing_sub_left]
    ring
  rw [hsplit]
  linarith [hcoerce z]

private theorem exists_eventual_momentNormalized_moving_base_integral_bound
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u₀ : Space n} (hu₀ : u₀ ∈ interior K.carrier)
    (u : ℕ → Space n)
    (hu : Tendsto u atTop (𝓝 u₀)) :
    ∃ B : ℝ, 0 < B ∧
      ∀ᶠ k : ℕ in atTop,
        monomialIntegral 1 (u k)
          (momentNormalizedPotential F) ≤ B := by
  obtain ⟨d, C, hd, hcoerce⟩ :=
    exists_eventual_momentNormalized_uniform_moving_phase_coercivity
      K F htransport hu₀ u hu
  have hrad := integrable_exp_neg_mul_norm_all (n := n) hd
  let B : ℝ := max 1
    (Real.exp C *
      (∫ z : Space n,
        Real.exp (-d * ‖z‖)
          ∂(volume : Measure (Space n))))
  have hB : 0 < B :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hinterior :
      ∀ᶠ k : ℕ in atTop, u k ∈ interior K.carrier :=
    hu.eventually (isOpen_interior.mem_nhds hu₀)
  refine ⟨B, hB, ?_⟩
  filter_upwards [hcoerce, hinterior] with k hk hku
  calc
    monomialIntegral 1 (u k)
        (momentNormalizedPotential F) ≤
      ∫ z : Space n,
        Real.exp C * Real.exp (-d * ‖z‖)
          ∂(volume : Measure (Space n)) := by
      unfold monomialIntegral
      apply MeasureTheory.integral_mono
        (integrable_monomialWeight_momentNormalized_of_mem_interior
          F htransport hku zero_lt_one)
        (hrad.const_mul (Real.exp C))
      intro z
      unfold monomialWeight
      simp only [one_mul]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h := hk z
      unfold phase at h
      linarith
    _ = Real.exp C *
        (∫ z : Space n,
          Real.exp (-d * ‖z‖)
            ∂(volume : Measure (Space n))) := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ B := le_max_right _ _

private theorem eventually_momentNormalized_moving_phase_le_max_add
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u₀ : Space n} (hu₀ : u₀ ∈ interior K.carrier)
    (u : ℕ → Space n)
    (hu : Tendsto u atTop (𝓝 u₀))
    (x : Space n)
    (hmax : ∀ z : Space n,
      phase u₀ (momentNormalizedPotential F) z ≤
        phase u₀ (momentNormalizedPotential F) x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ z : Space n,
      phase (u k) (momentNormalizedPotential F) z ≤
        phase u₀ (momentNormalizedPotential F) x + ε := by
  obtain ⟨d, C, hd, hcoerce⟩ :=
    exists_eventual_momentNormalized_uniform_moving_phase_coercivity
      K F htransport hu₀ u hu
  let M : ℝ := phase u₀ (momentNormalizedPotential F) x
  let R : ℝ := max 1 ((C - M) / d)
  have hR : 0 < R :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hboundary : C - d * R ≤ M := by
    have hratio : (C - M) / d ≤ R := le_max_right _ _
    have hmul := (div_le_iff₀ hd).mp hratio
    nlinarith
  have hnorm :
      Tendsto (fun k : ℕ => ‖u k - u₀‖)
        atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero] using (hu.sub_const u₀).norm
  have herr :
      Tendsto
        (fun k : ℕ => (n : ℝ) * ‖u k - u₀‖ * R)
        atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, zero_mul] using (hnorm.const_mul (n : ℝ)).mul_const R
  have hsmall :
      ∀ᶠ k : ℕ in atTop,
        (n : ℝ) * ‖u k - u₀‖ * R < ε :=
    herr (Iio_mem_nhds hε)
  filter_upwards [hcoerce, hsmall] with k hk herrk z
  by_cases hz : ‖z‖ ≤ R
  · have hpair :
        pairing (u k - u₀) z < ε := by
      calc
        pairing (u k - u₀) z ≤
            |pairing (u k - u₀) z| := le_abs_self _
        _ ≤ ((n : ℝ) * ‖u k - u₀‖) * ‖z‖ :=
          MonomialDivergence.abs_pairing_le_dimension_mul_norm
            (u k - u₀) z
        _ ≤ ((n : ℝ) * ‖u k - u₀‖) * R := by
          gcongr
        _ < ε := herrk
    have hsplit :
        phase (u k) (momentNormalizedPotential F) z =
          phase u₀ (momentNormalizedPotential F) z +
            pairing (u k - u₀) z := by
      unfold phase
      rw [MonomialDivergence.pairing_sub_left]
      ring
    rw [hsplit]
    dsimp [M] at *
    linarith [hmax z]
  · have hz' : R < ‖z‖ := lt_of_not_ge hz
    have hdecay : C - d * ‖z‖ ≤ M := by
      calc
        C - d * ‖z‖ ≤ C - d * R := by
          nlinarith
        _ ≤ M := hboundary
    exact (hk z).trans
      (hdecay.trans (by dsimp [M]; linarith))

private theorem eventually_log_momentNormalized_moving_monomialIntegral_div_le
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u₀ : Space n} (hu₀ : u₀ ∈ interior K.carrier)
    (u : ℕ → Space n)
    (hu : Tendsto u atTop (𝓝 u₀))
    (x : Space n)
    (hmax : ∀ z : Space n,
      phase u₀ (momentNormalizedPotential F) z ≤
        phase u₀ (momentNormalizedPotential F) x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      Real.log
          (monomialIntegral (k : ℝ) (u k)
            (momentNormalizedPotential F)) / (k : ℝ) ≤
        phase u₀ (momentNormalizedPotential F) x + ε := by
  obtain ⟨B, hB, hbase⟩ :=
    exists_eventual_momentNormalized_moving_base_integral_bound
      K F htransport hu₀ u hu
  let M : ℝ :=
    phase u₀ (momentNormalizedPotential F) x + ε / 2
  have hphase :=
    eventually_momentNormalized_moving_phase_le_max_add
      K F htransport hu₀ u hu x hmax (half_pos hε)
  have hinterior :
      ∀ᶠ k : ℕ in atTop, u k ∈ interior K.carrier :=
    hu.eventually (isOpen_interior.mem_nhds hu₀)
  have herr :
      Tendsto
        (fun k : ℕ => (Real.log B - M) / (k : ℝ))
        atTop (𝓝 (0 : ℝ)) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop
      (Real.log B - M)
  have hsmall :
      ∀ᶠ k : ℕ in atTop,
        (Real.log B - M) / (k : ℝ) < ε / 2 :=
    herr (Iio_mem_nhds (half_pos hε))
  filter_upwards
    [eventually_ge_atTop (1 : ℕ), hinterior,
      hbase, hphase, hsmall]
    with k hk hku hbasek hphasek hsmallk
  have hkreal : 0 < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hknorm : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hk
  have hI :
      0 < monomialIntegral (k : ℝ) (u k)
        (momentNormalizedPotential F) :=
    monomialIntegral_momentNormalized_pos
      F htransport hku hkreal
  have hupper :=
    momentNormalized_monomialIntegral_le_exp_mul_base
      F htransport hku hphasek hknorm
  have hIupper :
      monomialIntegral (k : ℝ) (u k)
          (momentNormalizedPotential F) ≤
        Real.exp (((k : ℝ) - 1) * M) * B := by
    exact hupper.trans
      (mul_le_mul_of_nonneg_left hbasek
        (Real.exp_pos _).le)
  have hlog := Real.log_le_log hI hIupper
  rw [Real.log_mul (Real.exp_ne_zero _) hB.ne',
    Real.log_exp] at hlog
  calc
    Real.log
        (monomialIntegral (k : ℝ) (u k)
          (momentNormalizedPotential F)) / (k : ℝ) ≤
      (((k : ℝ) - 1) * M + Real.log B) / (k : ℝ) :=
        (div_le_div_iff_of_pos_right hkreal).mpr hlog
    _ = M + (Real.log B - M) / (k : ℝ) := by
      (field_simp; ring)
    _ ≤ phase u₀ (momentNormalizedPotential F) x + ε := by
      dsimp [M] at *
      linarith

private theorem eventually_log_momentNormalized_diagonalKernel_div_ge_sub
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    (x : Space n)
    (hmax : ∀ z : Space n,
      phase u (momentNormalizedPotential F) z ≤
        phase u (momentNormalizedPotential F) x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      momentNormalizedPotential F x - ε ≤
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) x) / (k : ℝ) := by
  let v : ℕ → Space n :=
    fun k => (nearestMonomialIndex K u k : Space n)
  have hv : Tendsto v atTop (𝓝 u) :=
    tendsto_nearestMonomialIndex K hu
  have hpair :
      Tendsto
        (fun k : ℕ => pairing (v k) x)
        atTop (𝓝 (pairing u x)) :=
    (continuous_pairing_left x).continuousAt.tendsto.comp hv
  have hpairlower :
      ∀ᶠ k : ℕ in atTop,
        pairing u x - ε / 2 < pairing (v k) x := by
    exact hpair (Ioi_mem_nhds (by linarith))
  have hphase :=
    eventually_log_momentNormalized_moving_monomialIntegral_div_le
      K F htransport hu v hv x hmax (half_pos hε)
  filter_upwards
    [eventually_ge_atTop (1 : ℕ), hpairlower, hphase]
    with k hk hpairk hphasek
  have hkpos : 0 < k :=
    lt_of_lt_of_le Nat.zero_lt_one hk
  have hdiag :=
    moment_pairing_sub_log_monomialNorm_le_log_diagonal
      K hkpos F htransport (nearestMonomialIndex K u k) x
  change
    pairing (v k) x -
        Real.log
          (monomialIntegral (k : ℝ) (v k)
            (momentNormalizedPotential F)) / (k : ℝ) ≤
      Real.log
        (diagonalKernel K k
          (momentNormalizedPotential F) x) / (k : ℝ)
    at hdiag
  unfold phase at hphasek
  linarith

private theorem tendsto_log_momentNormalized_diagonalKernel_div
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    (x : Space n)
    (hmax : ∀ z : Space n,
      phase u (momentNormalizedPotential F) z ≤
        phase u (momentNormalizedPotential F) x) :
    Tendsto
      (fun k : ℕ =>
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) x) / (k : ℝ))
      atTop (𝓝 (momentNormalizedPotential F x)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hupper :=
    eventually_log_momentNormalized_diagonalKernel_div_le_add
      K F htransport hhalf
  have hlower :=
    eventually_log_momentNormalized_diagonalKernel_div_ge_sub
      K F htransport hu x hmax hhalf
  have hclose :
      ∀ᶠ k : ℕ in atTop,
        dist
          (Real.log
            (diagonalKernel K k
              (momentNormalizedPotential F) x) / (k : ℝ))
          (momentNormalizedPotential F x) < ε := by
    filter_upwards [hupper, hlower]
      with k hupperk hlowerk
    rw [Real.dist_eq]
    apply abs_lt.mpr
    constructor
    · linarith
    · linarith [hupperk x]
  exact Filter.eventually_atTop.mp hclose

end BergmanJetPointwiseLogKernel

namespace WeightedTorusDistributionBridge

open Set Function MeasureTheory Filter
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution

local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private def unweightedTorusMeasure (n : ℕ) :
    Measure (WeightedTorusHilbert.LogTorus n) :=
  (volume : Measure (Space n)).prod
    (WeightedTorusHilbert.angularMeasure n)

private theorem radialWeight_pos {n k : ℕ}
    (φ : Space n → ℝ) (x : Space n) :
    0 < WeightedTorusHilbert.radialWeight k φ x := by
  unfold WeightedTorusHilbert.radialWeight
  exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)

private theorem radialWeight_lt_top {n k : ℕ}
    (φ : Space n → ℝ) (x : Space n) :
    WeightedTorusHilbert.radialWeight k φ x < ⊤ := by
  unfold WeightedTorusHilbert.radialWeight
  exact ENNReal.ofReal_lt_top

private theorem weightedTorusMeasure_eq_unweighted_withDensity {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ) :
    WeightedTorusHilbert.weightedTorusMeasure k φ =
      (unweightedTorusMeasure n).withDensity
        (fun z : WeightedTorusHilbert.LogTorus n =>
          WeightedTorusHilbert.radialWeight k φ z.1) := by
  exact WeightedTorusHilbert.weightedTorusMeasure_eq_withDensity
    k hφ

private theorem continuous_realRadialWeight {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ) :
    Continuous
      (fun z : WeightedTorusHilbert.LogTorus n =>
        Real.exp (-(k : ℝ) * φ z.1)) :=
  Real.continuous_exp.comp
    (continuous_const.mul (hφ.comp continuous_fst))

private theorem unweightedTorusMeasure_isLocallyFinite (n : ℕ) :
    IsLocallyFiniteMeasure (unweightedTorusMeasure n) := by
  unfold unweightedTorusMeasure
  infer_instance

private theorem weightedTorusMeasure_isLocallyFinite {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ) :
    IsLocallyFiniteMeasure
      (WeightedTorusHilbert.weightedTorusMeasure k φ) := by
  let : IsLocallyFiniteMeasure (unweightedTorusMeasure n) :=
    unweightedTorusMeasure_isLocallyFinite n
  rw [weightedTorusMeasure_eq_unweighted_withDensity hφ]
  exact IsLocallyFiniteMeasure.withDensity_ofReal
    (continuous_realRadialWeight hφ)

private theorem weightedScalarL2_locallyIntegrable_weighted {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (f : WeightedTorusHilbert.weightedHilbert k φ) :
    LocallyIntegrable
      (fun z : WeightedTorusHilbert.LogTorus n => f z)
      (WeightedTorusHilbert.weightedTorusMeasure k φ) := by
  let : IsLocallyFiniteMeasure
      (WeightedTorusHilbert.weightedTorusMeasure k φ) :=
    weightedTorusMeasure_isLocallyFinite hφ
  exact (MeasureTheory.Lp.memLp f).locallyIntegrable (by norm_num)

private theorem weightedScalarL2_locallyIntegrable_unweighted {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (f : WeightedTorusHilbert.weightedHilbert k φ) :
    LocallyIntegrable
      (fun z : WeightedTorusHilbert.LogTorus n => f z)
      (unweightedTorusMeasure n) := by
  let g : WeightedTorusHilbert.LogTorus n → ℂ :=
    fun z => f z
  change LocallyIntegrable g (unweightedTorusMeasure n)
  apply locallyIntegrable_iff.mpr
  intro K hK
  have hweighted : IntegrableOn g K
      (WeightedTorusHilbert.weightedTorusMeasure k φ) := by
    exact (weightedScalarL2_locallyIntegrable_weighted hφ f).integrableOn_isCompact hK
  rw [weightedTorusMeasure_eq_unweighted_withDensity hφ] at hweighted
  change Integrable
    g
    (((unweightedTorusMeasure n).withDensity
      (fun z : WeightedTorusHilbert.LogTorus n =>
        WeightedTorusHilbert.radialWeight k φ z.1)).restrict K)
    at hweighted
  rw [restrict_withDensity hK.isClosed.measurableSet] at hweighted
  have hdmeas : Measurable
      (fun z : WeightedTorusHilbert.LogTorus n =>
        WeightedTorusHilbert.radialWeight k φ z.1) :=
    (WeightedTorusHilbert.radialWeight_measurable k hφ).comp
      measurable_fst
  have hdfinite :
      ∀ᵐ z : WeightedTorusHilbert.LogTorus n
        ∂((unweightedTorusMeasure n).restrict K),
        WeightedTorusHilbert.radialWeight k φ z.1 < ⊤ :=
    Filter.Eventually.of_forall (fun z => radialWeight_lt_top φ z.1)
  have hscaled :=
    (integrable_withDensity_iff_integrable_smul'
      hdmeas hdfinite).mp hweighted
  have hexp : IntegrableOn
      (fun z : WeightedTorusHilbert.LogTorus n =>
        (Real.exp (-(k : ℝ) * φ z.1) : ℂ) * g z)
      K (unweightedTorusMeasure n) := by
    apply hscaled.congr
    filter_upwards [] with z
    simp only [WeightedTorusHilbert.radialWeight, neg_mul, (Real.exp_pos _).le,
      ENNReal.toReal_ofReal,
      Complex.real_smul, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_natCast]
  have hreciprocal : Continuous
      (fun z : WeightedTorusHilbert.LogTorus n =>
        (Real.exp ((k : ℝ) * φ z.1) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp
        (continuous_const.mul (hφ.comp continuous_fst)))
  have hproduct := hexp.mul_continuousOn
    hreciprocal.continuousOn hK
  refine hproduct.congr_fun ?_ hK.isClosed.measurableSet
  intro z hz
  have hcancel :
      (Real.exp (-(k : ℝ) * φ z.1) : ℂ) *
        (Real.exp ((k : ℝ) * φ z.1) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    have ha : -(k : ℝ) * φ z.1 + (k : ℝ) * φ z.1 = 0 := by ring
    rw [ha]
    simp only [Real.exp_zero, Complex.ofReal_one]
  calc
    ((Real.exp (-(k : ℝ) * φ z.1) : ℂ) * g z) *
        (Real.exp ((k : ℝ) * φ z.1) : ℂ) =
      ((Real.exp (-(k : ℝ) * φ z.1) : ℂ) *
        (Real.exp ((k : ℝ) * φ z.1) : ℂ)) * g z := by ring
    _ = g z := by rw [hcancel, one_mul]

private abbrev angularFundamentalCell (n : ℕ) :=
  {t : Space n // ∀ i : Fin n,
    t i ∈ Set.Ioc (0 : ℝ) ((0 : ℝ) + 1)}

private def angularFundamentalMeasure (n : ℕ) :
    Measure (angularFundamentalCell n) :=
  (volume : Measure (Space n)).comap Subtype.val

private def angularFundamentalEquiv (n : ℕ) :
    TorusCharacters.AngularTorus n ≃ᵐ
      angularFundamentalCell n :=
  UnitAddTorus.measurableEquivPiIoc (fun _ : Fin n => 0)

private theorem angularFundamentalEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (angularFundamentalEquiv n)
      (WeightedTorusHilbert.angularMeasure n)
      (angularFundamentalMeasure n) := by
  simpa only [angularFundamentalEquiv, WeightedTorusHilbert.angularMeasure,
    angularFundamentalMeasure] using
    (UnitAddTorus.measurePreserving_equivPiIoc
      (fun _ : Fin n => (0 : ℝ)))

private def torusFundamentalMeasurableEquiv (n : ℕ) :
    WeightedTorusHilbert.LogTorus n ≃ᵐ
      Space n × angularFundamentalCell n :=
  MeasurableEquiv.prodCongr
    (MeasurableEquiv.refl (Space n))
    (angularFundamentalEquiv n)

private def unweightedFundamentalMeasure (n : ℕ) :
    Measure (Space n × angularFundamentalCell n) :=
  (volume : Measure (Space n)).prod
    (angularFundamentalMeasure n)

private theorem unweightedTorusFundamental_measurePreserving (n : ℕ) :
    MeasurePreserving (torusFundamentalMeasurableEquiv n)
      (unweightedTorusMeasure n)
      (unweightedFundamentalMeasure n) := by
  change MeasurePreserving
    (Prod.map id (angularFundamentalEquiv n))
    ((volume : Measure (Space n)).prod
      (WeightedTorusHilbert.angularMeasure n))
    ((volume : Measure (Space n)).prod
      (angularFundamentalMeasure n))
  exact (MeasurePreserving.id
    (volume : Measure (Space n))).prod
      (angularFundamentalEquiv_measurePreserving n)

private theorem angularFundamentalEquiv_symm_apply {n : ℕ}
    (t : angularFundamentalCell n) :
    (angularFundamentalEquiv n).symm t =
      (fun i : Fin n => (t.1 i : UnitAddCircle)) := by
  rfl

private theorem coverRepresentative_fundamentalCell {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (x : Space n)
    (t : angularFundamentalCell n) :
    JointHolomorphicLaurentFourierCompatibility.coverRepresentative
      F x ((angularFundamentalEquiv n).symm t) =
      F (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t.1) := by
  rw [angularFundamentalEquiv_symm_apply]
  apply JointHolomorphicLaurentFourierCompatibility.coverRepresentative_coe
  intro i hi
  simpa only [mem_Ioc, zero_add] using t.property i

private def logarithmicCoordinatesEquiv (n : ℕ) :
    (Space n × Space n) ≃L[ℝ]
      TorusCharacters.LogSpace n where
  toFun p :=
    JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
      p.1 p.2
  invFun z :=
    (fun i => 2 * (z i).re,
     fun i => (z i).im / (2 * Real.pi))
  left_inv := by
    intro p
    apply Prod.ext
    · funext i
      simp only [JointHolomorphicLaurentFourierCompatibility.logarithmicPoint, Complex.add_re,
        Complex.div_ofNat_re, Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat,
        Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero, Complex.I_re, Complex.mul_im,
        zero_mul, add_zero, Complex.I_im, mul_one, sub_self]
      ring
    · funext i
      simp only [JointHolomorphicLaurentFourierCompatibility.logarithmicPoint, Complex.add_im,
        Complex.div_ofNat_im, Complex.ofReal_im, zero_div, Complex.mul_im, Complex.mul_re,
        Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat, mul_zero, sub_zero, Complex.I_re,
        zero_mul, add_zero, Complex.I_im, mul_one, sub_self, zero_add, ne_eq, mul_eq_zero,
        OfNat.ofNat_ne_zero, Real.pi_ne_zero, or_self, not_false_eq_true, mul_div_cancel_left₀]
  right_inv := by
    intro z
    funext i
    apply Complex.ext
    · simp only [JointHolomorphicLaurentFourierCompatibility.logarithmicPoint, Complex.add_re,
        Complex.div_ofNat_re, Complex.ofReal_re, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        mul_div_cancel_left₀, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
        Complex.ofReal_im, mul_zero, sub_zero, Complex.I_re, Complex.mul_im, zero_mul, add_zero,
        Complex.I_im, mul_one, sub_self]
    · simp only [JointHolomorphicLaurentFourierCompatibility.logarithmicPoint, Complex.add_im,
        Complex.div_ofNat_im, Complex.ofReal_im, zero_div, Complex.mul_im, Complex.mul_re,
        Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat, mul_zero, sub_zero, Complex.I_re,
        zero_mul, add_zero, Complex.I_im, mul_one, sub_self, zero_add]
      field_simp [Real.pi_ne_zero]
  map_add' := by
    intro p q
    funext i
    simp only [JointHolomorphicLaurentFourierCompatibility.logarithmicPoint, Prod.fst_add,
      Pi.add_apply, Complex.ofReal_add, Prod.snd_add]
    ring
  map_smul' := by
    intro c p
    funext i
    simp only [JointHolomorphicLaurentFourierCompatibility.logarithmicPoint, Prod.smul_fst,
      Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Prod.smul_snd, Real.ringHom_apply, smul_add,
      Complex.real_smul]
    ring
  continuous_toFun := by
    apply continuous_pi
    intro i
    change Continuous
      (fun p : Space n × Space n =>
        (p.1 i : ℂ) / 2 +
          (2 * (Real.pi : ℂ) * Complex.I) * (p.2 i : ℂ))
    fun_prop
  continuous_invFun := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro i
      fun_prop
    · apply continuous_pi
      intro i
      fun_prop

@[simp] private theorem logarithmicCoordinatesEquiv_apply {n : ℕ}
    (x t : Space n) :
    logarithmicCoordinatesEquiv n (x, t) =
      JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t := rfl

private def logarithmicCoverPushforward (n : ℕ) :
    Measure (TorusCharacters.LogSpace n) :=
  (volume : Measure (Space n × Space n)).map
    (logarithmicCoordinatesEquiv n)

private theorem logarithmicCoverPushforward_isAddHaar (n : ℕ) :
    (logarithmicCoverPushforward n).IsAddHaarMeasure := by
  let :
      (volume : Measure (Space n × Space n)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    exact Measure.prod.instIsAddHaarMeasure _ _
  unfold logarithmicCoverPushforward
  exact (logarithmicCoordinatesEquiv n).isAddHaarMeasure_map
    (volume : Measure (Space n × Space n))

private def logarithmicCoverJacobianFactor (n : ℕ) : NNReal := by
  letI : (logarithmicCoverPushforward n).IsAddHaarMeasure :=
    logarithmicCoverPushforward_isAddHaar n
  exact (logarithmicCoverPushforward n).addHaarScalarFactor
    (volume : Measure (TorusCharacters.LogSpace n))

private theorem logarithmicCoverJacobianFactor_pos (n : ℕ) :
    0 < logarithmicCoverJacobianFactor n := by
  let : (logarithmicCoverPushforward n).IsAddHaarMeasure :=
    logarithmicCoverPushforward_isAddHaar n
  exact Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
    (logarithmicCoverPushforward n)
    (volume : Measure (TorusCharacters.LogSpace n))

private theorem logarithmicCoverPushforward_eq_smul_volume (n : ℕ) :
    logarithmicCoverPushforward n =
      logarithmicCoverJacobianFactor n •
        (volume : Measure (TorusCharacters.LogSpace n)) := by
  let : (logarithmicCoverPushforward n).IsAddHaarMeasure :=
    logarithmicCoverPushforward_isAddHaar n
  exact Measure.isAddLeftInvariant_eq_smul
    (logarithmicCoverPushforward n)
    (volume : Measure (TorusCharacters.LogSpace n))

private theorem logarithmicCoordinates_measurePreserving (n : ℕ) :
    MeasurePreserving (logarithmicCoordinatesEquiv n)
      (volume : Measure (Space n × Space n))
      (logarithmicCoverPushforward n) := by
  exact (logarithmicCoordinatesEquiv n).toHomeomorph.measurable.measurePreserving
      (volume : Measure (Space n × Space n))

private theorem integral_logarithmicCoordinates_eq_pushforward {n : ℕ}
    (g : TorusCharacters.LogSpace n → ℂ) :
    (∫ p : Space n × Space n,
      g (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        p.1 p.2)
      ∂(volume : Measure (Space n × Space n))) =
      ∫ z : TorusCharacters.LogSpace n, g z
        ∂(logarithmicCoverPushforward n) := by
  calc
    (∫ p : Space n × Space n,
      g (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        p.1 p.2)
      ∂(volume : Measure (Space n × Space n))) =
        ∫ p : Space n × Space n,
          g (logarithmicCoordinatesEquiv n p)
          ∂(volume : Measure (Space n × Space n)) := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun p =>
        congrArg g (logarithmicCoordinatesEquiv_apply p.1 p.2).symm
    _ = _ :=
      (logarithmicCoordinates_measurePreserving n).integral_comp
        (logarithmicCoordinatesEquiv n).toHomeomorph.measurableEmbedding g

private theorem integral_logarithmicCoordinates_eq_jacobian {n : ℕ}
    (g : TorusCharacters.LogSpace n → ℂ) :
    (∫ p : Space n × Space n,
      g (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        p.1 p.2)
      ∂(volume : Measure (Space n × Space n))) =
      logarithmicCoverJacobianFactor n •
        (∫ z : TorusCharacters.LogSpace n, g z
          ∂(volume : Measure (TorusCharacters.LogSpace n))) := by
  rw [integral_logarithmicCoordinates_eq_pushforward,
    logarithmicCoverPushforward_eq_smul_volume,
    integral_smul_nnreal_measure]

private def angularFundamentalBox {n : ℕ} (b : Space n) :
    Set (Space n) :=
  {t | ∀ i : Fin n, t i ∈ Set.Ioc (b i) (b i + 1)}

private def angularCoverProjection (n : ℕ) :
    Space n → TorusCharacters.AngularTorus n :=
  fun t i => (t i : UnitAddCircle)

private theorem angularCoverProjection_integer_add {n : ℕ}
    (t : Space n) (q : Fin n → ℤ) :
    angularCoverProjection n (fun i => t i + (q i : ℝ)) =
      angularCoverProjection n t := by
  funext i
  change ((t i + (q i : ℝ) : ℝ) : UnitAddCircle) =
    (t i : UnitAddCircle)
  rw [AddCircle.coe_add]
  have hq : (((q i : ℝ) : UnitAddCircle) = 0) := by
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨q i, by simp only [zsmul_eq_mul, mul_one]⟩
  rw [hq, add_zero]

private theorem angularCoverProjection_measurePreserving {n : ℕ}
    (b : Space n) :
    MeasurePreserving (angularCoverProjection n)
      ((volume : Measure (Space n)).restrict
        (angularFundamentalBox b))
      (WeightedTorusHilbert.angularMeasure n) := by
  have hb : MeasurableSet (angularFundamentalBox b) := by
    unfold angularFundamentalBox
    exact MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)
  have hp : Measurable (angularCoverProjection n) := by
    apply measurable_pi_lambda
    intro i
    exact AddCircle.measurable_mk'.comp (measurable_pi_apply i)
  refine ⟨hp, ?_⟩
  rw [← map_comap_subtype_coe hb (volume : Measure (Space n)),
    Measure.map_map hp measurable_subtype_coe]
  change
    Measure.map
      (UnitAddTorus.measurableEquivPiIoc b).symm
      ((volume : Measure (Space n)).comap
        (Subtype.val : angularFundamentalBox b → Space n)) =
      WeightedTorusHilbert.angularMeasure n
  change
    Measure.map
      (UnitAddTorus.measurableEquivPiIoc b).symm
      ((volume : Measure (Space n)).comap
        (Subtype.val : angularFundamentalBox b → Space n)) =
      (volume : Measure (TorusCharacters.AngularTorus n))
  exact ((UnitAddTorus.measurePreserving_equivPiIoc b).symm
    (UnitAddTorus.measurableEquivPiIoc b)).map_eq

private def realTorusCoverProjection (n : ℕ) :
    Space n × Space n →
      WeightedTorusHilbert.LogTorus n :=
  fun p => (p.1, angularCoverProjection n p.2)

private theorem realTorusCoverProjection_measurePreserving {n : ℕ}
    (μ : Measure (Space n)) [SFinite μ]
    (b : Space n) :
    MeasurePreserving (realTorusCoverProjection n)
      (μ.prod
        ((volume : Measure (Space n)).restrict
          (angularFundamentalBox b)))
      (μ.prod (WeightedTorusHilbert.angularMeasure n)) := by
  change MeasurePreserving
    (Prod.map id (angularCoverProjection n))
    (μ.prod
      ((volume : Measure (Space n)).restrict
        (angularFundamentalBox b)))
    (μ.prod (WeightedTorusHilbert.angularMeasure n))
  exact (MeasurePreserving.id μ).prod
    (angularCoverProjection_measurePreserving b)

private theorem weightedRealTorusCoverProjection_measurePreserving {n k : ℕ}
    (φ : Space n → ℝ) (b : Space n) :
    MeasurePreserving (realTorusCoverProjection n)
      ((WeightedTorusHilbert.radialMeasure k φ).prod
        ((volume : Measure (Space n)).restrict
          (angularFundamentalBox b)))
      (WeightedTorusHilbert.weightedTorusMeasure k φ) := by
  simpa only [WeightedTorusHilbert.weightedTorusMeasure] using
    realTorusCoverProjection_measurePreserving
      (WeightedTorusHilbert.radialMeasure k φ) b

private def realTorusCoverLift {n : ℕ}
    (g : WeightedTorusHilbert.LogTorus n → ℂ) :
    Space n × Space n → ℂ :=
  fun p => g (realTorusCoverProjection n p)

private theorem realTorusCoverLift_integrableOn_fundamental {n : ℕ}
    {g : WeightedTorusHilbert.LogTorus n → ℂ}
    (hg : LocallyIntegrable g (unweightedTorusMeasure n))
    {s : Set (Space n)} (hs : IsCompact s)
    (b : Space n) :
    IntegrableOn (realTorusCoverLift g)
      (s ×ˢ angularFundamentalBox b)
      (volume : Measure (Space n × Space n)) := by
  have htorus : IntegrableOn g
      (s ×ˢ (Set.univ : Set (TorusCharacters.AngularTorus n)))
      (unweightedTorusMeasure n) :=
    hg.integrableOn_isCompact (hs.prod isCompact_univ)
  have hradial : Integrable g
      (((volume : Measure (Space n)).restrict s).prod
        (WeightedTorusHilbert.angularMeasure n)) := by
    simpa only [Measure.restrict_prod_eq_prod_univ, IntegrableOn, unweightedTorusMeasure] using
      htorus
  have hlift :=
    (realTorusCoverProjection_measurePreserving
      ((volume : Measure (Space n)).restrict s) b).integrable_comp_of_integrable
        hradial
  change Integrable (realTorusCoverLift g)
    (((volume : Measure (Space n)).prod
      (volume : Measure (Space n))).restrict
        (s ×ˢ angularFundamentalBox b))
  rw [← Measure.prod_restrict]
  change Integrable (g ∘ realTorusCoverProjection n)
    (((volume : Measure (Space n)).restrict s).prod
      ((volume : Measure (Space n)).restrict
        (angularFundamentalBox b)))
  exact hlift

private theorem angularFundamentalBox_mem_nhds {n : ℕ}
    (t : Space n) :
    angularFundamentalBox
        (fun i : Fin n => t i - (1 / 2 : ℝ)) ∈ 𝓝 t := by
  have h :
      Set.univ.pi
        (fun i : Fin n =>
          Set.Ioc (t i - (1 / 2 : ℝ))
            (t i - (1 / 2 : ℝ) + 1)) ∈ 𝓝 t := by
    apply set_pi_mem_nhds Set.finite_univ
    intro i _
    apply Ioc_mem_nhds <;> linarith
  simpa only [angularFundamentalBox, one_div, mem_Ioc, Set.pi, mem_univ, forall_const] using h

private theorem realTorusCoverLift_locallyIntegrable {n : ℕ}
    {g : WeightedTorusHilbert.LogTorus n → ℂ}
    (hg : LocallyIntegrable g (unweightedTorusMeasure n)) :
    LocallyIntegrable (realTorusCoverLift g)
      (volume : Measure (Space n × Space n)) := by
  intro p
  refine ⟨Metric.closedBall p.1 1 ×ˢ
    angularFundamentalBox
      (fun i : Fin n => p.2 i - (1 / 2 : ℝ)), ?_, ?_⟩
  · exact prod_mem_nhds
      (Metric.closedBall_mem_nhds p.1 (by norm_num))
      (angularFundamentalBox_mem_nhds p.2)
  · exact realTorusCoverLift_integrableOn_fundamental hg
      (isCompact_closedBall p.1 1)
      (fun i : Fin n => p.2 i - (1 / 2 : ℝ))

private def complexTorusCoverProjection (n : ℕ) :
    TorusCharacters.LogSpace n →
      WeightedTorusHilbert.LogTorus n :=
  fun z => realTorusCoverProjection n
    ((logarithmicCoordinatesEquiv n).symm z)

@[simp] private theorem complexTorusCoverProjection_logarithmicPoint {n : ℕ}
    (x t : Space n) :
    complexTorusCoverProjection n
      (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t) =
      realTorusCoverProjection n (x, t) := by
  change
    realTorusCoverProjection n
      ((logarithmicCoordinatesEquiv n).symm
        (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
          x t)) =
      realTorusCoverProjection n (x, t)
  rw [← logarithmicCoordinatesEquiv_apply,
    ContinuousLinearEquiv.symm_apply_apply]

private theorem logarithmicPoint_integer_add {n : ℕ}
    (x t : Space n) (q : Fin n → ℤ) :
    JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
      x (fun i => t i + (q i : ℝ)) =
      JointHolomorphicLaurentFourierCompatibility.logarithmicPoint x t +
        TorusCharacters.imaginaryShift q := by
  funext i
  simp only [JointHolomorphicLaurentFourierCompatibility.logarithmicPoint,
    TorusCharacters.imaginaryShift, Pi.add_apply,
    Complex.ofReal_add, Complex.ofReal_intCast]
  ring

private theorem complexTorusCoverProjection_imaginaryShift {n : ℕ}
    (z : TorusCharacters.LogSpace n)
    (q : Fin n → ℤ) :
    complexTorusCoverProjection n
      (z + TorusCharacters.imaginaryShift q) =
      complexTorusCoverProjection n z := by
  let p : Space n × Space n :=
    (logarithmicCoordinatesEquiv n).symm z
  have hz :
      JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        p.1 p.2 = z := by
    change (logarithmicCoordinatesEquiv n) p = z
    exact (logarithmicCoordinatesEquiv n).apply_symm_apply z
  rw [← hz, ← logarithmicPoint_integer_add,
    complexTorusCoverProjection_logarithmicPoint,
    complexTorusCoverProjection_logarithmicPoint]
  change
    (p.1, angularCoverProjection n (fun i => p.2 i + (q i : ℝ))) =
      (p.1, angularCoverProjection n p.2)
  rw [angularCoverProjection_integer_add]

private def complexTorusCoverLift {n : ℕ}
    (g : WeightedTorusHilbert.LogTorus n → ℂ) :
    TorusCharacters.LogSpace n → ℂ :=
  fun z => g (complexTorusCoverProjection n z)

private theorem complexTorusCoverLift_periodic {n : ℕ}
    (g : WeightedTorusHilbert.LogTorus n → ℂ)
    (q : Fin n → ℤ) :
    Function.Periodic (complexTorusCoverLift g)
      (TorusCharacters.imaginaryShift q) := by
  intro z
  unfold complexTorusCoverLift
  rw [complexTorusCoverProjection_imaginaryShift]

@[simp] private theorem complexTorusCoverLift_logarithmicPoint {n : ℕ}
    (g : WeightedTorusHilbert.LogTorus n → ℂ)
    (x t : Space n) :
    complexTorusCoverLift g
      (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t) =
      realTorusCoverLift g (x, t) := by
  change
    g (realTorusCoverProjection n
      ((logarithmicCoordinatesEquiv n).symm
        (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
          x t))) =
      g (realTorusCoverProjection n (x, t))
  rw [← logarithmicCoordinatesEquiv_apply,
    ContinuousLinearEquiv.symm_apply_apply]

private theorem locallyIntegrable_logarithmicCoverPushforward_iff {n : ℕ}
    (g : TorusCharacters.LogSpace n → ℂ) :
    LocallyIntegrable g (logarithmicCoverPushforward n) ↔
      LocallyIntegrable g
        (volume : Measure (TorusCharacters.LogSpace n)) := by
  rw [logarithmicCoverPushforward_eq_smul_volume]
  constructor
  · intro hg z
    obtain ⟨s, hs, hg⟩ := hg z
    refine ⟨s, hs, ?_⟩
    have hc :
        (logarithmicCoverJacobianFactor n : ℝ≥0∞) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr
        (logarithmicCoverJacobianFactor_pos n).ne'
    exact (integrable_smul_measure hc ENNReal.coe_ne_top).mp
      (by simpa only [Measure.coe_nnreal_smul, IntegrableOn, Measure.restrict_smul] using hg)
  · intro hg z
    obtain ⟨s, hs, hg⟩ := hg z
    refine ⟨s, hs, ?_⟩
    have hc :
        (logarithmicCoverJacobianFactor n : ℝ≥0∞) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr
        (logarithmicCoverJacobianFactor_pos n).ne'
    simpa only [IntegrableOn, Measure.restrict_smul, Measure.coe_nnreal_smul] using
      (integrable_smul_measure hc ENNReal.coe_ne_top).mpr hg

private theorem complexTorusCoverLift_locallyIntegrable {n : ℕ}
    {g : WeightedTorusHilbert.LogTorus n → ℂ}
    (hg : LocallyIntegrable g (unweightedTorusMeasure n)) :
    LocallyIntegrable (complexTorusCoverLift g)
      (volume : Measure (TorusCharacters.LogSpace n)) := by
  apply (locallyIntegrable_logarithmicCoverPushforward_iff _).mp
  apply (locallyIntegrable_map_homeomorph
    (logarithmicCoordinatesEquiv n).toHomeomorph).mpr
  refine (realTorusCoverLift_locallyIntegrable hg).congr
    (Filter.Eventually.of_forall fun p => ?_)
  simp only [realTorusCoverLift, ContinuousLinearEquiv.coe_toHomeomorph, comp_apply,
    complexTorusCoverLift, complexTorusCoverProjection, ContinuousLinearEquiv.symm_apply_apply]

private theorem weightedScalarL2_complexTorusCoverLift_locallyIntegrable
    {n k : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    (f : WeightedTorusHilbert.weightedHilbert k φ) :
    LocallyIntegrable
      (complexTorusCoverLift
        (fun z : WeightedTorusHilbert.LogTorus n => f z))
      (volume : Measure (TorusCharacters.LogSpace n)) :=
  complexTorusCoverLift_locallyIntegrable
    (weightedScalarL2_locallyIntegrable_unweighted hφ f)

end WeightedTorusDistributionBridge

namespace WeightedTorusGraphWeakBridge

open Set Function MeasureTheory Filter
open EqualitySaturatingKillingPaths ComplexKillingSaturationBridge DolbeaultGraphDistributionBridge
open WeightedTorusDistributionBridge
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution

private theorem weightedTorus_ae_iff_unweighted {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (P : WeightedTorusHilbert.LogTorus n → Prop) :
    (∀ᵐ z ∂(WeightedTorusHilbert.weightedTorusMeasure k φ), P z) ↔
      ∀ᵐ z ∂(unweightedTorusMeasure n), P z := by
  rw [weightedTorusMeasure_eq_unweighted_withDensity hφ]
  have hd : Measurable
      (fun z : WeightedTorusHilbert.LogTorus n =>
        WeightedTorusHilbert.radialWeight k φ z.1) :=
    (WeightedTorusHilbert.radialWeight_measurable k hφ).comp
      measurable_fst
  rw [ae_withDensity_iff hd]
  constructor
  · intro h
    filter_upwards [h] with z hz
    exact hz (radialWeight_pos φ z.1).ne'
  · intro h
    filter_upwards [h] with z hz _
    exact hz

private theorem weightedTorus_ae_eq_unweighted {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {f g : WeightedTorusHilbert.LogTorus n → ℂ}
    (h : f =ᵐ[WeightedTorusHilbert.weightedTorusMeasure k φ] g) :
    f =ᵐ[unweightedTorusMeasure n] g :=
  (weightedTorus_ae_iff_unweighted hφ (fun z => f z = g z)).mp h

private theorem unweightedTorus_ae_eq_weighted {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {f g : WeightedTorusHilbert.LogTorus n → ℂ}
    (h : f =ᵐ[unweightedTorusMeasure n] g) :
    f =ᵐ[WeightedTorusHilbert.weightedTorusMeasure k φ] g :=
  (weightedTorus_ae_iff_unweighted hφ (fun z => f z = g z)).mpr h

private theorem exists_integer_angularFundamentalBox {n : ℕ}
    (t : Space n) :
    ∃ q : Fin n → ℤ,
      t ∈ angularFundamentalBox (fun i => (q i : ℝ)) := by
  refine ⟨fun i => ⌈t i⌉ - 1, ?_⟩
  intro i
  constructor
  · push_cast
    have h := Int.ceil_lt_add_one (t i)
    linarith
  · push_cast
    have h := Int.le_ceil (t i)
    linarith

private theorem integer_angularFundamentalBoxes_cover (n : ℕ) :
    (⋃ q : Fin n → ℤ,
      (Set.univ : Set (Space n)) ×ˢ
        angularFundamentalBox (fun i => (q i : ℝ))) =
      (Set.univ : Set (Space n × Space n)) := by
  apply Set.iUnion_eq_univ_iff.mpr
  intro p
  obtain ⟨q, hq⟩ := exists_integer_angularFundamentalBox p.2
  exact ⟨q, ⟨Set.mem_univ p.1, hq⟩⟩

private theorem realTorusCoverLift_ae_eq_fundamental {n : ℕ}
    {f g : WeightedTorusHilbert.LogTorus n → ℂ}
    (h : f =ᵐ[unweightedTorusMeasure n] g)
    (q : Fin n → ℤ) :
    realTorusCoverLift f =ᵐ[
      (volume : Measure (Space n × Space n)).restrict
        ((Set.univ : Set (Space n)) ×ˢ
          angularFundamentalBox (fun i => (q i : ℝ)))]
      realTorusCoverLift g := by
  have hp :=
    (realTorusCoverProjection_measurePreserving
      (volume : Measure (Space n))
      (fun i => (q i : ℝ))).quasiMeasurePreserving.ae_eq_comp h
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  simp only [Measure.restrict_univ]
  filter_upwards [hp] with x hx
  change f (realTorusCoverProjection n x) =
    g (realTorusCoverProjection n x)
  exact hx

private theorem realTorusCoverLift_ae_eq {n : ℕ}
    {f g : WeightedTorusHilbert.LogTorus n → ℂ}
    (h : f =ᵐ[unweightedTorusMeasure n] g) :
    realTorusCoverLift f =ᵐ[
      (volume : Measure (Space n × Space n))]
      realTorusCoverLift g := by
  have hc :=
    (ae_eq_restrict_iUnion_iff
      (μ := (volume : Measure (Space n × Space n)))
      (fun q : Fin n → ℤ =>
        (Set.univ : Set (Space n)) ×ˢ
          angularFundamentalBox (fun i => (q i : ℝ)))
      (realTorusCoverLift f) (realTorusCoverLift g)).mpr
        (fun q => realTorusCoverLift_ae_eq_fundamental h q)
  simpa only [integer_angularFundamentalBoxes_cover, Measure.restrict_univ] using hc

private theorem complexTorusCoverLift_ae_eq {n : ℕ}
    {f g : WeightedTorusHilbert.LogTorus n → ℂ}
    (h : f =ᵐ[unweightedTorusMeasure n] g) :
    complexTorusCoverLift f =ᵐ[
      (volume : Measure (TorusCharacters.LogSpace n))]
      complexTorusCoverLift g := by
  have hr := realTorusCoverLift_ae_eq h
  have hp :=
    ((logarithmicCoordinates_measurePreserving n).symm
      (logarithmicCoordinatesEquiv
        n).toHomeomorph.toMeasurableEquiv).quasiMeasurePreserving.ae_eq_comp
        hr
  change
    (fun z : TorusCharacters.LogSpace n =>
      realTorusCoverLift f ((logarithmicCoordinatesEquiv n).symm z)) =ᵐ[
        logarithmicCoverPushforward n]
      (fun z : TorusCharacters.LogSpace n =>
        realTorusCoverLift g ((logarithmicCoordinatesEquiv n).symm z))
    at hp
  rw [logarithmicCoverPushforward_eq_smul_volume] at hp
  have hc : logarithmicCoverJacobianFactor n ≠ 0 :=
    (logarithmicCoverJacobianFactor_pos n).ne'
  have hv := (Measure.ae_smul_measure_iff hc).mp hp
  filter_upwards [hv] with z hz
  change
    f (realTorusCoverProjection n
      ((logarithmicCoordinatesEquiv n).symm z)) =
    g (realTorusCoverProjection n
      ((logarithmicCoordinatesEquiv n).symm z))
  exact hz

private theorem weightedTorus_complexCoverLift_ae_eq {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {f g : WeightedTorusHilbert.LogTorus n → ℂ}
    (h : f =ᵐ[WeightedTorusHilbert.weightedTorusMeasure k φ] g) :
    complexTorusCoverLift f =ᵐ[
      (volume : Measure (TorusCharacters.LogSpace n))]
      complexTorusCoverLift g :=
  complexTorusCoverLift_ae_eq (weightedTorus_ae_eq_unweighted hφ h)

private theorem exists_integer_translate_of_angularCoverProjection_eq
    {n : ℕ} {s t : Space n}
    (h : angularCoverProjection n s = angularCoverProjection n t) :
    ∃ q : Fin n → ℤ, s = fun i => t i + (q i : ℝ) := by
  have hi : ∀ i : Fin n,
      ∃ q : ℤ, s i = t i + (q : ℝ) := by
    intro i
    have he : ((s i : ℝ) : UnitAddCircle) =
        ((t i : ℝ) : UnitAddCircle) := congrFun h i
    have hz : (((s i - t i : ℝ) : UnitAddCircle) = 0) := by
      rw [AddCircle.coe_sub]
      exact sub_eq_zero.mpr he
    obtain ⟨q, hq⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
    refine ⟨q, ?_⟩
    have hq' : (q : ℝ) = s i - t i := by
      simpa only [zsmul_eq_mul, mul_one] using hq
    linarith
  choose q hq using hi
  exact ⟨q, funext hq⟩

private theorem angularCoverProjection_fundamentalRepresentative
    {n : ℕ} (t : Space n) :
    angularCoverProjection n
      (fun i : Fin n =>
        (AddCircle.equivIoc 1 0 ((t i : ℝ) : UnitAddCircle)).1) =
      angularCoverProjection n t := by
  funext i
  change
    (((AddCircle.equivIoc 1 0
      ((t i : ℝ) : UnitAddCircle)).1 : ℝ) : UnitAddCircle) =
      (t i : UnitAddCircle)
  exact (AddCircle.equivIoc 1 0).symm_apply_apply
    ((t i : ℝ) : UnitAddCircle)

private theorem periodic_torusScalarRepresentative_logarithmicPoint {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (x t : Space n) :
    torusScalarRepresentative F
      (x, angularCoverProjection n t) =
      F (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t) := by
  let u : Space n := fun i =>
    (AddCircle.equivIoc 1 0 ((t i : ℝ) : UnitAddCircle)).1
  obtain ⟨q, hq⟩ := exists_integer_translate_of_angularCoverProjection_eq
    (angularCoverProjection_fundamentalRepresentative t)
  change
    F (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
      x u) =
      F (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t)
  change u = (fun i => t i + (q i : ℝ)) at hq
  rw [hq, logarithmicPoint_integer_add]
  exact hperiod q _

private theorem complexTorusCoverLift_torusScalarRepresentative_eq {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q)) :
    complexTorusCoverLift (torusScalarRepresentative F) = F := by
  funext z
  let p : Space n × Space n :=
    (logarithmicCoordinatesEquiv n).symm z
  have hp :
      JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        p.1 p.2 = z := by
    change (logarithmicCoordinatesEquiv n) p = z
    exact (logarithmicCoordinatesEquiv n).apply_symm_apply z
  rw [← hp, complexTorusCoverLift_logarithmicPoint]
  exact periodic_torusScalarRepresentative_logarithmicPoint
    F hperiod p.1 p.2

private theorem barPartialCoordinate_periodic {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (j : Fin n) (q : Fin n → ℤ) :
    Function.Periodic (fun z => barPartialCoordinate F z j)
      (TorusCharacters.imaginaryShift q) := by
  intro z
  have he :
      (fun w : TorusCharacters.LogSpace n =>
        F (w + TorusCharacters.imaginaryShift q)) = F :=
    funext (hperiod q)
  have hd := congrArg
    (fun G : TorusCharacters.LogSpace n → ℂ =>
      fderiv ℝ G z) he
  change
    fderiv ℝ
      (fun w : TorusCharacters.LogSpace n =>
        F (w + TorusCharacters.imaginaryShift q)) z =
      fderiv ℝ F z at hd
  rw [fderiv_comp_add_right] at hd
  unfold barPartialCoordinate
  change
    ((fderiv ℝ F (z + TorusCharacters.imaginaryShift q))
        (Pi.single j (1 : ℂ)) +
      Complex.I *
        (fderiv ℝ F (z + TorusCharacters.imaginaryShift q))
          (Pi.single j Complex.I)) / 2 =
      ((fderiv ℝ F z) (Pi.single j (1 : ℂ)) +
        Complex.I * (fderiv ℝ F z) (Pi.single j Complex.I)) / 2
  rw [hd]

private theorem complexTorusCoverLift_barPartialRepresentative_eq {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (j : Fin n) :
    complexTorusCoverLift
      (fun z : WeightedTorusHilbert.LogTorus n =>
        (torusFunctionBarPartialRepresentative F z :
          EuclideanSpace ℂ (Fin n)) j) =
      (fun z : TorusCharacters.LogSpace n =>
        barPartialCoordinate F z j) := by
  change
    complexTorusCoverLift
      (torusScalarRepresentative
        (fun z : TorusCharacters.LogSpace n =>
          barPartialCoordinate F z j)) = _
  exact complexTorusCoverLift_torusScalarRepresentative_eq
    (fun z => barPartialCoordinate F z j)
    (fun q => barPartialCoordinate_periodic F hperiod j q)

private theorem weightedScalarGraphGenerator_complexCoverLift_ae_eq
    {n k : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hF : MemLp (torusScalarRepresentative F) 2
      (WeightedTorusHilbert.weightedTorusMeasure k φ)) :
    complexTorusCoverLift
      (fun z : WeightedTorusHilbert.LogTorus n =>
        torusScalarL2OfRepresentative φ F hF z) =ᵐ[
          (volume : Measure (TorusCharacters.LogSpace n))] F := by
  have h := weightedTorus_complexCoverLift_ae_eq hφ hF.coeFn_toLp
  change
    complexTorusCoverLift
      (fun z : WeightedTorusHilbert.LogTorus n =>
        torusScalarL2OfRepresentative φ F hF z) =ᵐ[
          (volume : Measure (TorusCharacters.LogSpace n))]
      complexTorusCoverLift (torusScalarRepresentative F)
    at h
  simpa only [complexTorusCoverLift_torusScalarRepresentative_eq F hperiod]
    using h

private theorem weightedFormGraphGenerator_complexCoverLift_ae_eq
    {n k : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (WeightedTorusHilbert.weightedTorusMeasure k φ))
    (j : Fin n) :
    complexTorusCoverLift
      (fun z : WeightedTorusHilbert.LogTorus n =>
        (torusFunctionBarPartialL2 φ F hD z :
          EuclideanSpace ℂ (Fin n)) j) =ᵐ[
            (volume : Measure (TorusCharacters.LogSpace n))]
      (fun z => barPartialCoordinate F z j) := by
  have hrow := hD.coeFn_toLp
  have hj :
      (fun z : WeightedTorusHilbert.LogTorus n =>
        (torusFunctionBarPartialL2 φ F hD z :
          EuclideanSpace ℂ (Fin n)) j) =ᵐ[
            WeightedTorusHilbert.weightedTorusMeasure k φ]
      (fun z : WeightedTorusHilbert.LogTorus n =>
        (torusFunctionBarPartialRepresentative F z :
          EuclideanSpace ℂ (Fin n)) j) := by
    filter_upwards [hrow] with z hz
    exact congrFun (congrArg WithLp.ofLp hz) j
  have h := weightedTorus_complexCoverLift_ae_eq hφ hj
  rw [complexTorusCoverLift_barPartialRepresentative_eq F hperiod j] at h
  exact h

private theorem weightedSmoothGraphGenerator_compact_barPartial_green
    {n k : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (hF₁ : ContDiff ℝ 1 F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hF : MemLp (torusScalarRepresentative F) 2
      (WeightedTorusHilbert.weightedTorusMeasure k φ))
    (hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (WeightedTorusHilbert.weightedTorusMeasure k φ))
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (j : Fin n) :
    (∫ z : TorusCharacters.LogSpace n,
      complexTorusCoverLift
        (fun p : WeightedTorusHilbert.LogTorus n =>
          torusScalarL2OfRepresentative φ F hF p) z *
        coverBarPartialTest ψ j z
      ∂(volume : Measure (TorusCharacters.LogSpace n))) =
      -(2 : ℂ) *
        (∫ z : TorusCharacters.LogSpace n,
          complexTorusCoverLift
            (fun p : WeightedTorusHilbert.LogTorus n =>
              (torusFunctionBarPartialL2 φ F hD p :
                EuclideanSpace ℂ (Fin n)) j) z * (ψ z : ℂ)
          ∂(volume : Measure (TorusCharacters.LogSpace n))) := by
  calc
    _ = ∫ z : TorusCharacters.LogSpace n,
      F z * coverBarPartialTest ψ j z
      ∂(volume : Measure (TorusCharacters.LogSpace n)) := by
        apply integral_congr_ae
        filter_upwards
          [weightedScalarGraphGenerator_complexCoverLift_ae_eq
            hφ F hperiod hF] with z hz
        rw [hz]
    _ = -(2 : ℂ) *
      (∫ z : TorusCharacters.LogSpace n,
        barPartialCoordinate F z j * (ψ z : ℂ)
        ∂(volume : Measure (TorusCharacters.LogSpace n))) :=
      complex_compact_barPartial_green hF₁ hψ hψcompact j
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards
        [weightedFormGraphGenerator_complexCoverLift_ae_eq
          hφ F hperiod hD j] with z hz
      rw [hz]

end WeightedTorusGraphWeakBridge

namespace WeightedTorusClosedGraphWeakBridge

open Set Function MeasureTheory Filter
open WeightedTorusHilbert WeightedBrascampSaturation ComplexKillingSaturationBridge
open DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
  Manifold ContDiff

private def realFundamentalCellMeasure {n : ℕ} (b : Space n) :
    Measure (Space n × Space n) :=
  (volume : Measure (Space n)).prod
    ((volume : Measure (Space n)).restrict
      (angularFundamentalBox b))

private def realWeightedFundamentalCellMeasure {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) (b : Space n) :
    Measure (Space n × Space n) :=
  (radialMeasure k φ).prod
    ((volume : Measure (Space n)).restrict
      (angularFundamentalBox b))

private abbrev weightedCellScalarL2 {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) (b : Space n) :=
  MeasureTheory.Lp ℂ 2 (realWeightedFundamentalCellMeasure k φ b)

private abbrev weightedCellFormL2 {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) (b : Space n) :=
  MeasureTheory.Lp (EuclideanSpace ℂ (Fin n)) 2
    (realWeightedFundamentalCellMeasure k φ b)

private theorem realWeightedFundamentalCell_measurePreserving {n k : ℕ}
    (φ : Space n → ℝ) (b : Space n) :
    MeasurePreserving (realTorusCoverProjection n)
      (realWeightedFundamentalCellMeasure k φ b)
      (weightedTorusMeasure k φ) :=
  weightedRealTorusCoverProjection_measurePreserving φ b

private def weightedScalarFundamentalLiftLI {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) (b : Space n) :
    weightedTorusScalarL2 k φ →ₗᵢ[ℂ] weightedCellScalarL2 k φ b :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ
    (realTorusCoverProjection n)
    (realWeightedFundamentalCell_measurePreserving φ b)

private def weightedFormFundamentalLiftLI {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) (b : Space n) :
    weightedTorusFormL2 k φ →ₗᵢ[ℂ] weightedCellFormL2 k φ b :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ
    (realTorusCoverProjection n)
    (realWeightedFundamentalCell_measurePreserving φ b)

private theorem weightedScalarFundamentalLiftLI_ae_eq {n k : ℕ}
    (φ : Space n → ℝ) (b : Space n)
    (f : weightedTorusScalarL2 k φ) :
    (fun p : Space n × Space n =>
      weightedScalarFundamentalLiftLI k φ b f p) =ᵐ[
        realWeightedFundamentalCellMeasure k φ b]
      (fun p => f (realTorusCoverProjection n p)) := by
  exact MeasureTheory.Lp.coeFn_compMeasurePreserving f
    (realWeightedFundamentalCell_measurePreserving φ b)

private theorem weightedFormFundamentalLiftLI_ae_eq {n k : ℕ}
    (φ : Space n → ℝ) (b : Space n)
    (f : weightedTorusFormL2 k φ) :
    (fun p : Space n × Space n =>
      weightedFormFundamentalLiftLI k φ b f p) =ᵐ[
        realWeightedFundamentalCellMeasure k φ b]
      (fun p => f (realTorusCoverProjection n p)) := by
  exact MeasureTheory.Lp.coeFn_compMeasurePreserving f
    (realWeightedFundamentalCell_measurePreserving φ b)

private def weightedCellScalarAdjointFunctional {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) (b : Space n)
    (u : weightedCellScalarL2 k φ b) :
    functionDolbeaultGraphAmbient k φ →L[ℂ] ℂ :=
  ((innerSL ℂ u).comp
    (weightedScalarFundamentalLiftLI k φ b).toContinuousLinearMap).comp
      (WithLp.fstL 2 ℂ (weightedTorusScalarL2 k φ)
        (weightedTorusFormL2 k φ))

private def weightedCellFormAdjointFunctional {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) (b : Space n)
    (u : weightedCellFormL2 k φ b) :
    functionDolbeaultGraphAmbient k φ →L[ℂ] ℂ :=
  ((innerSL ℂ u).comp
    (weightedFormFundamentalLiftLI k φ b).toContinuousLinearMap).comp
      (WithLp.sndL 2 ℂ (weightedTorusScalarL2 k φ)
        (weightedTorusFormL2 k φ))

private theorem realWeightedFundamentalCellMeasure_eq_withDensity {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (b : Space n) :
    realWeightedFundamentalCellMeasure k φ b =
      (realFundamentalCellMeasure b).withDensity
        (fun p : Space n × Space n =>
          radialWeight k φ p.1) := by
  unfold realWeightedFundamentalCellMeasure realFundamentalCellMeasure
    radialMeasure
  exact MeasureTheory.prod_withDensity_left
    (radialWeight_measurable k hφ)

private theorem realFundamentalCellMeasure_isLocallyFinite {n : ℕ}
    (b : Space n) :
    IsLocallyFiniteMeasure (realFundamentalCellMeasure b) := by
  unfold realFundamentalCellMeasure
  infer_instance

private theorem realWeightedFundamentalCellMeasure_isLocallyFinite {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (b : Space n) :
    IsLocallyFiniteMeasure (realWeightedFundamentalCellMeasure k φ b) := by
  let : IsLocallyFiniteMeasure (realFundamentalCellMeasure b) :=
    realFundamentalCellMeasure_isLocallyFinite b
  rw [realWeightedFundamentalCellMeasure_eq_withDensity hφ b]
  exact IsLocallyFiniteMeasure.withDensity_ofReal
    (Real.continuous_exp.comp
      (continuous_const.mul (hφ.comp continuous_fst)))

private def inverseRealCoverWeight {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ)
    (p : Space n × Space n) : ℂ :=
  (Real.exp ((k : ℝ) * φ p.1) : ℂ)

private theorem continuous_inverseRealCoverWeight {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ) :
    Continuous (inverseRealCoverWeight k φ) := by
  exact Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp
      (continuous_const.mul (hφ.comp continuous_fst)))

private def weightedCellAdjointScalarTest {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ)
    (ψ : TorusCharacters.LogSpace n → ℝ)
    (j : Fin n) (p : Space n × Space n) : ℂ :=
  inverseRealCoverWeight k φ p *
    coverAdjointScalarTest ψ j (logarithmicCoordinatesEquiv n p)

private def weightedCellAdjointVectorTest {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ)
    (ψ : TorusCharacters.LogSpace n → ℝ)
    (j : Fin n) (p : Space n × Space n) :
    EuclideanSpace ℂ (Fin n) :=
  inverseRealCoverWeight k φ p •
    coverAdjointVectorTest ψ j (logarithmicCoordinatesEquiv n p)

private theorem continuous_weightedCellAdjointScalarTest {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (j : Fin n) :
    Continuous (weightedCellAdjointScalarTest k φ ψ j) := by
  exact (continuous_inverseRealCoverWeight hφ).mul
    ((continuous_coverAdjointScalarTest hψ j).comp
      (logarithmicCoordinatesEquiv n).continuous)

private theorem continuous_weightedCellAdjointVectorTest {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (j : Fin n) :
    Continuous (weightedCellAdjointVectorTest k φ ψ j) := by
  exact (continuous_inverseRealCoverWeight hφ).smul
    ((continuous_coverAdjointVectorTest hψ.continuous j).comp
      (logarithmicCoordinatesEquiv n).continuous)

private theorem compactSupport_weightedCellAdjointScalarTest {n k : ℕ}
    (φ : Space n → ℝ)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    HasCompactSupport (weightedCellAdjointScalarTest k φ ψ j) := by
  have hcomp : HasCompactSupport
      (fun p : Space n × Space n =>
        coverAdjointScalarTest ψ j
          (logarithmicCoordinatesEquiv n p)) := by
    simpa only [ContinuousLinearEquiv.coe_toHomeomorph, comp_def] using
      (compactSupport_coverAdjointScalarTest hψcompact j).comp_homeomorph
        (logarithmicCoordinatesEquiv n).toHomeomorph
  exact hcomp.mul_left

private theorem compactSupport_weightedCellAdjointVectorTest {n k : ℕ}
    (φ : Space n → ℝ)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    HasCompactSupport (weightedCellAdjointVectorTest k φ ψ j) := by
  have hcomp : HasCompactSupport
      (fun p : Space n × Space n =>
        ψ (logarithmicCoordinatesEquiv n p)) := by
    simpa only [ContinuousLinearEquiv.coe_toHomeomorph, comp_def] using
      hψcompact.comp_homeomorph
        (logarithmicCoordinatesEquiv n).toHomeomorph
  refine hcomp.mono ?_
  intro p hp
  exact mt (fun h => by
    simp only [weightedCellAdjointVectorTest, coverAdjointVectorTest, h, Complex.ofReal_zero,
      mul_zero, smul_eq_zero, PiLp.single_eq_zero_iff, or_true]) hp

private def weightedCellAdjointScalarL2 {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    weightedCellScalarL2 k φ b := by
  letI : IsLocallyFiniteMeasure
      (realWeightedFundamentalCellMeasure k φ b) :=
    realWeightedFundamentalCellMeasure_isLocallyFinite hφ b
  exact ((continuous_weightedCellAdjointScalarTest hφ hψ j).memLp_of_hasCompactSupport
      (μ := realWeightedFundamentalCellMeasure k φ b)
      (compactSupport_weightedCellAdjointScalarTest φ hψcompact j)).toLp
        (weightedCellAdjointScalarTest k φ ψ j)

private def weightedCellAdjointVectorL2 {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    weightedCellFormL2 k φ b := by
  letI : IsLocallyFiniteMeasure
      (realWeightedFundamentalCellMeasure k φ b) :=
    realWeightedFundamentalCellMeasure_isLocallyFinite hφ b
  exact ((continuous_weightedCellAdjointVectorTest hφ hψ j).memLp_of_hasCompactSupport
      (μ := realWeightedFundamentalCellMeasure k φ b)
      (compactSupport_weightedCellAdjointVectorTest φ hψcompact j)).toLp
        (weightedCellAdjointVectorTest k φ ψ j)

private def weightedCellWeakAdjointFunctional {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    functionDolbeaultGraphAmbient k φ →L[ℂ] ℂ :=
  weightedCellScalarAdjointFunctional k φ b
    (weightedCellAdjointScalarL2 hφ b hψ hψcompact j) +
  weightedCellFormAdjointFunctional k φ b
    (weightedCellAdjointVectorL2 hφ b hψ hψcompact j)

private theorem weightedCellWeakAdjointFunctional_apply {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n)
    (v : functionDolbeaultGraphAmbient k φ) :
    weightedCellWeakAdjointFunctional hφ b hψ hψcompact j v =
      @inner ℂ (weightedCellScalarL2 k φ b) _
        (weightedCellAdjointScalarL2 hφ b hψ hψcompact j)
        (weightedScalarFundamentalLiftLI k φ b (WithLp.fst v)) +
      @inner ℂ (weightedCellFormL2 k φ b) _
        (weightedCellAdjointVectorL2 hφ b hψ hψcompact j)
        (weightedFormFundamentalLiftLI k φ b (WithLp.snd v)) := by
  rfl

private theorem realFundamentalCellMeasure_eq_restrict {n : ℕ}
    (b : Space n) :
    realFundamentalCellMeasure b =
      (volume : Measure (Space n × Space n)).restrict
        (Set.univ ×ˢ angularFundamentalBox b) := by
  rw [Measure.volume_eq_prod]
  simpa only [realFundamentalCellMeasure, Measure.restrict_univ] using
    (MeasureTheory.Measure.prod_restrict
      (μ := (volume : Measure (Space n)))
      (ν := (volume : Measure (Space n)))
      (Set.univ : Set (Space n))
      (angularFundamentalBox b))

private theorem weightedCellAdjointScalarL2_ae_eq {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    (fun p : Space n × Space n =>
      weightedCellAdjointScalarL2 (k := k) hφ b hψ hψcompact j p) =ᵐ[
        realWeightedFundamentalCellMeasure k φ b]
      weightedCellAdjointScalarTest k φ ψ j := by
  let : IsLocallyFiniteMeasure
      (realWeightedFundamentalCellMeasure k φ b) :=
    realWeightedFundamentalCellMeasure_isLocallyFinite hφ b
  simpa only [weightedCellAdjointScalarL2] using
    (MeasureTheory.MemLp.coeFn_toLp
      ((continuous_weightedCellAdjointScalarTest hφ hψ j).memLp_of_hasCompactSupport
          (μ := realWeightedFundamentalCellMeasure k φ b)
          (compactSupport_weightedCellAdjointScalarTest φ hψcompact j)))

private theorem weightedCellAdjointVectorL2_ae_eq {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    (fun p : Space n × Space n =>
      weightedCellAdjointVectorL2 (k := k) hφ b hψ hψcompact j p) =ᵐ[
        realWeightedFundamentalCellMeasure k φ b]
      weightedCellAdjointVectorTest k φ ψ j := by
  let : IsLocallyFiniteMeasure
      (realWeightedFundamentalCellMeasure k φ b) :=
    realWeightedFundamentalCellMeasure_isLocallyFinite hφ b
  simpa only [weightedCellAdjointVectorL2] using
    (MeasureTheory.MemLp.coeFn_toLp
      ((continuous_weightedCellAdjointVectorTest hφ hψ j).memLp_of_hasCompactSupport
          (μ := realWeightedFundamentalCellMeasure k φ b)
          (compactSupport_weightedCellAdjointVectorTest φ hψcompact j)))

private theorem radialWeight_mul_inverseRealCoverWeight {n k : ℕ}
    (φ : Space n → ℝ)
    (p : Space n × Space n) :
    ((radialWeight k φ p.1).toReal : ℂ) *
      inverseRealCoverWeight k φ p = 1 := by
  simp only [radialWeight, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    inverseRealCoverWeight]
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  have h : -(k : ℝ) * φ p.1 + (k : ℝ) * φ p.1 = 0 := by
    ring
  rw [h]
  simp only [Real.exp_zero, Complex.ofReal_one]

private theorem weightedCellScalar_inner_eq_unweighted {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n)
    (f : weightedTorusScalarL2 k φ) :
    @inner ℂ (weightedCellScalarL2 k φ b) _
      (weightedCellAdjointScalarL2 (k := k) hφ b hψ hψcompact j)
      (weightedScalarFundamentalLiftLI k φ b f) =
        ∫ p : Space n × Space n,
          f (realTorusCoverProjection n p) *
            coverBarPartialTest ψ j (logarithmicCoordinatesEquiv n p)
          ∂(realFundamentalCellMeasure b) := by
  calc
    _ = ∫ p : Space n × Space n,
        @inner ℂ ℂ _
          (weightedCellAdjointScalarTest k φ ψ j p)
          (f (realTorusCoverProjection n p))
        ∂(realWeightedFundamentalCellMeasure k φ b) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards
        [weightedCellAdjointScalarL2_ae_eq (k := k)
          hφ b hψ hψcompact j,
         weightedScalarFundamentalLiftLI_ae_eq φ b f] with p ha hf
      rw [ha, hf]
    _ = _ := by
      have hd : Measurable
          (fun p : Space n × Space n =>
            radialWeight k φ p.1) :=
        (radialWeight_measurable k hφ).comp measurable_fst
      rw [realWeightedFundamentalCellMeasure_eq_withDensity hφ b,
        integral_withDensity_eq_integral_toReal_smul
          hd
          (Filter.Eventually.of_forall
            (fun p : Space n × Space n =>
              radialWeight_lt_top φ p.1))]
      apply integral_congr_ae
      filter_upwards [] with p
      have hc := radialWeight_mul_inverseRealCoverWeight (k := k) φ p
      rw [RCLike.inner_apply]
      change
        (radialWeight k φ p.1).toReal •
          (f (realTorusCoverProjection n p) *
            star (weightedCellAdjointScalarTest k φ ψ j p)) =
          f (realTorusCoverProjection n p) *
            coverBarPartialTest ψ j (logarithmicCoordinatesEquiv n p)
      simp only [weightedCellAdjointScalarTest,
        coverAdjointScalarTest, star_mul,
        inverseRealCoverWeight, Complex.star_def, Complex.conj_ofReal,
        starRingEnd_self_apply,
        Complex.real_smul] at hc ⊢
      calc
        _ =
          (((radialWeight k φ p.1).toReal : ℂ) *
            (Real.exp ((k : ℝ) * φ p.1) : ℂ)) *
            (coverBarPartialTest ψ j
              (logarithmicCoordinatesEquiv n p) *
              f (realTorusCoverProjection n p)) := by ring
        _ = _ := by rw [hc, one_mul]; ring

private theorem weightedCellVector_inner_eq_unweighted {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n)
    (f : weightedTorusFormL2 k φ) :
    @inner ℂ (weightedCellFormL2 k φ b) _
      (weightedCellAdjointVectorL2 (k := k) hφ b hψ hψcompact j)
      (weightedFormFundamentalLiftLI k φ b f) =
        ∫ p : Space n × Space n,
          (2 : ℂ) *
            (((f (realTorusCoverProjection n p) :
              EuclideanSpace ℂ (Fin n)) j) *
                (ψ (logarithmicCoordinatesEquiv n p) : ℂ))
          ∂(realFundamentalCellMeasure b) := by
  calc
    _ = ∫ p : Space n × Space n,
        @inner ℂ (EuclideanSpace ℂ (Fin n)) _
          (weightedCellAdjointVectorTest k φ ψ j p)
          (f (realTorusCoverProjection n p))
        ∂(realWeightedFundamentalCellMeasure k φ b) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards
        [weightedCellAdjointVectorL2_ae_eq (k := k)
          hφ b hψ hψcompact j,
         weightedFormFundamentalLiftLI_ae_eq φ b f] with p ha hf
      rw [ha, hf]
    _ = _ := by
      have hd : Measurable
          (fun p : Space n × Space n =>
            radialWeight k φ p.1) :=
        (radialWeight_measurable k hφ).comp measurable_fst
      rw [realWeightedFundamentalCellMeasure_eq_withDensity hφ b,
        integral_withDensity_eq_integral_toReal_smul
          hd
          (Filter.Eventually.of_forall
            (fun p : Space n × Space n =>
              radialWeight_lt_top φ p.1))]
      apply integral_congr_ae
      filter_upwards [] with p
      have hc := radialWeight_mul_inverseRealCoverWeight (k := k) φ p
      unfold weightedCellAdjointVectorTest coverAdjointVectorTest
      rw [inner_smul_left, EuclideanSpace.inner_single_left]
      simp only [inverseRealCoverWeight,
        map_mul, map_ofNat, Complex.conj_ofReal,
        Complex.real_smul] at hc ⊢
      calc
        _ =
          (((radialWeight k φ p.1).toReal : ℂ) *
            (Real.exp ((k : ℝ) * φ p.1) : ℂ)) *
            ((2 : ℂ) *
              (((f (realTorusCoverProjection n p) :
                EuclideanSpace ℂ (Fin n)) j) *
                (ψ (logarithmicCoordinatesEquiv n p) : ℂ))) := by ring
        _ = _ := by rw [hc, one_mul]

private def coverFundamentalCell {n : ℕ} (b : Space n) :
    Set (TorusCharacters.LogSpace n) :=
  {z | ((logarithmicCoordinatesEquiv n).symm z).2 ∈ angularFundamentalBox b}

private theorem coverBarPartialTest_eq_zero_of_notMem_tsupport {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (j : Fin n) {z : TorusCharacters.LogSpace n}
    (hz : z ∉ tsupport ψ) :
    coverBarPartialTest ψ j z = 0 := by
  unfold coverBarPartialTest
  rw [fderiv_of_notMem_tsupport ℝ hz]
  simp only [zero_apply, Complex.ofReal_zero, mul_zero, add_zero]

private theorem coverRealTest_eq_zero_of_notMem_tsupport {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    {z : TorusCharacters.LogSpace n}
    (hz : z ∉ tsupport ψ) :
    ψ z = 0 := by
  by_contra hn
  apply hz
  exact subset_closure hn

private theorem realFundamentalCell_integral_eq_coverJacobian {n : ℕ}
    (b : Space n)
    (g : TorusCharacters.LogSpace n → ℂ)
    (hsupport : ∀ p : Space n × Space n,
      p.2 ∉ angularFundamentalBox b →
        g (logarithmicCoordinatesEquiv n p) = 0) :
    (∫ p : Space n × Space n,
      g (logarithmicCoordinatesEquiv n p)
      ∂(realFundamentalCellMeasure b)) =
      logarithmicCoverJacobianFactor n •
        (∫ z : TorusCharacters.LogSpace n, g z
          ∂(volume : Measure
            (TorusCharacters.LogSpace n))) := by
  calc
    _ = ∫ p : Space n × Space n,
        g (logarithmicCoordinatesEquiv n p)
        ∂(volume : Measure (Space n × Space n)) := by
      rw [realFundamentalCellMeasure_eq_restrict b]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      apply hsupport p
      simpa only [mem_prod, mem_univ, true_and] using hp
    _ = ∫ p : Space n × Space n,
        g (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
          p.1 p.2)
        ∂(volume : Measure (Space n × Space n)) := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun p =>
        congrArg g (logarithmicCoordinatesEquiv_apply p.1 p.2)
    _ = _ := integral_logarithmicCoordinates_eq_jacobian g

private theorem coverTest_zero_outside_fundamentalCell {n : ℕ}
    {b : Space n}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hcell : tsupport ψ ⊆ coverFundamentalCell b)
    (p : Space n × Space n)
    (hp : p.2 ∉ angularFundamentalBox b) :
    ψ (logarithmicCoordinatesEquiv n p) = 0 ∧
      ∀ j : Fin n,
        coverBarPartialTest ψ j (logarithmicCoordinatesEquiv n p) = 0 := by
  have hz : logarithmicCoordinatesEquiv n p ∉ tsupport ψ := by
    intro hz
    apply hp
    have hm :
        ((logarithmicCoordinatesEquiv n).symm
          (logarithmicCoordinatesEquiv n p)).2 ∈
            angularFundamentalBox b := hcell hz
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hm
  exact ⟨coverRealTest_eq_zero_of_notMem_tsupport hz,
    fun j => coverBarPartialTest_eq_zero_of_notMem_tsupport j hz⟩

private theorem weightedCellScalar_inner_eq_jacobian_cover {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalCell b)
    (j : Fin n) (f : weightedTorusScalarL2 k φ) :
    @inner ℂ (weightedCellScalarL2 k φ b) _
      (weightedCellAdjointScalarL2 (k := k) hφ b hψ hψcompact j)
      (weightedScalarFundamentalLiftLI k φ b f) =
      logarithmicCoverJacobianFactor n •
        (∫ z : TorusCharacters.LogSpace n,
          complexTorusCoverLift
            (fun p : WeightedTorusHilbert.LogTorus n => f p) z *
              coverBarPartialTest ψ j z
          ∂(volume : Measure
            (TorusCharacters.LogSpace n))) := by
  calc
    _ = ∫ p : Space n × Space n,
        f (realTorusCoverProjection n p) *
          coverBarPartialTest ψ j (logarithmicCoordinatesEquiv n p)
        ∂(realFundamentalCellMeasure b) :=
      weightedCellScalar_inner_eq_unweighted
        hφ b hψ hψcompact j f
    _ = ∫ p : Space n × Space n,
        (complexTorusCoverLift
          (fun q : WeightedTorusHilbert.LogTorus n => f q)
          (logarithmicCoordinatesEquiv n p)) *
          coverBarPartialTest ψ j (logarithmicCoordinatesEquiv n p)
        ∂(realFundamentalCellMeasure b) := by
      apply integral_congr_ae
      filter_upwards [] with p
      unfold complexTorusCoverLift complexTorusCoverProjection
      rw [ContinuousLinearEquiv.symm_apply_apply]
    _ = _ := by
      apply realFundamentalCell_integral_eq_coverJacobian b
        (fun z =>
          complexTorusCoverLift
            (fun p : WeightedTorusHilbert.LogTorus n => f p) z *
              coverBarPartialTest ψ j z)
      intro p hp
      rw [(coverTest_zero_outside_fundamentalCell hcell p hp).2 j,
        mul_zero]

private theorem weightedCellVector_inner_eq_jacobian_cover {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalCell b)
    (j : Fin n) (f : weightedTorusFormL2 k φ) :
    @inner ℂ (weightedCellFormL2 k φ b) _
      (weightedCellAdjointVectorL2 (k := k) hφ b hψ hψcompact j)
      (weightedFormFundamentalLiftLI k φ b f) =
      logarithmicCoverJacobianFactor n •
        (∫ z : TorusCharacters.LogSpace n,
          (2 : ℂ) *
            (complexTorusCoverLift
              (fun p : WeightedTorusHilbert.LogTorus n =>
                (f p : EuclideanSpace ℂ (Fin n)) j) z *
                (ψ z : ℂ))
          ∂(volume : Measure
            (TorusCharacters.LogSpace n))) := by
  calc
    _ = ∫ p : Space n × Space n,
        (2 : ℂ) *
          (((f (realTorusCoverProjection n p) :
            EuclideanSpace ℂ (Fin n)) j) *
              (ψ (logarithmicCoordinatesEquiv n p) : ℂ))
        ∂(realFundamentalCellMeasure b) :=
      weightedCellVector_inner_eq_unweighted
        hφ b hψ hψcompact j f
    _ = ∫ p : Space n × Space n,
        (2 : ℂ) *
          (complexTorusCoverLift
            (fun q : WeightedTorusHilbert.LogTorus n =>
              (f q : EuclideanSpace ℂ (Fin n)) j)
              (logarithmicCoordinatesEquiv n p) *
            (ψ (logarithmicCoordinatesEquiv n p) : ℂ))
        ∂(realFundamentalCellMeasure b) := by
      apply integral_congr_ae
      filter_upwards [] with p
      unfold complexTorusCoverLift complexTorusCoverProjection
      rw [ContinuousLinearEquiv.symm_apply_apply]
    _ = _ := by
      apply realFundamentalCell_integral_eq_coverJacobian b
        (fun z =>
          (2 : ℂ) *
            (complexTorusCoverLift
              (fun p : WeightedTorusHilbert.LogTorus n =>
                (f p : EuclideanSpace ℂ (Fin n)) j) z *
                (ψ z : ℂ)))
      intro p hp
      rw [(coverTest_zero_outside_fundamentalCell hcell p hp).1]
      simp only [Complex.ofReal_zero, mul_zero]

private theorem weightedCellWeakAdjointFunctional_smoothGraph_zero
    {n k : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ) (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalCell b)
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF₁ : ContDiff ℝ 1 F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hF : MemLp (torusScalarRepresentative F) 2
      (weightedTorusMeasure k φ))
    (hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (weightedTorusMeasure k φ)) (j : Fin n) :
    weightedCellWeakAdjointFunctional (k := k)
      hφ b hψ hψcompact j
        (WithLp.toLp 2
          (torusScalarL2OfRepresentative φ F hF,
           torusFunctionBarPartialL2 φ F hD)) = 0 := by
  rw [weightedCellWeakAdjointFunctional_apply]
  change
    @inner ℂ (weightedCellScalarL2 k φ b) _
      (weightedCellAdjointScalarL2 (k := k) hφ b hψ hψcompact j)
      (weightedScalarFundamentalLiftLI k φ b
        (torusScalarL2OfRepresentative φ F hF)) +
    @inner ℂ (weightedCellFormL2 k φ b) _
      (weightedCellAdjointVectorL2 (k := k) hφ b hψ hψcompact j)
      (weightedFormFundamentalLiftLI k φ b
        (torusFunctionBarPartialL2 φ F hD)) = 0
  rw [weightedCellScalar_inner_eq_jacobian_cover
    hφ b hψ hψcompact hcell j,
    weightedCellVector_inner_eq_jacobian_cover
      hφ b hψ hψcompact hcell j,
    ← smul_add, integral_const_mul,
    weightedSmoothGraphGenerator_compact_barPartial_green
      hφ F hF₁ hperiod hF hD hψ hψcompact j]
  simp only [neg_mul, neg_add_cancel, smul_zero]

private theorem weightedCellWeakAdjointFunctional_closedGraph_zero
    {n k : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ) (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalCell b)
    (j : Fin n) (v : functionDolbeaultGraphAmbient k φ)
    (hv : v ∈ functionDolbeaultGraph k φ) :
    weightedCellWeakAdjointFunctional
      hφ b hψ hψcompact j v = 0 := by
  let L : functionDolbeaultGraphAmbient k φ →L[ℂ] ℂ :=
    weightedCellWeakAdjointFunctional hφ b hψ hψcompact j
  have hspan :
      Submodule.span ℂ (smoothFunctionDolbeaultGraphSet k φ) ≤
        L.ker := by
    apply Submodule.span_le.mpr
    intro v hv'
    rcases hv' with ⟨F, hF, hperiod, _hcompact, hFLp, hDLp, rfl⟩
    change
      L (WithLp.toLp 2
        (torusScalarL2OfRepresentative φ F hFLp,
         torusFunctionBarPartialL2 φ F hDLp)) = 0
    exact weightedCellWeakAdjointFunctional_smoothGraph_zero
      hφ b hψ hψcompact hcell
      (hF.of_le (by norm_num)) hperiod hFLp hDLp j
  have hgraph : functionDolbeaultGraph k φ ≤ L.ker := by
    unfold functionDolbeaultGraph
    exact Submodule.topologicalClosure_minimal
      (Submodule.span ℂ (smoothFunctionDolbeaultGraphSet k φ))
      hspan L.isClosed_ker
  exact hgraph hv

private theorem weightedZeroGraph_compact_barPartial_zero_of_fundamentalCell
    {n k : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    (f : weightedTorusScalarL2 k φ)
    (hf : WithLp.toLp 2 (f, (0 : weightedTorusFormL2 k φ)) ∈
      functionDolbeaultGraph k φ)
    (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalCell b)
    (j : Fin n) :
    (∫ z : TorusCharacters.LogSpace n,
      complexTorusCoverLift
        (fun p : WeightedTorusHilbert.LogTorus n => f p) z *
          coverBarPartialTest ψ j z
      ∂(volume : Measure (TorusCharacters.LogSpace n))) = 0 := by
  have hz := weightedCellWeakAdjointFunctional_closedGraph_zero
    hφ b hψ hψcompact hcell j
    (WithLp.toLp 2 (f, (0 : weightedTorusFormL2 k φ))) hf
  rw [weightedCellWeakAdjointFunctional_apply] at hz
  change
    @inner ℂ (weightedCellScalarL2 k φ b) _
      (weightedCellAdjointScalarL2 (k := k) hφ b hψ hψcompact j)
      (weightedScalarFundamentalLiftLI k φ b f) +
    @inner ℂ (weightedCellFormL2 k φ b) _
      (weightedCellAdjointVectorL2 (k := k) hφ b hψ hψcompact j)
      (weightedFormFundamentalLiftLI k φ b
        (0 : weightedTorusFormL2 k φ)) = 0 at hz
  rw [map_zero, inner_zero_right, add_zero,
    weightedCellScalar_inner_eq_jacobian_cover
      hφ b hψ hψcompact hcell j] at hz
  exact (smul_eq_zero.mp hz).resolve_left
    (logarithmicCoverJacobianFactor_pos n).ne'

private def angularFundamentalInterior {n : ℕ} (b : Space n) :
    Set (Space n) :=
  {t | ∀ i : Fin n, t i ∈ Set.Ioo (b i) (b i + 1)}

private theorem angularFundamentalInterior_isOpen {n : ℕ}
    (b : Space n) :
    IsOpen (angularFundamentalInterior b) := by
  simpa only [angularFundamentalInterior, mem_Ioo, Set.pi, mem_univ, forall_const] using
    (isOpen_set_pi (s := fun i : Fin n => Set.Ioo (b i) (b i + 1))
      Set.finite_univ (fun _ _ => isOpen_Ioo))

private def coverFundamentalInterior {n : ℕ}
    (b : Space n) :
    Set (TorusCharacters.LogSpace n) :=
  {z | ((logarithmicCoordinatesEquiv n).symm z).2 ∈
    angularFundamentalInterior b}

private theorem coverFundamentalInterior_isOpen {n : ℕ}
    (b : Space n) :
    IsOpen (coverFundamentalInterior b) := by
  exact (angularFundamentalInterior_isOpen b).preimage
    (continuous_snd.comp (logarithmicCoordinatesEquiv n).symm.continuous)

private def coverCenteredFundamentalBase {n : ℕ}
    (z : TorusCharacters.LogSpace n) : Space n :=
  fun i => ((logarithmicCoordinatesEquiv n).symm z).2 i - (1 / 2 : ℝ)

private theorem self_mem_coverFundamentalInterior {n : ℕ}
    (z : TorusCharacters.LogSpace n) :
    z ∈ coverFundamentalInterior (coverCenteredFundamentalBase z) := by
  intro i
  change
    ((logarithmicCoordinatesEquiv n).symm z).2 i ∈
      Set.Ioo
        (((logarithmicCoordinatesEquiv n).symm z).2 i -
          (1 / 2 : ℝ))
        (((logarithmicCoordinatesEquiv n).symm z).2 i -
          (1 / 2 : ℝ) + 1)
  constructor <;> linarith

private theorem coverTestWithinFundamentalCell_of_tsupport_subset_interior
    {n : ℕ} (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : tsupport ψ ⊆ coverFundamentalInterior b) :
    tsupport ψ ⊆ coverFundamentalCell b := by
  intro z hz
  have h := hψ hz
  intro i
  exact ⟨h i |>.1, (h i).2.le⟩

private theorem exists_finite_fundamental_test_partition {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψcompact : HasCompactSupport ψ) :
    ∃ (s : Finset (TorusCharacters.LogSpace n))
      (χ : TorusCharacters.LogSpace n →
        TorusCharacters.LogSpace n → ℝ),
      (∀ i, ContDiff ℝ 1 (χ i)) ∧
      (∀ i, tsupport (χ i) ⊆
        coverFundamentalInterior (coverCenteredFundamentalBase i)) ∧
      (∀ z : TorusCharacters.LogSpace n,
        ψ z = ∑ i ∈ s, χ i z * ψ z) := by
  classical
  let E := TorusCharacters.LogSpace n
  let U : E → Set E := fun z =>
    coverFundamentalInterior (coverCenteredFundamentalBase z)
  have hUopen : ∀ z : E, IsOpen (U z) := fun z =>
    coverFundamentalInterior_isOpen (coverCenteredFundamentalBase z)
  have hUcover : tsupport ψ ⊆ ⋃ z : E, U z := by
    intro z _
    exact Set.mem_iUnion_of_mem z
      (self_mem_coverFundamentalInterior z)
  obtain ⟨ρ, hρ⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate
      (I := 𝓘(ℝ, E)) (isClosed_tsupport ψ) U hUopen hUcover
  have hfinite :
      {i : E | (Function.support (ρ i) ∩ tsupport ψ).Nonempty}.Finite :=
    ρ.locallyFinite.finite_nonempty_inter_compact hψcompact
  let s : Finset E := hfinite.toFinset
  refine ⟨s, fun i z => ρ i z, ?_, ?_, ?_⟩
  · intro i
    exact (ρ i).contMDiff.contDiff.of_le (by simp only [WithTop.one_le_coe, le_top])
  · intro i
    exact hρ i
  · intro z
    by_cases hz : z ∈ tsupport ψ
    · have hsubset : ρ.finsupport z ⊆ s := by
        intro i hi
        apply hfinite.mem_toFinset.mpr
        refine ⟨z, ?_, hz⟩
        exact (ρ.mem_finsupport z).mp hi
      have hone := ρ.sum_finsupport' z hz hsubset
      rw [← Finset.sum_mul, hone, one_mul]
    · rw [coverRealTest_eq_zero_of_notMem_tsupport hz]
      simp only [mul_zero, Finset.sum_const_zero]

private theorem coverBarPartialTest_finset_sum {n : ℕ}
    {ι : Type*} (s : Finset ι)
    (ψ : ι → TorusCharacters.LogSpace n → ℝ)
    (hψ : ∀ i ∈ s, ContDiff ℝ 1 (ψ i))
    (j : Fin n) (z : TorusCharacters.LogSpace n) :
    coverBarPartialTest (fun w => ∑ i ∈ s, ψ i w) j z =
      ∑ i ∈ s, coverBarPartialTest (ψ i) j z := by
  unfold coverBarPartialTest
  rw [fderiv_fun_sum
    (fun i hi => (hψ i hi).differentiable (by simp only [ne_eq, one_ne_zero, not_false_eq_true]) z)]
  simp only [sum_apply, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_add_distrib]

private theorem weightedZeroGraph_hasWeakBarPartialZero {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (f : weightedTorusScalarL2 k φ)
    (hf : WithLp.toLp 2 (f, (0 : weightedTorusFormL2 k φ)) ∈
      functionDolbeaultGraph k φ) :
    (∀ weakTest, ContDiff ℝ 1 weakTest → HasCompactSupport weakTest →
      ∀ weakCoordinate,
        (∫ weakPoint, (complexTorusCoverLift
        (fun p : WeightedTorusHilbert.LogTorus n => f p)) weakPoint *
          coverBarPartialTest weakTest weakCoordinate weakPoint) = 0) := by
  classical
  intro ψ hψ hψcompact j
  obtain ⟨s, χ, hχ, hχsupport, hpartition⟩ :=
    exists_finite_fundamental_test_partition hψcompact
  let ξ : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n → ℝ :=
    fun i z => χ i z * ψ z
  have hξ : ∀ i, ContDiff ℝ 1 (ξ i) := by
    intro i
    exact (hχ i).mul hψ
  have hξcompact : ∀ i, HasCompactSupport (ξ i) := by
    intro i
    exact hψcompact.mul_left
  have hξcell : ∀ i,
      tsupport (ξ i) ⊆ coverFundamentalCell (coverCenteredFundamentalBase i) := by
    intro i
    apply coverTestWithinFundamentalCell_of_tsupport_subset_interior
    exact tsupport_mul_subset_left.trans (hχsupport i)
  have hψsum : ψ = fun z => ∑ i ∈ s, ξ i z := by
    funext z
    exact hpartition z
  have hloc :=
    weightedScalarL2_complexTorusCoverLift_locallyIntegrable hφ f
  have hint : ∀ i ∈ s, Integrable
      (fun z : TorusCharacters.LogSpace n =>
        complexTorusCoverLift
          (fun p : WeightedTorusHilbert.LogTorus n => f p) z *
            coverBarPartialTest (ξ i) j z)
      (volume : Measure (TorusCharacters.LogSpace n)) := by
    intro i _
    simpa only [smul_eq_mul] using
      hloc.integrable_smul_right_of_hasCompactSupport
        (continuous_coverBarPartialTest (hξ i) j)
        (compactSupport_coverBarPartialTest (hξcompact i) j)
  change
    (∫ z : TorusCharacters.LogSpace n,
      complexTorusCoverLift
        (fun p : WeightedTorusHilbert.LogTorus n => f p) z *
          coverBarPartialTest ψ j z
      ∂(volume : Measure (TorusCharacters.LogSpace n))) = 0
  calc
    _ = ∫ z : TorusCharacters.LogSpace n,
        ∑ i ∈ s,
          complexTorusCoverLift
            (fun p : WeightedTorusHilbert.LogTorus n => f p) z *
              coverBarPartialTest (ξ i) j z
        ∂(volume : Measure (TorusCharacters.LogSpace n)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hψsum, coverBarPartialTest_finset_sum s ξ
        (fun i _ => hξ i) j z, Finset.mul_sum]
    _ = ∑ i ∈ s,
        (∫ z : TorusCharacters.LogSpace n,
          complexTorusCoverLift
            (fun p : WeightedTorusHilbert.LogTorus n => f p) z *
              coverBarPartialTest (ξ i) j z
          ∂(volume : Measure
            (TorusCharacters.LogSpace n))) :=
      integral_finsetSum s hint
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact weightedZeroGraph_compact_barPartial_zero_of_fundamentalCell
        hφ f hf (coverCenteredFundamentalBase i)
        (hξ i) (hξcompact i) (hξcell i) j

end WeightedTorusClosedGraphWeakBridge

namespace WeightedTorusVectorClosedGraphWeakBridge

open Set Function MeasureTheory Filter
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution

private def formCoordinateCLM {n : ℕ} (i : Fin n) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ :=
  PiLp.proj 2 (fun _ : Fin n => ℂ) i

end WeightedTorusVectorClosedGraphWeakBridge

namespace WeightedTorusWeylRepresentativeBridge

open Set MeasureTheory Filter Complex
open scoped BigOperators ContDiff Convolution ENNReal Topology

open DolbeaultRegularity DolbeaultGraphDistributionBridge

private theorem polarInterval_holomorphic_circle_mean
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (c : ℂ) (r : ℝ) :
    (∫ θ : ℝ in -Real.pi..Real.pi,
      f (circleMap c r θ)) =
      (2 * Real.pi : ℝ) • f c := by
  have hπ : (2 * Real.pi : ℝ) ≠ 0 :=
    ne_of_gt Real.two_pi_pos
  have hshift :
      (∫ θ : ℝ in 0..2 * Real.pi,
        f (circleMap c r (θ + -Real.pi))) =
        ∫ θ : ℝ in -Real.pi..Real.pi,
          f (circleMap c r θ) := by
    have h := intervalIntegral.integral_comp_add_right
      (a := (0 : ℝ)) (b := 2 * Real.pi)
      (fun θ : ℝ => f (circleMap c r θ)) (-Real.pi)
    convert h using 1
    all_goals ring_nf
  have hnormalized :
      (2 * Real.pi : ℝ)⁻¹ •
          (∫ θ : ℝ in -Real.pi..Real.pi,
            f (circleMap c r θ)) = f c := by
    calc
      (2 * Real.pi : ℝ)⁻¹ •
          (∫ θ : ℝ in -Real.pi..Real.pi,
            f (circleMap c r θ)) =
          Real.circleAverage f c r := by
            symm
            calc
              Real.circleAverage f c r =
                  (2 * Real.pi : ℝ)⁻¹ •
                    (∫ θ : ℝ in 0..2 * Real.pi,
                      f (circleMap c r (θ + -Real.pi))) :=
                Real.circleAverage_eq_integral_add (-Real.pi)
              _ = (2 * Real.pi : ℝ)⁻¹ •
                    (∫ θ : ℝ in -Real.pi..Real.pi,
                      f (circleMap c r θ)) := by rw [hshift]
      _ = f c :=
        (hf.diffContOnCl (s := Metric.ball c |r|)).circleAverage
  let A : ℂ :=
    ∫ θ : ℝ in -Real.pi..Real.pi, f (circleMap c r θ)
  have hcancel :
      (2 * Real.pi : ℝ) • ((2 * Real.pi : ℝ)⁻¹ • A) = A := by
    simp only [Complex.real_smul]
    push_cast
    field_simp [Real.pi_ne_zero]
  have h := congrArg
    (fun w : ℂ => (2 * Real.pi : ℝ) • w) hnormalized
  exact hcancel.symm.trans h

private def radialCoordinateKernel (w : ℂ) : ℝ :=
  Real.smoothTransition (1 - Complex.normSq w)

private theorem contDiff_radialCoordinateKernel :
    ContDiff ℝ ∞ radialCoordinateKernel := by
  unfold radialCoordinateKernel
  apply Real.smoothTransition.contDiff.comp
  simp_rw [Complex.normSq_apply]
  have hre : ContDiff ℝ ∞ (fun w : ℂ => w.re) :=
    Complex.reCLM.contDiff
  have him : ContDiff ℝ ∞ (fun w : ℂ => w.im) :=
    Complex.imCLM.contDiff
  exact contDiff_const.sub ((hre.mul hre).add (him.mul him))

private theorem radialCoordinateKernel_eq_zero_iff (w : ℂ) :
    radialCoordinateKernel w = 0 ↔ 1 ≤ ‖w‖ := by
  simp only [radialCoordinateKernel, Real.smoothTransition.zero_iff_nonpos, tsub_le_iff_right,
    zero_add, one_le_normSq_iff]

private theorem radialCoordinateKernel_nonneg (w : ℂ) :
    0 ≤ radialCoordinateKernel w :=
  Real.smoothTransition.nonneg _

private theorem radialCoordinateKernel_polar (r θ : ℝ) :
    radialCoordinateKernel
      (Complex.polarCoord.symm (r, θ)) =
      Real.smoothTransition (1 - r ^ 2) := by
  simp only [radialCoordinateKernel, Complex.polarCoord_symm_apply, ofReal_cos, ofReal_sin,
    normSq_eq_norm_sq, Complex.norm_mul, norm_real, Real.norm_eq_abs, norm_cos_add_sin_mul_I,
    mul_one, sq_abs]

private def productRadialKernel {n : ℕ}
    (w : TorusCharacters.LogSpace n) : ℝ :=
  ∏ i : Fin n, radialCoordinateKernel (w i)

private theorem contDiff_productRadialKernel (n : ℕ) :
    ContDiff ℝ ∞
      (productRadialKernel (n := n)) := by
  unfold productRadialKernel
  apply contDiff_prod
  intro i hi
  apply contDiff_radialCoordinateKernel.comp
  fun_prop

private theorem productRadialKernel_nonneg {n : ℕ}
    (w : TorusCharacters.LogSpace n) :
    0 ≤ productRadialKernel w := by
  unfold productRadialKernel
  exact Finset.prod_nonneg fun i hi => radialCoordinateKernel_nonneg _

private theorem support_productRadialKernel_subset_closedBall (n : ℕ) :
    Function.support (productRadialKernel (n := n)) ⊆
      Metric.closedBall
        (0 : TorusCharacters.LogSpace n) 1 := by
  intro w hw
  rw [Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  by_contra hi
  have hzero : radialCoordinateKernel (w i) = 0 :=
    (radialCoordinateKernel_eq_zero_iff _).2
      (le_of_lt (lt_of_not_ge hi))
  change (∏ j : Fin n, radialCoordinateKernel (w j)) ≠ 0 at hw
  exact hw (Finset.prod_eq_zero (Finset.mem_univ i) hzero)

private theorem hasCompactSupport_productRadialKernel (n : ℕ) :
    HasCompactSupport
      (productRadialKernel (n := n)) :=
  HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall
      (0 : TorusCharacters.LogSpace n) 1)
    (support_productRadialKernel_subset_closedBall n)

private def productRadialKernelMass (n : ℕ) : ℝ :=
  ∫ w : TorusCharacters.LogSpace n,
    productRadialKernel w

private theorem productRadialKernelMass_pos (n : ℕ) :
    0 < productRadialKernelMass n := by
  unfold productRadialKernelMass
  apply (contDiff_productRadialKernel n).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (hasCompactSupport_productRadialKernel n)
    (fun w => productRadialKernel_nonneg w)
    (x := (0 : TorusCharacters.LogSpace n))
  simp only [productRadialKernel, radialCoordinateKernel, Pi.zero_apply, map_zero, sub_zero,
    Real.smoothTransition.one, Finset.prod_const_one, ne_eq, one_ne_zero, not_false_eq_true]

private def normalizedProductRadialKernel {n : ℕ}
    (w : TorusCharacters.LogSpace n) : ℝ :=
  productRadialKernel w / productRadialKernelMass n

private theorem contDiff_normalizedProductRadialKernel (n : ℕ) :
    ContDiff ℝ ∞
      (normalizedProductRadialKernel (n := n)) := by
  unfold normalizedProductRadialKernel
  exact (contDiff_productRadialKernel n).div_const _

private theorem hasCompactSupport_normalizedProductRadialKernel (n : ℕ) :
    HasCompactSupport
      (normalizedProductRadialKernel (n := n)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall
      (0 : TorusCharacters.LogSpace n) 1)
  intro w hw
  apply support_productRadialKernel_subset_closedBall n
  intro hzero
  apply hw
  simp only [normalizedProductRadialKernel, hzero, zero_div]

private def productRadialHolomorphicMollification {n : ℕ}
    (g : TorusCharacters.LogSpace n → ℂ) :
    TorusCharacters.LogSpace n → ℂ :=
  normalizedProductRadialKernel
    ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      (volume : Measure (TorusCharacters.LogSpace n))] g

private theorem differentiable_productRadialHolomorphicMollification
    {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    (hweak : (∀ weakTest, ContDiff ℝ 1 weakTest → HasCompactSupport weakTest →
      ∀ weakCoordinate,
        (∫ weakPoint, g weakPoint *
          coverBarPartialTest weakTest weakCoordinate weakPoint) = 0)) :
    Differentiable ℂ (productRadialHolomorphicMollification g) := by
  unfold productRadialHolomorphicMollification
  rw [← complex_convolution_flip]
  apply differentiable_complex_of_weak_barPartial_convolution hg
  · exact (contDiff_normalizedProductRadialKernel n).of_le (by simp only [WithTop.one_le_coe,
    le_top])
  · exact hasCompactSupport_normalizedProductRadialKernel n
  · exact hweak

private theorem productRadialHolomorphicMollification_periodic
    {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    {d : TorusCharacters.LogSpace n}
    (hperiod : Function.Periodic g d) :
    Function.Periodic (productRadialHolomorphicMollification g) d := by
  unfold productRadialHolomorphicMollification
  rw [← complex_convolution_flip]
  exact complexReal_convolution_periodic
    (normalizedProductRadialKernel (n := n)) hperiod

end WeightedTorusWeylRepresentativeBridge

namespace WeightedTorusWeylRadialIntegrationBridge

open Set MeasureTheory Filter Complex
open scoped BigOperators ContDiff Convolution ENNReal Topology

open WeightedTorusWeylRepresentativeBridge

private def radialPolarIntegrand
    (f : ℂ → ℂ) (c : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) *
    ((radialCoordinateKernel (Complex.polarCoord.symm p) : ℂ) *
      f (c - Complex.polarCoord.symm p))

private theorem continuous_complexPolarSymm :
    Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
  simp only [Complex.polarCoord_symm_apply]
  fun_prop

private theorem continuous_radialPolarIntegrand
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) :
    Continuous (radialPolarIntegrand f c) := by
  unfold radialPolarIntegrand
  apply Continuous.mul (Complex.continuous_ofReal.comp continuous_fst)
  apply Continuous.mul
    (Complex.continuous_ofReal.comp
      (contDiff_radialCoordinateKernel.continuous.comp
        continuous_complexPolarSymm))
  exact hf.continuous.comp
    (continuous_const.sub continuous_complexPolarSymm)

private theorem radialCoordinateKernel_integral_eq_polar
    (f : ℂ → ℂ) (c : ℂ) :
    (∫ w : ℂ, radialCoordinateKernel w • f (c - w)) =
      ∫ p : ℝ × ℝ in Complex.polarCoord.target,
        radialPolarIntegrand f c p := by
  calc
    (∫ w : ℂ, radialCoordinateKernel w • f (c - w)) =
        ∫ p : ℝ × ℝ in Complex.polarCoord.target,
          p.1 •
            (radialCoordinateKernel (Complex.polarCoord.symm p) •
              f (c - Complex.polarCoord.symm p)) :=
      (Complex.integral_comp_polarCoord_symm
        (fun w : ℂ => radialCoordinateKernel w • f (c - w))).symm
    _ = ∫ p : ℝ × ℝ in Complex.polarCoord.target,
        radialPolarIntegrand f c p := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        simp only [radialPolarIntegrand, Complex.real_smul]

private def compactPolarDomain : Set (ℝ × ℝ) :=
  Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi

private theorem compactPolarDomain_subset_polarTarget :
    compactPolarDomain ⊆ Complex.polarCoord.target := by
  rw [Complex.polarCoord_target]
  intro p hp
  exact ⟨hp.1.1, hp.2⟩

private theorem radialPolarIntegrand_eq_zero_outside_compactDomain
    (f : ℂ → ℂ) (c : ℂ)
    (p : ℝ × ℝ)
    (hp : p ∈ Complex.polarCoord.target)
    (houtside : p ∉ compactPolarDomain) :
    radialPolarIntegrand f c p = 0 := by
  rw [Complex.polarCoord_target] at hp
  have hr : ¬p.1 ≤ 1 := by
    intro hle
    apply houtside
    exact ⟨⟨hp.1, hle⟩, hp.2⟩
  have hnorm : 1 ≤ ‖Complex.polarCoord.symm p‖ := by
    rw [Complex.norm_polarCoord_symm,
      abs_of_pos hp.1]
    exact le_of_lt (lt_of_not_ge hr)
  have hzero :=
    (radialCoordinateKernel_eq_zero_iff
      (Complex.polarCoord.symm p)).2 hnorm
  change
    (p.1 : ℂ) *
      ((radialCoordinateKernel (Complex.polarCoord.symm p) : ℂ) *
        f (c - Complex.polarCoord.symm p)) = 0
  rw [hzero]
  simp only [ofReal_zero, Complex.polarCoord_symm_apply, ofReal_cos, ofReal_sin, zero_mul, mul_zero]

private theorem radialPolarIntegral_eq_compactDomain
    (f : ℂ → ℂ) (c : ℂ) :
    (∫ p : ℝ × ℝ in Complex.polarCoord.target,
      radialPolarIntegrand f c p) =
      ∫ p : ℝ × ℝ in compactPolarDomain,
        radialPolarIntegrand f c p := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    Complex.polarCoord.open_target.measurableSet
    compactPolarDomain_subset_polarTarget
  intro p hp
  exact radialPolarIntegrand_eq_zero_outside_compactDomain
    f c p hp.1 hp.2

private theorem radialPolarIntegrand_integrableOn_compactDomain
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) :
    IntegrableOn (radialPolarIntegrand f c)
      compactPolarDomain (volume : Measure (ℝ × ℝ)) := by
  have hcompact :
      IsCompact
        (Set.Icc (0 : ℝ) 1 ×ˢ
          Set.Icc (-Real.pi) Real.pi) :=
    isCompact_Icc.prod isCompact_Icc
  have hi : IntegrableOn (radialPolarIntegrand f c)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-Real.pi) Real.pi)
      (volume : Measure (ℝ × ℝ)) :=
    (continuous_radialPolarIntegrand hf c).continuousOn.integrableOn_compact
      hcompact
  apply hi.mono_set
  intro p hp
  exact ⟨⟨hp.1.1.le, hp.1.2⟩,
    ⟨hp.2.1.le, hp.2.2.le⟩⟩

private theorem compactPolarDomain_volume :
    (volume : Measure (ℝ × ℝ)).restrict compactPolarDomain =
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)).prod
        ((volume : Measure ℝ).restrict
          (Set.Ioo (-Real.pi) Real.pi)) := by
  unfold compactPolarDomain
  change
    ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi) = _
  exact (MeasureTheory.Measure.prod_restrict
    (Set.Ioc (0 : ℝ) 1) (Set.Ioo (-Real.pi) Real.pi)).symm

private theorem radialPolar_compact_integral_eq_iterated
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) :
    (∫ p : ℝ × ℝ in compactPolarDomain,
      radialPolarIntegrand f c p) =
      ∫ r : ℝ in Set.Ioc (0 : ℝ) 1,
        ∫ θ : ℝ in Set.Ioo (-Real.pi) Real.pi,
          radialPolarIntegrand f c (r, θ) := by
  let μr : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)
  let μθ : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioo (-Real.pi) Real.pi)
  have hmeasure :
      (volume : Measure (ℝ × ℝ)).restrict compactPolarDomain =
        μr.prod μθ := compactPolarDomain_volume
  have hi : Integrable (radialPolarIntegrand f c) (μr.prod μθ) := by
    rw [← hmeasure]
    exact radialPolarIntegrand_integrableOn_compactDomain hf c
  calc
    (∫ p : ℝ × ℝ in compactPolarDomain,
      radialPolarIntegrand f c p) =
      ∫ p : ℝ × ℝ, radialPolarIntegrand f c p ∂(μr.prod μθ) := by
        rw [← hmeasure]
    _ = ∫ r : ℝ, ∫ θ : ℝ,
      radialPolarIntegrand f c (r, θ) ∂μθ ∂μr :=
      MeasureTheory.integral_prod _ hi
    _ = ∫ r : ℝ in Set.Ioc (0 : ℝ) 1,
      ∫ θ : ℝ in Set.Ioo (-Real.pi) Real.pi,
        radialPolarIntegrand f c (r, θ) := rfl

private theorem complexPolarSymm_eq_circleMap_zero (r θ : ℝ) :
    Complex.polarCoord.symm (r, θ) = circleMap 0 r θ := by
  simp only [Complex.polarCoord_symm_apply, ofReal_cos, ofReal_sin, circleMap, exp_mul_I, zero_add]

private theorem complexPolar_center_sub_eq_circleMap
    (c : ℂ) (r θ : ℝ) :
    c - Complex.polarCoord.symm (r, θ) =
      circleMap c (-r) θ := by
  rw [complexPolarSymm_eq_circleMap_zero]
  simp only [circleMap, zero_add, ofReal_neg, neg_mul]
  ring

private theorem radialPolar_angle_integral
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (c : ℂ) (r : ℝ) :
    (∫ θ : ℝ in Set.Ioo (-Real.pi) Real.pi,
      radialPolarIntegrand f c (r, θ)) =
      (r : ℂ) *
        ((Real.smoothTransition (1 - r ^ 2) : ℂ) *
          ((2 * Real.pi : ℝ) • f c)) := by
  have hangle : -Real.pi ≤ Real.pi := by
    linarith [Real.pi_pos]
  have hcircle :=
    polarInterval_holomorphic_circle_mean hf c (-r)
  have hpoint (θ : ℝ) :
      radialPolarIntegrand f c (r, θ) =
        (r : ℂ) *
          ((Real.smoothTransition (1 - r ^ 2) : ℂ) *
            f (circleMap c (-r) θ)) := by
    unfold radialPolarIntegrand
    rw [radialCoordinateKernel_polar,
      complexPolar_center_sub_eq_circleMap]
  calc
    (∫ θ : ℝ in Set.Ioo (-Real.pi) Real.pi,
      radialPolarIntegrand f c (r, θ)) =
      ∫ θ : ℝ in Set.Ioc (-Real.pi) Real.pi,
        radialPolarIntegrand f c (r, θ) :=
      MeasureTheory.integral_Ioc_eq_integral_Ioo.symm
    _ = ∫ θ : ℝ in -Real.pi..Real.pi,
      radialPolarIntegrand f c (r, θ) :=
      (intervalIntegral.integral_of_le hangle).symm
    _ = ∫ θ : ℝ in -Real.pi..Real.pi,
      (r : ℂ) *
        ((Real.smoothTransition (1 - r ^ 2) : ℂ) *
          f (circleMap c (-r) θ)) := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        exact hpoint θ
    _ = (r : ℂ) *
        (∫ θ : ℝ in -Real.pi..Real.pi,
          (Real.smoothTransition (1 - r ^ 2) : ℂ) *
            f (circleMap c (-r) θ)) :=
        intervalIntegral.integral_const_mul _ _
    _ = (r : ℂ) *
        ((Real.smoothTransition (1 - r ^ 2) : ℂ) *
          (∫ θ : ℝ in -Real.pi..Real.pi,
            f (circleMap c (-r) θ))) := by
        congr 1
        exact intervalIntegral.integral_const_mul _ _
    _ = (r : ℂ) *
        ((Real.smoothTransition (1 - r ^ 2) : ℂ) *
          ((2 * Real.pi : ℝ) • f c)) := by
        rw [hcircle]

private theorem radialPolar_angle_integral_eq_one_mul_center
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (c : ℂ) (r : ℝ) :
    (∫ θ : ℝ in Set.Ioo (-Real.pi) Real.pi,
      radialPolarIntegrand f c (r, θ)) =
      (∫ θ : ℝ in Set.Ioo (-Real.pi) Real.pi,
        radialPolarIntegrand (fun _ : ℂ => (1 : ℂ)) 0 (r, θ)) *
          f c := by
  have hone : Differentiable ℂ (fun _ : ℂ => (1 : ℂ)) := by
    fun_prop
  rw [radialPolar_angle_integral hf c r,
    radialPolar_angle_integral hone 0 r]
  simp only [Complex.real_smul, mul_one]
  ring

private theorem radialCoordinateKernel_holomorphic_integral
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (c : ℂ) :
    (∫ w : ℂ,
      radialCoordinateKernel w • f (c - w)) =
      (∫ w : ℂ, radialCoordinateKernel w) • f c := by
  have hone : Differentiable ℂ (fun _ : ℂ => (1 : ℂ)) := by
    fun_prop
  calc
    (∫ w : ℂ,
      radialCoordinateKernel w • f (c - w)) =
      ∫ p : ℝ × ℝ in Complex.polarCoord.target,
        radialPolarIntegrand f c p :=
      radialCoordinateKernel_integral_eq_polar f c
    _ = ∫ p : ℝ × ℝ in compactPolarDomain,
        radialPolarIntegrand f c p :=
      radialPolarIntegral_eq_compactDomain f c
    _ = ∫ r : ℝ in Set.Ioc (0 : ℝ) 1,
        ∫ θ : ℝ in Set.Ioo (-Real.pi) Real.pi,
          radialPolarIntegrand f c (r, θ) :=
      radialPolar_compact_integral_eq_iterated hf c
    _ = ∫ r : ℝ in Set.Ioc (0 : ℝ) 1,
        ((∫ θ : ℝ in Set.Ioo (-Real.pi) Real.pi,
          radialPolarIntegrand (fun _ : ℂ => (1 : ℂ)) 0 (r, θ)) *
            f c) := by
      apply integral_congr_ae
      filter_upwards [] with r
      exact radialPolar_angle_integral_eq_one_mul_center hf c r
    _ = (∫ r : ℝ in Set.Ioc (0 : ℝ) 1,
          ∫ θ : ℝ in Set.Ioo (-Real.pi) Real.pi,
            radialPolarIntegrand (fun _ : ℂ => (1 : ℂ))
              0 (r, θ)) * f c :=
      MeasureTheory.integral_mul_const _ _
    _ = (∫ p : ℝ × ℝ in compactPolarDomain,
          radialPolarIntegrand (fun _ : ℂ => (1 : ℂ)) 0 p) *
            f c := by
      rw [radialPolar_compact_integral_eq_iterated hone 0]
    _ = (∫ p : ℝ × ℝ in Complex.polarCoord.target,
          radialPolarIntegrand (fun _ : ℂ => (1 : ℂ)) 0 p) *
            f c := by
      rw [radialPolarIntegral_eq_compactDomain]
    _ = (∫ w : ℂ,
          radialCoordinateKernel w • (1 : ℂ)) * f c := by
      rw [radialCoordinateKernel_integral_eq_polar
        (fun _ : ℂ => (1 : ℂ)) 0]
    _ = (∫ w : ℂ, radialCoordinateKernel w) • f c := by
      simp only [Complex.real_smul, mul_one]
      exact congrArg (fun w : ℂ => w * f c)
        (integral_complex_ofReal (f := radialCoordinateKernel))

private theorem radialCoordinateKernel_holomorphic_integral_at_zero
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    (∫ w : ℂ, radialCoordinateKernel w • f w) =
      (∫ w : ℂ, radialCoordinateKernel w) • f 0 := by
  have hneg : Differentiable ℂ (fun w : ℂ => f (-w)) := by
    apply hf.comp
    fun_prop
  simpa only [zero_sub, neg_neg, neg_zero] using
    radialCoordinateKernel_holomorphic_integral hneg 0

private theorem productRadialKernel_insertNth {n : ℕ}
    (i : Fin (n + 1)) (w : ℂ)
    (y : Fin n → ℂ) :
    productRadialKernel (i.insertNth w y) =
      radialCoordinateKernel w * productRadialKernel y := by
  unfold productRadialKernel
  have hfun :
      (fun j : Fin (n + 1) =>
        radialCoordinateKernel
          ((i.insertNth w y : Fin (n + 1) → ℂ) j)) =
        (i.insertNth (radialCoordinateKernel w)
          (fun j : Fin n => radialCoordinateKernel (y j)) :
            Fin (n + 1) → ℝ) := by
    apply funext
    rw [i.forall_iff_succAbove]
    constructor
    · simp only [Fin.insertNth_apply_same]
    · intro j
      simp only [Fin.insertNth_apply_succAbove]
  rw [hfun]
  exact Fin.prod_insertNth i (radialCoordinateKernel w)
    (fun j : Fin n => radialCoordinateKernel (y j))

private def productRadialWeightedIntegrand {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (w : TorusCharacters.LogSpace n) : ℂ :=
  (productRadialKernel w : ℂ) * F w

private theorem continuous_productRadialWeightedIntegrand {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Continuous F) :
    Continuous (productRadialWeightedIntegrand F) := by
  unfold productRadialWeightedIntegrand
  exact (Complex.continuous_ofReal.comp
    (contDiff_productRadialKernel n).continuous).mul hF

private theorem hasCompactSupport_productRadialWeightedIntegrand
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ) :
    HasCompactSupport (productRadialWeightedIntegrand F) := by
  refine (hasCompactSupport_productRadialKernel n).mono ?_
  intro w hw
  change productRadialKernel w ≠ 0
  intro hzero
  apply hw
  simp only [productRadialWeightedIntegrand, hzero, ofReal_zero, zero_mul]

private theorem integrable_productRadialWeightedIntegrand {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Continuous F) :
    Integrable (productRadialWeightedIntegrand F)
      (volume : Measure
        (TorusCharacters.LogSpace n)) :=
  (continuous_productRadialWeightedIntegrand hF).integrable_of_hasCompactSupport
    (hasCompactSupport_productRadialWeightedIntegrand F)

private theorem productRadialWeighted_integral_eq_coordinateFubini
    {n : ℕ}
    {F : TorusCharacters.LogSpace (n + 1) → ℂ}
    (hF : Continuous F)
    (i : Fin (n + 1)) :
    (∫ w : TorusCharacters.LogSpace (n + 1),
      productRadialWeightedIntegrand F w) =
      ∫ y : TorusCharacters.LogSpace n,
        ∫ x : ℂ,
          productRadialWeightedIntegrand F
            (i.insertNth x y) := by
  let e :
      (ℂ × TorusCharacters.LogSpace n) ≃ᵐ
        TorusCharacters.LogSpace (n + 1) :=
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => ℂ) i).symm
  have he : MeasurePreserving e
      ((volume : Measure ℂ).prod
        (volume : Measure
          (TorusCharacters.LogSpace n)))
      (volume : Measure
        (TorusCharacters.LogSpace (n + 1))) := by
    simpa [e, MeasureTheory.volume_pi] using
      (MeasureTheory.measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => (volume : Measure ℂ)) i).symm
  have hi :
      Integrable
        (fun p : ℂ × TorusCharacters.LogSpace n =>
          productRadialWeightedIntegrand F
            (i.insertNth p.1 p.2))
        ((volume : Measure ℂ).prod
          (volume : Measure
            (TorusCharacters.LogSpace n))) := by
    have h := he.integrable_comp_of_integrable
      (integrable_productRadialWeightedIntegrand hF)
    simpa [e, Function.comp_def,
      MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv] using h
  calc
    (∫ w : TorusCharacters.LogSpace (n + 1),
      productRadialWeightedIntegrand F w) =
      ∫ p : ℂ × TorusCharacters.LogSpace n,
        productRadialWeightedIntegrand F
          (i.insertNth p.1 p.2)
        ∂((volume : Measure ℂ).prod
          (volume : Measure
            (TorusCharacters.LogSpace n))) := by
      simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk,
        e] using
          (he.integral_comp'
            (productRadialWeightedIntegrand F)).symm
    _ = ∫ y : TorusCharacters.LogSpace n,
        ∫ x : ℂ,
          productRadialWeightedIntegrand F
            (i.insertNth x y) :=
      MeasureTheory.integral_prod_symm _ hi

private def holomorphicCoordinateReset {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (i : Fin n) :
    TorusCharacters.LogSpace n → ℂ :=
  fun w => F (Function.update w i 0)

private theorem differentiable_holomorphicCoordinateReset {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F) (i : Fin n) :
    Differentiable ℂ (holomorphicCoordinateReset F i) := by
  unfold holomorphicCoordinateReset
  change Differentiable ℂ
    (F ∘ fun w : TorusCharacters.LogSpace n =>
      Function.update w i 0)
  apply hF.comp
  apply differentiable_pi.mpr
  intro j
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self, differentiable_const]
  · have heq :
        (fun w : TorusCharacters.LogSpace n =>
          Function.update w i 0 j) =
          (fun w : TorusCharacters.LogSpace n => w j) := by
        funext w
        simp only [ne_eq, hj, not_false_eq_true, Function.update_of_ne]
    rw [heq]
    exact (ContinuousLinearMap.proj j :
      TorusCharacters.LogSpace n →L[ℂ] ℂ).differentiable

private theorem differentiable_insertNth_holomorphicSlice {n : ℕ}
    {F : TorusCharacters.LogSpace (n + 1) → ℂ}
    (hF : Differentiable ℂ F)
    (i : Fin (n + 1))
    (y : TorusCharacters.LogSpace n) :
    Differentiable ℂ
      (fun x : ℂ => F (i.insertNth x y)) := by
  have hslice :=
    HolomorphicLaurentFourierCompletenessBridge.differentiable_coordinateHolomorphicSlice
      hF (i.insertNth (0 : ℂ) y) i
  have heq :
      (fun x : ℂ => F (i.insertNth x y)) =
        HolomorphicLaurentFourierCompletenessBridge.coordinateHolomorphicSlice
          F (i.insertNth (0 : ℂ) y) i := by
    funext x
    apply congrArg F
    apply funext
    rw [i.forall_iff_succAbove]
    constructor
    · simp only [Fin.insertNth_apply_same, ↓reduceIte]
    · intro j
      simp only [Fin.insertNth_apply_succAbove, i.succAbove_ne, ↓reduceIte]
  rw [heq]
  exact hslice

private theorem update_insertNth_zero {n : ℕ}
    (i : Fin (n + 1)) (x : ℂ)
    (y : TorusCharacters.LogSpace n) :
    Function.update
      (i.insertNth x y : Fin (n + 1) → ℂ) i 0 =
      (i.insertNth (0 : ℂ) y : Fin (n + 1) → ℂ) := by
  apply funext
  rw [i.forall_iff_succAbove]
  constructor
  · simp only [Function.update_self, Fin.insertNth_apply_same]
  · intro j
    simp only [ne_eq, i.succAbove_ne, not_false_eq_true, Function.update_of_ne,
      Fin.insertNth_apply_succAbove]

private theorem productRadialWeighted_slice_integral_reset
    {n : ℕ}
    {F : TorusCharacters.LogSpace (n + 1) → ℂ}
    (hF : Differentiable ℂ F)
    (i : Fin (n + 1))
    (y : TorusCharacters.LogSpace n) :
    (∫ x : ℂ,
      productRadialWeightedIntegrand F (i.insertNth x y)) =
      ∫ x : ℂ,
        productRadialWeightedIntegrand
          (holomorphicCoordinateReset F i)
          (i.insertNth x y) := by
  let g : ℂ → ℂ := fun x => F (i.insertNth x y)
  have hg : Differentiable ℂ g :=
    differentiable_insertNth_holomorphicSlice hF i y
  have hrad :
      (∫ x : ℂ, (radialCoordinateKernel x : ℂ) * g x) =
        (↑(∫ x : ℂ, radialCoordinateKernel x) : ℂ) * g 0 := by
    simpa only [Complex.real_smul] using
      radialCoordinateKernel_holomorphic_integral_at_zero hg
  have hbase :
      (∫ x : ℂ, (radialCoordinateKernel x : ℂ) * g 0) =
        (↑(∫ x : ℂ, radialCoordinateKernel x) : ℂ) * g 0 := by
    calc
      (∫ x : ℂ, (radialCoordinateKernel x : ℂ) * g 0) =
        (∫ x : ℂ, (radialCoordinateKernel x : ℂ)) * g 0 :=
        MeasureTheory.integral_mul_const _ _
      _ = (↑(∫ x : ℂ, radialCoordinateKernel x) : ℂ) * g 0 :=
        congrArg (fun a : ℂ => a * g 0)
          (integral_complex_ofReal (f := radialCoordinateKernel))
  have hpoint (x : ℂ) :
      productRadialWeightedIntegrand F (i.insertNth x y) =
        (productRadialKernel y : ℂ) *
          ((radialCoordinateKernel x : ℂ) * g x) := by
    change
      (productRadialKernel (i.insertNth x y) : ℂ) *
        F (i.insertNth x y) = _
    rw [productRadialKernel_insertNth]
    push_cast
    dsimp [g]
    ring
  have hreset (x : ℂ) :
      productRadialWeightedIntegrand
        (holomorphicCoordinateReset F i) (i.insertNth x y) =
        (productRadialKernel y : ℂ) *
          ((radialCoordinateKernel x : ℂ) * g 0) := by
    change
      (productRadialKernel (i.insertNth x y) : ℂ) *
        F (Function.update
          (i.insertNth x y : Fin (n + 1) → ℂ) i 0) = _
    rw [productRadialKernel_insertNth, update_insertNth_zero]
    push_cast
    dsimp [g]
    ring
  calc
    (∫ x : ℂ,
      productRadialWeightedIntegrand F (i.insertNth x y)) =
      ∫ x : ℂ,
        (productRadialKernel y : ℂ) *
          ((radialCoordinateKernel x : ℂ) * g x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact hpoint x
    _ = (productRadialKernel y : ℂ) *
        (∫ x : ℂ, (radialCoordinateKernel x : ℂ) * g x) :=
      MeasureTheory.integral_const_mul _ _
    _ = (productRadialKernel y : ℂ) *
        ((↑(∫ x : ℂ, radialCoordinateKernel x) : ℂ) * g 0) := by
      rw [hrad]
    _ = (productRadialKernel y : ℂ) *
        (∫ x : ℂ, (radialCoordinateKernel x : ℂ) * g 0) := by
      rw [hbase]
    _ = ∫ x : ℂ,
        (productRadialKernel y : ℂ) *
          ((radialCoordinateKernel x : ℂ) * g 0) :=
      (MeasureTheory.integral_const_mul _ _).symm
    _ = ∫ x : ℂ,
      productRadialWeightedIntegrand
        (holomorphicCoordinateReset F i) (i.insertNth x y) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (hreset x).symm

private theorem productRadialWeighted_integral_coordinate_reset
    {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (i : Fin n) :
    (∫ w : TorusCharacters.LogSpace n,
      productRadialWeightedIntegrand F w) =
      ∫ w : TorusCharacters.LogSpace n,
        productRadialWeightedIntegrand
          (holomorphicCoordinateReset F i) w := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    calc
      (∫ w : TorusCharacters.LogSpace (n + 1),
        productRadialWeightedIntegrand F w) =
        ∫ y : TorusCharacters.LogSpace n,
          ∫ x : ℂ,
            productRadialWeightedIntegrand F
              (i.insertNth x y) :=
        productRadialWeighted_integral_eq_coordinateFubini
          hF.continuous i
      _ = ∫ y : TorusCharacters.LogSpace n,
          ∫ x : ℂ,
            productRadialWeightedIntegrand
              (holomorphicCoordinateReset F i)
              (i.insertNth x y) := by
        apply integral_congr_ae
        filter_upwards [] with y
        exact productRadialWeighted_slice_integral_reset hF i y
      _ = ∫ w : TorusCharacters.LogSpace (n + 1),
          productRadialWeightedIntegrand
            (holomorphicCoordinateReset F i) w :=
        (productRadialWeighted_integral_eq_coordinateFubini
          (differentiable_holomorphicCoordinateReset hF i).continuous
          i).symm

private def holomorphicFinsetReset {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (s : Finset (Fin n)) :
    TorusCharacters.LogSpace n → ℂ :=
  fun w => F (fun i => if i ∈ s then 0 else w i)

private theorem differentiable_holomorphicFinsetReset {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (s : Finset (Fin n)) :
    Differentiable ℂ (holomorphicFinsetReset F s) := by
  unfold holomorphicFinsetReset
  change Differentiable ℂ
    (F ∘ fun w : TorusCharacters.LogSpace n =>
      fun i => if i ∈ s then 0 else w i)
  apply hF.comp
  apply differentiable_pi.mpr
  intro i
  by_cases hi : i ∈ s
  · simp only [hi, ↓reduceIte, differentiable_const]
  · change Differentiable ℂ
      (fun w : TorusCharacters.LogSpace n =>
        if i ∈ s then 0 else w i)
    simp only [ite_eq_right hi]
    exact (ContinuousLinearMap.proj i :
      TorusCharacters.LogSpace n →L[ℂ] ℂ).differentiable

private theorem holomorphicCoordinateReset_finsetReset
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (s : Finset (Fin n)) (i : Fin n) :
    holomorphicCoordinateReset (holomorphicFinsetReset F s) i =
      holomorphicFinsetReset F (insert i s) := by
  funext w
  unfold holomorphicCoordinateReset holomorphicFinsetReset
  apply congrArg F
  funext j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self, ite_self, Finset.mem_insert, true_or, ↓reduceIte]
  · simp only [ne_eq, hji, not_false_eq_true, Function.update_of_ne, Finset.mem_insert, false_or]

private theorem productRadialWeighted_integral_finset_reset
    {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (s : Finset (Fin n)) :
    (∫ w : TorusCharacters.LogSpace n,
      productRadialWeightedIntegrand F w) =
      ∫ w : TorusCharacters.LogSpace n,
        productRadialWeightedIntegrand
          (holomorphicFinsetReset F s) w := by
  induction s using Finset.induction_on with
  | empty =>
    rfl
  | @insert i s hi ih =>
    calc
      (∫ w : TorusCharacters.LogSpace n,
        productRadialWeightedIntegrand F w) =
        ∫ w : TorusCharacters.LogSpace n,
          productRadialWeightedIntegrand
            (holomorphicFinsetReset F s) w := ih
      _ = ∫ w : TorusCharacters.LogSpace n,
          productRadialWeightedIntegrand
            (holomorphicCoordinateReset
              (holomorphicFinsetReset F s) i) w :=
        productRadialWeighted_integral_coordinate_reset
          (differentiable_holomorphicFinsetReset hF s) i
      _ = ∫ w : TorusCharacters.LogSpace n,
          productRadialWeightedIntegrand
            (holomorphicFinsetReset F (insert i s)) w := by
        rw [holomorphicCoordinateReset_finsetReset]

private theorem productRadialWeighted_holomorphic_integral
    {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F) :
    (∫ w : TorusCharacters.LogSpace n,
      productRadialWeightedIntegrand F w) =
      productRadialKernelMass n • F 0 := by
  have hreset :=
    productRadialWeighted_integral_finset_reset hF
      (Finset.univ : Finset (Fin n))
  have hone :
      holomorphicFinsetReset F (Finset.univ : Finset (Fin n)) =
        (fun _ : TorusCharacters.LogSpace n => F 0) := by
    funext w
    unfold holomorphicFinsetReset
    congr 1
    funext i
    simp only [Finset.mem_univ, ↓reduceIte, Pi.zero_apply]
  calc
    (∫ w : TorusCharacters.LogSpace n,
      productRadialWeightedIntegrand F w) =
      ∫ w : TorusCharacters.LogSpace n,
        productRadialWeightedIntegrand
          (fun _ : TorusCharacters.LogSpace n => F 0) w := by
      rw [← hone]
      exact hreset
    _ = (∫ w : TorusCharacters.LogSpace n,
          (productRadialKernel w : ℂ)) * F 0 :=
      MeasureTheory.integral_mul_const _ _
    _ = (productRadialKernelMass n : ℂ) * F 0 := by
      apply congrArg (fun a : ℂ => a * F 0)
      exact integral_complex_ofReal
        (f := productRadialKernel (n := n))
    _ = productRadialKernelMass n • F 0 := by
      rw [Complex.real_smul]

private theorem normalizedProductRadial_holomorphic_integral
    {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (z : TorusCharacters.LogSpace n) :
    (∫ w : TorusCharacters.LogSpace n,
      normalizedProductRadialKernel w • F (z - w)) = F z := by
  let G : TorusCharacters.LogSpace n → ℂ :=
    fun w => F (z - w)
  have hG : Differentiable ℂ G := by
    dsimp [G]
    apply hF.comp
    fun_prop
  have hmass : (productRadialKernelMass n : ℂ) ≠ 0 := by
    exact_mod_cast (productRadialKernelMass_pos n).ne'
  have hpoint (w : TorusCharacters.LogSpace n) :
      normalizedProductRadialKernel w • F (z - w) =
        (productRadialKernelMass n : ℂ)⁻¹ *
          productRadialWeightedIntegrand G w := by
    simp only [normalizedProductRadialKernel,
      productRadialWeightedIntegrand, Complex.real_smul,
      div_eq_mul_inv]
    push_cast
    dsimp [G]
    ring
  calc
    (∫ w : TorusCharacters.LogSpace n,
      normalizedProductRadialKernel w • F (z - w)) =
      ∫ w : TorusCharacters.LogSpace n,
        (productRadialKernelMass n : ℂ)⁻¹ *
          productRadialWeightedIntegrand G w := by
        apply integral_congr_ae
        filter_upwards [] with w
        exact hpoint w
    _ = (productRadialKernelMass n : ℂ)⁻¹ *
          (∫ w : TorusCharacters.LogSpace n,
            productRadialWeightedIntegrand G w) :=
        MeasureTheory.integral_const_mul _ _
    _ = (productRadialKernelMass n : ℂ)⁻¹ *
          (productRadialKernelMass n • G 0) := by
        rw [productRadialWeighted_holomorphic_integral hG]
    _ = F z := by
        dsimp [G]
        simp only [sub_zero, ne_eq, hmass, not_false_eq_true, inv_mul_cancel_left₀]

private theorem productRadialHolomorphicMollification_eq_of_differentiable
    {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F) :
    productRadialHolomorphicMollification F = F := by
  funext z
  unfold productRadialHolomorphicMollification
  rw [MeasureTheory.convolution_def]
  change
    (∫ w : TorusCharacters.LogSpace n,
      normalizedProductRadialKernel w • F (z - w)) = F z
  exact normalizedProductRadial_holomorphic_integral hF z

end WeightedTorusWeylRadialIntegrationBridge

namespace WeightedTorusWeylWeakRepresentativeBridge

open Set Function MeasureTheory Filter
open scoped BigOperators ContDiff Convolution ENNReal InnerProductSpace Topology

open WeightedBrascampSaturation DolbeaultRegularity ComplexKillingSaturationBridge
open DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge
open WeightedTorusClosedGraphWeakBridge WeightedTorusWeylRepresentativeBridge
open WeightedTorusWeylRadialIntegrationBridge

private theorem complexCover_hasCompactSupport_norm {n : ℕ}
    {κ : TorusCharacters.LogSpace n → ℝ}
    (hκ : HasCompactSupport κ) :
    HasCompactSupport (fun z => ‖κ z‖) := by
  refine hκ.mono ?_
  intro z hz
  change ‖κ z‖ ≠ 0 at hz
  change κ z ≠ 0
  intro hzero
  apply hz
  simp only [hzero, norm_zero]

private theorem complexCover_locallyIntegrable_norm {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n))) :
    LocallyIntegrable (fun z => ‖g z‖)
      (volume : Measure (TorusCharacters.LogSpace n)) := by
  exact locallyIntegrableOn_univ.mp
    ((hg.locallyIntegrableOn Set.univ).norm)

private theorem complexCover_hasCompactSupport_normConvolution {n : ℕ}
    {κ η : TorusCharacters.LogSpace n → ℝ}
    (hκ : HasCompactSupport κ) (hη : HasCompactSupport η) :
    HasCompactSupport
      ((fun z => ‖κ z‖)
        ⋆[ContinuousLinearMap.mul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))]
            (fun z => ‖η z‖)) := by
  exact (complexCover_hasCompactSupport_norm hκ).convolution
    (ContinuousLinearMap.mul ℝ ℝ)
    (complexCover_hasCompactSupport_norm hη)

private theorem complexCover_continuous_normConvolution {n : ℕ}
    {κ η : TorusCharacters.LogSpace n → ℝ}
    (hκcont : Continuous κ) (hκcompact : HasCompactSupport κ)
    (hηcont : Continuous η) (hηcompact : HasCompactSupport η) :
    Continuous
      ((fun z => ‖κ z‖)
        ⋆[ContinuousLinearMap.mul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))]
            (fun z => ‖η z‖)) := by
  have hκint : Integrable κ
      (volume : Measure (TorusCharacters.LogSpace n)) :=
    hκcont.integrable_of_hasCompactSupport hκcompact
  exact (complexCover_hasCompactSupport_norm hηcompact).continuous_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ)
    hκint.norm.locallyIntegrable hηcont.norm

private theorem complexReal_compactKernel_convolution_assoc {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    {κ η : TorusCharacters.LogSpace n → ℝ}
    (hκcont : Continuous κ) (hκcompact : HasCompactSupport κ)
    (hηcont : Continuous η) (hηcompact : HasCompactSupport η)
    (z : TorusCharacters.LogSpace n) :
    ((g ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))] κ)
      ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))] η) z =
      (g ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))]
        (κ ⋆[ContinuousLinearMap.mul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))] η)) z := by
  have hκint : Integrable κ
      (volume : Measure (TorusCharacters.LogSpace n)) :=
    hκcont.integrable_of_hasCompactSupport hκcompact
  have hηint : Integrable η
      (volume : Measure (TorusCharacters.LogSpace n)) :=
    hηcont.integrable_of_hasCompactSupport hηcompact
  refine MeasureTheory.convolution_assoc
    complexRealMultiplication complexRealMultiplication
    complexRealMultiplication (ContinuousLinearMap.mul ℝ ℝ)
    ?_ hg.aestronglyMeasurable hκcont.aestronglyMeasurable
    hηcont.aestronglyMeasurable ?_ ?_ ?_
  · intro w a b
    change (b : ℂ) * ((a : ℂ) * w) =
      ((a * b : ℝ) : ℂ) * w
    push_cast
    ring
  · exact Filter.Eventually.of_forall
      (hκcompact.convolutionExists_right
        complexRealMultiplication hg hκcont)
  · exact hκint.norm.ae_convolution_exists
      (ContinuousLinearMap.mul ℝ ℝ) hηint.norm
  · exact (complexCover_hasCompactSupport_normConvolution
      hκcompact hηcompact).convolutionExists_right
        (ContinuousLinearMap.mul ℝ ℝ)
        (complexCover_locallyIntegrable_norm hg)
        (complexCover_continuous_normConvolution
          hκcont hκcompact hηcont hηcompact) z

private theorem complexCover_real_convolution_comm {n : ℕ}
    (κ η : TorusCharacters.LogSpace n → ℝ) :
    (κ ⋆[ContinuousLinearMap.mul ℝ ℝ,
      (volume : Measure (TorusCharacters.LogSpace n))] η) =
      (η ⋆[ContinuousLinearMap.mul ℝ ℝ,
        (volume : Measure (TorusCharacters.LogSpace n))] κ) := by
  have h := MeasureTheory.convolution_flip
    (μ := (volume : Measure (TorusCharacters.LogSpace n)))
    (f := η) (g := κ) (ContinuousLinearMap.mul ℝ ℝ)
  rw [ContinuousLinearMap.flip_mul] at h
  exact h

private theorem complexReal_compactKernel_convolution_commute {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    {κ η : TorusCharacters.LogSpace n → ℝ}
    (hκcont : Continuous κ) (hκcompact : HasCompactSupport κ)
    (hηcont : Continuous η) (hηcompact : HasCompactSupport η)
    (z : TorusCharacters.LogSpace n) :
    ((g ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))] κ)
      ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))] η) z =
      ((g ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))] η)
      ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))] κ) z := by
  calc
    _ = (g ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))]
        (κ ⋆[ContinuousLinearMap.mul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))] η)) z :=
      complexReal_compactKernel_convolution_assoc hg
        hκcont hκcompact hηcont hηcompact z
    _ = (g ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))]
        (η ⋆[ContinuousLinearMap.mul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))] κ)) z := by
      rw [complexCover_real_convolution_comm κ η]
    _ = _ := (complexReal_compactKernel_convolution_assoc hg
      hηcont hηcompact hκcont hκcompact z).symm

private theorem normalizedShrinkingConvolution_eq_radialRepresentativeConvolution
    {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    (hweak : (∀ weakTest, ContDiff ℝ 1 weakTest → HasCompactSupport weakTest →
      ∀ weakCoordinate,
        (∫ weakPoint, g weakPoint *
          coverBarPartialTest weakTest weakCoordinate weakPoint) = 0))
    (m : ℕ) (z : TorusCharacters.LogSpace n) :
    (((complexShrinkingBump (n := n) m).normed
        (volume : Measure (TorusCharacters.LogSpace n)))
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        (volume : Measure (TorusCharacters.LogSpace n))] g) z =
      (((complexShrinkingBump (n := n) m).normed
          (volume : Measure (TorusCharacters.LogSpace n)))
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))]
            productRadialHolomorphicMollification g) z := by
  let κ : TorusCharacters.LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) m).normed
      (volume : Measure (TorusCharacters.LogSpace n))
  let η : TorusCharacters.LogSpace n → ℝ :=
    normalizedProductRadialKernel
  have hκcont : Continuous κ :=
    (complexShrinkingBump (n := n) m).continuous_normed
  have hκcompact : HasCompactSupport κ :=
    (complexShrinkingBump (n := n) m).hasCompactSupport_normed
  have hηcont : Continuous η :=
    (contDiff_normalizedProductRadialKernel n).continuous
  have hηcompact : HasCompactSupport η :=
    hasCompactSupport_normalizedProductRadialKernel n
  have hhol : Differentiable ℂ
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        (volume : Measure (TorusCharacters.LogSpace n))] g) := by
    exact differentiable_complex_normalizedShrinkingConvolution
      hg hweak m
  have hfix :
      (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        (volume : Measure (TorusCharacters.LogSpace n))]
        (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))] g)) z =
        (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))] g) z := by
    simpa only [η, productRadialHolomorphicMollification] using
      congrFun
        (productRadialHolomorphicMollification_eq_of_differentiable hhol) z
  have hcomm := complexReal_compactKernel_convolution_commute
    (κ := κ) (η := η) hg
    hκcont hκcompact hηcont hηcompact z
  have hcomm' :
      (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        (volume : Measure (TorusCharacters.LogSpace n))]
        (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))] g)) z =
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        (volume : Measure (TorusCharacters.LogSpace n))]
        (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))] g)) z := by
    simpa only [complex_convolution_flip] using hcomm
  change
    (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      (volume : Measure (TorusCharacters.LogSpace n))] g) z =
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        (volume : Measure (TorusCharacters.LogSpace n))]
          productRadialHolomorphicMollification g) z
  calc
    _ = (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        (volume : Measure (TorusCharacters.LogSpace n))]
        (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))] g)) z :=
      hfix.symm
    _ = (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        (volume : Measure (TorusCharacters.LogSpace n))]
        (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))] g)) z :=
      hcomm'
    _ = _ := rfl

private theorem productRadialHolomorphicMollification_ae_eq_of_weak
    {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    (hweak : (∀ weakTest, ContDiff ℝ 1 weakTest → HasCompactSupport weakTest →
      ∀ weakCoordinate,
        (∫ weakPoint, g weakPoint *
          coverBarPartialTest weakTest weakCoordinate weakPoint) = 0)) :
    productRadialHolomorphicMollification g =ᵐ[
      (volume : Measure (TorusCharacters.LogSpace n))] g := by
  have hhol := differentiable_productRadialHolomorphicMollification
    hg hweak
  filter_upwards [ae_tendsto_normalized_holomorphic_mollifications hg]
    with z hz
  have hradial : Tendsto
      (fun m : ℕ =>
        (((complexShrinkingBump (n := n) m).normed
            (volume : Measure (TorusCharacters.LogSpace n)))
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
            (volume : Measure (TorusCharacters.LogSpace n))]
              productRadialHolomorphicMollification g) z)
      atTop (nhds (productRadialHolomorphicMollification g z)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous
      (complexShrinkingBump_rOut_tendsto (n := n)) hhol.continuous z
  have hto_g : Tendsto
      (fun m : ℕ =>
        (((complexShrinkingBump (n := n) m).normed
            (volume : Measure (TorusCharacters.LogSpace n)))
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
            (volume : Measure (TorusCharacters.LogSpace n))]
              productRadialHolomorphicMollification g) z)
      atTop (nhds (g z)) := by
    exact hz.congr' (Filter.Eventually.of_forall fun m =>
      normalizedShrinkingConvolution_eq_radialRepresentativeConvolution
        hg hweak m z)
  exact tendsto_nhds_unique hradial hto_g

private theorem exists_periodic_holomorphic_representative_of_weak_barPartial
    {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    (hweak : (∀ weakTest, ContDiff ℝ 1 weakTest → HasCompactSupport weakTest →
      ∀ weakCoordinate,
        (∫ weakPoint, g weakPoint *
          coverBarPartialTest weakTest weakCoordinate weakPoint) = 0))
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic g (TorusCharacters.imaginaryShift q)) :
    ∃ F : TorusCharacters.LogSpace n → ℂ,
      Differentiable ℂ F ∧
        (∀ q : Fin n → ℤ,
          Function.Periodic F
            (TorusCharacters.imaginaryShift q)) ∧
        F =ᵐ[(volume : Measure
          (TorusCharacters.LogSpace n))] g := by
  refine ⟨productRadialHolomorphicMollification g,
    differentiable_productRadialHolomorphicMollification hg hweak,
    ?_, productRadialHolomorphicMollification_ae_eq_of_weak hg hweak⟩
  intro q
  exact productRadialHolomorphicMollification_periodic (hperiod q)

private theorem weightedZeroGraph_exists_periodic_holomorphic_representative
    {n k : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    (f : weightedTorusScalarL2 k φ)
    (hf : WithLp.toLp 2
      (f, (0 : weightedTorusFormL2 k φ)) ∈
        functionDolbeaultGraph k φ) :
    ∃ F : TorusCharacters.LogSpace n → ℂ,
      Differentiable ℂ F ∧
        (∀ q : Fin n → ℤ,
          Function.Periodic F
            (TorusCharacters.imaginaryShift q)) ∧
        F =ᵐ[(volume : Measure
          (TorusCharacters.LogSpace n))]
          complexTorusCoverLift
            (fun p : WeightedTorusHilbert.LogTorus n => f p) := by
  apply exists_periodic_holomorphic_representative_of_weak_barPartial
    (weightedScalarL2_complexTorusCoverLift_locallyIntegrable hφ f)
    (weightedZeroGraph_hasWeakBarPartialZero hφ f hf)
  intro q
  exact complexTorusCoverLift_periodic
    (fun p : WeightedTorusHilbert.LogTorus n => f p) q

end WeightedTorusWeylWeakRepresentativeBridge

namespace ComplexMatrixWeightedHilbert

open Set Function MeasureTheory Filter Matrix
open scoped BigOperators ContDiff Convolution ENNReal InnerProductSpace
  MatrixOrder Matrix.Norms.L2Operator Topology

private def sourceMatrixHessian {n : ℕ}
    (φ : Space n → ℝ) :
    Space n → Matrix (Fin n) (Fin n) ℝ :=
  BergmanAsymptotics.actualHessianMatrix φ

end ComplexMatrixWeightedHilbert

namespace MatrixTorusBochnerBridge

open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert EqualitySaturatingKillingPaths WeightedTorusDistributionBridge
open WeightedDolbeaultBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

private def angularSmoothPartitionBump (t : ℝ) : ℝ :=
  Real.smoothTransition (t + 1) - Real.smoothTransition t

private theorem contDiff_angularSmoothPartitionBump {m : ℕ∞} :
    ContDiff ℝ m angularSmoothPartitionBump := by
  unfold angularSmoothPartitionBump
  exact (Real.smoothTransition.contDiff.comp
    (contDiff_id.add contDiff_const)).sub
      Real.smoothTransition.contDiff

private theorem angularSmoothPartitionBump_nonneg (t : ℝ) :
    0 ≤ angularSmoothPartitionBump t := by
  unfold angularSmoothPartitionBump
  exact sub_nonneg.mpr
    (Real.smoothTransition.monotone (by linarith))

private theorem angularSmoothPartitionBump_zero_of_le
    {t : ℝ} (ht : t ≤ -1) :
    angularSmoothPartitionBump t = 0 := by
  unfold angularSmoothPartitionBump
  rw [Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith),
    sub_zero]

private theorem angularSmoothPartitionBump_zero_of_ge
    {t : ℝ} (ht : 1 ≤ t) :
    angularSmoothPartitionBump t = 0 := by
  unfold angularSmoothPartitionBump
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le ht,
    sub_self]

private theorem angularSmoothPartitionBump_add_translate
    {t : ℝ} (hzero : 0 ≤ t) (hone : t ≤ 1) :
    angularSmoothPartitionBump t +
      angularSmoothPartitionBump (t - 1) = 1 := by
  have hplus : Real.smoothTransition (t + 1) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  have hminus : Real.smoothTransition (t - 1) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have ht : t - 1 + 1 = t := by ring
  unfold angularSmoothPartitionBump
  rw [hplus, ht, hminus]
  ring

private def angularSmoothPartition {n : ℕ} (t : Space n) : ℝ :=
  ∏ i : Fin n, angularSmoothPartitionBump (t i)

private theorem contDiff_angularSmoothPartition
    {n : ℕ} {m : ℕ∞} :
    ContDiff ℝ m (angularSmoothPartition (n := n)) := by
  unfold angularSmoothPartition
  apply contDiff_prod
  intro i _
  apply contDiff_angularSmoothPartitionBump.comp
  fun_prop

private theorem angularSmoothPartition_nonneg
    {n : ℕ} (t : Space n) :
    0 ≤ angularSmoothPartition t := by
  unfold angularSmoothPartition
  exact Finset.prod_nonneg
    (fun i _ => angularSmoothPartitionBump_nonneg (t i))

private theorem hasCompactSupport_angularSmoothPartition
    {n : ℕ} :
    HasCompactSupport (angularSmoothPartition (n := n)) := by
  let Q : Set (Space n) :=
    Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1)
  have hQ : IsCompact Q :=
    isCompact_univ_pi (fun _ : Fin n => isCompact_Icc)
  apply hQ.of_isClosed_subset
    (isClosed_tsupport (angularSmoothPartition (n := n)))
  apply closure_minimal
  · intro t ht
    change angularSmoothPartition t ≠ 0 at ht
    intro i _
    have hi : angularSmoothPartitionBump (t i) ≠ 0 := by
      intro hz
      apply ht
      unfold angularSmoothPartition
      exact Finset.prod_eq_zero (Finset.mem_univ i) hz
    constructor
    · by_contra hn
      exact hi (angularSmoothPartitionBump_zero_of_le
        (le_of_lt (lt_of_not_ge hn)))
    · by_contra hn
      exact hi (angularSmoothPartitionBump_zero_of_ge
        (le_of_lt (lt_of_not_ge hn)))
  · exact hQ.isClosed

private theorem angularSmoothPartition_binary_sum
    {n : ℕ} (t : Space n)
    (hzero : ∀ i : Fin n, 0 ≤ t i)
    (hone : ∀ i : Fin n, t i ≤ 1) :
    (∑ q : Fin n → Bool,
      angularSmoothPartition
        (fun i => t i - if q i then (1 : ℝ) else 0)) = 1 := by
  classical
  calc
    _ = ∑ q : Fin n → Bool,
      ∏ i : Fin n,
        angularSmoothPartitionBump
          (t i - if q i then (1 : ℝ) else 0) := rfl
    _ = ∏ i : Fin n, ∑ b : Bool,
      angularSmoothPartitionBump
        (t i - if b then (1 : ℝ) else 0) :=
      (Fintype.prod_sum
        (fun (i : Fin n) (b : Bool) =>
          angularSmoothPartitionBump
            (t i - if b then (1 : ℝ) else 0))).symm
    _ = 1 := by
      apply Finset.prod_eq_one
      intro i _
      simpa only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
        Finset.sum_insert, ↓reduceIte, Finset.sum_singleton, Bool.false_eq_true, sub_zero,
        add_comm] using
        angularSmoothPartitionBump_add_translate
          (hzero i) (hone i)

private theorem continuous_angularCoverProjection
    (n : ℕ) :
    Continuous (angularCoverProjection n) := by
  unfold angularCoverProjection
  fun_prop

private def binaryAngularFundamentalBase {n : ℕ}
    (q : Fin n → Bool) : Space n :=
  fun i => if q i then (-1 : ℝ) else 0

private theorem measurableSet_angularFundamentalBox
    {n : ℕ} (b : Space n) :
    MeasurableSet (angularFundamentalBox b) := by
  unfold angularFundamentalBox
  exact MeasurableSet.univ_pi'
    (fun i : Fin n => measurableSet_Ioc)

private theorem iUnion_binaryAngularFundamentalBox
    (n : ℕ) :
    (⋃ q : Fin n → Bool,
      angularFundamentalBox (binaryAngularFundamentalBase q)) =
      Set.univ.pi (fun _ : Fin n => Set.Ioc (-1 : ℝ) 1) := by
  classical
  ext t
  constructor
  · intro ht
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp ht
    intro i _
    have hi := hq i
    change
      t i ∈ Set.Ioc
        (if q i then (-1 : ℝ) else 0)
        ((if q i then (-1 : ℝ) else 0) + 1) at hi
    change (-1 : ℝ) < t i ∧ t i ≤ 1
    cases hqi : q i
    · simp only [hqi, Bool.false_eq_true, ↓reduceIte, zero_add, mem_Ioc] at hi
      exact ⟨by linarith [hi.1], hi.2⟩
    · simp only [hqi, ↓reduceIte, neg_add_cancel, mem_Ioc] at hi
      exact ⟨hi.1, by linarith [hi.2]⟩
  · intro ht
    let q : Fin n → Bool := fun i => decide (t i ≤ 0)
    apply Set.mem_iUnion.mpr
    refine ⟨q, ?_⟩
    intro i
    have hi := ht i (Set.mem_univ i)
    change
      t i ∈ Set.Ioc
        (if q i then (-1 : ℝ) else 0)
        ((if q i then (-1 : ℝ) else 0) + 1)
    by_cases hzero : t i ≤ 0
    · have hq : q i = true := by
        simp only [hzero, decide_true, q]
      rw [hq]
      simpa only [↓reduceIte, neg_add_cancel, mem_Ioc] using
        (show (-1 : ℝ) < t i ∧ t i ≤ 0 from ⟨hi.1, hzero⟩)
    · have hq : q i = false := by
        simp only [hzero, decide_false, q]
      rw [hq]
      simpa only [Bool.false_eq_true, ↓reduceIte, zero_add, mem_Ioc] using
        (show 0 < t i ∧ t i ≤ (1 : ℝ) from
          ⟨lt_of_not_ge hzero, hi.2⟩)

private theorem pairwiseDisjoint_binaryAngularFundamentalBox
    (n : ℕ) :
    Pairwise
      (Disjoint on
        (fun q : Fin n → Bool =>
          angularFundamentalBox (binaryAngularFundamentalBase q))) := by
  classical
  intro q r hqr
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hqr
  apply Set.disjoint_left.mpr
  intro t hq hr
  have hqi := hq i
  have hri := hr i
  change
    t i ∈ Set.Ioc
      (if q i then (-1 : ℝ) else 0)
      ((if q i then (-1 : ℝ) else 0) + 1) at hqi
  change
    t i ∈ Set.Ioc
      (if r i then (-1 : ℝ) else 0)
      ((if r i then (-1 : ℝ) else 0) + 1) at hri
  cases hqval : q i <;> cases hrval : r i <;>
    simp_all [Set.mem_Ioc] <;> linarith

private theorem binaryAngularFundamentalBox_eq_translate
    {n : ℕ} (q : Fin n → Bool) :
    (fun t : Space n =>
      binaryAngularFundamentalBase q + t) ''
        angularFundamentalBox (0 : Space n) =
      angularFundamentalBox (binaryAngularFundamentalBase q) := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    intro i
    have hi : 0 < u i ∧ u i ≤ (1 : ℝ) := by
      simpa only [Pi.zero_apply, zero_add, mem_Ioc] using hu i
    change
      binaryAngularFundamentalBase q i <
        binaryAngularFundamentalBase q i + u i ∧
      binaryAngularFundamentalBase q i + u i ≤
        binaryAngularFundamentalBase q i + 1
    constructor <;> linarith
  · intro ht
    refine ⟨t - binaryAngularFundamentalBase q, ?_, ?_⟩
    · intro i
      have hi := ht i
      change
        binaryAngularFundamentalBase q i < t i ∧
        t i ≤ binaryAngularFundamentalBase q i + 1 at hi
      have hp :
          0 < t i - binaryAngularFundamentalBase q i ∧
            t i - binaryAngularFundamentalBase q i ≤ (1 : ℝ) := by
        constructor <;> linarith
      simpa only [Pi.zero_apply, zero_add, Pi.sub_apply, mem_Ioc, sub_pos, tsub_le_iff_right]
        using hp
    · funext i
      change
        binaryAngularFundamentalBase q i +
          (t i - binaryAngularFundamentalBase q i) = t i
      ring

private theorem integral_angularSmoothPartition_eq_fundamental
    {n : ℕ} {g : Space n → ℂ}
    (hg : Continuous g)
    (hperiod : ∀ (q : Fin n → Bool) (t : Space n),
      g (binaryAngularFundamentalBase q + t) = g t) :
    (∫ t : Space n,
      (angularSmoothPartition t : ℂ) * g t
      ∂(volume : Measure (Space n))) =
    ∫ t : Space n
      in angularFundamentalBox (0 : Space n), g t
      ∂(volume : Measure (Space n)) := by
  classical
  let f : Space n → ℂ :=
    fun t => (angularSmoothPartition t : ℂ) * g t
  have hfc : Continuous f :=
    (Complex.continuous_ofReal.comp
      (contDiff_angularSmoothPartition
        (n := n) (m := 1)).continuous).mul hg
  have hfs : HasCompactSupport f := by
    apply hasCompactSupport_angularSmoothPartition.mono
    intro t ht
    change (angularSmoothPartition t : ℂ) * g t ≠ 0 at ht
    intro hz
    apply ht
    simp only [hz, Complex.ofReal_zero, zero_mul]
  have hf : Integrable f
      (volume : Measure (Space n)) :=
    hfc.integrable_of_hasCompactSupport hfs
  let U : Set (Space n) :=
    ⋃ q : Fin n → Bool,
      angularFundamentalBox (binaryAngularFundamentalBase q)
  have houtside : ∀ t : Space n, t ∉ U → f t = 0 := by
    intro t ht
    have hcube :
        t ∉ Set.univ.pi
          (fun _ : Fin n => Set.Ioc (-1 : ℝ) 1) := by
      rw [← iUnion_binaryAngularFundamentalBox n]
      exact ht
    have hnot :
        ¬ ∀ i : Fin n, (-1 : ℝ) < t i ∧ t i ≤ 1 := by
      intro h
      apply hcube
      intro i _
      exact h i
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hbump : angularSmoothPartitionBump (t i) = 0 := by
      by_cases hleft : t i ≤ -1
      · exact angularSmoothPartitionBump_zero_of_le hleft
      · have hright : 1 < t i := by
          by_contra hn
          apply hi
          exact ⟨lt_of_not_ge hleft, le_of_not_gt hn⟩
        exact angularSmoothPartitionBump_zero_of_ge hright.le
    have hzero : angularSmoothPartition t = 0 := by
      unfold angularSmoothPartition
      exact Finset.prod_eq_zero (Finset.mem_univ i) hbump
    simp only [hzero, Complex.ofReal_zero, zero_mul, f]
  have htranslate (q : Fin n → Bool) :
      (∫ t : Space n
        in angularFundamentalBox (binaryAngularFundamentalBase q),
        f t ∂(volume : Measure (Space n))) =
      ∫ t : Space n
        in angularFundamentalBox (0 : Space n),
        f (binaryAngularFundamentalBase q + t)
          ∂(volume : Measure (Space n)) := by
    have h :=
      (MeasureTheory.measurePreserving_add_left
        (volume : Measure (Space n))
        (binaryAngularFundamentalBase q)).setIntegral_image_emb
          (measurableEmbedding_addLeft
            (binaryAngularFundamentalBase q))
          f (angularFundamentalBox (0 : Space n))
    rwa [binaryAngularFundamentalBox_eq_translate] at h
  have hshift (q : Fin n → Bool) :
      IntegrableOn
        (fun t : Space n =>
          f (binaryAngularFundamentalBase q + t))
        (angularFundamentalBox (0 : Space n))
        (volume : Measure (Space n)) := by
    have h :=
      (MeasureTheory.measurePreserving_add_left
        (volume : Measure (Space n))
        (binaryAngularFundamentalBase q)).integrable_comp_of_integrable hf
    exact (show Integrable
      (fun t : Space n =>
        f (binaryAngularFundamentalBase q + t))
      (volume : Measure (Space n)) by
        simpa only [comp_def] using h).integrableOn
  change (∫ t : Space n, f t
    ∂(volume : Measure (Space n))) = _
  calc
    _ = ∫ t : Space n in U, f t
        ∂(volume : Measure (Space n)) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero houtside).symm
    _ = ∑ q : Fin n → Bool,
      ∫ t : Space n
        in angularFundamentalBox (binaryAngularFundamentalBase q),
        f t ∂(volume : Measure (Space n)) := by
      exact MeasureTheory.integral_iUnion_fintype
        (fun q => measurableSet_angularFundamentalBox
          (binaryAngularFundamentalBase q))
        (pairwiseDisjoint_binaryAngularFundamentalBox n)
        (fun q => hf.integrableOn)
    _ = ∑ q : Fin n → Bool,
      ∫ t : Space n
        in angularFundamentalBox (0 : Space n),
        f (binaryAngularFundamentalBase q + t)
          ∂(volume : Measure (Space n)) := by
      refine Finset.sum_congr rfl ?_
      intro q _
      exact htranslate q
    _ = ∫ t : Space n
        in angularFundamentalBox (0 : Space n),
        ∑ q : Fin n → Bool,
          f (binaryAngularFundamentalBase q + t)
        ∂(volume : Measure (Space n)) := by
      symm
      exact MeasureTheory.integral_finsetSum Finset.univ
        (fun q _ => hshift q)
    _ = _ := by
      apply MeasureTheory.setIntegral_congr_fun
        (measurableSet_angularFundamentalBox
          (0 : Space n))
      intro t ht
      have ht0 : ∀ i : Fin n, 0 ≤ t i := by
        intro i
        have h := ht i
        have h' : 0 < t i ∧ t i ≤ (1 : ℝ) := by
          simpa only [Pi.zero_apply, zero_add, mem_Ioc] using h
        exact h'.1.le
      have ht1 : ∀ i : Fin n, t i ≤ 1 := by
        intro i
        have h := ht i
        have h' : 0 < t i ∧ t i ≤ (1 : ℝ) := by
          simpa only [Pi.zero_apply, zero_add, mem_Ioc] using h
        exact h'.2
      have hsum :
          (∑ q : Fin n → Bool,
            angularSmoothPartition
              (binaryAngularFundamentalBase q + t)) = 1 := by
        calc
          _ = ∑ q : Fin n → Bool,
            angularSmoothPartition
              (fun i => t i - if q i then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro q _
            congr 1
            funext i
            simp only [Pi.add_apply,
              binaryAngularFundamentalBase]
            split <;> ring
          _ = 1 := angularSmoothPartition_binary_sum t ht0 ht1
      have hcomplex :
          (∑ q : Fin n → Bool,
            (angularSmoothPartition
              (binaryAngularFundamentalBase q + t) : ℂ)) = 1 := by
        exact_mod_cast hsum
      change
        (∑ q : Fin n → Bool,
          (angularSmoothPartition
            (binaryAngularFundamentalBase q + t) : ℂ) *
            g (binaryAngularFundamentalBase q + t)) = g t
      simp_rw [hperiod]
      rw [← Finset.sum_mul, hcomplex, one_mul]

private theorem angularFundamental_integral_eq_haar
    {n : ℕ}
    {g : TorusCharacters.AngularTorus n → ℂ}
    (hg : Continuous g) :
    (∫ t : Space n
      in angularFundamentalBox (0 : Space n),
      g (angularCoverProjection n t)
      ∂(volume : Measure (Space n))) =
      ∫ θ : TorusCharacters.AngularTorus n,
        g θ ∂(angularMeasure n) := by
  let μ : Measure (Space n) :=
    (volume : Measure (Space n)).restrict
      (angularFundamentalBox (0 : Space n))
  have hp :=
    angularCoverProjection_measurePreserving (0 : Space n)
  change
    (∫ t : Space n,
      g (angularCoverProjection n t) ∂μ) = _
  calc
    _ = ∫ θ : TorusCharacters.AngularTorus n,
      g θ ∂(Measure.map (angularCoverProjection n) μ) := by
      exact (MeasureTheory.integral_map
        hp.measurable.aemeasurable
        hg.aestronglyMeasurable).symm
    _ = _ := by rw [hp.map_eq]

private theorem integral_angularSmoothPartition_eq_angularHaar
    {n : ℕ}
    {g : TorusCharacters.AngularTorus n → ℂ}
    (hg : Continuous g) :
    (∫ t : Space n,
      (angularSmoothPartition t : ℂ) *
        g (angularCoverProjection n t)
      ∂(volume : Measure (Space n))) =
      ∫ θ : TorusCharacters.AngularTorus n,
        g θ ∂(angularMeasure n) := by
  have hcont :
      Continuous (fun t : Space n =>
        g (angularCoverProjection n t)) :=
    hg.comp (continuous_angularCoverProjection n)
  have hperiod :
      ∀ (q : Fin n → Bool) (t : Space n),
        g (angularCoverProjection n
          (binaryAngularFundamentalBase q + t)) =
        g (angularCoverProjection n t) := by
    intro q t
    apply congrArg g
    let u : Fin n → ℤ :=
      fun i => if q i then (-1 : ℤ) else 0
    have heq :
        binaryAngularFundamentalBase q + t =
          fun i : Fin n => t i + (u i : ℝ) := by
      funext i
      simp only [Pi.add_apply,
        binaryAngularFundamentalBase, u]
      split <;> simp ; ring
    rw [heq, angularCoverProjection_integer_add]
  calc
    _ = ∫ t : Space n
      in angularFundamentalBox (0 : Space n),
      g (angularCoverProjection n t)
      ∂(volume : Measure (Space n)) :=
      integral_angularSmoothPartition_eq_fundamental hcont hperiod
    _ = _ := angularFundamental_integral_eq_haar hg

private theorem weightedRealDerivative_integration_by_parts_compact_right
    {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 1 a)
    (hF : ContDiff ℝ 1 F)
    (hG : ContDiff ℝ 1 G)
    (hGcompact : HasCompactSupport G)
    (v : TorusCharacters.LogSpace n) :
    (∫ z : TorusCharacters.LogSpace n,
      weightedRealDerivative a F v z * G z
      ∂(coverWeightedMeasure a)) =
    -(∫ z : TorusCharacters.LogSpace n,
      F z * (fderiv ℝ G z) v
      ∂(coverWeightedMeasure a)) := by
  let E := TorusCharacters.LogSpace n
  let μ : Measure E := coverWeightedMeasure a
  have hplain : Integrable
      (fun z : E => (fderiv ℝ F z) v * G z) μ :=
    integrable_fderiv_mul_coverWeightedMeasure
      ha hF hG hGcompact v
  have hpot : Integrable
      (fun z : E =>
        (F z * ((fderiv ℝ a z) v : ℂ)) * G z) μ := by
    apply integrable_of_continuous_compact_cover ha.continuous
      ((hF.continuous.mul
        (Complex.continuous_ofReal.comp
          ((ha.continuous_fderiv (by simp only [ne_eq, one_ne_zero, not_false_eq_true])).clm_apply
            continuous_const))).mul hG.continuous)
    exact hGcompact.mul_left
  have hweighted : Integrable
      (fun z : E => F z * weightedRealDerivative a G v z) μ :=
    integrable_mul_weightedRealDerivative_coverWeightedMeasure
      ha hF hG hGcompact v
  have hparts := weighted_complex_coordinate_integration_by_parts
    ha hF hG hGcompact v
  change
    (∫ z : E, weightedRealDerivative a F v z * G z ∂μ) =
      -(∫ z : E, F z * (fderiv ℝ G z) v ∂μ)
  calc
    _ = ∫ z : E,
      ((fderiv ℝ F z) v * G z -
        (F z * ((fderiv ℝ a z) v : ℂ)) * G z) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      unfold weightedRealDerivative
      ring
    _ = (∫ z : E, (fderiv ℝ F z) v * G z ∂μ) -
      (∫ z : E, (F z * ((fderiv ℝ a z) v : ℂ)) * G z ∂μ) :=
      MeasureTheory.integral_sub hplain hpot
    _ = -(∫ z : E, F z * weightedRealDerivative a G v z ∂μ) -
      (∫ z : E, (F z * ((fderiv ℝ a z) v : ℂ)) * G z ∂μ) := by
      rw [hparts]
    _ = -((∫ z : E, F z * weightedRealDerivative a G v z ∂μ) +
      (∫ z : E, (F z * ((fderiv ℝ a z) v : ℂ)) * G z ∂μ)) := by
      ring
    _ = -(∫ z : E,
      (F z * weightedRealDerivative a G v z +
        (F z * ((fderiv ℝ a z) v : ℂ)) * G z) ∂μ) :=
      congrArg Neg.neg
        (MeasureTheory.integral_add hweighted hpot).symm
    _ = _ := by
      apply congrArg Neg.neg
      apply integral_congr_ae
      filter_upwards [] with z
      unfold weightedRealDerivative
      ring

private theorem conj_barPartialCoordinate_eq_real_fderiv
    {n : ℕ}
    {G : TorusCharacters.LogSpace n → ℂ}
    (hG : ContDiff ℝ 1 G)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    conj (barPartialCoordinate G z j) =
      ((fderiv ℝ (fun w => conj (G w)) z)
          (Pi.single j (1 : ℂ)) -
        Complex.I *
          (fderiv ℝ (fun w => conj (G w)) z)
            (Pi.single j Complex.I)) / 2 := by
  rw [fderiv_conj (hG.differentiable (by simp only [ne_eq, one_ne_zero, not_false_eq_true])) z
    (Pi.single j (1 : ℂ)),
    fderiv_conj (hG.differentiable (by simp only [ne_eq, one_ne_zero, not_false_eq_true])) z
      (Pi.single j Complex.I)]
  unfold barPartialCoordinate
  simp only [map_div₀, map_add, map_mul,
    Complex.conj_I, map_ofNat]
  ring

private theorem weighted_holomorphic_hermitian_integration_by_parts_compact_right
    {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 1 a)
    (hF : ContDiff ℝ 1 F)
    (hG : ContDiff ℝ 1 G)
    (hGcompact : HasCompactSupport G)
    (j : Fin n) :
    (∫ z : TorusCharacters.LogSpace n,
      weightedHolomorphicDerivative a F j z * conj (G z)
      ∂(coverWeightedMeasure a)) =
    -(∫ z : TorusCharacters.LogSpace n,
      F z * conj (barPartialCoordinate G z j)
      ∂(coverWeightedMeasure a)) := by
  let E := TorusCharacters.LogSpace n
  let μ : Measure E := coverWeightedMeasure a
  let Gc : E → ℂ := fun z => conj (G z)
  let v₀ : E := Pi.single j (1 : ℂ)
  let v₁ : E := Pi.single j Complex.I
  have hGc : ContDiff ℝ 1 Gc :=
    Complex.conjCLE.contDiff.comp hG
  have hGccompact : HasCompactSupport Gc :=
    compactSupport_conj hGcompact
  have hL₀ : Integrable
      (fun z : E => weightedRealDerivative a F v₀ z * Gc z) μ := by
    apply integrable_of_continuous_compact_cover ha.continuous
      ((continuous_weightedRealDerivative ha hF v₀).mul
        hGc.continuous)
    exact hGccompact.mul_left
  have hL₁ : Integrable
      (fun z : E => weightedRealDerivative a F v₁ z * Gc z) μ := by
    apply integrable_of_continuous_compact_cover ha.continuous
      ((continuous_weightedRealDerivative ha hF v₁).mul
        hGc.continuous)
    exact hGccompact.mul_left
  have hR₀ : Integrable
      (fun z : E => F z * (fderiv ℝ Gc z) v₀) μ := by
    apply integrable_of_continuous_compact_cover ha.continuous
      (hF.continuous.mul
        ((hGc.continuous_fderiv (by simp only [ne_eq, one_ne_zero, not_false_eq_true])).clm_apply
          continuous_const))
    exact (hGccompact.fderiv_apply ℝ v₀).mul_left
  have hR₁ : Integrable
      (fun z : E => F z * (fderiv ℝ Gc z) v₁) μ := by
    apply integrable_of_continuous_compact_cover ha.continuous
      (hF.continuous.mul
        ((hGc.continuous_fderiv (by simp only [ne_eq, one_ne_zero, not_false_eq_true])).clm_apply
          continuous_const))
    exact (hGccompact.fderiv_apply ℝ v₁).mul_left
  have hLI :
      (∫ z : E,
        Complex.I * (weightedRealDerivative a F v₁ z * Gc z) ∂μ) =
      Complex.I *
        (∫ z : E,
          weightedRealDerivative a F v₁ z * Gc z ∂μ) :=
    MeasureTheory.integral_const_mul Complex.I
      (fun z : E => weightedRealDerivative a F v₁ z * Gc z)
  have hRI :
      (∫ z : E,
        Complex.I * (F z * (fderiv ℝ Gc z) v₁) ∂μ) =
      Complex.I *
        (∫ z : E, F z * (fderiv ℝ Gc z) v₁ ∂μ) :=
    MeasureTheory.integral_const_mul Complex.I
      (fun z : E => F z * (fderiv ℝ Gc z) v₁)
  have hleft :
      (∫ z : E,
        weightedHolomorphicDerivative a F j z * Gc z ∂μ) =
      ((∫ z : E,
        weightedRealDerivative a F v₀ z * Gc z ∂μ) -
        Complex.I *
          (∫ z : E,
            weightedRealDerivative a F v₁ z * Gc z ∂μ)) / 2 := by
    calc
      _ = ∫ z : E,
        (weightedRealDerivative a F v₀ z * Gc z -
          Complex.I *
            (weightedRealDerivative a F v₁ z * Gc z)) / 2
          ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [weightedHolomorphicDerivative_eq_real ha z j]
        change
          ((weightedRealDerivative a F v₀ z -
            Complex.I * weightedRealDerivative a F v₁ z) / 2) *
              Gc z = _
        ring
      _ = _ := by
        rw [MeasureTheory.integral_div,
          MeasureTheory.integral_sub hL₀
            (hL₁.const_mul Complex.I), hLI]
  have hright :
      (∫ z : E,
        F z * conj (barPartialCoordinate G z j) ∂μ) =
      ((∫ z : E, F z * (fderiv ℝ Gc z) v₀ ∂μ) -
        Complex.I *
          (∫ z : E, F z * (fderiv ℝ Gc z) v₁ ∂μ)) / 2 := by
    calc
      _ = ∫ z : E,
        (F z * (fderiv ℝ Gc z) v₀ -
          Complex.I *
            (F z * (fderiv ℝ Gc z) v₁)) / 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [conj_barPartialCoordinate_eq_real_fderiv hG z j]
        change
          F z *
            (((fderiv ℝ Gc z) v₀ -
              Complex.I * (fderiv ℝ Gc z) v₁) / 2) = _
        ring
      _ = _ := by
        rw [MeasureTheory.integral_div,
          MeasureTheory.integral_sub hR₀
            (hR₁.const_mul Complex.I), hRI]
  have hb₀ :=
    weightedRealDerivative_integration_by_parts_compact_right
      ha hF hGc hGccompact v₀
  have hb₁ :=
    weightedRealDerivative_integration_by_parts_compact_right
      ha hF hGc hGccompact v₁
  change
    (∫ z : E,
      weightedHolomorphicDerivative a F j z * Gc z ∂μ) =
      -(∫ z : E,
        F z * conj (barPartialCoordinate G z j) ∂μ)
  calc
    _ = ((∫ z : E,
        weightedRealDerivative a F v₀ z * Gc z ∂μ) -
        Complex.I *
          (∫ z : E,
            weightedRealDerivative a F v₁ z * Gc z ∂μ)) / 2 := hleft
    _ = -(((∫ z : E, F z * (fderiv ℝ Gc z) v₀ ∂μ) -
        Complex.I *
          (∫ z : E, F z * (fderiv ℝ Gc z) v₁ ∂μ)) / 2) := by
      rw [hb₀, hb₁]
      ring
    _ = _ := congrArg Neg.neg hright.symm

private theorem weighted_complex_bochner_coordinate_identity_compact_right
    {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 2 a)
    (hF : ContDiff ℝ 2 F)
    (hG : ContDiff ℝ 2 G)
    (hGcompact : HasCompactSupport G)
    (i j : Fin n) :
    (∫ z : TorusCharacters.LogSpace n,
      weightedHolomorphicDerivative a F i z *
        conj (weightedHolomorphicDerivative a G j z)
      ∂(coverWeightedMeasure a)) =
    ∫ z : TorusCharacters.LogSpace n,
      (barPartialCoordinate F z j *
        conj (barPartialCoordinate G z i) +
       (F z * complexHessian a z i j) * conj (G z))
      ∂(coverWeightedMeasure a) := by
  let E := TorusCharacters.LogSpace n
  let μ : Measure E := coverWeightedMeasure a
  have haone : ContDiff ℝ 1 a := ha.of_le (by norm_num)
  have hfone : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hgone : ContDiff ℝ 1 G := hG.of_le (by norm_num)
  have hFbar : ContDiff ℝ 1
      (fun z : E => barPartialCoordinate F z j) :=
    contDiff_barPartialCoordinate hF j
  have hGc : HasCompactSupport (fun z : E => conj (G z)) :=
    compactSupport_conj hGcompact
  have hfirst := weighted_barPartial_hermitian_integration_by_parts
    haone (contDiff_weightedHolomorphicDerivative ha hF i)
    hgone hGcompact j
  have hfirstrev :
      (∫ z : E,
        weightedHolomorphicDerivative a F i z *
          conj (weightedHolomorphicDerivative a G j z) ∂μ) =
      -(∫ z : E,
        barPartialCoordinate
          (fun w => weightedHolomorphicDerivative a F i w) z j *
            conj (G z) ∂μ) := by
    linear_combination hfirst
  have hsecond :=
    weighted_holomorphic_hermitian_integration_by_parts_compact_right
      haone hFbar hgone hGcompact i
  have hcore : Integrable
      (fun z : E =>
        weightedHolomorphicDerivative a
          (fun w => barPartialCoordinate F w j) i z * conj (G z)) μ := by
    apply integrable_of_continuous_compact_cover ha.continuous
      ((continuous_weightedHolomorphicDerivative haone hFbar i).mul
        (Complex.continuous_conj.comp hG.continuous))
    exact hGc.mul_left
  have hcurv : Integrable
      (fun z : E =>
        (F z * complexHessian a z i j) * conj (G z)) μ := by
    apply integrable_of_continuous_compact_cover ha.continuous
      ((hF.continuous.mul
        (continuous_complexHessian ha i j)).mul
          (Complex.continuous_conj.comp hG.continuous))
    exact hGc.mul_left
  have hcross : Integrable
      (fun z : E =>
        barPartialCoordinate F z j *
          conj (barPartialCoordinate G z i)) μ := by
    apply integrable_of_continuous_compact_cover ha.continuous
      ((continuous_barPartialCoordinate hfone j).mul
        (Complex.continuous_conj.comp
          (continuous_barPartialCoordinate hgone i)))
    exact (compactSupport_conj
      (compactSupport_barPartialCoordinate hGcompact i)).mul_left
  change
    (∫ z : E,
      weightedHolomorphicDerivative a F i z *
        conj (weightedHolomorphicDerivative a G j z) ∂μ) =
    ∫ z : E,
      (barPartialCoordinate F z j *
        conj (barPartialCoordinate G z i) +
       (F z * complexHessian a z i j) * conj (G z)) ∂μ
  calc
    _ = -(∫ z : E,
      barPartialCoordinate
        (fun w => weightedHolomorphicDerivative a F i w) z j *
          conj (G z) ∂μ) := hfirstrev
    _ = -(∫ z : E,
      (weightedHolomorphicDerivative a
          (fun w => barPartialCoordinate F w j) i z * conj (G z) -
        (F z * complexHessian a z i j) * conj (G z)) ∂μ) := by
      apply congrArg Neg.neg
      apply integral_congr_ae
      filter_upwards [] with z
      rw [barPartial_weightedHolomorphicDerivative_commutator
        ha hF z i j]
      ring
    _ = -((∫ z : E,
      weightedHolomorphicDerivative a
        (fun w => barPartialCoordinate F w j) i z * conj (G z) ∂μ) -
      (∫ z : E,
        (F z * complexHessian a z i j) * conj (G z) ∂μ)) := by
      rw [MeasureTheory.integral_sub hcore hcurv]
    _ = (∫ z : E,
      barPartialCoordinate F z j *
        conj (barPartialCoordinate G z i) ∂μ) +
      (∫ z : E,
        (F z * complexHessian a z i j) * conj (G z) ∂μ) := by
      rw [hsecond]
      ring
    _ = _ := (MeasureTheory.integral_add hcross hcurv).symm

private def matrixSourceCoverPotential {n : ℕ}
    (φ : Space n → ℝ)
    (z : TorusCharacters.LogSpace n) : ℝ :=
  φ ((logarithmicCoordinatesEquiv n).symm z).1

private theorem contDiff_matrixSourceCoverPotential
    {n : ℕ} {m : ℕ∞} {φ : Space n → ℝ}
    (hφ : ContDiff ℝ m φ) :
    ContDiff ℝ m (matrixSourceCoverPotential φ) := by
  unfold matrixSourceCoverPotential
  exact hφ.comp (by fun_prop)

private theorem continuous_matrixSourceCoverPotential
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ) :
    Continuous (matrixSourceCoverPotential φ) := by
  unfold matrixSourceCoverPotential
  exact hφ.comp
    (continuous_fst.comp (logarithmicCoordinatesEquiv n).symm.continuous)

@[simp] private theorem matrixSourceCoverPotential_logarithmicPoint
    {n : ℕ} (φ : Space n → ℝ)
    (x t : Space n) :
    matrixSourceCoverPotential φ
      (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t) = φ x := by
  unfold matrixSourceCoverPotential
  rw [← logarithmicCoordinatesEquiv_apply,
    ContinuousLinearEquiv.symm_apply_apply]

private def coverAngularSmoothPartition {n : ℕ}
    (z : TorusCharacters.LogSpace n) : ℝ :=
  angularSmoothPartition
    ((logarithmicCoordinatesEquiv n).symm z).2

private theorem contDiff_coverAngularSmoothPartition
    {n : ℕ} {m : ℕ∞} :
    ContDiff ℝ m (coverAngularSmoothPartition (n := n)) := by
  unfold coverAngularSmoothPartition
  exact contDiff_angularSmoothPartition.comp (by fun_prop)

@[simp] private theorem coverAngularSmoothPartition_logarithmicPoint
    {n : ℕ} (x t : Space n) :
    coverAngularSmoothPartition
      (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t) = angularSmoothPartition t := by
  unfold coverAngularSmoothPartition
  rw [← logarithmicCoordinatesEquiv_apply,
    ContinuousLinearEquiv.symm_apply_apply]

private def partitionedRealCoverIntegrand {n : ℕ}
    (φ : Space n → ℝ)
    (f : WeightedTorusHilbert.LogTorus n → ℂ)
    (p : Space n × Space n) : ℂ :=
  (Real.exp (-φ p.1) : ℂ) *
    ((angularSmoothPartition p.2 : ℂ) *
      f (p.1, angularCoverProjection n p.2))

private theorem continuous_partitionedRealCoverIntegrand
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : Continuous f) :
    Continuous (partitionedRealCoverIntegrand φ f) := by
  unfold partitionedRealCoverIntegrand
  apply (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp
      (hφ.comp continuous_fst).neg)).mul
  apply (Complex.continuous_ofReal.comp
    ((contDiff_angularSmoothPartition (m := 0)).continuous.comp
      continuous_snd)).mul
  exact hf.comp
    (continuous_fst.prodMk
      ((continuous_angularCoverProjection n).comp continuous_snd))

private theorem hasCompactSupport_partitionedRealCoverIntegrand
    {n : ℕ} {φ : Space n → ℝ}
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hfc : HasCompactSupport f) :
    HasCompactSupport (partitionedRealCoverIntegrand φ f) := by
  let Kr : Set (Space n) :=
    Prod.fst '' tsupport f
  let K : Set (Space n × Space n) :=
    Kr ×ˢ tsupport (angularSmoothPartition (n := n))
  have hKr : IsCompact Kr := hfc.image continuous_fst
  have hK : IsCompact K :=
    hKr.prod hasCompactSupport_angularSmoothPartition
  apply HasCompactSupport.intro hK
  intro p hp
  by_contra hnonzero
  have hangular : angularSmoothPartition p.2 ≠ 0 := by
    intro hzero
    apply hnonzero
    simp only [partitionedRealCoverIntegrand, Complex.ofReal_exp, Complex.ofReal_neg, hzero,
      Complex.ofReal_zero, zero_mul, mul_zero]
  have htest : f (p.1, angularCoverProjection n p.2) ≠ 0 := by
    intro hzero
    apply hnonzero
    simp only [partitionedRealCoverIntegrand, Complex.ofReal_exp, Complex.ofReal_neg, hzero,
      mul_zero]
  apply hp
  exact ⟨⟨(p.1, angularCoverProjection n p.2),
    subset_closure htest, rfl⟩, subset_closure hangular⟩

private theorem integrable_partitionedRealCoverIntegrand
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    Integrable (partitionedRealCoverIntegrand φ f)
      (volume : Measure (Space n × Space n)) := by
  exact (continuous_partitionedRealCoverIntegrand hφ hf).integrable_of_hasCompactSupport
    (hasCompactSupport_partitionedRealCoverIntegrand hfc)

private def unweightedSourceTorusIntegrand {n : ℕ}
    (φ : Space n → ℝ)
    (f : WeightedTorusHilbert.LogTorus n → ℂ)
    (p : WeightedTorusHilbert.LogTorus n) : ℂ :=
  (Real.exp (-φ p.1) : ℂ) * f p

private theorem continuous_unweightedSourceTorusIntegrand
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : Continuous f) :
    Continuous (unweightedSourceTorusIntegrand φ f) := by
  unfold unweightedSourceTorusIntegrand
  exact (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp
      (hφ.comp continuous_fst).neg)).mul hf

private theorem hasCompactSupport_unweightedSourceTorusIntegrand
    {n : ℕ} {φ : Space n → ℝ}
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hfc : HasCompactSupport f) :
    HasCompactSupport (unweightedSourceTorusIntegrand φ f) := by
  exact hfc.mul_left

private theorem integrable_unweightedSourceTorusIntegrand
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    Integrable (unweightedSourceTorusIntegrand φ f)
      ((volume : Measure (Space n)).prod
        (angularMeasure n)) := by
  let : IsLocallyFiniteMeasure
      ((volume : Measure (Space n)).prod
        (angularMeasure n)) := by
    infer_instance
  exact (continuous_unweightedSourceTorusIntegrand hφ hf).integrable_of_hasCompactSupport
    (hasCompactSupport_unweightedSourceTorusIntegrand hfc)

private theorem integral_partitionedRealCoverIntegrand_eq_unweightedSourceTorus
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    (∫ p : Space n × Space n,
      partitionedRealCoverIntegrand φ f p
      ∂(volume : Measure (Space n × Space n))) =
    ∫ p : WeightedTorusHilbert.LogTorus n,
      unweightedSourceTorusIntegrand φ f p
      ∂((volume : Measure (Space n)).prod
        (angularMeasure n)) := by
  have hreal := integrable_partitionedRealCoverIntegrand hφ hf hfc
  have hrealprod :
      Integrable (partitionedRealCoverIntegrand φ f)
        ((volume : Measure (Space n)).prod
          (volume : Measure (Space n))) := by
    rw [← Measure.volume_eq_prod]
    exact hreal
  have htorus := integrable_unweightedSourceTorusIntegrand hφ hf hfc
  calc
    _ = ∫ x : Space n,
      ∫ t : Space n,
        partitionedRealCoverIntegrand φ f (x, t)
        ∂(volume : Measure (Space n))
        ∂(volume : Measure (Space n)) := by
      rw [Measure.volume_eq_prod]
      exact MeasureTheory.integral_prod _ hrealprod
    _ = ∫ x : Space n,
      ∫ θ : TorusCharacters.AngularTorus n,
        unweightedSourceTorusIntegrand φ f (x, θ)
        ∂(angularMeasure n)
        ∂(volume : Measure (Space n)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      have hg : Continuous
          (fun θ : TorusCharacters.AngularTorus n =>
            f (x, θ)) :=
        hf.comp (continuous_const.prodMk continuous_id)
      have hpartition :=
        integral_angularSmoothPartition_eq_angularHaar hg
      have hcovermul :
          (∫ t : Space n,
            (Real.exp (-φ x) : ℂ) *
              ((angularSmoothPartition t : ℂ) *
                f (x, angularCoverProjection n t))
            ∂(volume : Measure (Space n))) =
          (Real.exp (-φ x) : ℂ) *
            (∫ t : Space n,
              (angularSmoothPartition t : ℂ) *
                f (x, angularCoverProjection n t)
              ∂(volume : Measure (Space n))) :=
        MeasureTheory.integral_const_mul
          (Real.exp (-φ x) : ℂ)
          (fun t : Space n =>
            (angularSmoothPartition t : ℂ) *
              f (x, angularCoverProjection n t))
      have htorusmul :
          (∫ θ : TorusCharacters.AngularTorus n,
            (Real.exp (-φ x) : ℂ) * f (x, θ)
            ∂(angularMeasure n)) =
          (Real.exp (-φ x) : ℂ) *
            (∫ θ : TorusCharacters.AngularTorus n,
              f (x, θ) ∂(angularMeasure n)) :=
        MeasureTheory.integral_const_mul
          (Real.exp (-φ x) : ℂ)
          (fun θ : TorusCharacters.AngularTorus n => f (x, θ))
      change
        (∫ t : Space n,
          (Real.exp (-φ x) : ℂ) *
            ((angularSmoothPartition t : ℂ) *
              f (x, angularCoverProjection n t))
          ∂(volume : Measure (Space n))) =
        ∫ θ : TorusCharacters.AngularTorus n,
          (Real.exp (-φ x) : ℂ) * f (x, θ)
          ∂(angularMeasure n)
      rw [hcovermul, htorusmul, hpartition]
    _ = _ := (MeasureTheory.integral_prod _ htorus).symm

private theorem integral_unweightedSourceTorusIntegrand_eq_weighted
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    (f : WeightedTorusHilbert.LogTorus n → ℂ) :
    (∫ p : WeightedTorusHilbert.LogTorus n,
      unweightedSourceTorusIntegrand φ f p
      ∂((volume : Measure (Space n)).prod
        (angularMeasure n))) =
    ∫ p : WeightedTorusHilbert.LogTorus n,
      f p ∂(weightedTorusMeasure 1 φ) := by
  have hd : Measurable
      (fun p : WeightedTorusHilbert.LogTorus n =>
        radialWeight 1 φ p.1) :=
    (radialWeight_measurable 1 hφ).comp measurable_fst
  rw [weightedTorusMeasure_eq_withDensity 1 hφ,
    integral_withDensity_eq_integral_toReal_smul
      hd (Filter.Eventually.of_forall
        (fun p : WeightedTorusHilbert.LogTorus n =>
          radialWeight_lt_top φ p.1))]
  apply integral_congr_ae
  filter_upwards [] with p
  unfold unweightedSourceTorusIntegrand radialWeight
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le,
    Complex.real_smul]
  norm_num

private theorem partitioned_coverWeighted_integral_eq_torus
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    logarithmicCoverJacobianFactor n •
      (∫ z : TorusCharacters.LogSpace n,
        (coverAngularSmoothPartition z : ℂ) *
          f (complexTorusCoverProjection n z)
        ∂(coverWeightedMeasure (matrixSourceCoverPotential φ))) =
      ∫ p : WeightedTorusHilbert.LogTorus n,
        f p ∂(weightedTorusMeasure 1 φ) := by
  let g : TorusCharacters.LogSpace n → ℂ :=
    fun z =>
      complexCoverWeight (matrixSourceCoverPotential φ) z *
        ((coverAngularSmoothPartition z : ℂ) *
          f (complexTorusCoverProjection n z))
  have hcover := integral_coverWeightedMeasure
    (continuous_matrixSourceCoverPotential hφ)
    (fun z : TorusCharacters.LogSpace n =>
      (coverAngularSmoothPartition z : ℂ) *
        f (complexTorusCoverProjection n z))
  calc
    _ = logarithmicCoverJacobianFactor n •
      (∫ z : TorusCharacters.LogSpace n, g z
        ∂(volume : Measure (TorusCharacters.LogSpace n))) := by
      exact congrArg
        (fun q : ℂ => logarithmicCoverJacobianFactor n • q) hcover
    _ = ∫ p : Space n × Space n,
      g (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        p.1 p.2)
      ∂(volume : Measure (Space n × Space n)) :=
      (integral_logarithmicCoordinates_eq_jacobian g).symm
    _ = ∫ p : Space n × Space n,
      partitionedRealCoverIntegrand φ f p
      ∂(volume : Measure (Space n × Space n)) := by
      apply integral_congr_ae
      filter_upwards [] with p
      simp only [complexCoverWeight, coverWeight, Complex.ofReal_exp, Complex.ofReal_neg,
        matrixSourceCoverPotential_logarithmicPoint, coverAngularSmoothPartition_logarithmicPoint,
        complexTorusCoverProjection_logarithmicPoint, realTorusCoverProjection,
        partitionedRealCoverIntegrand, g]
    _ = ∫ p : WeightedTorusHilbert.LogTorus n,
      unweightedSourceTorusIntegrand φ f p
      ∂((volume : Measure (Space n)).prod
        (angularMeasure n)) :=
      integral_partitionedRealCoverIntegrand_eq_unweightedSourceTorus
        hφ hf hfc
    _ = _ := integral_unweightedSourceTorusIntegrand_eq_weighted hφ f

end MatrixTorusBochnerBridge

namespace MatrixTorusBochnerIdentity

open Set Function MeasureTheory Filter Matrix
open EqualitySaturatingKillingPaths WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity MatrixTorusBochnerBridge
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

private def binaryAngularPartitionSum (n : ℕ)
    (t : Space n) : ℝ :=
  ∑ q : Fin n → Bool,
    angularSmoothPartition (binaryAngularFundamentalBase q + t)

private theorem contDiff_binaryAngularPartitionSum
    {n : ℕ} {m : ℕ∞} :
    ContDiff ℝ m (binaryAngularPartitionSum n) := by
  unfold binaryAngularPartitionSum
  apply ContDiff.sum
  intro q _
  exact contDiff_angularSmoothPartition.comp
    (contDiff_const.add contDiff_id)

private theorem binaryAngularPartitionSum_eq_one
    {n : ℕ} (t : Space n)
    (hzero : ∀ i : Fin n, 0 ≤ t i)
    (hone : ∀ i : Fin n, t i ≤ 1) :
    binaryAngularPartitionSum n t = 1 := by
  unfold binaryAngularPartitionSum
  calc
    _ = ∑ q : Fin n → Bool,
      angularSmoothPartition
        (fun i => t i - if q i then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro q _
      congr 1
      funext i
      simp only [Pi.add_apply, binaryAngularFundamentalBase]
      split <;> ring
    _ = 1 := angularSmoothPartition_binary_sum t hzero hone

private theorem fderiv_binaryAngularPartitionSum_eq_zero_of_open
    {n : ℕ} (t : Space n)
    (hzero : ∀ i : Fin n, 0 < t i)
    (hone : ∀ i : Fin n, t i < 1) :
    fderiv ℝ (binaryAngularPartitionSum n) t = 0 := by
  let U : Set (Space n) :=
    Set.univ.pi (fun _ : Fin n => Set.Ioo (0 : ℝ) 1)
  have hU : IsOpen U :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have ht : t ∈ U := by
    intro i _
    exact ⟨hzero i, hone i⟩
  have hevent :
      binaryAngularPartitionSum n =ᶠ[𝓝 t]
        (fun _ : Space n => (1 : ℝ)) := by
    filter_upwards [hU.mem_nhds ht] with s hs
    exact binaryAngularPartitionSum_eq_one s
      (fun i => (hs i (Set.mem_univ i)).1.le)
      (fun i => (hs i (Set.mem_univ i)).2.le)
  simpa only [fderiv_fun_const, Pi.zero_apply] using (hevent.fderiv_eq (𝕜 := ℝ))

private theorem fderiv_binaryAngularPartitionSum_eq_zero
    {n : ℕ} (t : Space n)
    (hzero : ∀ i : Fin n, 0 ≤ t i)
    (hone : ∀ i : Fin n, t i ≤ 1) :
    fderiv ℝ (binaryAngularPartitionSum n) t = 0 := by
  let U : Set (Space n) :=
    Set.univ.pi (fun _ : Fin n => Set.Ioo (0 : ℝ) 1)
  let Z : Set (Space n) :=
    {s | fderiv ℝ (binaryAngularPartitionSum n) s = 0}
  have hcont : Continuous
      (fderiv ℝ (binaryAngularPartitionSum n)) := by
    exact (contDiff_binaryAngularPartitionSum (n := n) (m := 1)).continuous_fderiv
      (by simp only [WithTop.coe_one, ne_eq, one_ne_zero, not_false_eq_true])
  have hclosed : IsClosed Z := by
    exact isClosed_eq hcont continuous_const
  have hsub : U ⊆ Z := by
    intro s hs
    exact fderiv_binaryAngularPartitionSum_eq_zero_of_open s
      (fun i => (hs i (Set.mem_univ i)).1)
      (fun i => (hs i (Set.mem_univ i)).2)
  have ht : t ∈ closure U := by
    rw [show closure U =
      Set.univ.pi (fun _ : Fin n => Set.Icc (0 : ℝ) 1) by
        dsimp [U]
        rw [closure_pi_set]
        simp only [ne_eq, zero_ne_one, not_false_eq_true, closure_Ioo, pi_univ_Icc]]
    intro i _
    exact ⟨hzero i, hone i⟩
  exact (closure_minimal hsub hclosed) ht

private theorem fderiv_angularSmoothPartition_translate
    {n : ℕ} (b t : Space n) :
    fderiv ℝ (fun s : Space n =>
      angularSmoothPartition (b + s)) t =
      fderiv ℝ (angularSmoothPartition (n := n)) (b + t) := by
  have hbump : DifferentiableAt ℝ
      (angularSmoothPartition (n := n)) (b + t) :=
    (contDiff_angularSmoothPartition (n := n) (m := 1)).differentiable
      (by simp only [WithTop.coe_one, ne_eq, one_ne_zero, not_false_eq_true]) (b + t)
  have hshift : DifferentiableAt ℝ
      (fun s : Space n => b + s) t := by
    fun_prop
  have hinner :
      fderiv ℝ (fun s : Space n => b + s) t =
        ContinuousLinearMap.id ℝ (Space n) := by
    simpa only [fderiv_fun_id] using
      (fderiv_const_add (𝕜 := ℝ)
        (f := fun s : Space n => s) (x := t) b)
  have hcomp := fderiv_comp t hbump hshift
  change
    fderiv ℝ
      (fun s : Space n => angularSmoothPartition (b + s)) t =
      (fderiv ℝ (angularSmoothPartition (n := n)) (b + t)).comp
        (fderiv ℝ (fun s : Space n => b + s) t)
    at hcomp
  rw [hinner, ContinuousLinearMap.comp_id] at hcomp
  exact hcomp

private theorem sum_fderiv_angularSmoothPartition_binary_eq_zero
    {n : ℕ} (t v : Space n)
    (hzero : ∀ i : Fin n, 0 ≤ t i)
    (hone : ∀ i : Fin n, t i ≤ 1) :
    (∑ q : Fin n → Bool,
      (fderiv ℝ (angularSmoothPartition (n := n))
        (binaryAngularFundamentalBase q + t)) v) = 0 := by
  classical
  have hsum :
      fderiv ℝ (binaryAngularPartitionSum n) t =
        ∑ q : Fin n → Bool,
          fderiv ℝ
            (fun s : Space n =>
              angularSmoothPartition
                (binaryAngularFundamentalBase q + s)) t := by
    unfold binaryAngularPartitionSum
    apply fderiv_fun_sum
    intro q _
    exact (contDiff_angularSmoothPartition
      (n := n) (m := 1)).differentiable (by simp only [WithTop.coe_one, ne_eq, one_ne_zero,
        not_false_eq_true])
        (binaryAngularFundamentalBase q + t) |>.comp t (by fun_prop)
  have hzeroDeriv := fderiv_binaryAngularPartitionSum_eq_zero
    t hzero hone
  have happly := congrArg
    (fun A : Space n →L[ℝ] ℝ => A v)
    (hsum.trans (Finset.sum_congr rfl (fun q _ =>
      fderiv_angularSmoothPartition_translate
        (binaryAngularFundamentalBase q) t)))
  rw [hzeroDeriv] at happly
  simpa only [_root_.sum_apply, _root_.zero_apply] using happly.symm

private theorem fderiv_angularSmoothPartition_eq_zero_of_zero
    {n : ℕ} {t : Space n}
    (ht : angularSmoothPartition t = 0) :
    fderiv ℝ (angularSmoothPartition (n := n)) t = 0 := by
  have hmin : IsLocalMin (angularSmoothPartition (n := n)) t := by
    change ∀ᶠ s : Space n in 𝓝 t,
      angularSmoothPartition t ≤ angularSmoothPartition s
    exact Filter.Eventually.of_forall (fun s => by
      rw [ht]
      exact angularSmoothPartition_nonneg s)
  exact hmin.fderiv_eq_zero

private theorem integral_binaryPeriodic_cutoff_eq_zero
    {n : ℕ} {κ : Space n → ℝ}
    (hκ : Continuous κ)
    (hκcompact : HasCompactSupport κ)
    (houtside : ∀ t : Space n,
      t ∉ Set.univ.pi
        (fun _ : Fin n => Set.Ioc (-1 : ℝ) 1) → κ t = 0)
    (hcancel : ∀ t : Space n,
      (∀ i : Fin n, 0 ≤ t i) →
      (∀ i : Fin n, t i ≤ 1) →
      (∑ q : Fin n → Bool,
        κ (binaryAngularFundamentalBase q + t)) = 0)
    {g : Space n → ℂ}
    (hg : Continuous g)
    (hperiod : ∀ (q : Fin n → Bool) (t : Space n),
      g (binaryAngularFundamentalBase q + t) = g t) :
    (∫ t : Space n,
      (κ t : ℂ) * g t
      ∂(volume : Measure (Space n))) = 0 := by
  classical
  let F : Space n → ℂ :=
    fun t => (κ t : ℂ) * g t
  have hFc : Continuous F :=
    (Complex.continuous_ofReal.comp hκ).mul hg
  have hFs : HasCompactSupport F := by
    apply hκcompact.mono
    intro t ht
    change (κ t : ℂ) * g t ≠ 0 at ht
    intro hz
    exact ht (by simp only [hz, Complex.ofReal_zero, zero_mul])
  have hF : Integrable F
      (volume : Measure (Space n)) :=
    hFc.integrable_of_hasCompactSupport hFs
  let U : Set (Space n) :=
    ⋃ q : Fin n → Bool,
      angularFundamentalBox (binaryAngularFundamentalBase q)
  have hvanish : ∀ t : Space n, t ∉ U → F t = 0 := by
    intro t ht
    have hcube :
        t ∉ Set.univ.pi
          (fun _ : Fin n => Set.Ioc (-1 : ℝ) 1) := by
      rw [← iUnion_binaryAngularFundamentalBox n]
      exact ht
    simp only [houtside t hcube, Complex.ofReal_zero, zero_mul, F]
  have htranslate (q : Fin n → Bool) :
      (∫ t : Space n
        in angularFundamentalBox (binaryAngularFundamentalBase q),
        F t ∂(volume : Measure (Space n))) =
      ∫ t : Space n
        in angularFundamentalBox (0 : Space n),
        F (binaryAngularFundamentalBase q + t)
          ∂(volume : Measure (Space n)) := by
    have h :=
      (MeasureTheory.measurePreserving_add_left
        (volume : Measure (Space n))
        (binaryAngularFundamentalBase q)).setIntegral_image_emb
          (measurableEmbedding_addLeft
            (binaryAngularFundamentalBase q))
          F (angularFundamentalBox (0 : Space n))
    rwa [binaryAngularFundamentalBox_eq_translate] at h
  have hshift (q : Fin n → Bool) :
      IntegrableOn
        (fun t : Space n =>
          F (binaryAngularFundamentalBase q + t))
        (angularFundamentalBox (0 : Space n))
        (volume : Measure (Space n)) := by
    have h :=
      (MeasureTheory.measurePreserving_add_left
        (volume : Measure (Space n))
        (binaryAngularFundamentalBase q)).integrable_comp_of_integrable hF
    exact (show Integrable
      (fun t : Space n =>
        F (binaryAngularFundamentalBase q + t))
      (volume : Measure (Space n)) by
        simpa only [comp_def] using h).integrableOn
  change (∫ t : Space n, F t
    ∂(volume : Measure (Space n))) = 0
  calc
    _ = ∫ t : Space n in U, F t
        ∂(volume : Measure (Space n)) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hvanish).symm
    _ = ∑ q : Fin n → Bool,
      ∫ t : Space n
        in angularFundamentalBox (binaryAngularFundamentalBase q),
        F t ∂(volume : Measure (Space n)) := by
      exact MeasureTheory.integral_iUnion_fintype
        (fun q => measurableSet_angularFundamentalBox
          (binaryAngularFundamentalBase q))
        (pairwiseDisjoint_binaryAngularFundamentalBox n)
        (fun _ => hF.integrableOn)
    _ = ∑ q : Fin n → Bool,
      ∫ t : Space n
        in angularFundamentalBox (0 : Space n),
        F (binaryAngularFundamentalBase q + t)
          ∂(volume : Measure (Space n)) := by
      apply Finset.sum_congr rfl
      intro q _
      exact htranslate q
    _ = ∫ t : Space n
        in angularFundamentalBox (0 : Space n),
        ∑ q : Fin n → Bool,
          F (binaryAngularFundamentalBase q + t)
        ∂(volume : Measure (Space n)) := by
      symm
      exact MeasureTheory.integral_finsetSum Finset.univ
        (fun q _ => hshift q)
    _ = ∫ _t : Space n
        in angularFundamentalBox (0 : Space n),
        (0 : ℂ) ∂(volume : Measure (Space n)) := by
      apply MeasureTheory.setIntegral_congr_fun
        (measurableSet_angularFundamentalBox
          (0 : Space n))
      intro t ht
      have ht0 : ∀ i : Fin n, 0 ≤ t i := by
        intro i
        have h := ht i
        have h' : 0 < t i ∧ t i ≤ (1 : ℝ) := by
          simpa only [Pi.zero_apply, zero_add, mem_Ioc] using h
        exact h'.1.le
      have ht1 : ∀ i : Fin n, t i ≤ 1 := by
        intro i
        have h := ht i
        have h' : 0 < t i ∧ t i ≤ (1 : ℝ) := by
          simpa only [Pi.zero_apply, zero_add, mem_Ioc] using h
        exact h'.2
      have hreal :
          (∑ q : Fin n → Bool,
            κ (binaryAngularFundamentalBase q + t)) = 0 :=
        hcancel t ht0 ht1
      have hcomplex :
          (∑ q : Fin n → Bool,
            (κ (binaryAngularFundamentalBase q + t) : ℂ)) = 0 := by
        exact_mod_cast hreal
      change
        (∑ q : Fin n → Bool,
          (κ (binaryAngularFundamentalBase q + t) : ℂ) *
            g (binaryAngularFundamentalBase q + t)) = 0
      simp_rw [hperiod]
      rw [← Finset.sum_mul, hcomplex, zero_mul]
    _ = 0 := by simp only [integral_zero]

private theorem integral_fderiv_angularSmoothPartition_periodic_eq_zero
    {n : ℕ} (v : Space n)
    {g : Space n → ℂ}
    (hg : Continuous g)
    (hperiod : ∀ (q : Fin n → Bool) (t : Space n),
      g (binaryAngularFundamentalBase q + t) = g t) :
    (∫ t : Space n,
      ((fderiv ℝ (angularSmoothPartition (n := n)) t) v : ℂ) *
        g t ∂(volume : Measure (Space n))) = 0 := by
  let κ : Space n → ℝ :=
    fun t => (fderiv ℝ (angularSmoothPartition (n := n)) t) v
  have hκ : Continuous κ := by
    exact ((contDiff_angularSmoothPartition
      (n := n) (m := 1)).continuous_fderiv
        (by simp only [WithTop.coe_one, ne_eq, one_ne_zero, not_false_eq_true])).clm_apply
          continuous_const
  have hκcompact : HasCompactSupport κ :=
    hasCompactSupport_angularSmoothPartition.fderiv_apply ℝ v
  have houtside : ∀ t : Space n,
      t ∉ Set.univ.pi
        (fun _ : Fin n => Set.Ioc (-1 : ℝ) 1) → κ t = 0 := by
    intro t ht
    have hnot :
        ¬ ∀ i : Fin n, (-1 : ℝ) < t i ∧ t i ≤ 1 := by
      intro h
      apply ht
      intro i _
      exact h i
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hbump : angularSmoothPartitionBump (t i) = 0 := by
      by_cases hleft : t i ≤ -1
      · exact angularSmoothPartitionBump_zero_of_le hleft
      · have hright : 1 < t i := by
          by_contra hn
          apply hi
          exact ⟨lt_of_not_ge hleft, le_of_not_gt hn⟩
        exact angularSmoothPartitionBump_zero_of_ge hright.le
    have hzero : angularSmoothPartition t = 0 := by
      unfold angularSmoothPartition
      exact Finset.prod_eq_zero (Finset.mem_univ i) hbump
    change (fderiv ℝ (angularSmoothPartition (n := n)) t) v = 0
    rw [fderiv_angularSmoothPartition_eq_zero_of_zero hzero]
    rfl
  exact integral_binaryPeriodic_cutoff_eq_zero hκ hκcompact houtside
    (fun t ht0 ht1 =>
      sum_fderiv_angularSmoothPartition_binary_eq_zero t v ht0 ht1)
    hg hperiod

private theorem angularCoverProjection_binary_translate
    {n : ℕ} (q : Fin n → Bool) (t : Space n) :
    angularCoverProjection n
      (binaryAngularFundamentalBase q + t) =
      angularCoverProjection n t := by
  let u : Fin n → ℤ :=
    fun i => if q i then (-1 : ℤ) else 0
  have heq :
      binaryAngularFundamentalBase q + t =
        fun i : Fin n => t i + (u i : ℝ) := by
    funext i
    simp only [Pi.add_apply, binaryAngularFundamentalBase, u]
    split <;> simp ; ring
  rw [heq, angularCoverProjection_integer_add]

private def derivativePartitionedRealCoverIntegrand {n : ℕ}
    (φ : Space n → ℝ)
    (f : WeightedTorusHilbert.LogTorus n → ℂ)
    (v : Space n)
    (p : Space n × Space n) : ℂ :=
  (Real.exp (-φ p.1) : ℂ) *
    (((fderiv ℝ (angularSmoothPartition (n := n)) p.2) v : ℂ) *
      f (p.1, angularCoverProjection n p.2))

private theorem continuous_derivativePartitionedRealCoverIntegrand
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : Continuous f)
    (v : Space n) :
    Continuous (derivativePartitionedRealCoverIntegrand φ f v) := by
  have hder : Continuous
      (fun t : Space n =>
        (fderiv ℝ (angularSmoothPartition (n := n)) t) v) :=
    ((contDiff_angularSmoothPartition
      (n := n) (m := 1)).continuous_fderiv
        (by simp only [WithTop.coe_one, ne_eq, one_ne_zero, not_false_eq_true])).clm_apply
          continuous_const
  unfold derivativePartitionedRealCoverIntegrand
  apply (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp
      (hφ.comp continuous_fst).neg)).mul
  apply (Complex.continuous_ofReal.comp
    (hder.comp continuous_snd)).mul
  exact hf.comp
    (continuous_fst.prodMk
      ((continuous_angularCoverProjection n).comp continuous_snd))

private theorem hasCompactSupport_derivativePartitionedRealCoverIntegrand
    {n : ℕ} {φ : Space n → ℝ}
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hfc : HasCompactSupport f)
    (v : Space n) :
    HasCompactSupport
      (derivativePartitionedRealCoverIntegrand φ f v) := by
  let κ : Space n → ℝ :=
    fun t => (fderiv ℝ (angularSmoothPartition (n := n)) t) v
  let Kr : Set (Space n) :=
    Prod.fst '' tsupport f
  let K : Set (Space n × Space n) :=
    Kr ×ˢ tsupport κ
  have hKr : IsCompact Kr := hfc.image continuous_fst
  have hκ : HasCompactSupport κ :=
    hasCompactSupport_angularSmoothPartition.fderiv_apply ℝ v
  have hK : IsCompact K := hKr.prod hκ
  apply HasCompactSupport.intro hK
  intro p hp
  by_contra hnonzero
  have hangular : κ p.2 ≠ 0 := by
    intro hzero
    apply hnonzero
    simp only [derivativePartitionedRealCoverIntegrand, Complex.ofReal_exp, Complex.ofReal_neg,
      hzero,
      Complex.ofReal_zero, zero_mul, mul_zero, κ]
  have htest : f (p.1, angularCoverProjection n p.2) ≠ 0 := by
    intro hzero
    apply hnonzero
    simp only [derivativePartitionedRealCoverIntegrand, Complex.ofReal_exp, Complex.ofReal_neg,
      hzero,
      mul_zero]
  apply hp
  exact ⟨⟨(p.1, angularCoverProjection n p.2),
    subset_closure htest, rfl⟩, subset_closure hangular⟩

private theorem integrable_derivativePartitionedRealCoverIntegrand
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : Continuous f)
    (hfc : HasCompactSupport f)
    (v : Space n) :
    Integrable (derivativePartitionedRealCoverIntegrand φ f v)
      (volume : Measure (Space n × Space n)) := by
  exact (continuous_derivativePartitionedRealCoverIntegrand
    hφ hf v).integrable_of_hasCompactSupport
      (hasCompactSupport_derivativePartitionedRealCoverIntegrand hfc v)

private theorem integral_derivativePartitionedRealCoverIntegrand_eq_zero
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : Continuous f)
    (hfc : HasCompactSupport f)
    (v : Space n) :
    (∫ p : Space n × Space n,
      derivativePartitionedRealCoverIntegrand φ f v p
      ∂(volume : Measure (Space n × Space n))) = 0 := by
  have hreal :=
    integrable_derivativePartitionedRealCoverIntegrand hφ hf hfc v
  have hrealprod :
      Integrable (derivativePartitionedRealCoverIntegrand φ f v)
        ((volume : Measure (Space n)).prod
          (volume : Measure (Space n))) := by
    rw [← Measure.volume_eq_prod]
    exact hreal
  calc
    _ = ∫ x : Space n,
      ∫ t : Space n,
        derivativePartitionedRealCoverIntegrand φ f v (x, t)
        ∂(volume : Measure (Space n))
        ∂(volume : Measure (Space n)) := by
      rw [Measure.volume_eq_prod]
      exact MeasureTheory.integral_prod _ hrealprod
    _ = ∫ _x : Space n, (0 : ℂ)
        ∂(volume : Measure (Space n)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      let g : Space n → ℂ :=
        fun t => f (x, angularCoverProjection n t)
      have hg : Continuous g :=
        hf.comp (continuous_const.prodMk
          (continuous_angularCoverProjection n))
      have hperiod : ∀ (q : Fin n → Bool) (t : Space n),
          g (binaryAngularFundamentalBase q + t) = g t := by
        intro q t
        change
          f (x, angularCoverProjection n
            (binaryAngularFundamentalBase q + t)) =
          f (x, angularCoverProjection n t)
        rw [angularCoverProjection_binary_translate]
      let d : Space n → ℂ :=
        fun t => ((fderiv ℝ
          (angularSmoothPartition (n := n)) t) v : ℂ)
      have hzero :
          (∫ t : Space n, d t * g t
            ∂(volume : Measure (Space n))) = 0 := by
        exact integral_fderiv_angularSmoothPartition_periodic_eq_zero
          v hg hperiod
      have hmul :
          (∫ t : Space n,
            (Real.exp (-φ x) : ℂ) * (d t * g t)
            ∂(volume : Measure (Space n))) =
          (Real.exp (-φ x) : ℂ) *
            (∫ t : Space n, d t * g t
              ∂(volume : Measure (Space n))) :=
        MeasureTheory.integral_const_mul
          (Real.exp (-φ x) : ℂ)
          (fun t : Space n => d t * g t)
      change
        (∫ t : Space n,
          (Real.exp (-φ x) : ℂ) * (d t * g t)
          ∂(volume : Measure (Space n))) = 0
      rw [hmul, hzero, mul_zero]
    _ = 0 := by simp only [integral_zero]

private theorem integral_sourceCoverAngularPartitionDerivative_mul_lift_eq_zero
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : Continuous f)
    (hfc : HasCompactSupport f)
    (v : Space n) :
    (∫ z : TorusCharacters.LogSpace n,
      (((fderiv ℝ (angularSmoothPartition (n := n))
        ((logarithmicCoordinatesEquiv n).symm z).2) v : ℂ) *
        f (complexTorusCoverProjection n z))
      ∂(coverWeightedMeasure (matrixSourceCoverPotential φ))) = 0 := by
  let F : TorusCharacters.LogSpace n → ℂ :=
    fun z =>
      (((fderiv ℝ (angularSmoothPartition (n := n))
        ((logarithmicCoordinatesEquiv n).symm z).2) v : ℂ) *
        f (complexTorusCoverProjection n z))
  let G : TorusCharacters.LogSpace n → ℂ :=
    fun z => complexCoverWeight (matrixSourceCoverPotential φ) z * F z
  have hcover := integral_coverWeightedMeasure
    (continuous_matrixSourceCoverPotential hφ) F
  have hsmul :
      logarithmicCoverJacobianFactor n •
        (∫ z : TorusCharacters.LogSpace n,
          F z ∂(coverWeightedMeasure (matrixSourceCoverPotential φ))) =
        0 := by
    calc
      _ = logarithmicCoverJacobianFactor n •
        (∫ z : TorusCharacters.LogSpace n,
          G z ∂(volume : Measure
            (TorusCharacters.LogSpace n))) := by
        exact congrArg
          (fun w : ℂ => logarithmicCoverJacobianFactor n • w)
          hcover
      _ = ∫ p : Space n × Space n,
        G (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
          p.1 p.2)
        ∂(volume : Measure (Space n × Space n)) :=
        (integral_logarithmicCoordinates_eq_jacobian G).symm
      _ = ∫ p : Space n × Space n,
        derivativePartitionedRealCoverIntegrand φ f v p
        ∂(volume : Measure (Space n × Space n)) := by
        apply integral_congr_ae
        filter_upwards [] with p
        simp only [G, F, complexCoverWeight, coverWeight,
          derivativePartitionedRealCoverIntegrand,
          matrixSourceCoverPotential,
          complexTorusCoverProjection,
          realTorusCoverProjection,
          ← logarithmicCoordinatesEquiv_apply,
          ContinuousLinearEquiv.symm_apply_apply]
      _ = 0 :=
        integral_derivativePartitionedRealCoverIntegrand_eq_zero
          hφ hf hfc v
  exact (smul_eq_zero.mp hsmul).resolve_left
    (logarithmicCoverJacobianFactor_pos n).ne'

private def sourceCoverAngularLinear (n : ℕ) :
    TorusCharacters.LogSpace n →L[ℝ] Space n :=
  (ContinuousLinearMap.snd ℝ (Space n)
    (Space n)).comp
      (logarithmicCoordinatesEquiv n).symm.toContinuousLinearMap

private theorem fderiv_coverAngularSmoothPartition_apply
    {n : ℕ}
    (z v : TorusCharacters.LogSpace n) :
    (fderiv ℝ (coverAngularSmoothPartition (n := n)) z) v =
      (fderiv ℝ (angularSmoothPartition (n := n))
        ((logarithmicCoordinatesEquiv n).symm z).2)
          (((logarithmicCoordinatesEquiv n).symm v).2) := by
  let P : TorusCharacters.LogSpace n →L[ℝ]
      Space n := sourceCoverAngularLinear n
  have hη : DifferentiableAt ℝ
      (angularSmoothPartition (n := n)) (P z) :=
    (contDiff_angularSmoothPartition
      (n := n) (m := 1)).differentiable (by simp only [WithTop.coe_one, ne_eq, one_ne_zero,
        not_false_eq_true]) (P z)
  have hp : DifferentiableAt ℝ
      (fun w : TorusCharacters.LogSpace n => P w) z :=
    P.differentiableAt
  have hc := fderiv_comp z hη hp
  have hinner :
      fderiv ℝ
        (fun w : TorusCharacters.LogSpace n => P w) z = P :=
    P.fderiv
  change
    fderiv ℝ
      (fun w : TorusCharacters.LogSpace n =>
        angularSmoothPartition (P w)) z =
      (fderiv ℝ (angularSmoothPartition (n := n)) (P z)).comp
        (fderiv ℝ
          (fun w : TorusCharacters.LogSpace n => P w) z)
    at hc
  rw [hinner] at hc
  have ha := congrArg
    (fun A : TorusCharacters.LogSpace n →L[ℝ] ℝ => A v) hc
  exact ha

private theorem integral_fderiv_coverAngularSmoothPartition_mul_lift_eq_zero
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : Continuous f)
    (hfc : HasCompactSupport f)
    (v : TorusCharacters.LogSpace n) :
    (∫ z : TorusCharacters.LogSpace n,
      (((fderiv ℝ (coverAngularSmoothPartition (n := n)) z) v : ℂ) *
        f (complexTorusCoverProjection n z))
      ∂(coverWeightedMeasure (matrixSourceCoverPotential φ))) = 0 := by
  calc
    _ = ∫ z : TorusCharacters.LogSpace n,
      (((fderiv ℝ (angularSmoothPartition (n := n))
        ((logarithmicCoordinatesEquiv n).symm z).2)
          (((logarithmicCoordinatesEquiv n).symm v).2) : ℂ) *
        f (complexTorusCoverProjection n z))
      ∂(coverWeightedMeasure (matrixSourceCoverPotential φ)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [fderiv_coverAngularSmoothPartition_apply]
    _ = 0 :=
      integral_sourceCoverAngularPartitionDerivative_mul_lift_eq_zero
        hφ hf hfc (((logarithmicCoordinatesEquiv n).symm v).2)

private theorem angularCoverProjection_isOpenQuotientMap (n : ℕ) :
    IsOpenQuotientMap (angularCoverProjection n) := by
  change IsOpenQuotientMap
    (Pi.map (fun _ : Fin n =>
      (fun t : ℝ => (t : UnitAddCircle))))
  exact IsOpenQuotientMap.piMap
    (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)

private theorem realTorusCoverProjection_isOpenQuotientMap (n : ℕ) :
    IsOpenQuotientMap (realTorusCoverProjection n) := by
  change IsOpenQuotientMap
    (Prod.map (id : Space n → Space n)
      (angularCoverProjection n))
  exact IsOpenQuotientMap.id.prodMap
    (angularCoverProjection_isOpenQuotientMap n)

private theorem complexTorusCoverProjection_isOpenQuotientMap (n : ℕ) :
    IsOpenQuotientMap (complexTorusCoverProjection n) := by
  have h :=
    (realTorusCoverProjection_isOpenQuotientMap n).comp
      (logarithmicCoordinatesEquiv n).symm.toHomeomorph.isOpenQuotientMap
  change IsOpenQuotientMap
    (realTorusCoverProjection n ∘ (logarithmicCoordinatesEquiv n).symm)
  exact h

private theorem continuous_torusScalarRepresentative_of_periodic
    {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Continuous F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q)) :
    Continuous (torusScalarRepresentative F) := by
  apply (complexTorusCoverProjection_isOpenQuotientMap n).continuous_comp_iff.mp
  have hrecover :=
    complexTorusCoverLift_torusScalarRepresentative_eq F hperiod
  have hcomp :
      (torusScalarRepresentative F ∘
        complexTorusCoverProjection n) = F := by
    funext z
    exact congrFun hrecover z
  rw [hcomp]
  exact hF

private theorem continuous_complexTorusCoverProjection (n : ℕ) :
    Continuous (complexTorusCoverProjection n) :=
  (complexTorusCoverProjection_isOpenQuotientMap n).continuous

private def sourceAngularCutoffLift {n : ℕ}
    (f : WeightedTorusHilbert.LogTorus n → ℂ)
    (z : TorusCharacters.LogSpace n) : ℂ :=
  (coverAngularSmoothPartition z : ℂ) *
    f (complexTorusCoverProjection n z)

private theorem continuous_sourceAngularCutoffLift
    {n : ℕ}
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : Continuous f) :
    Continuous (sourceAngularCutoffLift f) := by
  unfold sourceAngularCutoffLift
  exact (Complex.continuous_ofReal.comp
    (contDiff_coverAngularSmoothPartition
      (n := n) (m := 1)).continuous).mul
        (hf.comp (continuous_complexTorusCoverProjection n))

private theorem hasCompactSupport_sourceAngularCutoffLift
    {n : ℕ}
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hfc : HasCompactSupport f) :
    HasCompactSupport (sourceAngularCutoffLift f) := by
  let Kr : Set (Space n) :=
    Prod.fst '' tsupport f
  let A : Set (Space n × Space n) :=
    Kr ×ˢ tsupport (angularSmoothPartition (n := n))
  let K : Set (TorusCharacters.LogSpace n) :=
    logarithmicCoordinatesEquiv n '' A
  have hKr : IsCompact Kr := hfc.image continuous_fst
  have hA : IsCompact A :=
    hKr.prod hasCompactSupport_angularSmoothPartition
  have hK : IsCompact K :=
    hA.image (logarithmicCoordinatesEquiv n).continuous
  apply HasCompactSupport.intro hK
  intro z hz
  by_contra hnonzero
  have hangular :
      angularSmoothPartition
        ((logarithmicCoordinatesEquiv n).symm z).2 ≠ 0 := by
    intro hzero
    apply hnonzero
    change
      (angularSmoothPartition
        ((logarithmicCoordinatesEquiv n).symm z).2 : ℂ) *
        f (complexTorusCoverProjection n z) = 0
    rw [hzero]
    simp only [Complex.ofReal_zero, zero_mul]
  have htest : f (complexTorusCoverProjection n z) ≠ 0 := by
    intro hzero
    apply hnonzero
    simp only [sourceAngularCutoffLift, hzero, mul_zero]
  apply hz
  refine ⟨(logarithmicCoordinatesEquiv n).symm z, ?_,
    (logarithmicCoordinatesEquiv n).apply_symm_apply z⟩
  refine ⟨?_, subset_closure hangular⟩
  refine ⟨complexTorusCoverProjection n z,
    subset_closure htest, ?_⟩
  rfl

private theorem contDiff_sourceAngularCutoffLift
    {n : ℕ} {m : ℕ∞}
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : ContDiff ℝ m (complexTorusCoverLift f)) :
    ContDiff ℝ m (sourceAngularCutoffLift f) := by
  change ContDiff ℝ m
    (fun z : TorusCharacters.LogSpace n =>
      (coverAngularSmoothPartition z : ℂ) *
        complexTorusCoverLift f z)
  exact (Complex.ofRealCLM.contDiff.comp
    (contDiff_coverAngularSmoothPartition
      (n := n) (m := m))).mul hf

private def sourceAngularDerivativeLift {n : ℕ}
    (f : WeightedTorusHilbert.LogTorus n → ℂ)
    (v : TorusCharacters.LogSpace n)
    (z : TorusCharacters.LogSpace n) : ℂ :=
  ((fderiv ℝ (coverAngularSmoothPartition (n := n)) z) v : ℂ) *
    f (complexTorusCoverProjection n z)

private theorem continuous_sourceAngularDerivativeLift
    {n : ℕ}
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : Continuous f)
    (v : TorusCharacters.LogSpace n) :
    Continuous (sourceAngularDerivativeLift f v) := by
  unfold sourceAngularDerivativeLift
  apply (Complex.continuous_ofReal.comp
    (((contDiff_coverAngularSmoothPartition
      (n := n) (m := 1)).continuous_fderiv
        (by simp only [WithTop.coe_one, ne_eq, one_ne_zero,
              not_false_eq_true])).clm_apply continuous_const)).mul
  exact hf.comp (continuous_complexTorusCoverProjection n)

private theorem hasCompactSupport_sourceAngularDerivativeLift
    {n : ℕ}
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hfc : HasCompactSupport f)
    (v : TorusCharacters.LogSpace n) :
    HasCompactSupport (sourceAngularDerivativeLift f v) := by
  let w : Space n :=
    ((logarithmicCoordinatesEquiv n).symm v).2
  let κ : Space n → ℝ :=
    fun t => (fderiv ℝ (angularSmoothPartition (n := n)) t) w
  let Kr : Set (Space n) :=
    Prod.fst '' tsupport f
  let A : Set (Space n × Space n) :=
    Kr ×ˢ tsupport κ
  let K : Set (TorusCharacters.LogSpace n) :=
    logarithmicCoordinatesEquiv n '' A
  have hKr : IsCompact Kr := hfc.image continuous_fst
  have hκ : HasCompactSupport κ :=
    hasCompactSupport_angularSmoothPartition.fderiv_apply ℝ w
  have hA : IsCompact A := hKr.prod hκ
  have hK : IsCompact K :=
    hA.image (logarithmicCoordinatesEquiv n).continuous
  apply HasCompactSupport.intro hK
  intro z hz
  by_contra hnonzero
  have hangular :
      κ ((logarithmicCoordinatesEquiv n).symm z).2 ≠ 0 := by
    intro hzero
    apply hnonzero
    unfold sourceAngularDerivativeLift
    rw [fderiv_coverAngularSmoothPartition_apply]
    change (κ ((logarithmicCoordinatesEquiv n).symm z).2 : ℂ) *
      f (complexTorusCoverProjection n z) = 0
    rw [hzero]
    simp only [Complex.ofReal_zero, zero_mul]
  have htest : f (complexTorusCoverProjection n z) ≠ 0 := by
    intro hzero
    apply hnonzero
    simp only [sourceAngularDerivativeLift, hzero, mul_zero]
  apply hz
  refine ⟨(logarithmicCoordinatesEquiv n).symm z, ?_,
    (logarithmicCoordinatesEquiv n).apply_symm_apply z⟩
  refine ⟨?_, subset_closure hangular⟩
  refine ⟨complexTorusCoverProjection n z,
    subset_closure htest, ?_⟩
  rfl

private theorem integrable_sourceAngularDerivativeLift
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : Continuous f)
    (hfc : HasCompactSupport f)
    (v : TorusCharacters.LogSpace n) :
    Integrable (sourceAngularDerivativeLift f v)
      (coverWeightedMeasure (matrixSourceCoverPotential φ)) := by
  let : IsLocallyFiniteMeasure
      (coverWeightedMeasure (matrixSourceCoverPotential φ)) :=
    coverWeightedMeasure_isLocallyFinite
      (continuous_matrixSourceCoverPotential hφ)
  exact (continuous_sourceAngularDerivativeLift
    hf v).integrable_of_hasCompactSupport
      (hasCompactSupport_sourceAngularDerivativeLift hfc v)

private theorem fderiv_periodic
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q))
    (q : Fin n → ℤ) :
    Function.Periodic (fderiv ℝ F)
      (TorusCharacters.imaginaryShift q) := by
  intro z
  have he :
      (fun w : TorusCharacters.LogSpace n =>
        F (w + TorusCharacters.imaginaryShift q)) = F :=
    funext (hperiod q)
  have hd := congrArg
    (fun G : TorusCharacters.LogSpace n → ℂ =>
      fderiv ℝ G z) he
  change
    fderiv ℝ
      (fun w : TorusCharacters.LogSpace n =>
        F (w + TorusCharacters.imaginaryShift q)) z =
      fderiv ℝ F z at hd
  rw [fderiv_comp_add_right] at hd
  exact hd

private theorem holomorphicCoordinate_periodic
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q))
    (j : Fin n) (q : Fin n → ℤ) :
    Function.Periodic (fun z => holomorphicCoordinate F z j)
      (TorusCharacters.imaginaryShift q) := by
  intro z
  change
    holomorphicCoordinate F
      (z + TorusCharacters.imaginaryShift q) j =
    holomorphicCoordinate F z j
  unfold holomorphicCoordinate
  rw [fderiv_periodic F hperiod q z]

private theorem matrixSourceCoverPotential_periodic
    {n : ℕ} (φ : Space n → ℝ)
    (q : Fin n → ℤ) :
    Function.Periodic (matrixSourceCoverPotential φ)
      (TorusCharacters.imaginaryShift q) := by
  intro z
  change
    φ (complexTorusCoverProjection n
      (z + TorusCharacters.imaginaryShift q)).1 =
    φ (complexTorusCoverProjection n z).1
  rw [complexTorusCoverProjection_imaginaryShift]

private theorem fderiv_complex_mul_apply
    {n : ℕ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℝ F)
    (hG : Differentiable ℝ G)
    (z v : TorusCharacters.LogSpace n) :
    (fderiv ℝ (fun w => F w * G w) z) v =
      F z * (fderiv ℝ G z) v +
        G z * (fderiv ℝ F z) v := by
  have h := congrArg
    (fun A : TorusCharacters.LogSpace n →L[ℝ] ℂ => A v)
    (fderiv_fun_mul (hF z) (hG z))
  simpa only [_root_.add_apply, _root_.smul_apply, smul_eq_mul] using h

private theorem barPartialCoordinate_mul
    {n : ℕ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℝ F)
    (hG : Differentiable ℝ G)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    barPartialCoordinate (fun w => F w * G w) z j =
      F z * barPartialCoordinate G z j +
        G z * barPartialCoordinate F z j := by
  unfold barPartialCoordinate
  rw [fderiv_complex_mul_apply hF hG z (Pi.single j (1 : ℂ)),
    fderiv_complex_mul_apply hF hG z (Pi.single j Complex.I)]
  ring

private theorem holomorphicCoordinate_mul
    {n : ℕ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℝ F)
    (hG : Differentiable ℝ G)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    holomorphicCoordinate (fun w => F w * G w) z j =
      F z * holomorphicCoordinate G z j +
        G z * holomorphicCoordinate F z j := by
  unfold holomorphicCoordinate
  rw [fderiv_complex_mul_apply hF hG z (Pi.single j (1 : ℂ)),
    fderiv_complex_mul_apply hF hG z (Pi.single j Complex.I)]
  ring

private theorem weightedHolomorphicDerivative_mul
    {n : ℕ}
    (a : TorusCharacters.LogSpace n → ℝ)
    {F G : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℝ F)
    (hG : Differentiable ℝ G)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    weightedHolomorphicDerivative a
      (fun w => F w * G w) j z =
      F z * weightedHolomorphicDerivative a G j z +
        G z * holomorphicCoordinate F z j := by
  unfold weightedHolomorphicDerivative
  rw [holomorphicCoordinate_mul hF hG z j]
  ring

private theorem integral_holomorphicCoordinate_coverAngularSmoothPartition_mul_lift_eq_zero
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : Continuous f)
    (hfc : HasCompactSupport f)
    (j : Fin n) :
    (∫ z : TorusCharacters.LogSpace n,
      holomorphicCoordinate
        (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
        f (complexTorusCoverProjection n z)
      ∂(coverWeightedMeasure (matrixSourceCoverPotential φ))) = 0 := by
  let μ : Measure (TorusCharacters.LogSpace n) :=
    coverWeightedMeasure (matrixSourceCoverPotential φ)
  let v₀ : TorusCharacters.LogSpace n :=
    Pi.single j (1 : ℂ)
  let v₁ : TorusCharacters.LogSpace n :=
    Pi.single j Complex.I
  let d₀ := sourceAngularDerivativeLift f v₀
  let d₁ := sourceAngularDerivativeLift f v₁
  have hi₀ : Integrable d₀ μ :=
    integrable_sourceAngularDerivativeLift hφ hf hfc v₀
  have hi₁ : Integrable d₁ μ :=
    integrable_sourceAngularDerivativeLift hφ hf hfc v₁
  have hz₀ : (∫ z, d₀ z ∂μ) = 0 :=
    integral_fderiv_coverAngularSmoothPartition_mul_lift_eq_zero
      hφ hf hfc v₀
  have hz₁ : (∫ z, d₁ z ∂μ) = 0 :=
    integral_fderiv_coverAngularSmoothPartition_mul_lift_eq_zero
      hφ hf hfc v₁
  have hI :
      (∫ z, Complex.I * d₁ z ∂μ) =
        Complex.I * (∫ z, d₁ z ∂μ) :=
    MeasureTheory.integral_const_mul Complex.I d₁
  have hη : Differentiable ℝ
      (coverAngularSmoothPartition (n := n)) :=
    (contDiff_coverAngularSmoothPartition
      (n := n) (m := 1)).differentiable (by simp only [WithTop.coe_one, ne_eq, one_ne_zero,
        not_false_eq_true])
  change
    (∫ z : TorusCharacters.LogSpace n,
      holomorphicCoordinate
        (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
        f (complexTorusCoverProjection n z) ∂μ) = 0
  calc
    _ = ∫ z : TorusCharacters.LogSpace n,
      (d₀ z - Complex.I * d₁ z) / 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      unfold holomorphicCoordinate
      rw [DolbeaultGraphDistributionBridge.fderiv_complexOfReal
        hη z v₀,
        DolbeaultGraphDistributionBridge.fderiv_complexOfReal
          hη z v₁]
      change
        (((fderiv ℝ (coverAngularSmoothPartition (n := n)) z)
          v₀ : ℂ) -
          Complex.I *
            ((fderiv ℝ (coverAngularSmoothPartition (n := n)) z)
              v₁ : ℂ)) / 2 *
            f (complexTorusCoverProjection n z) =
          (d₀ z - Complex.I * d₁ z) / 2
      dsimp [d₀, d₁, sourceAngularDerivativeLift]
      ring
    _ = ((∫ z, d₀ z ∂μ) -
      Complex.I * (∫ z, d₁ z ∂μ)) / 2 := by
      rw [MeasureTheory.integral_div,
        MeasureTheory.integral_sub hi₀ (hi₁.const_mul Complex.I),
        hI]
    _ = 0 := by rw [hz₀, hz₁]; norm_num

private theorem integral_barPartialCoordinate_coverAngularSmoothPartition_mul_lift_eq_zero
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : Continuous f)
    (hfc : HasCompactSupport f)
    (j : Fin n) :
    (∫ z : TorusCharacters.LogSpace n,
      barPartialCoordinate
        (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
        f (complexTorusCoverProjection n z)
      ∂(coverWeightedMeasure (matrixSourceCoverPotential φ))) = 0 := by
  let μ : Measure (TorusCharacters.LogSpace n) :=
    coverWeightedMeasure (matrixSourceCoverPotential φ)
  let v₀ : TorusCharacters.LogSpace n :=
    Pi.single j (1 : ℂ)
  let v₁ : TorusCharacters.LogSpace n :=
    Pi.single j Complex.I
  let d₀ := sourceAngularDerivativeLift f v₀
  let d₁ := sourceAngularDerivativeLift f v₁
  have hi₀ : Integrable d₀ μ :=
    integrable_sourceAngularDerivativeLift hφ hf hfc v₀
  have hi₁ : Integrable d₁ μ :=
    integrable_sourceAngularDerivativeLift hφ hf hfc v₁
  have hz₀ : (∫ z, d₀ z ∂μ) = 0 :=
    integral_fderiv_coverAngularSmoothPartition_mul_lift_eq_zero
      hφ hf hfc v₀
  have hz₁ : (∫ z, d₁ z ∂μ) = 0 :=
    integral_fderiv_coverAngularSmoothPartition_mul_lift_eq_zero
      hφ hf hfc v₁
  have hI :
      (∫ z, Complex.I * d₁ z ∂μ) =
        Complex.I * (∫ z, d₁ z ∂μ) :=
    MeasureTheory.integral_const_mul Complex.I d₁
  have hη : Differentiable ℝ
      (coverAngularSmoothPartition (n := n)) :=
    (contDiff_coverAngularSmoothPartition
      (n := n) (m := 1)).differentiable (by simp only [WithTop.coe_one, ne_eq, one_ne_zero,
        not_false_eq_true])
  change
    (∫ z : TorusCharacters.LogSpace n,
      barPartialCoordinate
        (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
        f (complexTorusCoverProjection n z) ∂μ) = 0
  calc
    _ = ∫ z : TorusCharacters.LogSpace n,
      (d₀ z + Complex.I * d₁ z) / 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      unfold barPartialCoordinate
      rw [DolbeaultGraphDistributionBridge.fderiv_complexOfReal
        hη z v₀,
        DolbeaultGraphDistributionBridge.fderiv_complexOfReal
          hη z v₁]
      change
        (((fderiv ℝ (coverAngularSmoothPartition (n := n)) z)
          v₀ : ℂ) +
          Complex.I *
            ((fderiv ℝ (coverAngularSmoothPartition (n := n)) z)
              v₁ : ℂ)) / 2 *
            f (complexTorusCoverProjection n z) =
          (d₀ z + Complex.I * d₁ z) / 2
      dsimp [d₀, d₁, sourceAngularDerivativeLift]
      ring
    _ = ((∫ z, d₀ z ∂μ) +
      Complex.I * (∫ z, d₁ z ∂μ)) / 2 := by
      rw [MeasureTheory.integral_div,
        MeasureTheory.integral_add hi₀ (hi₁.const_mul Complex.I),
        hI]
    _ = 0 := by rw [hz₀, hz₁]; norm_num

private theorem conj_holomorphicCoordinate_real
    {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : Differentiable ℝ ψ)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    conj (holomorphicCoordinate (fun w => (ψ w : ℂ)) z j) =
      barPartialCoordinate (fun w => (ψ w : ℂ)) z j := by
  unfold holomorphicCoordinate barPartialCoordinate
  rw [DolbeaultGraphDistributionBridge.fderiv_complexOfReal
    hψ z (Pi.single j (1 : ℂ)),
    DolbeaultGraphDistributionBridge.fderiv_complexOfReal
      hψ z (Pi.single j Complex.I)]
  simp only [map_div₀, map_sub, map_mul, Complex.conj_I,
    Complex.conj_ofReal, map_ofNat]
  ring

private theorem conj_barPartialCoordinate_real
    {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : Differentiable ℝ ψ)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    conj (barPartialCoordinate (fun w => (ψ w : ℂ)) z j) =
      holomorphicCoordinate (fun w => (ψ w : ℂ)) z j := by
  have h := congrArg conj (conj_holomorphicCoordinate_real hψ z j)
  simpa only [RingHomCompTriple.comp_apply, RingHom.id_apply] using h.symm

private theorem directionalDerivative_periodic
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q))
    (v : TorusCharacters.LogSpace n)
    (q : Fin n → ℤ) :
    Function.Periodic
      (fun z : TorusCharacters.LogSpace n =>
        (fderiv ℝ F z) v)
      (TorusCharacters.imaginaryShift q) := by
  intro z
  exact congrArg
    (fun A : TorusCharacters.LogSpace n →L[ℝ] ℂ => A v)
    (fderiv_periodic F hperiod q z)

private def torusDirectionalDerivativeRepresentative
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (v : TorusCharacters.LogSpace n) :
    WeightedTorusHilbert.LogTorus n → ℂ :=
  torusScalarRepresentative
    (fun z : TorusCharacters.LogSpace n =>
      (fderiv ℝ F z) v)

private theorem tsupport_torusDirectionalDerivativeRepresentative_subset
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q))
    (v : TorusCharacters.LogSpace n) :
    tsupport (torusDirectionalDerivativeRepresentative F v) ⊆
      tsupport (torusScalarRepresentative F) := by
  apply closure_minimal
    (t := tsupport (torusScalarRepresentative F))
    ?_ (isClosed_tsupport _)
  intro p hp
  by_contra hn
  obtain ⟨z, hz⟩ :=
    (complexTorusCoverProjection_isOpenQuotientMap n).surjective p
  let g : WeightedTorusHilbert.LogTorus n → ℂ :=
    torusScalarRepresentative F
  have hsubset :
      tsupport (complexTorusCoverLift g) ⊆
        (complexTorusCoverProjection n) ⁻¹' tsupport g := by
    have hlift : complexTorusCoverLift g =
        g ∘ complexTorusCoverProjection n := by
      funext z
      rfl
    rw [hlift]
    exact tsupport_comp_subset_preimage g
      (continuous_complexTorusCoverProjection n)
  have hnot : z ∉ tsupport (complexTorusCoverLift g) := by
    intro h
    apply hn
    have hp' := hsubset h
    simpa only [mem_preimage, hz] using hp'
  have hrec : complexTorusCoverLift g = F :=
    complexTorusCoverLift_torusScalarRepresentative_eq F hperiod
  have hderzero : fderiv ℝ F z = 0 := by
    rw [← hrec]
    exact fderiv_of_notMem_tsupport ℝ hnot
  have hrep := congrFun
    (complexTorusCoverLift_torusScalarRepresentative_eq
      (fun w : TorusCharacters.LogSpace n =>
        (fderiv ℝ F w) v)
      (fun q => directionalDerivative_periodic F hperiod v q)) z
  change torusDirectionalDerivativeRepresentative F v p ≠ 0 at hp
  change
    torusDirectionalDerivativeRepresentative F v
      (complexTorusCoverProjection n z) =
        (fderiv ℝ F z) v at hrep
  rw [hz] at hrep
  apply hp
  rw [hrep, hderzero]
  simp only [_root_.zero_apply]

private theorem hasCompactSupport_torusDirectionalDerivativeRepresentative
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q))
    (hcompact : HasCompactSupport (torusScalarRepresentative F))
    (v : TorusCharacters.LogSpace n) :
    HasCompactSupport (torusDirectionalDerivativeRepresentative F v) := by
  exact hcompact.of_isClosed_subset
    (isClosed_tsupport (torusDirectionalDerivativeRepresentative F v))
    (tsupport_torusDirectionalDerivativeRepresentative_subset
      F hperiod v)

private def sourceTorusBarPartial
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (j : Fin n) : WeightedTorusHilbert.LogTorus n → ℂ :=
  torusScalarRepresentative
    (fun z => barPartialCoordinate F z j)

private def sourceTorusHolomorphicDerivative
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (j : Fin n) : WeightedTorusHilbert.LogTorus n → ℂ :=
  torusScalarRepresentative
    (fun z => holomorphicCoordinate F z j)

private theorem continuous_sourceTorusBarPartial
    {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 2 F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q))
    (j : Fin n) :
    Continuous (sourceTorusBarPartial F j) := by
  unfold sourceTorusBarPartial
  exact continuous_torusScalarRepresentative_of_periodic
    (continuous_barPartialCoordinate
      (hF.of_le (by norm_num)) j)
    (fun q => barPartialCoordinate_periodic F hperiod j q)

private theorem hasCompactSupport_sourceTorusBarPartial
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q))
    (hcompact : HasCompactSupport (torusScalarRepresentative F))
    (j : Fin n) :
    HasCompactSupport (sourceTorusBarPartial F j) := by
  let v₀ : TorusCharacters.LogSpace n :=
    Pi.single j (1 : ℂ)
  let v₁ : TorusCharacters.LogSpace n :=
    Pi.single j Complex.I
  have hs : HasCompactSupport
      (fun p : WeightedTorusHilbert.LogTorus n =>
        torusDirectionalDerivativeRepresentative F v₀ p +
          Complex.I *
            torusDirectionalDerivativeRepresentative F v₁ p) := by
    exact (hasCompactSupport_torusDirectionalDerivativeRepresentative
      F hperiod hcompact v₀).add
      ((hasCompactSupport_torusDirectionalDerivativeRepresentative
        F hperiod hcompact v₁).mul_left)
  have hp := hs.mul_right
    (f' := fun _ : WeightedTorusHilbert.LogTorus n =>
      ((2 : ℂ)⁻¹))
  change HasCompactSupport
    (fun p : WeightedTorusHilbert.LogTorus n =>
      (torusDirectionalDerivativeRepresentative F v₀ p +
        Complex.I * torusDirectionalDerivativeRepresentative F v₁ p) *
        ((2 : ℂ)⁻¹)) at hp
  have hfunction :
      (fun p : WeightedTorusHilbert.LogTorus n =>
        (torusDirectionalDerivativeRepresentative F v₀ p +
          Complex.I * torusDirectionalDerivativeRepresentative F v₁ p) *
          ((2 : ℂ)⁻¹)) = sourceTorusBarPartial F j := by
    funext p
    change
      ((fderiv ℝ F _) (Pi.single j (1 : ℂ)) +
        Complex.I * (fderiv ℝ F _) (Pi.single j Complex.I)) *
          ((2 : ℂ)⁻¹) =
        ((fderiv ℝ F _) (Pi.single j (1 : ℂ)) +
          Complex.I * (fderiv ℝ F _) (Pi.single j Complex.I)) / 2
    exact (div_eq_mul_inv _ _).symm
  rw [hfunction] at hp
  exact hp

private theorem hasCompactSupport_sourceTorusHolomorphicDerivative
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q))
    (hcompact : HasCompactSupport (torusScalarRepresentative F))
    (j : Fin n) :
    HasCompactSupport (sourceTorusHolomorphicDerivative F j) := by
  let v₀ : TorusCharacters.LogSpace n :=
    Pi.single j (1 : ℂ)
  let v₁ : TorusCharacters.LogSpace n :=
    Pi.single j Complex.I
  have hs : HasCompactSupport
      (fun p : WeightedTorusHilbert.LogTorus n =>
        torusDirectionalDerivativeRepresentative F v₀ p -
          Complex.I *
            torusDirectionalDerivativeRepresentative F v₁ p) := by
    exact (hasCompactSupport_torusDirectionalDerivativeRepresentative
      F hperiod hcompact v₀).sub
      ((hasCompactSupport_torusDirectionalDerivativeRepresentative
        F hperiod hcompact v₁).mul_left)
  have hp := hs.mul_right
    (f' := fun _ : WeightedTorusHilbert.LogTorus n =>
      ((2 : ℂ)⁻¹))
  change HasCompactSupport
    (fun p : WeightedTorusHilbert.LogTorus n =>
      (torusDirectionalDerivativeRepresentative F v₀ p -
        Complex.I * torusDirectionalDerivativeRepresentative F v₁ p) *
        ((2 : ℂ)⁻¹)) at hp
  have hfunction :
      (fun p : WeightedTorusHilbert.LogTorus n =>
        (torusDirectionalDerivativeRepresentative F v₀ p -
          Complex.I * torusDirectionalDerivativeRepresentative F v₁ p) *
          ((2 : ℂ)⁻¹)) = sourceTorusHolomorphicDerivative F j := by
    funext p
    change
      ((fderiv ℝ F _) (Pi.single j (1 : ℂ)) -
        Complex.I * (fderiv ℝ F _) (Pi.single j Complex.I)) *
          ((2 : ℂ)⁻¹) =
        ((fderiv ℝ F _) (Pi.single j (1 : ℂ)) -
          Complex.I * (fderiv ℝ F _) (Pi.single j Complex.I)) / 2
    exact (div_eq_mul_inv _ _).symm
  rw [hfunction] at hp
  exact hp

private theorem hasCompactSupport_sourceTorusConj
    {n : ℕ}
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : HasCompactSupport f) :
    HasCompactSupport (fun p => conj (f p)) := by
  apply hf.mono
  intro p hp
  change conj (f p) ≠ 0 at hp
  change f p ≠ 0
  intro hzero
  apply hp
  rw [hzero, map_zero]

private def sourceTorusFormMixedDerivativeDensity
    {n : ℕ}
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (p : WeightedTorusHilbert.LogTorus n) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n,
    sourceTorusBarPartial (fun z => W z i) j p *
      conj (sourceTorusBarPartial (fun z => W z j) i p)

private def sourceTorusFormFullDerivativeDensity
    {n : ℕ}
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (p : WeightedTorusHilbert.LogTorus n) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n,
    sourceTorusBarPartial (fun z => W z i) j p *
      conj (sourceTorusBarPartial (fun z => W z i) j p)

private def sourceTorusFormExteriorDerivativeDensity
    {n : ℕ}
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (p : WeightedTorusHilbert.LogTorus n) : ℂ :=
  (∑ i : Fin n, ∑ j : Fin n,
    (sourceTorusBarPartial (fun z => W z i) j p -
      sourceTorusBarPartial (fun z => W z j) i p) *
      conj
        (sourceTorusBarPartial (fun z => W z i) j p -
          sourceTorusBarPartial (fun z => W z j) i p)) / 2

private theorem sourceTorusFormExterior_add_mixed_eq_full
    {n : ℕ}
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (p : WeightedTorusHilbert.LogTorus n) :
    sourceTorusFormExteriorDerivativeDensity W p +
      sourceTorusFormMixedDerivativeDensity W p =
        sourceTorusFormFullDerivativeDensity W p := by
  exact antisymmetric_matrix_energy_add_cross
    (fun i j => sourceTorusBarPartial (fun z => W z i) j p)

end MatrixTorusBochnerIdentity

namespace MatrixTorusBochnerCore

open Set Function MeasureTheory Filter Matrix
open EqualitySaturatingKillingPaths WeightedTorusDistributionBridge WeightedDolbeaultBochnerIdentity
open ComplexMatrixWeightedHilbert MatrixTorusBochnerBridge MatrixTorusBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

private def sourceCoverRadialLinear (n : ℕ) :
    TorusCharacters.LogSpace n →L[ℝ] Space n :=
  (ContinuousLinearMap.fst ℝ
    (Space n) (Space n)).comp
    (logarithmicCoordinatesEquiv n).symm.toContinuousLinearMap

@[simp] private theorem sourceCoverRadialLinear_apply
    {n : ℕ} (z : TorusCharacters.LogSpace n)
    (i : Fin n) :
    sourceCoverRadialLinear n z i = 2 * (z i).re := by
  rfl

private theorem sourceCoverRadialLinear_single_one
    {n : ℕ} (j : Fin n) :
    sourceCoverRadialLinear n (Pi.single j (1 : ℂ)) =
      (2 : ℝ) • (Pi.single j (1 : ℝ) : Space n) := by
  funext i
  by_cases h : i = j
  · subst i
    simp only [sourceCoverRadialLinear_apply, Pi.single_eq_same, Complex.one_re, mul_one,
      Pi.smul_apply, smul_eq_mul]
  · simp only [sourceCoverRadialLinear_apply, ne_eq, h, not_false_eq_true, Pi.single_eq_of_ne,
      Complex.zero_re, mul_zero, Pi.smul_apply, smul_eq_mul]

private theorem sourceCoverRadialLinear_single_I
    {n : ℕ} (j : Fin n) :
    sourceCoverRadialLinear n (Pi.single j Complex.I) = 0 := by
  funext i
  by_cases h : i = j
  · subst i
    simp only [sourceCoverRadialLinear_apply, Pi.single_eq_same, Complex.I_re, mul_zero,
      Pi.zero_apply]
  · simp only [sourceCoverRadialLinear_apply, ne_eq, h, not_false_eq_true, Pi.single_eq_of_ne,
      Complex.zero_re, mul_zero, Pi.zero_apply]

private theorem fderiv_sourceCoverRadialComp_apply
    {n : ℕ}
    {ψ : Space n → ℝ}
    (hψ : Differentiable ℝ ψ)
    (z v : TorusCharacters.LogSpace n) :
    (fderiv ℝ
      (fun w : TorusCharacters.LogSpace n =>
        ψ (sourceCoverRadialLinear n w)) z) v =
      (fderiv ℝ ψ (sourceCoverRadialLinear n z))
        (sourceCoverRadialLinear n v) := by
  have hd := (hψ (sourceCoverRadialLinear n z)).hasFDerivAt.comp z
    (sourceCoverRadialLinear n).hasFDerivAt
  have hp := congrArg
    (fun A : TorusCharacters.LogSpace n →L[ℝ] ℝ => A v)
    hd.fderiv
  simpa only [comp_def, ContinuousLinearMap.comp_apply] using hp

private theorem fderiv_matrixSourceCoverPotential_apply
    {n : ℕ}
    {φ : Space n → ℝ}
    (hφ : Differentiable ℝ φ)
    (z v : TorusCharacters.LogSpace n) :
    (fderiv ℝ (matrixSourceCoverPotential φ) z) v =
      (fderiv ℝ φ (sourceCoverRadialLinear n z))
        (sourceCoverRadialLinear n v) := by
  exact fderiv_sourceCoverRadialComp_apply hφ z v

private theorem holomorphicCoordinate_matrixSourceCoverPotential
    {n : ℕ}
    {φ : Space n → ℝ}
    (hφ : Differentiable ℝ φ)
    (z : TorusCharacters.LogSpace n)
    (i : Fin n) :
    holomorphicCoordinate
      (fun w : TorusCharacters.LogSpace n =>
        (matrixSourceCoverPotential φ w : ℂ)) z i =
      ((fderiv ℝ φ (sourceCoverRadialLinear n z))
        (Pi.single i (1 : ℝ)) : ℂ) := by
  have hrad : Differentiable ℝ (matrixSourceCoverPotential φ) := by
    exact hφ.comp (sourceCoverRadialLinear n).differentiable
  unfold holomorphicCoordinate
  rw [DolbeaultGraphDistributionBridge.fderiv_complexOfReal
    hrad z (Pi.single i (1 : ℂ)),
    DolbeaultGraphDistributionBridge.fderiv_complexOfReal
      hrad z (Pi.single i Complex.I),
    fderiv_matrixSourceCoverPotential_apply hφ,
    fderiv_matrixSourceCoverPotential_apply hφ,
    sourceCoverRadialLinear_single_one,
    sourceCoverRadialLinear_single_I]
  simp only [map_smul, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_ofNat, map_zero,
    Complex.ofReal_zero, mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    mul_div_cancel_left₀]

private theorem contDiff_sourceRealDirectional
    {n : ℕ}
    {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ)
    (i : Fin n) :
    ContDiff ℝ 1
      (fun x : Space n =>
        (fderiv ℝ φ x) (Pi.single i (1 : ℝ))) := by
  have hp : ContDiff ℝ 1
      (fun q : Space n × Space n =>
        (fderiv ℝ φ q.1) q.2) :=
    hφ.contDiff_fderiv_apply (by norm_num)
  exact hp.comp (contDiff_id.prodMk contDiff_const)

private theorem barPartialCoordinate_sourceCoverRadialComp
    {n : ℕ}
    {ψ : Space n → ℝ}
    (hψ : Differentiable ℝ ψ)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    barPartialCoordinate
      (fun w : TorusCharacters.LogSpace n =>
        (ψ (sourceCoverRadialLinear n w) : ℂ)) z j =
      ((fderiv ℝ ψ (sourceCoverRadialLinear n z))
        (Pi.single j (1 : ℝ)) : ℂ) := by
  have hrad : Differentiable ℝ
      (fun w : TorusCharacters.LogSpace n =>
        ψ (sourceCoverRadialLinear n w)) :=
    hψ.comp (sourceCoverRadialLinear n).differentiable
  unfold barPartialCoordinate
  rw [DolbeaultGraphDistributionBridge.fderiv_complexOfReal
    hrad z (Pi.single j (1 : ℂ)),
    DolbeaultGraphDistributionBridge.fderiv_complexOfReal
      hrad z (Pi.single j Complex.I),
    fderiv_sourceCoverRadialComp_apply hψ,
    fderiv_sourceCoverRadialComp_apply hψ,
    sourceCoverRadialLinear_single_one,
    sourceCoverRadialLinear_single_I]
  simp only [map_smul, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_ofNat, map_zero,
    Complex.ofReal_zero, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    mul_div_cancel_left₀]

private theorem complexHessian_matrixSourceCoverPotential_eq_real_transpose
    {n : ℕ}
    {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ)
    (z : TorusCharacters.LogSpace n)
    (i j : Fin n) :
    complexHessian (matrixSourceCoverPotential φ) z i j =
      (sourceMatrixHessian φ
        (sourceCoverRadialLinear n z) j i : ℂ) := by
  let g : Space n → ℝ :=
    fun x => (fderiv ℝ φ x) (Pi.single i (1 : ℝ))
  have hg : Differentiable ℝ g :=
    (contDiff_sourceRealDirectional hφ i).differentiable
      (by norm_num)
  have hhol :
      (fun w : TorusCharacters.LogSpace n =>
        holomorphicCoordinate
          (fun ξ => (matrixSourceCoverPotential φ ξ : ℂ)) w i) =
      (fun w : TorusCharacters.LogSpace n =>
        (g (sourceCoverRadialLinear n w) : ℂ)) := by
    funext w
    exact holomorphicCoordinate_matrixSourceCoverPotential
      (hφ.differentiable (by norm_num)) w i
  unfold complexHessian
  rw [hhol, barPartialCoordinate_sourceCoverRadialComp hg z j]
  change
    ((fderiv ℝ
      (fun x : Space n =>
        (fderiv ℝ φ x) (Pi.single i (1 : ℝ)))
      (sourceCoverRadialLinear n z))
        (Pi.single j (1 : ℝ)) : ℂ) =
      (sourceMatrixHessian φ
        (sourceCoverRadialLinear n z) j i : ℂ)
  rw [WeightedBochner.fderiv_coordinate_eval
    hφ (sourceCoverRadialLinear n z)
    (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ))]
  unfold sourceMatrixHessian
    BergmanAsymptotics.actualHessianMatrix
  rw [LinearMap.toMatrix₂'_apply]
  rfl

private theorem sourceMatrixHessian_entry_symm
    {n : ℕ}
    {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ)
    (x : Space n)
    (i j : Fin n) :
    sourceMatrixHessian φ x i j =
      sourceMatrixHessian φ x j i := by
  unfold sourceMatrixHessian
    BergmanAsymptotics.actualHessianMatrix
  rw [LinearMap.toMatrix₂'_apply,
    LinearMap.toMatrix₂'_apply]
  change
    ((fderiv ℝ (fderiv ℝ φ) x)
      (Pi.single i (1 : ℝ))) (Pi.single j (1 : ℝ)) =
      ((fderiv ℝ (fderiv ℝ φ) x)
        (Pi.single j (1 : ℝ))) (Pi.single i (1 : ℝ))
  exact (hφ.contDiffAt.isSymmSndFDerivAt
    (by norm_num)).eq (Pi.single i (1 : ℝ))
      (Pi.single j (1 : ℝ))

private theorem complexHessian_matrixSourceCoverPotential_eq_real
    {n : ℕ}
    {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ)
    (z : TorusCharacters.LogSpace n)
    (i j : Fin n) :
    complexHessian (matrixSourceCoverPotential φ) z i j =
      (sourceMatrixHessian φ
        (sourceCoverRadialLinear n z) i j : ℂ) := by
  rw [complexHessian_matrixSourceCoverPotential_eq_real_transpose
    hφ z i j,
    sourceMatrixHessian_entry_symm hφ
      (sourceCoverRadialLinear n z) j i]

private theorem sourceTorusFormFullDerivativeDensity_re_nonneg
    {n : ℕ}
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (p : WeightedTorusHilbert.LogTorus n) :
    0 ≤ (sourceTorusFormFullDerivativeDensity W p).re := by
  unfold sourceTorusFormFullDerivativeDensity
  simp_rw [Complex.mul_conj, Complex.re_sum, Complex.ofReal_re]
  exact Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ =>
      Complex.normSq_nonneg
        (sourceTorusBarPartial (fun z => W z i) j p)))

end MatrixTorusBochnerCore

namespace MatrixTorusBochnerCoreDensity

open Set Function MeasureTheory Filter Matrix
open MatrixTorusBochnerCore WeightedResolventConstantCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

private def sourceRadialCutoff {n : ℕ} (m : ℕ)
    (p : WeightedTorusHilbert.LogTorus n) : ℝ :=
  growingBump m p.1

private def sourceCoverRadialCutoff {n : ℕ} (m : ℕ)
    (z : TorusCharacters.LogSpace n) : ℝ :=
  growingBump m (sourceCoverRadialLinear n z)

private theorem sourceRadialCutoff_hasCompactSupport
    {n : ℕ} (m : ℕ) :
    HasCompactSupport (sourceRadialCutoff (n := n) m) := by
  let K : Set (WeightedTorusHilbert.LogTorus n) :=
    tsupport (fun x : Space n => growingBump m x) ×ˢ
      (Set.univ : Set (TorusCharacters.AngularTorus n))
  have hK : IsCompact K :=
    (growingBump (n := n) m).hasCompactSupport.prod isCompact_univ
  apply HasCompactSupport.intro hK
  intro p hp
  have hrad :
      p.1 ∉ tsupport
        (fun x : Space n => growingBump m x) := by
    intro hx
    apply hp
    exact ⟨hx, Set.mem_univ p.2⟩
  change growingBump m p.1 = 0
  exact image_eq_zero_of_notMem_tsupport hrad

private theorem sourceRadialCutoff_eventually_one
    {n : ℕ}
    (p : WeightedTorusHilbert.LogTorus n) :
    ∀ᶠ m : ℕ in atTop, sourceRadialCutoff m p = 1 :=
  growingBump_eventually_one p.1

private theorem contDiff_sourceCoverRadialCutoff
    {n : ℕ} (m : ℕ) :
    ContDiff ℝ 2 (sourceCoverRadialCutoff (n := n) m) := by
  exact (growingBump (n := n) m).contDiff.comp
    (sourceCoverRadialLinear n).contDiff

private theorem sourceCoverRadialLinear_imaginaryShift
    {n : ℕ}
    (z : TorusCharacters.LogSpace n)
    (q : Fin n → ℤ) :
    sourceCoverRadialLinear n
        (z + TorusCharacters.imaginaryShift q) =
      sourceCoverRadialLinear n z := by
  funext i
  simp only [sourceCoverRadialLinear_apply, Pi.add_apply, TorusCharacters.imaginaryShift,
    Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.re_ofNat, Complex.ofReal_re,
    Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero, Complex.I_re, Complex.mul_im,
    zero_mul, add_zero, Complex.I_im, mul_one, sub_self, Complex.intCast_im]

private theorem sourceCoverRadialCutoff_periodic
    {n : ℕ} (m : ℕ) (q : Fin n → ℤ) :
    Function.Periodic (sourceCoverRadialCutoff (n := n) m)
      (TorusCharacters.imaginaryShift q) := by
  intro z
  simp only [sourceCoverRadialCutoff, sourceCoverRadialLinear_imaginaryShift]

end MatrixTorusBochnerCoreDensity

namespace MatrixTorusBochnerCoreApproximation

open Set Function MeasureTheory Filter Matrix
open EqualitySaturatingKillingPaths ComplexKillingSaturationBridge MatrixTorusBochnerIdentity
open MatrixTorusBochnerCore MatrixTorusBochnerCoreDensity WeightedResolventConstantCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

private def complexSourceCoverRadialCutoff {n : ℕ} (m : ℕ)
    (z : TorusCharacters.LogSpace n) : ℂ :=
  (sourceCoverRadialCutoff m z : ℂ)

private theorem contDiff_complexSourceCoverRadialCutoff
    {n : ℕ} (m : ℕ) :
    ContDiff ℝ 2 (complexSourceCoverRadialCutoff (n := n) m) := by
  change ContDiff ℝ 2
    (Complex.ofRealCLM ∘ sourceCoverRadialCutoff (n := n) m)
  exact Complex.ofRealCLM.contDiff.comp
    (contDiff_sourceCoverRadialCutoff m)

private theorem complexSourceCoverRadialCutoff_periodic
    {n : ℕ} (m : ℕ) (q : Fin n → ℤ) :
    Function.Periodic (complexSourceCoverRadialCutoff (n := n) m)
      (TorusCharacters.imaginaryShift q) := by
  intro z
  exact congrArg Complex.ofReal
    (sourceCoverRadialCutoff_periodic m q z)

private theorem torusScalarRepresentative_complexSourceCoverRadialCutoff
    {n : ℕ} (m : ℕ)
    (p : WeightedTorusHilbert.LogTorus n) :
    torusScalarRepresentative
      (complexSourceCoverRadialCutoff (n := n) m) p =
      (sourceRadialCutoff m p : ℂ) := by
  unfold torusScalarRepresentative
    JointHolomorphicLaurentFourierCompatibility.coverRepresentative
    complexSourceCoverRadialCutoff sourceCoverRadialCutoff
    sourceRadialCutoff
  congr 2
  funext i
  simp only [sourceCoverRadialLinear_apply, Complex.add_re, Complex.div_ofNat_re, Complex.ofReal_re,
    Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.I_re, Complex.mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self]
  ring

private theorem complexSourceRadialCutoff_hasCompactSupport
    {n : ℕ} (m : ℕ) :
    HasCompactSupport
      (fun p : WeightedTorusHilbert.LogTorus n =>
        (sourceRadialCutoff m p : ℂ)) := by
  apply (sourceRadialCutoff_hasCompactSupport m).mono
  intro p hp
  change (sourceRadialCutoff m p : ℂ) ≠ 0 at hp
  change sourceRadialCutoff m p ≠ 0
  intro hzero
  apply hp
  simp only [hzero, Complex.ofReal_zero]

private def cutoffPhysicalField {n : ℕ} (m : ℕ)
    (W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n)
    (z : TorusCharacters.LogSpace n) :
    TorusCharacters.LogSpace n :=
  fun i => complexSourceCoverRadialCutoff m z * W z i

private theorem contDiff_cutoffPhysicalField {n : ℕ} (m : ℕ)
    {W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n}
    (hW : ContDiff ℝ 2 W) :
    ContDiff ℝ 2 (cutoffPhysicalField m W) := by
  apply contDiff_pi.mpr
  intro i
  exact (contDiff_complexSourceCoverRadialCutoff m).mul
    (contDiff_pi.mp hW i)

private theorem cutoffPhysicalField_periodic {n : ℕ} (m : ℕ)
    {W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n}
    (hW : ∀ q : Fin n → ℤ,
      Function.Periodic W
        (TorusCharacters.imaginaryShift q))
    (q : Fin n → ℤ) :
    Function.Periodic (cutoffPhysicalField m W)
      (TorusCharacters.imaginaryShift q) := by
  intro z
  funext i
  unfold cutoffPhysicalField
  rw [complexSourceCoverRadialCutoff_periodic m q z,
    congrFun (hW q z) i]

private theorem torusScalarRepresentative_cutoffPhysicalField
    {n : ℕ} (m : ℕ)
    (W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n)
    (i : Fin n)
    (p : WeightedTorusHilbert.LogTorus n) :
    torusScalarRepresentative
      (fun z => cutoffPhysicalField m W z i) p =
      (sourceRadialCutoff m p : ℂ) *
        torusScalarRepresentative (fun z => W z i) p := by
  rw [← torusScalarRepresentative_complexSourceCoverRadialCutoff m p]
  rfl

private theorem cutoffPhysicalField_coordinate_hasCompactSupport
    {n : ℕ} (m : ℕ)
    (W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n)
    (i : Fin n) :
    HasCompactSupport
      (torusScalarRepresentative
        (fun z => cutoffPhysicalField m W z i)) := by
  have hcompact :=
    (complexSourceRadialCutoff_hasCompactSupport (n := n) m).mul_right
      (f' := torusScalarRepresentative (fun z => W z i))
  have hfunction :
      torusScalarRepresentative
        (fun z => cutoffPhysicalField m W z i) =
      (fun p : WeightedTorusHilbert.LogTorus n =>
        (sourceRadialCutoff m p : ℂ) *
          torusScalarRepresentative (fun z => W z i) p) := by
    funext p
    exact torusScalarRepresentative_cutoffPhysicalField m W i p
  rw [hfunction]
  exact hcompact

private theorem torusFormRepresentative_cutoffPhysicalField
    {n : ℕ} (m : ℕ)
    (W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n)
    (p : WeightedTorusHilbert.LogTorus n) :
    torusFormRepresentative (cutoffPhysicalField m W) p =
      (sourceRadialCutoff m p : ℂ) •
        torusFormRepresentative W p := by
  ext i
  change torusScalarRepresentative
    (fun z => cutoffPhysicalField m W z i) p =
      (sourceRadialCutoff m p : ℂ) *
        torusScalarRepresentative (fun z => W z i) p
  exact torusScalarRepresentative_cutoffPhysicalField m W i p

private theorem continuous_torusFormRepresentative_of_smooth_periodic
    {n : ℕ}
    {W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n}
    (hW : ContDiff ℝ 2 W)
    (hWp : ∀ q : Fin n → ℤ,
      Function.Periodic W
        (TorusCharacters.imaginaryShift q)) :
    Continuous (torusFormRepresentative W) := by
  have hcoordinate (i : Fin n) :
      Continuous
        (torusScalarRepresentative (fun z => W z i)) := by
    apply continuous_torusScalarRepresentative_of_periodic
      (contDiff_pi.mp hW i).continuous
    intro q z
    exact congrFun (hWp q z) i
  change Continuous
    (fun p : WeightedTorusHilbert.LogTorus n =>
      WithLp.toLp 2
        (fun i : Fin n =>
          torusScalarRepresentative (fun z => W z i) p))
  exact (PiLp.continuous_toLp 2
    (fun _ : Fin n => ℂ)).comp
      (continuous_pi hcoordinate)

private theorem continuous_sourceRadialCutoff
    {n : ℕ} (m : ℕ) :
    Continuous (sourceRadialCutoff (n := n) m) := by
  exact ((growingBump (n := n) m).contDiff
    (n := 2)).continuous.comp continuous_fst

private theorem sourceRadialCutoff_nonneg
    {n : ℕ} (m : ℕ)
    (p : WeightedTorusHilbert.LogTorus n) :
    0 ≤ sourceRadialCutoff m p :=
  (growingBump (n := n) m).nonneg

private theorem sourceRadialCutoff_le_one
    {n : ℕ} (m : ℕ)
    (p : WeightedTorusHilbert.LogTorus n) :
    sourceRadialCutoff m p ≤ 1 :=
  (growingBump (n := n) m).le_one

private theorem complexLp_norm_sq_eq_integral
    {X : Type*} [MeasurableSpace X]
    {μ : Measure X}
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (f : MeasureTheory.Lp E 2 μ) :
    ‖f‖ ^ 2 = ∫ x : X, ‖f x‖ ^ 2 ∂μ := by
  calc
    ‖f‖ ^ 2 = RCLike.re
        (@inner ℂ (MeasureTheory.Lp E 2 μ) _ f f) :=
      norm_sq_eq_re_inner f
    _ = RCLike.re
        (∫ x : X, @inner ℂ E _ (f x) (f x) ∂μ) := by
      rw [MeasureTheory.L2.inner_def]
    _ = ∫ x : X,
        RCLike.re (@inner ℂ E _ (f x) (f x)) ∂μ :=
      (integral_re
        (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) f f)).symm
    _ = ∫ x : X, ‖f x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (norm_sq_eq_re_inner (f x)).symm

private theorem barPartialCoordinate_complexSourceCoverRadialCutoff
    {n : ℕ} (m : ℕ)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    barPartialCoordinate
      (complexSourceCoverRadialCutoff (n := n) m) z j =
      ((fderiv ℝ
        (fun x : Space n => growingBump m x)
        (sourceCoverRadialLinear n z))
          (Pi.single j (1 : ℝ)) : ℂ) := by
  exact barPartialCoordinate_sourceCoverRadialComp
    (((growingBump (n := n) m).contDiff
      (n := 1)).differentiable (by norm_num)) z j

private theorem sourceTorusBarPartial_complexSourceCoverRadialCutoff
    {n : ℕ} (m : ℕ)
    (j : Fin n)
    (p : WeightedTorusHilbert.LogTorus n) :
    sourceTorusBarPartial
      (complexSourceCoverRadialCutoff (n := n) m) j p =
      ((fderiv ℝ
        (fun x : Space n => growingBump m x) p.1)
          (Pi.single j (1 : ℝ)) : ℂ) := by
  unfold sourceTorusBarPartial torusScalarRepresentative
    JointHolomorphicLaurentFourierCompatibility.coverRepresentative
  change
    barPartialCoordinate
      (complexSourceCoverRadialCutoff m)
      (fun i : Fin n =>
        (p.1 i : ℂ) / 2 +
          (2 * (Real.pi : ℂ) * Complex.I) *
            ((AddCircle.equivIoc 1 0 (p.2 i)).1 : ℂ))
      j = _
  rw [barPartialCoordinate_complexSourceCoverRadialCutoff]
  have hrad :
      sourceCoverRadialLinear n
        (fun i : Fin n =>
          (p.1 i : ℂ) / 2 +
            (2 * (Real.pi : ℂ) * Complex.I) *
              ((AddCircle.equivIoc 1 0 (p.2 i)).1 : ℂ)) =
        p.1 := by
    funext i
    simp only [sourceCoverRadialLinear_apply, Complex.add_re, Complex.div_ofNat_re,
      Complex.ofReal_re,
      Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.I_re, Complex.mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self]
    ring
  rw [hrad]

private theorem torusScalarRepresentative_mul
    {n : ℕ}
    (F G : TorusCharacters.LogSpace n → ℂ)
    (p : WeightedTorusHilbert.LogTorus n) :
    torusScalarRepresentative (fun z => F z * G z) p =
      torusScalarRepresentative F p *
        torusScalarRepresentative G p := by
  rfl

private theorem torusScalarRepresentative_add
    {n : ℕ}
    (F G : TorusCharacters.LogSpace n → ℂ)
    (p : WeightedTorusHilbert.LogTorus n) :
    torusScalarRepresentative (fun z => F z + G z) p =
      torusScalarRepresentative F p +
        torusScalarRepresentative G p := by
  rfl

private theorem sourceTorusBarPartial_cutoffPhysicalField
    {n : ℕ} (m : ℕ)
    {W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n}
    (hW : ContDiff ℝ 2 W)
    (i j : Fin n)
    (p : WeightedTorusHilbert.LogTorus n) :
    sourceTorusBarPartial
      (fun z => cutoffPhysicalField m W z i) j p =
      (sourceRadialCutoff m p : ℂ) *
        sourceTorusBarPartial (fun z => W z i) j p +
      torusScalarRepresentative (fun z => W z i) p *
        sourceTorusBarPartial
          (complexSourceCoverRadialCutoff m) j p := by
  have hproduct :
      (fun z : TorusCharacters.LogSpace n =>
        barPartialCoordinate
          (fun w => complexSourceCoverRadialCutoff m w * W w i)
          z j) =
      (fun z : TorusCharacters.LogSpace n =>
        complexSourceCoverRadialCutoff m z *
          barPartialCoordinate (fun w => W w i) z j +
        W z i * barPartialCoordinate
          (complexSourceCoverRadialCutoff m) z j) := by
    funext z
    exact barPartialCoordinate_mul
      ((contDiff_complexSourceCoverRadialCutoff m).differentiable
        (by norm_num))
      ((contDiff_pi.mp hW i).differentiable
        (by norm_num)) z j
  unfold sourceTorusBarPartial
  change
    torusScalarRepresentative
      (fun z => barPartialCoordinate
        (fun w => complexSourceCoverRadialCutoff m w * W w i)
        z j) p = _
  rw [hproduct, torusScalarRepresentative_add,
    torusScalarRepresentative_mul,
    torusScalarRepresentative_mul,
    torusScalarRepresentative_complexSourceCoverRadialCutoff]

end MatrixTorusBochnerCoreApproximation

namespace MatrixTorusBochnerCoreConvergence

open Set Function MeasureTheory Filter Matrix
open WeightedBrascampLieb EqualitySaturatingKillingPaths ComplexKillingSaturationBridge
open MatrixTorusBochnerIdentity MatrixTorusBochnerCoreApproximation WeightedResolventConstantCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

private def complexEuclideanOuterProduct
    {ι κ : Type*}
    (v : EuclideanSpace ℂ ι)
    (w : EuclideanSpace ℂ κ) :
    EuclideanSpace ℂ (ι × κ) :=
  WithLp.toLp 2 (fun ij : ι × κ => v ij.1 * w ij.2)

private theorem complexEuclideanOuterProduct_norm
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : EuclideanSpace ℂ ι)
    (w : EuclideanSpace ℂ κ) :
    ‖complexEuclideanOuterProduct v w‖ = ‖v‖ * ‖w‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  calc
    ‖complexEuclideanOuterProduct v w‖ ^ 2 =
        ∑ ij : ι × κ,
          ‖(complexEuclideanOuterProduct v w) ij‖ ^ 2 :=
      EuclideanSpace.norm_sq_eq _
    _ = ∑ ij : ι × κ, ‖v ij.1‖ ^ 2 * ‖w ij.2‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro ij _
      change ‖v ij.1 * w ij.2‖ ^ 2 = _
      rw [norm_mul, mul_pow]
    _ = ∑ i : ι, ∑ j : κ, ‖v i‖ ^ 2 * ‖w j‖ ^ 2 :=
      Fintype.sum_prod_type _
    _ = (∑ i : ι, ‖v i‖ ^ 2) *
        (∑ j : κ, ‖w j‖ ^ 2) :=
      (Fintype.sum_mul_sum
        (fun i : ι => ‖v i‖ ^ 2)
        (fun j : κ => ‖w j‖ ^ 2)).symm
    _ = (‖v‖ * ‖w‖) ^ 2 := by
      rw [← EuclideanSpace.norm_sq_eq,
        ← EuclideanSpace.norm_sq_eq, mul_pow]

private def sourceCutoffBarGradient {n : ℕ} (m : ℕ)
    (p : WeightedTorusHilbert.LogTorus n) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun j : Fin n =>
    sourceTorusBarPartial
      (complexSourceCoverRadialCutoff m) j p)

private theorem sourceCutoffBarGradient_norm_eq
    {n : ℕ} (m : ℕ)
    (p : WeightedTorusHilbert.LogTorus n) :
    ‖sourceCutoffBarGradient m p‖ =
      ‖euclideanGradient
        (fun x : Space n => growingBump m x) p.1‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro j _
  change
    ‖sourceTorusBarPartial
      (complexSourceCoverRadialCutoff m) j p‖ ^ 2 =
      ‖(fderiv ℝ
        (fun x : Space n => growingBump m x) p.1)
          (Pi.single j (1 : ℝ))‖ ^ 2
  rw [sourceTorusBarPartial_complexSourceCoverRadialCutoff,
    Complex.norm_real]

private theorem sourceCutoffBarGradient_norm_le
    {n : ℕ} {C : ℝ}
    (hC : ∀ x : Space n,
      ‖euclideanGradient
        (fun y : Space n => unitBump y) x‖ ≤ C)
    (m : ℕ)
    (p : WeightedTorusHilbert.LogTorus n) :
    ‖sourceCutoffBarGradient m p‖ ≤
      ((m : ℝ) + 1)⁻¹ * C := by
  rw [sourceCutoffBarGradient_norm_eq]
  exact growingBump_euclideanGradient_norm_le hC m p.1

private def sourceCutoffDerivativeCommutator {n : ℕ} (m : ℕ)
    (W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n)
    (p : WeightedTorusHilbert.LogTorus n) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  WithLp.toLp 2 (fun ij : Fin n × Fin n =>
    torusScalarRepresentative (fun z => W z ij.1) p *
      sourceTorusBarPartial
        (complexSourceCoverRadialCutoff m) ij.2 p)

private theorem sourceCutoffDerivativeCommutator_eq_outerProduct
    {n : ℕ} (m : ℕ)
    (W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n)
    (p : WeightedTorusHilbert.LogTorus n) :
    sourceCutoffDerivativeCommutator m W p =
      complexEuclideanOuterProduct
        (torusFormRepresentative W p)
        (sourceCutoffBarGradient m p) := by
  ext ij
  rfl

private theorem continuous_sourceCutoffBarGradient
    {n : ℕ} (m : ℕ) :
    Continuous (sourceCutoffBarGradient (n := n) m) := by
  change Continuous
    (fun p : WeightedTorusHilbert.LogTorus n =>
      WithLp.toLp 2 (fun j : Fin n =>
        sourceTorusBarPartial
          (complexSourceCoverRadialCutoff m) j p))
  apply (PiLp.continuous_toLp 2
    (fun _ : Fin n => ℂ)).comp
  apply continuous_pi
  intro j
  exact continuous_sourceTorusBarPartial
    (contDiff_complexSourceCoverRadialCutoff m)
    (complexSourceCoverRadialCutoff_periodic m) j

private theorem continuous_sourceCutoffDerivativeCommutator
    {n : ℕ} (m : ℕ)
    {W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n}
    (hW : ContDiff ℝ 2 W)
    (hWp : ∀ q : Fin n → ℤ,
      Function.Periodic W
        (TorusCharacters.imaginaryShift q)) :
    Continuous (sourceCutoffDerivativeCommutator m W) := by
  change Continuous
    (fun p : WeightedTorusHilbert.LogTorus n =>
      WithLp.toLp 2 (fun ij : Fin n × Fin n =>
        torusScalarRepresentative (fun z => W z ij.1) p *
          sourceTorusBarPartial
            (complexSourceCoverRadialCutoff m) ij.2 p))
  apply (PiLp.continuous_toLp 2
    (fun _ : Fin n × Fin n => ℂ)).comp
  apply continuous_pi
  intro ij
  apply (continuous_torusScalarRepresentative_of_periodic
    (contDiff_pi.mp hW ij.1).continuous
    (fun q z => congrFun (hWp q z) ij.1)).mul
  exact continuous_sourceTorusBarPartial
    (contDiff_complexSourceCoverRadialCutoff m)
    (complexSourceCoverRadialCutoff_periodic m) ij.2

/-- Almost-everywhere norm domination gives the corresponding `L²` norm bound. -/
public
theorem complexLp_norm_le_of_ae_norm_le
    {X : Type*} [MeasurableSpace X]
    {μ : Measure X}
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : X → E} {g : X → F}
    (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ x : X ∂μ, ‖f x‖ ≤ C * ‖g x‖) :
    ‖hf.toLp f‖ ≤ C * ‖hg.toLp g‖ := by
  have hsemi :=
    MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      hbound (2 : ℝ≥0∞)
  have htop :
      ENNReal.ofReal C * eLpNorm g 2 μ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.eLpNorm_ne_top
  calc
    ‖hf.toLp f‖ = (eLpNorm f 2 μ).toReal :=
      MeasureTheory.Lp.norm_toLp f hf
    _ ≤ (ENNReal.ofReal C * eLpNorm g 2 μ).toReal :=
      ENNReal.toReal_mono htop hsemi
    _ = C * (eLpNorm g 2 μ).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC]
    _ = C * ‖hg.toLp g‖ := by
      rw [MeasureTheory.Lp.norm_toLp g hg]

end MatrixTorusBochnerCoreConvergence

namespace WeightedTorusDolbeault

open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence ComplexKillingSaturationBridge
open WeightedTorusDistributionBridge MatrixTorusBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

private def angularWeightedTorusDensity {n : ℕ}
    (a : LogTorus n → ℝ) (p : LogTorus n) : ℝ :=
  Real.exp (-a p)

private def angularWeightedTorusMeasure {n : ℕ}
    (a : LogTorus n → ℝ) : Measure (LogTorus n) :=
  (sourceTorusBaseMeasure n).withDensity
    (fun p => ENNReal.ofReal (angularWeightedTorusDensity a p))

private theorem angularWeightedTorusDensity_pos {n : ℕ}
    (a : LogTorus n → ℝ) (p : LogTorus n) :
    0 < angularWeightedTorusDensity a p :=
  Real.exp_pos _

private theorem continuous_angularWeightedTorusDensity {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a) :
    Continuous (angularWeightedTorusDensity a) :=
  Real.continuous_exp.comp ha.neg

private theorem angularWeightedTorusMeasure_isLocallyFinite {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a) :
    IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) := by
  let : IsLocallyFiniteMeasure (sourceTorusBaseMeasure n) := by
    simpa only [sourceTorusBaseMeasure, unweightedTorusMeasure] using
      unweightedTorusMeasure_isLocallyFinite n
  exact IsLocallyFiniteMeasure.withDensity_ofReal
    (continuous_angularWeightedTorusDensity ha)

private def angularCoverPotential {n : ℕ}
    (a : LogTorus n → ℝ) :
    TorusCharacters.LogSpace n → ℝ :=
  fun z => a (complexTorusCoverProjection n z)

private theorem angularCoverPotential_periodic {n : ℕ}
    (a : LogTorus n → ℝ) (q : Fin n → ℤ) :
    Function.Periodic (angularCoverPotential a)
      (TorusCharacters.imaginaryShift q) := by
  intro z
  simp only [angularCoverPotential, complexTorusCoverProjection_imaginaryShift]

private theorem continuous_angularCoverPotential {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a) :
    Continuous (angularCoverPotential a) :=
  ha.comp (continuous_complexTorusCoverProjection n)

private abbrev angularWeightedScalarL2 {n : ℕ}
    (a : LogTorus n → ℝ) :=
  MeasureTheory.Lp ℂ 2 (angularWeightedTorusMeasure a)

private abbrev angularWeightedFormL2 {n : ℕ}
    (a : LogTorus n → ℝ) :=
  MeasureTheory.Lp (EuclideanSpace ℂ (Fin n)) 2
    (angularWeightedTorusMeasure a)

private abbrev angularDolbeaultGraphAmbient {n : ℕ}
    (a : LogTorus n → ℝ) :=
  WithLp 2 (angularWeightedScalarL2 a × angularWeightedFormL2 a)

private def angularScalarL2OfRepresentative {n : ℕ}
    (a : LogTorus n → ℝ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (hF : MemLp (torusScalarRepresentative F) 2
      (angularWeightedTorusMeasure a)) :
    angularWeightedScalarL2 a :=
  hF.toLp (torusScalarRepresentative F)

private def angularBarPartialL2OfRepresentative {n : ℕ}
    (a : LogTorus n → ℝ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (angularWeightedTorusMeasure a)) :
    angularWeightedFormL2 a :=
  hD.toLp (torusFunctionBarPartialRepresentative F)

private def smoothAngularDolbeaultGraphSet {n : ℕ}
    (a : LogTorus n → ℝ) : Set (angularDolbeaultGraphAmbient a) :=
  {v | ∃ F : TorusCharacters.LogSpace n → ℂ,
    ContDiff ℝ 3 F ∧
    (∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q)) ∧
    HasCompactSupport (torusScalarRepresentative F) ∧
    ∃ hF : MemLp (torusScalarRepresentative F) 2
      (angularWeightedTorusMeasure a),
    ∃ hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (angularWeightedTorusMeasure a),
      v = WithLp.toLp 2
        (angularScalarL2OfRepresentative a F hF,
         angularBarPartialL2OfRepresentative a F hD)}

private def angularDolbeaultGraph {n : ℕ}
    (a : LogTorus n → ℝ) :
    Submodule ℂ (angularDolbeaultGraphAmbient a) :=
  (Submodule.span ℂ (smoothAngularDolbeaultGraphSet a)).topologicalClosure

private theorem angularDolbeaultGraph_isClosed {n : ℕ}
    (a : LogTorus n → ℝ) :
    IsClosed (angularDolbeaultGraph a :
      Set (angularDolbeaultGraphAmbient a)) :=
  Submodule.isClosed_topologicalClosure
    (Submodule.span ℂ (smoothAngularDolbeaultGraphSet a))

private instance angularDolbeaultGraph_completeSpace {n : ℕ}
    (a : LogTorus n → ℝ) :
    CompleteSpace (angularDolbeaultGraph a) :=
  (angularDolbeaultGraph_isClosed a).completeSpace_coe

private theorem smoothAngularDolbeaultGraph_mem {n : ℕ}
    (a : LogTorus n → ℝ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (hcont : ContDiff ℝ 3 F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hcompact : HasCompactSupport (torusScalarRepresentative F))
    (hF : MemLp (torusScalarRepresentative F) 2
      (angularWeightedTorusMeasure a))
    (hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (angularWeightedTorusMeasure a)) :
    WithLp.toLp 2
      (angularScalarL2OfRepresentative a F hF,
       angularBarPartialL2OfRepresentative a F hD) ∈
        angularDolbeaultGraph a := by
  apply (Submodule.span ℂ
    (smoothAngularDolbeaultGraphSet a)).le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨F, hcont, hperiod, hcompact, hF, hD, rfl⟩

private def angularWeakDolbeaultResolvent {n : ℕ}
    (a : LogTorus n → ℝ)
    (f : angularWeightedScalarL2 a) :
    angularDolbeaultGraph a :=
  (angularDolbeaultGraph a).orthogonalProjectionOnto
    (WithLp.toLp 2 (f, (0 : angularWeightedFormL2 a)))

private theorem angularWeakDolbeaultResolvent_moment {n : ℕ}
    (a : LogTorus n → ℝ)
    (f : angularWeightedScalarL2 a)
    (v : angularDolbeaultGraph a) :
    @inner ℂ (angularDolbeaultGraphAmbient a) _
      (WithLp.toLp 2 (f, (0 : angularWeightedFormL2 a)) -
        (angularWeakDolbeaultResolvent a f :
          angularDolbeaultGraphAmbient a))
      (v : angularDolbeaultGraphAmbient a) = 0 := by
  exact (angularDolbeaultGraph a).starProjection_inner_eq_zero
    (WithLp.toLp 2 (f, (0 : angularWeightedFormL2 a)))
    (v : angularDolbeaultGraphAmbient a) v.property

private theorem angularWeakDolbeaultResolvent_moment_components {n : ℕ}
    (a : LogTorus n → ℝ)
    (f : angularWeightedScalarL2 a)
    (v : angularDolbeaultGraph a) :
    @inner ℂ (angularWeightedScalarL2 a) _
      (WithLp.fst (angularWeakDolbeaultResolvent a f :
        angularDolbeaultGraphAmbient a))
      (WithLp.fst (v : angularDolbeaultGraphAmbient a)) +
    @inner ℂ (angularWeightedFormL2 a) _
      (WithLp.snd (angularWeakDolbeaultResolvent a f :
        angularDolbeaultGraphAmbient a))
      (WithLp.snd (v : angularDolbeaultGraphAmbient a)) =
    @inner ℂ (angularWeightedScalarL2 a) _ f
      (WithLp.fst (v : angularDolbeaultGraphAmbient a)) := by
  have h := angularWeakDolbeaultResolvent_moment a f v
  rw [inner_sub_left] at h
  simp only [WithLp.prod_inner_apply, inner_zero_left, add_zero] at h
  exact (sub_eq_zero.mp h).symm

private theorem angularWeakDolbeaultResolvent_form_adjoint {n : ℕ}
    (a : LogTorus n → ℝ)
    (f : angularWeightedScalarL2 a)
    (v : angularDolbeaultGraph a) :
    @inner ℂ (angularWeightedFormL2 a) _
      (WithLp.snd (angularWeakDolbeaultResolvent a f :
        angularDolbeaultGraphAmbient a))
      (WithLp.snd (v : angularDolbeaultGraphAmbient a)) =
    @inner ℂ (angularWeightedScalarL2 a) _
      (f - WithLp.fst (angularWeakDolbeaultResolvent a f :
        angularDolbeaultGraphAmbient a))
      (WithLp.fst (v : angularDolbeaultGraphAmbient a)) := by
  rw [inner_sub_left]
  have h := angularWeakDolbeaultResolvent_moment_components a f v
  linear_combination h

end WeightedTorusDolbeault

namespace WeightedTorusBochner

open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge MatrixTorusBochnerBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

private theorem zeroSourceCoverWeightedMeasure {n : ℕ} :
    coverWeightedMeasure
      (matrixSourceCoverPotential (fun _ : Space n => (0 : ℝ))) =
        (volume : Measure (TorusCharacters.LogSpace n)) := by
  simp only [coverWeightedMeasure, coverWeight, matrixSourceCoverPotential, neg_zero, Real.exp_zero,
    ENNReal.ofReal_one, withDensity_const, one_smul]

private theorem zeroSourceWeightedTorusMeasure {n : ℕ} :
    weightedTorusMeasure 1 (fun _ : Space n => (0 : ℝ)) =
      sourceTorusBaseMeasure n := by
  rw [weightedTorusMeasure_eq_withDensity 1 continuous_const]
  simp only [radialWeight, Nat.cast_one, mul_zero, Real.exp_zero, ENNReal.ofReal_one,
    withDensity_const, one_smul, sourceTorusBaseMeasure]

private def angularUnweightedTorusIntegrand {n : ℕ}
    (a : LogTorus n → ℝ) (f : LogTorus n → ℂ)
    (p : LogTorus n) : ℂ :=
  (angularWeightedTorusDensity a p : ℂ) * f p

private theorem continuous_angularUnweightedTorusIntegrand {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    {f : LogTorus n → ℂ} (hf : Continuous f) :
    Continuous (angularUnweightedTorusIntegrand a f) :=
  (Complex.continuous_ofReal.comp
    (continuous_angularWeightedTorusDensity ha)).mul hf

private theorem hasCompactSupport_angularUnweightedTorusIntegrand {n : ℕ}
    (a : LogTorus n → ℝ)
    {f : LogTorus n → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (angularUnweightedTorusIntegrand a f) :=
  hf.mul_left

private theorem integral_angularUnweightedTorusIntegrand_eq_weighted
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (f : LogTorus n → ℂ) :
    (∫ p : LogTorus n,
      angularUnweightedTorusIntegrand a f p
        ∂(sourceTorusBaseMeasure n)) =
      ∫ p : LogTorus n, f p ∂(angularWeightedTorusMeasure a) := by
  have hm : Measurable
      (fun p : LogTorus n =>
        ENNReal.ofReal (angularWeightedTorusDensity a p)) :=
    ENNReal.measurable_ofReal.comp
      (continuous_angularWeightedTorusDensity ha).measurable
  rw [angularWeightedTorusMeasure,
    integral_withDensity_eq_integral_toReal_smul hm
      (Filter.Eventually.of_forall fun p => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with p
  simp only [angularUnweightedTorusIntegrand, angularWeightedTorusDensity, Complex.ofReal_exp,
    Complex.ofReal_neg, ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul]

private theorem angular_partitioned_coverWeighted_integral_eq_torus
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    {f : LogTorus n → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    logarithmicCoverJacobianFactor n •
      (∫ z : TorusCharacters.LogSpace n,
        (coverAngularSmoothPartition z : ℂ) *
          f (complexTorusCoverProjection n z)
        ∂(coverWeightedMeasure (angularCoverPotential a))) =
      ∫ p : LogTorus n, f p ∂(angularWeightedTorusMeasure a) := by
  let g : LogTorus n → ℂ := angularUnweightedTorusIntegrand a f
  have hg : Continuous g :=
    continuous_angularUnweightedTorusIntegrand ha hf
  have hgc : HasCompactSupport g :=
    hasCompactSupport_angularUnweightedTorusIntegrand a hfc
  have hzero := partitioned_coverWeighted_integral_eq_torus
    (φ := fun _ : Space n => (0 : ℝ))
    continuous_const hg hgc
  rw [zeroSourceCoverWeightedMeasure,
    zeroSourceWeightedTorusMeasure] at hzero
  calc
    _ = logarithmicCoverJacobianFactor n •
        (∫ z : TorusCharacters.LogSpace n,
          (coverAngularSmoothPartition z : ℂ) *
            g (complexTorusCoverProjection n z)
          ∂(volume : Measure
            (TorusCharacters.LogSpace n))) := by
      apply congrArg
        (fun q : ℂ => logarithmicCoverJacobianFactor n • q)
      rw [integral_coverWeightedMeasure
        (continuous_angularCoverPotential ha)]
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [complexCoverWeight, coverWeight, angularCoverPotential, Complex.ofReal_exp,
        Complex.ofReal_neg, angularUnweightedTorusIntegrand, angularWeightedTorusDensity, g]
      ring
    _ = ∫ p : LogTorus n, g p
          ∂(sourceTorusBaseMeasure n) := hzero
    _ = _ := integral_angularUnweightedTorusIntegrand_eq_weighted
      ha f

private theorem angular_integral_holomorphic_coverAngularSmoothPartition_eq_zero
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    {f : LogTorus n → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (j : Fin n) :
    (∫ z : TorusCharacters.LogSpace n,
      holomorphicCoordinate
        (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
        f (complexTorusCoverProjection n z)
      ∂(coverWeightedMeasure (angularCoverPotential a))) = 0 := by
  let g : LogTorus n → ℂ := angularUnweightedTorusIntegrand a f
  have hg : Continuous g :=
    continuous_angularUnweightedTorusIntegrand ha hf
  have hgc : HasCompactSupport g :=
    hasCompactSupport_angularUnweightedTorusIntegrand a hfc
  have hz :=
    integral_holomorphicCoordinate_coverAngularSmoothPartition_mul_lift_eq_zero
      (φ := fun _ : Space n => (0 : ℝ))
      continuous_const hg hgc j
  rw [zeroSourceCoverWeightedMeasure] at hz
  rw [integral_coverWeightedMeasure
    (continuous_angularCoverPotential ha)]
  calc
    _ = ∫ z : TorusCharacters.LogSpace n,
      holomorphicCoordinate
        (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
        g (complexTorusCoverProjection n z)
      ∂(volume : Measure (TorusCharacters.LogSpace n)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [complexCoverWeight, coverWeight, angularCoverPotential, Complex.ofReal_exp,
        Complex.ofReal_neg, angularUnweightedTorusIntegrand, angularWeightedTorusDensity, g]
      ring
    _ = 0 := hz

private theorem angular_integral_barPartial_coverAngularSmoothPartition_eq_zero
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    {f : LogTorus n → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (j : Fin n) :
    (∫ z : TorusCharacters.LogSpace n,
      barPartialCoordinate
        (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
        f (complexTorusCoverProjection n z)
      ∂(coverWeightedMeasure (angularCoverPotential a))) = 0 := by
  let g : LogTorus n → ℂ := angularUnweightedTorusIntegrand a f
  have hg : Continuous g :=
    continuous_angularUnweightedTorusIntegrand ha hf
  have hgc : HasCompactSupport g :=
    hasCompactSupport_angularUnweightedTorusIntegrand a hfc
  have hz :=
    integral_barPartialCoordinate_coverAngularSmoothPartition_mul_lift_eq_zero
      (φ := fun _ : Space n => (0 : ℝ))
      continuous_const hg hgc j
  rw [zeroSourceCoverWeightedMeasure] at hz
  rw [integral_coverWeightedMeasure
    (continuous_angularCoverPotential ha)]
  calc
    _ = ∫ z : TorusCharacters.LogSpace n,
      barPartialCoordinate
        (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
        g (complexTorusCoverProjection n z)
      ∂(volume : Measure (TorusCharacters.LogSpace n)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [complexCoverWeight, coverWeight, angularCoverPotential, Complex.ofReal_exp,
        Complex.ofReal_neg, angularUnweightedTorusIntegrand, angularWeightedTorusDensity, g]
      ring
    _ = 0 := hz

private theorem complexAngularCoverPotential_periodic {n : ℕ}
    (a : LogTorus n → ℝ) (q : Fin n → ℤ) :
    Function.Periodic
      (fun z : TorusCharacters.LogSpace n =>
        (angularCoverPotential a z : ℂ))
      (TorusCharacters.imaginaryShift q) := by
  intro z
  change
    (angularCoverPotential a
      (z + TorusCharacters.imaginaryShift q) : ℂ) =
      (angularCoverPotential a z : ℂ)
  rw [angularCoverPotential_periodic a q z]

private theorem angularWeightedHolomorphicDerivative_periodic {n : ℕ}
    (a : LogTorus n → ℝ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (j : Fin n) (q : Fin n → ℤ) :
    Function.Periodic
      (weightedHolomorphicDerivative (angularCoverPotential a) F j)
      (TorusCharacters.imaginaryShift q) := by
  intro z
  have hFhol := holomorphicCoordinate_periodic F hperiod j q z
  have hahol := holomorphicCoordinate_periodic
    (fun w : TorusCharacters.LogSpace n =>
      (angularCoverPotential a w : ℂ))
    (complexAngularCoverPotential_periodic a) j q z
  change
    holomorphicCoordinate F
      (z + TorusCharacters.imaginaryShift q) j =
      holomorphicCoordinate F z j at hFhol
  change
    holomorphicCoordinate
      (fun w : TorusCharacters.LogSpace n =>
        (angularCoverPotential a w : ℂ))
      (z + TorusCharacters.imaginaryShift q) j =
      holomorphicCoordinate
        (fun w : TorusCharacters.LogSpace n =>
          (angularCoverPotential a w : ℂ)) z j at hahol
  unfold weightedHolomorphicDerivative
  rw [hFhol, hperiod q z, hahol]

private theorem angularComplexHessian_periodic {n : ℕ}
    (a : LogTorus n → ℝ) (i j : Fin n) (q : Fin n → ℤ) :
    Function.Periodic
      (fun z : TorusCharacters.LogSpace n =>
        complexHessian (angularCoverPotential a) z i j)
      (TorusCharacters.imaginaryShift q) := by
  unfold complexHessian
  exact barPartialCoordinate_periodic
    (fun z : TorusCharacters.LogSpace n =>
      holomorphicCoordinate
        (fun w => (angularCoverPotential a w : ℂ)) z i)
    (fun r => holomorphicCoordinate_periodic
      (fun w : TorusCharacters.LogSpace n =>
        (angularCoverPotential a w : ℂ))
      (complexAngularCoverPotential_periodic a) i r)
    j q

private def angularTorusWeightedHolomorphicDerivative {n : ℕ}
    (a : LogTorus n → ℝ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (j : Fin n) : LogTorus n → ℂ :=
  torusScalarRepresentative
    (weightedHolomorphicDerivative (angularCoverPotential a) F j)

private def angularTorusComplexHessian {n : ℕ}
    (a : LogTorus n → ℝ)
    (i j : Fin n) : LogTorus n → ℂ :=
  torusScalarRepresentative
    (fun z => complexHessian (angularCoverPotential a) z i j)

private theorem continuous_angularTorusWeightedHolomorphicDerivative {n : ℕ}
    {a : LogTorus n → ℝ}
    (ha : ContDiff ℝ 2 (angularCoverPotential a))
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 2 F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (j : Fin n) :
    Continuous (angularTorusWeightedHolomorphicDerivative a F j) := by
  unfold angularTorusWeightedHolomorphicDerivative
  exact continuous_torusScalarRepresentative_of_periodic
    (continuous_weightedHolomorphicDerivative
      (ha.of_le (by norm_num))
      (hF.of_le (by norm_num)) j)
    (fun q => angularWeightedHolomorphicDerivative_periodic
      a F hperiod j q)

private theorem continuous_angularTorusComplexHessian {n : ℕ}
    {a : LogTorus n → ℝ}
    (ha : ContDiff ℝ 2 (angularCoverPotential a))
    (i j : Fin n) :
    Continuous (angularTorusComplexHessian a i j) := by
  unfold angularTorusComplexHessian
  exact continuous_torusScalarRepresentative_of_periodic
    (continuous_complexHessian ha i j)
    (fun q => angularComplexHessian_periodic a i j q)

private theorem hasCompactSupport_angularTorusWeightedHolomorphicDerivative
    {n : ℕ} (a : LogTorus n → ℝ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hcompact : HasCompactSupport (torusScalarRepresentative F))
    (j : Fin n) :
    HasCompactSupport (angularTorusWeightedHolomorphicDerivative a F j) := by
  have hh := hasCompactSupport_sourceTorusHolomorphicDerivative
    F hperiod hcompact j
  have hp := hcompact.mul_right
    (f' := sourceTorusHolomorphicDerivative
      (fun z : TorusCharacters.LogSpace n =>
        (angularCoverPotential a z : ℂ)) j)
  have hs := hh.sub hp
  change HasCompactSupport
    (fun q : LogTorus n =>
      sourceTorusHolomorphicDerivative F j q -
        torusScalarRepresentative F q *
          sourceTorusHolomorphicDerivative
            (fun z : TorusCharacters.LogSpace n =>
              (angularCoverPotential a z : ℂ)) j q) at hs
  have hfunction :
      (fun q : LogTorus n =>
        sourceTorusHolomorphicDerivative F j q -
          torusScalarRepresentative F q *
            sourceTorusHolomorphicDerivative
              (fun z : TorusCharacters.LogSpace n =>
                (angularCoverPotential a z : ℂ)) j q) =
        angularTorusWeightedHolomorphicDerivative a F j := by
    funext q
    rfl
  rw [hfunction] at hs
  exact hs

private theorem integrable_angularSourceAngularDerivativeLift {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    {f : LogTorus n → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f)
    (v : TorusCharacters.LogSpace n) :
    Integrable (sourceAngularDerivativeLift f v)
      (coverWeightedMeasure (angularCoverPotential a)) := by
  exact integrable_of_continuous_compact_cover
    (continuous_angularCoverPotential ha)
    (continuous_sourceAngularDerivativeLift hf v)
    (hasCompactSupport_sourceAngularDerivativeLift hfc v)

private theorem integrable_angularHolomorphicPartitionDerivativeLift {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    {f : LogTorus n → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (j : Fin n) :
    Integrable
      (fun z : TorusCharacters.LogSpace n =>
        holomorphicCoordinate
          (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
            f (complexTorusCoverProjection n z))
      (coverWeightedMeasure (angularCoverPotential a)) := by
  let μ : Measure (TorusCharacters.LogSpace n) :=
    coverWeightedMeasure (angularCoverPotential a)
  let v₀ : TorusCharacters.LogSpace n :=
    Pi.single j (1 : ℂ)
  let v₁ : TorusCharacters.LogSpace n :=
    Pi.single j Complex.I
  let d₀ := sourceAngularDerivativeLift f v₀
  let d₁ := sourceAngularDerivativeLift f v₁
  have hi₀ : Integrable d₀ μ :=
    integrable_angularSourceAngularDerivativeLift ha hf hfc v₀
  have hi₁ : Integrable d₁ μ :=
    integrable_angularSourceAngularDerivativeLift ha hf hfc v₁
  have hcomb : Integrable
      (fun z : TorusCharacters.LogSpace n =>
        (d₀ z - Complex.I * d₁ z) / 2) μ :=
    (hi₀.sub (hi₁.const_mul Complex.I)).div_const 2
  have hη : Differentiable ℝ
      (coverAngularSmoothPartition (n := n)) :=
    (contDiff_coverAngularSmoothPartition
      (n := n) (m := 1)).differentiable (by simp only [WithTop.coe_one, ne_eq, one_ne_zero,
        not_false_eq_true])
  apply hcomb.congr
  filter_upwards [] with z
  unfold holomorphicCoordinate
  rw [DolbeaultGraphDistributionBridge.fderiv_complexOfReal
    hη z v₀,
    DolbeaultGraphDistributionBridge.fderiv_complexOfReal
      hη z v₁]
  dsimp [d₀, d₁, sourceAngularDerivativeLift]
  ring

private theorem integrable_angularBarPartialPartitionDerivativeLift {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    {f : LogTorus n → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (j : Fin n) :
    Integrable
      (fun z : TorusCharacters.LogSpace n =>
        barPartialCoordinate
          (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
            f (complexTorusCoverProjection n z))
      (coverWeightedMeasure (angularCoverPotential a)) := by
  let μ : Measure (TorusCharacters.LogSpace n) :=
    coverWeightedMeasure (angularCoverPotential a)
  let v₀ : TorusCharacters.LogSpace n :=
    Pi.single j (1 : ℂ)
  let v₁ : TorusCharacters.LogSpace n :=
    Pi.single j Complex.I
  let d₀ := sourceAngularDerivativeLift f v₀
  let d₁ := sourceAngularDerivativeLift f v₁
  have hi₀ : Integrable d₀ μ :=
    integrable_angularSourceAngularDerivativeLift ha hf hfc v₀
  have hi₁ : Integrable d₁ μ :=
    integrable_angularSourceAngularDerivativeLift ha hf hfc v₁
  have hcomb : Integrable
      (fun z : TorusCharacters.LogSpace n =>
        (d₀ z + Complex.I * d₁ z) / 2) μ :=
    (hi₀.add (hi₁.const_mul Complex.I)).div_const 2
  have hη : Differentiable ℝ
      (coverAngularSmoothPartition (n := n)) :=
    (contDiff_coverAngularSmoothPartition
      (n := n) (m := 1)).differentiable (by simp only [WithTop.coe_one, ne_eq, one_ne_zero,
        not_false_eq_true])
  apply hcomb.congr
  filter_upwards [] with z
  unfold barPartialCoordinate
  rw [DolbeaultGraphDistributionBridge.fderiv_complexOfReal
    hη z v₀,
    DolbeaultGraphDistributionBridge.fderiv_complexOfReal
      hη z v₁]
  dsimp [d₀, d₁, sourceAngularDerivativeLift]
  ring

private theorem angularTorus_weighted_complex_bochner_left_cutoff_point
    {n : ℕ} {a : LogTorus n → ℝ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (hFp : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hGp : ∀ q : Fin n → ℤ,
      Function.Periodic G (TorusCharacters.imaginaryShift q))
    (hηreal : Differentiable ℝ
      (coverAngularSmoothPartition (n := n)))
    (hηcomplex : Differentiable ℝ
      (fun z : TorusCharacters.LogSpace n =>
        (coverAngularSmoothPartition z : ℂ)))
    (hGdiff : Differentiable ℝ G)
    (i j : Fin n) (z : TorusCharacters.LogSpace n) :
    weightedHolomorphicDerivative (angularCoverPotential a) F i z *
        conj (weightedHolomorphicDerivative (angularCoverPotential a)
          (fun w => (coverAngularSmoothPartition w : ℂ) * G w) j z) =
      sourceAngularCutoffLift
          (fun p => angularTorusWeightedHolomorphicDerivative a F i p *
            conj (angularTorusWeightedHolomorphicDerivative a G j p)) z +
        barPartialCoordinate
            (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
          (angularTorusWeightedHolomorphicDerivative a F i
              (complexTorusCoverProjection n z) *
            conj (torusScalarRepresentative G
              (complexTorusCoverProjection n z))) := by
  have hp := weightedHolomorphicDerivative_mul
    (angularCoverPotential a) hηcomplex hGdiff z j
  rw [hp, map_add, map_mul, map_mul,
    Complex.conj_ofReal,
    conj_holomorphicCoordinate_real hηreal z j]
  dsimp [sourceAngularCutoffLift]
  have hHFpoint :
      angularTorusWeightedHolomorphicDerivative a F i
          (complexTorusCoverProjection n z) =
        weightedHolomorphicDerivative (angularCoverPotential a) F i z :=
    congrFun
      (complexTorusCoverLift_torusScalarRepresentative_eq
        (weightedHolomorphicDerivative (angularCoverPotential a) F i)
        (fun q => angularWeightedHolomorphicDerivative_periodic
          a F hFp i q)) z
  have hHGpoint :
      angularTorusWeightedHolomorphicDerivative a G j
          (complexTorusCoverProjection n z) =
        weightedHolomorphicDerivative (angularCoverPotential a) G j z :=
    congrFun
      (complexTorusCoverLift_torusScalarRepresentative_eq
        (weightedHolomorphicDerivative (angularCoverPotential a) G j)
        (fun q => angularWeightedHolomorphicDerivative_periodic
          a G hGp j q)) z
  have hGpoint :
      torusScalarRepresentative G (complexTorusCoverProjection n z) = G z :=
    congrFun (complexTorusCoverLift_torusScalarRepresentative_eq G hGp) z
  rw [hHFpoint, hHGpoint, hGpoint]
  ring

private theorem angularTorus_weighted_complex_bochner_right_cutoff_point
    {n : ℕ} {a : LogTorus n → ℝ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (hFp : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hGp : ∀ q : Fin n → ℤ,
      Function.Periodic G (TorusCharacters.imaginaryShift q))
    (hηreal : Differentiable ℝ
      (coverAngularSmoothPartition (n := n)))
    (hηcomplex : Differentiable ℝ
      (fun z : TorusCharacters.LogSpace n =>
        (coverAngularSmoothPartition z : ℂ)))
    (hGdiff : Differentiable ℝ G)
    (i j : Fin n) (z : TorusCharacters.LogSpace n) :
    barPartialCoordinate F z j *
          conj (barPartialCoordinate
            (fun w => (coverAngularSmoothPartition w : ℂ) * G w) z i) +
        (F z * complexHessian (angularCoverPotential a) z i j) *
          conj ((coverAngularSmoothPartition z : ℂ) * G z) =
      sourceAngularCutoffLift
          (fun p =>
            sourceTorusBarPartial F j p *
                conj (sourceTorusBarPartial G i p) +
              (torusScalarRepresentative F p *
                angularTorusComplexHessian a i j p) *
                conj (torusScalarRepresentative G p)) z +
        holomorphicCoordinate
            (fun w => (coverAngularSmoothPartition w : ℂ)) z i *
          (sourceTorusBarPartial F j (complexTorusCoverProjection n z) *
            conj (torusScalarRepresentative G
              (complexTorusCoverProjection n z))) := by
  have hp := barPartialCoordinate_mul hηcomplex hGdiff z i
  rw [hp]
  change
    barPartialCoordinate F z j *
        conj ((coverAngularSmoothPartition z : ℂ) *
          barPartialCoordinate G z i + G z *
            barPartialCoordinate
              (fun w => (coverAngularSmoothPartition w : ℂ)) z i) +
      (F z * complexHessian (angularCoverPotential a) z i j) *
        conj ((coverAngularSmoothPartition z : ℂ) * G z) = _
  rw [map_add, map_mul, map_mul, map_mul,
    Complex.conj_ofReal,
    conj_barPartialCoordinate_real hηreal z i]
  dsimp [sourceAngularCutoffLift]
  have hBFpoint :
      sourceTorusBarPartial F j (complexTorusCoverProjection n z) =
        barPartialCoordinate F z j :=
    congrFun
      (complexTorusCoverLift_torusScalarRepresentative_eq
        (fun w => barPartialCoordinate F w j)
        (fun q => barPartialCoordinate_periodic F hFp j q)) z
  have hBGpoint :
      sourceTorusBarPartial G i (complexTorusCoverProjection n z) =
        barPartialCoordinate G z i :=
    congrFun
      (complexTorusCoverLift_torusScalarRepresentative_eq
        (fun w => barPartialCoordinate G w i)
        (fun q => barPartialCoordinate_periodic G hGp i q)) z
  have hFpoint :
      torusScalarRepresentative F (complexTorusCoverProjection n z) = F z :=
    congrFun (complexTorusCoverLift_torusScalarRepresentative_eq F hFp) z
  have hHpoint :
      angularTorusComplexHessian a i j
          (complexTorusCoverProjection n z) =
        complexHessian (angularCoverPotential a) z i j :=
    congrFun
      (complexTorusCoverLift_torusScalarRepresentative_eq
        (fun w => complexHessian (angularCoverPotential a) w i j)
        (fun q => angularComplexHessian_periodic a i j q)) z
  have hGpoint :
      torusScalarRepresentative G (complexTorusCoverProjection n z) = G z :=
    congrFun (complexTorusCoverLift_torusScalarRepresentative_eq G hGp) z
  rw [hBFpoint, hBGpoint, hFpoint, hHpoint, hGpoint]
  ring

private theorem angularTorus_weighted_complex_bochner_finish
    {n : ℕ} {a : LogTorus n → ℝ}
    {F Gcut : TorusCharacters.LogSpace n → ℂ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hF : ContDiff ℝ 2 F) (hGcut : ContDiff ℝ 2 Gcut)
    (hGcutcompact : HasCompactSupport Gcut)
    (i j : Fin n)
    (L B C CL CR : LogTorus n → ℂ)
    (hLc : Continuous L) (hLcompact : HasCompactSupport L)
    (hBc : Continuous B) (hBcompact : HasCompactSupport B)
    (hCc : Continuous C) (hCcompact : HasCompactSupport C)
    (hCLc : Continuous CL) (hCLcompact : HasCompactSupport CL)
    (hCRc : Continuous CR) (hCRcompact : HasCompactSupport CR)
    (hleftpoint : ∀ z : TorusCharacters.LogSpace n,
      weightedHolomorphicDerivative (angularCoverPotential a) F i z *
          conj (weightedHolomorphicDerivative
            (angularCoverPotential a) Gcut j z) =
        sourceAngularCutoffLift L z +
          barPartialCoordinate
              (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
            CL (complexTorusCoverProjection n z))
    (hrightpoint : ∀ z : TorusCharacters.LogSpace n,
      (barPartialCoordinate F z j *
          conj (barPartialCoordinate Gcut z i) +
        (F z * complexHessian (angularCoverPotential a) z i j) *
          conj (Gcut z)) =
        sourceAngularCutoffLift (fun p => B p + C p) z +
          holomorphicCoordinate
              (fun w => (coverAngularSmoothPartition w : ℂ)) z i *
            CR (complexTorusCoverProjection n z)) :
    (∫ p : LogTorus n, L p ∂(angularWeightedTorusMeasure a)) =
      ∫ p : LogTorus n, (B p + C p)
        ∂(angularWeightedTorusMeasure a) := by
  let E := TorusCharacters.LogSpace n
  let A : E → ℝ := angularCoverPotential a
  let μ : Measure E := coverWeightedMeasure A
  have hηL : Integrable (sourceAngularCutoffLift L) μ := by
    exact integrable_of_continuous_compact_cover
      (continuous_angularCoverPotential ha)
      (continuous_sourceAngularCutoffLift hLc)
      (hasCompactSupport_sourceAngularCutoffLift hLcompact)
  have hηR : Integrable
      (sourceAngularCutoffLift (fun p => B p + C p)) μ := by
    exact integrable_of_continuous_compact_cover
      (continuous_angularCoverPotential ha)
      (continuous_sourceAngularCutoffLift (hBc.add hCc))
      (hasCompactSupport_sourceAngularCutoffLift
        (hBcompact.add hCcompact))
  have hcrossL : Integrable
      (fun z : E =>
        barPartialCoordinate
          (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
            CL (complexTorusCoverProjection n z)) μ := by
    exact integrable_angularBarPartialPartitionDerivativeLift
      ha hCLc hCLcompact j
  have hcrossR : Integrable
      (fun z : E =>
        holomorphicCoordinate
          (fun w => (coverAngularSmoothPartition w : ℂ)) z i *
            CR (complexTorusCoverProjection n z)) μ := by
    exact integrable_angularHolomorphicPartitionDerivativeLift
      ha hCRc hCRcompact i
  have hzeroL :
      (∫ z : E,
        barPartialCoordinate
          (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
            CL (complexTorusCoverProjection n z) ∂μ) = 0 :=
    angular_integral_barPartial_coverAngularSmoothPartition_eq_zero
      ha hCLc hCLcompact j
  have hzeroR :
      (∫ z : E,
        holomorphicCoordinate
          (fun w => (coverAngularSmoothPartition w : ℂ)) z i *
            CR (complexTorusCoverProjection n z) ∂μ) = 0 :=
    angular_integral_holomorphic_coverAngularSmoothPartition_eq_zero
      ha hCRc hCRcompact i
  have hboch :=
    weighted_complex_bochner_coordinate_identity_compact_right
      ha2 hF hGcut hGcutcompact i j
  have hleft :
      (∫ z : E,
        weightedHolomorphicDerivative A F i z *
          conj (weightedHolomorphicDerivative A Gcut j z) ∂μ) =
      ∫ z : E, sourceAngularCutoffLift L z ∂μ := by
    calc
      _ = ∫ z : E,
        (sourceAngularCutoffLift L z +
          barPartialCoordinate
            (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
              CL (complexTorusCoverProjection n z)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with z
        exact hleftpoint z
      _ = (∫ z : E, sourceAngularCutoffLift L z ∂μ) +
          (∫ z : E,
            barPartialCoordinate
              (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
                CL (complexTorusCoverProjection n z) ∂μ) :=
        MeasureTheory.integral_add hηL hcrossL
      _ = _ := by rw [hzeroL, add_zero]
  have hright :
      (∫ z : E,
        (barPartialCoordinate F z j *
          conj (barPartialCoordinate Gcut z i) +
         (F z * complexHessian A z i j) * conj (Gcut z)) ∂μ) =
      ∫ z : E,
        sourceAngularCutoffLift (fun p => B p + C p) z ∂μ := by
    calc
      _ = ∫ z : E,
        (sourceAngularCutoffLift (fun p => B p + C p) z +
          holomorphicCoordinate
            (fun w => (coverAngularSmoothPartition w : ℂ)) z i *
              CR (complexTorusCoverProjection n z)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with z
        exact hrightpoint z
      _ = (∫ z : E,
          sourceAngularCutoffLift (fun p => B p + C p) z ∂μ) +
        (∫ z : E,
          holomorphicCoordinate
            (fun w => (coverAngularSmoothPartition w : ℂ)) z i *
              CR (complexTorusCoverProjection n z) ∂μ) :=
        MeasureTheory.integral_add hηR hcrossR
      _ = _ := by rw [hzeroR, add_zero]
  have hcover :
      (∫ z : E, sourceAngularCutoffLift L z ∂μ) =
      ∫ z : E,
        sourceAngularCutoffLift (fun p => B p + C p) z ∂μ :=
    hleft.symm.trans (hboch.trans hright)
  have hdescL := angular_partitioned_coverWeighted_integral_eq_torus
    ha hLc hLcompact
  have hdescR := angular_partitioned_coverWeighted_integral_eq_torus
    ha (hBc.add hCc) (hBcompact.add hCcompact)
  calc
    _ = logarithmicCoverJacobianFactor n •
      (∫ z : E, sourceAngularCutoffLift L z ∂μ) := hdescL.symm
    _ = logarithmicCoverJacobianFactor n •
      (∫ z : E,
        sourceAngularCutoffLift (fun p => B p + C p) z ∂μ) :=
      congrArg (fun q : ℂ => logarithmicCoverJacobianFactor n • q)
        hcover
    _ = _ := hdescR

private theorem angularTorus_weighted_complex_bochner_coordinate_identity
    {n : ℕ} {a : LogTorus n → ℝ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hF : ContDiff ℝ 2 F)
    (hG : ContDiff ℝ 2 G)
    (hFp : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q))
    (hGp : ∀ q : Fin n → ℤ,
      Function.Periodic G
        (TorusCharacters.imaginaryShift q))
    (hGc : HasCompactSupport (torusScalarRepresentative G))
    (i j : Fin n) :
    (∫ p : LogTorus n,
      angularTorusWeightedHolomorphicDerivative a F i p *
        conj (angularTorusWeightedHolomorphicDerivative a G j p)
      ∂(angularWeightedTorusMeasure a)) =
    ∫ p : LogTorus n,
      (sourceTorusBarPartial F j p *
        conj (sourceTorusBarPartial G i p) +
       (torusScalarRepresentative F p *
          angularTorusComplexHessian a i j p) *
            conj (torusScalarRepresentative G p))
      ∂(angularWeightedTorusMeasure a) := by
  let E := TorusCharacters.LogSpace n
  let T := LogTorus n
  let A : E → ℝ := angularCoverPotential a
  let g : T → ℂ := torusScalarRepresentative G
  let Gcut : E → ℂ := fun z =>
    (coverAngularSmoothPartition z : ℂ) * G z
  let L : T → ℂ := fun p =>
    angularTorusWeightedHolomorphicDerivative a F i p *
      conj (angularTorusWeightedHolomorphicDerivative a G j p)
  let B : T → ℂ := fun p =>
    sourceTorusBarPartial F j p *
      conj (sourceTorusBarPartial G i p)
  let C : T → ℂ := fun p =>
    (torusScalarRepresentative F p *
      angularTorusComplexHessian a i j p) * conj (g p)
  let CL : T → ℂ := fun p =>
    angularTorusWeightedHolomorphicDerivative a F i p * conj (g p)
  let CR : T → ℂ := fun p =>
    sourceTorusBarPartial F j p * conj (g p)
  have hgcont : Continuous g :=
    continuous_torusScalarRepresentative_of_periodic hG.continuous hGp
  have hFcont : Continuous (torusScalarRepresentative F) :=
    continuous_torusScalarRepresentative_of_periodic hF.continuous hFp
  have hgc : HasCompactSupport g := hGc
  have hgconj : HasCompactSupport (fun p : T => conj (g p)) :=
    hasCompactSupport_sourceTorusConj hgc
  have hLc : Continuous L :=
    (continuous_angularTorusWeightedHolomorphicDerivative
      ha2 hF hFp i).mul
      (Complex.continuous_conj.comp
        (continuous_angularTorusWeightedHolomorphicDerivative
          ha2 hG hGp j))
  have hLcompact : HasCompactSupport L := by
    dsimp [L]
    exact (hasCompactSupport_sourceTorusConj
      (hasCompactSupport_angularTorusWeightedHolomorphicDerivative
        a G hGp hGc j)).mul_left
  have hBc : Continuous B :=
    (continuous_sourceTorusBarPartial hF hFp j).mul
      (Complex.continuous_conj.comp
        (continuous_sourceTorusBarPartial hG hGp i))
  have hBcompact : HasCompactSupport B := by
    dsimp [B]
    exact (hasCompactSupport_sourceTorusConj
      (hasCompactSupport_sourceTorusBarPartial
        G hGp hGc i)).mul_left
  have hCc : Continuous C :=
    (hFcont.mul
      (continuous_angularTorusComplexHessian ha2 i j)).mul
      (Complex.continuous_conj.comp hgcont)
  have hCcompact : HasCompactSupport C := by
    dsimp [C]
    exact hgconj.mul_left
  have hCLc : Continuous CL :=
    (continuous_angularTorusWeightedHolomorphicDerivative
      ha2 hF hFp i).mul (Complex.continuous_conj.comp hgcont)
  have hCLcompact : HasCompactSupport CL := by
    dsimp [CL]
    exact hgconj.mul_left
  have hCRc : Continuous CR :=
    (continuous_sourceTorusBarPartial hF hFp j).mul
      (Complex.continuous_conj.comp hgcont)
  have hCRcompact : HasCompactSupport CR := by
    dsimp [CR]
    exact hgconj.mul_left
  have hgrec : complexTorusCoverLift g = G :=
    complexTorusCoverLift_torusScalarRepresentative_eq G hGp
  have hGpoint (z : E) :
      g (complexTorusCoverProjection n z) = G z := by
    exact congrFun hgrec z
  have hcut : sourceAngularCutoffLift g = Gcut := by
    funext z
    change
      (coverAngularSmoothPartition z : ℂ) *
        g (complexTorusCoverProjection n z) =
      (coverAngularSmoothPartition z : ℂ) * G z
    rw [hGpoint z]
  have hGcut : ContDiff ℝ 2 Gcut := by
    rw [← hcut]
    apply contDiff_sourceAngularCutoffLift
    rw [hgrec]
    exact hG
  have hGcutcompact : HasCompactSupport Gcut := by
    rw [← hcut]
    exact hasCompactSupport_sourceAngularCutoffLift hgc
  have hηreal : Differentiable ℝ
      (coverAngularSmoothPartition (n := n)) :=
    (contDiff_coverAngularSmoothPartition
      (n := n) (m := 1)).differentiable (by simp only [WithTop.coe_one, ne_eq, one_ne_zero,
        not_false_eq_true])
  have hηcomplex : Differentiable ℝ
      (fun z : E => (coverAngularSmoothPartition z : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp
      (contDiff_coverAngularSmoothPartition
        (n := n) (m := 1))).differentiable (by simp only [WithTop.coe_one, ne_eq, one_ne_zero,
          not_false_eq_true])
  have hGdiff : Differentiable ℝ G :=
    hG.differentiable (by norm_num)
  have hleftpoint (z : E) :
      weightedHolomorphicDerivative A F i z *
        conj (weightedHolomorphicDerivative A Gcut j z) =
        sourceAngularCutoffLift L z +
          barPartialCoordinate
            (fun w => (coverAngularSmoothPartition w : ℂ)) z j *
              CL (complexTorusCoverProjection n z) := by
    simpa only [A, Gcut, L, CL, g] using
      angularTorus_weighted_complex_bochner_left_cutoff_point
        (a := a) hFp hGp hηreal hηcomplex hGdiff i j z
  have hrightpoint (z : E) :
      (barPartialCoordinate F z j *
        conj (barPartialCoordinate Gcut z i) +
       (F z * complexHessian A z i j) * conj (Gcut z)) =
      sourceAngularCutoffLift (fun p => B p + C p) z +
        holomorphicCoordinate
          (fun w => (coverAngularSmoothPartition w : ℂ)) z i *
            CR (complexTorusCoverProjection n z) := by
    simpa only [A, Gcut, B, C, CR, g] using
      angularTorus_weighted_complex_bochner_right_cutoff_point
        (a := a) hFp hGp hηreal hηcomplex hGdiff i j z
  change
    (∫ p : T, L p ∂(angularWeightedTorusMeasure a)) =
      ∫ p : T, (B p + C p) ∂(angularWeightedTorusMeasure a)
  exact angularTorus_weighted_complex_bochner_finish
    ha ha2 hF hGcut hGcutcompact i j L B C CL CR
    hLc hLcompact hBc hBcompact hCc hCcompact
    hCLc hCLcompact hCRc hCRcompact hleftpoint hrightpoint

private def angularTorusFormAdjoint {n : ℕ}
    (a : LogTorus n → ℝ)
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (p : LogTorus n) : ℂ :=
  ∑ i : Fin n,
    angularTorusWeightedHolomorphicDerivative a
      (fun z => W z i) i p

private def angularTorusFormCurvatureDensity {n : ℕ}
    (a : LogTorus n → ℝ)
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (p : LogTorus n) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n,
    (torusScalarRepresentative (fun z => W z i) p *
      angularTorusComplexHessian a i j p) *
        conj (torusScalarRepresentative (fun z => W z j) p)

private theorem integrable_angularTorusWeightedHolomorphic_pair
    {n : ℕ} {a : LogTorus n → ℝ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hF : ContDiff ℝ 2 F)
    (hG : ContDiff ℝ 2 G)
    (hFp : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hGp : ∀ q : Fin n → ℤ,
      Function.Periodic G (TorusCharacters.imaginaryShift q))
    (hGc : HasCompactSupport (torusScalarRepresentative G))
    (i j : Fin n) :
    Integrable
      (fun p : LogTorus n =>
        angularTorusWeightedHolomorphicDerivative a F i p *
          conj (angularTorusWeightedHolomorphicDerivative a G j p))
      (angularWeightedTorusMeasure a) := by
  let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  have : IsFiniteMeasureOnCompacts (angularWeightedTorusMeasure a) :=
    isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  apply ((continuous_angularTorusWeightedHolomorphicDerivative
    ha2 hF hFp i).mul
      (Complex.continuous_conj.comp
        (continuous_angularTorusWeightedHolomorphicDerivative
          ha2 hG hGp j))).integrable_of_hasCompactSupport
  exact (hasCompactSupport_sourceTorusConj
    (hasCompactSupport_angularTorusWeightedHolomorphicDerivative
      a G hGp hGc j)).mul_left

private theorem integrable_angularTorusBarPartial_pair
    {n : ℕ} {a : LogTorus n → ℝ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (ha : Continuous a)
    (hF : ContDiff ℝ 2 F)
    (hG : ContDiff ℝ 2 G)
    (hFp : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hGp : ∀ q : Fin n → ℤ,
      Function.Periodic G (TorusCharacters.imaginaryShift q))
    (hGc : HasCompactSupport (torusScalarRepresentative G))
    (i j : Fin n) :
    Integrable
      (fun p : LogTorus n =>
        sourceTorusBarPartial F i p *
          conj (sourceTorusBarPartial G j p))
      (angularWeightedTorusMeasure a) := by
  let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  have : IsFiniteMeasureOnCompacts (angularWeightedTorusMeasure a) :=
    isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  apply ((continuous_sourceTorusBarPartial hF hFp i).mul
    (Complex.continuous_conj.comp
      (continuous_sourceTorusBarPartial hG hGp j))).integrable_of_hasCompactSupport
  exact (hasCompactSupport_sourceTorusConj
    (hasCompactSupport_sourceTorusBarPartial G hGp hGc j)).mul_left

private theorem integrable_angularTorusComplexHessian_pair
    {n : ℕ} {a : LogTorus n → ℝ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hF : ContDiff ℝ 2 F)
    (hG : ContDiff ℝ 2 G)
    (hFp : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hGp : ∀ q : Fin n → ℤ,
      Function.Periodic G (TorusCharacters.imaginaryShift q))
    (hGc : HasCompactSupport (torusScalarRepresentative G))
    (i j : Fin n) :
    Integrable
      (fun p : LogTorus n =>
        (torusScalarRepresentative F p *
          angularTorusComplexHessian a i j p) *
            conj (torusScalarRepresentative G p))
      (angularWeightedTorusMeasure a) := by
  let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  have : IsFiniteMeasureOnCompacts (angularWeightedTorusMeasure a) :=
    isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  have hFc := continuous_torusScalarRepresentative_of_periodic
    hF.continuous hFp
  have hGc' := continuous_torusScalarRepresentative_of_periodic
    hG.continuous hGp
  apply ((hFc.mul (continuous_angularTorusComplexHessian ha2 i j)).mul
    (Complex.continuous_conj.comp hGc')).integrable_of_hasCompactSupport
  exact (hasCompactSupport_sourceTorusConj hGc).mul_left

private theorem angularTorus_weighted_complex_bochner_form_coordinate_sum
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hW : ∀ i : Fin n, ContDiff ℝ 2 (fun z => W z i))
    (hWp : ∀ (i : Fin n) (q : Fin n → ℤ),
      Function.Periodic (fun z => W z i)
        (TorusCharacters.imaginaryShift q))
    (hWc : ∀ i : Fin n,
      HasCompactSupport (torusScalarRepresentative (fun z => W z i))) :
    (∑ i : Fin n, ∑ j : Fin n,
      ∫ p : LogTorus n,
        angularTorusWeightedHolomorphicDerivative a
          (fun z => W z i) i p *
          conj (angularTorusWeightedHolomorphicDerivative a
            (fun z => W z j) j p)
        ∂(angularWeightedTorusMeasure a)) =
    ∑ i : Fin n, ∑ j : Fin n,
      ∫ p : LogTorus n,
        (sourceTorusBarPartial (fun z => W z i) j p *
          conj (sourceTorusBarPartial (fun z => W z j) i p) +
          (torusScalarRepresentative (fun z => W z i) p *
            angularTorusComplexHessian a i j p) *
              conj (torusScalarRepresentative (fun z => W z j) p))
        ∂(angularWeightedTorusMeasure a) := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact angularTorus_weighted_complex_bochner_coordinate_identity
    ha ha2 (hW i) (hW j) (hWp i) (hWp j) (hWc j) i j

private theorem integral_angularTorusFormAdjoint_mul_conj_eq_coordinate_sum
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hW : ∀ i : Fin n, ContDiff ℝ 2 (fun z => W z i))
    (hWp : ∀ (i : Fin n) (q : Fin n → ℤ),
      Function.Periodic (fun z => W z i)
        (TorusCharacters.imaginaryShift q))
    (hWc : ∀ i : Fin n,
      HasCompactSupport (torusScalarRepresentative (fun z => W z i))) :
    (∫ p : LogTorus n,
      angularTorusFormAdjoint a W p *
        conj (angularTorusFormAdjoint a W p)
      ∂(angularWeightedTorusMeasure a)) =
    ∑ i : Fin n, ∑ j : Fin n,
      ∫ p : LogTorus n,
        angularTorusWeightedHolomorphicDerivative a
          (fun z => W z i) i p *
          conj (angularTorusWeightedHolomorphicDerivative a
            (fun z => W z j) j p)
        ∂(angularWeightedTorusMeasure a) := by
  let T := LogTorus n
  let μ : Measure T := angularWeightedTorusMeasure a
  have hp (i j : Fin n) : Integrable
      (fun p : T =>
        angularTorusWeightedHolomorphicDerivative a
          (fun z => W z i) i p *
          conj (angularTorusWeightedHolomorphicDerivative a
            (fun z => W z j) j p)) μ :=
    integrable_angularTorusWeightedHolomorphic_pair
      ha ha2 (hW i) (hW j) (hWp i) (hWp j) (hWc j) i j
  change
    (∫ p : T,
      angularTorusFormAdjoint a W p *
        conj (angularTorusFormAdjoint a W p) ∂μ) =
    ∑ i : Fin n, ∑ j : Fin n,
      ∫ p : T,
        angularTorusWeightedHolomorphicDerivative a
          (fun z => W z i) i p *
          conj (angularTorusWeightedHolomorphicDerivative a
            (fun z => W z j) j p) ∂μ
  calc
    _ = ∫ p : T, ∑ i : Fin n, ∑ j : Fin n,
      angularTorusWeightedHolomorphicDerivative a
        (fun z => W z i) i p *
        conj (angularTorusWeightedHolomorphicDerivative a
          (fun z => W z j) j p) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with p
      simp only [angularTorusFormAdjoint, map_sum,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ i : Fin n,
      ∫ p : T, ∑ j : Fin n,
        angularTorusWeightedHolomorphicDerivative a
          (fun z => W z i) i p *
          conj (angularTorusWeightedHolomorphicDerivative a
            (fun z => W z j) j p) ∂μ := by
      exact MeasureTheory.integral_finsetSum Finset.univ
        (fun i _ => MeasureTheory.integrable_finsetSum Finset.univ
          (fun j _ => hp i j))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact MeasureTheory.integral_finsetSum Finset.univ
        (fun j _ => hp i j)

private theorem integral_angularTorusFormMixed_add_curvature_eq_coordinate_sum
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hW : ∀ i : Fin n, ContDiff ℝ 2 (fun z => W z i))
    (hWp : ∀ (i : Fin n) (q : Fin n → ℤ),
      Function.Periodic (fun z => W z i)
        (TorusCharacters.imaginaryShift q))
    (hWc : ∀ i : Fin n,
      HasCompactSupport (torusScalarRepresentative (fun z => W z i))) :
    (∫ p : LogTorus n,
      sourceTorusFormMixedDerivativeDensity W p +
        angularTorusFormCurvatureDensity a W p
      ∂(angularWeightedTorusMeasure a)) =
    ∑ i : Fin n, ∑ j : Fin n,
      ∫ p : LogTorus n,
        (sourceTorusBarPartial (fun z => W z i) j p *
          conj (sourceTorusBarPartial (fun z => W z j) i p) +
          (torusScalarRepresentative (fun z => W z i) p *
            angularTorusComplexHessian a i j p) *
              conj (torusScalarRepresentative (fun z => W z j) p))
        ∂(angularWeightedTorusMeasure a) := by
  let T := LogTorus n
  let μ : Measure T := angularWeightedTorusMeasure a
  have hp (i j : Fin n) : Integrable
      (fun p : T =>
        sourceTorusBarPartial (fun z => W z i) j p *
          conj (sourceTorusBarPartial (fun z => W z j) i p) +
          (torusScalarRepresentative (fun z => W z i) p *
            angularTorusComplexHessian a i j p) *
              conj (torusScalarRepresentative (fun z => W z j) p)) μ :=
    (integrable_angularTorusBarPartial_pair
      ha (hW i) (hW j)
      (hWp i) (hWp j) (hWc j) j i).add
        (integrable_angularTorusComplexHessian_pair
          ha ha2 (hW i) (hW j)
          (hWp i) (hWp j) (hWc j) i j)
  change
    (∫ p : T,
      sourceTorusFormMixedDerivativeDensity W p +
        angularTorusFormCurvatureDensity a W p ∂μ) =
    ∑ i : Fin n, ∑ j : Fin n,
      ∫ p : T,
        (sourceTorusBarPartial (fun z => W z i) j p *
          conj (sourceTorusBarPartial (fun z => W z j) i p) +
          (torusScalarRepresentative (fun z => W z i) p *
            angularTorusComplexHessian a i j p) *
              conj (torusScalarRepresentative (fun z => W z j) p)) ∂μ
  calc
    _ = ∫ p : T, ∑ i : Fin n, ∑ j : Fin n,
      (sourceTorusBarPartial (fun z => W z i) j p *
        conj (sourceTorusBarPartial (fun z => W z j) i p) +
        (torusScalarRepresentative (fun z => W z i) p *
          angularTorusComplexHessian a i j p) *
            conj (torusScalarRepresentative (fun z => W z j) p)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with p
      simp only [sourceTorusFormMixedDerivativeDensity,
        angularTorusFormCurvatureDensity, ← Finset.sum_add_distrib]
    _ = ∑ i : Fin n,
      ∫ p : T, ∑ j : Fin n,
        (sourceTorusBarPartial (fun z => W z i) j p *
          conj (sourceTorusBarPartial (fun z => W z j) i p) +
          (torusScalarRepresentative (fun z => W z i) p *
            angularTorusComplexHessian a i j p) *
              conj (torusScalarRepresentative (fun z => W z j) p)) ∂μ := by
      exact MeasureTheory.integral_finsetSum Finset.univ
        (fun i _ => MeasureTheory.integrable_finsetSum Finset.univ
          (fun j _ => hp i j))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact MeasureTheory.integral_finsetSum Finset.univ
        (fun j _ => hp i j)

private theorem angularTorus_weighted_complex_bochner_form_cross_identity
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hW : ∀ i : Fin n, ContDiff ℝ 2 (fun z => W z i))
    (hWp : ∀ (i : Fin n) (q : Fin n → ℤ),
      Function.Periodic (fun z => W z i)
        (TorusCharacters.imaginaryShift q))
    (hWc : ∀ i : Fin n,
      HasCompactSupport (torusScalarRepresentative (fun z => W z i))) :
    (∫ p : LogTorus n,
      angularTorusFormAdjoint a W p *
        conj (angularTorusFormAdjoint a W p)
      ∂(angularWeightedTorusMeasure a)) =
    ∫ p : LogTorus n,
      (sourceTorusFormMixedDerivativeDensity W p +
        angularTorusFormCurvatureDensity a W p)
      ∂(angularWeightedTorusMeasure a) := by
  calc
    _ = ∑ i : Fin n, ∑ j : Fin n,
      ∫ p : LogTorus n,
        angularTorusWeightedHolomorphicDerivative a
          (fun z => W z i) i p *
          conj (angularTorusWeightedHolomorphicDerivative a
            (fun z => W z j) j p)
        ∂(angularWeightedTorusMeasure a) :=
      integral_angularTorusFormAdjoint_mul_conj_eq_coordinate_sum
        W ha ha2 hW hWp hWc
    _ = ∑ i : Fin n, ∑ j : Fin n,
      ∫ p : LogTorus n,
        (sourceTorusBarPartial (fun z => W z i) j p *
          conj (sourceTorusBarPartial (fun z => W z j) i p) +
          (torusScalarRepresentative (fun z => W z i) p *
            angularTorusComplexHessian a i j p) *
              conj (torusScalarRepresentative (fun z => W z j) p))
        ∂(angularWeightedTorusMeasure a) :=
      angularTorus_weighted_complex_bochner_form_coordinate_sum
        W ha ha2 hW hWp hWc
    _ = _ :=
      (integral_angularTorusFormMixed_add_curvature_eq_coordinate_sum
        W ha ha2 hW hWp hWc).symm

private theorem integrable_angularTorusFormMixedDerivativeDensity
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (ha : Continuous a)
    (hW : ∀ i : Fin n, ContDiff ℝ 2 (fun z => W z i))
    (hWp : ∀ (i : Fin n) (q : Fin n → ℤ),
      Function.Periodic (fun z => W z i)
        (TorusCharacters.imaginaryShift q))
    (hWc : ∀ i : Fin n,
      HasCompactSupport (torusScalarRepresentative (fun z => W z i))) :
    Integrable (sourceTorusFormMixedDerivativeDensity W)
      (angularWeightedTorusMeasure a) := by
  unfold sourceTorusFormMixedDerivativeDensity
  exact MeasureTheory.integrable_finsetSum Finset.univ
    (fun i _ => MeasureTheory.integrable_finsetSum Finset.univ
      (fun j _ => integrable_angularTorusBarPartial_pair
        ha (hW i) (hW j)
        (hWp i) (hWp j) (hWc j) j i))

private theorem integrable_angularTorusFormCurvatureDensity
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hW : ∀ i : Fin n, ContDiff ℝ 2 (fun z => W z i))
    (hWp : ∀ (i : Fin n) (q : Fin n → ℤ),
      Function.Periodic (fun z => W z i)
        (TorusCharacters.imaginaryShift q))
    (hWc : ∀ i : Fin n,
      HasCompactSupport (torusScalarRepresentative (fun z => W z i))) :
    Integrable (angularTorusFormCurvatureDensity a W)
      (angularWeightedTorusMeasure a) := by
  unfold angularTorusFormCurvatureDensity
  exact MeasureTheory.integrable_finsetSum Finset.univ
    (fun i _ => MeasureTheory.integrable_finsetSum Finset.univ
      (fun j _ => integrable_angularTorusComplexHessian_pair
        ha ha2 (hW i) (hW j)
        (hWp i) (hWp j) (hWc j) i j))

private theorem integrable_angularTorusFormFullDerivativeDensity
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (ha : Continuous a)
    (hW : ∀ i : Fin n, ContDiff ℝ 2 (fun z => W z i))
    (hWp : ∀ (i : Fin n) (q : Fin n → ℤ),
      Function.Periodic (fun z => W z i)
        (TorusCharacters.imaginaryShift q))
    (hWc : ∀ i : Fin n,
      HasCompactSupport (torusScalarRepresentative (fun z => W z i))) :
    Integrable (sourceTorusFormFullDerivativeDensity W)
      (angularWeightedTorusMeasure a) := by
  unfold sourceTorusFormFullDerivativeDensity
  exact MeasureTheory.integrable_finsetSum Finset.univ
    (fun i _ => MeasureTheory.integrable_finsetSum Finset.univ
      (fun j _ => integrable_angularTorusBarPartial_pair
        ha (hW i) (hW i)
        (hWp i) (hWp i) (hWc i) j j))

private theorem integrable_angularTorusFormExteriorDerivativeDensity
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (ha : Continuous a)
    (hW : ∀ i : Fin n, ContDiff ℝ 2 (fun z => W z i))
    (hWp : ∀ (i : Fin n) (q : Fin n → ℤ),
      Function.Periodic (fun z => W z i)
        (TorusCharacters.imaginaryShift q))
    (hWc : ∀ i : Fin n,
      HasCompactSupport (torusScalarRepresentative (fun z => W z i))) :
    Integrable (sourceTorusFormExteriorDerivativeDensity W)
      (angularWeightedTorusMeasure a) := by
  have hf := integrable_angularTorusFormFullDerivativeDensity
    W ha hW hWp hWc
  have hm := integrable_angularTorusFormMixedDerivativeDensity
    W ha hW hWp hWc
  apply (hf.sub hm).congr
  filter_upwards [] with p
  have hp := sourceTorusFormExterior_add_mixed_eq_full W p
  change
    sourceTorusFormFullDerivativeDensity W p -
      sourceTorusFormMixedDerivativeDensity W p =
        sourceTorusFormExteriorDerivativeDensity W p
  linear_combination -hp

private theorem angularTorus_weighted_complex_dolbeault_form_bochner_identity
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hW : ∀ i : Fin n, ContDiff ℝ 2 (fun z => W z i))
    (hWp : ∀ (i : Fin n) (q : Fin n → ℤ),
      Function.Periodic (fun z => W z i)
        (TorusCharacters.imaginaryShift q))
    (hWc : ∀ i : Fin n,
      HasCompactSupport (torusScalarRepresentative (fun z => W z i))) :
    (∫ p : LogTorus n,
      sourceTorusFormExteriorDerivativeDensity W p
      ∂(angularWeightedTorusMeasure a)) +
    (∫ p : LogTorus n,
      angularTorusFormAdjoint a W p *
        conj (angularTorusFormAdjoint a W p)
      ∂(angularWeightedTorusMeasure a)) =
    (∫ p : LogTorus n,
      sourceTorusFormFullDerivativeDensity W p
      ∂(angularWeightedTorusMeasure a)) +
    (∫ p : LogTorus n,
      angularTorusFormCurvatureDensity a W p
      ∂(angularWeightedTorusMeasure a)) := by
  let T := LogTorus n
  let μ : Measure T := angularWeightedTorusMeasure a
  have hm : Integrable
      (sourceTorusFormMixedDerivativeDensity W) μ :=
    integrable_angularTorusFormMixedDerivativeDensity
      W ha hW hWp hWc
  have hc : Integrable
      (angularTorusFormCurvatureDensity a W) μ :=
    integrable_angularTorusFormCurvatureDensity
      W ha ha2 hW hWp hWc
  have he : Integrable
      (sourceTorusFormExteriorDerivativeDensity W) μ :=
    integrable_angularTorusFormExteriorDerivativeDensity
      W ha hW hWp hWc
  have hcross := angularTorus_weighted_complex_bochner_form_cross_identity
    W ha ha2 hW hWp hWc
  change
    (∫ p : T, sourceTorusFormExteriorDerivativeDensity W p ∂μ) +
      (∫ p : T,
        angularTorusFormAdjoint a W p *
          conj (angularTorusFormAdjoint a W p) ∂μ) =
    (∫ p : T, sourceTorusFormFullDerivativeDensity W p ∂μ) +
      (∫ p : T, angularTorusFormCurvatureDensity a W p ∂μ)
  calc
    _ = (∫ p : T,
        sourceTorusFormExteriorDerivativeDensity W p ∂μ) +
      (∫ p : T,
        (sourceTorusFormMixedDerivativeDensity W p +
          angularTorusFormCurvatureDensity a W p) ∂μ) := by
      rw [hcross]
    _ = ((∫ p : T,
        sourceTorusFormExteriorDerivativeDensity W p ∂μ) +
        (∫ p : T,
          sourceTorusFormMixedDerivativeDensity W p ∂μ)) +
      (∫ p : T,
        angularTorusFormCurvatureDensity a W p ∂μ) := by
      rw [MeasureTheory.integral_add hm hc]
      ring
    _ = (∫ p : T,
        (sourceTorusFormExteriorDerivativeDensity W p +
          sourceTorusFormMixedDerivativeDensity W p) ∂μ) +
      (∫ p : T,
        angularTorusFormCurvatureDensity a W p ∂μ) := by
      rw [MeasureTheory.integral_add he hm]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with p
      exact sourceTorusFormExterior_add_mixed_eq_full W p

end WeightedTorusBochner

end Ehrhart

end
