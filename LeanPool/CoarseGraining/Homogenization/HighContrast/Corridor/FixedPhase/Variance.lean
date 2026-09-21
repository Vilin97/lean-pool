/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.PerCoreEnergy
import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.EfronSteinPhase
import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.PhaseComparison.Stability
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.CoarseBounds.Sandwich

/-!
# The fixed-phase variance (Proposition 4.3), realization bound

The Efron–Stein sensitivity step of `p.fixed.phase.variance` assembled at the
level of a single (everywhere-`(1,Θ)`-elliptic) realization pair `a, a'`.

For two fields elliptic on the closed cube `U := cubeSet (originCube d m)`, the
summed squared resampling deviation over any finite family of cores obeys the
`max·sum` estimate of §4.3:

`Σ_k (F_σ(patchCore k a a') − F_σ(a))² ≤ C_d · 4608 · Θ³ · (ℓ/3^m)^{d−2} · (Θ|p|² + |q|²)²`,

with the per-core energies bounded by `exists_perCore_minimizer_energy_le`
(Part B) and the total energy by the C1′ sandwich
(`blockVecDot_coarseBlockMatrix_cube_le`).  The single minimizer `Z` for the
corridor field serves both the sensitivity (via
`abs_phaseObservable_resample_sub_le_of_minimizer`) and the energies.

This is the deterministic, measurability-free core of Proposition 4.3.
-/

open Homogenization MeasureTheory
open scoped BigOperators

namespace Homogenization

variable {d : ℕ}

/-! ## The ratio power identity -/

private theorem ratio_pow_identity {d : ℕ} (hd : 3 ≤ d) {R ℓ : ℝ} (hR : 0 < R) :
    R ^ 2 * (R ^ d)⁻¹ * ℓ ^ (d - 2) = (ℓ / R) ^ (d - 2) := by
  have hRd : R ^ d = R ^ (d - 2) * R ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have hne : (R : ℝ) ^ (d - 2) ≠ 0 := by positivity
  rw [div_pow, hRd]
  field_simp

/-! ## Ellipticity of the two-field patch -/

/-- The two-field core patch of two fields elliptic on the cube is elliptic on
the cube. -/
theorem isEllipticFieldOn_patchCore {Θ : ℝ} {m : ℤ} {ℓ : ℝ} {σ : Vec d} {k : Fin d → ℤ}
    {a a' : CoeffField d}
    (hElla : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a)
    (hElla' : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a') :
    IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) (patchCore ℓ σ k a a') := by
  classical
  refine ⟨?_, fun x hx => ?_⟩
  · refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    have ha := (measurable_pi_iff.mp (measurable_pi_iff.mp hElla.1 i)) j
    have ha' := (measurable_pi_iff.mp (measurable_pi_iff.mp hElla'.1 i)) j
    have heq : (fun x : Vec d => if x ∈ cubeSet (originCube d m)
          then patchCore ℓ σ k a a' x i j else 0)
        = fun x => if x ∈ coreBox ℓ σ k
            then (if x ∈ cubeSet (originCube d m) then a' x i j else 0)
            else (if x ∈ cubeSet (originCube d m) then a x i j else 0) := by
      funext x
      by_cases hc : x ∈ coreBox ℓ σ k
      · simp only [patchCore_apply_of_mem hc, if_pos hc]
      · simp only [patchCore_apply_of_not_mem hc, if_neg hc]
    rw [heq]
    exact Measurable.ite (measurableSet_coreBox ℓ σ k) ha' ha
  · by_cases hc : x ∈ coreBox ℓ σ k
    · rw [patchCore_apply_of_mem hc]; exact hElla'.2 x hx
    · rw [patchCore_apply_of_not_mem hc]; exact hElla.2 x hx

/-! ## The total energy of the cores -/

/-- The summed core energy is bounded by the whole-cube energy `≤ 2 M² · (3^m)^d`. -/
theorem sum_coreEnergy_le [NeZero d] {Θ : ℝ} {m : ℤ} {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (σ : Vec d)
    (P : BlockVec d) {c : CoeffField d}
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) c)
    {Z : BlockState d} (hZadm : IsBlockMuAdmissible (cubeSet (originCube d m)) P Z)
    (hZeng : Mu (cubeSet (originCube d m)) P c
      = blockEnergyAverage (cubeSet (originCube d m)) c Z)
    (K : Finset (Fin d → ℤ)) :
    ∑ k : {k // k ∈ K},
        (∫ x in coreBox ℓ σ k.val ∩ cubeSet (originCube d m),
          blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField c x) (Z.eval x)))
      ≤ 2 * (Θ * vecNormSq P.1 + vecNormSq P.2)
          * ((volume (cubeSet (originCube d m))).toReal) := by
  classical
  set U := cubeSet (originCube d m) with hUdef
  have hU : MeasurableSet U := measurableSet_cubeSet (originCube d m)
  set g : Vec d → ℝ := fun x =>
    blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField c x) (Z.eval x)) with hgdef
  have hZbl : MemBlockL2 U Z.eval := hZadm.memBlockL2_eval
  have hgint : IntegrableOn g U := by
    simpa [blockPairingIntegrand, hgdef] using!
      blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
        (X := Z) (Y := Z) hZbl hZbl hEll
  have hg0 : ∀ x ∈ U, 0 ≤ g x :=
    fun x hx => blockMatrixOfCoeff_quadratic_nonneg (hEll.2 x hx) (Z.eval x)
  -- disjoint core boxes intersected with `U`
  have hmeasS : ∀ k : {k // k ∈ K}, MeasurableSet (coreBox ℓ σ k.val ∩ U) :=
    fun k => (measurableSet_coreBox ℓ σ k.val).inter hU
  have hdisjS : Set.Pairwise (↑(Finset.univ : Finset {k // k ∈ K}))
      (Function.onFun Disjoint fun k : {k // k ∈ K} => coreBox ℓ σ k.val ∩ U) := by
    intro k _ k' _ hkk'
    have hne : k.val ≠ k'.val := fun h => hkk' (Subtype.ext h)
    exact ((disjoint_coreBox hℓ σ hne).inter_left U).inter_right U
  have hintS : ∀ k : {k // k ∈ K}, IntegrableOn g (coreBox ℓ σ k.val ∩ U) :=
    fun k => hgint.mono_set Set.inter_subset_right
  have hbiUnion : ∑ k : {k // k ∈ K},
        (∫ x in coreBox ℓ σ k.val ∩ U, g x)
      = ∫ x in ⋃ k : {k // k ∈ K}, (coreBox ℓ σ k.val ∩ U), g x := by
    rw [show (⋃ k : {k // k ∈ K}, coreBox ℓ σ k.val ∩ U)
          = ⋃ k ∈ (Finset.univ : Finset {k // k ∈ K}), (coreBox ℓ σ k.val ∩ U) by
        simp only [Finset.mem_univ, Set.iUnion_true]]
    exact (integral_biUnion_finset Finset.univ (fun k _ => hmeasS k) hdisjS
      (fun k _ => hintS k)).symm
  have hsub : (⋃ k : {k // k ∈ K}, (coreBox ℓ σ k.val ∩ U)) ⊆ U :=
    Set.iUnion_subset (fun k => Set.inter_subset_right)
  have hunionle : (∫ x in ⋃ k : {k // k ∈ K}, (coreBox ℓ σ k.val ∩ U), g x)
      ≤ ∫ x in U, g x := by
    refine setIntegral_mono_set hgint ?_ (LE.le.eventuallyLE hsub)
    exact (ae_restrict_iff' hU).2 (Filter.Eventually.of_forall (fun x hx => hg0 x hx))
  -- whole-cube energy `= (vol U)·F(c) ≤ (vol U)·2M²`
  have hFeq : blockVecDot P (blockMatVecMul (coarseBlockMatrix U c) P)
      = (volume U).toReal⁻¹ * ∫ x in U, g x :=
    coarseBlockMatrix_quadratic_eq_energyIntegral P hEll hZeng
  have hFle : blockVecDot P (blockMatVecMul (coarseBlockMatrix U c) P)
      ≤ 2 * (Θ * vecNormSq P.1 + vecNormSq P.2) :=
    blockVecDot_coarseBlockMatrix_cube_le hEll P
  have hvolpos : (0 : ℝ) < (volume U).toReal :=
    volume_cubeSet_originCube_toReal_pos_recovery (d := d) m
  have hcubeint : (∫ x in U, g x) ≤ 2 * (Θ * vecNormSq P.1 + vecNormSq P.2) * (volume U).toReal := by
    have h : (volume U).toReal⁻¹ * ∫ x in U, g x ≤ 2 * (Θ * vecNormSq P.1 + vecNormSq P.2) := by
      rw [← hFeq]; exact hFle
    have := mul_le_mul_of_nonneg_left h hvolpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hvolpos.ne', one_mul] at this
    linarith [this]
  calc ∑ k : {k // k ∈ K},
        (∫ x in coreBox ℓ σ k.val ∩ U, g x)
      = ∫ x in ⋃ k : {k // k ∈ K}, (coreBox ℓ σ k.val ∩ U), g x := hbiUnion
    _ ≤ ∫ x in U, g x := hunionle
    _ ≤ 2 * (Θ * vecNormSq P.1 + vecNormSq P.2) * (volume U).toReal := hcubeint


/-! ## The per-realization summed-square bound -/

/-- **Realization bound for `p.fixed.phase.variance`.**  For two fields elliptic
on the closed cube, the summed squared resampling deviation over any finite core
family satisfies the `max·sum` estimate of §4.3, with an explicit
`(ℓ/3^m)^{d−2}` scaling. -/
theorem summed_sq_le_of_ellipticFieldOn [NeZero d] (hd : 3 ≤ d) {m : ℤ} {Θ : ℝ}
    (hΘ : 1 ≤ Θ) {ℓ : ℝ} (hℓ4 : 4 ≤ ℓ) (hℓL : ℓ ≤ (3 : ℝ) ^ m) (σ : Vec d) (P : BlockVec d)
    {a a' : CoeffField d}
    (hElla : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a)
    (hElla' : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a')
    (K : Finset (Fin d → ℤ)) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∑ k : {k // k ∈ K},
          (phaseObservable ℓ σ m P (patchCore ℓ σ k.val a a')
            - phaseObservable ℓ σ m P a) ^ 2
        ≤ Cd * Θ ^ 3 * (ℓ / (3 : ℝ) ^ m) ^ (d - 2)
            * (Θ * vecNormSq P.1 + vecNormSq P.2) ^ 2 := by
  classical
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hΘ0 : (0 : ℝ) < Θ := lt_of_lt_of_le one_pos hΘ
  have hR0 : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hU : MeasurableSet (cubeSet (originCube d m)) := measurableSet_cubeSet (originCube d m)
  set Msq : ℝ := Θ * vecNormSq P.1 + vecNormSq P.2 with hMsqdef
  have hMsq0 : (0 : ℝ) ≤ Msq :=
    add_nonneg (mul_nonneg hΘ0.le (vecNormSq_nonneg _)) (vecNormSq_nonneg _)
  set nrm : ℝ := (volume (cubeSet (originCube d m))).toReal⁻¹ with hnrmdef
  set volReal : ℝ := (volume (cubeSet (originCube d m))).toReal with hvolRealdef
  have hvolR : volReal = ((3 : ℝ) ^ m) ^ d := by
    rw [hvolRealdef, volume_cubeSet_toReal, cubeVolume_eq_pow_scale]; rfl
  have hvolpos : (0 : ℝ) < volReal :=
    volume_cubeSet_originCube_toReal_pos_recovery (d := d) m
  have hnrm0 : (0 : ℝ) ≤ nrm := by rw [hnrmdef]; positivity
  -- the corridor field, its ellipticity, and the per-core package
  have hEllc : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) (corridorField ℓ σ a) :=
    isEllipticFieldOn_corridorField hU hΘ hElla
  obtain ⟨Z, Cd, hCd0, hZadm, hZresp, hZeng, hpercore⟩ :=
    exists_perCore_minimizer_energy_le hd hΘ hℓ4 hℓL σ P hEllc K
  -- per-core energy abbreviation and its two bounds
  set E : {k // k ∈ K} → ℝ := fun k =>
    ∫ x in coreBox ℓ σ k.val ∩ cubeSet (originCube d m),
      blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField (corridorField ℓ σ a) x) (Z.eval x))
    with hEdef
  have hE0 : ∀ k : {k // k ∈ K}, 0 ≤ E k := by
    intro k
    exact setIntegral_nonneg ((measurableSet_coreBox ℓ σ k.val).inter hU)
      (fun x hx => blockMatrixOfCoeff_quadratic_nonneg (hEllc.2 x hx.2) (Z.eval x))
  set Mbound : ℝ := Cd * Θ * ((3 : ℝ) ^ m) ^ 2 * ℓ ^ (d - 2) * Msq with hMbounddef
  have hEle : ∀ k : {k // k ∈ K}, E k ≤ Mbound := fun k => hpercore k.val k.2
  have hMbound0 : (0 : ℝ) ≤ Mbound := by
    rw [hMbounddef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCd0 hΘ0.le)
      (by positivity)) (by positivity)) hMsq0
  -- total energy
  have htotal : ∑ k : {k // k ∈ K}, E k ≤ 2 * Msq * volReal :=
    sum_coreEnergy_le hℓ0.le σ P hEllc hZadm hZeng K
  -- per-core sensitivity
  have hsens : ∀ k : {k // k ∈ K},
      |phaseObservable ℓ σ m P (patchCore ℓ σ k.val a a') - phaseObservable ℓ σ m P a|
        ≤ 48 * Θ * nrm * E k := by
    intro k
    have hbb' : Set.EqOn a (patchCore ℓ σ k.val a a') (coreBox ℓ σ k.val)ᶜ :=
      fun x hx => (patchCore_apply_of_not_mem hx).symm
    exact abs_phaseObservable_resample_sub_le_of_minimizer hΘ P hElla
      (isEllipticFieldOn_patchCore hElla hElla') hbb' hZadm hZresp hZeng
  -- each squared deviation is bounded by `(48 Θ nrm)² E_k²`
  have hfk : ∀ k : {k // k ∈ K},
      (phaseObservable ℓ σ m P (patchCore ℓ σ k.val a a') - phaseObservable ℓ σ m P a) ^ 2
        ≤ (48 * Θ * nrm) ^ 2 * E k ^ 2 := by
    intro k
    have hM0 : (0 : ℝ) ≤ 48 * Θ * nrm * E k :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hΘ0.le) hnrm0) (hE0 k)
    have h := hsens k
    have hsq : (phaseObservable ℓ σ m P (patchCore ℓ σ k.val a a')
        - phaseObservable ℓ σ m P a) ^ 2 ≤ (48 * Θ * nrm * E k) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    calc (phaseObservable ℓ σ m P (patchCore ℓ σ k.val a a') - phaseObservable ℓ σ m P a) ^ 2
        ≤ (48 * Θ * nrm * E k) ^ 2 := hsq
      _ = (48 * Θ * nrm) ^ 2 * E k ^ 2 := by ring
  -- assemble the max·sum estimate
  have hstep : ∑ k : {k // k ∈ K},
        (phaseObservable ℓ σ m P (patchCore ℓ σ k.val a a') - phaseObservable ℓ σ m P a) ^ 2
      ≤ (48 * Θ * nrm) ^ 2 * (Mbound * (2 * Msq * volReal)) := by
    have hsum1 : ∑ k : {k // k ∈ K},
          (phaseObservable ℓ σ m P (patchCore ℓ σ k.val a a') - phaseObservable ℓ σ m P a) ^ 2
        ≤ ∑ k : {k // k ∈ K}, (48 * Θ * nrm) ^ 2 * E k ^ 2 :=
      Finset.sum_le_sum (fun k _ => hfk k)
    have hEsq : ∀ k : {k // k ∈ K}, E k ^ 2 ≤ Mbound * E k := by
      intro k
      have := mul_le_mul_of_nonneg_right (hEle k) (hE0 k)
      calc E k ^ 2 = E k * E k := by ring
        _ ≤ Mbound * E k := this
    have hsum2 : ∑ k : {k // k ∈ K}, E k ^ 2 ≤ Mbound * ∑ k : {k // k ∈ K}, E k := by
      calc ∑ k : {k // k ∈ K}, E k ^ 2 ≤ ∑ k : {k // k ∈ K}, Mbound * E k :=
            Finset.sum_le_sum (fun k _ => hEsq k)
        _ = Mbound * ∑ k : {k // k ∈ K}, E k := by rw [Finset.mul_sum]
    have hcoef0 : (0 : ℝ) ≤ (48 * Θ * nrm) ^ 2 := sq_nonneg _
    calc ∑ k : {k // k ∈ K},
          (phaseObservable ℓ σ m P (patchCore ℓ σ k.val a a') - phaseObservable ℓ σ m P a) ^ 2
        ≤ ∑ k : {k // k ∈ K}, (48 * Θ * nrm) ^ 2 * E k ^ 2 := hsum1
      _ = (48 * Θ * nrm) ^ 2 * ∑ k : {k // k ∈ K}, E k ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (48 * Θ * nrm) ^ 2 * (Mbound * ∑ k : {k // k ∈ K}, E k) :=
          mul_le_mul_of_nonneg_left hsum2 hcoef0
      _ ≤ (48 * Θ * nrm) ^ 2 * (Mbound * (2 * Msq * volReal)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left htotal hMbound0) hcoef0
  -- close: rewrite the constant into `(ℓ/3^m)^{d−2}` form
  refine ⟨4608 * Cd, mul_nonneg (by norm_num) hCd0, le_trans hstep (le_of_eq ?_)⟩
  have hRdne : ((3 : ℝ) ^ m) ^ d ≠ 0 := by positivity
  have hnrmR : nrm = (((3 : ℝ) ^ m) ^ d)⁻¹ := by rw [hnrmdef, hvolR]
  have key : (48 * Θ * nrm) ^ 2 * (Mbound * (2 * Msq * volReal))
      = 4608 * Cd * Θ ^ 3
          * (((3 : ℝ) ^ m) ^ 2 * (((3 : ℝ) ^ m) ^ d)⁻¹ * ℓ ^ (d - 2)) * Msq ^ 2 := by
    rw [hMbounddef, hnrmR, hvolR]
    field_simp
    ring
  rw [key, ratio_pow_identity hd hR0]

/-! ## The per-realization summed-square bound, uniform constant -/

/-- **Uniform realization bound.**  The constant-outside form of
`summed_sq_le_of_ellipticFieldOn`: a single dimensional constant `B`, independent
of the realization pair `(a, a')` and the core family `K`, bounds the summed
squared resampling deviation.  Uniformity is inherited from
`exists_perCore_minimizer_energy_le_uniform`. -/
theorem summed_sq_le_of_ellipticFieldOn_uniform [NeZero d] (hd : 3 ≤ d) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {m : ℤ} {Θ : ℝ} (_hΘ : 1 ≤ Θ) {ℓ : ℝ} (_hℓ4 : 4 ≤ ℓ) (_hℓL : ℓ ≤ (3 : ℝ) ^ m)
        (σ : Vec d) (P : BlockVec d) {a a' : CoeffField d}
        (_hElla : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a)
        (_hElla' : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a')
        (K : Finset (Fin d → ℤ)),
      ∑ k : {k // k ∈ K},
          (phaseObservable ℓ σ m P (patchCore ℓ σ k.val a a')
            - phaseObservable ℓ σ m P a) ^ 2
        ≤ B * Θ ^ 3 * (ℓ / (3 : ℝ) ^ m) ^ (d - 2)
            * (Θ * vecNormSq P.1 + vecNormSq P.2) ^ 2 := by
  classical
  obtain ⟨CdPC, hCdPC0, hpercoreU⟩ := exists_perCore_minimizer_energy_le_uniform hd
  refine ⟨4608 * CdPC, mul_nonneg (by norm_num) hCdPC0, ?_⟩
  intro m Θ hΘ ℓ hℓ4 hℓL σ P a a' hElla hElla' K
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hΘ0 : (0 : ℝ) < Θ := lt_of_lt_of_le one_pos hΘ
  have hR0 : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hU : MeasurableSet (cubeSet (originCube d m)) := measurableSet_cubeSet (originCube d m)
  set Msq : ℝ := Θ * vecNormSq P.1 + vecNormSq P.2 with hMsqdef
  have hMsq0 : (0 : ℝ) ≤ Msq :=
    add_nonneg (mul_nonneg hΘ0.le (vecNormSq_nonneg _)) (vecNormSq_nonneg _)
  set nrm : ℝ := (volume (cubeSet (originCube d m))).toReal⁻¹ with hnrmdef
  set volReal : ℝ := (volume (cubeSet (originCube d m))).toReal with hvolRealdef
  have hvolR : volReal = ((3 : ℝ) ^ m) ^ d := by
    rw [hvolRealdef, volume_cubeSet_toReal, cubeVolume_eq_pow_scale]; rfl
  have hvolpos : (0 : ℝ) < volReal :=
    volume_cubeSet_originCube_toReal_pos_recovery (d := d) m
  have hnrm0 : (0 : ℝ) ≤ nrm := by rw [hnrmdef]; positivity
  have hEllc : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) (corridorField ℓ σ a) :=
    isEllipticFieldOn_corridorField hU hΘ hElla
  obtain ⟨Z, hZadm, hZresp, hZeng, hpercore⟩ := hpercoreU hΘ hℓ4 hℓL σ P hEllc K
  set E : {k // k ∈ K} → ℝ := fun k =>
    ∫ x in coreBox ℓ σ k.val ∩ cubeSet (originCube d m),
      blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField (corridorField ℓ σ a) x) (Z.eval x))
    with hEdef
  have hE0 : ∀ k : {k // k ∈ K}, 0 ≤ E k := by
    intro k
    exact setIntegral_nonneg ((measurableSet_coreBox ℓ σ k.val).inter hU)
      (fun x hx => blockMatrixOfCoeff_quadratic_nonneg (hEllc.2 x hx.2) (Z.eval x))
  set Mbound : ℝ := CdPC * Θ * ((3 : ℝ) ^ m) ^ 2 * ℓ ^ (d - 2) * Msq with hMbounddef
  have hEle : ∀ k : {k // k ∈ K}, E k ≤ Mbound := fun k => hpercore k.val k.2
  have hMbound0 : (0 : ℝ) ≤ Mbound := by
    rw [hMbounddef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCdPC0 hΘ0.le)
      (by positivity)) (by positivity)) hMsq0
  have htotal : ∑ k : {k // k ∈ K}, E k ≤ 2 * Msq * volReal :=
    sum_coreEnergy_le hℓ0.le σ P hEllc hZadm hZeng K
  have hsens : ∀ k : {k // k ∈ K},
      |phaseObservable ℓ σ m P (patchCore ℓ σ k.val a a') - phaseObservable ℓ σ m P a|
        ≤ 48 * Θ * nrm * E k := by
    intro k
    have hbb' : Set.EqOn a (patchCore ℓ σ k.val a a') (coreBox ℓ σ k.val)ᶜ :=
      fun x hx => (patchCore_apply_of_not_mem hx).symm
    exact abs_phaseObservable_resample_sub_le_of_minimizer hΘ P hElla
      (isEllipticFieldOn_patchCore hElla hElla') hbb' hZadm hZresp hZeng
  have hfk : ∀ k : {k // k ∈ K},
      (phaseObservable ℓ σ m P (patchCore ℓ σ k.val a a') - phaseObservable ℓ σ m P a) ^ 2
        ≤ (48 * Θ * nrm) ^ 2 * E k ^ 2 := by
    intro k
    have hM0 : (0 : ℝ) ≤ 48 * Θ * nrm * E k :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hΘ0.le) hnrm0) (hE0 k)
    have h := hsens k
    have hsq : (phaseObservable ℓ σ m P (patchCore ℓ σ k.val a a')
        - phaseObservable ℓ σ m P a) ^ 2 ≤ (48 * Θ * nrm * E k) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    calc (phaseObservable ℓ σ m P (patchCore ℓ σ k.val a a') - phaseObservable ℓ σ m P a) ^ 2
        ≤ (48 * Θ * nrm * E k) ^ 2 := hsq
      _ = (48 * Θ * nrm) ^ 2 * E k ^ 2 := by ring
  have hstep : ∑ k : {k // k ∈ K},
        (phaseObservable ℓ σ m P (patchCore ℓ σ k.val a a') - phaseObservable ℓ σ m P a) ^ 2
      ≤ (48 * Θ * nrm) ^ 2 * (Mbound * (2 * Msq * volReal)) := by
    have hsum1 : ∑ k : {k // k ∈ K},
          (phaseObservable ℓ σ m P (patchCore ℓ σ k.val a a') - phaseObservable ℓ σ m P a) ^ 2
        ≤ ∑ k : {k // k ∈ K}, (48 * Θ * nrm) ^ 2 * E k ^ 2 :=
      Finset.sum_le_sum (fun k _ => hfk k)
    have hEsq : ∀ k : {k // k ∈ K}, E k ^ 2 ≤ Mbound * E k := by
      intro k
      have := mul_le_mul_of_nonneg_right (hEle k) (hE0 k)
      calc E k ^ 2 = E k * E k := by ring
        _ ≤ Mbound * E k := this
    have hsum2 : ∑ k : {k // k ∈ K}, E k ^ 2 ≤ Mbound * ∑ k : {k // k ∈ K}, E k := by
      calc ∑ k : {k // k ∈ K}, E k ^ 2 ≤ ∑ k : {k // k ∈ K}, Mbound * E k :=
            Finset.sum_le_sum (fun k _ => hEsq k)
        _ = Mbound * ∑ k : {k // k ∈ K}, E k := by rw [Finset.mul_sum]
    have hcoef0 : (0 : ℝ) ≤ (48 * Θ * nrm) ^ 2 := sq_nonneg _
    calc ∑ k : {k // k ∈ K},
          (phaseObservable ℓ σ m P (patchCore ℓ σ k.val a a') - phaseObservable ℓ σ m P a) ^ 2
        ≤ ∑ k : {k // k ∈ K}, (48 * Θ * nrm) ^ 2 * E k ^ 2 := hsum1
      _ = (48 * Θ * nrm) ^ 2 * ∑ k : {k // k ∈ K}, E k ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (48 * Θ * nrm) ^ 2 * (Mbound * ∑ k : {k // k ∈ K}, E k) :=
          mul_le_mul_of_nonneg_left hsum2 hcoef0
      _ ≤ (48 * Θ * nrm) ^ 2 * (Mbound * (2 * Msq * volReal)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left htotal hMbound0) hcoef0
  refine le_trans hstep (le_of_eq ?_)
  have hnrmR : nrm = (((3 : ℝ) ^ m) ^ d)⁻¹ := by rw [hnrmdef, hvolR]
  have key : (48 * Θ * nrm) ^ 2 * (Mbound * (2 * Msq * volReal))
      = 4608 * CdPC * Θ ^ 3
          * (((3 : ℝ) ^ m) ^ 2 * (((3 : ℝ) ^ m) ^ d)⁻¹ * ℓ ^ (d - 2)) * Msq ^ 2 := by
    rw [hMbounddef, hnrmR, hvolR]
    field_simp
    ring
  rw [key, ratio_pow_identity hd hR0]

end Homogenization
