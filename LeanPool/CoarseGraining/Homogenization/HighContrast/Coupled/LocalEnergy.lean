/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.HighContrast.Coupled.LocalEnergy.Bounds

/-!
# Local block energy (Prop 3.4)

The two consumer theorems, assembled from the test
identity (`energyIntegral_eq_bulk_add_cutoff`) and the pointwise bulk/cutoff
estimates (`bulkIntegrand_le`, `cutoffIntegrand_le`).

* `centered_local_block_energy` (T1): the `𝓔`-level bound
  `𝓔 ≤ C_d (M²·|supp η ∩ U| + Θ·K∞²·∫_U Σᵢ(∂ᵢη)²)`.
* `local_block_energy` (T2): the consumer shape
  `∫_C Z·𝐁Z ≤ C_d (M²·|supp η ∩ U| + Θ·K∞²·∫_U Σᵢ(∂ᵢη)²)`.

`M² = Θ|p|² + |q|²`.  No `EuclideanSpace`.
-/

namespace Homogenization

open Homogenization
open MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d] {m : ℤ}

local notation "U" => openCubeSet (originCube d m)

/-! ## Integrability of the two elementary weights -/

omit [NeZero d] in
theorem integrableOn_sqCutoff {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hIcc : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) :
    IntegrableOn (sqCutoff η) U := by
  let := isFiniteMeasure_openCubeSet_originCube (d := d) m
  exact (sqCutoff_memLpTop (m := m) hη hIcc).integrable le_top

omit [NeZero d] in
/-- The squared-gradient norm is integrable on the cube. -/
theorem integrableOn_gradEtaSq {η : Vec d → ℝ} {Gη : ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hGη : ∀ x i, |fderiv ℝ η x (basisVec i)| ≤ Gη) :
    IntegrableOn (fun x => vecNormSq (fun i => fderiv ℝ η x (basisVec i))) U := by
  let := isFiniteMeasure_openCubeSet_originCube (d := d) m
  have hcont : Continuous (fun x => vecNormSq (fun i => fderiv ℝ η x (basisVec i))) := by
    have hfd : Continuous (fun x => fderiv ℝ η x) := hη.continuous_fderiv (by simp)
    have hco : Continuous (fun x => (fun i => fderiv ℝ η x (basisVec i))) :=
      continuous_pi (fun i => hfd.clm_apply continuous_const)
    unfold vecNormSq vecDot
    exact continuous_finsetSum _ (fun i _ =>
      ((continuous_apply i).comp hco).mul ((continuous_apply i).comp hco))
  have hmem : MemLp (fun x => vecNormSq (fun i => fderiv ℝ η x (basisVec i))) (⊤ : ENNReal)
      (volumeMeasureOn (openCubeSet (originCube d m))) := by
    refine MeasureTheory.memLp_top_of_bound hcont.aestronglyMeasurable
      ((d : ℝ) * Gη ^ 2) ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (vecNormSq_nonneg _)]
    calc vecNormSq (fun i => fderiv ℝ η x (basisVec i))
        = ∑ i, (fderiv ℝ η x (basisVec i)) * (fderiv ℝ η x (basisVec i)) := rfl
      _ ≤ ∑ _i : Fin d, Gη ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          nlinarith [hGη x i, abs_nonneg (fderiv ℝ η x (basisVec i)),
            sq_abs (fderiv ℝ η x (basisVec i))]
      _ = (d : ℝ) * Gη ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact hmem.integrable le_top

/-! ## `∫ η² ≤ |supp η ∩ U|` -/

omit [NeZero d] in
theorem setIntegral_sqCutoff_le {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hIcc : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x in U, sqCutoff η x) ≤ (volume (Function.support η ∩ U)).toReal := by
  let := isFiniteMeasure_openCubeSet_originCube (d := d) m
  have hsuppOpen : IsOpen (Function.support η) := by
    have hpre : Function.support η = η ⁻¹' {0}ᶜ := by
      ext x; simp [Function.mem_support]
    rw [hpre]; exact isOpen_compl_singleton.preimage hη.continuous
  have hsuppMeas : MeasurableSet (Function.support η) := hsuppOpen.measurableSet
  have hUmeas : MeasurableSet (openCubeSet (originCube d m)) := measurableSet_openCubeSet _
  have hsq_int : IntegrableOn (sqCutoff η) U := integrableOn_sqCutoff hη hIcc
  have hind_int : IntegrableOn (Set.indicator (Function.support η) (fun _ => (1:ℝ)))
      (openCubeSet (originCube d m)) :=
    (integrable_const (1:ℝ)).indicator hsuppMeas
  have hbound : ∀ x ∈ (openCubeSet (originCube d m) : Set (Vec d)),
      sqCutoff η x ≤ Set.indicator (Function.support η) (fun _ => (1:ℝ)) x := by
    intro x _
    by_cases hx : x ∈ Function.support η
    · rw [Set.indicator_of_mem hx]; exact sqCutoff_le_one hIcc x
    · rw [Set.indicator_of_notMem hx]
      simp only [Function.mem_support, not_not] at hx
      rw [sqCutoff_apply, hx]; norm_num
  calc (∫ x in U, sqCutoff η x)
      ≤ ∫ x in U, Set.indicator (Function.support η) (fun _ => (1:ℝ)) x :=
        setIntegral_mono_on hsq_int hind_int hUmeas hbound
    _ = ∫ _ in (U ∩ Function.support η), (1:ℝ) := setIntegral_indicator hsuppMeas
    _ = (volume (U ∩ Function.support η)).toReal := by
        rw [setIntegral_const, smul_eq_mul, mul_one]; rfl
    _ = (volume (Function.support η ∩ U)).toReal := by rw [Set.inter_comm]

/-! ## The two integral estimates -/

omit [NeZero d] in
theorem setIntegral_bulkIntegrand_le {a : CoeffField d} {Θ : ℝ} {v vstar : H1Function U}
    {P : BlockVec d} {η : Vec d → ℝ}
    (hEllO : IsEllipticFieldOn 1 Θ U a)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hIcc : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x in U, bulkIntegrand a v vstar P η x)
      ≤ 5 * (Θ * vecNormSq P.1 + vecNormSq P.2) * (∫ x in U, sqCutoff η x)
        + (1/8) * (∫ x in U, energyIntegrand a v vstar P η x) := by
  have hib : IntegrableOn (bulkIntegrand a v vstar P η) U := integrableOn_bulkIntegrand hEllO hη hIcc
  have hisq := integrableOn_sqCutoff (m := m) hη hIcc
  have hie : IntegrableOn (energyIntegrand a v vstar P η) U :=
    integrableOn_energyIntegrand hEllO hη hIcc
  have hbnd : IntegrableOn (fun x => 5 * (Θ * vecNormSq P.1 + vecNormSq P.2) * sqCutoff η x
      + (1/8) * energyIntegrand a v vstar P η x) U :=
    (hisq.const_mul _).add (hie.const_mul _)
  calc (∫ x in U, bulkIntegrand a v vstar P η x)
      ≤ ∫ x in U, (5 * (Θ * vecNormSq P.1 + vecNormSq P.2) * sqCutoff η x
          + (1/8) * energyIntegrand a v vstar P η x) :=
        setIntegral_mono_on hib hbnd (measurableSet_openCubeSet _)
          (fun x hx => bulkIntegrand_le hEllO hx)
    _ = 5 * (Θ * vecNormSq P.1 + vecNormSq P.2) * (∫ x in U, sqCutoff η x)
          + (1/8) * (∫ x in U, energyIntegrand a v vstar P η x) := by
        rw [integral_add (hisq.const_mul _) (hie.const_mul _), integral_const_mul,
          integral_const_mul]

omit [NeZero d] in
theorem setIntegral_cutoffIntegrand_le {a : CoeffField d} {Θ : ℝ} {v vstar : H1Function U}
    {P : BlockVec d} {η : Vec d → ℝ} {Gη c Kinf : ℝ}
    (hEllO : IsEllipticFieldOn 1 Θ U a)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hIcc : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (hGη : ∀ x i, |fderiv ℝ η x (basisVec i)| ≤ Gη)
    (hKv : ∀ᵐ x ∂(volumeMeasureOn U), |(centeredPotential m v P.1 c).toFun x| ≤ Kinf)
    (hKvs : ∀ᵐ x ∂(volumeMeasureOn U), |(centeredPotential m vstar P.1 (-c)).toFun x| ≤ Kinf) :
    (∫ x in U, cutoffIntegrand a v vstar P c η x)
      ≤ (1/16) * (∫ x in U, energyIntegrand a v vstar P η x)
        + 2 * (Θ * vecNormSq P.1 + vecNormSq P.2) * (∫ x in U, sqCutoff η x)
        + 67 * Θ * Kinf ^ 2
          * (∫ x in U, vecNormSq (fun i => fderiv ℝ η x (basisVec i))) := by
  have hic : IntegrableOn (cutoffIntegrand a v vstar P c η) U :=
    integrableOn_cutoffIntegrand hEllO hη hIcc hGη c
  have hisq := integrableOn_sqCutoff (m := m) hη hIcc
  have hie : IntegrableOn (energyIntegrand a v vstar P η) U :=
    integrableOn_energyIntegrand hEllO hη hIcc
  have hig := integrableOn_gradEtaSq (m := m) hη hGη
  have hbnd : IntegrableOn (fun x => (1/16) * energyIntegrand a v vstar P η x
      + 2 * (Θ * vecNormSq P.1 + vecNormSq P.2) * sqCutoff η x
      + 67 * Θ * Kinf ^ 2 * vecNormSq (fun i => fderiv ℝ η x (basisVec i))) U :=
    ((hie.const_mul _).add (hisq.const_mul _)).add (hig.const_mul _)
  have hae : (fun x => cutoffIntegrand a v vstar P c η x) ≤ᵐ[volumeMeasureOn U]
      (fun x => (1/16) * energyIntegrand a v vstar P η x
        + 2 * (Θ * vecNormSq P.1 + vecNormSq P.2) * sqCutoff η x
        + 67 * Θ * Kinf ^ 2 * vecNormSq (fun i => fderiv ℝ η x (basisVec i))) := by
    have hmem : ∀ᵐ x ∂(volumeMeasureOn U), x ∈ (openCubeSet (originCube d m) : Set (Vec d)) :=
      ae_restrict_mem (measurableSet_openCubeSet _)
    filter_upwards [hmem, hKv, hKvs] with x hx hxv hxvs
    exact cutoffIntegrand_le hEllO hη hx hxv hxvs
  calc (∫ x in U, cutoffIntegrand a v vstar P c η x)
      ≤ ∫ x in U, ((1/16) * energyIntegrand a v vstar P η x
          + 2 * (Θ * vecNormSq P.1 + vecNormSq P.2) * sqCutoff η x
          + 67 * Θ * Kinf ^ 2 * vecNormSq (fun i => fderiv ℝ η x (basisVec i))) :=
        setIntegral_mono_ae_restrict hic hbnd hae
    _ = (1/16) * (∫ x in U, energyIntegrand a v vstar P η x)
          + 2 * (Θ * vecNormSq P.1 + vecNormSq P.2) * (∫ x in U, sqCutoff η x)
          + 67 * Θ * Kinf ^ 2
            * (∫ x in U, vecNormSq (fun i => fderiv ℝ η x (basisVec i))) := by
        have e1 : (∫ x in U, ((1/16) * energyIntegrand a v vstar P η x
              + 2 * (Θ * vecNormSq P.1 + vecNormSq P.2) * sqCutoff η x
              + 67 * Θ * Kinf ^ 2 * vecNormSq (fun i => fderiv ℝ η x (basisVec i))))
            = (∫ x in U, ((1/16) * energyIntegrand a v vstar P η x
              + 2 * (Θ * vecNormSq P.1 + vecNormSq P.2) * sqCutoff η x))
              + ∫ x in U, 67 * Θ * Kinf ^ 2 * vecNormSq (fun i => fderiv ℝ η x (basisVec i)) :=
          integral_add ((hie.const_mul _).add (hisq.const_mul _)) (hig.const_mul _)
        have e2 : (∫ x in U, ((1/16) * energyIntegrand a v vstar P η x
              + 2 * (Θ * vecNormSq P.1 + vecNormSq P.2) * sqCutoff η x))
            = (∫ x in U, (1/16) * energyIntegrand a v vstar P η x)
              + ∫ x in U, 2 * (Θ * vecNormSq P.1 + vecNormSq P.2) * sqCutoff η x :=
          integral_add (hie.const_mul _) (hisq.const_mul _)
        rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul]

/-! ## `∑ᵢ(∂ᵢη)² = |∇η|²` bridge -/

omit [NeZero d] in
/-- The coordinate expression of `|∇η|²` equals its vector norm. -/
theorem gradEtaSq_eq_vecNormSq {η : Vec d → ℝ} (x : Vec d) :
    (∑ i, (fderiv ℝ η x (basisVec i)) ^ 2)
      = vecNormSq (fun i => fderiv ℝ η x (basisVec i)) := by
  unfold vecNormSq vecDot
  exact Finset.sum_congr rfl (fun i _ => by rw [pow_two])

/-! ## Θ ≥ 0 from ellipticity on the (nonempty) cube -/

omit [NeZero d] in
/-- The ellipticity parameter is nonnegative on the nonempty cube. -/
theorem theta_nonneg_of_isEllipticFieldOn {a : CoeffField d} {Θ : ℝ}
    (hEllO : IsEllipticFieldOn 1 Θ U a) : 0 ≤ Θ := by
  have hne : Set.Nonempty (openCubeSet (originCube d m)) := by
    refine ⟨cubeCenter (originCube d m), ?_⟩
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos _)
  obtain ⟨x0, hx0⟩ := hne
  exact le_trans zero_le_one (hEllO.2 x0 hx0).2.1

/-! ## T1 — the centered energy bound -/

omit [NeZero d] in
/-- **T1 — `centered_local_block_energy`.**  The `𝓔`-level bound of `p.local.block.energy`. -/
theorem centered_local_block_energy {a : CoeffField d} {Θ : ℝ}
    {v vstar : H1Function U} {P : BlockVec d} {η : Vec d → ℝ} {Gη c Kinf : ℝ}
    (hEllO : IsEllipticFieldOn 1 Θ U a)
    (hWeak : CoupledWeakForm a U P.2 v vstar)
    (hTrace : MemH10 U (fun x => v.toFun x + vstar.toFun x - vecDot P.1 x))
    (hKv : ∀ᵐ x ∂(volumeMeasureOn U), |(centeredPotential m v P.1 c).toFun x| ≤ Kinf)
    (hKvs : ∀ᵐ x ∂(volumeMeasureOn U), |(centeredPotential m vstar P.1 (-c)).toFun x| ≤ Kinf)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hIcc : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (hGη : ∀ x i, |fderiv ℝ η x (basisVec i)| ≤ Gη) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      (∫ x in U, (η x) ^ 2
          * (vecDot ((centeredPotential m v P.1 c).grad x)
                (matVecMul (symmPart (a x)) ((centeredPotential m v P.1 c).grad x))
            + vecDot ((centeredPotential m vstar P.1 (-c)).grad x)
                (matVecMul (symmPart (a x)) ((centeredPotential m vstar P.1 (-c)).grad x))))
        ≤ Cd * ((Θ * vecNormSq P.1 + vecNormSq P.2)
              * (volume (Function.support η ∩ U)).toReal
            + Θ * Kinf ^ 2 * (∫ x in U, ∑ i, (fderiv ℝ η x (basisVec i)) ^ 2)) := by
  -- rewrite the `𝓔`-integrand to `energyIntegrand`
  have hEeq : (∫ x in U, (η x) ^ 2
        * (vecDot ((centeredPotential m v P.1 c).grad x)
              (matVecMul (symmPart (a x)) ((centeredPotential m v P.1 c).grad x))
          + vecDot ((centeredPotential m vstar P.1 (-c)).grad x)
              (matVecMul (symmPart (a x)) ((centeredPotential m vstar P.1 (-c)).grad x))))
      = ∫ x in U, energyIntegrand a v vstar P η x := by
    refine setIntegral_congr_fun (measurableSet_openCubeSet _) (fun x _ => ?_)
    simp only [energyIntegrand, centeredPotential_grad, sqCutoff_apply]
  -- rewrite the gradient-squared integral to `vecNormSq`
  have hIGeq : (∫ x in U, ∑ i, (fderiv ℝ η x (basisVec i)) ^ 2)
      = ∫ x in U, vecNormSq (fun i => fderiv ℝ η x (basisVec i)) := by
    refine setIntegral_congr_fun (measurableSet_openCubeSet _) (fun x _ => ?_)
    exact gradEtaSq_eq_vecNormSq x
  rw [hEeq, hIGeq]
  -- abbreviations
  set 𝓔 := ∫ x in U, energyIntegrand a v vstar P η x with h𝓔
  set Isq := ∫ x in U, sqCutoff η x with hIsq
  set IG := ∫ x in U, vecNormSq (fun i => fderiv ℝ η x (basisVec i)) with hIG
  set M2 := Θ * vecNormSq P.1 + vecNormSq P.2 with hM2
  have hΘ0 : 0 ≤ Θ := theta_nonneg_of_isEllipticFieldOn (m := m) hEllO
  have hM20 : 0 ≤ M2 := by
    rw [hM2]; exact add_nonneg (mul_nonneg hΘ0 (vecNormSq_nonneg _)) (vecNormSq_nonneg _)
  have hvol0 : 0 ≤ (volume (Function.support η ∩ U)).toReal := ENNReal.toReal_nonneg
  have hIG0 : 0 ≤ IG := by
    rw [hIG]
    exact setIntegral_nonneg (measurableSet_openCubeSet _) (fun x _ => vecNormSq_nonneg _)
  have hIsqvol : Isq ≤ (volume (Function.support η ∩ U)).toReal := by
    rw [hIsq]; exact setIntegral_sqCutoff_le hη hIcc
  -- the test identity and the two integral estimates
  have hsplit : 𝓔 = (∫ x in U, bulkIntegrand a v vstar P η x)
      + (∫ x in U, cutoffIntegrand a v vstar P c η x) := by
    rw [h𝓔]; exact energyIntegral_eq_bulk_add_cutoff hEllO hη hIcc hGη hWeak hTrace
  have hbulk : (∫ x in U, bulkIntegrand a v vstar P η x) ≤ 5 * M2 * Isq + (1/8) * 𝓔 := by
    rw [hM2, hIsq, h𝓔]; exact setIntegral_bulkIntegrand_le hEllO hη hIcc
  have hcut : (∫ x in U, cutoffIntegrand a v vstar P c η x)
      ≤ (1/16) * 𝓔 + 2 * M2 * Isq + 67 * Θ * Kinf ^ 2 * IG := by
    rw [hM2, hIsq, h𝓔, hIG]; exact setIntegral_cutoffIntegrand_le hEllO hη hIcc hGη hKv hKvs
  -- combine and absorb
  have hKinf2 : 0 ≤ Kinf ^ 2 := sq_nonneg _
  have hMsqvol : 5 * M2 * Isq ≤ 5 * M2 * (volume (Function.support η ∩ U)).toReal :=
    mul_le_mul_of_nonneg_left hIsqvol (by positivity)
  have hMsqvol2 : 2 * M2 * Isq ≤ 2 * M2 * (volume (Function.support η ∩ U)).toReal :=
    mul_le_mul_of_nonneg_left hIsqvol (by positivity)
  refine ⟨128, by norm_num, ?_⟩
  have hΘKIG : 0 ≤ Θ * Kinf ^ 2 * IG :=
    mul_nonneg (mul_nonneg hΘ0 hKinf2) hIG0
  have hMvol0 : 0 ≤ M2 * (volume (Function.support η ∩ U)).toReal :=
    mul_nonneg hM20 hvol0
  nlinarith [hsplit, hbulk, hcut, hMsqvol, hMsqvol2, hΘKIG, hMvol0]

/-! ## T2 — the consumer shape -/

omit [NeZero d] in
/-- Adding back the affine part: `2∇v·s∇v ≤ 4V·sV + Θ|p|²` with `V = ∇v − ½p`. -/
theorem two_symmPart_grad_le {Θ : ℝ} {A : Mat d} (hA : IsThetaElliptic Θ A) (gv p : Vec d) :
    2 * vecDot gv (matVecMul (symmPart A) gv)
      ≤ 4 * vecDot (gv - (1/2:ℝ)•p) (matVecMul (symmPart A) (gv - (1/2:ℝ)•p))
        + Θ * vecNormSq p := by
  set s := symmPart A with hs
  set V := gv - (1/2:ℝ)•p with hVd
  set b := (1/2:ℝ)•p with hbd
  have hgvVb : gv = V + b := by rw [hVd, hbd]; abel
  have hpsd : 0 ≤ vecDot (V - b) (matVecMul s (V - b)) :=
    vecDot_matVecMul_symmPart_nonneg hA _
  have hpar : vecDot (V + b) (matVecMul s (V + b)) + vecDot (V - b) (matVecMul s (V - b))
      = 2 * vecDot V (matVecMul s V) + 2 * vecDot b (matVecMul s b) := by
    have e2 : matVecMul s (V - b) = matVecMul s V - matVecMul s b := by
      rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, ← sub_eq_add_neg]
    rw [matVecMul_add, e2]
    simp only [sub_eq_add_neg, vecDot_add_left, vecDot_add_right, vecDot_neg_left,
      vecDot_neg_right]
    ring
  have hbsb : vecDot b (matVecMul s b) = (1/4) * vecDot p (matVecMul s p) := by
    rw [hbd, matVecMul_smul, vecDot_smul_left, vecDot_smul_right]; ring
  have hupper : vecDot p (matVecMul s p) ≤ Θ * vecNormSq p :=
    upperBound_symmPart_of_isEllipticMatrix hA p
  rw [hgvVb]
  nlinarith [hpar, hpsd, hbsb, hupper]

omit [NeZero d] in
/-- **T2 — `local_block_energy`.**  The consumer shape of `p.local.block.energy`:
the block energy on `C` is controlled by `M²·|supp η ∩ U| + Θ·K∞²·∫_U Σᵢ(∂ᵢη)²`. -/
theorem local_block_energy {a : CoeffField d} {Θ : ℝ}
    {v vstar : H1Function U} {P : BlockVec d} {η : Vec d → ℝ} {Gη c Kinf : ℝ}
    {Z : BlockState d} {C : Set (Vec d)}
    (hEllO : IsEllipticFieldOn 1 Θ U a)
    (hWeak : CoupledWeakForm a U P.2 v vstar)
    (hTrace : MemH10 U (fun x => v.toFun x + vstar.toFun x - vecDot P.1 x))
    (hKv : ∀ᵐ x ∂(volumeMeasureOn U), |(centeredPotential m v P.1 c).toFun x| ≤ Kinf)
    (hKvs : ∀ᵐ x ∂(volumeMeasureOn U), |(centeredPotential m vstar P.1 (-c)).toFun x| ≤ Kinf)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hIcc : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (hGη : ∀ x i, |fderiv ℝ η x (basisVec i)| ≤ Gη)
    (hEnergyId :
      (fun x => blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField a x) (Z.eval x)))
        =ᵐ[volumeMeasureOn U]
      (fun x => 2 * vecDot (v.grad x) (matVecMul (symmPart (a x)) (v.grad x))
        + 2 * vecDot (vstar.grad x) (matVecMul (symmPart (a x)) (vstar.grad x))))
    (hCmeas : MeasurableSet C) (hCU : C ⊆ (openCubeSet (originCube d m) : Set (Vec d)))
    (hηC : ∀ᵐ x ∂(volumeMeasureOn C), η x = 1) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      (∫ x in C, blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField a x) (Z.eval x)))
        ≤ Cd * ((Θ * vecNormSq P.1 + vecNormSq P.2)
              * (volume (Function.support η ∩ U)).toReal
            + Θ * Kinf ^ 2 * (∫ x in U, ∑ i, (fderiv ℝ η x (basisVec i)) ^ 2)) := by
  let := isFiniteMeasure_openCubeSet_originCube (d := d) m
  have hUfin : volume (openCubeSet (originCube d m)) ≠ (⊤ : ENNReal) :=
    (volume_openCubeSet_originCube_lt_top m).ne
  have hCfin : volume C ≠ (⊤ : ENNReal) :=
    (lt_of_le_of_lt (measure_mono hCU) (volume_openCubeSet_originCube_lt_top m)).ne
  set M2 := Θ * vecNormSq P.1 + vecNormSq P.2 with hM2
  set vol := (volume (Function.support η ∩ U)).toReal with hvoldef
  set IG := ∫ x in U, ∑ i, (fderiv ℝ η x (basisVec i)) ^ 2 with hIGdef
  have hΘ0 : 0 ≤ Θ := theta_nonneg_of_isEllipticFieldOn (m := m) hEllO
  have hM20 : 0 ≤ M2 := by
    rw [hM2]; exact add_nonneg (mul_nonneg hΘ0 (vecNormSq_nonneg _)) (vecNormSq_nonneg _)
  -- abbreviation for the centered energy density
  set ced : Vec d → ℝ := fun x =>
    vecDot (v.grad x - (1/2:ℝ)•P.1) (matVecMul (symmPart (a x)) (v.grad x - (1/2:ℝ)•P.1))
      + vecDot (vstar.grad x - (1/2:ℝ)•P.1) (matVecMul (symmPart (a x)) (vstar.grad x - (1/2:ℝ)•P.1))
    with hced
  set gEd : Vec d → ℝ := fun x =>
    2 * vecDot (v.grad x) (matVecMul (symmPart (a x)) (v.grad x))
      + 2 * vecDot (vstar.grad x) (matVecMul (symmPart (a x)) (vstar.grad x)) with hgEd
  -- L² integrability facts on `U`
  have hVL2 : MemVectorL2 U (fun x => v.grad x - (1/2:ℝ)•P.1) := memVectorL2_centeredGrad v P
  have hVsL2 : MemVectorL2 U (fun x => vstar.grad x - (1/2:ℝ)•P.1) :=
    memVectorL2_centeredGrad vstar P
  have hced_int : IntegrableOn ced U := by
    refine (integrableOn_vecDot_of_memVectorL2 hVL2
      (memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEllO hVL2)).add
      (integrableOn_vecDot_of_memVectorL2 hVsL2
        (memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEllO hVsL2))
  have hgEd_int : IntegrableOn gEd U := by
    refine (Integrable.const_mul (integrableOn_vecDot_of_memVectorL2 v.grad_memVectorL2
        (memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEllO v.grad_memVectorL2)) 2).add
      (Integrable.const_mul (integrableOn_vecDot_of_memVectorL2 vstar.grad_memVectorL2
        (memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEllO vstar.grad_memVectorL2)) 2)
  have hbnd_int : IntegrableOn (fun x => 4 * ced x + 2 * M2) U :=
    (hced_int.const_mul 4).add (integrableOn_const hUfin)
  -- Step 1: block energy = grad energy on `C`
  have hstep1 : (∫ x in C, blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField a x) (Z.eval x)))
      = ∫ x in C, gEd x := by
    refine integral_congr_ae ?_
    exact hEnergyId.filter_mono (ae_mono (Measure.restrict_mono hCU le_rfl))
  -- Step 2: grad energy ≤ 4·ced + 2M²  a.e. on `C`
  have hstep2 : (∫ x in C, gEd x) ≤ ∫ x in C, (4 * ced x + 2 * M2) := by
    refine setIntegral_mono_ae_restrict (hgEd_int.mono_set hCU) (hbnd_int.mono_set hCU) ?_
    have hmem : ∀ᵐ x ∂(volumeMeasureOn C), x ∈ (openCubeSet (originCube d m) : Set (Vec d)) :=
      (ae_restrict_mem hCmeas).mono (fun x hx => hCU hx)
    filter_upwards [hmem] with x hx
    have hA : IsThetaElliptic Θ (a x) := hEllO.2 x hx
    have h1 := two_symmPart_grad_le hA (v.grad x) P.1
    have h2 := two_symmPart_grad_le hA (vstar.grad x) P.1
    have hup : Θ * vecNormSq P.1 ≤ M2 := by
      rw [hM2]; nlinarith [vecNormSq_nonneg P.2]
    simp only [hgEd, hced]
    nlinarith [h1, h2, hup]
  -- Step 3: `∫_C (4ced + 2M²) = 4·∫_C ced + 2M²·|C|`
  have hcst : (∫ _x in C, (2 * M2 : ℝ)) = 2 * M2 * (volume C).toReal := by
    rw [setIntegral_const, smul_eq_mul, mul_comm]; rfl
  have hstep3 : (∫ x in C, (4 * ced x + 2 * M2))
      = 4 * (∫ x in C, ced x) + 2 * M2 * (volume C).toReal := by
    rw [integral_add ((hced_int.mono_set hCU).const_mul 4) (integrableOn_const hCfin),
      integral_const_mul, hcst]
  -- Step 4: `∫_C ced = ∫_C energyIntegrand ≤ 𝓔`
  have hcedC : (∫ x in C, ced x) = ∫ x in C, energyIntegrand a v vstar P η x := by
    refine integral_congr_ae ?_
    filter_upwards [hηC] with x hx
    simp only [hced, energyIntegrand, sqCutoff_apply, hx]; ring
  have hEnonneg : 0 ≤ᵐ[volumeMeasureOn U] energyIntegrand a v vstar P η := by
    have hmem : ∀ᵐ x ∂(volumeMeasureOn U), x ∈ (openCubeSet (originCube d m) : Set (Vec d)) :=
      ae_restrict_mem (measurableSet_openCubeSet _)
    filter_upwards [hmem] with x hx
    have hA : IsThetaElliptic Θ (a x) := hEllO.2 x hx
    have hnn1 := vecDot_matVecMul_symmPart_nonneg hA (v.grad x - (1/2:ℝ)•P.1)
    have hnn2 := vecDot_matVecMul_symmPart_nonneg hA (vstar.grad x - (1/2:ℝ)•P.1)
    have hη2 := sqCutoff_nonneg η x
    simp only [energyIntegrand]
    exact mul_nonneg hη2 (add_nonneg hnn1 hnn2)
  have hie : IntegrableOn (energyIntegrand a v vstar P η) U :=
    integrableOn_energyIntegrand hEllO hη hIcc
  have hcedle : (∫ x in C, ced x) ≤ ∫ x in U, energyIntegrand a v vstar P η x := by
    rw [hcedC]
    exact setIntegral_mono_set hie hEnonneg (LE.le.eventuallyLE hCU)
  -- T1 bound on `𝓔`
  obtain ⟨Cd1, hCd1, hT1⟩ :=
    centered_local_block_energy (m := m) (c := c) hEllO hWeak hTrace hKv hKvs hη hIcc hGη
  have hEeq : (∫ x in U, (η x) ^ 2
        * (vecDot ((centeredPotential m v P.1 c).grad x)
              (matVecMul (symmPart (a x)) ((centeredPotential m v P.1 c).grad x))
          + vecDot ((centeredPotential m vstar P.1 (-c)).grad x)
              (matVecMul (symmPart (a x)) ((centeredPotential m vstar P.1 (-c)).grad x))))
      = ∫ x in U, energyIntegrand a v vstar P η x := by
    refine setIntegral_congr_fun (measurableSet_openCubeSet _) (fun x _ => ?_)
    simp only [energyIntegrand, centeredPotential_grad, sqCutoff_apply]
  rw [hEeq] at hT1
  -- volume of `C`
  have hvolC : (volume C).toReal ≤ vol := by
    rw [hvoldef]
    have hsub : ∀ᵐ x ∂volume, x ∈ C →
        x ∈ (Function.support η ∩ (openCubeSet (originCube d m)) : Set (Vec d)) := by
      have hη1 : ∀ᵐ x ∂volume, x ∈ C → η x = 1 := by
        rw [← ae_restrict_iff' hCmeas]; exact hηC
      filter_upwards [hη1] with x hx hxC
      refine ⟨?_, hCU hxC⟩
      rw [Function.mem_support, hx hxC]; norm_num
    have hSUfin : volume (Function.support η ∩ (openCubeSet (originCube d m) : Set (Vec d)))
        ≠ (⊤ : ENNReal) :=
      (lt_of_le_of_lt (measure_mono Set.inter_subset_right)
        (volume_openCubeSet_originCube_lt_top m)).ne
    exact ENNReal.toReal_mono hSUfin (measure_mono_ae hsub)
  -- assemble
  refine ⟨4 * Cd1 + 2, by linarith [hCd1], ?_⟩
  have hIG0 : 0 ≤ IG := by
    rw [hIGdef]
    refine setIntegral_nonneg (measurableSet_openCubeSet _) (fun x _ => ?_)
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hΘKIG : 0 ≤ Θ * Kinf ^ 2 * IG := mul_nonneg (mul_nonneg hΘ0 (sq_nonneg _)) hIG0
  have hvol0 : 0 ≤ vol := by rw [hvoldef]; exact ENNReal.toReal_nonneg
  have hMvol0 : 0 ≤ M2 * vol := mul_nonneg hM20 hvol0
  have hMvolC : 2 * M2 * (volume C).toReal ≤ 2 * M2 * vol :=
    mul_le_mul_of_nonneg_left hvolC (by linarith [hM20])
  have hfinal : (∫ x in C, blockVecDot (Z.eval x)
      (blockMatVecMul (blockCoeffField a x) (Z.eval x)))
      ≤ 4 * (∫ x in U, energyIntegrand a v vstar P η x) + 2 * M2 * (volume C).toReal := by
    rw [hstep1]
    calc (∫ x in C, gEd x) ≤ ∫ x in C, (4 * ced x + 2 * M2) := hstep2
      _ = 4 * (∫ x in C, ced x) + 2 * M2 * (volume C).toReal := hstep3
      _ ≤ 4 * (∫ x in U, energyIntegrand a v vstar P η x) + 2 * M2 * (volume C).toReal := by
          have := mul_le_mul_of_nonneg_left hcedle (by norm_num : (0:ℝ) ≤ 4)
          linarith [this]
  nlinarith [hfinal, hT1, hMvolC, hΘKIG, hMvol0, hCd1]

/-! ## T1 and T2 — explicit-numeral (uniform-constant) restatements -/

omit [NeZero d] in
/-- **T1 with the explicit numeral `128`.**  The witness of
`centered_local_block_energy` is the fixed dimensional constant `128`; this is the
same bound stated with that literal so the consumer can see a field-independent
constant. -/
theorem centered_local_block_energy_num {a : CoeffField d} {Θ : ℝ}
    {v vstar : H1Function U} {P : BlockVec d} {η : Vec d → ℝ} {Gη c Kinf : ℝ}
    (hEllO : IsEllipticFieldOn 1 Θ U a)
    (hWeak : CoupledWeakForm a U P.2 v vstar)
    (hTrace : MemH10 U (fun x => v.toFun x + vstar.toFun x - vecDot P.1 x))
    (hKv : ∀ᵐ x ∂(volumeMeasureOn U), |(centeredPotential m v P.1 c).toFun x| ≤ Kinf)
    (hKvs : ∀ᵐ x ∂(volumeMeasureOn U), |(centeredPotential m vstar P.1 (-c)).toFun x| ≤ Kinf)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hIcc : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (hGη : ∀ x i, |fderiv ℝ η x (basisVec i)| ≤ Gη) :
    (∫ x in U, (η x) ^ 2
        * (vecDot ((centeredPotential m v P.1 c).grad x)
              (matVecMul (symmPart (a x)) ((centeredPotential m v P.1 c).grad x))
          + vecDot ((centeredPotential m vstar P.1 (-c)).grad x)
              (matVecMul (symmPart (a x)) ((centeredPotential m vstar P.1 (-c)).grad x))))
      ≤ 128 * ((Θ * vecNormSq P.1 + vecNormSq P.2)
            * (volume (Function.support η ∩ U)).toReal
          + Θ * Kinf ^ 2 * (∫ x in U, ∑ i, (fderiv ℝ η x (basisVec i)) ^ 2)) := by
  have hEeq : (∫ x in U, (η x) ^ 2
        * (vecDot ((centeredPotential m v P.1 c).grad x)
              (matVecMul (symmPart (a x)) ((centeredPotential m v P.1 c).grad x))
          + vecDot ((centeredPotential m vstar P.1 (-c)).grad x)
              (matVecMul (symmPart (a x)) ((centeredPotential m vstar P.1 (-c)).grad x))))
      = ∫ x in U, energyIntegrand a v vstar P η x := by
    refine setIntegral_congr_fun (measurableSet_openCubeSet _) (fun x _ => ?_)
    simp only [energyIntegrand, centeredPotential_grad, sqCutoff_apply]
  have hIGeq : (∫ x in U, ∑ i, (fderiv ℝ η x (basisVec i)) ^ 2)
      = ∫ x in U, vecNormSq (fun i => fderiv ℝ η x (basisVec i)) := by
    refine setIntegral_congr_fun (measurableSet_openCubeSet _) (fun x _ => ?_)
    exact gradEtaSq_eq_vecNormSq x
  rw [hEeq, hIGeq]
  set 𝓔 := ∫ x in U, energyIntegrand a v vstar P η x with h𝓔
  set Isq := ∫ x in U, sqCutoff η x with hIsq
  set IG := ∫ x in U, vecNormSq (fun i => fderiv ℝ η x (basisVec i)) with hIG
  set M2 := Θ * vecNormSq P.1 + vecNormSq P.2 with hM2
  have hΘ0 : 0 ≤ Θ := theta_nonneg_of_isEllipticFieldOn (m := m) hEllO
  have hM20 : 0 ≤ M2 := by
    rw [hM2]; exact add_nonneg (mul_nonneg hΘ0 (vecNormSq_nonneg _)) (vecNormSq_nonneg _)
  have hvol0 : 0 ≤ (volume (Function.support η ∩ U)).toReal := ENNReal.toReal_nonneg
  have hIG0 : 0 ≤ IG := by
    rw [hIG]
    exact setIntegral_nonneg (measurableSet_openCubeSet _) (fun x _ => vecNormSq_nonneg _)
  have hIsqvol : Isq ≤ (volume (Function.support η ∩ U)).toReal := by
    rw [hIsq]; exact setIntegral_sqCutoff_le hη hIcc
  have hsplit : 𝓔 = (∫ x in U, bulkIntegrand a v vstar P η x)
      + (∫ x in U, cutoffIntegrand a v vstar P c η x) := by
    rw [h𝓔]; exact energyIntegral_eq_bulk_add_cutoff hEllO hη hIcc hGη hWeak hTrace
  have hbulk : (∫ x in U, bulkIntegrand a v vstar P η x) ≤ 5 * M2 * Isq + (1/8) * 𝓔 := by
    rw [hM2, hIsq, h𝓔]; exact setIntegral_bulkIntegrand_le hEllO hη hIcc
  have hcut : (∫ x in U, cutoffIntegrand a v vstar P c η x)
      ≤ (1/16) * 𝓔 + 2 * M2 * Isq + 67 * Θ * Kinf ^ 2 * IG := by
    rw [hM2, hIsq, h𝓔, hIG]; exact setIntegral_cutoffIntegrand_le hEllO hη hIcc hGη hKv hKvs
  have hKinf2 : 0 ≤ Kinf ^ 2 := sq_nonneg _
  have hMsqvol : 5 * M2 * Isq ≤ 5 * M2 * (volume (Function.support η ∩ U)).toReal :=
    mul_le_mul_of_nonneg_left hIsqvol (by positivity)
  have hMsqvol2 : 2 * M2 * Isq ≤ 2 * M2 * (volume (Function.support η ∩ U)).toReal :=
    mul_le_mul_of_nonneg_left hIsqvol (by positivity)
  have hΘKIG : 0 ≤ Θ * Kinf ^ 2 * IG :=
    mul_nonneg (mul_nonneg hΘ0 hKinf2) hIG0
  have hMvol0 : 0 ≤ M2 * (volume (Function.support η ∩ U)).toReal :=
    mul_nonneg hM20 hvol0
  nlinarith [hsplit, hbulk, hcut, hMsqvol, hMsqvol2, hΘKIG, hMvol0]

omit [NeZero d] in
/-- **T2 with the explicit numeral `514 = 4·128 + 2`.**  The uniform-constant
restatement of `local_block_energy`: its witness is the field-independent
dimensional constant `514`, exposed here as a literal so the per-core energy
bound can be made uniform over realizations. -/
theorem local_block_energy_uniform {a : CoeffField d} {Θ : ℝ}
    {v vstar : H1Function U} {P : BlockVec d} {η : Vec d → ℝ} {Gη c Kinf : ℝ}
    {Z : BlockState d} {C : Set (Vec d)}
    (hEllO : IsEllipticFieldOn 1 Θ U a)
    (hWeak : CoupledWeakForm a U P.2 v vstar)
    (hTrace : MemH10 U (fun x => v.toFun x + vstar.toFun x - vecDot P.1 x))
    (hKv : ∀ᵐ x ∂(volumeMeasureOn U), |(centeredPotential m v P.1 c).toFun x| ≤ Kinf)
    (hKvs : ∀ᵐ x ∂(volumeMeasureOn U), |(centeredPotential m vstar P.1 (-c)).toFun x| ≤ Kinf)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hIcc : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (hGη : ∀ x i, |fderiv ℝ η x (basisVec i)| ≤ Gη)
    (hEnergyId :
      (fun x => blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField a x) (Z.eval x)))
        =ᵐ[volumeMeasureOn U]
      (fun x => 2 * vecDot (v.grad x) (matVecMul (symmPart (a x)) (v.grad x))
        + 2 * vecDot (vstar.grad x) (matVecMul (symmPart (a x)) (vstar.grad x))))
    (hCmeas : MeasurableSet C) (hCU : C ⊆ (openCubeSet (originCube d m) : Set (Vec d)))
    (hηC : ∀ᵐ x ∂(volumeMeasureOn C), η x = 1) :
    (∫ x in C, blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField a x) (Z.eval x)))
      ≤ 514 * ((Θ * vecNormSq P.1 + vecNormSq P.2)
            * (volume (Function.support η ∩ U)).toReal
          + Θ * Kinf ^ 2 * (∫ x in U, ∑ i, (fderiv ℝ η x (basisVec i)) ^ 2)) := by
  let := isFiniteMeasure_openCubeSet_originCube (d := d) m
  have hUfin : volume (openCubeSet (originCube d m)) ≠ (⊤ : ENNReal) :=
    (volume_openCubeSet_originCube_lt_top m).ne
  have hCfin : volume C ≠ (⊤ : ENNReal) :=
    (lt_of_le_of_lt (measure_mono hCU) (volume_openCubeSet_originCube_lt_top m)).ne
  set M2 := Θ * vecNormSq P.1 + vecNormSq P.2 with hM2
  set vol := (volume (Function.support η ∩ U)).toReal with hvoldef
  set IG := ∫ x in U, ∑ i, (fderiv ℝ η x (basisVec i)) ^ 2 with hIGdef
  have hΘ0 : 0 ≤ Θ := theta_nonneg_of_isEllipticFieldOn (m := m) hEllO
  have hM20 : 0 ≤ M2 := by
    rw [hM2]; exact add_nonneg (mul_nonneg hΘ0 (vecNormSq_nonneg _)) (vecNormSq_nonneg _)
  set ced : Vec d → ℝ := fun x =>
    vecDot (v.grad x - (1/2:ℝ)•P.1) (matVecMul (symmPart (a x)) (v.grad x - (1/2:ℝ)•P.1))
      + vecDot (vstar.grad x - (1/2:ℝ)•P.1) (matVecMul (symmPart (a x)) (vstar.grad x - (1/2:ℝ)•P.1))
    with hced
  set gEd : Vec d → ℝ := fun x =>
    2 * vecDot (v.grad x) (matVecMul (symmPart (a x)) (v.grad x))
      + 2 * vecDot (vstar.grad x) (matVecMul (symmPart (a x)) (vstar.grad x)) with hgEd
  have hVL2 : MemVectorL2 U (fun x => v.grad x - (1/2:ℝ)•P.1) := memVectorL2_centeredGrad v P
  have hVsL2 : MemVectorL2 U (fun x => vstar.grad x - (1/2:ℝ)•P.1) :=
    memVectorL2_centeredGrad vstar P
  have hced_int : IntegrableOn ced U := by
    refine (integrableOn_vecDot_of_memVectorL2 hVL2
      (memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEllO hVL2)).add
      (integrableOn_vecDot_of_memVectorL2 hVsL2
        (memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEllO hVsL2))
  have hgEd_int : IntegrableOn gEd U := by
    refine (Integrable.const_mul (integrableOn_vecDot_of_memVectorL2 v.grad_memVectorL2
        (memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEllO v.grad_memVectorL2)) 2).add
      (Integrable.const_mul (integrableOn_vecDot_of_memVectorL2 vstar.grad_memVectorL2
        (memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEllO vstar.grad_memVectorL2)) 2)
  have hbnd_int : IntegrableOn (fun x => 4 * ced x + 2 * M2) U :=
    (hced_int.const_mul 4).add (integrableOn_const hUfin)
  have hstep1 : (∫ x in C, blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField a x) (Z.eval x)))
      = ∫ x in C, gEd x := by
    refine integral_congr_ae ?_
    exact hEnergyId.filter_mono (ae_mono (Measure.restrict_mono hCU le_rfl))
  have hstep2 : (∫ x in C, gEd x) ≤ ∫ x in C, (4 * ced x + 2 * M2) := by
    refine setIntegral_mono_ae_restrict (hgEd_int.mono_set hCU) (hbnd_int.mono_set hCU) ?_
    have hmem : ∀ᵐ x ∂(volumeMeasureOn C), x ∈ (openCubeSet (originCube d m) : Set (Vec d)) :=
      (ae_restrict_mem hCmeas).mono (fun x hx => hCU hx)
    filter_upwards [hmem] with x hx
    have hA : IsThetaElliptic Θ (a x) := hEllO.2 x hx
    have h1 := two_symmPart_grad_le hA (v.grad x) P.1
    have h2 := two_symmPart_grad_le hA (vstar.grad x) P.1
    have hup : Θ * vecNormSq P.1 ≤ M2 := by
      rw [hM2]; nlinarith [vecNormSq_nonneg P.2]
    simp only [hgEd, hced]
    nlinarith [h1, h2, hup]
  have hcst : (∫ _x in C, (2 * M2 : ℝ)) = 2 * M2 * (volume C).toReal := by
    rw [setIntegral_const, smul_eq_mul, mul_comm]; rfl
  have hstep3 : (∫ x in C, (4 * ced x + 2 * M2))
      = 4 * (∫ x in C, ced x) + 2 * M2 * (volume C).toReal := by
    rw [integral_add ((hced_int.mono_set hCU).const_mul 4) (integrableOn_const hCfin),
      integral_const_mul, hcst]
  have hcedC : (∫ x in C, ced x) = ∫ x in C, energyIntegrand a v vstar P η x := by
    refine integral_congr_ae ?_
    filter_upwards [hηC] with x hx
    simp only [hced, energyIntegrand, sqCutoff_apply, hx]; ring
  have hEnonneg : 0 ≤ᵐ[volumeMeasureOn U] energyIntegrand a v vstar P η := by
    have hmem : ∀ᵐ x ∂(volumeMeasureOn U), x ∈ (openCubeSet (originCube d m) : Set (Vec d)) :=
      ae_restrict_mem (measurableSet_openCubeSet _)
    filter_upwards [hmem] with x hx
    have hA : IsThetaElliptic Θ (a x) := hEllO.2 x hx
    have hnn1 := vecDot_matVecMul_symmPart_nonneg hA (v.grad x - (1/2:ℝ)•P.1)
    have hnn2 := vecDot_matVecMul_symmPart_nonneg hA (vstar.grad x - (1/2:ℝ)•P.1)
    have hη2 := sqCutoff_nonneg η x
    simp only [energyIntegrand]
    exact mul_nonneg hη2 (add_nonneg hnn1 hnn2)
  have hie : IntegrableOn (energyIntegrand a v vstar P η) U :=
    integrableOn_energyIntegrand hEllO hη hIcc
  have hcedle : (∫ x in C, ced x) ≤ ∫ x in U, energyIntegrand a v vstar P η x := by
    rw [hcedC]
    exact setIntegral_mono_set hie hEnonneg (LE.le.eventuallyLE hCU)
  have hT1 :=
    centered_local_block_energy_num (m := m) (c := c) hEllO hWeak hTrace hKv hKvs hη hIcc hGη
  have hEeq : (∫ x in U, (η x) ^ 2
        * (vecDot ((centeredPotential m v P.1 c).grad x)
              (matVecMul (symmPart (a x)) ((centeredPotential m v P.1 c).grad x))
          + vecDot ((centeredPotential m vstar P.1 (-c)).grad x)
              (matVecMul (symmPart (a x)) ((centeredPotential m vstar P.1 (-c)).grad x))))
      = ∫ x in U, energyIntegrand a v vstar P η x := by
    refine setIntegral_congr_fun (measurableSet_openCubeSet _) (fun x _ => ?_)
    simp only [energyIntegrand, centeredPotential_grad, sqCutoff_apply]
  rw [hEeq] at hT1
  have hvolC : (volume C).toReal ≤ vol := by
    rw [hvoldef]
    have hsub : ∀ᵐ x ∂volume, x ∈ C →
        x ∈ (Function.support η ∩ (openCubeSet (originCube d m)) : Set (Vec d)) := by
      have hη1 : ∀ᵐ x ∂volume, x ∈ C → η x = 1 := by
        rw [← ae_restrict_iff' hCmeas]; exact hηC
      filter_upwards [hη1] with x hx hxC
      refine ⟨?_, hCU hxC⟩
      rw [Function.mem_support, hx hxC]; norm_num
    have hSUfin : volume (Function.support η ∩ (openCubeSet (originCube d m) : Set (Vec d)))
        ≠ (⊤ : ENNReal) :=
      (lt_of_le_of_lt (measure_mono Set.inter_subset_right)
        (volume_openCubeSet_originCube_lt_top m)).ne
    exact ENNReal.toReal_mono hSUfin (measure_mono_ae hsub)
  have hIG0 : 0 ≤ IG := by
    rw [hIGdef]
    refine setIntegral_nonneg (measurableSet_openCubeSet _) (fun x _ => ?_)
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hΘKIG : 0 ≤ Θ * Kinf ^ 2 * IG := mul_nonneg (mul_nonneg hΘ0 (sq_nonneg _)) hIG0
  have hvol0 : 0 ≤ vol := by rw [hvoldef]; exact ENNReal.toReal_nonneg
  have hMvol0 : 0 ≤ M2 * vol := mul_nonneg hM20 hvol0
  have hMvolC : 2 * M2 * (volume C).toReal ≤ 2 * M2 * vol :=
    mul_le_mul_of_nonneg_left hvolC (by linarith [hM20])
  have hfinal : (∫ x in C, blockVecDot (Z.eval x)
      (blockMatVecMul (blockCoeffField a x) (Z.eval x)))
      ≤ 4 * (∫ x in U, energyIntegrand a v vstar P η x) + 2 * M2 * (volume C).toReal := by
    rw [hstep1]
    calc (∫ x in C, gEd x) ≤ ∫ x in C, (4 * ced x + 2 * M2) := hstep2
      _ = 4 * (∫ x in C, ced x) + 2 * M2 * (volume C).toReal := hstep3
      _ ≤ 4 * (∫ x in U, energyIntegrand a v vstar P η x) + 2 * M2 * (volume C).toReal := by
          have := mul_le_mul_of_nonneg_left hcedle (by norm_num : (0:ℝ) ≤ 4)
          linarith [this]
  nlinarith [hfinal, hT1, hMvolC, hΘKIG, hMvol0]

end

end Homogenization
