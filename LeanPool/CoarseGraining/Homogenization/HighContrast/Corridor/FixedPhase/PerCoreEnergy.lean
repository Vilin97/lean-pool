/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.CutoffData
public import LeanPool.CoarseGraining.Homogenization.HighContrast.Coupled.LocalEnergy
public import LeanPool.CoarseGraining.Homogenization.HighContrast.Coupled.Stampacchia
public import LeanPool.CoarseGraining.Homogenization.HighContrast.Coupled.Representation
public import LeanPool.CoarseGraining.Homogenization.Geometry.OriginCubeMeasureBridge

/-!
# The per-core minimizer energy bound

For a coefficient field `c` that is `(1, Θ)`-elliptic on the closed cube
`U := cubeSet (originCube d m)`, we produce a single block minimizer `Z`
for `(c, P)` together with, for every core `coreBox ℓ σ k` meeting a finite index
set `K`, the per-core energy bound of `e.fixed.phase.max.energy`:

`∫_{coreBox ℓ σ k ∩ U} Z·𝐁(c)Z ≤ Cd · Θ · (3^m)² · ℓ^{d−2} · (Θ|p|² + |q|²)`.

The proof follows §4.3: the coupled representation (`exists_coupledRepresentation`)
supplies `Z, v, v*`; the coupled Stampacchia estimate (`coupled_stampacchia`)
supplies the sup-norm `K∞ = C_d·3^m·√M²`; the per-core smooth cutoff
(`CutoffData`) plus `local_block_energy` (T2) supplies the energy bound, whose two
terms `M²·|supp η ∩ U|` and `Θ·K∞²·∫_U|∇η|²` are collapsed by the uniform cutoff
estimates `(3ℓ)^d` and `d·(16/ℓ)²·(3ℓ)^d` and the power identity
`ℓ^d = ℓ^{d−2}·ℓ²`.  The energy is stated on the closed cube by transporting the
open-cube integrals through the null-boundary bridge
`cubeSet_originCube_ae_eq_openCubeSet`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators

namespace Homogenization

variable {d : ℕ}

/-! ## The numeric combination of the two `local_block_energy` terms -/

private theorem perCore_numeric {d : ℕ} (hd : 3 ≤ d)
    {Θ ℓ R Msq CdT CdS suppvol gradint Kinf : ℝ}
    (hΘ : 1 ≤ Θ) (hℓ4 : 4 ≤ ℓ) (hℓR : ℓ ≤ R) (hMsq : 0 ≤ Msq)
    (hCdT : 0 ≤ CdT)
    (hsupp : suppvol ≤ (3 * ℓ) ^ d)
    (hgrad : gradint ≤ (d : ℝ) * (16 / ℓ) ^ 2 * (3 * ℓ) ^ d)
    (hKinf : Kinf = CdS * R * Real.sqrt Msq) :
    CdT * (Msq * suppvol + Θ * Kinf ^ 2 * gradint)
      ≤ (CdT * 3 ^ d + CdT * CdS ^ 2 * (d : ℝ) * 256 * 3 ^ d) * Θ * R ^ 2 * ℓ ^ (d - 2) * Msq := by
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have he : d = (d - 2) + 2 := by omega
  set e := d - 2 with hedef
  have hℓd : ℓ ^ d = ℓ ^ e * ℓ ^ 2 := by rw [he, pow_add]
  have h3ℓd : (3 * ℓ) ^ d = 3 ^ d * ℓ ^ d := by rw [mul_pow]
  have hKsq : Kinf ^ 2 = CdS ^ 2 * R ^ 2 * Msq := by
    rw [hKinf, mul_pow, mul_pow, Real.sq_sqrt hMsq]
  have h16 : (16 / ℓ) ^ 2 * ℓ ^ 2 = 256 := by field_simp; norm_num
  have hkey : (16 / ℓ) ^ 2 * ℓ ^ d = 256 * ℓ ^ e := by
    rw [hℓd, show (16 / ℓ) ^ 2 * (ℓ ^ e * ℓ ^ 2) = ((16 / ℓ) ^ 2 * ℓ ^ 2) * ℓ ^ e from by ring, h16]
  have hℓe0 : 0 ≤ ℓ ^ e := by positivity
  have h3d0 : (0 : ℝ) ≤ 3 ^ d := by positivity
  have hℓ2R2 : ℓ ^ 2 ≤ R ^ 2 := by nlinarith [hℓR, hℓ0.le]
  have hT1 : CdT * (Msq * suppvol) ≤ (CdT * 3 ^ d) * Θ * R ^ 2 * ℓ ^ e * Msq := by
    have h1 : Msq * suppvol ≤ Msq * (3 ^ d * (ℓ ^ e * ℓ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hMsq
      calc suppvol ≤ (3 * ℓ) ^ d := hsupp
        _ = 3 ^ d * ℓ ^ d := h3ℓd
        _ = 3 ^ d * (ℓ ^ e * ℓ ^ 2) := by rw [hℓd]
    calc CdT * (Msq * suppvol) ≤ CdT * (Msq * (3 ^ d * (ℓ ^ e * ℓ ^ 2))) :=
          mul_le_mul_of_nonneg_left h1 hCdT
      _ ≤ CdT * (Msq * (3 ^ d * (ℓ ^ e * R ^ 2))) := by
          apply mul_le_mul_of_nonneg_left _ hCdT
          apply mul_le_mul_of_nonneg_left _ hMsq
          apply mul_le_mul_of_nonneg_left _ h3d0
          exact mul_le_mul_of_nonneg_left hℓ2R2 hℓe0
      _ ≤ CdT * (Msq * (3 ^ d * (ℓ ^ e * R ^ 2))) * Θ := by
          nlinarith [mul_nonneg (mul_nonneg hCdT hMsq)
            (mul_nonneg h3d0 (mul_nonneg hℓe0 (by positivity : (0:ℝ) ≤ R ^ 2))), hΘ]
      _ = (CdT * 3 ^ d) * Θ * R ^ 2 * ℓ ^ e * Msq := by ring
  have hT2 : CdT * (Θ * Kinf ^ 2 * gradint)
      ≤ (CdT * CdS ^ 2 * (d : ℝ) * 256 * 3 ^ d) * Θ * R ^ 2 * ℓ ^ e * Msq := by
    have hgbound : gradint ≤ (d : ℝ) * 256 * 3 ^ d * ℓ ^ e := by
      calc gradint ≤ (d : ℝ) * (16 / ℓ) ^ 2 * (3 * ℓ) ^ d := hgrad
        _ = (d : ℝ) * ((16 / ℓ) ^ 2 * (3 ^ d * ℓ ^ d)) := by rw [h3ℓd]; ring
        _ = (d : ℝ) * (3 ^ d * ((16 / ℓ) ^ 2 * ℓ ^ d)) := by ring
        _ = (d : ℝ) * (3 ^ d * (256 * ℓ ^ e)) := by rw [hkey]
        _ = (d : ℝ) * 256 * 3 ^ d * ℓ ^ e := by ring
    have hΘK0 : 0 ≤ Θ * Kinf ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    calc CdT * (Θ * Kinf ^ 2 * gradint)
        ≤ CdT * (Θ * Kinf ^ 2 * ((d : ℝ) * 256 * 3 ^ d * ℓ ^ e)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgbound hΘK0) hCdT
      _ = CdT * (Θ * (CdS ^ 2 * R ^ 2 * Msq) * ((d : ℝ) * 256 * 3 ^ d * ℓ ^ e)) := by rw [hKsq]
      _ = (CdT * CdS ^ 2 * (d : ℝ) * 256 * 3 ^ d) * Θ * R ^ 2 * ℓ ^ e * Msq := by ring
  calc CdT * (Msq * suppvol + Θ * Kinf ^ 2 * gradint)
      = CdT * (Msq * suppvol) + CdT * (Θ * Kinf ^ 2 * gradint) := by ring
    _ ≤ (CdT * 3 ^ d) * Θ * R ^ 2 * ℓ ^ e * Msq
          + (CdT * CdS ^ 2 * (d : ℝ) * 256 * 3 ^ d) * Θ * R ^ 2 * ℓ ^ e * Msq :=
        add_le_add hT1 hT2
    _ = (CdT * 3 ^ d + CdT * CdS ^ 2 * (d : ℝ) * 256 * 3 ^ d) * Θ * R ^ 2 * ℓ ^ e * Msq := by ring

/-! ## The null-boundary energy bridge -/

/-- Set integrals over `coreBox ∩ cubeSet` and `coreBox ∩ openCubeSet` coincide:
the two cubes differ only by the null boundary. -/
theorem setIntegral_coreBox_inter_cubeSet_eq_openCubeSet {m : ℤ}
    (ℓ : ℝ) (σ : Vec d) (k : Fin d → ℤ) (f : Vec d → ℝ) :
    (∫ x in coreBox ℓ σ k ∩ cubeSet (originCube d m), f x)
      = ∫ x in coreBox ℓ σ k ∩ openCubeSet (originCube d m), f x := by
  refine setIntegral_congr_set ?_
  exact (Filter.EventuallyEq.refl _ _).inter (cubeSet_originCube_ae_eq_openCubeSet (d := d) m)


/-! ## The per-core minimizer energy bound -/

/-- **Per-core energy bound (`e.fixed.phase.max.energy`).**  For `c` elliptic on
the closed cube there is a block minimizer `Z` for `(c, P)` and a
dimensional constant `Cd ≥ 0` such that every core meeting `K` has normalized
energy `≤ Cd · Θ · (3^m)² · ℓ^{d−2} · (Θ|p|² + |q|²)`. -/
theorem exists_perCore_minimizer_energy_le [NeZero d] (hd : 3 ≤ d) {m : ℤ} {Θ : ℝ}
    (hΘ : 1 ≤ Θ) {ℓ : ℝ} (hℓ4 : 4 ≤ ℓ) (hℓL : ℓ ≤ (3 : ℝ) ^ m) (σ : Vec d) (P : BlockVec d)
    {c : CoeffField d} (hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) c)
    (K : Finset (Fin d → ℤ)) :
    ∃ (Z : BlockState d) (Cd : ℝ), 0 ≤ Cd ∧
      IsBlockMuAdmissible (cubeSet (originCube d m)) P Z ∧
      BlockResponseSpace c (cubeSet (originCube d m)) Z ∧
      Mu (cubeSet (originCube d m)) P c = blockEnergyAverage (cubeSet (originCube d m)) c Z ∧
      ∀ k ∈ K,
        (∫ x in coreBox ℓ σ k ∩ cubeSet (originCube d m),
            blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField c x) (Z.eval x)))
          ≤ Cd * Θ * ((3 : ℝ) ^ m) ^ 2 * ℓ ^ (d - 2) * (Θ * vecNormSq P.1 + vecNormSq P.2) := by
  classical
  let := isFiniteMeasure_openCubeSet_originCube (d := d) m
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hΘ0 : (0 : ℝ) < Θ := lt_of_lt_of_le one_pos hΘ
  set R : ℝ := (3 : ℝ) ^ m with hRdef
  set Msq : ℝ := Θ * vecNormSq P.1 + vecNormSq P.2 with hMsqdef
  have hMsq0 : (0 : ℝ) ≤ Msq :=
    add_nonneg (mul_nonneg hΘ0.le (vecNormSq_nonneg _)) (vecNormSq_nonneg _)
  have hUmeasO : MeasurableSet (openCubeSet (originCube d m)) := measurableSet_openCubeSet _
  have hEllO : IsEllipticFieldOn 1 Θ (openCubeSet (originCube d m)) c :=
    hEll.mono hUmeasO (openCubeSet_subset_cubeSet (originCube d m))
  -- the coupled representation
  obtain ⟨Z, v, vstar, hAdmO, hEngO, hRespO, hTrace, _hgp, _hgf, hWeak, hEnergyId⟩ :=
    exists_coupledRepresentation hEll P
  -- the coupled Stampacchia estimate
  obtain ⟨CdS, cval, hCdS0, hvb, hvsb⟩ := coupled_stampacchia hd hEll hWeak hTrace
  set Kinf : ℝ := CdS * R * Real.sqrt Msq with hKinfdef
  -- the two sup-norm bounds in `centeredPotential` form
  have hKv : ∀ᵐ x ∂(volumeMeasureOn (openCubeSet (originCube d m))),
      |(centeredPotential m v P.1 cval).toFun x| ≤ Kinf := by
    filter_upwards [hvb] with x hx
    rw [centeredPotential_toFun]; exact hx
  have hKvs : ∀ᵐ x ∂(volumeMeasureOn (openCubeSet (originCube d m))),
      |(centeredPotential m vstar P.1 (-cval)).toFun x| ≤ Kinf := by
    filter_upwards [hvsb] with x hx
    rw [centeredPotential_toFun]
    simpa using hx
  set W : ℝ := Θ * R ^ 2 * ℓ ^ (d - 2) * Msq with hWdef
  have hW0 : (0 : ℝ) ≤ W := by
    rw [hWdef]; positivity
  -- per-core existential bound
  have hperk : ∀ k : Fin d → ℤ, ∃ e : ℝ, 0 ≤ e ∧
      (∫ x in coreBox ℓ σ k ∩ cubeSet (originCube d m),
          blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField c x) (Z.eval x)))
        ≤ e * W := by
    intro k
    set C : Set (Vec d) := coreBox ℓ σ k ∩ openCubeSet (originCube d m) with hCdef
    have hCmeas : MeasurableSet C :=
      (measurableSet_coreBox ℓ σ k).inter hUmeasO
    have hCU : C ⊆ (openCubeSet (originCube d m) : Set (Vec d)) := Set.inter_subset_right
    have hηC : ∀ᵐ x ∂(volumeMeasureOn C), coreCutoff ℓ σ k x = 1 := by
      refine (ae_restrict_iff' hCmeas).2 (Filter.Eventually.of_forall (fun x hx => ?_))
      exact coreCutoff_eq_one_of_mem_coreBox hℓ0 σ k hx.1
    -- T2
    obtain ⟨CdT, hCdT0, hbound⟩ :=
      local_block_energy hEllO hWeak hTrace hKv hKvs (coreCutoff_contDiff ℓ σ k)
        (coreCutoff_mem_Icc ℓ σ k) (fun x i => coreCutoff_deriv_bound hℓ0 σ k x i)
        hEnergyId hCmeas hCU hηC
    -- the two uniform cutoff estimates
    have hsupp : (volume (Function.support (coreCutoff ℓ σ k) ∩
          openCubeSet (originCube d m))).toReal ≤ (3 * ℓ) ^ d :=
      coreCutoff_support_volume_le hℓ4 σ k _
    have hgrad : (∫ x in openCubeSet (originCube d m),
          ∑ i, (fderiv ℝ (coreCutoff ℓ σ k) x (basisVec i)) ^ 2)
        ≤ (d : ℝ) * (16 / ℓ) ^ 2 * (3 * ℓ) ^ d :=
      coreCutoff_sqGrad_integral_le hℓ4 σ k _
    refine ⟨CdT * 3 ^ d + CdT * CdS ^ 2 * (d : ℝ) * 256 * 3 ^ d, by positivity, ?_⟩
    rw [setIntegral_coreBox_inter_cubeSet_eq_openCubeSet]
    calc (∫ x in C, blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField c x) (Z.eval x)))
        ≤ CdT * ((Θ * vecNormSq P.1 + vecNormSq P.2) *
              (volume (Function.support (coreCutoff ℓ σ k) ∩
                openCubeSet (originCube d m))).toReal
            + Θ * Kinf ^ 2 * (∫ x in openCubeSet (originCube d m),
                ∑ i, (fderiv ℝ (coreCutoff ℓ σ k) x (basisVec i)) ^ 2)) := hbound
      _ ≤ (CdT * 3 ^ d + CdT * CdS ^ 2 * (d : ℝ) * 256 * 3 ^ d) * Θ * R ^ 2 * ℓ ^ (d - 2) * Msq :=
          perCore_numeric hd hΘ hℓ4 hℓL hMsq0 hCdT0 hsupp hgrad hKinfdef
      _ = (CdT * 3 ^ d + CdT * CdS ^ 2 * (d : ℝ) * 256 * 3 ^ d) * W := by rw [hWdef]; ring
  choose f hf0 hfb using hperk
  -- uniform constant over the finite `K`
  refine ⟨Z, ∑ k ∈ K, |f k|,
    Finset.sum_nonneg (fun k _ => abs_nonneg _),
    (isBlockMuAdmissible_cubeSet_originCube_iff_openCubeSet).2 hAdmO,
    (blockResponseSpace_cubeSet_originCube_iff_openCubeSet).2 hRespO, ?_, ?_⟩
  · rw [Mu_cubeSet_originCube_eq_openCubeSet (d := d) m P c, hEngO]
    unfold blockEnergyAverage
    exact (volumeAverage_cubeSet_originCube_eq_openCubeSet (d := d) m
      (blockEnergyDensity c Z)).symm
  · intro k hk
    have hfkle : f k ≤ ∑ k' ∈ K, |f k'| :=
      le_trans (le_abs_self _)
        (Finset.single_le_sum (f := fun k' => |f k'|) (fun k' _ => abs_nonneg _) hk)
    calc (∫ x in coreBox ℓ σ k ∩ cubeSet (originCube d m),
            blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField c x) (Z.eval x)))
        ≤ f k * W := hfb k
      _ ≤ (∑ k' ∈ K, |f k'|) * W := mul_le_mul_of_nonneg_right hfkle hW0
      _ = (∑ k' ∈ K, |f k'|) * Θ * ((3 : ℝ) ^ m) ^ 2 * ℓ ^ (d - 2)
            * (Θ * vecNormSq P.1 + vecNormSq P.2) := by rw [hWdef, hRdef, hMsqdef]; ring

/-- **Uniform per-core energy bound.**  The constant-outside form of
`exists_perCore_minimizer_energy_le`: a single dimensional constant `Cd`,
independent of the realization `c` and the core family `K`, bounds every per-core
normalized energy.  Uniformity comes from `coupled_stampacchia_uniform` (single
sup-norm constant `CdS`) and `local_block_energy_uniform` (literal `514`); the
per-core numeric collapse is `perCore_numeric` with `CdT := 514`. -/
theorem exists_perCore_minimizer_energy_le_uniform [NeZero d] (hd : 3 ≤ d) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ {m : ℤ} {Θ : ℝ} (_hΘ : 1 ≤ Θ) {ℓ : ℝ} (_hℓ4 : 4 ≤ ℓ) (_hℓL : ℓ ≤ (3 : ℝ) ^ m)
        (σ : Vec d) (P : BlockVec d) {c : CoeffField d}
        (_hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) c) (K : Finset (Fin d → ℤ)),
      ∃ (Z : BlockState d),
        IsBlockMuAdmissible (cubeSet (originCube d m)) P Z ∧
        BlockResponseSpace c (cubeSet (originCube d m)) Z ∧
        Mu (cubeSet (originCube d m)) P c = blockEnergyAverage (cubeSet (originCube d m)) c Z ∧
        ∀ k ∈ K,
          (∫ x in coreBox ℓ σ k ∩ cubeSet (originCube d m),
              blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField c x) (Z.eval x)))
            ≤ Cd * Θ * ((3 : ℝ) ^ m) ^ 2 * ℓ ^ (d - 2)
                * (Θ * vecNormSq P.1 + vecNormSq P.2) := by
  classical
  obtain ⟨CdS, hCdS0, hstampU⟩ := coupled_stampacchia_uniform hd
  refine ⟨514 * 3 ^ d + 514 * CdS ^ 2 * (d : ℝ) * 256 * 3 ^ d, by positivity, ?_⟩
  intro m Θ hΘ ℓ hℓ4 hℓL σ P c hEll K
  let := isFiniteMeasure_openCubeSet_originCube (d := d) m
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hΘ0 : (0 : ℝ) < Θ := lt_of_lt_of_le one_pos hΘ
  set R : ℝ := (3 : ℝ) ^ m with hRdef
  set Msq : ℝ := Θ * vecNormSq P.1 + vecNormSq P.2 with hMsqdef
  have hMsq0 : (0 : ℝ) ≤ Msq :=
    add_nonneg (mul_nonneg hΘ0.le (vecNormSq_nonneg _)) (vecNormSq_nonneg _)
  have hUmeasO : MeasurableSet (openCubeSet (originCube d m)) := measurableSet_openCubeSet _
  have hEllO : IsEllipticFieldOn 1 Θ (openCubeSet (originCube d m)) c :=
    hEll.mono hUmeasO (openCubeSet_subset_cubeSet (originCube d m))
  obtain ⟨Z, v, vstar, hAdmO, hEngO, hRespO, hTrace, _hgp, _hgf, hWeak, hEnergyId⟩ :=
    exists_coupledRepresentation hEll P
  obtain ⟨cval, hvb, hvsb⟩ := hstampU hEll hWeak hTrace
  set Kinf : ℝ := CdS * R * Real.sqrt Msq with hKinfdef
  have hKv : ∀ᵐ x ∂(volumeMeasureOn (openCubeSet (originCube d m))),
      |(centeredPotential m v P.1 cval).toFun x| ≤ Kinf := by
    filter_upwards [hvb] with x hx
    rw [centeredPotential_toFun]; exact hx
  have hKvs : ∀ᵐ x ∂(volumeMeasureOn (openCubeSet (originCube d m))),
      |(centeredPotential m vstar P.1 (-cval)).toFun x| ≤ Kinf := by
    filter_upwards [hvsb] with x hx
    rw [centeredPotential_toFun]; simpa using hx
  refine ⟨Z, (isBlockMuAdmissible_cubeSet_originCube_iff_openCubeSet).2 hAdmO,
    (blockResponseSpace_cubeSet_originCube_iff_openCubeSet).2 hRespO, ?_, ?_⟩
  · rw [Mu_cubeSet_originCube_eq_openCubeSet (d := d) m P c, hEngO]
    unfold blockEnergyAverage
    exact (volumeAverage_cubeSet_originCube_eq_openCubeSet (d := d) m
      (blockEnergyDensity c Z)).symm
  · intro k hk
    set C : Set (Vec d) := coreBox ℓ σ k ∩ openCubeSet (originCube d m) with hCdef
    have hCmeas : MeasurableSet C := (measurableSet_coreBox ℓ σ k).inter hUmeasO
    have hCU : C ⊆ (openCubeSet (originCube d m) : Set (Vec d)) := Set.inter_subset_right
    have hηC : ∀ᵐ x ∂(volumeMeasureOn C), coreCutoff ℓ σ k x = 1 := by
      refine (ae_restrict_iff' hCmeas).2 (Filter.Eventually.of_forall (fun x hx => ?_))
      exact coreCutoff_eq_one_of_mem_coreBox hℓ0 σ k hx.1
    have hbound := local_block_energy_uniform hEllO hWeak hTrace hKv hKvs
      (coreCutoff_contDiff ℓ σ k) (coreCutoff_mem_Icc ℓ σ k)
      (fun x i => coreCutoff_deriv_bound hℓ0 σ k x i) hEnergyId hCmeas hCU hηC
    have hsupp : (volume (Function.support (coreCutoff ℓ σ k) ∩
          openCubeSet (originCube d m))).toReal ≤ (3 * ℓ) ^ d :=
      coreCutoff_support_volume_le hℓ4 σ k _
    have hgrad : (∫ x in openCubeSet (originCube d m),
          ∑ i, (fderiv ℝ (coreCutoff ℓ σ k) x (basisVec i)) ^ 2)
        ≤ (d : ℝ) * (16 / ℓ) ^ 2 * (3 * ℓ) ^ d :=
      coreCutoff_sqGrad_integral_le hℓ4 σ k _
    rw [setIntegral_coreBox_inter_cubeSet_eq_openCubeSet]
    calc (∫ x in C, blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField c x) (Z.eval x)))
        ≤ 514 * ((Θ * vecNormSq P.1 + vecNormSq P.2) *
              (volume (Function.support (coreCutoff ℓ σ k) ∩
                openCubeSet (originCube d m))).toReal
            + Θ * Kinf ^ 2 * (∫ x in openCubeSet (originCube d m),
                ∑ i, (fderiv ℝ (coreCutoff ℓ σ k) x (basisVec i)) ^ 2)) := hbound
      _ ≤ (514 * 3 ^ d + 514 * CdS ^ 2 * (d : ℝ) * 256 * 3 ^ d) * Θ
            * ((3 : ℝ) ^ m) ^ 2 * ℓ ^ (d - 2) * (Θ * vecNormSq P.1 + vecNormSq P.2) :=
          perCore_numeric hd hΘ hℓ4 hℓL hMsq0 (by norm_num) hsupp hgrad hKinfdef

end Homogenization
