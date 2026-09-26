/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.CubeMinimizer
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.SharpBlockBounds.DiagonalSandwich
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeEllipticRecovery.QuadraticMu
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.ZeroTraceAverages

/-! # Sandwich -/

@[expose] public section

namespace Homogenization

/-!
# Coarse diagonal sandwich (items C1, C1′)

The coarse block matrix `𝐀(U; a) = coarseBlockMatrix U a` on the half-open
triadic cube `U = cubeSet (originCube d m)` is sandwiched between the two
scalar-diagonal block matrices `blockDiag (½•1) ((2Θ)⁻¹•1)` and
`blockDiag ((2Θ)•1) (2•1)` in the block Loewner order, for every coefficient
field that is `(1, Θ)`-elliptic on `U`.  This is Proposition 2.2's coarse
ellipticity statement `e.coarse.block.ellipticity` in the high-moment paper
(Armstrong–Kuusi–Loher, to appear).

* **C1 upper** — the constant competitor `X ≡ P` is `Mu`-admissible, and the
  pointwise A8 upper bound `bfA ≤ blockDiag ((2Θ)•1) (2•1)` gives
  `Mu ≤ Θ|p|² + |q|²`.
* **C1 lower** — for any admissible `X`, the pointwise A8 lower bound
  `blockDiag (½•1) ((2Θ)⁻¹•1) ≤ bfA`, followed by componentwise Jensen
  (`vecNormSq_volumeAverage_le_volumeAverage_vecNormSq`) and the mean-zero
  identities `⨍ X.potential = p`, `⨍ X.flux = q` (from the a.e. zero-trace
  averages `IsPotentialZeroTraceOn.integral_eq_zero_cubeSet_originCube` and
  `IsSolenoidalZeroNormalTraceOn.integral_eq_zero_cubeSet_originCube`), gives
  `¼|p|² + (4Θ)⁻¹|q|² ≤ Mu`.

Everything is rewritten through `mu_eq_half_coarseBlockMatrix_cube`
(`Mu = ½ P·𝐀 P`).  Vectors are `Vec d = Fin d → ℝ`; no `EuclideanSpace`.
-/

open Homogenization.Book.Ch02
open MeasureTheory

noncomputable section

variable {d : ℕ} {m : ℤ} {Θ : ℝ} {a : CoeffField d}

/-! ## Shared cube data -/

private theorem cube_volume_pos :
    0 < (volume (cubeSet (originCube d m))).toReal :=
  volume_cubeSet_originCube_toReal_pos_recovery (d := d) m

private theorem measurableSet_cube :
    MeasurableSet (cubeSet (originCube d m)) :=
  measurableSet_cubeSet (originCube d m)

/-- The origin belongs to every centered triadic cube, so ellipticity on the
cube forces `1 ≤ Θ`, in particular `0 < Θ`. -/
private theorem theta_pos (hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a) :
    0 < Θ := by
  have h0 : (0 : Vec d) ∈ cubeSet (originCube d m) := by
    rw [mem_cubeSet_originCube_iff]
    intro i
    have hpow : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
    simp only [Pi.zero_apply]
    constructor
    · nlinarith [hpow]
    · nlinarith [hpow]
  exact lt_of_lt_of_le one_pos (hEll.2 (0 : Vec d) h0).2.1

/-- Coordinate integrability from `L²` membership on the (finite-measure) cube. -/
private theorem coord_integrableOn_of_memVectorL2
    {f : Vec d → Vec d} (hf : MemVectorL2 (cubeSet (originCube d m)) f) (i : Fin d) :
    IntegrableOn (fun x => f x i) (cubeSet (originCube d m)) := by
  have h := integrableOn_vecDot_of_memVectorL2 hf
    (memVectorL2_const (U := cubeSet (originCube d m)) (basisVec i))
  simpa [vecDot_basisVec_right] using h

/-- `X.potential ∈ L²(U)` from admissibility. -/
private theorem memVectorL2_potential_of_admissible
    {P : BlockVec d} {X : BlockState d}
    (hX : IsBlockMuAdmissible (cubeSet (originCube d m)) P X) :
    MemVectorL2 (cubeSet (originCube d m)) X.potential := by
  have h := (memVectorL2_const (U := cubeSet (originCube d m)) P.1).add
    hX.potentialCorrection_memL2
  have heq : ((fun _ : Vec d => P.1) + fun x => X.potential x - P.1) = X.potential := by
    funext x; simp only [Pi.add_apply]; abel
  rwa [heq] at h

/-- `X.flux ∈ L²(U)` from admissibility. -/
private theorem memVectorL2_flux_of_admissible
    {P : BlockVec d} {X : BlockState d}
    (hX : IsBlockMuAdmissible (cubeSet (originCube d m)) P X) :
    MemVectorL2 (cubeSet (originCube d m)) X.flux := by
  have h := (memVectorL2_const (U := cubeSet (originCube d m)) P.2).add
    hX.fluxCorrection_memL2
  have heq : ((fun _ : Vec d => P.2) + fun x => X.flux x - P.2) = X.flux := by
    funext x; simp only [Pi.add_apply]; abel
  rwa [heq] at h

section

variable [NeZero d]

/-- The average of an admissible potential field recovers `p`.  This is C0(i)
turned into a `volumeAverage` identity. -/
private theorem volumeAverage_potential_eq
    {P : BlockVec d} {X : BlockState d}
    (hX : IsBlockMuAdmissible (cubeSet (originCube d m)) P X) :
    (fun i => volumeAverage (cubeSet (originCube d m)) (fun x => X.potential x i)) = P.1 := by
  funext i
  have hcorr :=
    congrFun (IsPotentialZeroTraceOn.integral_eq_zero_cubeSet_originCube (d := d) (n := m)
      hX.isPotentialZeroTrace) i
  have hcorrfun :
      ∫ x in cubeSet (originCube d m), (X.potential x i - P.1 i) ∂volume = 0 := by
    simpa using hcorr
  have hcorrInt : IntegrableOn (fun x => X.potential x i - P.1 i)
      (cubeSet (originCube d m)) := by
    have := coord_integrableOn_of_memVectorL2 (m := m)
      (f := fun x => X.potential x - P.1) hX.potentialCorrection_memL2 i
    simpa using this
  have hconstInt : IntegrableOn (fun _ : Vec d => P.1 i) (cubeSet (originCube d m)) :=
    integrable_const _
  have hsplit :
      (fun x => X.potential x i) =
        (fun x => X.potential x i - P.1 i) + (fun _ : Vec d => P.1 i) := by
    funext x; simp only [Pi.add_apply]; ring
  rw [hsplit, volumeAverage_add hcorrInt hconstInt,
    volumeAverage_eq_zero_of_integral_eq_zero hcorrfun,
    volumeAverage_const cube_volume_pos.ne']
  ring

/-- The average of an admissible flux field recovers `q`.  C0(ii) as a
`volumeAverage` identity. -/
private theorem volumeAverage_flux_eq
    {P : BlockVec d} {X : BlockState d}
    (hX : IsBlockMuAdmissible (cubeSet (originCube d m)) P X) :
    (fun i => volumeAverage (cubeSet (originCube d m)) (fun x => X.flux x i)) = P.2 := by
  funext i
  have hcorr :=
    congrFun (IsSolenoidalZeroNormalTraceOn.integral_eq_zero_cubeSet_originCube (d := d) (n := m)
      hX.isSolenoidalZeroNormalTrace) i
  have hcorrfun :
      ∫ x in cubeSet (originCube d m), (X.flux x i - P.2 i) ∂volume = 0 := by
    simpa using hcorr
  have hcorrInt : IntegrableOn (fun x => X.flux x i - P.2 i)
      (cubeSet (originCube d m)) := by
    have := coord_integrableOn_of_memVectorL2 (m := m)
      (f := fun x => X.flux x - P.2) hX.fluxCorrection_memL2 i
    simpa using this
  have hconstInt : IntegrableOn (fun _ : Vec d => P.2 i) (cubeSet (originCube d m)) :=
    integrable_const _
  have hsplit :
      (fun x => X.flux x i) =
        (fun x => X.flux x i - P.2 i) + (fun _ : Vec d => P.2 i) := by
    funext x; simp only [Pi.add_apply]; ring
  rw [hsplit, volumeAverage_add hcorrInt hconstInt,
    volumeAverage_eq_zero_of_integral_eq_zero hcorrfun,
    volumeAverage_const cube_volume_pos.ne']
  ring

end

/-! ## The pointwise A8 bounds on the block energy density -/

/-- Pointwise A8 lower bound on the block energy density. -/
private theorem quarter_add_le_blockEnergyDensity
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a) (X : BlockState d)
    {x : Vec d} (hx : x ∈ cubeSet (originCube d m)) :
    (1 / 4 : ℝ) * vecNormSq (X.potential x) +
        (4 * Θ)⁻¹ * vecNormSq (X.flux x) ≤ blockEnergyDensity a X x := by
  have hlo := blockDiag_blockMatLoewnerLE_blockMatrixOfCoeff_of_isThetaElliptic
    (hEll.2 x hx) (X.potential x, X.flux x)
  have hdiag := blockVecDot_blockMatVecMul_blockDiag_smul_one (1 / 2 : ℝ) ((2 * Θ)⁻¹)
    (X.potential x) (X.flux x)
  have hΘ : 0 < Θ := theta_pos hEll
  have hne : (2 * Θ) ≠ 0 := by positivity
  -- `blockEnergyDensity a X x = ½ (X.eval x)·bfA(a x)(X.eval x)`
  have hEnergy :
      blockEnergyDensity a X x =
        (1 / 2 : ℝ) *
          blockVecDot (X.potential x, X.flux x)
            (blockMatVecMul (blockMatrixOfCoeff (a x)) (X.potential x, X.flux x)) := by
    rfl
  rw [hEnergy]
  rw [hdiag] at hlo
  have harith : (1 / 2 : ℝ) * ((1 / 2) * vecNormSq (X.potential x) +
      (2 * Θ)⁻¹ * vecNormSq (X.flux x)) =
      (1 / 4 : ℝ) * vecNormSq (X.potential x) + (4 * Θ)⁻¹ * vecNormSq (X.flux x) := by
    rw [show (4 * Θ)⁻¹ = (1 / 2 : ℝ) * (2 * Θ)⁻¹ by
      rw [mul_inv]; ring]
    ring
  linarith [hlo, harith.symm.le, harith.le]

/-- Pointwise A8 upper bound on the block energy density of the constant
competitor `X ≡ P`. -/
private theorem blockEnergyDensity_const_le
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a) (P : BlockVec d)
    {x : Vec d} (hx : x ∈ cubeSet (originCube d m)) :
    blockEnergyDensity a { potential := fun _ => P.1, flux := fun _ => P.2 } x ≤
      Θ * vecNormSq P.1 + vecNormSq P.2 := by
  have hup := blockMatrixOfCoeff_blockMatLoewnerLE_blockDiag_of_isThetaElliptic
    (hEll.2 x hx) (P.1, P.2)
  have hdiag := blockVecDot_blockMatVecMul_blockDiag_smul_one (2 * Θ) (2 : ℝ) P.1 P.2
  have hEnergy :
      blockEnergyDensity a { potential := fun _ => P.1, flux := fun _ => P.2 } x =
        (1 / 2 : ℝ) *
          blockVecDot (P.1, P.2)
            (blockMatVecMul (blockMatrixOfCoeff (a x)) (P.1, P.2)) := by
    rfl
  rw [hEnergy]
  rw [hdiag] at hup
  have harith : (1 / 2 : ℝ) * ((2 * Θ) * vecNormSq P.1 + 2 * vecNormSq P.2) =
      Θ * vecNormSq P.1 + vecNormSq P.2 := by ring
  linarith [hup, harith.le, harith.symm.le]

/-! ## C1 as `Mu` bounds -/

variable [NeZero d]

/-- **C1 lower** as a `Mu` bound:
`¼|p|² + (4Θ)⁻¹|q|² ≤ Mu (U; P, a)`. -/
theorem diag_lower_le_mu_cube
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a) (P : BlockVec d) :
    (1 / 4 : ℝ) * vecNormSq P.1 + (4 * Θ)⁻¹ * vecNormSq P.2 ≤
      Mu (cubeSet (originCube d m)) P a := by
  have hΘ : 0 < Θ := theta_pos hEll
  refine le_Mu_of_forall_isBlockMuAdmissible ?_
  intro X hX
  -- L² memberships and energy integrability
  have hPotL2 : MemVectorL2 (cubeSet (originCube d m)) X.potential :=
    memVectorL2_potential_of_admissible hX
  have hFluxL2 : MemVectorL2 (cubeSet (originCube d m)) X.flux :=
    memVectorL2_flux_of_admissible hX
  have hEnergyInt : IntegrableOn (blockEnergyDensity a X) (cubeSet (originCube d m)) :=
    (hX.toBlockMuIntegrabilityDataOfIsEllipticFieldOn (a := a) hEll).energyIntegrable
  have hf1Int : IntegrableOn (fun x => vecNormSq (X.potential x))
      (cubeSet (originCube d m)) := by
    simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hPotL2 hPotL2
  have hf2Int : IntegrableOn (fun x => vecNormSq (X.flux x))
      (cubeSet (originCube d m)) := by
    simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hFluxL2 hFluxL2
  -- lower comparison function is integrable
  have hgInt : IntegrableOn
      (fun x => (1 / 4 : ℝ) * vecNormSq (X.potential x) +
        (4 * Θ)⁻¹ * vecNormSq (X.flux x)) (cubeSet (originCube d m)) :=
    (hf1Int.const_mul (1 / 4 : ℝ)).add (hf2Int.const_mul ((4 * Θ)⁻¹))
  -- Step 1: pointwise A8 lower + volumeAverage monotonicity
  have hstep1 :
      volumeAverage (cubeSet (originCube d m))
          (fun x => (1 / 4 : ℝ) * vecNormSq (X.potential x) +
            (4 * Θ)⁻¹ * vecNormSq (X.flux x)) ≤
        volumeAverage (cubeSet (originCube d m)) (blockEnergyDensity a X) :=
    volumeAverage_le_volumeAverage_of_le_on measurableSet_cube hgInt hEnergyInt
      (fun x hx => quarter_add_le_blockEnergyDensity hEll X hx)
  -- Step 2: split the average
  have hsplit :
      volumeAverage (cubeSet (originCube d m))
          (fun x => (1 / 4 : ℝ) * vecNormSq (X.potential x) +
            (4 * Θ)⁻¹ * vecNormSq (X.flux x)) =
        (1 / 4 : ℝ) *
            volumeAverage (cubeSet (originCube d m)) (fun x => vecNormSq (X.potential x)) +
          (4 * Θ)⁻¹ *
            volumeAverage (cubeSet (originCube d m)) (fun x => vecNormSq (X.flux x)) := by
    unfold volumeAverage
    rw [integral_add (hf1Int.const_mul (1 / 4 : ℝ)) (hf2Int.const_mul ((4 * Θ)⁻¹)),
      integral_const_mul, integral_const_mul]
    ring
  -- Step 3: componentwise Jensen
  have hJensenPot :
      vecNormSq P.1 ≤
        volumeAverage (cubeSet (originCube d m)) (fun x => vecNormSq (X.potential x)) := by
    have hJ := vecNormSq_volumeAverage_le_volumeAverage_vecNormSq
      measurableSet_cube cube_volume_pos.ne' hPotL2
    rwa [volumeAverage_potential_eq hX] at hJ
  have hJensenFlux :
      vecNormSq P.2 ≤
        volumeAverage (cubeSet (originCube d m)) (fun x => vecNormSq (X.flux x)) := by
    have hJ := vecNormSq_volumeAverage_le_volumeAverage_vecNormSq
      measurableSet_cube cube_volume_pos.ne' hFluxL2
    rwa [volumeAverage_flux_eq hX] at hJ
  -- assemble
  have hquarter : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have hcoef : (0 : ℝ) ≤ (4 * Θ)⁻¹ := by positivity
  calc
    (1 / 4 : ℝ) * vecNormSq P.1 + (4 * Θ)⁻¹ * vecNormSq P.2
        ≤ (1 / 4 : ℝ) *
              volumeAverage (cubeSet (originCube d m)) (fun x => vecNormSq (X.potential x)) +
            (4 * Θ)⁻¹ *
              volumeAverage (cubeSet (originCube d m)) (fun x => vecNormSq (X.flux x)) := by
          have h1 := mul_le_mul_of_nonneg_left hJensenPot hquarter
          have h2 := mul_le_mul_of_nonneg_left hJensenFlux hcoef
          linarith
    _ = volumeAverage (cubeSet (originCube d m))
          (fun x => (1 / 4 : ℝ) * vecNormSq (X.potential x) +
            (4 * Θ)⁻¹ * vecNormSq (X.flux x)) := hsplit.symm
    _ ≤ volumeAverage (cubeSet (originCube d m)) (blockEnergyDensity a X) := hstep1

omit [NeZero d] in
/-- **C1 upper** as a `Mu` bound:
`Mu (U; P, a) ≤ Θ|p|² + |q|²`. -/
theorem mu_le_diag_upper_cube
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a) (P : BlockVec d) :
    Mu (cubeSet (originCube d m)) P a ≤ Θ * vecNormSq P.1 + vecNormSq P.2 := by
  classical
  set U := cubeSet (originCube d m) with hU
  -- the constant competitor
  set X₀ : BlockState d := { potential := fun _ => P.1, flux := fun _ => P.2 } with hX₀
  have hAdm : IsBlockMuAdmissible U P X₀ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hz : (fun x => X₀.potential x - P.1) = (0 : Vec d → Vec d) := by
        funext x; simp [hX₀]
      rw [hz]; exact MemLp.zero
    · have hz : (fun x => X₀.potential x - P.1) = (0 : Vec d → Vec d) := by
        funext x; simp [hX₀]
      rw [hz]; exact isPotentialZeroTraceOn_zero (U := U)
    · have hz : (fun x => X₀.flux x - P.2) = (0 : Vec d → Vec d) := by
        funext x; simp [hX₀]
      rw [hz]; exact MemLp.zero
    · have hz : (fun x => X₀.flux x - P.2) = (0 : Vec d → Vec d) := by
        funext x; simp [hX₀]
      rw [hz]; exact isSolenoidalZeroNormalTraceOn_zero (U := U)
  -- muValueSet is bounded below by 0 (block energy density is p.s.d.)
  have hBddBelow : BddBelow (muValueSet U P a) := by
    refine ⟨0, ?_⟩
    intro s hs
    rcases hs with ⟨Y, _hY, rfl⟩
    refine volumeAverage_nonneg_of_nonneg_on measurableSet_cube ?_
    intro x hx
    have hpsd := blockMatrixOfCoeff_quadratic_nonneg (hEll.2 x hx) (Y.eval x)
    have : blockEnergyDensity a Y x =
        (1 / 2 : ℝ) *
          blockVecDot (Y.eval x) (blockMatVecMul (blockMatrixOfCoeff (a x)) (Y.eval x)) := rfl
    rw [this]; positivity
  -- Mu ≤ average of the competitor's energy
  have hMuLe : Mu U P a ≤ volumeAverage U (blockEnergyDensity a X₀) := by
    unfold Mu
    exact csInf_le hBddBelow (muValueSet_mem hAdm)
  -- competitor's energy average ≤ Θ|p|² + |q|²
  have hEnergyInt : IntegrableOn (blockEnergyDensity a X₀) U :=
    (hAdm.toBlockMuIntegrabilityDataOfIsEllipticFieldOn (a := a) hEll).energyIntegrable
  have hAvgLe :
      volumeAverage U (blockEnergyDensity a X₀) ≤ Θ * vecNormSq P.1 + vecNormSq P.2 :=
    volumeAverage_le_of_le_on measurableSet_cube hEnergyInt cube_volume_pos.ne'
      (fun x hx => by
        have := blockEnergyDensity_const_le hEll P hx
        simpa [hX₀] using this)
  exact le_trans hMuLe hAvgLe

/-! ## C1 — the block Loewner sandwich -/

/-- **C1 (lower).**  `blockDiag (½•1) ((2Θ)⁻¹•1) ≤ 𝐀(U; a)` in the block Loewner
order, on the half-open triadic cube. -/
theorem blockDiag_blockMatLoewnerLE_coarseBlockMatrix_cube
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a) :
    BlockMatLoewnerLE
      (blockDiag ((1 / 2 : ℝ) • (1 : Mat d)) ((2 * Θ)⁻¹ • (1 : Mat d)))
      (coarseBlockMatrix (cubeSet (originCube d m)) a) := by
  intro X
  obtain ⟨p, q⟩ := X
  rw [← mu_eq_half_coarseBlockMatrix_cube hEll (p, q)]
  rw [blockVecDot_blockMatVecMul_blockDiag_smul_one (1 / 2 : ℝ) ((2 * Θ)⁻¹) p q]
  have hlow := diag_lower_le_mu_cube hEll (p, q)
  have hval : (1 / 2 : ℝ) * ((1 / 2 : ℝ) * vecNormSq p + (2 * Θ)⁻¹ * vecNormSq q) =
      (1 / 4 : ℝ) * vecNormSq p + (4 * Θ)⁻¹ * vecNormSq q := by
    rw [show (4 * Θ)⁻¹ = (1 / 2 : ℝ) * (2 * Θ)⁻¹ by rw [mul_inv]; ring]
    ring
  rw [hval]
  simpa using hlow

/-- **C1 (upper).**  `𝐀(U; a) ≤ blockDiag ((2Θ)•1) (2•1)` in the block Loewner
order, on the half-open triadic cube. -/
theorem coarseBlockMatrix_blockMatLoewnerLE_blockDiag_cube
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a) :
    BlockMatLoewnerLE
      (coarseBlockMatrix (cubeSet (originCube d m)) a)
      (blockDiag ((2 * Θ) • (1 : Mat d)) ((2 : ℝ) • (1 : Mat d))) := by
  intro X
  obtain ⟨p, q⟩ := X
  rw [← mu_eq_half_coarseBlockMatrix_cube hEll (p, q)]
  rw [blockVecDot_blockMatVecMul_blockDiag_smul_one (2 * Θ) (2 : ℝ) p q]
  have hup := mu_le_diag_upper_cube hEll (p, q)
  have hval : (1 / 2 : ℝ) * ((2 * Θ) * vecNormSq p + 2 * vecNormSq q) =
      Θ * vecNormSq p + vecNormSq q := by ring
  rw [hval]
  simpa using hup

/-! ## C1′ — scalar corollaries -/

/-- **C1′ (nonnegativity).**  `0 ≤ P·𝐀(U; a) P`. -/
theorem zero_le_blockVecDot_coarseBlockMatrix_cube
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a) (P : BlockVec d) :
    0 ≤ blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a) P) := by
  have hlow := blockDiag_blockMatLoewnerLE_coarseBlockMatrix_cube hEll P
  obtain ⟨p, q⟩ := P
  rw [blockVecDot_blockMatVecMul_blockDiag_smul_one (1 / 2 : ℝ) ((2 * Θ)⁻¹) p q] at hlow
  have hΘ : 0 < Θ := theta_pos hEll
  have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) * vecNormSq p + (2 * Θ)⁻¹ * vecNormSq q) := by
    have h1 : (0 : ℝ) ≤ vecNormSq p := vecNormSq_nonneg p
    have h2 : (0 : ℝ) ≤ vecNormSq q := vecNormSq_nonneg q
    have h3 : (0 : ℝ) ≤ (2 * Θ)⁻¹ := by positivity
    positivity
  linarith [hlow, hnn]

/-- **C1′ (upper).**  `P·𝐀(U; a) P ≤ 2 (Θ|p|² + |q|²)`. -/
theorem blockVecDot_coarseBlockMatrix_cube_le
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a) (P : BlockVec d) :
    blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a) P) ≤
      2 * (Θ * vecNormSq P.1 + vecNormSq P.2) := by
  have hup := coarseBlockMatrix_blockMatLoewnerLE_blockDiag_cube hEll P
  obtain ⟨p, q⟩ := P
  rw [blockVecDot_blockMatVecMul_blockDiag_smul_one (2 * Θ) (2 : ℝ) p q] at hup
  simp only at hup ⊢
  linarith [hup]

end

end Homogenization
