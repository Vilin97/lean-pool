/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.HighContrast.Coupled.LocalEnergy.Identity

/-!
# Local block energy: the bulk and cutoff estimates

Pointwise upper bounds on the bulk and cutoff densities of the test identity,
absorbed against the energy density, following `e.local.block.bulk` and
`e.local.block.cutoff`.  Integrating gives the centered energy bound
(`e.local.block.centered.energy`), the analytic core of `T1`.

* bulk:   `bulk x ≤ 5M²·η² + ⅛·𝓔-density`;
* cutoff: `cutoff x ≤ 5M²·η² + ⅟₁₆·𝓔-density + 67Θ·K∞²·|∇η|²`  (a.e.),

where `M² = Θ|p|² + |q|²`.  No `EuclideanSpace`.
-/

@[expose] public section

namespace Homogenization

open Homogenization
open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Elementary scalar helpers -/

/-- Cauchy–Schwarz for the dot product in square-root form. -/
theorem abs_vecDot_le_sqrt_mul_sqrt (x y : Vec d) :
    |vecDot x y| ≤ Real.sqrt (vecNormSq x) * Real.sqrt (vecNormSq y) := by
  have hcs : vecDot x y ^ 2 ≤ vecNormSq x * vecNormSq y :=
    sq_vecDot_le_vecNormSq_mul_vecNormSq x y
  have h1 : |vecDot x y| = Real.sqrt (vecDot x y ^ 2) := by
    rw [Real.sqrt_sq_eq_abs]
  rw [h1, ← Real.sqrt_mul (vecNormSq_nonneg x)]
  exact Real.sqrt_le_sqrt hcs

/-- `a·b ≤ ½a² + ½b²`. -/
theorem mul_le_half_sq_add_half_sq (a b : ℝ) : a * b ≤ a ^ 2 / 2 + b ^ 2 / 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- AM–GM from a squared bound: if `x² ≤ 4c₁c₂` with `x, c₁, c₂ ≥ 0` then
`x ≤ c₁ + c₂`. -/
theorem amgm_of_sq_le {x c1 c2 : ℝ} (hx : 0 ≤ x) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hsq : x ^ 2 ≤ 4 * c1 * c2) : x ≤ c1 + c2 := by
  have h1 : x ^ 2 ≤ (c1 + c2) ^ 2 := by nlinarith [sq_nonneg (c1 - c2)]
  have h2 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq hx, Real.sqrt_sq (by linarith)] at h2

/-- Cauchy–Schwarz + AM–GM packaged: from a dot-product Cauchy–Schwarz bound
and a matching product bound, `K·|D| ≤ A + B`. -/
theorem amgm_term {K D nX nG A B : ℝ} (hK : 0 ≤ K) (hCS : D ^ 2 ≤ nX * nG)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hkey : K ^ 2 * (nX * nG) ≤ 4 * A * B) :
    K * |D| ≤ A + B := by
  have hx : 0 ≤ K * |D| := mul_nonneg hK (abs_nonneg _)
  have hsq : (K * |D|) ^ 2 ≤ 4 * A * B := by
    have he : (K * |D|) ^ 2 = K ^ 2 * D ^ 2 := by rw [mul_pow, sq_abs]
    rw [he]
    have := mul_le_mul_of_nonneg_left hCS (sq_nonneg K)
    linarith [hkey]
  exact amgm_of_sq_le hx hA hB hsq

/-- A single cutoff dot-product term: Cauchy–Schwarz against `∇(η²)` plus AM–GM.
`|∇(η²)|² = 4η²N`, `|X|² ≤ Q`, and `4K²η²N·Q = 4AB` give `K·|X·∇(η²)| ≤ A + B`. -/
theorem cutoff_amgm_dot {K ηx N Q A B : ℝ} {X gS : Vec d}
    (hK : 0 ≤ K) (hgSN : vecNormSq gS = 4 * ηx ^ 2 * N) (hnX : vecNormSq X ≤ Q)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hfac : 0 ≤ 4 * K ^ 2 * ηx ^ 2 * N)
    (hkey : 4 * K ^ 2 * ηx ^ 2 * N * Q ≤ 4 * A * B) :
    K * |vecDot X gS| ≤ A + B := by
  refine amgm_term hK (sq_vecDot_le_vecNormSq_mul_vecNormSq X gS) hA hB ?_
  rw [hgSN]
  nlinarith [mul_le_mul_of_nonneg_left hnX hfac, hkey]

/-- The absolute-value decomposition of the cutoff density into five scalar
terms, each dominated by `K = K∞`. -/
theorem cutoff_abs_split {uu uus K t1 t2 t3 t4 t5 : ℝ}
    (hK : 0 ≤ K) (huu : |uu| ≤ K) (huus : |uus| ≤ K) :
    uu * (t1 - t2 - (1/2) * t3) - uus * (t4 + (1/2) * t5)
      ≤ K * |t1| + K * |t2| + (1/2) * (K * |t3|)
        + K * |t4| + (1/2) * (K * |t5|) := by
  have hD1abs : |t1 - t2 - (1/2) * t3| ≤ |t1| + |t2| + (1/2) * |t3| := by
    have h1 := abs_sub (t1 - t2) ((1/2) * t3)
    have h2 := abs_sub t1 t2
    have h3 : |(1/2) * t3| = (1/2) * |t3| := by rw [abs_mul]; norm_num
    linarith [h1, h2, h3.le, h3.ge]
  have hD2abs : |t4 + (1/2) * t5| ≤ |t4| + (1/2) * |t5| := by
    have h1 := abs_add_le t4 ((1/2) * t5)
    have h3 : |(1/2) * t5| = (1/2) * |t5| := by rw [abs_mul]; norm_num
    linarith [h1, h3.le, h3.ge]
  have huu1 : |uu * (t1 - t2 - (1/2) * t3)|
      ≤ K * |t1| + K * |t2| + (1/2) * (K * |t3|) := by
    rw [abs_mul]
    calc |uu| * |t1 - t2 - (1/2) * t3|
        ≤ K * (|t1| + |t2| + (1/2) * |t3|) := mul_le_mul huu hD1abs (abs_nonneg _) hK
      _ = _ := by ring
  have huu2 : |uus * (t4 + (1/2) * t5)|
      ≤ K * |t4| + (1/2) * (K * |t5|) := by
    rw [abs_mul]
    calc |uus| * |t4 + (1/2) * t5|
        ≤ K * (|t4| + (1/2) * |t5|) := mul_le_mul huus hD2abs (abs_nonneg _) hK
      _ = _ := by ring
  have hself := le_abs_self (uu * (t1 - t2 - (1/2) * t3) - uus * (t4 + (1/2) * t5))
  have ha2 := abs_sub (uu * (t1 - t2 - (1/2) * t3)) (uus * (t4 + (1/2) * t5))
  linarith [hself, ha2, huu1, huu2]

section Cube

variable [NeZero d] {m : ℤ}

local notation "U" => openCubeSet (originCube d m)

/-! ## The bulk estimate -/

omit [NeZero d] in
/-- **Bulk density bound.**  For `x ∈ U`,
`bulk x ≤ 5M²·η²(x) + ⅛·(energy density)(x)`. -/
theorem bulkIntegrand_le {a : CoeffField d} {Θ : ℝ} {v vstar : H1Function U}
    {P : BlockVec d} {η : Vec d → ℝ}
    (hEllO : IsEllipticFieldOn 1 Θ U a) {x : Vec d} (hx : x ∈ U) :
    bulkIntegrand a v vstar P η x
      ≤ 5 * (Θ * vecNormSq P.1 + vecNormSq P.2) * sqCutoff η x
        + (1/8) * energyIntegrand a v vstar P η x := by
  have hA : IsThetaElliptic Θ (a x) := hEllO.2 x hx
  set V := v.grad x - (1/2:ℝ)•P.1 with hVdef
  set Vstar := vstar.grad x - (1/2:ℝ)•P.1 with hVsdef
  set Msq := Θ * vecNormSq P.1 + vecNormSq P.2 with hMsqdef
  -- nonnegativity of the two `s`-forms
  have hVsV : 0 ≤ vecDot V (matVecMul (symmPart (a x)) V) :=
    vecDot_matVecMul_symmPart_nonneg hA V
  have hVsVs : 0 ≤ vecDot Vstar (matVecMul (symmPart (a x)) Vstar) :=
    vecDot_matVecMul_symmPart_nonneg hA Vstar
  -- term 1 : `(q − ½ap)·V`
  have hy1 := symmForm_young hA (t := (1/4:ℝ)) (by norm_num)
    (P.2 - (1/2:ℝ)•matVecMul (a x) P.1) V
  have hb1 := symmPartInv_bulkV_le hA P.1 P.2
  have hterm1 : vecDot (P.2 - (1/2:ℝ)•matVecMul (a x) P.1) V
      ≤ 4 * Msq + (1/8) * vecDot V (matVecMul (symmPart (a x)) V) := by
    nlinarith [hy1, hb1]
  -- term 2 : `−½(aᵀp)·V*`
  set ξ2 : Vec d := -(matVecMul (matTranspose (a x)) P.1) with hξ2
  have hy2 := symmForm_young hA (t := (1/4:ℝ)) (by norm_num) ξ2 Vstar
  have hb2raw := symmPartInv_imageTranspose_le hA P.1
  have hb2 : vecDot ξ2 (matVecMul (symmPart (a x))⁻¹ ξ2) ≤ Msq := by
    have heq : vecDot ξ2 (matVecMul (symmPart (a x))⁻¹ ξ2)
        = vecDot (matVecMul (matTranspose (a x)) P.1)
            (matVecMul (symmPart (a x))⁻¹ (matVecMul (matTranspose (a x)) P.1)) := by
      simp only [hξ2, matVecMul_neg, vecDot_neg_left, vecDot_neg_right, neg_neg]
    rw [heq]
    have : Θ * vecNormSq P.1 ≤ Msq := by
      rw [hMsqdef]; nlinarith [vecNormSq_nonneg P.2]
    exact le_trans hb2raw this
  have hterm2 : -(1/2:ℝ) * vecDot (matVecMul (matTranspose (a x)) P.1) Vstar
      ≤ Msq + (1/16) * vecDot Vstar (matVecMul (symmPart (a x)) Vstar) := by
    have hneg : -(1/2:ℝ) * vecDot (matVecMul (matTranspose (a x)) P.1) Vstar
        = (1/2:ℝ) * vecDot ξ2 Vstar := by
      rw [hξ2, vecDot_neg_left]; ring
    rw [hneg]
    nlinarith [hy2, hb2]
  -- combine and multiply by `η² ≥ 0`
  have hinner : vecDot (P.2 - (1/2:ℝ)•matVecMul (a x) P.1) V
        - (1/2:ℝ) * vecDot (matVecMul (matTranspose (a x)) P.1) Vstar
      ≤ 5 * Msq
        + (1/8) * (vecDot V (matVecMul (symmPart (a x)) V)
          + vecDot Vstar (matVecMul (symmPart (a x)) Vstar)) := by
    nlinarith [hterm1, hterm2, hVsVs]
  have hη2 : 0 ≤ sqCutoff η x := sqCutoff_nonneg η x
  calc bulkIntegrand a v vstar P η x
      = sqCutoff η x * (vecDot (P.2 - (1/2:ℝ)•matVecMul (a x) P.1) V
          - (1/2:ℝ) * vecDot (matVecMul (matTranspose (a x)) P.1) Vstar) := rfl
    _ ≤ sqCutoff η x * (5 * Msq
          + (1/8) * (vecDot V (matVecMul (symmPart (a x)) V)
            + vecDot Vstar (matVecMul (symmPart (a x)) Vstar))) :=
        mul_le_mul_of_nonneg_left hinner hη2
    _ = 5 * Msq * sqCutoff η x + (1/8) * energyIntegrand a v vstar P η x := by
        simp only [energyIntegrand, hVdef, hVsdef]; ring

/-! ## The cutoff estimate -/

omit [NeZero d] in
/-- **Cutoff density bound** (a.e.).  For `x ∈ U` with `|u|, |u*| ≤ K∞`,
requiring no range condition on the cutoff,
`cutoff x ≤ ⅟₁₆·(energy density)(x) + 2M²·η²(x) + 67Θ·K∞²·|∇η(x)|²`. -/
theorem cutoffIntegrand_le {a : CoeffField d} {Θ : ℝ} {v vstar : H1Function U}
    {P : BlockVec d} {η : Vec d → ℝ} {c Kinf : ℝ}
    (hEllO : IsEllipticFieldOn 1 Θ U a) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {x : Vec d} (hx : x ∈ U)
    (hKv : |(centeredPotential m v P.1 c).toFun x| ≤ Kinf)
    (hKvs : |(centeredPotential m vstar P.1 (-c)).toFun x| ≤ Kinf) :
    cutoffIntegrand a v vstar P c η x
      ≤ (1/16) * energyIntegrand a v vstar P η x
        + 2 * (Θ * vecNormSq P.1 + vecNormSq P.2) * sqCutoff η x
        + 67 * Θ * Kinf ^ 2 * vecNormSq (fun i => fderiv ℝ η x (basisVec i)) := by
  have hA : IsThetaElliptic Θ (a x) := hEllO.2 x hx
  have hΘ1 : (1 : ℝ) ≤ Θ := hA.2.1
  have hΘ0 : (0 : ℝ) ≤ Θ := by linarith
  have hKinf0 : (0 : ℝ) ≤ Kinf := le_trans (abs_nonneg _) hKv
  set V := v.grad x - (1/2:ℝ)•P.1 with hVdef
  set Vstar := vstar.grad x - (1/2:ℝ)•P.1 with hVsdef
  set EV := vecDot V (matVecMul (symmPart (a x)) V) with hEVdef
  set EVs := vecDot Vstar (matVecMul (symmPart (a x)) Vstar) with hEVsdef
  have hEV0 : 0 ≤ EV := vecDot_matVecMul_symmPart_nonneg hA V
  have hEVs0 : 0 ≤ EVs := vecDot_matVecMul_symmPart_nonneg hA Vstar
  set Msq := Θ * vecNormSq P.1 + vecNormSq P.2 with hMsqdef
  have hMsq0 : 0 ≤ Msq :=
    add_nonneg (mul_nonneg hΘ0 (vecNormSq_nonneg _)) (vecNormSq_nonneg _)
  set N := vecNormSq (fun i => fderiv ℝ η x (basisVec i)) with hNdef
  have hN0 : 0 ≤ N := vecNormSq_nonneg _
  have hgSN : vecNormSq (fun i => fderiv ℝ (sqCutoff η) x (basisVec i))
      = 4 * (η x) ^ 2 * N := by
    have hgSeq : (fun i => fderiv ℝ (sqCutoff η) x (basisVec i))
        = (2 * η x) • (fun i => fderiv ℝ η x (basisVec i)) := by
      funext i; rw [fderiv_sqCutoff hη x i]; simp [Pi.smul_apply, mul_comm, mul_assoc]
    rw [hgSeq, vecNormSq_smul, hNdef]; ring
  set gS := fun i => fderiv ℝ (sqCutoff η) x (basisVec i) with hgSdef
  -- squared-norm bounds
  have hnP2 : vecNormSq P.2 ≤ Msq := by
    rw [hMsqdef]; exact le_add_of_nonneg_left (mul_nonneg hΘ0 (vecNormSq_nonneg P.1))
  have hnaV : vecNormSq (matVecMul (a x) V) ≤ 2 * Θ * EV := vecNormSq_image_le hA V
  have hnaVs : vecNormSq (matVecMul (matTranspose (a x)) Vstar) ≤ 2 * Θ * EVs :=
    vecNormSq_imageTranspose_le hA Vstar
  have hnaP1 : vecNormSq (matVecMul (a x) P.1) ≤ 2 * Θ * Msq := by
    have h1 := vecNormSq_image_le hA P.1
    have h2 := upperBound_symmPart_of_isEllipticMatrix hA P.1
    have h3 : 2 * Θ * vecDot P.1 (matVecMul (symmPart (a x)) P.1)
        ≤ 2 * Θ * (Θ * vecNormSq P.1) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have h4 : 0 ≤ 2 * Θ * vecNormSq P.2 :=
      mul_nonneg (by linarith) (vecNormSq_nonneg P.2)
    rw [hMsqdef]; linarith [h1, h3, h4]
  have hnaTP1 : vecNormSq (matVecMul (matTranspose (a x)) P.1) ≤ 2 * Θ * Msq := by
    have h1 := vecNormSq_imageTranspose_le hA P.1
    have h2 := upperBound_symmPart_of_isEllipticMatrix hA P.1
    have h3 : 2 * Θ * vecDot P.1 (matVecMul (symmPart (a x)) P.1)
        ≤ 2 * Θ * (Θ * vecNormSq P.1) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have h4 : 0 ≤ 2 * Θ * vecNormSq P.2 :=
      mul_nonneg (by linarith) (vecNormSq_nonneg P.2)
    rw [hMsqdef]; linarith [h1, h3, h4]
  -- nonnegativity of the AM–GM operands
  have hfac : 0 ≤ 4 * Kinf ^ 2 * (η x) ^ 2 * N :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)) hN0
  have hAMsq : 0 ≤ (η x) ^ 2 * Msq := mul_nonneg (sq_nonneg _) hMsq0
  have hB1 : 0 ≤ Kinf ^ 2 * N := mul_nonneg (sq_nonneg _) hN0
  have hB32 : 0 ≤ 32 * Θ * Kinf ^ 2 * N :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hΘ0) (sq_nonneg _)) hN0
  have hB2 : 0 ≤ 2 * Θ * Kinf ^ 2 * N :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hΘ0) (sq_nonneg _)) hN0
  have hAEV : 0 ≤ (1/16) * ((η x) ^ 2 * EV) :=
    mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) hEV0)
  have hAEVs : 0 ≤ (1/16) * ((η x) ^ 2 * EVs) :=
    mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) hEVs0)
  -- the five per-term bounds (each a term-mode application)
  have bP2 : Kinf * |vecDot P.2 gS| ≤ (η x) ^ 2 * Msq + Kinf ^ 2 * N :=
    cutoff_amgm_dot hKinf0 hgSN hnP2 hAMsq hB1 hfac (le_of_eq (by ring))
  have baV : Kinf * |vecDot (matVecMul (a x) V) gS|
      ≤ (1/16) * ((η x) ^ 2 * EV) + 32 * Θ * Kinf ^ 2 * N :=
    cutoff_amgm_dot hKinf0 hgSN hnaV hAEV hB32 hfac (le_of_eq (by ring))
  have baP1 : Kinf * |vecDot (matVecMul (a x) P.1) gS|
      ≤ (η x) ^ 2 * Msq + 2 * Θ * Kinf ^ 2 * N :=
    cutoff_amgm_dot hKinf0 hgSN hnaP1 hAMsq hB2 hfac (le_of_eq (by ring))
  have baVs : Kinf * |vecDot (matVecMul (matTranspose (a x)) Vstar) gS|
      ≤ (1/16) * ((η x) ^ 2 * EVs) + 32 * Θ * Kinf ^ 2 * N :=
    cutoff_amgm_dot hKinf0 hgSN hnaVs hAEVs hB32 hfac (le_of_eq (by ring))
  have baTP1 : Kinf * |vecDot (matVecMul (matTranspose (a x)) P.1) gS|
      ≤ (η x) ^ 2 * Msq + 2 * Θ * Kinf ^ 2 * N :=
    cutoff_amgm_dot hKinf0 hgSN hnaTP1 hAMsq hB2 hfac (le_of_eq (by ring))
  -- the abs decomposition (delegated to `cutoff_abs_split`)
  have vsub : ∀ (a1 b1 c1 : Vec d), vecDot (a1 - b1) c1 = vecDot a1 c1 - vecDot b1 c1 := by
    intro a1 b1 c1
    rw [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left, ← sub_eq_add_neg]
  have hgv : v.grad x = V + (1/2:ℝ)•P.1 := by rw [hVdef]; abel
  have hgvs : vstar.grad x = Vstar + (1/2:ℝ)•P.1 := by rw [hVsdef]; abel
  have hD1 : vecDot (P.2 - matVecMul (a x) (v.grad x)) gS
      = vecDot P.2 gS - vecDot (matVecMul (a x) V) gS
        - (1/2) * vecDot (matVecMul (a x) P.1) gS := by
    rw [hgv, matVecMul_add, matVecMul_smul, sub_add_eq_sub_sub, vsub, vsub, vecDot_smul_left]
  have hD2 : vecDot (matVecMul (matTranspose (a x)) (vstar.grad x)) gS
      = vecDot (matVecMul (matTranspose (a x)) Vstar) gS
        + (1/2) * vecDot (matVecMul (matTranspose (a x)) P.1) gS := by
    rw [hgvs, matVecMul_add, matVecMul_smul, vecDot_add_left, vecDot_smul_left]
  set uu := (centeredPotential m v P.1 c).toFun x with huudef
  set uus := (centeredPotential m vstar P.1 (-c)).toFun x with huusdef
  have he : cutoffIntegrand a v vstar P c η x
      = uu * (vecDot P.2 gS - vecDot (matVecMul (a x) V) gS
            - (1/2) * vecDot (matVecMul (a x) P.1) gS)
        - uus * (vecDot (matVecMul (matTranspose (a x)) Vstar) gS
            + (1/2) * vecDot (matVecMul (matTranspose (a x)) P.1) gS) := by
    simp only [cutoffIntegrand]
    rw [← hgSdef, ← huudef, ← huusdef, hD1, hD2]
  have hcut_le : cutoffIntegrand a v vstar P c η x
      ≤ Kinf * |vecDot P.2 gS| + Kinf * |vecDot (matVecMul (a x) V) gS|
        + (1/2) * (Kinf * |vecDot (matVecMul (a x) P.1) gS|)
        + Kinf * |vecDot (matVecMul (matTranspose (a x)) Vstar) gS|
        + (1/2) * (Kinf * |vecDot (matVecMul (matTranspose (a x)) P.1) gS|) := by
    rw [he]; exact cutoff_abs_split hKinf0 hKv hKvs
  -- energy identity and final combination
  have henergy : energyIntegrand a v vstar P η x = (η x) ^ 2 * (EV + EVs) := by
    rw [energyIntegrand, hEVdef, hEVsdef, sqCutoff_apply]
  have hΘN : Kinf ^ 2 * N ≤ Θ * (Kinf ^ 2 * N) := by
    have h := mul_le_mul_of_nonneg_right hΘ1 hB1
    rwa [one_mul] at h
  clear_value EV EVs Msq N
  rw [henergy, sqCutoff_apply]
  have H3 := mul_le_mul_of_nonneg_left baP1 (by norm_num : (0:ℝ) ≤ 1/2)
  have H5 := mul_le_mul_of_nonneg_left baTP1 (by norm_num : (0:ℝ) ≤ 1/2)
  refine le_trans hcut_le
    (le_trans (add_le_add (add_le_add (add_le_add (add_le_add bP2 baV) H3) baVs) H5) ?_)
  linarith [hΘN]

end Cube

end

end Homogenization
