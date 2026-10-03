/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.GradientChain
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.Assembly.SecondLast
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.IndyStepDownPartI
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.IndyStepDownPartI
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.TimeIBP.Cube

/-! with the actual initial corrector. The active flow derivative bound,
corrector size and positive initial gradient trace are separate named inputs.
No identity ansatz(0)=g is asserted. -/

@[expose] public section

noncomputable section
open scoped ContDiff
open Homogenization MeasureTheory AVenhance AVenhance.Infra.Section5
open AVenhance.Infra.Section5.Integration AVenhance.Infra.Section5.LeftToShow
namespace AVenhance.Infra.Section5.RelativeError

theorem RelativeInitial.abs_coord_le_sqrt_vecNormSq (v : Vec 2) (i : Fin 2) :
    |v i| ≤ Real.sqrt (vecNormSq v) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Homogenization.sq_apply_le_vecNormSq v i)

theorem RelativeInitial.mulVec_coord_le {Q : Matrix (Fin 2) (Fin 2) ℝ} {v : Vec 2}
    (hQ : ∀ i j, |Q i j| ≤ 2) (i : Fin 2) :
    |Q.mulVec v i| ≤ 4 * Real.sqrt (vecNormSq v) := by
  unfold Matrix.mulVec dotProduct
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have h (j : Fin 2) : |Q i j * v j| ≤ 2 * Real.sqrt (vecNormSq v) := by
    rw [abs_mul]
    exact mul_le_mul (hQ i j) (RelativeInitial.abs_coord_le_sqrt_vecNormSq v j)
      (abs_nonneg _) (by norm_num)
  calc ∑ j : Fin 2, |Q i j * v j| ≤ ∑ _j : Fin 2, 2 * Real.sqrt (vecNormSq v) :=
        Finset.sum_le_sum fun j _ => h j
    _ = _ := by simp; ring

/-- The active-flow operator bound used by implies the entrywise bound
in the derivative-row convention. -/
theorem relative_flowGrad_entry_le_two {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ)
    (hDX : ∀ y, ‖fderiv ℝ (I.xFlow hΦ m l 0) y‖ ≤ 2)
    (x : Vec 2) (i j : Fin 2) : |I.flowGrad hΦ m l 0 x i j| ≤ 2 := by
  let y := I.xFlowInv hΦ m l 0 x
  have hdiff := ((xFlow_spatial_contDiff_two I hΦ m l 0).differentiable (by norm_num) y).hasFDerivAt
  have hcomp := (ContinuousLinearMap.proj j : Vec 2 →L[ℝ] ℝ).hasFDerivAt.comp y hdiff
  have he : I.flowGrad hΦ m l 0 x i j =
      (fderiv ℝ (I.xFlow hΦ m l 0) y (basisVec i)) j := by
    change fderiv ℝ (fun z => I.xFlow hΦ m l 0 z j) y (basisVec i) = _
    change fderiv ℝ ((ContinuousLinearMap.proj j : Vec 2 →L[ℝ] ℝ) ∘
      I.xFlow hΦ m l 0) y (basisVec i) = _
    rw [hcomp.fderiv]
    rfl
  rw [he, ← Real.norm_eq_abs]
  calc _ ≤ ‖fderiv ℝ (I.xFlow hΦ m l 0) y (basisVec i)‖ := norm_le_pi_norm _ j
    _ ≤ ‖fderiv ℝ (I.xFlow hΦ m l 0) y‖ * ‖basisVec i‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 2 := by simpa only [basisVec, Pi.norm_single, norm_one, mul_one] using hDX y

/-- The initial corrector series has only the positive derivative of g.
The two-dimensional conversion costs 8 with entrywise |DX|<=2. -/
theorem relative_initial_corrector_bound {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ) (κ : ℝ)
    {g : Vec 2 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (T : ℝ → Vec 2 → ℝ) (hT0 : T 0 = g) {B K : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hChi : ∀ k, I.xiMK m k 0 ≠ 0 → ∀ x i,
      |I.chiTilde hΦ m κ k 0 x i| ≤ B)
    (hFlow2 : ∀ k, I.xiMK m k 0 ≠ 0 → ∀ x i j,
      |I.flowGrad hΦ m (lIdx β I.Λ m k) 0 x i j| ≤ 2)
    (hCutoff : ∑ k ∈ (I.xiMK_support_finite m 0).toFinset, |I.xiMK m k 0| ≤ K) :
    Real.sqrt (l2NormSq (fun x => ∑' k : ℤ, I.xiMK m k 0 *
      vecDot (I.chiTilde hΦ m κ k 0 x)
        (spaceGrad (fun y => T 0 (I.xFlow hΦ m (lIdx β I.Λ m k) 0 y))
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) 0 x)))) ≤
      (8 * B * K) * Real.sqrt (gradNormSq (spaceGrad g)) := by
  classical
  let s := (I.xiMK_support_finite m 0).toFinset
  let f : Vec 2 → ℝ := fun x => ∑' k : ℤ, I.xiMK m k 0 *
    vecDot (I.chiTilde hΦ m κ k 0 x)
      (spaceGrad (fun y => T 0 (I.xFlow hΦ m (lIdx β I.Λ m k) 0 y))
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) 0 x))
  have he (x : Vec 2) : f x = ∑ k ∈ s, I.xiMK m k 0 *
      vecDot (I.chiTilde hΦ m κ k 0 x)
        ((I.flowGrad hΦ m (lIdx β I.Λ m k) 0 x).mulVec (spaceGrad g x)) := by
    dsimp [f]
    rw [hT0]
    have hterms (k : ℤ) : spaceGrad
        (fun y => g (I.xFlow hΦ m (lIdx β I.Λ m k) 0 y))
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) 0 x) =
        (I.flowGrad hΦ m (lIdx β I.Λ m k) 0 x).mulVec (spaceGrad g x) := by
      funext j
      have h := G_eq_flowGrad_mulVec I hΦ m (fun _ => g) (lIdx β I.Λ m k) 0 x
        ((hg.differentiable (by simp) x).hasFDerivAt)
        (((xFlow_spatial_contDiff_two I hΦ m (lIdx β I.Λ m k) 0).differentiable
          (by norm_num) _).hasFDerivAt)
        ((xFlowDiffeo I hΦ m (lIdx β I.Λ m k) 0).right_inv x)
      exact congrFun h j
    simp_rw [hterms]
    exact tsum_eq_sum fun k hk => by
      have hz : I.xiMK m k 0 = 0 := by
        by_contra hn
        exact hk ((I.xiMK_support_finite m 0).mem_toFinset.mpr hn)
      rw [hz, zero_mul]
  have hb (x : Vec 2) : |f x| ≤ (8 * B * K) * Real.sqrt (vecNormSq (spaceGrad g x)) := by
    rw [he]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    have ht (k : ℤ) (hk : k ∈ s) :
        |I.xiMK m k 0 * vecDot (I.chiTilde hΦ m κ k 0 x)
          ((I.flowGrad hΦ m (lIdx β I.Λ m k) 0 x).mulVec (spaceGrad g x))| ≤
        |I.xiMK m k 0| * (8 * B * Real.sqrt (vecNormSq (spaceGrad g x))) := by
      have hn : I.xiMK m k 0 ≠ 0 := (I.xiMK_support_finite m 0).mem_toFinset.mp hk
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      unfold vecDot
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      calc ∑ i : Fin 2, |I.chiTilde hΦ m κ k 0 x i *
              ((I.flowGrad hΦ m (lIdx β I.Λ m k) 0 x).mulVec (spaceGrad g x)) i| ≤
          ∑ _i : Fin 2, B * (4 * Real.sqrt (vecNormSq (spaceGrad g x))) := by
            apply Finset.sum_le_sum
            intro i _
            rw [abs_mul]
            exact mul_le_mul (hChi k hn x i) (RelativeInitial.mulVec_coord_le (hFlow2 k hn x) i)
              (abs_nonneg _) hB
        _ = _ := by simp; ring
    calc _ ≤ ∑ k ∈ s, |I.xiMK m k 0| *
          (8 * B * Real.sqrt (vecNormSq (spaceGrad g x))) := Finset.sum_le_sum ht
      _ = (∑ k ∈ s, |I.xiMK m k 0|) *
          (8 * B * Real.sqrt (vecNormSq (spaceGrad g x))) := (Finset.sum_mul _ _ _).symm
      _ ≤ K * (8 * B * Real.sqrt (vecNormSq (spaceGrad g x))) :=
          mul_le_mul_of_nonneg_right hCutoff (by positivity)
      _ = _ := by ring
  have hfc : Continuous f := by
    exact continuous_ansatz_series I hΦ m κ (T := T) (t := 0)
      (by rw [hT0]; exact hg.of_le (by simp))
  have hgc : Continuous (fun x => vecNormSq (spaceGrad g x)) := by
    unfold vecNormSq vecDot
    exact continuous_finsetSum _ fun i _ =>
      ((hg.continuous_fderiv (by simp)).clm_apply continuous_const).mul
        ((hg.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hi : l2NormSq f ≤ (8 * B * K) ^ 2 * gradNormSq (spaceGrad g) := by
    unfold l2NormSq gradNormSq
    rw [← integral_const_mul]
    apply integral_mono (integrableOn_unitCube_of_continuous (hfc.pow 2))
      (integrableOn_unitCube_of_continuous (hgc.const_mul _))
    intro x
    have h := pow_le_pow_left₀ (abs_nonneg _) (hb x) 2
    rw [sq_abs, mul_pow, Real.sq_sqrt (vecNormSq_nonneg _)] at h
    exact h
  have hsqrt := Real.sqrt_le_sqrt hi
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity : 0 ≤ 8 * B * K)] at hsqrt
  exact hsqrt

end AVenhance.Infra.Section5.RelativeError
