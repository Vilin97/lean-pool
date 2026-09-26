/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondOperator
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Equation
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Identification L2

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

private lemma hasCompactSupport_spatialDeriv {f : Vec3 → ℝ}
    (hf : HasCompactSupport f) (i : Fin 3) :
    HasCompactSupport (spatialDeriv f i) := by
  change HasCompactSupport (fun x => (fderiv ℝ f x) (basisVec i))
  exact hf.fderiv_apply (𝕜 := ℝ) (basisVec i)

private lemma tsupport_spatialDeriv_subset {f : Vec3 → ℝ} (i : Fin 3) :
    tsupport (spatialDeriv f i) ⊆ tsupport f := by
  exact closure_minimal
    (by
      intro x hx
      by_contra hxt
      exact hx (by simp [spatialDeriv,
        fderiv_of_notMem_tsupport (𝕜 := ℝ) hxt]))
    (isClosed_tsupport f)

private lemma deriv_swap {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i j : Fin 3) :
    spatialDeriv (spatialDeriv f j) i =
      spatialDeriv (spatialDeriv f i) j := by
  funext x
  simpa only [mixedSecond] using mixedSecond_swap hf i j x

private lemma spatialDeriv_congr {f g : Vec3 → ℝ} (h : f = g) (i : Fin 3) :
    spatialDeriv f i = spatialDeriv g i := by
  rw [h]

private lemma fourth_laplacian_mixed_swap {ψ : Vec3 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i j k : Fin 3) :
    (fun x => spatialDeriv (spatialDeriv
      (spatialDeriv (spatialDeriv ψ k) k) i) j x) =
      (fun x => spatialDeriv (spatialDeriv
        (spatialDeriv (spatialDeriv ψ j) i) k) k x) := by
  have hk : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv ψ k) :=
    contDiff_spatialDeriv_smooth hψ k
  have hkk : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv (spatialDeriv ψ k) k) :=
    contDiff_spatialDeriv_smooth hk k
  have hji : ContDiff ℝ (⊤ : ℕ∞)
      (spatialDeriv (spatialDeriv ψ j) i) :=
    contDiff_spatialDeriv_smooth (contDiff_spatialDeriv_smooth hψ j) i
  calc
    (fun x => spatialDeriv (spatialDeriv
        (spatialDeriv (spatialDeriv ψ k) k) i) j x) =
        (fun x => spatialDeriv (spatialDeriv
          (spatialDeriv (spatialDeriv ψ k) k) j) i x) :=
      (deriv_swap hkk i j).symm
    _ = (fun x => spatialDeriv (spatialDeriv
          (spatialDeriv (spatialDeriv ψ k) j) k) i x) := by
      exact spatialDeriv_congr (deriv_swap hk j k) i
    _ = (fun x => spatialDeriv (spatialDeriv
          (spatialDeriv (spatialDeriv ψ k) j) i) k x) := by
      exact deriv_swap (contDiff_spatialDeriv_smooth hk j) i k
    _ = (fun x => spatialDeriv (spatialDeriv
          (spatialDeriv (spatialDeriv ψ j) k) i) k x) := by
      exact spatialDeriv_congr (spatialDeriv_congr (deriv_swap hψ j k) i) k
    _ = (fun x => spatialDeriv (spatialDeriv
          (spatialDeriv (spatialDeriv ψ j) i) k) k x) := by
      exact spatialDeriv_congr
        (deriv_swap (contDiff_spatialDeriv_smooth hψ j) i k) k

private lemma local_ibp {u φ : Vec3 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (i : Fin 3) :
    ∫ x, u x * spatialDeriv φ i x =
      -∫ x, spatialDeriv u i x * φ x := by
  have hφd : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv φ i) :=
    contDiff_spatialDeriv_smooth hφ i
  have hud : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv u i) :=
    contDiff_spatialDeriv_smooth hu i
  have hφdc : HasCompactSupport (spatialDeriv φ i) :=
    hasCompactSupport_spatialDeriv hφc i
  have hleft : Integrable (fun x => u x * spatialDeriv φ i x) volume :=
    (hu.continuous.mul hφd.continuous).integrable_of_hasCompactSupport
      (hφdc.mul_left (f := u))
  have hright : Integrable (fun x => spatialDeriv u i x * φ x) volume :=
    (hud.continuous.mul hφ.continuous).integrable_of_hasCompactSupport
      (hφc.mul_left (f := spatialDeriv u i))
  have hprod : Integrable (fun x => u x * φ x) volume :=
    (hu.continuous.mul hφ.continuous).integrable_of_hasCompactSupport
      (hφc.mul_left (f := u))
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure Vec3)) (v := basisVec i) hright hleft hprod
    (fun x _ => hu.differentiable (by norm_num) x)
    (fun x _ => hφ.differentiable (by norm_num) x)
  simpa only [spatialDeriv] using h

private lemma hessian_laplacian_pairing {u ψ : Vec3 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (i j : Fin 3) :
    ∫ x, mixedSecond u i j x * spatialLaplacian ψ x =
      ∫ x, u x * spatialLaplacian (mixedSecond ψ i j) x := by
  have hψm : ContDiff ℝ (⊤ : ℕ∞) (mixedSecond ψ i j) :=
    contDiff_mixedSecond_smooth hψ i j
  have hψmc : HasCompactSupport (mixedSecond ψ i j) := by
    exact hasCompactSupport_spatialDeriv (hasCompactSupport_spatialDeriv hψc j) i
  have hleft (k : Fin 3) : Integrable
      (fun x => mixedSecond u i j x *
        spatialDeriv (spatialDeriv ψ k) k x) volume := by
    exact ((contDiff_mixedSecond_smooth hu i j).continuous.mul
      (contDiff_spatialDeriv_smooth
        (contDiff_spatialDeriv_smooth hψ k) k).continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_spatialDeriv
        (hasCompactSupport_spatialDeriv hψc k) k |>.mul_left
          (f := mixedSecond u i j))
  have hleftSum : ∫ x, mixedSecond u i j x * spatialLaplacian ψ x =
      ∑ k : Fin 3, ∫ x, mixedSecond u i j x *
        spatialDeriv (spatialDeriv ψ k) k x := by
    unfold spatialLaplacian
    rw [show (fun x => mixedSecond u i j x * ∑ k : Fin 3,
        spatialDeriv (spatialDeriv ψ k) k x) =
        (fun x => ∑ k : Fin 3, mixedSecond u i j x *
          spatialDeriv (spatialDeriv ψ k) k x) by
          funext x; rw [Finset.mul_sum]]
    rw [integral_finsetSum]
    intro k hk
    exact hleft k
  have hrightSum : ∫ x, u x * spatialLaplacian (mixedSecond ψ i j) x =
      ∑ k : Fin 3, ∫ x, u x * spatialDeriv (spatialDeriv
        (mixedSecond ψ i j) k) k x := by
    unfold spatialLaplacian
    rw [show (fun x => u x * ∑ k : Fin 3,
        spatialDeriv (spatialDeriv (mixedSecond ψ i j) k) k x) =
        (fun x => ∑ k : Fin 3, u x *
          spatialDeriv (spatialDeriv (mixedSecond ψ i j) k) k x) by
          funext x; rw [Finset.mul_sum]]
    rw [integral_finsetSum]
    intro k hk
    exact ((hu.continuous.mul
      (contDiff_spatialDeriv_smooth (contDiff_spatialDeriv_smooth hψm k)
        k).continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_spatialDeriv
        (hasCompactSupport_spatialDeriv hψmc k) k |>.mul_left (f := u)))
  rw [hleftSum, hrightSum]
  apply Finset.sum_congr rfl
  intro k hk
  have hφ := local_ibp (u := spatialDeriv u j)
    (φ := spatialDeriv (spatialDeriv ψ k) k)
    (contDiff_spatialDeriv_smooth hu j)
    (contDiff_spatialDeriv_smooth (contDiff_spatialDeriv_smooth hψ k) k)
    (hasCompactSupport_spatialDeriv
      (hasCompactSupport_spatialDeriv hψc k) k) i
  have hφi : HasCompactSupport
      (spatialDeriv (spatialDeriv (spatialDeriv ψ k) k) i) :=
    hasCompactSupport_spatialDeriv
      (hasCompactSupport_spatialDeriv
        (hasCompactSupport_spatialDeriv hψc k) k) i
  have hψi : ContDiff ℝ (⊤ : ℕ∞)
      (spatialDeriv (spatialDeriv (spatialDeriv ψ k) k) i) :=
    contDiff_spatialDeriv_smooth
      (contDiff_spatialDeriv_smooth (contDiff_spatialDeriv_smooth hψ k) k) i
  have hU := local_ibp hu hψi hφi j
  have hcomm := fourth_laplacian_mixed_swap hψ i j k
  have hφ' :
      ∫ x, spatialDeriv u j x *
          spatialDeriv (spatialDeriv (spatialDeriv ψ k) k) i x =
        -∫ x, mixedSecond u i j x *
          spatialDeriv (spatialDeriv ψ k) k x := by
    simpa only [mixedSecond] using hφ
  calc
    ∫ x, mixedSecond u i j x * spatialDeriv (spatialDeriv ψ k) k x =
        -∫ x, spatialDeriv u j x *
          spatialDeriv (spatialDeriv (spatialDeriv ψ k) k) i x := by
      calc
        _ = -(-∫ x, mixedSecond u i j x *
            spatialDeriv (spatialDeriv ψ k) k x) := by ring
        _ = _ := by rw [← hφ']
    _ = ∫ x, u x * spatialDeriv (spatialDeriv
          (spatialDeriv (spatialDeriv ψ k) k) i) j x := by
      exact hU.symm
    _ = ∫ x, u x * spatialDeriv (spatialDeriv
          (spatialDeriv (spatialDeriv ψ j) i) k) k x := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [congrFun hcomm x]
    _ = ∫ x, u x * spatialDeriv (spatialDeriv
          (mixedSecond ψ i j) k) k x := by
      rfl

private lemma smooth_distributional_identity {F ψ : Vec3 → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (i j : Fin 3) :
    ∫ x, mixedSecond (pressureNewtonianPotential F) i j x *
        spatialLaplacian ψ x =
      ∫ x, F x * mixedSecond ψ i j x := by
  have hU := pressureNewtonianPotential_smooth hF hFc
  have hpair := hessian_laplacian_pairing hU hψ hψc i j
  have htest : ContDiff ℝ (⊤ : ℕ∞) (mixedSecond ψ i j) :=
    contDiff_mixedSecond_smooth hψ i j
  have htestc : HasCompactSupport (mixedSecond ψ i j) := by
    exact hasCompactSupport_spatialDeriv (hasCompactSupport_spatialDeriv hψc j) i
  have hdist := pressureNewtonianPotential_distributional_pairing
    (hF.continuous.integrable_of_hasCompactSupport hFc) hFc htest htestc
  exact hpair.trans hdist

private lemma integral_eq_inner {f g : Vec3 → ℝ}
    (hf : MemLp f (2 : ℝ≥0∞) volume)
    (hg : MemLp g (2 : ℝ≥0∞) volume) :
    ∫ x, f x * g x =
      inner ℝ (MemLp.toLp f hf) (MemLp.toLp g hg) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]
  simp [RCLike.inner_apply]
  ring

/-- The indexed L² second-order operator satisfies the test-function
distributional identity on compactly supported smooth data and, by L²
continuity, on every L² class. -/
theorem rieszSecondL2_distributional_identity {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (g : rieszSecondL2) :
    ∫ x, rieszSecondL2MeasurableOperator hL2 g x *
        spatialLaplacian ψ x =
      ∫ x, (g : Vec3 → ℝ) x * mixedSecond ψ i j x := by
  have hψΔ : ContDiff ℝ (⊤ : ℕ∞) (spatialLaplacian ψ) :=
    contDiff_spatialLaplacian_smooth hψ
  have hψΔc : HasCompactSupport (spatialLaplacian ψ) := by
    change HasCompactSupport (fun x => ∑ k : Fin 3,
      spatialDeriv (spatialDeriv ψ k) k x)
    refine HasCompactSupport.of_support_subset_isCompact hψc.isCompact ?_
    intro x hx
    by_contra hxt
    apply hx
    refine Finset.sum_eq_zero (fun k _ => ?_)
    have hkn : x ∉ tsupport (spatialDeriv ψ k) := by
      exact fun hk => hxt (tsupport_spatialDeriv_subset k hk)
    simp only [spatialDeriv,
      fderiv_of_notMem_tsupport (𝕜 := ℝ) hkn, zero_apply]
  have hmix : ContDiff ℝ (⊤ : ℕ∞) (mixedSecond ψ i j) :=
    contDiff_mixedSecond_smooth hψ i j
  have hmixc : HasCompactSupport (mixedSecond ψ i j) := by
    exact hasCompactSupport_spatialDeriv (hasCompactSupport_spatialDeriv hψc j) i
  have hΔmem : MemLp (spatialLaplacian ψ) (2 : ℝ≥0∞) volume :=
    hψΔ.continuous.memLp_of_hasCompactSupport hψΔc
  have hmixmem : MemLp (mixedSecond ψ i j) (2 : ℝ≥0∞) volume :=
    hmix.continuous.memLp_of_hasCompactSupport hmixc
  let A : rieszSecondL2 → ℝ := fun v =>
    inner ℝ (rieszSecondL2Extension hL2 v) (MemLp.toLp _ hΔmem)
  let B : rieszSecondL2 → ℝ := fun v =>
    inner ℝ v (MemLp.toLp _ hmixmem)
  have hAcont : Continuous A := by
    dsimp [A]
    fun_prop
  have hBcont : Continuous B := by
    dsimp [B]
    fun_prop
  have hclosed : IsClosed {v : rieszSecondL2 | A v = B v} := by
    exact isClosed_eq hAcont hBcont
  have hdense : DenseRange
      ((fun s : {v : rieszSecondL2 // ∃ F : Vec3 → ℝ,
        v =ᵐ[volume] F ∧ HasCompactSupport F ∧
          ContDiff ℝ (⊤ : ℕ∞) F} => (s : rieszSecondL2))) := by
    exact (MeasureTheory.Lp.dense_hasCompactSupport_contDiff
      (F := ℝ) (p := (2 : ℝ≥0∞)) (μ := (volume : Measure Vec3))
      (by norm_num)).denseRange_val
  have hAB : A g = B g := by
    apply isClosed_property hdense hclosed
    rintro ⟨v, hv⟩
    change A v = B v
    rcases hv with ⟨F, hvF, hFc, hF⟩
    have hFmem : MemLp F (2 : ℝ≥0∞) volume :=
      hF.continuous.memLp_of_hasCompactSupport hFc
    have hv : v = MemLp.toLp F hFmem := by
      apply Lp.ext
      exact hvF.trans hFmem.coeFn_toLp.symm
    rw [hv]
    obtain ⟨hmem, hExt⟩ := rieszSecondL2Extension_smooth_hessian hL2 hF hFc
    have hsmooth := smooth_distributional_identity hF hFc hψ hψc i j
    have hleft := integral_eq_inner hmem hΔmem
    have hright := integral_eq_inner hFmem hmixmem
    change inner ℝ (rieszSecondL2Extension hL2 (MemLp.toLp F hFmem))
        (MemLp.toLp _ hΔmem) =
      inner ℝ (MemLp.toLp F hFmem) (MemLp.toLp _ hmixmem)
    rw [hExt]
    rw [← hleft, ← hright, hsmooth]
  have hAB' := hAB
  have hleft : ∫ x, rieszSecondL2MeasurableOperator hL2 g x *
        spatialLaplacian ψ x = A g := by
    dsimp [A]
    calc
      _ = ∫ x, (rieszSecondL2Extension hL2 g : Vec3 → ℝ) x *
          spatialLaplacian ψ x := by
        apply integral_congr_ae
        filter_upwards [rieszSecondL2MeasurableOperator_ae_eq_extension hL2 g] with x hx
        rw [hx]
      _ = inner ℝ (rieszSecondL2Extension hL2 g)
          (MemLp.toLp _ hΔmem) := by
        have hi := integral_eq_inner
          (Lp.memLp (rieszSecondL2Extension hL2 g)) hΔmem
        rw [Lp.toLp_coeFn] at hi
        exact hi
  have hright : ∫ x, (g : Vec3 → ℝ) x * mixedSecond ψ i j x = B g := by
    dsimp [B]
    have hi := integral_eq_inner (Lp.memLp g) hmixmem
    rw [Lp.toLp_coeFn] at hi
    exact hi
  exact hleft.trans (hAB'.trans hright.symm)

end CKN.Foundation.Euclidean
