/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.BasicLemmas
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Euclidean L2CZ -/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal Topology

/-!
# Euclidean `L²` Calderon-Zygmund helpers

This file starts the `q = 2` Euclidean Calderon-Zygmund discharge.  The main
identity will be the smooth compactly supported integration-by-parts formula
`‖D²u‖₂ = ‖Δu‖₂`; the lemmas below package coordinate derivatives in the
project's `Vec d`/`basisVec` convention and record the support and symmetry
facts needed by the IBP chain.
-/

noncomputable section

/-- Coordinate derivative in the `i`th `basisVec` direction. -/
def euclideanCoordDeriv {d : ℕ} (i : Fin d) (u : Vec d → ℝ) : Vec d → ℝ :=
  fun x => fderiv ℝ u x (basisVec i)

/-- The pointwise support of a coordinate derivative is contained in the
topological support of the original function. -/
theorem support_euclideanCoordDeriv_subset_tsupport {d : ℕ}
    (i : Fin d) (u : Vec d → ℝ) :
    Function.support (euclideanCoordDeriv i u) ⊆ tsupport u := by
  intro x hx
  exact
    (support_fderiv_subset (𝕜 := ℝ) (f := u)) <| by
      change fderiv ℝ u x ≠ 0
      intro hzero
      apply hx
      simp [euclideanCoordDeriv, hzero]

/-- Coordinate differentiation does not enlarge topological support. -/
theorem tsupport_euclideanCoordDeriv_subset_tsupport {d : ℕ}
    (i : Fin d) (u : Vec d → ℝ) :
    tsupport (euclideanCoordDeriv i u) ⊆ tsupport u :=
  closure_minimal
    (support_euclideanCoordDeriv_subset_tsupport i u) isClosed_closure

/-- Euclidean gradient expressed in the project's coordinate-vector convention. -/
def euclideanGradient {d : ℕ} (u : Vec d → ℝ) : Vec d → Vec d :=
  fun x i => euclideanCoordDeriv i u x

/-- Smoothness is preserved by squaring a scalar test function. -/
theorem contDiff_sq {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => u x ^ 2) := by
  simpa [pow_two] using hu.mul hu

/-- Compact support is preserved by squaring a scalar test function. -/
theorem hasCompactSupport_sq {d : ℕ} {u : Vec d → ℝ}
    (hu : HasCompactSupport u) :
    HasCompactSupport (fun x => u x ^ 2) := by
  simpa [pow_two, Pi.mul_apply] using! (hu.mul_right (f' := u))

/-- Squaring a scalar test function does not enlarge topological support. -/
theorem tsupport_sq_subset {d : ℕ} (u : Vec d → ℝ) :
    tsupport (fun x => u x ^ 2) ⊆ tsupport u := by
  simpa [pow_two, Pi.mul_apply] using
    (tsupport_mul_subset_left (f := u) (g := u))

/-- Coordinate derivative of a squared scalar test function. -/
theorem euclideanCoordDeriv_sq {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i : Fin d) (x : Vec d) :
    euclideanCoordDeriv i (fun y => u y ^ 2) x =
      2 * u x * euclideanCoordDeriv i u x := by
  unfold euclideanCoordDeriv
  have hd : DifferentiableAt ℝ u x := (hu.differentiable (by simp)) x
  have hpow :=
    congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec i))
      (fderiv_pow (𝕜 := ℝ) (f := u) (x := x) 2 hd)
  simpa [pow_one, two_nsmul, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
    using! hpow

/-- Euclidean gradient of a squared scalar test function. -/
theorem euclideanGradient_sq {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x : Vec d) :
    euclideanGradient (fun y => u y ^ 2) x =
      fun i => 2 * u x * euclideanGradient u x i := by
  ext i
  exact euclideanCoordDeriv_sq hu i x

/-- A function has zero Euclidean gradient outside its topological support. -/
theorem euclideanGradient_eq_zero_of_notMem_tsupport {d : ℕ}
    {u : Vec d → ℝ} {x : Vec d} (hx : x ∉ tsupport u) :
    euclideanGradient u x = 0 := by
  ext i
  simp [euclideanGradient, euclideanCoordDeriv,
    fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]

/-- Coordinate second derivative, differentiating first in `i` and then in `j`. -/
def euclideanCoordSecondDeriv {d : ℕ} (i j : Fin d) (u : Vec d → ℝ) : Vec d → ℝ :=
  fun x => fderiv ℝ (euclideanCoordDeriv i u) x (basisVec j)

/-- The pointwise support of a coordinate second derivative is contained in
the topological support of the original function. -/
theorem support_euclideanCoordSecondDeriv_subset_tsupport {d : ℕ}
    (i j : Fin d) (u : Vec d → ℝ) :
    Function.support (euclideanCoordSecondDeriv i j u) ⊆ tsupport u := by
  intro x hx
  exact
    tsupport_euclideanCoordDeriv_subset_tsupport i u
      (support_euclideanCoordDeriv_subset_tsupport j
        (euclideanCoordDeriv i u) hx)

/-- Coordinate second differentiation does not enlarge topological support. -/
theorem tsupport_euclideanCoordSecondDeriv_subset_tsupport {d : ℕ}
    (i j : Fin d) (u : Vec d → ℝ) :
    tsupport (euclideanCoordSecondDeriv i j u) ⊆ tsupport u :=
  closure_minimal
    (support_euclideanCoordSecondDeriv_subset_tsupport i j u) isClosed_closure

/-- Coordinate third derivative, differentiating successively in `i`, `j`, and `k`. -/
def euclideanCoordThirdDeriv {d : ℕ} (i j k : Fin d) (u : Vec d → ℝ) :
    Vec d → ℝ :=
  fun x => fderiv ℝ (euclideanCoordSecondDeriv i j u) x (basisVec k)

/-- Coordinate Laplacian, expressed as the trace of coordinate second derivatives. -/
def euclideanCoordLaplacian {d : ℕ} (u : Vec d → ℝ) : Vec d → ℝ :=
  fun x => ∑ i : Fin d, euclideanCoordSecondDeriv i i u x

/-- The pointwise support of the coordinate Laplacian is contained in the
topological support of the original function. -/
theorem support_euclideanCoordLaplacian_subset_tsupport {d : ℕ}
    (u : Vec d → ℝ) :
    Function.support (euclideanCoordLaplacian u) ⊆ tsupport u := by
  intro x hx
  by_contra hxt
  have hzero : ∀ i : Fin d, euclideanCoordSecondDeriv i i u x = 0 := by
    intro i
    by_contra hnonzero
    exact hxt (support_euclideanCoordSecondDeriv_subset_tsupport i i u hnonzero)
  apply hx
  simp [euclideanCoordLaplacian, hzero]

/-- The coordinate Laplacian does not enlarge topological support. -/
theorem tsupport_euclideanCoordLaplacian_subset_tsupport {d : ℕ}
    (u : Vec d → ℝ) :
    tsupport (euclideanCoordLaplacian u) ⊆ tsupport u :=
  closure_minimal
    (support_euclideanCoordLaplacian_subset_tsupport u) isClosed_closure

theorem contDiff_euclideanCoordDeriv {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanCoordDeriv i u) := by
  unfold euclideanCoordDeriv
  exact (hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem hasCompactSupport_euclideanCoordDeriv {d : ℕ} {u : Vec d → ℝ}
    (hu : HasCompactSupport u) (i : Fin d) :
    HasCompactSupport (euclideanCoordDeriv i u) := by
  unfold euclideanCoordDeriv
  exact hu.fderiv_apply (𝕜 := ℝ) (basisVec i)

/-- The squared Euclidean gradient norm of a smooth scalar test is continuous. -/
theorem continuous_vecNormSq_euclideanGradient_of_contDiff
    {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    Continuous (fun x => vecNormSq (euclideanGradient u x)) := by
  unfold vecNormSq vecDot euclideanGradient
  exact continuous_finsetSum Finset.univ fun i _ =>
    ((contDiff_euclideanCoordDeriv hu i).continuous).mul
      ((contDiff_euclideanCoordDeriv hu i).continuous)

/-- The squared Euclidean gradient norm of a compactly supported scalar test
is compactly supported. -/
theorem hasCompactSupport_vecNormSq_euclideanGradient
    {d : ℕ} {u : Vec d → ℝ}
    (hu : HasCompactSupport u) :
    HasCompactSupport (fun x => vecNormSq (euclideanGradient u x)) := by
  unfold vecNormSq vecDot euclideanGradient
  let F : Fin d → Vec d → ℝ :=
    fun i x => euclideanCoordDeriv i u x * euclideanCoordDeriv i u x
  have hF : ∀ i : Fin d, HasCompactSupport (F i) := by
    intro i
    exact (hasCompactSupport_euclideanCoordDeriv hu i).mul_right
  have hsum :
      ∀ s : Finset (Fin d),
        HasCompactSupport (fun x => s.sum fun i => F i x) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa [F] using!
          (HasCompactSupport.zero : HasCompactSupport (0 : Vec d → ℝ))
    | insert a s has ih =>
        simpa [Finset.sum_insert has, F] using! (hF a).add ih
  simpa [F] using hsum Finset.univ

theorem contDiff_euclideanCoordSecondDeriv {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanCoordSecondDeriv i j u) := by
  unfold euclideanCoordSecondDeriv
  exact contDiff_euclideanCoordDeriv (contDiff_euclideanCoordDeriv hu i) j

theorem hasCompactSupport_euclideanCoordSecondDeriv {d : ℕ} {u : Vec d → ℝ}
    (hu : HasCompactSupport u) (i j : Fin d) :
    HasCompactSupport (euclideanCoordSecondDeriv i j u) := by
  unfold euclideanCoordSecondDeriv
  exact hasCompactSupport_euclideanCoordDeriv
    (hasCompactSupport_euclideanCoordDeriv hu i) j

theorem contDiff_euclideanCoordLaplacian {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanCoordLaplacian u) := by
  unfold euclideanCoordLaplacian
  exact ContDiff.sum fun i _ => contDiff_euclideanCoordSecondDeriv hu i i

theorem hasCompactSupport_euclideanCoordLaplacian {d : ℕ} {u : Vec d → ℝ}
    (hu : HasCompactSupport u) :
    HasCompactSupport (euclideanCoordLaplacian u) := by
  classical
  unfold euclideanCoordLaplacian
  let f : Fin d → Vec d → ℝ := fun i x => euclideanCoordSecondDeriv i i u x
  have hs :
      ∀ s : Finset (Fin d),
        HasCompactSupport (fun x => s.sum fun i => f i x) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa [f] using!
          (HasCompactSupport.zero : HasCompactSupport (0 : Vec d → ℝ))
    | insert a s has ih =>
        have ha : HasCompactSupport (f a) := by
          simpa [f] using hasCompactSupport_euclideanCoordSecondDeriv hu a a
        simpa [Finset.sum_insert has, f] using! ha.add ih
  simpa [f] using hs Finset.univ

theorem euclideanCoordSecondDeriv_eq_fderiv_fderiv {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i j : Fin d) (x : Vec d) :
    euclideanCoordSecondDeriv i j u x =
      fderiv ℝ (fderiv ℝ u) x (basisVec j) (basisVec i) := by
  unfold euclideanCoordSecondDeriv euclideanCoordDeriv
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x := by
    exact
      ((hu.fderiv_right (m := 1)
        (by
          exact WithTop.coe_le_coe.2
            (show ((1 : ℕ∞) + 1) ≤ ⊤ from le_top))).differentiable
        (by norm_num)) x
  rw [fderiv_clm_apply]
  · simp
  · exact hfd
  · exact differentiableAt_const _

theorem euclideanCoordSecondDeriv_comm {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i j : Fin d) (x : Vec d) :
    euclideanCoordSecondDeriv i j u x =
      euclideanCoordSecondDeriv j i u x := by
  rw [euclideanCoordSecondDeriv_eq_fderiv_fderiv hu i j x,
    euclideanCoordSecondDeriv_eq_fderiv_fderiv hu j i x]
  exact (ContDiffAt.isSymmSndFDerivAt (hu.contDiffAt)
    (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 (show (2 : ℕ∞) ≤ ⊤ from le_top))).eq
        (basisVec j) (basisVec i)

theorem euclideanCoordSecondDeriv_comm_fun {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i j : Fin d) :
    euclideanCoordSecondDeriv i j u = euclideanCoordSecondDeriv j i u := by
  funext x
  exact euclideanCoordSecondDeriv_comm hu i j x

theorem contDiff_euclideanCoordThirdDeriv {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i j k : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanCoordThirdDeriv i j k u) := by
  unfold euclideanCoordThirdDeriv
  exact contDiff_euclideanCoordDeriv
    (contDiff_euclideanCoordSecondDeriv hu i j) k

theorem hasCompactSupport_euclideanCoordThirdDeriv {d : ℕ} {u : Vec d → ℝ}
    (hu : HasCompactSupport u) (i j k : Fin d) :
    HasCompactSupport (euclideanCoordThirdDeriv i j k u) := by
  unfold euclideanCoordThirdDeriv
  exact hasCompactSupport_euclideanCoordDeriv
    (hasCompactSupport_euclideanCoordSecondDeriv hu i j) k

/-- A smooth compactly supported scalar test has an `L²` Euclidean gradient on
any measurable restriction. -/
theorem memVectorL2_euclideanGradient_of_contDiff_hasCompactSupport
    {d : ℕ} {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφs : HasCompactSupport φ) :
    MemVectorL2 U (euclideanGradient φ) := by
  refine MeasureTheory.MemLp.of_eval ?_
  intro i
  have hcoord_cont : Continuous (fun x => euclideanGradient φ x i) := by
    simpa [euclideanGradient] using
      (contDiff_euclideanCoordDeriv hφ i).continuous
  have hcoord_supp :
      HasCompactSupport (fun x => euclideanGradient φ x i) := by
    simpa [euclideanGradient] using hasCompactSupport_euclideanCoordDeriv hφs i
  simpa [MemScalarL2, MemVectorL2, volumeMeasureOn] using
    (hcoord_cont.memLp_of_hasCompactSupport hcoord_supp).restrict U

theorem euclideanCoordThirdDeriv_diag_right_comm {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i j : Fin d) (x : Vec d) :
    euclideanCoordThirdDeriv i j j u x =
      euclideanCoordThirdDeriv j j i u x := by
  unfold euclideanCoordThirdDeriv
  have hcomm : euclideanCoordSecondDeriv i j u = euclideanCoordSecondDeriv j i u :=
    euclideanCoordSecondDeriv_comm_fun hu i j
  rw [hcomm]
  change euclideanCoordSecondDeriv i j (euclideanCoordDeriv j u) x =
    euclideanCoordSecondDeriv j i (euclideanCoordDeriv j u) x
  exact euclideanCoordSecondDeriv_comm (contDiff_euclideanCoordDeriv hu j) i j x

theorem integrable_mul_of_contDiff_hasCompactSupport_left {d : ℕ} {f g : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hfs : HasCompactSupport f) :
    Integrable (fun x : Vec d => f x * g x) := by
  have hf_cont : Continuous f := (hf.differentiable (by simp)).continuous
  have hg_cont : Continuous g := (hg.differentiable (by simp)).continuous
  exact ((hf_cont.mul hg_cont).integrable_of_hasCompactSupport hfs.mul_right)

theorem integrable_mul_of_contDiff_hasCompactSupport_right {d : ℕ} {f g : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgs : HasCompactSupport g) :
    Integrable (fun x : Vec d => f x * g x) := by
  have hf_cont : Continuous f := (hf.differentiable (by simp)).continuous
  have hg_cont : Continuous g := (hg.differentiable (by simp)).continuous
  exact ((hf_cont.mul hg_cont).integrable_of_hasCompactSupport hgs.mul_left)

theorem integral_mul_euclideanCoordDeriv_eq_neg_integral_euclideanCoordDeriv_mul
    {d : ℕ} {f g : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hfs : HasCompactSupport f)
    (i : Fin d) :
    ∫ x, f x * euclideanCoordDeriv i g x ∂volume =
      - ∫ x, euclideanCoordDeriv i f x * g x ∂volume := by
  have hf_diff : Differentiable ℝ f := hf.differentiable (by simp)
  have hg_diff : Differentiable ℝ g := hg.differentiable (by simp)
  have hfderiv_g : Integrable (fun x : Vec d => euclideanCoordDeriv i f x * g x) :=
    integrable_mul_of_contDiff_hasCompactSupport_left
      (contDiff_euclideanCoordDeriv hf i) hg
      (hasCompactSupport_euclideanCoordDeriv hfs i)
  have hf_gderiv : Integrable (fun x : Vec d => f x * euclideanCoordDeriv i g x) :=
    integrable_mul_of_contDiff_hasCompactSupport_left hf
      (contDiff_euclideanCoordDeriv hg i) hfs
  have hfg : Integrable (fun x : Vec d => f x * g x) :=
    integrable_mul_of_contDiff_hasCompactSupport_left hf hg hfs
  simpa [euclideanCoordDeriv] using
    (integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) (v := basisVec i)
      hfderiv_g hf_gderiv hfg
      (fun x _ => hf_diff.differentiableAt) (fun x _ => hg_diff.differentiableAt))

/-- Smooth compactly supported weak-solution test by `-Δu`.

For a compactly supported smooth scalar `u`, the weak pairing of `∇u` against
`∇(-Δu)` is exactly the `L²` norm of the coordinate Laplacian. This is the
integration-by-parts bridge used after the reflected weak equation supplies the
test `-Δu`. -/
theorem integral_vecDot_euclideanGradient_euclideanGradient_neg_laplacian_eq_laplacian_sq
    {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hu_supp : HasCompactSupport u) :
    ∫ x, vecDot (euclideanGradient u x)
          (euclideanGradient (fun y => -euclideanCoordLaplacian u y) x) ∂volume =
      ∫ x, (euclideanCoordLaplacian u x) ^ 2 ∂volume := by
  let L : Vec d → ℝ := euclideanCoordLaplacian u
  have hL : ContDiff ℝ (⊤ : ℕ∞) L := contDiff_euclideanCoordLaplacian hu
  have hcomp :
      ∀ i : Fin d,
        ∫ x, euclideanCoordDeriv i u x *
            euclideanCoordDeriv i (fun y => -L y) x ∂volume =
          ∫ x, euclideanCoordSecondDeriv i i u x * L x ∂volume := by
    intro i
    have h :=
      integral_mul_euclideanCoordDeriv_eq_neg_integral_euclideanCoordDeriv_mul
        (f := euclideanCoordDeriv i u) (g := fun y => -L y)
        (contDiff_euclideanCoordDeriv hu i) hL.neg
        (hasCompactSupport_euclideanCoordDeriv hu_supp i) i
    simpa [L, euclideanCoordSecondDeriv, integral_neg] using! h
  have hleftInt :
      ∀ i : Fin d,
        Integrable
          (fun x : Vec d =>
            euclideanCoordDeriv i u x *
              euclideanCoordDeriv i (fun y => -L y) x) volume := by
    intro i
    exact integrable_mul_of_contDiff_hasCompactSupport_left
      (contDiff_euclideanCoordDeriv hu i)
      (contDiff_euclideanCoordDeriv hL.neg i)
      (hasCompactSupport_euclideanCoordDeriv hu_supp i)
  have hrightInt :
      ∀ i : Fin d,
        Integrable
          (fun x : Vec d => euclideanCoordSecondDeriv i i u x * L x) volume := by
    intro i
    exact integrable_mul_of_contDiff_hasCompactSupport_left
      (contDiff_euclideanCoordSecondDeriv hu i i) hL
      (hasCompactSupport_euclideanCoordSecondDeriv hu_supp i i)
  calc
    ∫ x, vecDot (euclideanGradient u x)
          (euclideanGradient (fun y => -euclideanCoordLaplacian u y) x) ∂volume
        = ∫ x, ∑ i : Fin d, euclideanCoordDeriv i u x *
            euclideanCoordDeriv i (fun y => -L y) x ∂volume := by
            simp [vecDot, euclideanGradient, L]
    _ = ∑ i : Fin d,
          ∫ x, euclideanCoordDeriv i u x *
            euclideanCoordDeriv i (fun y => -L y) x ∂volume := by
          exact integral_finsetSum Finset.univ (fun i _ => hleftInt i)
    _ = ∑ i : Fin d,
          ∫ x, euclideanCoordSecondDeriv i i u x * L x ∂volume := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact hcomp i
    _ = ∫ x, ∑ i : Fin d, euclideanCoordSecondDeriv i i u x * L x ∂volume := by
          exact (integral_finsetSum Finset.univ (fun i _ => hrightInt i)).symm
    _ = ∫ x, (L x) ^ 2 ∂volume := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            simp [L, euclideanCoordLaplacian, pow_two, Finset.sum_mul]
    _ = ∫ x, (euclideanCoordLaplacian u x) ^ 2 ∂volume := by
          rfl

/-- Fixed-component `L²` Hessian identity on `ℝ^d` for smooth compact support.

This is the componentwise integration-by-parts brick behind the `q = 2`
Calderon-Zygmund identity: the square of the mixed second derivative equals,
after integration, the product of the two matching pure second derivatives. -/
theorem integral_euclideanCoordSecondDeriv_sq_eq_integral_diag_mul_diag {d : ℕ}
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hu_supp : HasCompactSupport u)
    (i j : Fin d) :
    ∫ x, (euclideanCoordSecondDeriv i j u x) ^ 2 ∂volume =
      ∫ x, euclideanCoordSecondDeriv i i u x *
        euclideanCoordSecondDeriv j j u x ∂volume := by
  have h1 :
      ∫ x, euclideanCoordSecondDeriv i j u x *
          euclideanCoordSecondDeriv i j u x ∂volume =
        - ∫ x, euclideanCoordThirdDeriv i j j u x *
          euclideanCoordDeriv i u x ∂volume := by
    simpa [euclideanCoordSecondDeriv, euclideanCoordThirdDeriv] using!
      (integral_mul_euclideanCoordDeriv_eq_neg_integral_euclideanCoordDeriv_mul
        (f := euclideanCoordSecondDeriv i j u) (g := euclideanCoordDeriv i u)
        (contDiff_euclideanCoordSecondDeriv hu i j)
        (contDiff_euclideanCoordDeriv hu i)
        (hasCompactSupport_euclideanCoordSecondDeriv hu_supp i j) j)
  have h2 :
      ∫ x, euclideanCoordSecondDeriv j j u x *
          euclideanCoordSecondDeriv i i u x ∂volume =
        - ∫ x, euclideanCoordThirdDeriv j j i u x *
          euclideanCoordDeriv i u x ∂volume := by
    simpa [euclideanCoordSecondDeriv, euclideanCoordThirdDeriv] using!
      (integral_mul_euclideanCoordDeriv_eq_neg_integral_euclideanCoordDeriv_mul
        (f := euclideanCoordSecondDeriv j j u) (g := euclideanCoordDeriv i u)
        (contDiff_euclideanCoordSecondDeriv hu j j)
        (contDiff_euclideanCoordDeriv hu i)
        (hasCompactSupport_euclideanCoordSecondDeriv hu_supp j j) i)
  calc
    ∫ x, (euclideanCoordSecondDeriv i j u x) ^ 2 ∂volume
        = ∫ x, euclideanCoordSecondDeriv i j u x *
            euclideanCoordSecondDeriv i j u x ∂volume := by
            simp [pow_two]
    _ = - ∫ x, euclideanCoordThirdDeriv i j j u x *
          euclideanCoordDeriv i u x ∂volume := h1
    _ = - ∫ x, euclideanCoordThirdDeriv j j i u x *
          euclideanCoordDeriv i u x ∂volume := by
          congr 1
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            change euclideanCoordThirdDeriv i j j u x * euclideanCoordDeriv i u x =
              euclideanCoordThirdDeriv j j i u x * euclideanCoordDeriv i u x
            rw [euclideanCoordThirdDeriv_diag_right_comm hu i j x]
    _ = ∫ x, euclideanCoordSecondDeriv j j u x *
          euclideanCoordSecondDeriv i i u x ∂volume := by
          rw [← h2]
    _ = ∫ x, euclideanCoordSecondDeriv i i u x *
          euclideanCoordSecondDeriv j j u x ∂volume := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by ring

/-- Smooth compactly supported Euclidean `L²` Calderon-Zygmund identity in
coordinate form.

The sum of squared coordinate Hessian components has the same integral as the
square of the coordinate Laplacian. This is the `q = 2` replacement for the
Euclidean Calderon-Zygmund citation. -/
theorem integral_sum_euclideanCoordSecondDeriv_sq_eq_integral_euclideanCoordLaplacian_sq
    {d : ℕ} {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hu_supp : HasCompactSupport u) :
    (∑ i : Fin d, ∑ j : Fin d,
      ∫ x, (euclideanCoordSecondDeriv i j u x) ^ 2 ∂volume) =
      ∫ x, (euclideanCoordLaplacian u x) ^ 2 ∂volume := by
  let f : Fin d → Fin d → Vec d → ℝ :=
    fun i j x => euclideanCoordSecondDeriv i i u x *
      euclideanCoordSecondDeriv j j u x
  have hdiag_int : ∀ i j : Fin d, Integrable (f i j) := by
    intro i j
    exact integrable_mul_of_contDiff_hasCompactSupport_left
      (contDiff_euclideanCoordSecondDeriv hu i i)
      (contDiff_euclideanCoordSecondDeriv hu j j)
      (hasCompactSupport_euclideanCoordSecondDeriv hu_supp i i)
  have hsum_int : ∀ i : Fin d, Integrable (fun x : Vec d => ∑ j : Fin d, f i j x) := by
    intro i
    exact integrable_finsetSum Finset.univ (fun j _ => hdiag_int i j)
  calc
    (∑ i : Fin d, ∑ j : Fin d,
      ∫ x, (euclideanCoordSecondDeriv i j u x) ^ 2 ∂volume)
        = ∑ i : Fin d, ∑ j : Fin d, ∫ x, f i j x ∂volume := by
            apply Finset.sum_congr rfl
            intro i _hi
            apply Finset.sum_congr rfl
            intro j _hj
            exact integral_euclideanCoordSecondDeriv_sq_eq_integral_diag_mul_diag
              hu hu_supp i j
    _ = ∑ i : Fin d, ∫ x, ∑ j : Fin d, f i j x ∂volume := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact (integral_finsetSum Finset.univ
            (f := fun j x => f i j x) (fun j _ => hdiag_int i j)).symm
    _ = ∫ x, ∑ i : Fin d, ∑ j : Fin d, f i j x ∂volume := by
          exact (integral_finsetSum Finset.univ
            (f := fun i x => ∑ j : Fin d, f i j x) (fun i _ => hsum_int i)).symm
    _ = ∫ x, (euclideanCoordLaplacian u x) ^ 2 ∂volume := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            symm
            simp [euclideanCoordLaplacian, f, pow_two, Finset.sum_mul_sum]

/-- Smooth compactly supported weak Euclidean CZ identity.

If a smooth compactly supported `u` satisfies the weak equation
`∫ ∇u · ∇φ = ∫ f φ` against all compactly supported smooth tests, then the
coordinate Hessian energy is obtained by testing with `φ = -Δu`. This isolates
the analytic bridge still needed for nonsmooth reflected Neumann solutions:
density/mollification must produce this smooth weak-equation situation. -/
theorem integral_sum_euclideanCoordSecondDeriv_sq_eq_integral_forcing_mul_neg_laplacian
    {d : ℕ} {u f : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hu_supp : HasCompactSupport u)
    (hweak :
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        ∫ x, vecDot (euclideanGradient u x) (euclideanGradient φ x) ∂volume =
          ∫ x, f x * φ x ∂volume) :
    (∑ i : Fin d, ∑ j : Fin d,
      ∫ x, (euclideanCoordSecondDeriv i j u x) ^ 2 ∂volume) =
      ∫ x, f x * (-euclideanCoordLaplacian u x) ∂volume := by
  have hL : ContDiff ℝ (⊤ : ℕ∞) (euclideanCoordLaplacian u) :=
    contDiff_euclideanCoordLaplacian hu
  have hLs : HasCompactSupport (euclideanCoordLaplacian u) :=
    hasCompactSupport_euclideanCoordLaplacian hu_supp
  calc
    (∑ i : Fin d, ∑ j : Fin d,
      ∫ x, (euclideanCoordSecondDeriv i j u x) ^ 2 ∂volume)
        = ∫ x, (euclideanCoordLaplacian u x) ^ 2 ∂volume := by
            exact
              integral_sum_euclideanCoordSecondDeriv_sq_eq_integral_euclideanCoordLaplacian_sq
                hu hu_supp
    _ = ∫ x, vecDot (euclideanGradient u x)
          (euclideanGradient (fun y => -euclideanCoordLaplacian u y) x) ∂volume := by
            exact
              (integral_vecDot_euclideanGradient_euclideanGradient_neg_laplacian_eq_laplacian_sq
                hu hu_supp).symm
    _ = ∫ x, f x * (-euclideanCoordLaplacian u x) ∂volume := by
            simpa using
              hweak (fun y => -euclideanCoordLaplacian u y) hL.neg hLs.neg

/-- Local-support variant of the smooth weak Euclidean CZ identity.

It is enough for the weak equation to hold against tests supported in `U`,
provided the potential itself has topological support in `U`; the test
`-Δu` is then still supported in `U`. -/
theorem integral_sum_euclideanCoordSecondDeriv_sq_eq_integral_forcing_mul_neg_laplacian_of_tsupport_subset
    {d : ℕ} {U : Set (Vec d)} {u f : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hu_supp : HasCompactSupport u)
    (hu_sub : tsupport u ⊆ U)
    (hweak :
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ U →
        ∫ x, vecDot (euclideanGradient u x) (euclideanGradient φ x) ∂volume =
          ∫ x, f x * φ x ∂volume) :
    (∑ i : Fin d, ∑ j : Fin d,
      ∫ x, (euclideanCoordSecondDeriv i j u x) ^ 2 ∂volume) =
      ∫ x, f x * (-euclideanCoordLaplacian u x) ∂volume := by
  have hL : ContDiff ℝ (⊤ : ℕ∞) (euclideanCoordLaplacian u) :=
    contDiff_euclideanCoordLaplacian hu
  have hLs : HasCompactSupport (euclideanCoordLaplacian u) :=
    hasCompactSupport_euclideanCoordLaplacian hu_supp
  have hL_sub :
      tsupport (fun y => -euclideanCoordLaplacian u y) ⊆ U := by
    change tsupport (-(euclideanCoordLaplacian u)) ⊆ U
    rw [tsupport_neg]
    exact (tsupport_euclideanCoordLaplacian_subset_tsupport u).trans hu_sub
  calc
    (∑ i : Fin d, ∑ j : Fin d,
      ∫ x, (euclideanCoordSecondDeriv i j u x) ^ 2 ∂volume)
        = ∫ x, (euclideanCoordLaplacian u x) ^ 2 ∂volume := by
            exact
              integral_sum_euclideanCoordSecondDeriv_sq_eq_integral_euclideanCoordLaplacian_sq
                hu hu_supp
    _ = ∫ x, vecDot (euclideanGradient u x)
          (euclideanGradient (fun y => -euclideanCoordLaplacian u y) x) ∂volume := by
            exact
              (integral_vecDot_euclideanGradient_euclideanGradient_neg_laplacian_eq_laplacian_sq
                hu hu_supp).symm
    _ = ∫ x, f x * (-euclideanCoordLaplacian u x) ∂volume := by
            simpa using
              hweak (fun y => -euclideanCoordLaplacian u y) hL.neg hLs.neg hL_sub

/-- Smooth compactly supported Euclidean CZ estimate in Cauchy-Schwarz form.

This is the estimate produced by the weak `-Δu` test before cancelling the
common Laplacian factor. It is the most stable form for the later
density/reflection bridge, because it separates the weak-equation step from the
final square-root algebra. -/
theorem integral_sum_euclideanCoordSecondDeriv_sq_le_forcing_l2_mul_laplacian_l2
    {d : ℕ} {u f : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hu_supp : HasCompactSupport u)
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) volume)
    (hweak :
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        ∫ x, vecDot (euclideanGradient u x) (euclideanGradient φ x) ∂volume =
          ∫ x, f x * φ x ∂volume) :
    (∑ i : Fin d, ∑ j : Fin d,
      ∫ x, (euclideanCoordSecondDeriv i j u x) ^ 2 ∂volume) ≤
      (∫ x, ‖f x‖ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) *
        (∫ x, ‖euclideanCoordLaplacian u x‖ ^ (2 : ℝ) ∂volume) ^
          (1 / (2 : ℝ)) := by
  let L : Vec d → ℝ := euclideanCoordLaplacian u
  have hLcont : Continuous L := (contDiff_euclideanCoordLaplacian hu).continuous
  have hLs : HasCompactSupport L := hasCompactSupport_euclideanCoordLaplacian hu_supp
  have hf_ofReal : MeasureTheory.MemLp f (ENNReal.ofReal (2 : ℝ)) volume := by
    simpa using hf
  have hLmem : MeasureTheory.MemLp L (2 : ℝ≥0∞) volume := by
    simpa [L] using hLcont.memLp_of_hasCompactSupport hLs
  have hLmem_ofReal : MeasureTheory.MemLp L (ENNReal.ofReal (2 : ℝ)) volume := by
    simpa using hLmem
  have hcz_eq :
      (∑ i : Fin d, ∑ j : Fin d,
        ∫ x, (euclideanCoordSecondDeriv i j u x) ^ 2 ∂volume) =
        ∫ x, f x * (-L x) ∂volume := by
    simpa [L] using
      integral_sum_euclideanCoordSecondDeriv_sq_eq_integral_forcing_mul_neg_laplacian
        hu hu_supp hweak
  have habs :
      ∫ x, f x * (-L x) ∂volume ≤
        ∫ x, ‖f x‖ * ‖L x‖ ∂volume := by
    calc
      ∫ x, f x * (-L x) ∂volume
          ≤ |∫ x, f x * (-L x) ∂volume| := le_abs_self _
      _ ≤ ∫ x, ‖f x * (-L x)‖ ∂volume := by
            exact norm_integral_le_integral_norm (fun x => f x * (-L x))
      _ = ∫ x, ‖f x‖ * ‖L x‖ ∂volume := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x => by
              simp
  have hholder :
      ∫ x, ‖f x‖ * ‖L x‖ ∂volume ≤
        (∫ x, ‖f x‖ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) *
          (∫ x, ‖L x‖ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) := by
    exact MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
      (μ := volume) (f := f) (g := L)
      Real.HolderConjugate.two_two hf_ofReal hLmem_ofReal
  calc
    (∑ i : Fin d, ∑ j : Fin d,
      ∫ x, (euclideanCoordSecondDeriv i j u x) ^ 2 ∂volume)
        = ∫ x, f x * (-L x) ∂volume := hcz_eq
    _ ≤ ∫ x, ‖f x‖ * ‖L x‖ ∂volume := habs
    _ ≤ (∫ x, ‖f x‖ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) *
        (∫ x, ‖euclideanCoordLaplacian u x‖ ^ (2 : ℝ) ∂volume) ^
          (1 / (2 : ℝ)) := by
          simpa [L] using hholder

private theorem le_of_le_sqrt_mul_sqrt_self {A H : ℝ}
    (hA : 0 ≤ A) (hH : 0 ≤ H)
    (h : H ≤ Real.sqrt A * Real.sqrt H) :
    H ≤ A := by
  by_cases hzero : H = 0
  · simpa [hzero] using hA
  have hpos : 0 < H := lt_of_le_of_ne hH (Ne.symm hzero)
  have hsquare :
      H * H ≤ (Real.sqrt A * Real.sqrt H) * (Real.sqrt A * Real.sqrt H) :=
    mul_self_le_mul_self hH h
  have hrhs :
      (Real.sqrt A * Real.sqrt H) * (Real.sqrt A * Real.sqrt H) = A * H := by
    calc
      (Real.sqrt A * Real.sqrt H) * (Real.sqrt A * Real.sqrt H)
          = (Real.sqrt A * Real.sqrt A) * (Real.sqrt H * Real.sqrt H) := by ring
      _ = A * H := by
          rw [Real.mul_self_sqrt hA, Real.mul_self_sqrt hH]
  have hsq : H * H ≤ A * H := by
    calc
      H * H ≤ (Real.sqrt A * Real.sqrt H) * (Real.sqrt A * Real.sqrt H) := hsquare
      _ = A * H := hrhs
  nlinarith

/-- Smooth compactly supported Euclidean `L²` Calderon-Zygmund estimate after
cancelling the common Laplacian factor. -/
theorem integral_sum_euclideanCoordSecondDeriv_sq_le_forcing_l2
    {d : ℕ} {u f : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hu_supp : HasCompactSupport u)
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) volume)
    (hweak :
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        ∫ x, vecDot (euclideanGradient u x) (euclideanGradient φ x) ∂volume =
          ∫ x, f x * φ x ∂volume) :
    (∑ i : Fin d, ∑ j : Fin d,
      ∫ x, (euclideanCoordSecondDeriv i j u x) ^ 2 ∂volume) ≤
      ∫ x, ‖f x‖ ^ (2 : ℝ) ∂volume := by
  let H : ℝ :=
    ∑ i : Fin d, ∑ j : Fin d,
      ∫ x, (euclideanCoordSecondDeriv i j u x) ^ 2 ∂volume
  let A : ℝ := ∫ x, (f x) ^ 2 ∂volume
  let L : Vec d → ℝ := euclideanCoordLaplacian u
  have hidentity :
      H = ∫ x, (L x) ^ 2 ∂volume := by
    simpa [H, L] using
      integral_sum_euclideanCoordSecondDeriv_sq_eq_integral_euclideanCoordLaplacian_sq
        hu hu_supp
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact MeasureTheory.integral_nonneg fun x => sq_nonneg (f x)
  have hH_nonneg : 0 ≤ H := by
    rw [hidentity]
    exact MeasureTheory.integral_nonneg fun x => sq_nonneg (L x)
  have hbase0 :
      H ≤ A ^ (1 / (2 : ℝ)) *
          (∫ x, (L x) ^ 2 ∂volume) ^ (1 / (2 : ℝ)) := by
    simpa [H, A, L, Real.norm_eq_abs, pow_two] using
      integral_sum_euclideanCoordSecondDeriv_sq_le_forcing_l2_mul_laplacian_l2
        hu hu_supp hf hweak
  have hbase :
      H ≤ A ^ (1 / (2 : ℝ)) * H ^ (1 / (2 : ℝ)) := by
    rwa [← hidentity] at hbase0
  have hbase_sqrt : H ≤ Real.sqrt A * Real.sqrt H := by
    simpa [Real.sqrt_eq_rpow] using hbase
  have hfinal : H ≤ A :=
    le_of_le_sqrt_mul_sqrt_self hA_nonneg hH_nonneg hbase_sqrt
  simpa [H, A, Real.norm_eq_abs, pow_two] using hfinal

/-- Local-support variant of the smooth compactly supported Euclidean CZ
estimate.

This is the Cauchy-Schwarz estimate in the exact form needed after reflection:
the weak equation is required only for smooth compactly supported tests whose
topological support stays in `U`. -/
theorem integral_sum_euclideanCoordSecondDeriv_sq_le_forcing_l2_mul_laplacian_l2_of_tsupport_subset
    {d : ℕ} {U : Set (Vec d)} {u f : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hu_supp : HasCompactSupport u)
    (hu_sub : tsupport u ⊆ U)
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) volume)
    (hweak :
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ U →
        ∫ x, vecDot (euclideanGradient u x) (euclideanGradient φ x) ∂volume =
          ∫ x, f x * φ x ∂volume) :
    (∑ i : Fin d, ∑ j : Fin d,
      ∫ x, (euclideanCoordSecondDeriv i j u x) ^ 2 ∂volume) ≤
      (∫ x, ‖f x‖ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) *
        (∫ x, ‖euclideanCoordLaplacian u x‖ ^ (2 : ℝ) ∂volume) ^
          (1 / (2 : ℝ)) := by
  let L : Vec d → ℝ := euclideanCoordLaplacian u
  have hLcont : Continuous L := (contDiff_euclideanCoordLaplacian hu).continuous
  have hLs : HasCompactSupport L := hasCompactSupport_euclideanCoordLaplacian hu_supp
  have hf_ofReal : MeasureTheory.MemLp f (ENNReal.ofReal (2 : ℝ)) volume := by
    simpa using hf
  have hLmem : MeasureTheory.MemLp L (2 : ℝ≥0∞) volume := by
    simpa [L] using hLcont.memLp_of_hasCompactSupport hLs
  have hLmem_ofReal : MeasureTheory.MemLp L (ENNReal.ofReal (2 : ℝ)) volume := by
    simpa using hLmem
  have hcz_eq :
      (∑ i : Fin d, ∑ j : Fin d,
        ∫ x, (euclideanCoordSecondDeriv i j u x) ^ 2 ∂volume) =
        ∫ x, f x * (-L x) ∂volume := by
    simpa [L] using
      integral_sum_euclideanCoordSecondDeriv_sq_eq_integral_forcing_mul_neg_laplacian_of_tsupport_subset
        hu hu_supp hu_sub hweak
  have habs :
      ∫ x, f x * (-L x) ∂volume ≤
        ∫ x, ‖f x‖ * ‖L x‖ ∂volume := by
    calc
      ∫ x, f x * (-L x) ∂volume
          ≤ |∫ x, f x * (-L x) ∂volume| := le_abs_self _
      _ ≤ ∫ x, ‖f x * (-L x)‖ ∂volume := by
            exact norm_integral_le_integral_norm (fun x => f x * (-L x))
      _ = ∫ x, ‖f x‖ * ‖L x‖ ∂volume := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x => by
              simp
  have hholder :
      ∫ x, ‖f x‖ * ‖L x‖ ∂volume ≤
        (∫ x, ‖f x‖ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) *
          (∫ x, ‖L x‖ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) := by
    exact MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
      (μ := volume) (f := f) (g := L)
      Real.HolderConjugate.two_two hf_ofReal hLmem_ofReal
  calc
    (∑ i : Fin d, ∑ j : Fin d,
      ∫ x, (euclideanCoordSecondDeriv i j u x) ^ 2 ∂volume)
        = ∫ x, f x * (-L x) ∂volume := hcz_eq
    _ ≤ ∫ x, ‖f x‖ * ‖L x‖ ∂volume := habs
    _ ≤ (∫ x, ‖f x‖ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)) *
        (∫ x, ‖euclideanCoordLaplacian u x‖ ^ (2 : ℝ) ∂volume) ^
          (1 / (2 : ℝ)) := by
          simpa [L] using hholder

/-- Local-support variant of the cancelled smooth compactly supported
Euclidean `L²` Calderon-Zygmund estimate. -/
theorem integral_sum_euclideanCoordSecondDeriv_sq_le_forcing_l2_of_tsupport_subset
    {d : ℕ} {U : Set (Vec d)} {u f : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hu_supp : HasCompactSupport u)
    (hu_sub : tsupport u ⊆ U)
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) volume)
    (hweak :
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ U →
        ∫ x, vecDot (euclideanGradient u x) (euclideanGradient φ x) ∂volume =
          ∫ x, f x * φ x ∂volume) :
    (∑ i : Fin d, ∑ j : Fin d,
      ∫ x, (euclideanCoordSecondDeriv i j u x) ^ 2 ∂volume) ≤
      ∫ x, ‖f x‖ ^ (2 : ℝ) ∂volume := by
  let H : ℝ :=
    ∑ i : Fin d, ∑ j : Fin d,
      ∫ x, (euclideanCoordSecondDeriv i j u x) ^ 2 ∂volume
  let A : ℝ := ∫ x, (f x) ^ 2 ∂volume
  let L : Vec d → ℝ := euclideanCoordLaplacian u
  have hidentity :
      H = ∫ x, (L x) ^ 2 ∂volume := by
    simpa [H, L] using
      integral_sum_euclideanCoordSecondDeriv_sq_eq_integral_euclideanCoordLaplacian_sq
        hu hu_supp
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact MeasureTheory.integral_nonneg fun x => sq_nonneg (f x)
  have hH_nonneg : 0 ≤ H := by
    rw [hidentity]
    exact MeasureTheory.integral_nonneg fun x => sq_nonneg (L x)
  have hbase0 :
      H ≤ A ^ (1 / (2 : ℝ)) *
          (∫ x, (L x) ^ 2 ∂volume) ^ (1 / (2 : ℝ)) := by
    simpa [H, A, L, Real.norm_eq_abs, pow_two] using
      integral_sum_euclideanCoordSecondDeriv_sq_le_forcing_l2_mul_laplacian_l2_of_tsupport_subset
        hu hu_supp hu_sub hf hweak
  have hbase :
      H ≤ A ^ (1 / (2 : ℝ)) * H ^ (1 / (2 : ℝ)) := by
    rwa [← hidentity] at hbase0
  have hbase_sqrt : H ≤ Real.sqrt A * Real.sqrt H := by
    simpa [Real.sqrt_eq_rpow] using hbase
  have hfinal : H ≤ A :=
    le_of_le_sqrt_mul_sqrt_self hA_nonneg hH_nonneg hbase_sqrt
  simpa [H, A, Real.norm_eq_abs, pow_two] using hfinal

end

end Homogenization
