/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Ambient.Euclidean
public import LeanPool.CoarseGraining.Homogenization.Ambient.CoefficientField
public import LeanPool.CoarseGraining.Homogenization.Geometry.SignedPermutation
public import LeanPool.CoarseGraining.Homogenization.Geometry.Translation
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Algebra.Support

/-! # Coarse -/

@[expose] public section

namespace Homogenization.Source.Coarse

open MeasureTheory

def euclideanBall {d : ℕ} (R : ℝ) : Set (Vec d) :=
  {x | euclideanNorm x < R}

structure SmoothCompactProbe {d : ℕ} (φ : Vec d → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) φ
  compact : HasCompactSupport φ

def Carrier (d : ℕ) :=
  {a : CoeffField d //
    (∀ i j, Measurable (fun x : Vec d => a x i j)) ∧
    ∀ R : ℝ, 1 ≤ R → ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ x, x ∈ euclideanBall R → IsEllipticMatrix ε ε⁻¹ (a x)}

instance instCoeFunCarrier (d : ℕ) : CoeFun (Carrier d) (fun _ => CoeffField d) where
  coe a := a.1

noncomputable def bilinearTest {d : ℕ} (e e' : Vec d)
    (φ : Vec d → ℝ) (a : Carrier d) : ℝ :=
  ∫ x, vecDot e' (matVecMul (a x) e) * φ x ∂volume
def localSigma {d : ℕ} (U : Set (Vec d)) (_hU : MeasurableSet U) :
    MeasurableSpace (Carrier d) :=
  MeasurableSpace.generateFrom
    {s | ∃ (e e' : Vec d) (φ : Vec d → ℝ),
      SmoothCompactProbe φ ∧ tsupport φ ⊆ U ∧
      ∃ t : Set ℝ, MeasurableSet t ∧ s = bilinearTest e e' φ ⁻¹' t}
def globalSigma (d : ℕ) : MeasurableSpace (Carrier d) :=
  localSigma Set.univ MeasurableSet.univ

instance instMeasurableSpaceCarrier (d : ℕ) : MeasurableSpace (Carrier d) :=
  globalSigma d

def IsLocalObservable {d : ℕ} (U : Set (Vec d)) (hU : MeasurableSet U)
    {β : Type*} [MeasurableSpace β] (X : Carrier d → β) : Prop :=
  @Measurable (Carrier d) β (localSigma U hU) _ X

private theorem euclideanNorm_add_le {d : ℕ} (x y : Vec d) :
    euclideanNorm (x + y) ≤ euclideanNorm x + euclideanNorm y := by
  rw [euclideanNorm_eq_norm_ofVec, euclideanNorm_eq_norm_ofVec,
    euclideanNorm_eq_norm_ofVec]
  change ‖WithLp.toLp 2 (x + y)‖ ≤ ‖WithLp.toLp 2 x‖ + ‖WithLp.toLp 2 y‖
  rw [WithLp.toLp_add]
  exact norm_add_le _ _

private theorem vecNormSq_matVecMul_signedPermutation {d : ℕ} {R : Mat d}
    (hR : IsSignedPermutationMatrix R) (x : Vec d) :
    vecNormSq (matVecMul R x) = vecNormSq x := by
  classical
  rcases hR with ⟨σ, s, hs, hR⟩
  have happly : ∀ j, matVecMul R x (σ j) = s j * x j := by
    intro j
    unfold matVecMul
    rw [Finset.sum_eq_single j]
    · rw [hR (σ j) j]
      simp
    · intro k _ hkj
      rw [hR (σ j) k]
      have hne : σ j ≠ σ k := fun h => hkj (σ.injective h.symm)
      simp [hne]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  have hsq :
      ∑ i, (matVecMul R x i) ^ 2 = ∑ i, x i ^ 2 := by
    calc
      ∑ i, (matVecMul R x i) ^ 2 =
          ∑ j, (matVecMul R x (σ j)) ^ 2 := (Equiv.sum_comp σ _).symm
      _ = ∑ j, (s j * x j) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [happly]
      _ = ∑ j, x j ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        rcases hs j with hj | hj <;> rw [hj] <;> ring
  simpa [vecNormSq, vecDot, pow_two] using hsq

private theorem euclideanNorm_matVecMul_signedPermutation {d : ℕ} {R : Mat d}
    (hR : IsSignedPermutationMatrix R) (x : Vec d) :
    euclideanNorm (matVecMul R x) = euclideanNorm x := by
  rw [← sq_eq_sq₀ (euclideanNorm_nonneg _) (euclideanNorm_nonneg _),
    euclideanNorm_sq, euclideanNorm_sq]
  simpa [vecNormSq, vecDot, pow_two] using vecNormSq_matVecMul_signedPermutation hR x

private theorem isEllipticMatrix_rotate {d : ℕ} {lam Lam : ℝ} {R A : Mat d}
    (hR : IsSignedPermutationMatrix R) (hA : IsEllipticMatrix lam Lam A) :
    IsEllipticMatrix lam Lam (matTranspose R * A * R) := by
  have hdetA : IsUnit A.det := isUnit_det_of_isEllipticMatrix hA
  have hdetR : IsUnit R.det := isUnit_iff_ne_zero.mpr hR.det_ne_zero
  have hdetRT : IsUnit (matTranspose R).det := by
    simpa [matTranspose, Matrix.det_transpose] using hdetR
  have hdetB : IsUnit (matTranspose R * A * R).det := by
    simpa [Matrix.det_mul] using (hdetRT.mul hdetA).mul hdetR
  have hprod :
      (matTranspose R * A * R) * (matTranspose R * A⁻¹ * R) = 1 := by
    calc
      (matTranspose R * A * R) * (matTranspose R * A⁻¹ * R) =
          (matTranspose R * A) * (R * matTranspose R) * A⁻¹ * R := by
            simp only [Matrix.mul_assoc]
      _ = matTranspose R * A * A⁻¹ * R := by
        rw [hR.mul_transpose_self]
        simp
      _ = (matTranspose R * (A * A⁻¹)) * R := by
        simp only [Matrix.mul_assoc]
      _ = matTranspose R * R := by
        rw [Matrix.mul_nonsing_inv A hdetA]
        simp
      _ = 1 := hR.transpose_mul_self
  have hinv : (matTranspose R * A * R)⁻¹ = matTranspose R * A⁻¹ * R := by
    calc
      (matTranspose R * A * R)⁻¹ = (matTranspose R * A * R)⁻¹ * 1 :=
        (mul_one _).symm
      _ = (matTranspose R * A * R)⁻¹ *
          ((matTranspose R * A * R) * (matTranspose R * A⁻¹ * R)) := by rw [hprod]
      _ = ((matTranspose R * A * R)⁻¹ * (matTranspose R * A * R)) *
          (matTranspose R * A⁻¹ * R) := by rw [← Matrix.mul_assoc]
      _ = 1 * (matTranspose R * A⁻¹ * R) := by
        rw [Matrix.nonsing_inv_mul _ hdetB]
      _ = matTranspose R * A⁻¹ * R := one_mul _
  rcases hA with ⟨hlam, hlamLam, hlower, hinvA⟩
  refine ⟨hlam, hlamLam, ?_, ?_⟩
  · intro ξ
    calc
      lam * vecNormSq ξ = lam * vecNormSq (matVecMul R ξ) := by
        rw [vecNormSq_matVecMul_signedPermutation hR]
      _ ≤ vecDot (matVecMul R ξ) (matVecMul A (matVecMul R ξ)) :=
        hlower (matVecMul R ξ)
      _ = vecDot ξ (matVecMul (matTranspose R * A * R) ξ) := by
        symm
        rw [← matVecMul_mul (matTranspose R * A) R ξ,
          ← matVecMul_mul (matTranspose R) A (matVecMul R ξ),
          vecDot_matVecMul_transpose]
  · intro ξ
    calc
      Lam⁻¹ * vecNormSq ξ = Lam⁻¹ * vecNormSq (matVecMul R ξ) := by
        rw [vecNormSq_matVecMul_signedPermutation hR]
      _ ≤ vecDot (matVecMul R ξ) (matVecMul A⁻¹ (matVecMul R ξ)) :=
        hinvA (matVecMul R ξ)
      _ = vecDot ξ (matVecMul (matTranspose R * A⁻¹ * R) ξ) := by
        symm
        rw [← matVecMul_mul (matTranspose R * A⁻¹) R ξ,
          ← matVecMul_mul (matTranspose R) A⁻¹ (matVecMul R ξ),
          vecDot_matVecMul_transpose]
      _ = vecDot ξ (matVecMul ((matTranspose R * A * R)⁻¹) ξ) := by rw [hinv]

def Carrier.translate {d : ℕ} (z : Fin d → ℤ) (a : Carrier d) : Carrier d where
  val := fun x => a (x + intVecToRealVec z)
  property := by
    constructor
    · intro i j
      exact (a.2.1 i j).comp (measurable_id.add measurable_const)
    · intro R hR
      obtain ⟨ε, hε, hεone, hEll⟩ :=
        a.2.2 (R + euclideanNorm (intVecToRealVec z) + 1) (by
          have hnonneg : 0 ≤ euclideanNorm (intVecToRealVec z) :=
            euclideanNorm_nonneg _
          linarith)
      refine ⟨ε, hε, hεone, ?_⟩
      intro x hx
      apply hEll (x + intVecToRealVec z)
      change euclideanNorm (x + intVecToRealVec z) <
        R + euclideanNorm (intVecToRealVec z) + 1
      calc
        euclideanNorm (x + intVecToRealVec z) ≤
            euclideanNorm x + euclideanNorm (intVecToRealVec z) :=
          euclideanNorm_add_le x _
        _ < R + euclideanNorm (intVecToRealVec z) + 1 := by
          change euclideanNorm x < R at hx
          linarith

@[simp] theorem Carrier.translate_apply {d : ℕ} (z : Fin d → ℤ)
    (a : Carrier d) (x : Vec d) :
    Carrier.translate z a x = a (x + intVecToRealVec z) :=
  rfl

def Carrier.adjoint {d : ℕ} (a : Carrier d) : Carrier d where
  val := fun x => matTranspose (a x)
  property := by
    constructor
    · intro i j
      simpa [matTranspose] using a.2.1 j i
    · intro R hR
      obtain ⟨ε, hε, hεone, hEll⟩ := a.2.2 R hR
      exact ⟨ε, hε, hεone, fun x hx => isEllipticMatrix_transpose (hEll x hx)⟩

@[simp] theorem Carrier.adjoint_apply {d : ℕ} (a : Carrier d) (x : Vec d) :
    Carrier.adjoint a x = matTranspose (a x) :=
  rfl

def Carrier.rotate {d : ℕ} (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (a : Carrier d) : Carrier d where
  val := fun x => matTranspose R * a (matVecMul R x) * R
  property := by
    constructor
    · intro i j
      let f : Fin d → Vec d → ℝ := fun l x =>
        ∑ k ∈ Finset.univ, (matTranspose R) i k * (a (matVecMul R x) k l * R l j)
      have hf : ∀ l ∈ Finset.univ, Measurable (f l) := by
        intro l _
        refine Finset.measurable_sum (s := Finset.univ)
          (f := fun k => fun x : Vec d =>
            (matTranspose R) i k * (a (matVecMul R x) k l * R l j)) ?_
        intro k _
        have hEval : Measurable (fun x : Vec d => a (matVecMul R x) k l) :=
          (a.2.1 k l).comp (signedPermutationHomeomorph R hR).continuous_toFun.measurable
        exact measurable_const.mul (hEval.mul measurable_const)
      simpa [f, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc] using
        (Finset.measurable_sum (s := Finset.univ) (f := f) hf)
    · intro r hr
      obtain ⟨ε, hε, hεone, hEll⟩ := a.2.2 r hr
      refine ⟨ε, hε, hεone, ?_⟩
      intro x hx
      apply isEllipticMatrix_rotate hR
      apply hEll (matVecMul R x)
      change euclideanNorm (matVecMul R x) < r
      rw [euclideanNorm_matVecMul_signedPermutation hR]
      exact hx

@[simp] theorem Carrier.rotate_apply {d : ℕ} (R : Mat d)
    (hR : IsSignedPermutationMatrix R) (a : Carrier d) (x : Vec d) :
    Carrier.rotate R hR a x = matTranspose R * a (matVecMul R x) * R :=
  rfl

private theorem contDiff_matVecMul {d : ℕ} (R : Mat d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => matVecMul R x) := by
  rw [contDiff_pi]
  intro i
  change ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => ∑ j, R i j * x j)
  exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℝ j)

private theorem smoothCompactProbe_translate {d : ℕ} (z : Vec d) {φ : Vec d → ℝ}
    (hφ : SmoothCompactProbe φ) :
    SmoothCompactProbe (fun x => φ (x - z)) := by
  constructor
  · simpa [Function.comp_def] using
      hφ.smooth.comp (contDiff_id.sub contDiff_const)
  · simpa [Function.comp_def] using hφ.compact.comp_homeomorph (Homeomorph.subRight z)

private theorem smoothCompactProbe_rotate {d : ℕ} {R : Mat d}
    (hR : IsSignedPermutationMatrix R) {φ : Vec d → ℝ}
    (hφ : SmoothCompactProbe φ) :
    SmoothCompactProbe (fun y => φ (matVecMul (matTranspose R) y)) := by
  constructor
  · simpa [Function.comp_def] using hφ.smooth.comp (contDiff_matVecMul (matTranspose R))
  · simpa [Function.comp_def] using!
      hφ.compact.comp_homeomorph (signedPermutationHomeomorph (matTranspose R) hR.transpose)

private theorem bilinearTest_translate {d : ℕ} (z : Fin d → ℤ)
    (e e' : Vec d) (φ : Vec d → ℝ) (a : Carrier d) :
    bilinearTest e e' φ (Carrier.translate z a) =
      bilinearTest e e' (fun y => φ (y - intVecToRealVec z)) a := by
  let g : Vec d → ℝ := fun y =>
    vecDot e' (matVecMul (a y) e) * φ (y - intVecToRealVec z)
  have hcv :=
    (measurePreserving_add_right (MeasureTheory.volume : MeasureTheory.Measure (Vec d))
      (intVecToRealVec z)).integral_comp
      (Homeomorph.addRight (intVecToRealVec z)).measurableEmbedding g
  unfold bilinearTest
  calc
    ∫ x, vecDot e' (matVecMul (Carrier.translate z a x) e) * φ x ∂volume =
        ∫ x, g (x + intVecToRealVec z) ∂volume := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          simp [g, sub_eq_add_neg, add_assoc]
    _ = ∫ y, g y ∂volume := hcv
    _ = ∫ y, vecDot e' (matVecMul (a y) e) *
        (fun y => φ (y - intVecToRealVec z)) y ∂volume := rfl

private theorem bilinearTest_adjoint {d : ℕ} (e e' : Vec d) (φ : Vec d → ℝ)
    (a : Carrier d) :
    bilinearTest e e' φ (Carrier.adjoint a) = bilinearTest e' e φ a := by
  unfold bilinearTest
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change vecDot e' (matVecMul (matTranspose (a x)) e) * φ x =
    vecDot e (matVecMul (a x) e') * φ x
  rw [vecDot_matVecMul_transpose, vecDot_comm]

private theorem bilinearTest_rotate {d : ℕ} {R : Mat d}
    (hR : IsSignedPermutationMatrix R) (e e' : Vec d) (φ : Vec d → ℝ)
    (a : Carrier d) :
    bilinearTest e e' φ (Carrier.rotate R hR a) =
      bilinearTest (matVecMul R e) (matVecMul R e')
        (fun y => φ (matVecMul (matTranspose R) y)) a := by
  let g : Vec d → ℝ := fun y =>
    vecDot (matVecMul R e') (matVecMul (a y) (matVecMul R e)) *
      φ (matVecMul (matTranspose R) y)
  have hcv := (measurePreserving_matVecMul_signedPermutation hR).integral_comp
    (signedPermutationHomeomorph R hR).measurableEmbedding g
  have hleft :
      (∫ x, vecDot e' (matVecMul (Carrier.rotate R hR a x) e) * φ x
        ∂volume) =
        ∫ x, g (matVecMul R x) ∂volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    have hback : matVecMul (matTranspose R) (matVecMul R x) = x := by
      rw [matVecMul_mul, hR.transpose_mul_self]
      unfold matVecMul
      simp [Matrix.one_apply]
    have halg :
        vecDot e' (matVecMul ((matTranspose R) * (a (matVecMul R x)) * R) e) =
          vecDot (matVecMul R e') (matVecMul (a (matVecMul R x)) (matVecMul R e)) := by
      calc
        vecDot e' (matVecMul ((matTranspose R) * (a (matVecMul R x)) * R) e) =
            vecDot e' (matVecMul ((matTranspose R) * (a (matVecMul R x)))
              (matVecMul R e)) := by rw [← matVecMul_mul]
        _ = vecDot e' (matVecMul (matTranspose R)
              (matVecMul (a (matVecMul R x)) (matVecMul R e))) := by
              rw [← matVecMul_mul]
        _ = vecDot (matVecMul R e')
              (matVecMul (a (matVecMul R x)) (matVecMul R e)) := by
              rw [vecDot_matVecMul_transpose]
    simp [g, hback, halg]
  unfold bilinearTest
  calc
    ∫ x, vecDot e' (matVecMul (Carrier.rotate R hR a x) e) * φ x ∂volume =
        ∫ x, g (matVecMul R x) ∂volume := hleft
    _ = ∫ y, g y ∂volume := hcv
    _ = ∫ y, vecDot (matVecMul R e') (matVecMul (a y) (matVecMul R e)) *
        φ (matVecMul (matTranspose R) y) ∂volume := rfl

theorem localSigma_mono {d : ℕ} {U V : Set (Vec d)}
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hUV : U ⊆ V) :
    localSigma U hU ≤ localSigma V hV := by
  unfold localSigma
  apply MeasurableSpace.generateFrom_mono
  rintro s ⟨e, e', φ, hφ, hφU, t, ht, rfl⟩
  exact ⟨e, e', φ, hφ, hφU.trans hUV, t, ht, rfl⟩

/-- Translating coefficients by `z` pulls observables local to `U` back to
observables local to `U + z`. -/
theorem measurable_translate_localSigma {d : ℕ} (z : Fin d → ℤ)
    {U : Set (Vec d)} (hU : MeasurableSet U) :
    @Measurable (Carrier d) (Carrier d)
      (localSigma (translateSet (intVecToRealVec z) U) (by
        rw [← preimage_subRight_eq_translateSet]
        exact hU.preimage (Homeomorph.subRight _).continuous.measurable))
      (localSigma U hU) (Carrier.translate z) := by
  let : MeasurableSpace (Carrier d) :=
    localSigma (translateSet (intVecToRealVec z) U) (by
      rw [← preimage_subRight_eq_translateSet]
      exact hU.preimage (Homeomorph.subRight _).continuous.measurable)
  apply measurable_generateFrom
  rintro s ⟨e, e', φ, hφ, hφU, t, ht, rfl⟩
  let ψ : Vec d → ℝ := fun y => φ (y - intVecToRealVec z)
  have htest : (fun a : Carrier d => bilinearTest e e' φ (Carrier.translate z a)) =
      bilinearTest e e' ψ := by
    funext a
    exact bilinearTest_translate z e e' φ a
  have hψsupport_eq :
      tsupport ψ = (fun y : Vec d => y - intVecToRealVec z) ⁻¹' tsupport φ := by
    simpa [ψ, Function.comp_def] using
      (tsupport_comp_eq_preimage φ (Homeomorph.subRight (intVecToRealVec z)))
  have hψsupport : tsupport ψ ⊆ translateSet (intVecToRealVec z) U := by
    intro y hy
    have hy'' : y ∈ (fun y : Vec d => y - intVecToRealVec z) ⁻¹' tsupport φ := by
      rw [← hψsupport_eq]
      exact hy
    have hy' : y - intVecToRealVec z ∈ tsupport φ := by
      exact hy''
    exact mem_translateSet_iff_sub_mem.mpr (hφU hy')
  change MeasurableSet ((fun a : Carrier d =>
    bilinearTest e e' φ (Carrier.translate z a)) ⁻¹' t)
  rw [htest]
  apply MeasurableSpace.measurableSet_generateFrom
  exact ⟨e, e', ψ, smoothCompactProbe_translate (intVecToRealVec z) hφ,
    hψsupport, t, ht, rfl⟩

/-- A local observable remains local after precomposing with a coefficient
translation, with its region translated by the same vector. -/
theorem IsLocalObservable.comp_translate {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) {β : Type*} [MeasurableSpace β]
    {X : Carrier d → β} (hX : IsLocalObservable U hU X) (z : Fin d → ℤ) :
    IsLocalObservable (translateSet (intVecToRealVec z) U) (by
      rw [← preimage_subRight_eq_translateSet]
      exact hU.preimage (Homeomorph.subRight _).continuous.measurable)
      (X ∘ Carrier.translate z) := by
  exact hX.comp (measurable_translate_localSigma z hU)

theorem measurable_translate_globalSigma {d : ℕ} (z : Fin d → ℤ) :
    Measurable (Carrier.translate (d := d) z) := by
  apply measurable_generateFrom
  rintro s ⟨e, e', φ, hφ, _hφ, t, ht, rfl⟩
  let ψ : Vec d → ℝ := fun y => φ (y - intVecToRealVec z)
  have htest : (fun a : Carrier d => bilinearTest e e' φ (Carrier.translate z a)) =
      bilinearTest e e' ψ := by
    funext a
    exact bilinearTest_translate z e e' φ a
  change MeasurableSet ((fun a : Carrier d =>
    bilinearTest e e' φ (Carrier.translate z a)) ⁻¹' t)
  rw [htest]
  apply MeasurableSpace.measurableSet_generateFrom
  exact ⟨e, e', ψ, smoothCompactProbe_translate (intVecToRealVec z) hφ,
    Set.subset_univ _, t, ht, rfl⟩

theorem measurable_adjoint_globalSigma {d : ℕ} :
    Measurable (Carrier.adjoint : Carrier d → Carrier d) := by
  apply measurable_generateFrom
  rintro s ⟨e, e', φ, hφ, _hφ, t, ht, rfl⟩
  have htest : (fun a : Carrier d => bilinearTest e e' φ (Carrier.adjoint a)) =
      bilinearTest e' e φ := by
    funext a
    exact bilinearTest_adjoint e e' φ a
  change MeasurableSet ((fun a : Carrier d =>
    bilinearTest e e' φ (Carrier.adjoint a)) ⁻¹' t)
  rw [htest]
  apply MeasurableSpace.measurableSet_generateFrom
  exact ⟨e', e, φ, hφ, Set.subset_univ _, t, ht, rfl⟩

theorem measurable_rotate_globalSigma {d : ℕ} (R : Mat d)
    (hR : IsSignedPermutationMatrix R) :
    Measurable (Carrier.rotate (d := d) R hR) := by
  apply measurable_generateFrom
  rintro s ⟨e, e', φ, hφ, _hφ, t, ht, rfl⟩
  let ψ : Vec d → ℝ := fun y => φ (matVecMul (matTranspose R) y)
  have htest :
      (fun a : Carrier d => bilinearTest e e' φ (Carrier.rotate R hR a)) =
        bilinearTest (matVecMul R e) (matVecMul R e') ψ := by
    funext a
    exact bilinearTest_rotate hR e e' φ a
  change MeasurableSet ((fun a : Carrier d =>
    bilinearTest e e' φ (Carrier.rotate R hR a)) ⁻¹' t)
  rw [htest]
  apply MeasurableSpace.measurableSet_generateFrom
  exact ⟨matVecMul R e, matVecMul R e', ψ, smoothCompactProbe_rotate hR hφ,
    Set.subset_univ _, t, ht, rfl⟩

end Homogenization.Source.Coarse
